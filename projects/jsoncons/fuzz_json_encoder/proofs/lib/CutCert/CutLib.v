(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CL.
Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_ret_at (pc : Z) : Prop :=
  exists w rd rs1 (imm : bv 12), fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (Jalr rd rs1 imm, 4)
     /\ bv_unsigned rd = 0 /\ bv_unsigned rs1 = 1 /\ bv_unsigned imm = 0.
Lemma ret_cps : forall (fx : FPState) R pc M model K,
  is_ret_at pc ->
  m_halted model = None -> m_vm_lazy model = [] ->
  Hoare.ret_ok (getr R 1%bv) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (getr R 1%bv) M (seg_rom segs)) model) K ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) model) K.
Proof.
  intros fx R pc M model K (w & rd & rs1 & imm & Hf & He & Hd & Urd & Urs & Uimm) Hh Hl Hret HK.
  assert (rd = 0%bv) as -> by (apply bv_eq; exact Urd).
  assert (rs1 = 1%bv) as -> by (apply bv_eq; exact Urs).
  assert (imm = 0%bv) as -> by (apply bv_eq; exact Uimm).
  eapply srz_step; [exact Hh | exact Hl | reflexivity | | exact HK].
  rewrite (step_jalr_x0 segs R (Z_to_bv 64 pc) M (seg_rom segs) w 1%bv 0%bv (getr R 1%bv) Hf He Hd eq_refl).
  change (bv_signed (0%bv : bv 12)) with 0. unfold Hoare.ret_ok in Hret. rewrite Hret. reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma leaf_reg : forall c ps E' R' M M' i e,
  CC.leaf_facts segs c ps E' R' M M' -> In (i, e) (SR.ps_regs ps) -> getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e.
Proof. intros c ps E' R' M M' i e H Hin. exact (proj2 (CC.lf_regs _ _ _ _ _ _ _ H i e Hin)). Qed.

(* [comment removed for export] *)
Lemma EnvR_reg : forall R (x : reg), ev (EnvR R) (ridx x) = getr R x.
Proof.
  intros R x. assert (H : (ridx x < 32)%nat).
  { unfold ridx. pose proof (bv_unsigned_in_range _ x) as B. change (bv_modulus 5) with 32 in B. lia. }
  rewrite (EnvR_ev R (ridx x) H). rewrite CC.reg_of_ridx. reflexivity.
Qed.
Lemma EnvR_reg_u : forall R (x : reg) z, getr R x = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ev (EnvR R) (ridx x)) = z.
Proof. intros R x z H Hz. rewrite EnvR_reg, H. apply u64_of_Z. exact Hz. Qed.

(* [comment removed for export] *)
Definition ps_reg_is (ps : SR.post_spec) (q : nat) (e : expr) : bool :=
  existsb (fun ie : nat * expr => Nat.eqb (fst ie) q && expr_eqb (snd ie) e)%bool (SR.ps_regs ps).
Definition ps_keeps (ps : SR.post_spec) (qs : list nat) : bool := forallb (fun q => ps_reg_is ps q (EVar q)) qs.
Definition ps_at (ps : SR.post_spec) (pcs : list Z) : bool := existsb (Z.eqb (SR.ps_pc ps)) pcs.
Lemma ps_reg_is_sound : forall c ps E' R' M M' q e,
  CC.leaf_facts segs c ps E' R' M M' -> ps_reg_is ps q e = true -> getr R' (Z_to_bv 5 (Z.of_nat q)) = edenot E' e.
Proof.
  intros c ps E' R' M M' q e HLF H. unfold ps_reg_is in H. apply existsb_exists in H as ([i e'] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_prop in Hb as [Hi He]. apply Nat.eqb_eq in Hi. apply expr_eqb_eq in He. subst i e'.
  exact (leaf_reg _ _ _ _ _ _ _ _ HLF Hin).
Qed.
(* [comment removed for export] *)
Lemma ps_keeps_sound : forall c ps E E' R' M M' qs b (x : reg),
  CC.leaf_facts segs c ps E' R' M M' -> ps_keeps ps qs = true -> env_agree b E E' -> In (ridx x) qs -> (ridx x < b)%nat ->
  getr R' x = ev E (ridx x).
Proof.
  intros c ps E E' R' M M' qs b x HLF H Hag Hin Hb. unfold ps_keeps in H. rewrite forallb_forall in H.
  rewrite <- (CC.reg_of_ridx x) at 1. rewrite (ps_reg_is_sound _ _ _ _ _ _ _ _ HLF (H _ Hin)). cbn [edenot].
  symmetry. apply (proj1 Hag). exact Hb.
Qed.
Lemma ps_at_sound : forall ps pcs, ps_at ps pcs = true -> In (SR.ps_pc ps) pcs.
Proof. intros ps pcs H. unfold ps_at in H. apply existsb_exists in H as (x & Hin & Heq). apply Z.eqb_eq in Heq. subst x. exact Hin. Qed.

(* [comment removed for export] *)
Lemma frozen_at_leaf : forall b E E' n, env_agree b E E' -> (n < b)%nat -> ev E' n = ev E n.
Proof. intros b E E' n [H _] Hn. symmetry. apply H. exact Hn. Qed.

(* [comment removed for export] *)
Section Pure.
Variable NF : nat.
Variable E0 : env.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variable F0 : list SGP.region.
Hypothesis F0vars : forallb (SGP.region_vars_lt NF) F0 = true.

Definition pure_amb (i : nat) (E : env) (M : word -> option byte) (model : Model) : Prop :=
  model = model0 /\ env_agree NF E0 E /\ (forall a : word, SGP.outside E0 F0 a -> M a = M0 a) /\ mem_grows M0 M.

(* [comment removed for export] *)
Definition sub_F (c : CC.cutpoint) : Prop :=
  forall E a, env_agree NF E0 E -> SGP.outside E0 F0 a -> SGP.outside E (CC.cp_F c) a.

Lemma outside_agree_F0 : forall E a, env_agree NF E0 E -> SGP.outside E0 F0 a -> SGP.outside E F0 a.
Proof.
  intros E a Hag H. unfold SGP.outside in *. rewrite Forall_forall in *. intros [[rb rlo] rlen] Hin.
  specialize (H _ Hin). cbn beta iota in H |- *.
  rewrite forallb_forall in F0vars. specialize (F0vars _ Hin). cbn [SGP.region_vars_lt] in F0vars.
  apply andb_prop in F0vars as [V1 V2].
  unfold estart, elenZ in *. cbn [a_base a_off] in *.
  rewrite <- (SR.edenot_agree_AP NF E0 E rb Hag V1), <- (SR.edenot_agree_AP NF E0 E rlen Hag V2). exact H.
Qed.

Lemma pure_amb_step : forall i j c ps E E' E2 R' M M' model,
  sub_F c -> (NF <= CC.cp_nx c)%nat ->
  pure_amb i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
  env_agree NF E' E2 ->
  pure_amb j E2 M' model.
Proof.
  intros i j c ps E E' E2 R' M M' model Hsub Hnf (Hm & Hag0 & Hfr & Hgr) Hag HLF Hag2.
  assert (HagE' : env_agree NF E0 E').
  { eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag | exact Hnf]]. }
  split; [exact Hm|]. split; [eapply CC.env_agree_trans; [exact HagE' | exact Hag2]|]. split.
  - intros a Ha. rewrite (CC.lf_frame _ _ _ _ _ _ _ HLF a (Hsub E' a HagE' Ha)). apply Hfr. exact Ha.
  - eapply mem_grows_trans; [exact Hgr | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma pure_amb_goto : forall i c ps j s,
  sub_F c -> (NF <= CC.cp_nx c)%nat -> CC.amb_goto segs pure_amb NF i c ps j s.
Proof.
  intros i c ps j s Hsub Hnf E R M model E' R' M' _ HAmb Hag HLF.
  eapply pure_amb_step; [exact Hsub | exact Hnf | exact HAmb | exact Hag | exact HLF | apply CC.env_over_agree].
Qed.

Lemma pure_amb_model : forall i E M model, m_halted model0 = None -> m_vm_lazy model0 = [] ->
  pure_amb i E M model -> m_halted model = None /\ m_vm_lazy model = [].
Proof. intros i E M model Hh Hl (-> & _). split; assumption. Qed.

Lemma sub_F_nil : forall c, CC.cp_F c = [] -> sub_F c.
Proof. intros c Hc E a _ _. rewrite Hc. constructor. Qed.
End Pure.

End WithSegs.
Ltac solve_is_ret := unfold is_ret_at; do 4 eexists; (split; [vm_compute; reflexivity|]); repeat split; vm_compute; reflexivity.
End CL.

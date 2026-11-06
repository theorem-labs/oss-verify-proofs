(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5SubMul.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5SM.
Abbreviation RSEGS := Plain.M.loaded_segments.
Module PA := LibSegZ_smA.
Module PI := LibSegZ_smI.
Module PK := LibSegZ_smK.
Module PB := LibSegZ_smB.
Module PJ := LibSegZ_smJ.
Module PT := LibSegZ_smT.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition SUBMUL : Z := 0x22674.
Definition L1HEAD : Z := 0x226a4.
Definition SM_BR : Z := 0x22730.
Definition SM_BOR : Z := 0x22734.
Definition L2HEAD : Z := 0x2274c.
Definition L2DONE : Z := 0x22778.
Definition SM_EPI : Z := 0x22780.
Definition SM_RET : Z := 0x2278c.
Definition SM_SCRATCH : Z := 16.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.

(* [comment removed for export] *)
Record smctx (M : word -> option byte) (sp a b qa : Z) (n : nat) : Prop := SMC {
  c_sp : sp mod 16 = 0 /\ 1048592 <= sp <= 140737488355328;
  c_spw : L5.writable RSEGS M (sp - 16) 16;
  c_a : a mod 8 = 0 /\ 4096 <= a /\ a + 8 * Z.of_nat n + 8 <= 2 ^ 47;
  c_aw : L5.writable RSEGS M a (8 * Z.of_nat n + 8);
  c_ad : L5.defined M a (8 * Z.of_nat n + 8);
  c_b : b mod 8 = 0 /\ 4096 <= b /\ b + 8 * Z.of_nat n <= 2 ^ 47;
  c_bd : L5.defined M b (8 * Z.of_nat n);
  c_q : qa mod 8 = 0 /\ 4096 <= qa <= 140737488355320;
  c_qw : L5.writable RSEGS M qa 8;
  c_qd : L5.defined M qa 8;
  c_n : (1 <= n <= 300)%nat;
  c_ap1 : apart (sp - 16) 16 a (8 * Z.of_nat n + 8);
  c_ap2 : apart (sp - 16) 16 b (8 * Z.of_nat n);
  c_ap3 : apart (sp - 16) 16 qa 8;
  c_ap4 : apart a (8 * Z.of_nat n + 8) b (8 * Z.of_nat n);
  c_ap5 : apart a (8 * Z.of_nat n + 8) qa 8;
  c_ap6 : apart b (8 * Z.of_nat n) qa 8 }.

Lemma smctx_grows M M' sp a b qa n : smctx M sp a b qa n -> mem_grows M M' -> smctx M' sp a b qa n.
Proof.
  intros C G. destruct C. constructor; auto.
  - eapply L5.writable_grows; eauto. - eapply L5.writable_grows; eauto. - eapply L5.defined_grows; eauto.
  - eapply L5.defined_grows; eauto. - eapply L5.writable_grows; eauto. - eapply L5.defined_grows; eauto.
Qed.

(* [comment removed for export] *)
Definition sm_kept : list nat := [1; 3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition submul_post (M M' : word -> option byte) (sp a b qa : Z) (n : nat) (R R' : bvmap 5 word) : Prop :=
  (forall i, In i sm_kept -> getr R' (reg i) = getr R (reg i))
  /\ getr R' (reg 2) = getr R (reg 2) /\ getr R' (reg 8) = getr R (reg 8) /\ getr R' (reg 9) = getr R (reg 9)
  /\ regs_preserved R R'
  /\ smctx M' sp a b qa n
  /\ L5.frame_but [(sp - 16, 16); (a, 8 * Z.of_nat n + 8); (qa, 8)] M M' /\ mem_grows M M'.

Definition submul_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (sp a b qa r : Z) (n : nat),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 11%bv = Z_to_bv 64 a -> getr R 12%bv = Z_to_bv 64 b ->
    getr R 13%bv = Z_to_bv 64 (Z.of_nat n) -> getr R 14%bv = Z_to_bv 64 qa ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    smctx M sp a b qa n ->
    (forall (fx' : FPState) R' M', submul_post M M' sp a b qa n R R' -> srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R SUBMUL M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VAL (R : bvmap 5 word) (sp a b qa : Z) (n i : nat) (x38 x39 x40 x41 : word) (k : nat) : word :=
  match k with
  | 2%nat => Z_to_bv 64 sp
  | 33%nat => Z_to_bv 64 a | 34%nat => Z_to_bv 64 b | 35%nat => Z_to_bv 64 (Z.of_nat n) | 36%nat => Z_to_bv 64 qa
  | 37%nat => Z_to_bv 64 (Z.of_nat i) | 38%nat => x38 | 39%nat => x39 | 40%nat => x40 | 41%nat => x41
  | _ => getr R (reg k)
  end.
Definition VZ (R : bvmap 5 word) (sp a b qa : Z) (n i : nat) (x38 x39 x40 x41 : word) (k : nat) : Z :=
  match k with
  | 2%nat => sp
  | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa
  | 37%nat => Z.of_nat i | 38%nat => bv_unsigned x38 | 39%nat => bv_unsigned x39 | 40%nat => bv_unsigned x40 | 41%nat => bv_unsigned x41
  | _ => bv_unsigned (getr R (reg k))
  end.
Lemma VAL_VZ R sp a b qa n i x38 x39 x40 x41 :
  0 <= sp < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= qa < 2 ^ 64 -> (n <= 300)%nat -> (i <= 300)%nat ->
  forall k, bv_unsigned (ev (Env (VAL R sp a b qa n i x38 x39 x40 x41) (fun _ => [])) k) = VZ R sp a b qa n i x38 x39 x40 x41 k.
Proof.
  intros Hs Ha Hb Hq Hn Hi k. cbn [ev].
  unfold VAL, VZ.
  repeat (lazymatch goal with
          | |- bv_unsigned (match k with _ => _ end) = _ => destruct k as [|k]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rl7 : (7%bv : bv 5) = reg 7. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl28 : (28%bv : bv 5) = reg 28. Proof. apply bv_eq. reflexivity. Qed.
Lemma br_225f8 fx R M :
  msteps RSEGS (st fx R 0x22730 M) (st fx R (if branch_taken BC_GEU (getr R (reg 7)) (getr R (reg 28)) then 0x22780 else 0x22734) M).
Proof.
  rewrite <- rl7, <- rl28.
  apply (@BDQ.br_site fx M R 0x22730 0x22780 (0x22730%bv : word) _ BC_GEU 7 28 _ eq_refl F_22730 eq_refl D_22730). reflexivity.
Qed.
Lemma ret_22654 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
  msteps RSEGS (st fx R 0x2278c M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M 0x2278c W_2278c r F_2278c eq_refl D_2278c H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_A : list nat := Eval vm_compute in (BG.kept_list 48 PA.regs0 PA.regs_out).
Lemma KS_A_ok : BG.kept_ok 48 PA.regs0 PA.regs_out KS_A = true. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A : SR.ps_cells PA.ps0 = [KWord (SA (EVar 2) (-16)) 8 (EVar 9); KWord (SA (EVar 2) (-8)) 8 (EVar 8)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition at_l1 (R : bvmap 5 word) (sp a b qa : Z) (n i : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 16) /\ getr R (reg 5) = Z_to_bv 64 (b + 8 * Z.of_nat i) /\
  getr R (reg 10) = Z_to_bv 64 4294967295 /\ getr R (reg 11) = Z_to_bv 64 a /\ getr R (reg 12) = Z_to_bv 64 b /\
  getr R (reg 13) = Z_to_bv 64 (8 * Z.of_nat n) /\ getr R (reg 14) = Z_to_bv 64 qa /\
  getr R (reg 15) = Z_to_bv 64 (a + 8 + 8 * Z.of_nat i) /\ getr R (reg 16) = Z_to_bv 64 (a + 8 + 8 * Z.of_nat n).

Local Ltac intro_ctx C := destruct C as [Csp Cspw Ca Caw Cad Cb Cbd Cq Cqw Cqd Cn Cap1 Cap2 Cap3 Cap4 Cap5 Cap6]; unfold apart in *.

Lemma smA_conc fx R M (sp a b qa : Z) (n : nat) :
  smctx M sp a b qa n ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b ->
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 14) = Z_to_bv 64 qa ->
  exists fx' R' M', msteps RSEGS (st fx R SUBMUL M) (st fx' R' L1HEAD M')
    /\ (forall x, In x KS_A -> getr R' (reg x) = getr R (reg x))
    /\ at_l1 R' sp a b qa n 0
    /\ L5.u64_at RSEGS M' (sp - 8) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 9)))
    /\ (forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C H2 H11 H12 H13 H14. intro_ctx C.
  set (Vf := VAL R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PA.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA.regs0 nth]. repeat split; assumption. }
  assert (HK: know_ok RSEGS E M PA.kn0). { unfold know_ok, PA.kn0. L5K.kn_all ZA. }
  destruct (PA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps0. change PA.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA.regs0 PA.regs_out 48 KS_A KS_A_ok HR Hag Hregs j Hj). }
  split. { unfold at_l1. repeat split.
    all: rewrite (BG.out_reg PA.regs_out E' R' _ Hregs) by lia; cbn [nth PA.regs_out PA.regs_out0]; L5K.wordE' ZA Hag. }
  rewrite cells_A in Hcells.
  split. { replace (sp - 8) with (sp + -8) by lia. eapply L5K.u64_of_KWord8. apply Hcells. right; left; reflexivity. L5K.evalE' ZA Hag. L5K.evalE' ZA Hag. }
  split. { replace (sp - 16) with (sp + -16) by lia. eapply L5K.u64_of_KWord8. apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. L5K.evalE' ZA Hag. }
  split. { intros x Hx. apply Hfr. unfold PA.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_I : list nat := Eval vm_compute in (BG.kept_list 48 PI.regs0 PI.regs_out0).
Lemma KS_I_ok0 : BG.kept_ok 48 PI.regs0 PI.regs_out0 KS_I = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS_I_ok1 : BG.kept_ok 48 PI.regs0 PI.regs_out1 KS_I = true. Proof. vm_compute. reflexivity. Qed.
Lemma PSS_I : PI.PSS = [PI.ps0; PI.ps1]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_I0 : exists cs, SR.ps_cells PI.ps0 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 2 300 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma cells_I1 : exists cs, SR.ps_cells PI.ps1 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 1 1 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma pc_I0 : SR.ps_pc PI.ps0 = 0x226a4. Proof. reflexivity. Qed.
Lemma pc_I1 : SR.ps_pc PI.ps1 = 0x22730. Proof. reflexivity. Qed.

Lemma smI_conc fx R M (sp a b qa : Z) (n i : nat) :
  smctx M sp a b qa n -> at_l1 R sp a b qa n i -> (i < n)%nat ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R L1HEAD M) (st fx' R' pc' M')
    /\ (forall x, In x KS_I -> getr R' (reg x) = getr R (reg x))
    /\ ((pc' = L1HEAD /\ (i + 1 < n)%nat /\ at_l1 R' sp a b qa n (S i)) \/ (pc' = SM_BR /\ (i + 1 = n)%nat))
    /\ (forall x : word, ~ (a + 8 * Z.of_nat i <= bv_unsigned x < a + 8 * Z.of_nat i + 16) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C AT Hi. intro_ctx C. destruct AT as (A2 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  set (Vf := VAL R sp a b qa n i (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n i (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PI.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PI.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PI.kn0). { unfold know_ok, PI.kn0. L5K.kn_all ZA. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  rewrite PSS_I in Hnth. change PI.NX0 with 48%nat in Hag.
  assert (FR: forall x : word, ~ (a + 8 * Z.of_nat i <= bv_unsigned x < a + 8 * Z.of_nat i + 16) -> M' x = M x).
  { intros x Hx. apply Hfr. unfold PI.F0. L5K.outsideF ZA Hag. }
  destruct (L5K.nth_error_pair _ _ _ _ Hnth) as [[-> ->] | [-> ->]].
  - (* [comment removed for export] *)
    exists fx', R', M', L1HEAD. rewrite pc_I0 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out0 48 KS_I KS_I_ok0 HR Hag Hregs j Hj). }
    split.
    { left. split. reflexivity.
      destruct cells_I0 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 2 <= Z.of_nat n - Z.of_nat i <= 300).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      split. lia.
      unfold at_l1. repeat split.
      all: rewrite (BG.out_reg PI.regs_out0 E' R' _ Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag. }
    split. exact FR. exact Hgr.
  - (* [comment removed for export] *)
    exists fx', R', M', SM_BR. rewrite pc_I1 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out1 48 KS_I KS_I_ok1 HR Hag Hregs j Hj). }
    split.
    { right. split. reflexivity.
      destruct cells_I1 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 1 <= Z.of_nat n - Z.of_nat i <= 1).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      lia. }
    split. exact FR. exact Hgr.
Qed.

(* [comment removed for export] *)
Definition KS_L : list nat := [1; 2; 3; 4; 10; 11; 12; 13; 14; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma KS_L_I x : In x KS_L -> In x KS_I.
Proof. unfold KS_L, KS_I. cbn. intuition lia. Qed.

Lemma loop1 (m : nat) : forall fx R M (sp a b qa : Z) (n i : nat),
  (m = n - i)%nat -> smctx M sp a b qa n -> at_l1 R sp a b qa n i -> (i < n)%nat ->
  exists fx' R' M', msteps RSEGS (st fx R L1HEAD M) (st fx' R' SM_BR M')
    /\ (forall x, In x KS_L -> getr R' (reg x) = getr R (reg x))
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R M sp a b qa n i Hm C AT Hi. lia.
  destruct (smI_conc fx R M sp a b qa n i C AT Hi) as (fx1 & R1 & M1 & pc1 & MS1 & K1 & EX & FR1 & G1).
  destruct EX as [(-> & Hlt & AT1) | (-> & Heq)].
  - destruct (IH fx1 R1 M1 sp a b qa n (S i) ltac:(lia) (smctx_grows _ _ _ _ _ _ _ C G1) AT1 ltac:(lia))
      as (fx' & R' & M' & MS & K & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. apply KS_L_I. exact Hx. }
    split. { intros x Hx. rewrite (FR x Hx). apply FR1. lia. }
    eapply mem_grows_trans; eauto.
  - exists fx1, R1, M1. split. exact MS1.
    split. { intros x Hx. apply K1. apply KS_L_I. exact Hx. }
    split. { intros x Hx. apply FR1. lia. } exact G1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_K : list nat := Eval vm_compute in (BG.kept_list 48 PK.regs0 PK.regs_out0).
Lemma KS_K_ok : BG.kept_ok 48 PK.regs0 PK.regs_out0 KS_K = true. Proof. vm_compute. reflexivity. Qed.

Lemma smK_conc fx R M (sp : Z) (v8 v9 : word) :
  sp mod 16 = 0 /\ 1048592 <= sp <= 140737488355328 -> L5.writable RSEGS M (sp - 16) 16 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 16) ->
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned v8) -> L5.u64_at RSEGS M (sp - 16) (bv_unsigned v9) ->
  exists fx' R' M', msteps RSEGS (st fx R SM_EPI M) (st fx' R' SM_RET M')
    /\ (forall x, In x KS_K -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = v8 /\ getr R' (reg 9) = v9
    /\ (forall x : word, M' x = M x) /\ mem_grows M M'.
Proof.
  intros Csp Cspw H2 U8 U9.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 8%nat => v8 | 9%nat => v9 | 40%nat => getr R (reg 8) | 41%nat => getr R (reg 9) | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = (fun k : nat => match k with 2%nat => sp | 8%nat => bv_unsigned v8 | 9%nat => bv_unsigned v9
                | 40%nat => bv_unsigned (getr R (reg 8)) | 41%nat => bv_unsigned (getr R (reg 9)) | _ => bv_unsigned (getr R (reg k)) end) k).
  { intros k. cbn [ev E]. subst Vf. cbv beta.
    repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try reflexivity; try (apply BG.unsigned_lit; lia)). }
  assert (HR: regs_ok E PK.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PK.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PK.kn0).
  { unfold know_ok, PK.kn0. L5K.kn_all ZA.
    all: try (replace (sp + -8) with (sp - 8) by lia; exact U8). all: try (replace (sp + -16) with (sp - 16) by lia; exact U9). }
  destruct (PK.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PK.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PK.regs0 PK.regs_out0 48 KS_K KS_K_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PK.regs_out0 E' R' 2 Hregs) by lia. cbn [nth PK.regs_out0]. L5K.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PK.regs_out0 E' R' 8 Hregs) by lia. cbn [nth PK.regs_out0 edenot]. rewrite <- (proj1 Hag 8%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PK.regs_out0 E' R' 9 Hregs) by lia. cbn [nth PK.regs_out0 edenot]. rewrite <- (proj1 Hag 9%nat) by lia. reflexivity. }
  split. { intros x. apply Hfr. unfold PK.F0. apply L5K.outside_nil_e. } exact Hgr.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_B : list nat := Eval vm_compute in (BG.kept_list 48 PB.regs0 PB.regs_out0).
Lemma KS_B_ok : BG.kept_ok 48 PB.regs0 PB.regs_out0 KS_B = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition at_l2 (R : bvmap 5 word) (sp a b qa : Z) (n j : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 16) /\ getr R (reg 10) = Z_to_bv 64 (b + 8 * Z.of_nat n) /\ getr R (reg 11) = Z_to_bv 64 a /\
  getr R (reg 12) = Z_to_bv 64 (b + 8 * Z.of_nat j) /\ getr R (reg 13) = Z_to_bv 64 (8 * Z.of_nat n) /\
  getr R (reg 14) = Z_to_bv 64 (a + 8 * Z.of_nat j).

Lemma smB_conc fx R M (sp a b qa : Z) (n : nat) :
  smctx M sp a b qa n ->
  getr R (reg 2) = Z_to_bv 64 (sp - 16) -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b ->
  getr R (reg 13) = Z_to_bv 64 (8 * Z.of_nat n) -> getr R (reg 14) = Z_to_bv 64 qa ->
  exists fx' R' M', msteps RSEGS (st fx R SM_BOR M) (st fx' R' L2HEAD M')
    /\ (forall x, In x KS_B -> getr R' (reg x) = getr R (reg x))
    /\ at_l2 R' sp a b qa n 0
    /\ (forall x : word, ~ (qa <= bv_unsigned x < qa + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C H2 H11 H12 H13 H14. intro_ctx C.
  set (Vf := VAL R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PB.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PB.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PB.kn0). { unfold know_ok, PB.kn0. L5K.kn_all ZA. }
  destruct (PB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PB.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PB.regs0 PB.regs_out0 48 KS_B KS_B_ok HR Hag Hregs j Hj). }
  split. { unfold at_l2. repeat split.
    all: rewrite (BG.out_reg PB.regs_out0 E' R' _ Hregs) by lia; cbn [nth PB.regs_out PB.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros x Hx. apply Hfr. unfold PB.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_J : list nat := Eval vm_compute in (BG.kept_list 48 PJ.regs0 PJ.regs_out0).
Lemma KS_J_ok0 : BG.kept_ok 48 PJ.regs0 PJ.regs_out0 KS_J = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS_J_ok1 : BG.kept_ok 48 PJ.regs0 PJ.regs_out1 KS_J = true. Proof. vm_compute. reflexivity. Qed.
Lemma PSS_J : PJ.PSS = [PJ.ps0; PJ.ps1]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_J0 : exists cs, SR.ps_cells PJ.ps0 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 2 300 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma cells_J1 : exists cs, SR.ps_cells PJ.ps1 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 1 1 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma pc_J0 : SR.ps_pc PJ.ps0 = 0x2274c. Proof. reflexivity. Qed.
Lemma pc_J1 : SR.ps_pc PJ.ps1 = 0x22778. Proof. reflexivity. Qed.

Lemma smJ_conc fx R M (sp a b qa : Z) (n j : nat) :
  smctx M sp a b qa n -> at_l2 R sp a b qa n j -> (j < n)%nat ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R L2HEAD M) (st fx' R' pc' M')
    /\ (forall x, In x KS_J -> getr R' (reg x) = getr R (reg x))
    /\ ((pc' = L2HEAD /\ (j + 1 < n)%nat /\ at_l2 R' sp a b qa n (S j)) \/ (pc' = L2DONE /\ (j + 1 = n)%nat))
    /\ (forall x : word, ~ (a + 8 * Z.of_nat j <= bv_unsigned x < a + 8 * Z.of_nat j + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C AT Hj. intro_ctx C. destruct AT as (A2 & A10 & A11 & A12 & A13 & A14).
  set (Vf := VAL R sp a b qa n j (getr R (reg 15)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n j (getr R (reg 15)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PJ.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PJ.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PJ.kn0). { unfold know_ok, PJ.kn0. L5K.kn_all ZA. }
  destruct (PJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  rewrite PSS_J in Hnth. change PJ.NX0 with 48%nat in Hag.
  assert (FR: forall x : word, ~ (a + 8 * Z.of_nat j <= bv_unsigned x < a + 8 * Z.of_nat j + 8) -> M' x = M x).
  { intros x Hx. apply Hfr. unfold PJ.F0. L5K.outsideF ZA Hag. }
  destruct (L5K.nth_error_pair _ _ _ _ Hnth) as [[-> ->] | [-> ->]].
  - exists fx', R', M', L2HEAD. rewrite pc_J0 in Hms. split. exact Hms.
    split. { intros i Hi. apply (BG.kept_regs E E' R R' PJ.regs0 PJ.regs_out0 48 KS_J KS_J_ok0 HR Hag Hregs i Hi). }
    split.
    { left. split. reflexivity.
      destruct cells_J0 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 2 <= Z.of_nat n - Z.of_nat j <= 300).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      split. lia.
      unfold at_l2. repeat split.
      all: rewrite (BG.out_reg PJ.regs_out0 E' R' _ Hregs) by lia; cbn [nth PJ.regs_out0]; L5K.wordE' ZA Hag. }
    split. exact FR. exact Hgr.
  - exists fx', R', M', L2DONE. rewrite pc_J1 in Hms. split. exact Hms.
    split. { intros i Hi. apply (BG.kept_regs E E' R R' PJ.regs0 PJ.regs_out1 48 KS_J KS_J_ok1 HR Hag Hregs i Hi). }
    split.
    { right. split. reflexivity.
      destruct cells_J1 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 1 <= Z.of_nat n - Z.of_nat j <= 1).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      lia. }
    split. exact FR. exact Hgr.
Qed.

Definition KS_L2 : list nat := [1; 2; 3; 4; 8; 9; 10; 11; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma KS_L2_J x : In x KS_L2 -> In x KS_J.
Proof. unfold KS_L2, KS_J. cbn. intuition lia. Qed.

Lemma loop2 (m : nat) : forall fx R M (sp a b qa : Z) (n j : nat),
  (m = n - j)%nat -> smctx M sp a b qa n -> at_l2 R sp a b qa n j -> (j < n)%nat ->
  exists fx' R' M', msteps RSEGS (st fx R L2HEAD M) (st fx' R' L2DONE M')
    /\ (forall x, In x KS_L2 -> getr R' (reg x) = getr R (reg x))
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n) -> M' x = M x) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R M sp a b qa n j Hm C AT Hj. lia.
  destruct (smJ_conc fx R M sp a b qa n j C AT Hj) as (fx1 & R1 & M1 & pc1 & MS1 & K1 & EX & FR1 & G1).
  destruct EX as [(-> & Hlt & AT1) | (-> & Heq)].
  - destruct (IH fx1 R1 M1 sp a b qa n (S j) ltac:(lia) (smctx_grows _ _ _ _ _ _ _ C G1) AT1 ltac:(lia))
      as (fx' & R' & M' & MS & K & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. apply KS_L2_J. exact Hx. }
    split. { intros x Hx. rewrite (FR x Hx). apply FR1. lia. }
    eapply mem_grows_trans; eauto.
  - exists fx1, R1, M1. split. exact MS1.
    split. { intros x Hx. apply K1. apply KS_L2_J. exact Hx. }
    split. { intros x Hx. apply FR1. lia. } exact G1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_T : list nat := Eval vm_compute in (BG.kept_list 48 PT.regs0 PT.regs_out0).
Lemma KS_T_ok : BG.kept_ok 48 PT.regs0 PT.regs_out0 KS_T = true. Proof. vm_compute. reflexivity. Qed.

Lemma smT_conc fx R M (sp a b qa : Z) (n : nat) (v8 v9 : word) :
  smctx M sp a b qa n ->
  getr R (reg 2) = Z_to_bv 64 (sp - 16) -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 13) = Z_to_bv 64 (8 * Z.of_nat n) ->
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned v8) -> L5.u64_at RSEGS M (sp - 16) (bv_unsigned v9) ->
  exists fx' R' M', msteps RSEGS (st fx R L2DONE M) (st fx' R' SM_RET M')
    /\ (forall x, In x KS_T -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = v8 /\ getr R' (reg 9) = v9
    /\ (forall x : word, ~ (a + 8 * Z.of_nat n <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C H2 H11 H13 U8 U9. intro_ctx C.
  set (Vf := VAL R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (Vf' := fun k : nat => match k with 8%nat => v8 | 9%nat => v9 | _ => Vf k end).
  set (E := Env Vf' (fun _ => [])).
  assert (ZA0 : forall k, bv_unsigned (Vf k) = VZ R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia).
  assert (ZA : forall k, bv_unsigned (ev E k) = (fun k : nat => match k with 8%nat => bv_unsigned v8 | 9%nat => bv_unsigned v9
             | _ => VZ R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k end) k).
  { intros k. cbn [ev E]. subst Vf'. cbv beta. destruct k as [|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]; try apply ZA0. reflexivity. reflexivity. }
  unfold VZ in ZA.
  assert (HR: regs_ok E PT.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PT.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PT.kn0).
  { unfold know_ok, PT.kn0. L5K.kn_all ZA.
    all: try (replace (sp + -8) with (sp - 8) by lia; exact U8). all: try (replace (sp + -16) with (sp - 16) by lia; exact U9). }
  destruct (PT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PT.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PT.regs0 PT.regs_out0 48 KS_T KS_T_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PT.regs_out0 E' R' 2 Hregs) by lia. cbn [nth PT.regs_out0]. L5K.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT.regs_out0 E' R' 8 Hregs) by lia. cbn [nth PT.regs_out0 edenot]. rewrite <- (proj1 Hag 8%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PT.regs_out0 E' R' 9 Hregs) by lia. cbn [nth PT.regs_out0 edenot]. rewrite <- (proj1 Hag 9%nat) by lia. reflexivity. }
  split. { intros x Hx. apply Hfr. unfold PT.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_regs_preserved R R' :
  (forall i, In i sm_kept -> getr R' (reg i) = getr R (reg i)) ->
  getr R' (reg 2) = getr R (reg 2) -> getr R' (reg 8) = getr R (reg 8) -> getr R' (reg 9) = getr R (reg 9) ->
  regs_preserved R R'.
Proof.
  intros K E2 E8 E9 x Hx. rewrite <- (AX2S.ridx_roundtrip x).
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; first [exact E2 | exact E8 | exact E9 | apply K; cbn; tauto] |]). destruct Hx.
Qed.

Theorem submul_run (fx : FPState) R M (sp a b qa r : Z) (n : nat) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b ->
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 14) = Z_to_bv 64 qa ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  smctx M sp a b qa n ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R SUBMUL M) (st fx' R' r M') /\ submul_post M M' sp a b qa n R R'.
Proof.
  intros H2 H11 H12 H13 H14 H1 [Hr He] C. pose proof C as C0. intro_ctx C.
  (* [comment removed for export] *)
  destruct (smA_conc fx R M sp a b qa n C0 H2 H11 H12 H13 H14) as (fx1 & R1 & M1 & MS1 & K1 & AT1 & U8 & U9 & FR1 & G1).
  pose proof (smctx_grows _ _ _ _ _ _ _ C0 G1) as C1.
  (* [comment removed for export] *)
  destruct (loop1 (n - 0) fx1 R1 M1 sp a b qa n 0 eq_refl C1 AT1 ltac:(lia)) as (fx2 & R2 & M2 & MS2 & K2 & FR2 & G2).
  pose proof (smctx_grows _ _ _ _ _ _ _ C1 G2) as C2.
  assert (U8b: L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (reg 8)))).
  { eapply (L5K.u64_at_keep RSEGS M1 M2). exact FR2. lia. lia. lia. exact U8. }
  assert (U9b: L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (reg 9)))).
  { eapply (L5K.u64_at_keep RSEGS M1 M2). exact FR2. lia. lia. lia. exact U9. }
  (* [comment removed for export] *)
  destruct AT1 as (A2 & _ & _ & A11 & A12 & A13 & A14 & _ & _).
  assert (B2: getr R2 (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite (K2 2%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact A2).
  assert (B11: getr R2 (reg 11) = Z_to_bv 64 a) by (rewrite (K2 11%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact A11).
  assert (B12: getr R2 (reg 12) = Z_to_bv 64 b) by (rewrite (K2 12%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact A12).
  assert (B13: getr R2 (reg 13) = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite (K2 13%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact A13).
  assert (B14: getr R2 (reg 14) = Z_to_bv 64 qa) by (rewrite (K2 14%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact A14).
  assert (B1: getr R2 (reg 1) = Z_to_bv 64 r). { rewrite (K2 1%nat ) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K1 1%nat ) by (apply L5K.in_b; vm_compute; reflexivity). exact H1. }
  (* [comment removed for export] *)
  assert (PACK: forall (fx' : FPState) R' M',
    (forall i, In i sm_kept -> getr R' (reg i) = getr R2 (reg i)) ->
    getr R' (reg 2) = Z_to_bv 64 sp -> getr R' (reg 8) = getr R (reg 8) -> getr R' (reg 9) = getr R (reg 9) ->
    smctx M' sp a b qa n ->
    (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> ~ (qa <= bv_unsigned x < qa + 8) -> M' x = M2 x) -> mem_grows M2 M' ->
    submul_post M M' sp a b qa n R R').
  { intros fx' R' M' K E2 E8 E9 C' FR G.
    assert (KK: forall i, In i sm_kept -> getr R' (reg i) = getr R (reg i)).
    { intros i Hi. rewrite (K i Hi). rewrite (K2 i). apply K1. apply (L5K.incl_b sm_kept KS_A ltac:(vm_compute; reflexivity)); exact Hi.
      apply (L5K.incl_b sm_kept KS_L ltac:(vm_compute; reflexivity)); exact Hi. }
    split. exact KK. split. rewrite E2, H2; reflexivity. split. exact E8. split. exact E9.
    split. { apply kept_regs_preserved. exact KK. rewrite E2, H2; reflexivity. exact E8. exact E9. }
    split. exact C'.
    split. { intros x Hx. rewrite FR. rewrite FR2. apply FR1.
             all: intros Hin.
             apply (Hx (sp - 16, 16)); [left; reflexivity | unfold L5.in_rng; cbn; lia].
             apply (Hx (a, 8 * Z.of_nat n + 8)); [right; left; reflexivity | unfold L5.in_rng; cbn; lia].
             apply (Hx (a, 8 * Z.of_nat n + 8)); [right; left; reflexivity | unfold L5.in_rng; cbn; lia].
             apply (Hx (qa, 8)); [right; right; left; reflexivity | unfold L5.in_rng; cbn; lia]. }
    eapply mem_grows_trans. exact G1. eapply mem_grows_trans. exact G2. exact G. }
  pose proof (br_225f8 fx2 R2 M2) as MB.
  destruct (branch_taken BC_GEU (getr R2 (reg 7)) (getr R2 (reg 28))).
  - (* [comment removed for export] *)
    destruct (smK_conc fx2 R2 M2 sp (getr R (reg 8)) (getr R (reg 9)) Csp (c_spw _ _ _ _ _ _ C2) B2 U8b U9b)
      as (fx3 & R3 & M3 & MS3 & K3 & E2 & E8 & E9 & MM3 & G3).
    pose proof (ret_22654 fx3 R3 M3 r ltac:(rewrite (K3 1%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact B1) Hr He) as MS4.
    exists fx3, R3, M3. split.
    { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB. eapply msteps_trans. exact MS3. exact MS4. }
    apply (PACK fx3 R3 M3). { intros i Hi. apply K3. apply (L5K.incl_b sm_kept KS_K ltac:(vm_compute; reflexivity)); exact Hi. } exact E2. exact E8. exact E9.
    { eapply smctx_grows. exact C2. exact G3. } { intros x _ _. apply MM3. } exact G3.
  - (* [comment removed for export] *)
    destruct (smB_conc fx2 R2 M2 sp a b qa n C2 B2 B11 B12 B13 B14) as (fx3 & R3 & M3 & MS3 & K3 & AT3 & FR3 & G3).
    pose proof (smctx_grows _ _ _ _ _ _ _ C2 G3) as C3.
    destruct (loop2 (n - 0) fx3 R3 M3 sp a b qa n 0 eq_refl C3 AT3 ltac:(lia)) as (fx4 & R4 & M4 & MS4 & K4 & FR4 & G4).
    pose proof (smctx_grows _ _ _ _ _ _ _ C3 G4) as C4.
    destruct AT3 as (D2 & _ & D11 & _ & D13 & _).
    assert (U8d: L5.u64_at RSEGS M4 (sp - 8) (bv_unsigned (getr R (reg 8)))).
    { eapply (L5K.u64_at_keep RSEGS M3 M4). exact FR4. lia. lia. lia. eapply (L5K.u64_at_keep RSEGS M2 M3). exact FR3. lia. lia. lia. exact U8b. }
    assert (U9d: L5.u64_at RSEGS M4 (sp - 16) (bv_unsigned (getr R (reg 9)))).
    { eapply (L5K.u64_at_keep RSEGS M3 M4). exact FR4. lia. lia. lia. eapply (L5K.u64_at_keep RSEGS M2 M3). exact FR3. lia. lia. lia. exact U9b. }
    destruct (smT_conc fx4 R4 M4 sp a b qa n (getr R (reg 8)) (getr R (reg 9)) C4
                ltac:(rewrite (K4 2%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact D2) ltac:(rewrite (K4 11%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact D11)
                ltac:(rewrite (K4 13%nat ) by (apply L5K.in_b; vm_compute; reflexivity); exact D13) U8d U9d)
      as (fx5 & R5 & M5 & MS5 & K5 & E2 & E8 & E9 & FR5 & G5).
    assert (B1': getr R5 (reg 1) = Z_to_bv 64 r).
    { rewrite (K5 1%nat ) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K4 1%nat ) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K3 1%nat ) by (apply L5K.in_b; vm_compute; reflexivity). exact B1. }
    pose proof (ret_22654 fx5 R5 M5 r B1' Hr He) as MS6.
    exists fx5, R5, M5. split.
    { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB.
      eapply msteps_trans. exact MS3. eapply msteps_trans. exact MS4. eapply msteps_trans. exact MS5. exact MS6. }
    apply (PACK fx5 R5 M5).
    { intros i Hi. rewrite (K5 i), (K4 i). apply K3.
      apply (L5K.incl_b sm_kept KS_B ltac:(vm_compute; reflexivity)); exact Hi.
      apply (L5K.incl_b sm_kept KS_L2 ltac:(vm_compute; reflexivity)); exact Hi.
      apply (L5K.incl_b sm_kept KS_T ltac:(vm_compute; reflexivity)); exact Hi. }
    exact E2. exact E8. exact E9. { eapply smctx_grows. exact C4. exact G5. }
    { intros x Ha Hq. rewrite FR5 by lia. rewrite FR4 by lia. apply FR3. exact Hq. }
    eapply mem_grows_trans. exact G3. eapply mem_grows_trans. exact G4. exact G5.
Qed.

(* [comment removed for export] *)
Lemma rl n : (n < 32)%nat -> Z_to_bv 5 (Z.of_nat n) = (Z_to_bv 5 (Z.of_nat n)). Proof. reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.
Lemma r12 : (12%bv : bv 5) = reg 12. Proof. apply bv_eq; reflexivity. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
Lemma r14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq; reflexivity. Qed.

Theorem submul_ok : submul_spec.
Proof.
  intros fx R M model K sp a b qa r n Hh Hl H2 H11 H12 H13 H14 H1 Hra C HK. unfold cfg.
  rewrite r2 in H2. rewrite r1 in H1. rewrite r11 in H11. rewrite r12 in H12. rewrite r13 in H13. rewrite r14 in H14.
  eapply (L5.run_cps RSEGS (fun _ R' M' => submul_post M M' sp a b qa n R R')). exact Hh. exact Hl.
  - exact (submul_run fx R M sp a b qa r n H2 H11 H12 H13 H14 H1 Hra C).
  - intros fx' R' M' HP. apply HK. exact HP.
Qed.
End SCFG_2.


End L5SM.

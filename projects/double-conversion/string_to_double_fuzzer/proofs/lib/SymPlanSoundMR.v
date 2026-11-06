(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibMainRet
  MallocDefs RefEnframeBase.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound SymPlanSoundH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Context {fx : PropExec.FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma call_mainret_sound' : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_main_ret P0 -> call_mainret P0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hpc Hn HK.
  unfold call_mainret in Hn.
  destruct (reg_lit cs 10) as [[|p|p]|] eqn:H10; try discriminate.
  destruct (fresh_ok nx0 cs) eqn:Hfresh; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn. subst cs'.
  destruct (reg_lit_sound E cs R M model 10 0 HC ltac:(lia) H10) as [R10 _].
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  destruct (main_ret_0 R M (seg_rom RSEGS) R10) as (R' & Hms & G8 & G10 & Goth).
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_main_ret P0)) with (0x326e8%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  set (nx := s_next (c_ss cs)).
  set (E' := ext1 (ext1 E nx (getr R' 1)) (S nx) (getr R' 11)).
  assert (Hag : env_agree nx E E').
  { eapply env_agree_le; [| apply Nat.le_refl].
    split; [|reflexivity]. intros n Hn. unfold E'. cbn [ext1 ev].
    destruct (Nat.eqb_spec n (S nx)); [lia|]. destruct (Nat.eqb_spec n nx); [lia|]. reflexivity. }
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh Hnx0]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv]. apply andb_prop in Hfresh as [Hsv Hkv]. apply Nat.leb_le in Hnx0.
  fold nx in Hnx0, Hslv, Hmv, Hsv, Hkv.
  specialize (HK E' R' M ltac:(eapply env_agree_le; [exact Hag | exact (max1_le_l _ _ Hnx0)])).
  unfold cfg_of in HK. cbn [pc c_ss s_pc] in HK.
  replace (Z_to_bv 64 (t_main_join P0)) with (0x32768%bv : word) in HK by (apply bv_eq; reflexivity).
  apply HK. clear HK.
  destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL HLIB].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
    pose proof (ridx_range r) as Hrr.
    destruct (Nat.eqb_spec (ridx r) 11) as [E11|N11].
    { rewrite (reg_of_ridx r 11 E11). cbn [edenot]. unfold E'. rewrite ext1_at.
      replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
    destruct (Nat.eqb_spec (ridx r) 10) as [E10|N10].
    { rewrite (reg_of_ridx r 10 E10). cbn [edenot].
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10. reflexivity. }
    destruct (Nat.eqb_spec (ridx r) 8) as [E8|N8].
    { rewrite (reg_of_ridx r 8 E8). cbn [edenot].
      replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G8. reflexivity. }
    destruct (Nat.eqb_spec (ridx r) 1) as [E1|N1].
    { rewrite (reg_of_ridx r 1 E1). cbn [edenot]. unfold E'. cbn [ext1 ev]. fold nx.
      destruct (Nat.eqb_spec nx (S nx)); [lia|]. rewrite Nat.eqb_refl.
      replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
    rewrite Goth; [| intros X; subst r; apply N1; reflexivity | intros X; subst r; apply N8; reflexivity
                   | intros X; subst r; apply N10; reflexivity | intros X; subst r; apply N11; reflexivity].
    pose proof (HR r) as X. unfold sr_get in X.
    destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
    rewrite X. apply (edenot_agree nx); [exact Hag|].
    rewrite <- expr_vars_lt_eq.
    clear -Hsv Hrr. revert Hsv. generalize (ridx r) as i. generalize (s_regs (c_ss cs)) as sr.
    induction sr as [|e t IH]; intros i Hsv; [destruct i; reflexivity|].
    cbn [SP.sr_vars_lt] in Hsv. apply andb_prop in Hsv as [H1 H2]. destruct i; [exact H1 | apply IH; exact H2].
  - eapply know_ok_ext; [exact Hag | exact Hkv | exact HKN].
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - eapply vm_ok_ext; [exact Hag | exact Hmv | | exact HV]. all: try (unfold SP0V; lia).   (* [comment removed for export] *)
  - eapply slots_ok_ext; [exact Hag | exact Hslv | exact HSL].
  - exact HLIB.
Qed.

Theorem call_mainret_ok_fx : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_main_ret P0 -> call_mainret P0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof. exact call_mainret_sound'. Qed.

End NX0.

(* [comment removed for export] *)
Theorem call_mainret_ok : forall nx0, mainret_sound_stmt nx0.
Proof. intros nx0  fx. exact (call_mainret_ok_fx nx0 ). Qed.

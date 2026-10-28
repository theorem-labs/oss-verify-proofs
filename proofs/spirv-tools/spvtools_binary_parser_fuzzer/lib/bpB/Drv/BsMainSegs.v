(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BAmb BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BHoare BFrame BShapeLaws BpecConsts BMmapSim BAllocSim BFileSim BAgentLib BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BSymDriveH4 BLibKnowFrame BSymAux BSpec BLibTail BeapCeil BazyRestrict BazySR BainDefs BainArith BainWalk_defs BainSegs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BRefExitBase BsDrvRun BsDrvDefs BsTRSegs BsMainWalk_defs.

Import ListNotations.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition caE := Eval vm_compute in carryM rE aknL.
Definition caN := Eval vm_compute in carryM rN aknL.
Definition caN' := Eval vm_compute in carryM rN' aknL.
Definition caR := Eval vm_compute in carryM rR aknL.
Definition caR' := Eval vm_compute in carryM rR' aknL.
Definition caL5a := Eval vm_compute in carryM rL5a aknL.
Definition caL5b := Eval vm_compute in carryM rL5b aknL.
Definition caL5c := Eval vm_compute in carryM rL5c aknL.
Definition caMa := Eval vm_compute in carryM rMa aknL.
Definition caMb := Eval vm_compute in carryM rMb aknL.
Definition caGb := Eval vm_compute in carryM rGb aknL.
Definition caGr := Eval vm_compute in carryM rGr aknL.
Definition caL2 := Eval vm_compute in carryM rL2 aknL.
Definition caL3 := Eval vm_compute in carryM rL3 aknL.
Definition caHs := Eval vm_compute in carryM rHs knH.
Definition caHo := Eval vm_compute in carryM rHo knH.
Definition caHk := Eval vm_compute in carryM rHk knH.
Definition caI := Eval vm_compute in carryM rI aknL.
Definition caX := Eval vm_compute in carryM rX knX.
Lemma acovE : log_covered regL (s_log (fst (fst rE))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovN : log_covered regL (s_log (fst (fst rN))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovN' : log_covered regL (s_log (fst (fst rN'))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovR : log_covered regL (s_log (fst (fst rR))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovR' : log_covered regL (s_log (fst (fst rR'))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovL5a : log_covered regL (s_log (fst (fst rL5a))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovL5b : log_covered regL (s_log (fst (fst rL5b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovL5c : log_covered regL (s_log (fst (fst rL5c))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovMa : log_covered regL (s_log (fst (fst rMa))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovMb : log_covered regL (s_log (fst (fst rMb))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovGb : log_covered regL (s_log (fst (fst rGb))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovGr : log_covered regL (s_log (fst (fst rGr))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovL2 : log_covered regL (s_log (fst (fst rL2))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovL3 : log_covered regL (s_log (fst (fst rL3))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovHs : log_covered regL (s_log (fst (fst rHs))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovHo : log_covered regL (s_log (fst (fst rHo))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovHk : log_covered regL (s_log (fst (fst rHk))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma acovI : log_covered regL (s_log (fst (fst rI))) = true. Proof. vm_compute. reflexivity. Qed.

Ltac run_segM scr pc sr kn nx r c E M R :=
  lazymatch goal with
  | HVx : BsIface.as_VIS ?Hh ?sx ?msFx = _, DLx : asan_driver_laws ?Hh |- @realizes _ _ (mkCfg ?msFx ?mox) _ =>
    eapply (drv_run_lf Hh DLx sx FUELM STOPSAM scr pc sr kn nx (fst (fst r)) (snd (fst r)) (snd r)
              (fst (fst c)) (snd (fst c)) (snd c) E M R msFx mox);
    [ vm_cast_no_check (@eq_refl _ r) | vm_cast_no_check (@eq_refl _ c) | | | | scs_nil | | | ]
  end.

Section Blocks.
  Context {fx : DFP}.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.
  Variable sp0 : word.
  Hypothesis Hvsp : valid_sp sp0.
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let rom := seg_rom asegs.

  Lemma aknL_ok : forall v regs mem,
    v_sp0 v = sp0 ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
    aro_none mem -> arelro_none mem ->
    know_ok RSEGS (MENV v regs) mem aknL.
  Proof.
    intros v regs mem Ev Hstk Hro Hrel. pose proof Hvsp as (Hlo & Hhi & Hal). unfold sp_window_lo, sp_window_hi in *.
    destruct v as [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13]. cbn in Ev. subst v0.
    unfold aknL. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. try rewrite ev0. exact Hal.
    - apply krange_intro. cbn [edenot]. try rewrite ev0. cbn. lia.
    - cbn [kentry_ok]. split; [apply flat_intro; cbn; unfold MSTK; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app v_sp0].
      pose proof (Hstk (Z_to_bv 64 (bv_unsigned sp0 + (-128 - MSTK) + d)) m) as Hs.
      rewrite !u_small in Hs by (unfold MSTK in *; lia). apply Hs; unfold MSTK in *; lia.
    - apply kimg_intro; [lia|lia|exact Hro].
    - apply kimg_intro; [lia|lia|exact Hrel].
  Qed.

  Lemma aknL_ra_ok : forall v regs mem (ra : Z),
    v_sp0 v = sp0 ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
    aro_none mem -> arelro_none mem -> (0 <= ra < 2 ^ 64)%Z ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ra)) ->
    know_ok RSEGS (MENV v regs) mem (KWord (SA (EVar 0) (-136)) 8 (ELit ra) :: aknL).
  Proof.
    intros v regs mem ra Ev Hstk Hro Hrel Hra Hrd. pose proof Hvsp as (Hlo & Hhi & _). unfold sp_window_lo, sp_window_hi in *.
    apply Forall_cons; [| apply aknL_ok; assumption].
    eapply (kword_intro RSEGS _ mem (EVar 0) sp0 (-136) 8 (ELit ra) (Z_to_bv 64 ra));
      [cbn; rewrite Ev; reflexivity | reflexivity | lia | lia | lia | lia |].
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia. exact Hrd.
  Qed.

  Definition abase_regs (regs : bvmap 5 word) (pp : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr regs 4 = Z_to_bv 64 0x6c5858 /\ getr regs 8 = Z_to_bv 64 2
    /\ getr regs 18 = pp /\ getr regs 20 = Z_to_bv 64 3.

  Definition albase_regs (regs : bvmap 5 word) (pp : word) : Prop :=
    abase_regs regs pp /\ getr regs 22 = Z_to_bv 64 0x6b3690.

  Ltac unset_v := repeat match goal with w := MV _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => subst w end.
  Ltac fin_reg HR' r :=
    unset_v; regv HR' r; unset_v; cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1];
    first [ reflexivity | assumption
          | rewrite ev_junk by lia; first [assumption | symmetry; assumption | reflexivity]
          | ed_lin idtac; unorm; first [reflexivity | f_equal; lia | apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; f_equal; lia] ].
  Ltac sc_open :=
    lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end;
    unset_v; repeat apply Forall_cons; try apply Forall_nil;
    cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1]; ed_lin idtac; unorm.
  Ltac fin_base HR' := repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg)].
  Ltac fin_lbase HR' := split; [fin_base HR' | fin_reg HR' (22:reg)].

  Ltac mk_frame v regs mem cov EQM LF FR :=
    pose proof (log_covered_frame (MENV v regs) mem regL _ cov (regL_flat v regs ltac:(cbn; lia)) LF) as FR;
    rewrite <- EQM, (regL_denot v regs) in FR by (cbn; lia).

  Lemma mstk_after : forall mem mem' rs, frame_mod mem mem' rs ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK.
  Proof. intros mem mem' rs FM Hstk a m Ha Hm. eapply frame_mod_store_ok; [exact FM|]. apply Hstk; assumption. Qed.

  Definition an_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) : Prop :=
    albase_regs regs pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 cap /\ getr regs 23 = Z_to_bv 64 A.

  Lemma aseg_E : forall s msF mo regs mem (pp : word) (A : Z) K,
    abase_regs regs pp -> getr regs 10 = Z_to_bv 64 A -> (0 < A < 2 ^ 64)%Z -> getr regs 21 = Z_to_bv 64 0x10000 ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe8480) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        an_regs regs' pp A 0 0x10000 ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8448) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A K (R2 & R4 & R8 & R18 & R20) R10 HA R21 Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srE0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM scrE 0xe8448%Z srE0 aknL 46%nat rE caE (MENV v regs) mem regs; [ exact HR | exact HKn | | exact HV | exact HAK | ].
    { sc_open. unfold bv_eqb. unorm. destruct (Z.eqb_spec A 0); [lia|reflexivity]. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rE))) with 0xe8480%Z. change (s_regs (fst (fst rE))) with srE in HR'.
    mk_frame v regs mem acovE EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [| exact FR | eapply mstk_after; [exact FR | exact Hstk]].
    split; [fin_lbase HR'|]. repeat split; [fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg)].
  Qed.

  Definition aloop_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) : Prop :=
    albase_regs regs pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 cap /\ getr regs 9 = Z_to_bv 64 A.

  Definition aread_call_regs (regs : bvmap 5 word) (pp : word) (A len cap cnt : Z) : Prop :=
    getr regs 1 = Z_to_bv 64 0xe84dc /\ getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr regs 4 = Z_to_bv 64 0x6c5858
    /\ getr regs 8 = Z_to_bv 64 2 /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 10 = Z_to_bv 64 3
    /\ getr regs 11 = Z_to_bv 64 0x6b3690 /\ getr regs 12 = Z_to_bv 64 cnt
    /\ getr regs 18 = pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 20 = Z_to_bv 64 3 /\ getr regs 21 = Z_to_bv 64 cap
    /\ getr regs 22 = Z_to_bv 64 0x6b3690.

  Ltac read_post HR' := repeat split; try (fin_reg HR' (1:reg)); try (fin_reg HR' (2:reg));
        try (fin_reg HR' (4:reg)); try (fin_reg HR' (8:reg)); try (fin_reg HR' (9:reg)); try (fin_reg HR' (10:reg));
        try (fin_reg HR' (11:reg)); try (fin_reg HR' (12:reg)); try (fin_reg HR' (18:reg));
        try (fin_reg HR' (19:reg)); try (fin_reg HR' (20:reg)); try (fin_reg HR' (21:reg)); try (fin_reg HR' (22:reg)); fail "post regs".

  Lemma aseg_N : forall s msF mo regs mem (pp : word) (A len cap : Z) K,
    an_regs regs pp A len cap -> (0 <= len < cap)%Z -> (cap < 2 ^ 47)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xa36a4) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        aread_call_regs regs' pp A len cap (Z.min (cap - len) 65536) ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8480) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap K (((R2 & R4 & R8 & R18 & R20) & R22) & R19 & R21 & R23) Hlen Hcap Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srN0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    assert (POST : forall (r : sym_state * list sidecond * scripts) (c : list kentry * list sidecond * list bool) (cov : log_covered regL (s_log (fst (fst r))) = true) R' M',
      regs_ok (MENV v regs) (s_regs (fst (fst r))) R' ->
      M' = mem_denot (MENV v regs) mem (s_log (fst (fst r))) -> log_flat (MENV v regs) (s_log (fst (fst r))) ->
      ((cap - len < 65536)%Z /\ s_regs (fst (fst r)) = srN \/ (65536 <= cap - len)%Z /\ s_regs (fst (fst r)) = srN') ->
      aread_call_regs R' pp A len cap (Z.min (cap - len) 65536) /\ frame_mod mem M' (regL_w sp0)
      /\ stk_ok RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { intros r c cov R' M' HR' EQM LF Hsr.
      mk_frame v regs mem cov EQM LF FR.
      split; [|split; [exact FR| eapply mstk_after; [exact FR | exact Hstk]]].
      destruct Hsr as [[Hs Esr]|[Hb Esr]]; rewrite Esr in HR'; [rewrite Z.min_l by lia | rewrite Z.min_r by lia].
      all: read_post HR'. }
    destruct (Z_lt_le_dec (cap - len) 65536) as [Hs|Hb].
    - run_segM scrN 0xe8480%Z srN0 aknL 46%nat rN caN (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_lt. lia. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rN))) with 0xa36a4%Z in HV'.
      destruct (POST rN caN acovN R' M' HR' EQM LF ltac:(left; split; [exact Hs|reflexivity])) as (P1 & P2 & P3).
      exact (HK R' M' msF' mo' HV' HA' SB' P1 P2 P3).
    - run_segM scrN' 0xe8480%Z srN0 aknL 46%nat rN' caN' (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_ge. lia. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rN'))) with 0xa36a4%Z in HV'.
      destruct (POST rN' caN' acovN' R' M' HR' EQM LF ltac:(right; split; [exact Hb|reflexivity])) as (P1 & P2 & P3).
      exact (HK R' M' msF' mo' HV' HA' SB' P1 P2 P3).
  Qed.

  Lemma aseg_R : forall s msF mo regs mem (pp : word) (A len cap : Z) K,
    aloop_regs regs pp A len cap -> (0 <= len < cap)%Z -> (cap < 2 ^ 47)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xa36a4) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        aread_call_regs regs' pp A len cap (Z.min (cap - len) 65536) ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe84c0) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap K (((R2 & R4 & R8 & R18 & R20) & R22) & R19 & R21 & R9) Hlen Hcap Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srR0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    assert (POST : forall (r : sym_state * list sidecond * scripts) (c : list kentry * list sidecond * list bool) (cov : log_covered regL (s_log (fst (fst r))) = true) R' M',
      regs_ok (MENV v regs) (s_regs (fst (fst r))) R' ->
      M' = mem_denot (MENV v regs) mem (s_log (fst (fst r))) -> log_flat (MENV v regs) (s_log (fst (fst r))) ->
      ((cap - len < 65536)%Z /\ s_regs (fst (fst r)) = srR \/ (65536 <= cap - len)%Z /\ s_regs (fst (fst r)) = srR') ->
      aread_call_regs R' pp A len cap (Z.min (cap - len) 65536) /\ frame_mod mem M' (regL_w sp0)
      /\ stk_ok RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { intros r c cov R' M' HR' EQM LF Hsr.
      mk_frame v regs mem cov EQM LF FR.
      split; [|split; [exact FR| eapply mstk_after; [exact FR | exact Hstk]]].
      destruct Hsr as [[Hs Esr]|[Hb Esr]]; rewrite Esr in HR'; [rewrite Z.min_l by lia | rewrite Z.min_r by lia].
      all: read_post HR'. }
    destruct (Z_lt_le_dec (cap - len) 65536) as [Hs|Hb].
    - run_segM scrR 0xe84c0%Z srR0 aknL 46%nat rR caR (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_lt. lia. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rR))) with 0xa36a4%Z in HV'.
      destruct (POST rR caR acovR R' M' HR' EQM LF ltac:(left; split; [exact Hs|reflexivity])) as (P1 & P2 & P3).
      exact (HK R' M' msF' mo' HV' HA' SB' P1 P2 P3).
    - run_segM scrR' 0xe84c0%Z srR0 aknL 46%nat rR' caR' (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_ge. lia. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rR'))) with 0xa36a4%Z in HV'.
      destruct (POST rR' caR' acovR' R' M' HR' EQM LF ltac:(right; split; [exact Hb|reflexivity])) as (P1 & P2 & P3).
      exact (HK R' M' msF' mo' HV' HA' SB' P1 P2 P3).
  Qed.

  Definition aread_ret_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) (res : word) : Prop :=
    albase_regs regs pp /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 10 = res /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 cap.

  Lemma aseg_L5a : forall s msF mo regs mem (pp : word) (A len cap n : Z) K,
    aread_ret_regs regs pp A len cap (Z_to_bv 64 n) -> (0 < n < 2 ^ 62)%Z -> (0 <= len < 2 ^ 62)%Z -> (0 < A)%Z -> (A + len < 2 ^ 62)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xb8580) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        albase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xe8474 -> getr regs' 9 = Z_to_bv 64 A ->
        getr regs' 10 = Z_to_bv 64 (A + len) -> getr regs' 11 = Z_to_bv 64 0x6b3690 -> getr regs' 12 = Z_to_bv 64 n ->
        getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 cap -> getr regs' 23 = Z_to_bv 64 n ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe84dc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap n K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R10 & R19 & R21) Hn Hlen HA HAl Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL50 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM scrL5a 0xe84dc%Z srL50 aknL 46%nat rL5a caL5a (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { sc_open.
      - unfold bv_eqb. unorm. destruct (Z.eqb_spec n 0); [lia|reflexivity].
      - rewrite lts_ZZ by lia. cbn [negb]. destruct (Z.ltb_spec n 0); [lia|reflexivity]. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rL5a))) with 0xb8580%Z in HV'. change (s_regs (fst (fst rL5a))) with srL5a in HR'.
    mk_frame v regs mem acovL5a EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_reg HR' (12:reg)
              | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg) | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Lemma aseg_L5b : forall s msF mo regs mem (pp : word) (A len cap : Z) K,
    aread_ret_regs regs pp A len cap (Z_to_bv 64 0) ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x177ad8) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        getr regs' 1 = Z_to_bv 64 0x17d450 -> getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 144) -> getr regs' 4 = Z_to_bv 64 0x6c5858 ->
        getr regs' 8 = Z_to_bv 64 2 -> getr regs' 9 = Z_to_bv 64 A -> getr regs' 10 = Z_to_bv 64 3 -> getr regs' 17 = Z_to_bv 64 57 ->
        getr regs' 18 = pp -> getr regs' 19 = Z_to_bv 64 len -> getr regs' 20 = Z_to_bv 64 3 -> getr regs' 21 = Z_to_bv 64 cap ->
        getr regs' 22 = Z_to_bv 64 0x6b3690 ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe84f0)) ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe84dc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R10 & R19 & R21) Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL50z regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM noscr 0xe84dc%Z srL50z aknL 46%nat rL5b caL5b (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HAK |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rL5b))) with 0x177ad8%Z in HV'. change (s_regs (fst (fst rL5b))) with srL5b in HR'.
    mk_frame v regs mem acovL5b EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_reg HR' (1:reg) | fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg)
              | fin_reg HR' (17:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg) | fin_reg HR' (21:reg) | fin_reg HR' (22:reg)
              | exact FR | eapply mstk_after; [exact FR | exact Hstk] |].
    pose proof (kread_rdn RSEGS (MENV v regs) M' (fst (fst caL5b)) (EVar 0) (-136) 8 (ELit 0xe84f0) HK' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
                  ltac:(apply flat_intro; cbn; lia)) as Hrd.
    unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app v_sp0] in Hrd.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in Hrd by lia. exact Hrd.
  Qed.

  Lemma aseg_L5c : forall s msF mo regs mem (pp : word) (A len cap : Z) K,
    aread_ret_regs regs pp A len cap (Z_to_bv 64 (2 ^ 64 - 1)) ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe8620) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        abase_regs regs' pp -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe84dc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R10 & R19 & R21) Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL50e regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM noscr 0xe84dc%Z srL50e aknL 46%nat rL5c caL5c (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HAK |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rL5c))) with 0xe8620%Z in HV'. change (s_regs (fst (fst rL5c))) with srL5c in HR'.
    mk_frame v regs mem acovL5c EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_base HR' | fin_reg HR' (9:reg) | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Definition am_regs (regs : bvmap 5 word) (pp : word) (A len cap n : Z) : Prop :=
    albase_regs regs pp /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 cap
    /\ getr regs 23 = Z_to_bv 64 n.

  Lemma aseg_Ma : forall s msF mo regs mem (pp : word) (A len cap n : Z) K,
    am_regs regs pp A len cap n -> (0 <= len)%Z -> (0 <= n)%Z -> (len + n < 2 ^ 63)%Z -> (0 <= cap < 2 ^ 63)%Z -> (len + n <> cap)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe8480) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        an_regs regs' pp A (len + n) cap -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8474) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap n K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hl Hn Hln Hcap Hne Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srM0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM scrMa 0xe8474%Z srM0 aknL 46%nat rMa caMa (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { sc_open. unfold bv_eqb. unorm. destruct (Z.eqb_spec (len + n) cap); [lia|reflexivity]. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rMa))) with 0xe8480%Z in HV'. change (s_regs (fst (fst rMa))) with srMa in HR'.
    mk_frame v regs mem acovMa EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [| fin_reg HR' (9:reg) | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
    split; [fin_lbase HR'|]. repeat split; [fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg)].
  Qed.

  Definition ag_regs (regs : bvmap 5 word) (pp : word) (A len : Z) : Prop :=
    albase_regs regs pp /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 len
    /\ getr regs 23 = Z_to_bv 64 A.

  Lemma aseg_Mb : forall s msF mo regs mem (pp : word) (A len cap n : Z) K,
    am_regs regs pp A len cap n -> (0 <= len)%Z -> (0 <= n)%Z -> (0 <= cap < 2 ^ 63)%Z -> (len + n = cap)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe8488) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        ag_regs regs' pp A cap ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8474) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap n K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hl Hn Hcap Heq Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srM0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM scrMb 0xe8474%Z srM0 aknL 46%nat rMb caMb (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { sc_open. unfold bv_eqb. unorm. rewrite <- Heq, Z.eqb_refl. reflexivity. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rMb))) with 0xe8488%Z in HV'. change (s_regs (fst (fst rMb))) with srMb in HR'.
    mk_frame v regs mem acovMb EQM LF FR.
    subst cap.
    apply (HK _ _ _ _ HV' HA' SB'); [| exact FR | eapply mstk_after; [exact FR | exact Hstk]].
    split; [fin_lbase HR'|]. repeat split; [fin_reg HR' (9:reg) | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg)].
  Qed.

  Lemma aseg_Gb : forall s msF mo regs mem (pp : word) (A len : Z) K,
    ag_regs regs pp A len -> (0 <= len < 67108864)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xba108) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        albase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xe849c -> getr regs' 9 = Z_to_bv 64 A -> getr regs' 10 = Z_to_bv 64 (2 * len) ->
        getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 (2 * len) -> getr regs' 23 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8488) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hlen Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srG0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM scrGb 0xe8488%Z srG0 aknL 46%nat rGb caGb (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { sc_open.
        rewrite alu_srl. unfold v_srl, bv_eqb. unorm. change (26 mod 64)%Z with 26%Z.
      rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rGb))) with 0xba108%Z in HV'. change (s_regs (fst (fst rGb))) with srGb in HR'.
    mk_frame v regs mem acovGb EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (19:reg) | fin_reg HR' (21:reg)
              | fin_reg HR' (23:reg) | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Lemma aseg_Gr : forall s msF mo regs mem (pp : word) (A len : Z) K,
    ag_regs regs pp A len -> (67108864 <= len < 2 ^ 62)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe863c) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        abase_regs regs' pp -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8488) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hlen Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srG0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM scrGr 0xe8488%Z srG0 aknL 46%nat rGr caGr (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { sc_open.
      rewrite alu_srl. unfold v_srl, bv_eqb. unorm. change (26 mod 64)%Z with 26%Z.
      assert (Hq : (0 <= Z.shiftr len 26 < 2 ^ 64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split;
        [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      unorm. rewrite Z.shiftr_div_pow2 in * by lia. cbn [negb].
      destruct (Z.eqb_spec (len / 2 ^ 26) 0) as [E|E]; [|reflexivity].
      exfalso. assert (2 ^ 26 <= len)%Z by lia. pose proof (Z.div_le_mono (2^26) len (2^26) ltac:(lia) ltac:(lia)) as Hd.
      rewrite Z.div_same in Hd by lia. lia. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rGr))) with 0xe863c%Z in HV'. change (s_regs (fst (fst rGr))) with srGr in HR'.
    mk_frame v regs mem acovGr EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_base HR' | fin_reg HR' (9:reg) | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Lemma aseg_L2 : forall s msF mo regs mem (pp : word) (A len cap A2 : Z) K,
    albase_regs regs pp -> getr regs 10 = Z_to_bv 64 A2 -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
    getr regs 9 = Z_to_bv 64 A -> getr regs 23 = Z_to_bv 64 A -> (0 < A2 < 2 ^ 64)%Z -> (0 < len < 2 ^ 64)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xb8580) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        albase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xe84b8 -> getr regs' 9 = Z_to_bv 64 A2 ->
        getr regs' 10 = Z_to_bv 64 A2 -> getr regs' 11 = Z_to_bv 64 A -> getr regs' 12 = Z_to_bv 64 len ->
        getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 cap -> getr regs' 23 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe849c) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap A2 K ((R2 & R4 & R8 & R18 & R20) & R22) R10 R19 R21 R9 R23 HA2 Hlen Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 A2) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL20 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM scrL2 0xe849c%Z srL20 aknL 46%nat rL2 caL2 (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { sc_open.
      - unfold bv_eqb. unorm. destruct (Z.eqb_spec len 0); [lia|reflexivity].
      - unfold bv_eqb. unorm. destruct (Z.eqb_spec A2 0); [lia|reflexivity]. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rL2))) with 0xb8580%Z in HV'. change (s_regs (fst (fst rL2))) with srL2 in HR'.
    mk_frame v regs mem acovL2 EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_reg HR' (12:reg)
              | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg) | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Lemma aseg_L3 : forall s msF mo regs mem (pp : word) (A len cap A2 : Z) K,
    albase_regs regs pp -> getr regs 9 = Z_to_bv 64 A2 -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
    getr regs 23 = Z_to_bv 64 A ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xba104) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        albase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xe84c0 -> getr regs' 9 = Z_to_bv 64 A2 ->
        getr regs' 10 = Z_to_bv 64 A -> getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 cap ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe84b8) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap A2 K ((R2 & R4 & R8 & R18 & R20) & R22) R9 R19 R21 R23 Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 A2) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL30 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM noscr 0xe84b8%Z srL30 aknL 46%nat rL3 caL3 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HAK |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rL3))) with 0xba104%Z in HV'. change (s_regs (fst (fst rL3))) with srL3 in HR'.
    mk_frame v regs mem acovL3 EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | exact FR
              | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Lemma aseg_I : forall s msF mo regs mem (pp : word) (A : Z) (status : word) K,
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 8 = status ->
    getr regs 9 = Z_to_bv 64 A ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xba104) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs' 4 = Z_to_bv 64 0x6c5858 -> getr regs' 8 = status ->
        getr regs' 1 = Z_to_bv 64 0xe85f0 -> getr regs' 9 = Z_to_bv 64 A -> getr regs' 10 = Z_to_bv 64 A ->
        (forall r : reg, In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r) ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe85e8) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A status K R2 R4 R8 R9 Hstk Hro Hrel HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) (getr regs 18) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srI0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem aknL) by (apply aknL_ok; subst v; try assumption; reflexivity).
    run_segM noscr 0xe85e8%Z srI0 aknL 46%nat rI caI (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HAK |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rI))) with 0xba104%Z in HV'. change (s_regs (fst (fst rI))) with srI in HR'.
    mk_frame v regs mem acovI EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg)
              | | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
    intros rr Hrr. cbn [In] in Hrr.
    destruct Hrr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
      [fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg) | fin_reg HR' (21:reg) | fin_reg HR' (22:reg)
      | fin_reg HR' (23:reg) | fin_reg HR' (24:reg) | fin_reg HR' (25:reg) | fin_reg HR' (26:reg) | fin_reg HR' (27:reg)].
  Qed.

  Definition amframe (M : word -> option byte) : Prop :=
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x164cb0))
    /\ forall i, (i < 8)%nat -> exists w : word,
         rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 120 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 w).

  Lemma aseg_X : forall s msF mo regs mem (status : word) K,
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 8 = status ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem -> amframe mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x165478) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) -> getr regs' 4 = Z_to_bv 64 0x6c5858 -> getr regs' 10 = status ->
        getr regs' 1 = Z_to_bv 64 0x164cb4 ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe85f0) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem status K R2 R4 R8 Hstk Hro Hrel [MF MS] HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct (MS 0%nat ltac:(lia)) as [w0 W0]. destruct (MS 1%nat ltac:(lia)) as [w1 W1]. destruct (MS 2%nat ltac:(lia)) as [w2 W2].
    destruct (MS 3%nat ltac:(lia)) as [w3 W3]. destruct (MS 4%nat ltac:(lia)) as [w4 W4]. destruct (MS 5%nat ltac:(lia)) as [w5 W5].
    destruct (MS 6%nat ltac:(lia)) as [w6 W6]. destruct (MS 7%nat ltac:(lia)) as [w7 W7].
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add] in W0, W1, W2, W3, W4, W5, W6, W7.
    set (v := MV sp0 (Z_to_bv 64 0) (getr regs 18) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) w0 w1 w2 w3 w4 w5 w6 w7).
    assert (HR : regs_ok (MENV v regs) srX0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knX).
    { unfold knX. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [| apply aknL_ok; subst v; try assumption; reflexivity].
      repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      all: lazymatch goal with |- kentry_ok _ _ _ (KWord (SA (EVar 0) ?k) 8 ?e) =>
             eapply (kword_intro RSEGS _ mem (EVar 0) sp0 k 8 e); [reflexivity | subst v; reflexivity | lia | lia | lia | lia |];
             first [ replace (bv_unsigned sp0 + k)%Z with (bv_unsigned sp0 - (- k))%Z by lia; cbn [Z.opp Pos.succ]; assumption
                   | match goal with W : rdn _ _ (Z_to_bv 64 ?a) 8 = Some (word_to_le_bytes 8 ?w) |- rdn _ _ (Z_to_bv 64 ?b) 8 = Some (word_to_le_bytes 8 ?w) =>
                       replace b with a by lia; exact W end ]
           end. }
    run_segM noscr 0xe85f0%Z srX0 knX 46%nat rX caX (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HAK |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rX))) with 0x165478%Z in HV'. change (s_regs (fst (fst rX))) with srX in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply (HK _ _ _ HV' HA' SB'); [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (10:reg) | fin_reg HR' (1:reg)].
  Qed.

  Definition aclose_ret_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) : Prop :=
    getr regs 1 = Z_to_bv 64 0x17d450 /\ getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144) /\ getr regs 4 = Z_to_bv 64 0x6c5858
    /\ getr regs 8 = Z_to_bv 64 2 /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 10 = Z_to_bv 64 0
    /\ getr regs 18 = pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 20 = Z_to_bv 64 3 /\ getr regs 21 = Z_to_bv 64 cap.

  Definition abuf_bytes (mem : word -> option byte) (A : Z) (data : list byte) : Prop :=
    forall i, (i < length data)%nat -> rdn RSEGS mem (Z_to_bv 64 (A + Z.of_nat i)) 1 = Some [nth i data (Z_to_bv 8 0)].

  Lemma ahdr_b_range : forall data i, (0 <= hdr_b data i < 256)%Z.
  Proof.
    intros data i. unfold hdr_b. pose proof (bv_unsigned_in_range 8 (nth i data (Z_to_bv 8 0))) as Hr.
    unfold bv_modulus in Hr. cbn in Hr. lia.
  Qed.

  Lemma ahdr_reads : forall v regs mem (A : Z) data M',
    v_A v = Z_to_bv 64 A -> v_b0 v = Z_to_bv 64 (hdr_b data 0) -> v_b1 v = Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)) ->
    (2 <= length data)%nat -> (0 < A)%Z -> (A + Z.of_nat (length data) < 2 ^ 47)%Z ->
    abuf_bytes mem A data -> (forall a : word, (A <= bv_unsigned a < A + Z.of_nat (length data))%Z -> M' a = mem a) ->
    sc_denot RSEGS M' (MENV v regs) (SCReadBase (SA (EVar 3) 0) 1 false (EVar 12))
    /\ sc_denot RSEGS M' (MENV v regs) (SCFlat (SA (EVar 3) 0) (ELit 1))
    /\ sc_denot RSEGS M' (MENV v regs) (SCReadBase (SA (EVar 3) 1) 1 true (EVar 13))
    /\ sc_denot RSEGS M' (MENV v regs) (SCFlat (SA (EVar 3) 1) (ELit 1)).
  Proof.
    intros v regs mem A data M' HA Hb0 Hb1 Hl HA0 HAh HB HM.
    assert (RD : forall i, (i < length data)%nat -> rdn RSEGS M' (Z_to_bv 64 (A + Z.of_nat i)) 1 = Some [nth i data (Z_to_bv 8 0)]).
    { intros i Hi. rewrite (rdn_ext RSEGS 1 M' mem); [apply HB; exact Hi | unorm; lia |].
      intros x Hx. apply HM. revert Hx. unorm. intros Hx. lia. }
    cbn [sc_denot]. unfold adenot, v_addi, flat, estart, elenZ. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app].
    rewrite HA, Hb0, Hb1. unorm. repeat split; try lia.
    - exists [nth 0 data (Z_to_bv 8 0)]. split; [rewrite <- (RD 0%nat) by lia; f_equal; f_equal; lia|].
      rewrite bytes_le_to_Z_1. reflexivity.
    - exists [nth 1 data (Z_to_bv 8 0)]. split; [rewrite <- (RD 1%nat) by lia; f_equal; f_equal; lia|].
      rewrite bytes_le_to_Z_1. reflexivity.
  Qed.

  Lemma acfg_expr_val : forall v regs data,
    v_b0 v = Z_to_bv 64 (hdr_b data 0) -> v_b1 v = Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)) ->
    edenot (MENV v regs) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))
    = Z_to_bv 64 (hdr_cfg data).
  Proof.
    intros v regs data Hb0 Hb1. unset_v; cbn [edenot ev MENV mvals vals_ev nth app]. rewrite Hb0, Hb1.
    rewrite alu_or, alu_srl, m_mul. change 144115188075855872%Z with (2 ^ 57)%Z.
    rewrite cfg_word by apply ahdr_b_range. reflexivity.
  Qed.

  Lemma aseg_Hs : forall s msF mo regs mem (pp : word) (A len cap : Z) K,
    aclose_ret_regs regs pp A len cap -> (0 <= len <= 5)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe84f0)) ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe85ac) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        abase_regs regs' pp -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x177adc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A len cap K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21) Hlen Hstk Hro Hrel Hra HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srH0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knH) by (apply aknL_ra_ok; subst v; try assumption; try reflexivity; lia).
    run_segM scrHs 0x177adc%Z srH0 knH 46%nat rHs caHs (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { sc_open. rewrite ltu_ZZ by lia. cbn [negb]. destruct (Z.ltb_spec 5 len); [lia|reflexivity]. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rHs))) with 0xe85ac%Z in HV'. change (s_regs (fst (fst rHs))) with srHs in HR'.
    mk_frame v regs mem acovHs EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_base HR' | fin_reg HR' (9:reg) | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Lemma aseg_Ho : forall s msF mo regs mem (pp : word) (A cap : Z) (data : list byte) K,
    aclose_ret_regs regs pp A (Z.of_nat (length data)) cap -> (6 <= length data)%nat ->
    (Z.of_nat (length data) < 6 + hdr_cfg data)%Z -> (0 < A)%Z -> (A + Z.of_nat (length data) < 2 ^ 47)%Z ->
    (A + Z.of_nat (length data) <= bv_unsigned sp0 - 128 - MSTK \/ bv_unsigned sp0 <= A)%Z ->
    abuf_bytes mem A data ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe84f0)) ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe85c8) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs' 4 = Z_to_bv 64 0x6c5858 -> getr regs' 8 = Z_to_bv 64 2 ->
        getr regs' 20 = Z_to_bv 64 3 -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x177adc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A cap data K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21) Hl6 Hov HA0 HAh Hdisj HB Hstk Hro Hrel Hra HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (hdr_cfg_range data) as Hcr.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 cap) (getr regs 22) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (hdr_b data 0)) (Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)))).
    assert (HR : regs_ok (MENV v regs) srH0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knH) by (apply aknL_ra_ok; subst v; try assumption; try reflexivity; lia).

    run_segM scrHo 0x177adc%Z srH0 knH 46%nat rHo caHo (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      destruct (ahdr_reads v regs mem A data mem eq_refl eq_refl eq_refl ltac:(lia) HA0 HAh HB ltac:(intros; reflexivity)) as (S1 & S2 & S3 & S4).
      repeat apply Forall_cons; try apply Forall_nil; try assumption.
      - cbn [sc_denot branch_taken]. rewrite ed_add, (acfg_expr_val v regs data eq_refl eq_refl), ed_lit, vadd_ZZ.
        unset_v. cbn [edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. apply Z.ltb_lt. lia.
      - unset_v. cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. cbn [negb].
        destruct (Z.ltb_spec 5 (Z.of_nat (length data))); [reflexivity|lia]. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rHo))) with 0xe85c8%Z in HV'. change (s_regs (fst (fst rHo))) with srHo in HR'.
    mk_frame v regs mem acovHo EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (20:reg) | fin_reg HR' (9:reg) | exact FR
              | eapply mstk_after; [exact FR | exact Hstk]].
  Qed.

  Definition atr_call_regs (regs : bvmap 5 word) (A len cfg sb1 : Z) : Prop :=
    getr regs 1 = Z_to_bv 64 0xe8568 /\ getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr regs 4 = Z_to_bv 64 0x6c5858
    /\ getr regs 8 = Z_to_bv 64 (A + 2) /\ getr regs 9 = Z_to_bv 64 A
    /\ getr regs 10 = Z_to_bv 64 (A + 2) /\ getr regs 11 = Z_to_bv 64 cfg
    /\ getr regs 12 = Z_to_bv 64 (A + 2 + cfg + 4) /\ getr regs 13 = Z_to_bv 64 (len - 6 - cfg)
    /\ getr regs 18 = Z_to_bv 64 cfg /\ getr regs 19 = Z_to_bv 64 (A + 2 + cfg + 4) /\ getr regs 20 = Z_to_bv 64 (len - 6 - cfg)
    /\ getr regs 21 = Z_to_bv 64 sb1.

  Lemma aseg_Hk : forall s msF mo regs mem (pp : word) (A cap : Z) (data : list byte) K,
    aclose_ret_regs regs pp A (Z.of_nat (length data)) cap ->
    (6 + hdr_cfg data <= Z.of_nat (length data))%Z -> (0 < A)%Z -> (A + Z.of_nat (length data) < 2 ^ 47)%Z ->
    abuf_bytes mem A data ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> aro_none mem -> arelro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe84f0)) ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe86c4) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        atr_call_regs regs' A (Z.of_nat (length data)) (hdr_cfg data) (bv_swrap 8 (hdr_b data 1)) ->
        (forall r : reg, In r [22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r) ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x177adc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem pp A cap data K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21) Hok HA0 HAh HB Hstk Hro Hrel Hra HK HV HAK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (hdr_cfg_range data) as Hcr.
    set (cfg := hdr_cfg data) in *.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 cap) (getr regs 22) (Z_to_bv 64 0)
                 (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 2))) (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 3)))
                 (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 4))) (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 5)))
                 (Z_to_bv 64 (hdr_b data 0)) (Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)))).
    assert (HR : regs_ok (MENV v regs) srH0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knH) by (apply aknL_ra_ok; subst v; try assumption; try reflexivity; lia).
    assert (CFG : edenot (MENV v regs) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))
                  = Z_to_bv 64 cfg) by (subst cfg; apply acfg_expr_val; reflexivity).

    assert (BM : forall (k : Z) (j : nat), (2 <= k <= 5)%Z -> j = (Z.to_nat cfg + Z.to_nat k)%nat ->
      sc_denot RSEGS mem (MENV v regs)
        (SCReadBase (SA (EAlu ALU_ADD (EVar 3) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))) k)
                    1 false (ELit (hdr_b data j)))
      /\ sc_denot RSEGS mem (MENV v regs)
        (SCFlat (SA (EAlu ALU_ADD (EVar 3) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))) k) (ELit 1))).
    { intros k j Hk Hj. cbn [sc_denot]. unfold adenot, v_addi, flat, estart, elenZ. cbn [a_base a_off].
      rewrite ed_add, CFG. unset_v; cbn [edenot ev MENV mvals vals_ev nth app v_A]. rewrite vadd_ZZ. unorm.
      split; [| lia]. exists [nth j data (Z_to_bv 8 0)]. split.
      - rewrite <- (HB j) by lia. f_equal. f_equal. lia.
      - rewrite bytes_le_to_Z_1. cbn [extz]. reflexivity. }
    run_segM scrHk 0x177adc%Z srH0 knH 46%nat rHk caHk (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HAK |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      destruct (ahdr_reads v regs mem A data mem eq_refl eq_refl eq_refl ltac:(lia) HA0 HAh HB ltac:(intros; reflexivity)) as (S1 & S2 & S3 & S4).
      destruct (BM 5%Z (Z.to_nat cfg + 5)%nat ltac:(lia) ltac:(lia)) as [B5 F5].
      destruct (BM 4%Z (Z.to_nat cfg + 4)%nat ltac:(lia) ltac:(lia)) as [B4 F4].
      destruct (BM 2%Z (Z.to_nat cfg + 2)%nat ltac:(lia) ltac:(lia)) as [B2 F2].
      destruct (BM 3%Z (Z.to_nat cfg + 3)%nat ltac:(lia) ltac:(lia)) as [B3 F3].
      repeat apply Forall_cons; try apply Forall_nil; try assumption.
      - cbn [sc_denot branch_taken]. rewrite ed_add, CFG, ed_lit, vadd_ZZ.
        unset_v; cbn [edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. apply Z.ltb_ge. lia.
      - unset_v. cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. cbn [negb].
        destruct (Z.ltb_spec 5 (Z.of_nat (length data))); [reflexivity|lia]. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rHk))) with 0xe86c4%Z in HV'. change (s_regs (fst (fst rHk))) with srHk in HR'.
    mk_frame v regs mem acovHk EQM LF FR.
    apply (HK _ _ _ _ HV' HA' SB'); [| | exact FR | eapply mstk_after; [exact FR | exact Hstk]].
    - unfold atr_call_regs. unset_v.
      repeat split;
        lazymatch goal with |- getr R' ?r = _ =>
          regv HR' r; rewrite ?ed_add, ?ed_mul, ?CFG, ?ed_lit, ?ed_var;
          cbn [ev MENV mvals vals_ev nth app v_sp0 v_A v_len v_b1]; ed_lin idtac; unorm;
          first [ reflexivity | f_equal; lia | apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; f_equal; lia ]
        end.
    - intros rr Hrr. cbn [In] in Hrr.
      destruct Hrr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        [fin_reg HR' (22:reg) | fin_reg HR' (23:reg) | fin_reg HR' (24:reg) | fin_reg HR' (25:reg) | fin_reg HR' (26:reg) | fin_reg HR' (27:reg)].
  Qed.
End Blocks.

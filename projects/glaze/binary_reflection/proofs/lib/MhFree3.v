(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhFree OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf.MhSub OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhFree OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Free3.
  Context {fx : FPState} {RN : run_ceil}.



  (* [comment removed for export] *)
  Lemma free_thunk : forall regs (M : mem) rom mdl (Q : config -> Prop),
    m_halted mdl = None -> m_vm_lazy mdl = [] ->
    kat RSEGS (mkCfg (mkst regs (0x61f44%bv : word) M rom) mdl) Q ->
    kat RSEGS (mkCfg (mkst regs (0x61b20%bv : word) M rom) mdl) Q.
  Proof.
    intros regs M rom mdl Q Hh Hl K.
    eapply kat_step; [exact Hh | exact Hl | reflexivity | exact (step_jal_x0 _ _ _ _ _ _ _ F_61acc eq_refl D_61acc) |].
    replace (btgt (0x61b20%bv : word) (bv_signed (1060%bv : bv 21))) with (0x61f44%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    exact K.
  Qed.

  (* [comment removed for export] *)
  Definition free_post3 (st : mst) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc' : list (Z * Z)) (B' C' ret sp : Z) (c' : config) : Prop :=
    exists R' M' mdl',
      c' = mkCfg (mkst R' (Z_to_bv 64 ret) M' (seg_rom RSEGS)) mdl' /\
      regs_kept R R' /\
      (forall a : word, M' a <> M a -> mh_changed stk Lc' sp a) /\
      (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M' a 1%nat = true) /\
      (exists st', WF st' Lc' /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\ nojunk st' /\ nolimbo st' /\ fsub st st') /\
      PHI Lc' <= B' /\ Z.of_nat (length Lc') <= C' /\ VMLIM <= vm_limit (m_vmmaps mdl') /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

  Lemma free_core : forall stk st R M mdl Lc Lc' B C B' C' ret sp p,
    FSTK <= stk ->
    WF st Lc -> REP st M -> LEDGER st (m_vmmaps mdl) -> nojunk st -> nolimbo st ->
    PHI Lc <= B -> Z.of_nat (length Lc) <= C -> VMLIM <= vm_limit (m_vmmaps mdl) ->
    free_pre stk R M mdl Lc Lc' B C B' C' ret sp p ->
    kat RSEGS (free_cfg R M mdl) (free_post3 st stk R M mdl Lc' B' C' ret sp).
  Proof.
    intros stk st R M mdl Lc Lc' B C B' C' ret sp p Hstk HWF HREP HLG NJ NL HB HC HV
           (Hh & Hlz & Hmat & H1 & Hret & Hret2 & H10 & CASE & H2 & Hsp16 & Hsplo & H4 & SOK).
    pose proof (u64_range (getr R 2)) as SPR. rewrite H2 in SPR.
    assert (E2 : getr R 2 = Z_to_bv 64 sp) by (apply bv_eq; rewrite u_Z2bv by lia; exact H2). ceil.
    assert (Hra : ret_ok (getr R 1)) by (rewrite H1; apply ret_ok_even; rewrite u_Z2bv by lia; exact Hret2).
    unfold FSTK in Hstk. unfold free_cfg, A_FREE.
    replace (Z_to_bv 64 400160) with (0x61b20%bv : word) by (apply bv_eq; reflexivity).
    apply free_thunk; [exact Hh | exact Hlz|].
    destruct CASE as [(-> & -> & -> & ->)|(m & L1 & L2 & EL & -> & -> & ->)].
    - (* [comment removed for export] *)
      apply (free_null_kat R M mdl (seg_rom RSEGS) _ Hh Hlz H10 Hra). rewrite H1.
      exists R, M, mdl. split; [reflexivity|]. split; [intros r _; reflexivity|].
      split; [intros a NE; exfalso; exact (NE eq_refl)|]. split; [exact SOK|].
      split; [exists st; repeat (split; [assumption|]); apply fsub_refl|].
      repeat (split; [assumption|]). split; reflexivity.
    - (* [comment removed for export] *)
      pose proof (wL_nodup st Lc (WF_live st Lc HWF)) as ND. apply NoDup_ListNoDup in ND.
      assert (Hin : In (bv_unsigned p, m) Lc) by (rewrite EL; apply in_app_iff; right; left; reflexivity).
      assert (HL'in : forall x, In x (L1 ++ L2) <-> In x Lc /\ x <> (bv_unsigned p, m)).
      { intros x. rewrite EL. rewrite !in_app_iff. cbn. split.
        - intros X. split; [tauto|]. intros ->. rewrite EL in ND. exact (NoDup_remove_2 L1 L2 _ ND ltac:(apply in_app_iff; exact X)).
        - intros [[X|[X|X]] NE]; [left; exact X | exfalso; exact (NE (eq_sym X)) | right; exact X]. }
      assert (HL'nd : NoDup (L1 ++ L2)).
      { apply NoDup_ListNoDup. rewrite EL in ND. exact (NoDup_remove_1 L1 L2 _ ND). }
      assert (HL'len : (length (L1 ++ L2) <= length Lc)%nat) by (rewrite EL, !length_app; cbn; lia).
      assert (DEF : defined M (sp - 912) sp).
      { apply defined_of_store_ok; [lia | lia | right; lia |]. intros a Ha.
        pose proof (SOK (Z_to_bv 64 a)) as X. rewrite u_Z2bv in X by lia. apply X. lia. }
      assert (P10 : getr R 10 = Z_to_bv 64 (bv_unsigned p)) by (rewrite H10; symmetry; apply bv_eq; rewrite u_Z2bv by (pose proof (u64_range p); lia); reflexivity).
      apply (free_kat st R M mdl (seg_rom RSEGS) Lc (L1 ++ L2) (bv_unsigned p) m sp _
               HWF HREP HLG NJ NL Hh Hlz Hmat Hin HL'in HL'nd HL'len P10 Hra E2 Hsp16 ltac:(unfold FSTK; lia) ltac:(lia) H4 DEF).
      intros c' (R' & M' & mdl' & -> & RG & FR & DF & MI & X1 & X2 & X3 & X4 & X5 & X6). unfold FSTK in FR, DF.
      destruct RG as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
      rewrite H1. exists R', M', mdl'. split; [reflexivity|]. split.
      { intros r Hr. unfold callee_saved_regs in Hr. cbn in Hr.
        repeat (destruct Hr as [<-|Hr]; [first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20
                                               | exact Q21 | exact Q22 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27] |]).
        destruct Hr. }
      split.
      { intros a NE. pose proof (u64_range a) as AR.
        assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (apply bv_eq; rewrite u_Z2bv by lia; reflexivity).
        rewrite Ea in NE. destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold mh_changed.
        - right; left. lia.
        - left. unfold in_blocks, app_of in *. exact A.
        - right; right; left. exact A.
        - right; right; right. exact A. }
      split.
      { intros a Ha. pose proof (u64_range a) as AR.
        assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (apply bv_eq; rewrite u_Z2bv by lia; reflexivity).
        destruct (Z.lt_ge_cases (bv_unsigned a) (sp - 912)) as [LO|HI].
        - (* [comment removed for export] *)
          assert (EQ : M' a = M a).
          { destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso. rewrite Ea in NE.
            destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in *; lia. }
          pose proof (SOK a Ha) as S0. cbn [store_ok] in S0 |- *. unfold wview in S0 |- *. rewrite EQ. exact S0.
        - rewrite Ea. eapply (store_ok_of_defined1 M' (sp - 912) sp); [exact DF | lia | lia | lia]. }
      split; [exact MI|].
      rewrite EL in HB. rewrite PHI_app in HB |- *. cbn in HB. rewrite EL, length_app in HC. cbn in HC. rewrite length_app.
      split; [lia|]. split; [lia|]. split; [rewrite X6; exact HV|].
      repeat (split; [assumption|]). exact X5.
  Qed.

  (* [comment removed for export] *)
  Theorem free_kat3 : FREE_KAT MSTK.
  Proof.
    intros R M mdl Lc Lc' B C B' C' ret sp p ((st & HWF & HREP & HLG & NJ & NL) & HB & HC & HV) PRE.
    eapply kat_conseq; [exact (free_core MSTK st R M mdl Lc Lc' B C B' C' ret sp p ltac:(unfold MSTK_M, FSTK; lia) HWF HREP HLG NJ NL HB HC HV PRE) |].
    intros c' (R' & M' & mdl' & E & RG & FR & SO & (st' & W' & RP' & LG' & NJ' & NL' & _) & HB' & HC' & HV' & X).
    exists R', M', mdl'. split; [exact E|]. split; [exact RG|]. split; [exact FR|]. split; [exact SO|].
    split; [| exact X]. split; [exists st'; repeat (split; [assumption|]); exact NL'|]. split; [exact HB'|]. split; [exact HC' | exact HV'].
  Qed.

  (* [comment removed for export] *)
  Theorem free_r3 : FREE_R MSTK.
  Proof.
    intros R M mdl Lc Lc' B C B' C' ret sp p ((st & HWF & HREP & HLG & NJ & NL & LO) & HB & HC & HV) PRE.
    eapply kat_conseq; [exact (free_core MSTK st R M mdl Lc Lc' B C B' C' ret sp p ltac:(unfold MSTK_M, FSTK; lia) HWF HREP HLG NJ NL HB HC HV PRE) |].
    intros c' (R' & M' & mdl' & E & RG & FR & SO & (st' & W' & RP' & LG' & NJ' & NL' & FS') & HB' & HC' & HV' & X).
    exists R', M', mdl'. split; [exact E|]. split; [exact RG|]. split; [exact FR|]. split; [exact SO|].
    split; [| exact X]. split; [| split; [exact HB' | split; [exact HC' | exact HV']]].
    exists st'. repeat (split; [assumption|]). exact (lone_all_fsub st st' Lc Lc' HWF W' NJ' FS' LO).
  Qed.
End Free3.

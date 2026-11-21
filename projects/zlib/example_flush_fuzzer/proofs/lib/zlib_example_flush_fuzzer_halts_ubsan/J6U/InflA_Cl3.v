(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ItCovIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvCov.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvTbl.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Match2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflDec6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflMem2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_ClS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Cl1 InflA_Cl1b InflA_Cl2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Ll.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Dist3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InffastCtx IfSpec IfSpec6 InflA_LenF.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvArms5.


Module InflA_Codelens9.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ItCovIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvCov.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTbl.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflMem2.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1b.InflA_Codelens5.
Import ListNotations.
Import InflA_Cl1.InflArmLib6e.
Import InflA_Cl1.InflNeed6b.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens1.
Import InflA_Cl1.InflA_Codelens2.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1b.InflA_Codelens4.
Import InflA_Cl1b.InflA_Codelens4b.
Import InflA_Cl2.InflA_Codelens8.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma cb_facts_of_pinv : forall v s c r,
  is_mode s = CODELENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_have s < is_nlen s + is_ndist s ->
  cb_facts v s /\ tab_ok CODES (cat (is_codes s) (CDyn 0)) (is_lenbits s) (is_next s) = true /\ is_next s <= 1444.
Proof.
  intros v s c r Hmode HP Hlt. open_pinv HP.
  destruct PS as (_ & _ & (Alens & Awork & Acodes) & _ & _ & QC & _). destruct (QC Hmode) as (QN & QD & QH & CT & QL15).
  unfold ctab_ok in CT. destruct (ctab_ok_cases _ _ _ _ CT) as (ELC & NX & TC).
  pose proof (tab_ok_root _ _ _ _ TC) as (Rt1 & _ & _).
  pose proof SR as X. unfold SRNGq in X. do 26 (destruct X as [_ X]). destruct X as ((BL & _ & _) & _).
  split; [| split; [exact TC | exact NX]].
  unfold cb_facts. repeat (split; [first [assumption | lia] |]). exact BL.
Qed.

Definition ilCP : cfg := ilSx [0x1f9d8; 0x1f96c] [].

Section Body.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_cb HB := destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens).

  Lemma cl_join : forall s c r R M here,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    tab_ok CODES (cat (is_codes s) (CDyn 0)) (is_lenbits s) (is_next s) = true -> is_next s <= 1444 ->
    here = cat (is_codes s) (is_lencode s) (BITSv (ir_hold r) (is_lenbits s)) -> code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> JREG v s r here R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ body_post v (mkW s c r) M (cb_after here (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M here Hmode HB RI CI TC NX Ehere Hhb HM HRC HX HJ. pose proof HB as HB0. open_cb HB.
    pose proof RI as RI0. unfold RINV in RI0. destruct RI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rbits & Rhold).
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    pose proof (tab_root_entry CODES _ _ _ (BITSv (ir_hold r) (is_lenbits s)) TC HJ1) as (HB1 & _ & _ & CASES).
    rewrite ELC in Ehere. rewrite <- Ehere in HB1, CASES.
    pose proof (tab_ok_root _ _ _ _ TC) as (Rt1 & _ & _).
    assert (Bh : 1 <= code_bits here <= 15) by (clear - HB1 Rt1; lia).
    pose proof (code_val_range here) as Hvr.
    destruct (Z_lt_le_dec (code_val here) 16) as [V16|V16].
    - rewrite (cb_lit here s c r V16).
      exact (cl_lit v C s c r R M here Hmode HB0 RI Hhb ltac:(lia) V16 HM HRC HX HJ).
    - destruct (cl_rep_pre v C s c r R M here HB0 RI ltac:(lia) V16 HM HJ) as (R1 & Hms1 & HV).
      destruct (Z.eq_dec (code_val here) 16) as [E16|N16]; [| destruct (Z.eq_dec (code_val here) 17) as [E17|N17]].
      + rewrite E16 in HV. destruct (cl_rep16_full v C s c r R1 M here Hmode HB0 RI CI E16 ltac:(lia) Hhb HM HRC HX HV) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
      + rewrite E17 in HV. destruct (cl_rep17_full v C s c r R1 M here Hmode HB0 RI CI E17 ltac:(lia) Hhb HM HRC HX HV) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
      + destruct (cl_rep18_full v C s c r R1 M here Hmode HB0 RI CI ltac:(lia) ltac:(lia) Hhb HM HRC HX HV) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
  Qed.

  Definition wpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (16, EVar 45%nat); (11, EVar 46%nat); (12, EVar 47%nat); (13, EVar 48%nat); (15, EVar 49%nat); (14, EVar 50%nat);
     (25, EVar 40%nat); (19, EVar 41%nat); (23, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat));
     (17, EAdd (EVar 43%nat) (EVar 44%nat)); (31, EVar 36%nat)].
  Definition wvb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 16); (49%nat, 2 ^ 15); (50%nat, 2 ^ 63); (51%nat, 65536); (52%nat, 65536)].

  Ltac cb_side Rhold64 Rt1 Rt2 TAB HJ1 HA0 HA1 Hext LE GT :=
    rewrite ?idx0_exec by (first [clear - Rhold64; lia | clear - Rt1; lia]);
    rewrite ?cent_reasm, ?cent_bits;
    repeat match goal with |- context [?x mod 2 ^ 64] =>
      lazymatch x with context [BITSv _ _] => rewrite (Z.mod_small x (2 ^ 64)) by (generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia) end end;
    first [ lazymatch goal with |- exists bs, _ => match goal with |- context [BITSv ?h ?n] => tab_read2 TAB (BITSv h n); clear - HJ1 Rt2 Hext; lia end end
          | lazymatch goal with |- context [if _ <? _ then 1 else 0] => generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; ub_ptr_side end
          | lazymatch goal with |- exists _, _ => idtac end
          | lazymatch goal with |- exists _ _ _, _ => idtac end
          | generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia
          | clear - LE; lia
          | clear - GT; lia
          | idtac ].

  Lemma cl_body : forall s c r R M,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    tab_ok CODES (cat (is_codes s) (CDyn 0)) (is_lenbits s) (is_next s) = true -> is_next s <= 1444 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> WREG v s r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f8f0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ body_post v (mkW s c r) M (codelens_body (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HB RI CI TC NX HM HRC HX HP. pose proof HB as HB0. open_cb HB.
    destruct HP as ((HF & G9 & G11 & G12 & G13 & G15 & G14) & G16 & G22 & G18 & G24 & G25 & G17 & G31). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22.
    pose proof G18 as P18. pose proof G24 as P24. pose proof G25 as P25.
    open_ictx C. open_lmem HM. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (tab_ok_root _ _ _ _ TC) as (Rt1 & Rt2 & Rt3).
    assert (Hofs : cofs_ok (is_lencode s)) by (rewrite ELC; cbn; lia).
    assert (TD : tab_ok CODES (cat (is_codes s) (is_lencode s)) (is_lenbits s) (is_next s) = true) by (rewrite ELC; exact TC).
    assert (Hext : is_next s <= cext (is_lencode s)) by (rewrite ELC; cbn [cext]; lia).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hofs) as TAB.
    pose proof (ones_range15 (is_lenbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    assert (Hhv32 : 0 <= is_have s < 2 ^ 32) by (clear - Hhv Htot; lia).
    assert (Hnd32 : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31) by (clear - Hnl Hnd Htot; lia).
    assert (Hh31 : 0 <= ir_have r < 2 ^ 31) by (clear - Rnh Rnx0 Rhv0 CI0; lia).
    set (last := cent1 s (ir_hold r)).
    pose proof (tab_root_entry CODES _ _ _ (BITSv (ir_hold r) (is_lenbits s)) TD HJ1) as (HB1 & _). change (cat _ _ _) with last in HB1.
    pose proof (code_bits_range last) as Hcb. pose proof (code_val_range last) as Hval. pose proof (clo_range last) as Hclo.
    pose proof (cent_range last) as Hcent. pose proof (cent_shr8_range last) as Hc8.
    assert (ED1 : DECODE1 (is_lencode s) (is_lenbits s) (mkW s c r)
                  = if code_bits last <=? ir_bits r then ARun last (mkW s c r)
                    else (PULLBYTE ;; DECODE_k 7 (is_lencode s) (fun h => BITSv h (is_lenbits s)) code_bits)%am (mkW s c r)).
    { unfold DECODE1. rewrite DECODE_k_S. rewrite code_at_cat. reflexivity. }
    rewrite codelens_body_dec1, ED1.
    destruct (Z.leb_spec (code_bits last) (ir_bits r)) as [LE|GT].
    -
      arm_symexP (@nil (Z * expr)) ilCP 30%nat [true; true; true; true] [RVal (EVar 51%nat); RVal (EVar 52%nat)] wpins wvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); code_val last; clo last] NoVals F0
        (mkst R (Z_to_bv 64 0x1f8f0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: subst last; unfold cent1 in *; cb_side Rhold64 Rt1 Rt2 TAB HJ1 HA0 HA1 Hext LE GT.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTCB1" G end.
      set (last := cat (is_codes s) (is_lencode s) (BITSv (ir_hold r) (is_lenbits s))) in *.
      assert (HJ : JREG v s r last R1).
      { symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (28%bv : reg) as Q28.
        symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (7%bv : reg) as Q7. symex_reg HR1 (20%bv : reg) as Q19. symex_reg HR1 (21%bv : reg) as Q20.
        symex_reg HR1 (24%bv : reg) as Q23. rewrite ?idx0_exec in Q23 by (first [clear - Rhold64; lia | clear - Rt1; lia]). rewrite ?cent_reasm in Q23.
        symex_reg HR1 (29%bv : reg) as Q29. rewrite ?idx0_exec in Q29 by (first [clear - Rhold64; lia | clear - Rt1; lia]). rewrite ?cent_reasm in Q29.
        symex_reg HR1 (30%bv : reg) as Q30. rewrite ?idx0_exec in Q30 by (first [clear - Rhold64; lia | clear - Rt1; lia]). rewrite ?cent_reasm, ?cent_bits in Q30.
        unfold JREG, BKc. split; [split; [lfixc_close Hfr1 HR1|]|]; subst last;
          regs_via Hfr1; first [ exact Q24 | exact Q25 | exact Q28 | exact Q5 | exact Q23 | exact Q29 | exact Q30
                               | rewrite Q24; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q6; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q7; rewrite ?szwrap32_small by (clear - Rbits; lia); rewrite ?Z.mod_small by (clear - Rbits; lia); f_equal; lia
                               | rewrite Q19; rewrite ?szwrap32_small by (clear - Rbits; lia); first [apply zw_neg_mod | f_equal; lia | apply zw_eqm; rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia]
                               | rewrite Q20; ub_ptr_side
                               | rewrite Q20; destruct (Z.ltb_spec 0 (ctab6 v (is_lencode s))); [reflexivity | exfalso; clear - HA0 H; lia]
                               | rewrite Q5; f_equal; lia
                               | match goal with |- ?G => idtac "JREG0 LEFT" G end ]. }
      destruct (cl_join s c r R1 M last Hmode HB0 RI0 CI' TC NX ltac:(subst last; reflexivity) LE HM HRC HX HJ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
    -
      arm_symexP (@nil (Z * expr)) ilCP 30%nat [true; true; true; false] [RVal (EVar 51%nat); RVal (EVar 52%nat)] wpins wvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); code_val last; clo last] NoVals F0
        (mkst R (Z_to_bv 64 0x1f8f0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: subst last; unfold cent1 in *; cb_side Rhold64 Rt1 Rt2 TAB HJ1 HA0 HA1 Hext LE GT.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTCB2" G end.
      set (last := cat (is_codes s) (is_lencode s) (BITSv (ir_hold r) (is_lenbits s))) in *.
      assert (HJS : CJS v s (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (28%bv : reg) as Q28.
        symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (7%bv : reg) as Q7. symex_reg HR1 (20%bv : reg) as Q19. symex_reg HR1 (21%bv : reg) as Q20.
        symex_reg HR1 (22%bv : reg) as Q21.
        unfold CJS, CK. split; [split; [lfixc_close Hfr1 HR1|]|];
          regs_via Hfr1; first [ exact Q24 | exact Q25 | exact Q28 | exact Q5
                               | rewrite Q24; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q6; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q21; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q7; rewrite ?szwrap32_small by (clear - Rbits; lia); rewrite ?Z.mod_small by (clear - Rbits; lia); f_equal; lia
                               | rewrite Q19; rewrite ?szwrap32_small by (clear - Rbits; lia); first [apply zw_neg_mod | f_equal; lia | apply zw_eqm; rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia]
                               | rewrite Q20; ub_ptr_side
                               | rewrite Q20; destruct (Z.ltb_spec 0 (ctab6 v (is_lencode s))); [reflexivity | exfalso; clear - HA0 H; lia]
                               | rewrite Q5; f_equal; lia
                               | clear; lia | clear - Rbits; lia
                               | match goal with |- ?G => idtac "CJS0 LEFT" G end ]. }
      pose proof HX as HX0. open_lx HX0.
      pose proof (dec_loop v s c (is_lencode s) (fun h => BITSv h (is_lenbits s)) code_bits 15 0x1f96c 0x1f9d8
                    (CJS v s (ir_bits r) (ir_have r) (ir_next r)) (CJE v s (ir_bits r) (ir_have r) (ir_next r)) C ltac:(lia)
                    (fun h Hh => need1_bound CODES _ _ _ h TD Hh)
                    CI'
                    (cl_step_H v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 (is_next s) TD Hext Hofs CI' Hhv32 Hnd32)
                    (cl_step_E v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 (is_next s) TD Hext Hofs CI' Hhv32 Hnd32)
                    (cl_dry v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 (is_next s) TD Hext Hofs CI' Hhv32 Hnd32)
                    7%nat r R1 M HM HRC HJS RI0
                    ltac:(cbv beta; change (code_at s (is_lencode s) (BITSv (ir_hold r) (is_lenbits s))) with last; exact GT)
                    ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
      destruct ((PULLBYTE ;; DECODE_k 7 (is_lencode s) (fun h => BITSv h (is_lenbits s)) code_bits)%am (mkW s c r))
        as [last1 w1 | w1 | rc w1]; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh1 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
        subst last1.
        assert (HJ : JREG v s r1 (code_at s (is_lencode s) (BITSv (ir_hold r1) (is_lenbits s))) R2).
        { pose proof HJE as X. unfold CJE, CK in X.
          destruct X as ((EF & E9 & E16 & E11 & E12 & E13 & E18 & E31 & E17 & E21 & E15 & E14 & E20) & E22 & E24 & E6 & E25 & E28 & E5 & E7 & E19 & E23 & E29 & E30).
          unfold cent1 in E23, E29, E30. rewrite <- code_at_cat in E23, E29, E30.
          unfold JREG, BKc. repeat match goal with |- _ /\ _ => split end; first [assumption | match goal with |- ?G => idtac "JREG1 LEFT" G end]. }
        destruct (cl_join s c r1 R2 M _ Hmode HB0 RI1 CI' TC NX (code_at_cat s (is_lencode s) (BITSv (ir_hold r1) (is_lenbits s))) (proj1 Hb1) HM1 HRC1 HX1 HJ) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
        apply (body_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
        cbn [body_post arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.
End Body.
End FXG.
End InflA_Codelens9.
Export InflA_Codelens9.

Module InflA_Codelens7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ItCovIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvCov.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTbl.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflMem2.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1b.InflA_Codelens5.
Import ListNotations.
Import InflA_Cl2.InflA_Codelens6.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilCA : cfg := ilS.

Definition apins : list (Z * expr) :=
  [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
   (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat));
   (12, EVar 45%nat)].

Definition cl_pinv_stmt : Prop := forall (NI NO WN TOT0 : Z) s c r,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = CODELENS -> is_nlen s + is_ndist s <= is_have s -> ir_ret r = 0 ->
  arr_get (is_lens s) 256 <> 0 -> it_ret (cd_call1 s) = 0 -> it_ret (cd_call2 (cd_S1 s (cd_call1 s))) = 0 ->
  pinv NI NO WN TOT0 (mkW (iset_mode (cd_S2 (cd_S1 s (cd_call1 s)) (cd_call2 (cd_S1 s (cd_call1 s)))) LEN_) c (irset_ret r 0)).

Section SegA.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis ITABLE : itable_run6.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.

  Definition AREG (s : inflate_state) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ LVARS v (mkW s c r) R /\ getr R 12 = zw (is_nlen s).

  Ltac open_cd HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & QN & QD & QL15 & Alens & Awork & Acodes & Blens & Bwork & Bcodes).

  Lemma codelens_segA : forall s c r R M,
    is_mode s = CODELENS -> cd_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> ir_ret r = 0 ->
    (arr_get (is_lens s) 256 <> 0 -> it_ret (cd_call1 s) = 0 -> it_ret (cd_call2 (cd_S1 s (cd_call1 s))) = 0 ->
       pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (iset_mode (cd_S2 (cd_S1 s (cd_call1 s)) (cd_call2 (cd_S1 s (cd_call1 s)))) LEN_) c (irset_ret r 0))) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> AREG s c r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fc88) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (cd_after (cv_flush v) s c r) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI Hret0 HPL HM HRC HX HR. pose proof HD as HD0. open_cd HD.
    destruct HR as (HF & HV & G12). open_fixc HF. open_vars HV.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr.
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (Mlens 256 ltac:(lia)) as C664. replace (cv_S v + 168 + 2 * 256) with (cv_S v + 680) in C664 by lia.
    pose proof (Blens 256 ltac:(lia)) as B256.
    unfold cd_after.
    destruct (Z.eq_dec (arr_get (is_lens s) 256) 0) as [E0|E0].
    -
      rewrite E0. cbn [Z.eqb]. rewrite E0 in C664.
      arm_symexP (@nil (Z * expr)) ilCA 14%nat [true; true]
        [RVal (EAdd (EVar 33%nat) (ELit 168)); RVal (ELit 0); RVal (EVar 35%nat)]
        apins [(45%nat, 512)] v r [is_nlen s] NoVals F0
        (mkst R (Z_to_bv 64 0x1fc88) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTA1" G end.
      set (c' := icset_msg c MSG_invalid_code_missing_end_of_block) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66831)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (HM1 : LMEM v (mkW s c' r) M1) by (exact (LMEM_store_msg v C s c r M MSG_invalid_code_missing_end_of_block HM Hput)).
      assert (HM2 : LMEM v (mkW s' c' r) M2).
      { apply (LMEM_store_scalar v C s c' r _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_code_missing_end_of_block) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      assert (HRC2 : RETC v (mkW s' c' r) M2) by (subst M2 M1; retc_tower C HRC).
      assert (HX2 : LX v (mkW s' c' r)).
      { apply (LX_step0 v s c r s' c' r HX NH NB); subst s' c'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_code_missing_end_of_block; lia | bk_side]. }
      arm_disp C HM2 Hfr1 R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode s')). split.
      { eapply msteps_trans; [| exact Hms2]. subst M2 M1. by_run Hms1. }
      replace (is_mode s') with BAD by (subst s'; destruct s; reflexivity).
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [exact HRC2|]. split; [exact HX2|].
        unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1 | split; [| intros _; exact G26']].
        unfold LVARS; cbn [w_r].
        repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption end
                | match goal with |- ?G => idtac "LVARSA LEFT" G end ].
      + cbn [w_r]. subst M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    - replace (arr_get (is_lens s) 256 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
      arm_symexP (@nil (Z * expr)) ilCA 18%nat [true; false]
        [RVal (EAdd (EVar 33%nat) (ELit 168)); RVal (EVar 46%nat); RVal (EAdd (EVar 33%nat) (ELit 1384));
         RVal (EAdd (EVar 33%nat) (ELit 160)); RVal (EAdd (EVar 33%nat) (ELit 136)); RVal (EAdd (EVar 33%nat) (ELit 808))]
        apins [(45%nat, 512); (46%nat, 65536)] v r [is_nlen s; arr_get (is_lens s) 256] NoVals F0
        (mkst R (Z_to_bv 64 0x1fc88) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTA2" G end.
      replace (Z_to_le_bytes 8 (cv_S v + 1384)) with (Z_to_le_bytes 8 (codeptr_addr 75438 77486 (cv_S v) (CDyn 0))) in Hms1 by (cbn [codeptr_addr]; f_equal; lia).
      set (sA := iset_lencode s (CDyn 0)). set (sB := iset_lenbits sA 9). set (sC := iset_next sB 0).
      set (M1 := wbytes M (zw (cv_S v + 120)) (Z_to_le_bytes 8 (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)))) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 136)) (Z_to_le_bytes 4 9)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 160)) (Z_to_le_bytes 8 (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)))) in *.
      assert (HM1 : LMEM v (mkW sA c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 120 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        exact (is6_upd_lencode M (cv_S v) _ s (CDyn 0) Msc ltac:(clear - CS; lia) ltac:(clear - CS; unfold is6_SIZE; lia)). }
      assert (HM2 : LMEM v (mkW sB c r) M2).
      { apply (LMEM_store_scalar v C sA c r _ M1 136 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_lenbits M1 (cv_S v) _ sA 9 (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW sC c r) M3).
      { apply (LMEM_store_scalar v C sB c r _ M2 160 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        replace (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)) with (cv_S v + 1384 + 4 * 0) by (cbn [codeptr_addr]; lia).
        apply (is6_upd_next M2 (cv_S v) _ sB 0 (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof HM3 as HM3'. clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mleftc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
      clear Fsv Fflush Flens Fnlens Fm16224 Fjtab Fbad Fin Fsane Ffl5 Fnext Fwork Fcodes Flenb Fdistb C664.
      open_lmem HM3'. unfold mapped in *.
      pose proof (is6_next _ _ _ _ Msc) as C144. pose proof (is6_lenbits _ _ _ _ Msc) as C120. cbn [w_s] in C144, C120.
      replace (is_next sC) with 0 in C144 by (subst sC sB sA; destruct s; reflexivity).
      replace (is_lenbits sC) with 9 in C120 by (subst sC sB sA; destruct s; reflexivity).
      replace (is_lens sC) with (is_lens s) in Mlens by (subst sC sB sA; destruct s; reflexivity).
      replace (is_work sC) with (is_work s) in Mwork by (subst sC sB sA; destruct s; reflexivity).
      replace (is_codes sC) with (is_codes s) in Mcodes by (subst sC sB sA; destruct s; reflexivity).
      symex_reg HR1 (10%bv : reg) as Q10. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (13%bv : reg) as Q13.
      symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (1%bv : reg) as Q1.
      destruct (ITABLE M3 R1 LENS (cv_S v) 0 (is_nlen s) 0 9 (cv_S v + 136) (cv_sp v - 256) (zw 0x1fccc) (is_lens s) (is_codes s) (is_work s)
                  Q10 ltac:(rewrite Q11; f_equal; lia) Q12 Q13 Q14 Q15 ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact P2) Q1
                  ltac:(apply ret_ok_lit; [lia | reflexivity]) ltac:(left; reflexivity)
                  ltac:(clear - CS; lia) ltac:(clear - CS; lia) ltac:(clear - CS; lia) CoS
                  ltac:(unfold ITFR6, IMG6_TOP in *; clear - Csp; lia) ltac:(clear - Csp; lia) ltac:(clear - Csp47; lia)
                  ltac:(clear - Csp; replace (cv_sp v - 256) with (cv_sp v + (-16) * 16) by lia; rewrite Z.mod_add by lia; destruct Csp as (_ & _ & E); exact E)
                  ltac:(unfold ITFR6; clear - CSb; lia))
        as (R3 & M4 & HmsT & T10 & Tret & T2 & Tfr & Tlens & Tcodes & Twork & Tnext & Tbits & TLt & TLw & TRt & TRw & Tsh & Tg & Tag).
      { intros x Hx. apply Mmap_f. unfold ITFR6 in Hx. clear - Hx. lia. }
      { exact Mmap_S. }
      { exact Mrod. }
      { exact Alens. } { exact Acodes. } { exact Awork. }
      { exact Mlens. } { exact Mcodes. } { exact Mwork. }
      { replace (cv_S v + 1384 + 4 * 0) with (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)) by (cbn [codeptr_addr]; lia). exact C144. } { exact C120. }
      { exact Blens. } { exact Bcodes. } { exact Bwork. }
      { lia. } { clear - QN; lia. } { clear - QN; lia. }
      { intros i Hi. apply (proj2 (QL15 (0 + i) ltac:(clear - Hi QN QD; lia))). }
      { intros X; discriminate X. }
      { intros X; discriminate X. }
      { lia. } { lia. } { cbn [it_room]; unfold ENOUGH_LENS; lia. }
      change (inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s)) with (cd_call1 s) in *.
      set (r1 := cd_call1 s) in *.
      assert (ES1 : iset_work (iset_codes (iset_next (if 136 =? 136 then iset_lenbits sC (it_bits r1) else iset_distbits sC (it_bits r1)) (it_table r1)) (it_tbl r1)) (it_work r1) = cd_S1 s r1)
        by (cbn [Z.eqb]; subst sC sB sA; unfold cd_S1; destruct s; reflexivity).
      pose proof (LMEM_itable v C sC c r M3 M4 136 (it_table r1) (it_bits r1) (it_tbl r1) (it_work r1) HM3 Hput ltac:(left; reflexivity)
                    (ITF_agree v 136 M3 M4 Tag) Tg Tcodes Twork Tnext Tbits) as HM4. rewrite ES1 in HM4.
      assert (HRC4 : RETC v (mkW (cd_S1 s r1) c r) M4).
      { apply (RETC_itable v C (mkW s c r) 136 M3 M4); [subst M3 M2 M1; retc_tower C HRC | left; reflexivity | exact (ITF_agree v 136 M3 M4 Tag)]. }
      assert (HX4 : LX v (mkW (cd_S1 s r1) c r)).
      { apply (LX_step0 v s c r _ c r HX NH NB); unfold cd_S1; try (destruct s; reflexivity); [destruct s; cbn; cbn in Xlive; exact Xlive | exact Xret | exact Xmsg | destruct s; cbn; cbn in Xbk; bk_side]. }
      assert (HB4 : BREG v (cd_S1 s r1) c r (it_ret r1) R3).
      { unfold BREG, INF_FRAME, LVARK. cbn [w_r].
        repeat match goal with |- _ /\ _ => split end;
          first [ exact T2 | exact T10
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Tfr n eq_refl), (Hfr1 n eq_refl); assumption end
                | match goal with |- ?G => idtac "BREGA LEFT" G end ]. }
      assert (HT : it_ret r1 = 0 -> is_lencode (cd_S1 s r1) = CDyn 0 /\ 0 <= is_next (cd_S1 s r1) <= 852 /\ 1 <= is_lenbits (cd_S1 s r1) <= 15
                    /\ tab_ok LENS (cat (is_codes (cd_S1 s r1)) (CDyn 0)) (is_lenbits (cd_S1 s r1)) (is_next (cd_S1 s r1)) = true).
      { intros R0.
        pose proof (tab_ok_of_shape LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) ltac:(clear - QN; lia)
                      ltac:(intros i Hi; rewrite Z.add_0_l; apply QL15; clear - Hi QN QD; lia)
                      ltac:(intros X; discriminate X) ltac:(intros X; discriminate X) ltac:(lia) ltac:(lia)
                      ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite Acodes; lia) ltac:(rewrite Awork; clear - QN; lia)) as TS1.
        change (inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s)) with r1 in TS1.
        cbv zeta in TS1. destruct (TS1 R0) as (TL1 & BL1 & NX1 & _ & _). cbn [it_room] in NX1. unfold ENOUGH_LENS in NX1.
        clearbody r1. clear - TL1 BL1 NX1.
        unfold cd_S1, it_bits, it_table, it_tbl in *. destruct s; cbn. rewrite Z.sub_0_r in TL1.
        split; [reflexivity|]. split; [clear - NX1 BL1; assert (2 <= 2 ^ snd (fst r1)) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia); lia|]. split; [exact BL1 | exact TL1]. }
      assert (HD1 : cd_facts v (cd_S1 s r1) c) by (apply (cd_facts_S1 v s c r1 HD0 TLt TLw TRw TRt)).
      destruct (codelens_segB v C ITABLE IFAST FFOK FASTOK GFOB FFRAME (cd_S1 s r1) c r R3 M4 (it_ret r1) ltac:(unfold cd_S1; destruct s; exact Hmode) HD1 RI0 Hret0 Tret HT (HPL E0) HM4 HRC4 HX4 HB4)
        as (R' & M' & pc' & Hms3 & HPOST).
      exists R', M', pc'. split.
      { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 0x21cb4) M3 s6u_rom)); [subst M3 M2 M1; by_run Hms1 | eapply msteps_trans; [exact HmsT | exact Hms3]]. }
      apply (arm_post_chain v (mkW s c r) (mkW (cd_S1 s r1) c r) M M4); [unfold cd_S1; destruct s; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. apply (MFRAME_trans v (ir_put r) (ir_put r) (ir_put r) M M3 M4); [| exact (MFRAME_itable v (ir_put r) M3 M4 136 C (proj1 Hput) ltac:(left; reflexivity) Tg (ITF_agree v 136 M3 M4 Tag))].
      subst M3 M2 M1. do 3 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl.
  Qed.
End SegA.
End FXG.
End InflA_Codelens7.
Export InflA_Codelens7.

Module InflA_Codelens10.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ItCovIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvCov.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTbl.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflMem2.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1b.InflA_Codelens5.
Import ListNotations.
Import InflA_Cl1.InflArmLib6e.
Import InflA_Cl1.InflNeed6b.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens1.
Import InflA_Cl1.InflA_Codelens2.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1b.InflA_Codelens4.
Import InflA_Cl1b.InflA_Codelens4b.
Import InflA_Cl1b.InflA_Codelens5.
Import InflA_Cl2.InflA_Codelens6.
Import InflA_Codelens7.
Import InflA_Cl2.InflA_Codelens8.
Import InflA_Codelens9.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Local Abbreviation HREGc := InflA_Ll.InflA_Lenlens3.HREGc.
Local Abbreviation codelens_core_stmt := InflA_Ll.InflA_Lenlens3.codelens_core_stmt.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma cw_done : forall k s c r, is_nlen s + is_ndist s <= is_have s -> codelens_while k (mkW s c r) = ARun tt (mkW s c r).
Proof.
  intros k s c r H. destruct k; [reflexivity|]. cbn [codelens_while]. unfold abind at 1. unfold gs. cbn [w_s].
  replace (is_have s <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; exact H). reflexivity.
Qed.
Lemma cw_step : forall k s c r, is_have s < is_nlen s + is_ndist s ->
  codelens_while (S k) (mkW s c r)
  = match codelens_body (mkW s c r) with
    | ARun c' w' => if c' then codelens_while k w' else ARun tt w'
    | ALeave w' => ALeave w' | ARet rc w' => ARet rc w' end.
Proof.
  intros k s c r H. cbn [codelens_while]. unfold abind at 1. unfold gs. cbn [w_s].
  replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; exact H).
  unfold abind. destruct (codelens_body (mkW s c r)) as [[|] w'|w'|rc w']; reflexivity.
Qed.

Lemma cd_facts_of_pinv : forall v s c r,
  is_mode s = CODELENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_nlen s + is_ndist s <= is_have s ->
  cd_facts v s c /\ ir_ret r = 0.
Proof.
  intros v s c r Hmode HP Hge. open_pinv HP.
  destruct PS as (Hw1 & Hw2 & (Alens & Awork & Acodes) & _ & _ & QC & _). destruct (QC Hmode) as (QN & QD & QH & CT & QL15).
  pose proof (sr_sane s SR) as Hsane.
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  pose proof SR as X. unfold SRNGq in X. do 26 (destruct X as [_ X]). destruct X as ((BL & BW & BC) & _).
  pose proof PX as XI'. unfold xinv in XI'. cbn [w_s w_c w_r] in XI'. destruct XI' as (XR & _).
  split.
  - unfold cd_facts. repeat (split; [first [assumption | lia] |]).
    split; [intros i Hi; apply QL15; lia|]. repeat (split; [first [assumption | lia] |]). exact BC.
  - destruct XR as [XR|XR]; [exact XR | rewrite Hmode in XR; cbv in XR; discriminate].
Qed.

Lemma arm_CODELENS_bad : forall flush w0 s c r,
  codelens_while 321 w0 = ARun tt (mkW s c r) -> is_mode s = BAD -> arm_CODELENS ivar_ref flush w0 = ARun tt (mkW s c r).
Proof.
  intros flush w0 s c r HW HB. unfold arm_CODELENS. rewrite abind_run, HW. mstep1 (@gs_eq inflate_state).
  rewrite HB. reflexivity.
Qed.
Lemma arm_CODELENS_leave : forall flush w0 w',
  codelens_while 321 w0 = ALeave w' -> arm_CODELENS ivar_ref flush w0 = ALeave w'.
Proof. intros flush w0 w' HW. unfold arm_CODELENS. rewrite abind_run, HW. reflexivity. Qed.

Definition ilCW : cfg := ilSx [0x1f8f0; 0x1fc88] [].

Definition hpins : list (Z * expr) :=
  [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
   (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))].

Section While.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis ITABLE : itable_run6.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.
  Hypothesis CLPINV : cl_pinv_stmt.

  Definition wpost (w : iw) (M : word -> option byte) (res : ares unit) (R' : bvmap 5 word) (M' : word -> option byte) (pc' : Z) : Prop :=
    match res with
    | ARun _ w' => (is_mode (w_s w') = BAD /\ arm_post v w M (ARun tt w') R' M' pc')
                   \/ (is_mode (w_s w') = CODELENS /\ is_nlen (w_s w') + is_ndist (w_s w') <= is_have (w_s w')
                       /\ pc' = 0x1fc88 /\ AREG v (w_s w') (w_c w') (w_r w') R' /\ LMEM v w' M' /\ RETC v w' M' /\ LX v w'
                       /\ pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w'
                       /\ same_blocks (w_s w) (w_s w') /\ MFRAME v (ir_put (w_r w)) (ir_put (w_r w')) M M')
    | ALeave w' => arm_post v w M (ALeave w') R' M' pc'
    | ARet _ _ => False
    end.

  Lemma wpost_chain : forall w0 w1 M0 M1 res R' M' pc',
    same_blocks (w_s w0) (w_s w1) -> MFRAME v (ir_put (w_r w0)) (ir_put (w_r w1)) M0 M1 ->
    wpost w1 M1 res R' M' pc' -> wpost w0 M0 res R' M' pc'.
  Proof.
    intros w0 w1 M0 M1 res R' M' pc' HS HF H. destruct res as [u w'|w'|rc w']; cbn [wpost] in *; [| | exact H].
    - destruct H as [[A B]|(A & B & P & G & HM & HRC & HX & HP & SB & MF)].
      + left. split; [exact A | exact (arm_post_chain v w0 w1 M0 M1 _ _ _ _ HS HF B)].
      + right. split; [exact A|]. split; [exact B|]. split; [exact P|]. split; [exact G|]. split; [exact HM|]. split; [exact HRC|].
        split; [exact HX|]. split; [exact HP|]. split; [exact (same_blocks_trans _ _ _ HS SB) | exact (MFRAME_trans v _ _ _ _ _ _ HF MF)].
    - exact (arm_post_chain v w0 w1 M0 M1 _ _ _ _ HS HF H).
  Qed.

  Lemma cl_while : forall k s c r R M,
    is_mode s = CODELENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    is_have s < is_nlen s + is_ndist s -> is_nlen s + is_ndist s - is_have s <= Z.of_nat k ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> WREG v s r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f8f0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ wpost (mkW s c r) M (codelens_while (S k) (mkW s c r)) R' M' pc'.
  Proof.
    open_ictx C.
    induction k as [|k IH]; intros s c r R M Hmode HP Hlt Hk HM HRC HX HPR; [exfalso; cbn in Hk; lia|].
    rewrite cw_step by exact Hlt.
    destruct (cb_facts_of_pinv v s c r Hmode HP Hlt) as (HB & TC & NX).
    pose proof HP as HP'. open_pinv HP'.
    pose proof (CB (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) ltac:(lia) ltac:(lia) (mkW s c r) HP Hmode Hlt) as HCB. cbn [w_s w_r] in HCB.
    destruct (cl_body v C s c r R M Hmode HB RI CI TC NX HM HRC HX HPR) as (R1 & M1 & pc1 & Hms1 & HBP).
    destruct (codelens_body (mkW s c r)) as [cc w1 | w1 | rc w1]; [| | destruct HCB].
    - destruct HCB as (P21 & N1 & D1 & T1 & F1 & W1).
      destruct cc.
      + destruct (T1 eq_refl) as (M1' & H1 & B1). cbn [body_post] in HBP. destruct HBP as (Epc1 & HW & HM1 & HRC1 & HX1 & SB1 & MF1).
        destruct w1 as [s1 c1 r1]. cbn [w_s w_r w_c] in *.
        clear PNI PNO PL PS PX PB PC SR CI RI WI CR.
        destruct (Z_lt_le_dec (is_have s1) (is_nlen s1 + is_ndist s1)) as [LT1|GE1].
        *
          replace pc1 with 0x1f8f0 in Hms1 by (rewrite Epc1; unfold foot_pc; rewrite (proj2 (Z.ltb_lt _ _) LT1); reflexivity).
          destruct (IH s1 c1 r1 R1 M1 M1' P21 LT1 ltac:(clear - Hk H1 N1 D1 LT1; cbn in Hk |- *; lia) HM1 HRC1 HX1 HW)
            as (R' & M' & pc' & Hms3 & HW3).
          exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms3]|].
          exact (wpost_chain (mkW s c r) (mkW s1 c1 r1) M M1 _ _ _ _ SB1 MF1 HW3).
        *
          replace pc1 with 0x1fc88 in Hms1 by (rewrite Epc1; unfold foot_pc; rewrite (proj2 (Z.ltb_ge _ _) GE1); reflexivity).
          exists R1, M1, 0x1fc88. split; [exact Hms1|].
          rewrite (cw_done (S k) s1 c1 r1 GE1). cbn [wpost w_s w_c w_r]. right.
          split; [exact M1'|]. split; [exact GE1|]. split; [reflexivity|].
          split.
          { destruct HW as ((HF & G9 & G11 & G12 & G13 & G15 & G14) & G16 & G22 & G18 & G24 & G25 & G17 & G31).
            unfold AREG, LVARS. cbn [w_r]. split; [exact HF|]. repeat match goal with |- _ /\ _ => split end; assumption. }
          split; [exact HM1|]. split; [exact HRC1|]. split; [exact HX1|]. split; [exact P21|]. split; [exact SB1 | exact MF1].
      +
        cbn [body_post] in HBP. destruct HBP as [HAP HBAD].
        exists R1, M1, pc1. split; [exact Hms1|]. cbn [wpost]. left. split; [exact HBAD | exact HAP].
    - cbn [body_post] in HBP. exists R1, M1, pc1. split; [exact Hms1 | cbn [wpost]; exact HBP].
  Qed.

  Lemma codelens_core : forall s c r R M,
    is_mode s = CODELENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> HREGc v s c r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f8c0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_CODELENS ivar_ref (cv_flush v) (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HP HM HRC HX HR.
    destruct HR as (HF & HV). pose proof HF as HF0. open_fixc HF. pose proof HV as HV0. open_vars HV.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    open_ictx C. pose proof HM as HM0. open_lmem HM. pose proof HP as HP'. open_pinv HP'. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    unfold mapped in *.
    destruct PS as (Hw1 & Hw2 & (Alens & Awork & Acodes) & Hs4 & Hs5 & QC & Hs7). destruct (QC Hmode) as (QN & QD & QH & CT & QL15).
    clear Hw1 Hw2 Hs4 Hs5 QC Hs7.
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (is6_nlen _ _ _ _ Msc) as C132. pose proof (is6_ndist _ _ _ _ Msc) as C136. pose proof (is6_have _ _ _ _ Msc) as C140.
    assert (Htot : 0 <= is_nlen s + is_ndist s < 2 ^ 31) by (clear - QN QD; lia).
    destruct (Z_lt_le_dec (is_have s) (is_nlen s + is_ndist s)) as [LT|GE].
    -
      destruct (cb_facts_of_pinv v s c r Hmode HP LT) as (HB & TC & NX).
      pose proof (tab_ok_root _ _ _ _ TC) as (Rt1 & Rt2 & Rt3).
      destruct HB as (Hhv & Hnl & Hnd & Htot' & Halen & Hlb & ELC & Blens).
      assert (Hofs : cofs_ok (is_lencode s)) by (rewrite ELC; cbn; lia).
      pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
      pose proof (is6_lenbits _ _ _ _ Msc) as C120. pose proof (is6_lencode _ _ _ _ Msc) as C104.
      change (codeptr_addr 75438 77486 (cv_S v) (is_lencode s)) with (ctab6 v (is_lencode s)) in C104.
      assert (Hc0 : 0 <= cext (is_lencode s)) by (rewrite ELC; cbn; lia).
      assert (Hh31 : 0 <= ir_have r < 2 ^ 31) by (clear - Rnh Rnx0 Rhv0 CI0; lia).
      arm_symexP (@nil (Z * expr)) ilCW 14%nat [false]
        [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 45%nat); RVal (EVar 48%nat); RVal (EVar 49%nat)]
        hpins [(45%nat, 2 ^ 31); (46%nat, 2 ^ 31); (47%nat, 2 ^ 31); (48%nat, 16); (49%nat, 2 ^ 63)] v r
        [is_have s; is_nlen s; is_ndist s; is_lenbits s; ctab6 v (is_lencode s)] NoVals F0
        (mkst R (Z_to_bv 64 0x1f8c0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTCC1" G end.
      assert (HPR : WREG v s r R1).
      { symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (16%bv : reg) as Q16.
        symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (14%bv : reg) as Q14.
        symex_reg HR1 (15%bv : reg) as Q15. rewrite ?mask_reg in Q15 by (clear - Rt1; lia).
        symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (31%bv : reg) as Q31.
        unfold WREG, BKc. split; [split; [lfixc_close Hfr1 HR1|]|];
          regs_via Hfr1; first [ exact Q12 | exact Q16 | exact Q13 | exact Q14 | exact Q15 | exact Q17 | exact Q31
                               | rewrite Q11; rewrite ?szwrap32_small by (clear - Htot; lia); f_equal; clear; lia
                               | rewrite Q16; rewrite ?Z.mod_small by (clear - Hhv Htot'; lia); f_equal; lia
                               | rewrite Q13; rewrite ?Z.mod_small by (clear - Rt1; lia); f_equal; lia
                               | rewrite Q31; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | match goal with |- ?G => idtac "WREG0 LEFT" G end ]. }
      destruct (cl_while 320%nat s c r R1 M Hmode HP LT ltac:(clear - QN QD QH; cbn; lia) HM0 HRC HX HPR) as (R2 & M2 & pc2 & Hms2 & HW).
      change 321%nat with (S 320).
      destruct (codelens_while (S 320) (mkW s c r)) as [u w2 | w2 | rc w2] eqn:EW; [| | destruct HW].
      + destruct u. cbn [wpost] in HW. destruct HW as [[HBAD HAP] | (M2' & GE2 & -> & HA2 & HM2 & HRC2 & HX2 & HP2 & SB2 & MF2)].
        * destruct w2 as [s2 c2 r2]. rewrite (arm_CODELENS_bad (cv_flush v) _ s2 c2 r2 EW HBAD).
          exists R2, M2, pc2. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HAP].
        * destruct w2 as [s2 c2 r2]. cbn [w_s w_c w_r] in *.
          destruct (cd_facts_of_pinv v s2 c2 r2 M2' HP2 GE2) as [HD2 Hret2].
          pose proof HP2 as HP2'. clear PNI PNO PL PX PB PC SR CI RI WI CR. open_pinv HP2'.
          destruct (codelens_segA v C ITABLE IFAST FFOK FASTOK GFOB FFRAME s2 c2 r2 R2 M2 M2' HD2 RI Hret2 (CLPINV _ _ _ _ s2 c2 r2 HP2 M2' GE2 Hret2) HM2 HRC2 HX2 HA2) as (R' & M' & pc' & Hms3 & HPOST).
          rewrite (arm_CODELENS_after (cv_flush v) _ s2 c2 r2 EW ltac:(rewrite M2'; cbv; discriminate)).
          exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
          exact (arm_post_chain v (mkW s c r) (mkW s2 c2 r2) M M2 _ _ _ _ SB2 MF2 HPOST).
      + cbn [wpost] in HW. rewrite (arm_CODELENS_leave (cv_flush v) _ _ EW).
        exists R2, M2, pc2. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HW].
    -
      arm_symexP (@nil (Z * expr)) ilCW 7%nat [true] [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 45%nat)]
        hpins [(45%nat, 2 ^ 31); (46%nat, 2 ^ 31); (47%nat, 2 ^ 31)] v r
        [is_have s; is_nlen s; is_ndist s] NoVals F0
        (mkst R (Z_to_bv 64 0x1f8c0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTCC2" G end.
      assert (HA : AREG v s c r R1).
      { symex_reg HR1 (12%bv : reg) as Q12.
        unfold AREG. split; [lfixc_close Hfr1 HR1|]. split; [| exact Q12].
        unfold LVARS. cbn [w_r]. regs_via Hfr1; match goal with |- ?G => idtac "AREG0 LEFT" G end. }
      destruct (cd_facts_of_pinv v s c r Hmode HP GE) as [HD Hret].
      destruct (codelens_segA v C ITABLE IFAST FFOK FASTOK GFOB FFRAME s c r R1 M Hmode HD RI0 Hret (CLPINV _ _ _ _ s c r HP Hmode GE Hret) HM0 HRC HX HA) as (R' & M' & pc' & Hms3 & HPOST).
      rewrite (arm_CODELENS_after (cv_flush v) _ s c r (cw_done 321 s c r GE) NB).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms3]; by_run Hms1 | exact HPOST].
  Qed.
End While.

Section Arm.
  Hypothesis ITABLE : itable_run6.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.
  Hypothesis CLPINV : cl_pinv_stmt.

  Theorem codelens_core_ok : forall v, ictx v -> codelens_core_stmt v.
  Proof. intros v C. exact (codelens_core v C ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV). Qed.

  Theorem arm_CODELENS_sim : arm_stmt CODELENS.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) CODELENS) with (arm_CODELENS ivar_ref (cv_flush v)).
    change (arm6_pc CODELENS) with 0x1f8c0.
    destruct HE as (HM & HRC & HX & (HF & HV & _)).
    exact (codelens_core v C ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV s c r R M Hmode HP HM HRC HX (conj (LFIX_LFIXc v R HF) HV)).
  Qed.
End Arm.
End FXG.
End InflA_Codelens10.
Export InflA_Codelens10.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ItCovIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInvCov.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInvTbl.
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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflA_Match2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflDec6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflA_Len3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflMem2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require InflA_ClS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require InflA_Cl1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require InflA_Cl2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflA_Dist3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InffastSafe IfSpec IfSpec6 InflA_LenF.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInvArms5.

Module InflA_Codelens7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.ItCovIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvCov.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvTbl.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S.Callee6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflA_Len3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflA_Len7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflMem2.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens5.
Import InflA_Cl2.InflA_Codelens6.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


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
    LFIX v R /\ LVARS v (mkW s c r) R /\ getr R 12 = zw (is_nlen s).

  Ltac open_cd HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & QN & QD & QL15 & Alens & Awork & Acodes & Blens & Bwork & Bcodes).

  Lemma codelens_segA : forall s c r R M,
    is_mode s = CODELENS -> cd_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> ir_ret r = 0 ->
    (arr_get (is_lens s) 256 <> 0 -> it_ret (cd_call1 s) = 0 -> it_ret (cd_call2 (cd_S1 s (cd_call1 s))) = 0 ->
       pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (iset_mode (cd_S2 (cd_S1 s (cd_call1 s)) (cd_call2 (cd_S1 s (cd_call1 s)))) LEN_) c (irset_ret r 0))) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> AREG s c r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d964) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (cd_after (cv_flush v) s c r) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI Hret0 HPL HM HRC HX HR. pose proof HD as HD0. open_cd HD.
    destruct HR as (HF & HV & G12). open_fix HF. open_vars HV.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
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
      arm_symex ilS 24%nat [true; true] [RVal (ELit 0); RVal (ELit (JT BAD))] [(12, EVar 45%nat)] [(45%nat, 512)] v r [is_nlen s] NoVals F0
        (mkst R (Z_to_bv 64 0x1d964) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (c' := icset_msg c MSG_invalid_code_missing_end_of_block) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66831)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (HM1 : LMEM v (mkW s c' r) M1) by (exact (LMEM_store_msg v C s c r M MSG_invalid_code_missing_end_of_block HM Hput)).
      assert (HM2 : LMEM v (mkW s' c' r) M2).
      { apply (LMEM_store_scalar v C s c' r _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_code_missing_end_of_block) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      exists R1, M2, (arm6_pc BAD). split; [subst M2 M1; by_run Hms1|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * apply (LX_step0 v s c r s' c' r HX NH NB); subst s' c'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_code_missing_end_of_block; lia].
        * symex_reg HR1 (9%bv : reg) as G8'. unfold LREG_arm. split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. split; [| intros _; exact G8'].
          unfold LVARS; cbn [w_r]. regs_via Hfr1; (symex_reg HR1 (27%bv : reg) as G26'; exact G26').
      + cbn [w_r]. subst M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    - replace (arr_get (is_lens s) 256 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
      arm_symex ilS 24%nat [false]
        [RVal (EVar 46%nat); RVal (EAdd (EVar 33%nat) (ELit 1384)); RVal (EAdd (EVar 33%nat) (ELit 160)); RVal (EAdd (EVar 33%nat) (ELit 136)); RVal (EAdd (EVar 33%nat) (ELit 808))]
        [(12, EVar 45%nat)] [(45%nat, 512); (46%nat, 65536)] v r [is_nlen s; arr_get (is_lens s) 256] NoVals F0
        (mkst R (Z_to_bv 64 0x1d964) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
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
      pose proof HM3 as HM3'. clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
      clear Fsv F104 F96 F88 F72 F56 F48 F40 F32 F24 F16 F8 Fd0 C664.
      open_lmem HM3'. unfold mapped in *.
      pose proof (is6_next _ _ _ _ Msc) as C144. pose proof (is6_lenbits _ _ _ _ Msc) as C120. cbn [w_s] in C144, C120.
      replace (is_next sC) with 0 in C144 by (subst sC sB sA; destruct s; reflexivity).
      replace (is_lenbits sC) with 9 in C120 by (subst sC sB sA; destruct s; reflexivity).
      replace (is_lens sC) with (is_lens s) in Mlens by (subst sC sB sA; destruct s; reflexivity).
      replace (is_work sC) with (is_work s) in Mwork by (subst sC sB sA; destruct s; reflexivity).
      replace (is_codes sC) with (is_codes s) in Mcodes by (subst sC sB sA; destruct s; reflexivity).
      symex_reg HR1 (10%bv : reg) as Q10. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (13%bv : reg) as Q13.
      symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (1%bv : reg) as Q1.
      destruct (ITABLE M3 R1 LENS (cv_S v) 0 (is_nlen s) 0 9 (cv_S v + 136) (cv_sp v - 224) (zw 0x1d99c) (is_lens s) (is_codes s) (is_work s)
                  Q10 ltac:(rewrite Q11; f_equal; lia) Q12 Q13 Q14 Q15 ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact P2) Q1
                  ltac:(apply ret_ok_lit; [lia | reflexivity]) ltac:(left; reflexivity)
                  ltac:(clear - CS; lia) ltac:(clear - CS; lia) ltac:(clear - CS; lia) CoS
                  ltac:(unfold ITFR6, IMG6_TOP in *; clear - Csp; lia) ltac:(clear - Csp; lia) ltac:(clear - Csp47; lia)
                  ltac:(clear - Csp; replace (cv_sp v - 224) with (cv_sp v + (-14) * 16) by lia; rewrite Z.mod_add by lia; destruct Csp as (_ & _ & E); exact E)
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
      (* 1.4: the length table's bits pointer is S + 136 (1.3.1: 120) *)
      assert (ES1 : iset_work (iset_codes (iset_next (if 136 =? 136 then iset_lenbits sC (it_bits r1) else iset_distbits sC (it_bits r1)) (it_table r1)) (it_tbl r1)) (it_work r1) = cd_S1 s r1)
        by (cbn [Z.eqb]; subst sC sB sA; unfold cd_S1; destruct s; reflexivity).
      pose proof (LMEM_itable v C sC c r M3 M4 136 (it_table r1) (it_bits r1) (it_tbl r1) (it_work r1) HM3 Hput ltac:(left; reflexivity)
                    (ITF_agree v 136 M3 M4 Tag) Tg Tcodes Twork Tnext Tbits) as HM4. rewrite ES1 in HM4.
      assert (HRC4 : RETC v (mkW (cd_S1 s r1) c r) M4).
      { apply (RETC_itable v C (mkW s c r) 136 M3 M4); [subst M3 M2 M1; retc_tower C HRC | left; reflexivity | exact (ITF_agree v 136 M3 M4 Tag)]. }
      assert (HX4 : LX v (mkW (cd_S1 s r1) c r)).
      { apply (LX_step0 v s c r _ c r HX NH NB); unfold cd_S1; try (destruct s; reflexivity); [destruct s; cbn; cbn in Xlive; exact Xlive | exact Xret | exact Xmsg]. }
      symex_reg HR1 (9%bv : reg) as Q8.
      assert (HB4 : BREG v (cd_S1 s r1) c r (it_ret r1) R3).
      { unfold BREG, INF_FRAME, LVARK. cbn [w_r]. split; [exact T2|].
        repeat match goal with |- _ /\ _ => split end;
          first [ exact T10
                | rewrite (Tfr (9%bv : reg) eq_refl); exact Q8
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Tfr n eq_refl), (Hfr1 n eq_refl); assumption end
                | match goal with |- ?G => idtac "BREG LEFT" G end ]. }
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
      { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 0x1f188) M3 s6_rom)); [subst M3 M2 M1; by_run Hms1 | eapply msteps_trans; [exact HmsT | exact Hms3]]. }
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
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.InflA_Dist3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S.Callee6i.
Import InflA_Cl1.InflArmLib6e.
Import InflA_Cl1.InflNeed6b.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens1.
Import InflA_Cl1.InflA_Codelens2.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Cl1.InflA_Codelens4.
Import InflA_Cl1.InflA_Codelens4b.
Import InflA_Cl1.InflA_Codelens5.
Import InflA_Cl2.InflA_Codelens6.
Import InflA_Codelens7.
Import InflA_Cl2.InflA_Codelens8.
Import InflA_Cl2.InflA_Codelens9.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

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

Definition ilCW : cfg := ilSx [0x1d73c; 0x1d964] [].

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
                       /\ pc' = 0x1d964 /\ AREG v (w_s w') (w_c w') (w_r w') R' /\ LMEM v w' M' /\ RETC v w' M' /\ LX v w'
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
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> PREG v s c r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d73c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
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
      + destruct (T1 eq_refl) as (M1' & H1 & B1). cbn [body_post] in HBP. destruct HBP as (-> & HW & HM1 & HRC1 & HX1 & SB1 & MF1).
        destruct w1 as [s1 c1 r1]. cbn [w_s w_r w_c] in *.
        destruct HW as ((HF & G18 & G1 & G14 & G12 & G16 & G15) & G13 & G22 & G23 & G9 & G26). open_fix HF.
        clear PNI PNO PL PS PX PB PC SR CI RI WI CR. open_pinv P21.
        pose proof RI as RIx. open_rinv RIx.
        assert (Hhv1 : 0 <= is_have s1 < 2 ^ 31).
        { destruct PS as (_ & _ & _ & _ & _ & QC1 & _). destruct (QC1 M1') as (QN1 & QD1 & QH1 & _). clear - QN1 QD1 QH1. lia. }
        assert (Htot1 : 0 <= is_nlen s1 + is_ndist s1 < 2 ^ 31) by (destruct HB as (Hhv & Hnl & Hnd & Htot & _); rewrite N1, D1; clear - Hhv Hnl Hnd Htot; lia).
        destruct (Z_lt_le_dec (is_have s1) (is_nlen s1 + is_ndist s1)) as [LT1|GE1].
        *
          arm_symex ilCW 6%nat [true] (@nil (option expr)) [(13, EVar 45%nat); (14, EVar 46%nat)] [(45%nat, 2 ^ 31); (46%nat, 2 ^ 31)] v r1
            [is_have s1; is_nlen s1 + is_ndist s1] NoVals F0
            (mkst R1 (Z_to_bv 64 0x1d958) M1 s6_rom) R2 HR2 Hfr2 Hms2.
          all: try arm_side.
          all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTW1" G end.
          assert (HPR1 : PREG v s1 c1 r1 R2).
          { symex_reg HR2 (6%bv : reg) as Q6. symex_reg HR2 (7%bv : reg) as Q7.
            unfold PREG, BKc. split; [split; [apply (LFIX_frame v R1 R2 _ HF Hfr2); reflexivity|]|];
              regs_via Hfr2; first [exact Q6 | exact Q7 | match goal with |- ?G => idtac "PREG1 LEFT" G end]. }
          destruct (IH s1 c1 r1 R2 M1 M1' P21 LT1 ltac:(clear - Hk H1 N1 D1 LT1; cbn in Hk |- *; lia) HM1 HRC1 HX1 HPR1)
            as (R' & M' & pc' & Hms3 & HW3).
         
          exists R', M', pc'. split.
          { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [| exact Hms3]. by_run Hms2. }
         
          exact (wpost_chain (mkW s c r) (mkW s1 c1 r1) M M1 _ _ _ _ SB1 MF1 HW3).
        *
          arm_symex ilCW 6%nat [false] (@nil (option expr)) [(13, EVar 45%nat); (14, EVar 46%nat)] [(45%nat, 2 ^ 31); (46%nat, 2 ^ 31)] v r1
            [is_have s1; is_nlen s1 + is_ndist s1] NoVals F0
            (mkst R1 (Z_to_bv 64 0x1d958) M1 s6_rom) R2 HR2 Hfr2 Hms2.
          all: try arm_side.
          all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTW2" G end.
          exists R2, M1, 0x1d964. split; [eapply msteps_trans; [exact Hms1|]; by_run Hms2|].
          rewrite (cw_done (S k) s1 c1 r1 GE1). cbn [wpost w_s w_c w_r]. right.
          split; [exact M1'|]. split; [exact GE1|]. split; [reflexivity|].
          split.
          { unfold AREG, LVARS. cbn [w_r]. split; [apply (LFIX_frame v R1 R2 _ HF Hfr2); reflexivity|].
            regs_via Hfr2; match goal with |- ?G => idtac "AREG1 LEFT" G end. }
         
          split; [exact HM1|]. split; [exact HRC1|]. split; [exact HX1|]. split; [exact P21|]. split; [exact SB1 | ]. exact MF1.
      +
       
        cbn [body_post] in HBP. destruct HBP as [HAP HBAD].
        exists R1, M1, pc1. split; [exact Hms1|]. cbn [wpost]. left. split; [exact HBAD | exact HAP].
    - cbn [body_post] in HBP. exists R1, M1, pc1. split; [exact Hms1 | cbn [wpost]; exact HBP].
  Qed.

  Definition HREG (s : inflate_state) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ LVARS v (mkW s c r) R /\ getr R 13 = zw (is_have s).

  Lemma codelens_core : forall s c r R M,
    is_mode s = CODELENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> HREG s c r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d710) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_CODELENS ivar_ref (cv_flush v) (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HP HM HRC HX HR.
    destruct HR as (HF & HV & G13). pose proof HF as HF0. open_fix HF. pose proof HV as HV0. open_vars HV.
    open_ictx C. pose proof HM as HM0. open_lmem HM. pose proof HP as HP'. open_pinv HP'. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF0 HV0) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    destruct PS as (Hw1 & Hw2 & (Alens & Awork & Acodes) & Hs4 & Hs5 & QC & Hs7). destruct (QC Hmode) as (QN & QD & QH & CT & QL15).
    clear Hw1 Hw2 Hs4 Hs5 QC Hs7.
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (is6_nlen _ _ _ _ Msc) as C132. pose proof (is6_ndist _ _ _ _ Msc) as C136.
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
      arm_symex ilCW 16%nat [false] [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 49%nat)]
        [(13, EVar 45%nat)] [(45%nat, 2 ^ 31); (46%nat, 2 ^ 31); (47%nat, 2 ^ 31); (48%nat, 16); (49%nat, 2 ^ 63)] v r
        [is_have s; is_nlen s; is_ndist s; is_lenbits s; ctab6 v (is_lencode s)] NoVals F0
        (mkst R (Z_to_bv 64 0x1d710) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTCC1" G end.
      assert (HPR : PREG v s c r R1).
      { symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (16%bv : reg) as Q16.
        rewrite mask_reg in Q16 by (clear - Rt1; lia).
        symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (7%bv : reg) as Q7.
        unfold PREG, BKc. split; [split; [apply (LFIX_frame v R R1 _ HF0 Hfr1); reflexivity|]|];
          regs_via Hfr1; first [exact Q12 | rewrite Q14; rewrite szwrap32_small by (clear - Htot; lia); f_equal; clear; lia | exact Q16 | exact Q15 | exact Q6 | exact Q7
                                 | match goal with |- ?G => idtac "PREG0 LEFT" G end]. }
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
      arm_symex ilCW 16%nat [true] [RVal (EVar 46%nat); RVal (EVar 47%nat)]
        [(13, EVar 45%nat)] [(45%nat, 2 ^ 31); (46%nat, 2 ^ 31); (47%nat, 2 ^ 31)] v r
        [is_have s; is_nlen s; is_ndist s] NoVals F0
        (mkst R (Z_to_bv 64 0x1d710) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTCC2" G end.
      assert (HA : AREG v s c r R1).
      { symex_reg HR1 (12%bv : reg) as Q12.
        unfold AREG. split; [apply (LFIX_frame v R R1 _ HF0 Hfr1); reflexivity|]. split; [| exact Q12].
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

  Theorem arm_CODELENS_sim : arm_stmt CODELENS.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) CODELENS) with (arm_CODELENS ivar_ref (cv_flush v)).
    change (arm6_pc CODELENS) with 0x1d190.
    destruct HE as (HM & HRC & HX & HR). destruct HR as (HF & HV & _). pose proof HF as HF0. open_fix HF. pose proof HV as HV0. open_vars HV.
    open_ictx C. pose proof HM as HM0. open_lmem HM. pose proof HP as HP'. open_pinv HP'. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF0 HV0) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    destruct PS as (Hw1 & Hw2 & (Alens & Awork & Acodes) & Hs4 & Hs5 & QC & Hs7). destruct (QC Hmode) as (QN & QD & QH & CT & QL15).
    clear Hw1 Hw2 Hs4 Hs5 QC Hs7.
    pose proof (is6_have _ _ _ _ Msc) as C140.
    arm_symex ilCW 6%nat (@nil bool) [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 31)] v r [is_have s] NoVals F0
      (mkst R (Z_to_bv 64 0x1d190) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTCA" G end.
    assert (HH : HREG v s c r R1).
    { symex_reg HR1 (13%bv : reg) as Q13.
      unfold HREG. split; [apply (LFIX_frame v R R1 _ HF0 Hfr1); reflexivity|]. split; [| exact Q13].
      unfold LVARS. cbn [w_r]. regs_via Hfr1; match goal with |- ?G => idtac "HREGA LEFT" G end. }
    destruct (codelens_core v C ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV s c r R1 M Hmode HP HM0 HRC HX HH) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.
End Arm.
End FXG.
End InflA_Codelens10.
Export InflA_Codelens10.


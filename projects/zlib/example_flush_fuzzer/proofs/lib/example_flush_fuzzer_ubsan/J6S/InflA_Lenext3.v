(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Distext1 InflA_Distext2 InflDec6 InflA_Dist3 InflA_Dist7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Lenext1 InflA_Lenext2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilXLA : cfg := CFG [] [] arm_rets (0x1d164 :: 0x1d9e8 :: arm_stops) [].

Section LenextCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lf HD :=
    destruct HD as (Hlen3 & Hex & Hle & HDD); pose proof HDD as HDD0;
    destruct HDD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Lemma lenext_nz : forall s c r R M,
    is_mode s = LENEXT -> lenext_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_extra s <> 0 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVARS v (mkW s c r) R ->
    getr R 13 = zw (is_extra s) ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d154) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_LENEXT ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI E0 HM HRC HX HF HV G13. pose proof HD as HD0. open_lf HD.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. pose proof RI as RI0. open_rinv RI. pose proof CI as CI0'. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    rewrite Z.shiftl_1_l in Hle.
    assert (Hex1 : 1 <= is_extra s <= 15) by (clear - Hex E0; lia).
    assert (P2e : 0 < 2 ^ is_extra s) by (apply Z.pow_pos_nonneg; lia).
    assert (Hl32 : is_length s + 2 ^ is_extra s <= 2 ^ 32) by (clear - Hle Hlen3; lia).
    destruct (Z_le_gt_dec (is_extra s) (ir_bits r)) as [GE|LT].
    +
      assert (HN : NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
      rewrite (arm_LENEXT_run s c r c r ltac:(clear - Hex1; lia) ltac:(lia) Hl32 HN ltac:(clear - GE Rbits; lia) Rhold).
      arm_symex ilXLA 8%nat [true] (@nil (option expr)) [(13, EVar 45%nat)] [(45%nat, 16)] v r [is_extra s] NoVals F0
        (mkst R (Z_to_bv 64 0x1d154) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      assert (HJ : XJE v (ir_bits r) (ir_have r) (ir_next r) (is_extra s) c r R1).
      { symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (15%bv : reg) as Q15.
        unfold XJE, XK. repeat match goal with |- _ /\ _ => split end;
          first [ apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | exact Q14 | exact Q12 | exact Q15 ]. }
      destruct (lenext_body v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD0 RI0 E0 GE HM HRC HX HJ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
    +
      arm_symex ilXLA 8%nat [false] (@nil (option expr)) [(13, EVar 45%nat)] [(45%nat, 16)] v r [is_extra s] NoVals F0
        (mkst R (Z_to_bv 64 0x1d154) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      assert (HJ : XJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s) c r R1).
      { symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (16%bv : reg) as Q16.
        unfold XJS, XK. repeat match goal with |- _ /\ _ => split end;
          first [ apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | exact Q14 | exact Q12 | exact Q16 | clear; lia | clear - Rbits; lia ]. }
      pose proof (need_loop v (is_extra s) 0x1d164 0x1d9e8 (XJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s)) (XJE v (ir_bits r) (ir_have r) (ir_next r) (is_extra s)) C ltac:(lia)
                    (lenext_step_H v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                    (lenext_step_E v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                    (lenext_dry v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                    8%nat s c r R1 M HM HRC HJ RI0 CI0' ltac:(lia) ltac:(cbn; clear - LT Rbits Hex1; lia)) as NL.
      change (NEEDBITS_k 8 (is_extra s)) with (NEEDBITS (is_extra s)) in NL.
      destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct NL].
      * destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        pose proof RI1 as X. unfold RINV in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb1 & Rh1).
        rewrite (arm_LENEXT_run s c r c r1 ltac:(clear - Hex1; lia) ltac:(lia) Hl32 EN ltac:(clear - Hb1 Rb1; lia) Rh1).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]).
        destruct (lenext_body v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD0 RI1 E0 ltac:(clear - Hb1; lia) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      * destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        rewrite (arm_LENEXT_leave s c r _ E0 EN).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
        cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
  Qed.
End LenextCore.

Theorem arm_LENEXT_sim : arm_stmt LENEXT.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LENEXT) with (arm_LENEXT ivar_ref).
  pose proof (lenext_facts_of_pinv v s c r Hmode HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  pose proof HM as HM0. pose proof HX as HX0. pose proof HF as HF0. pose proof HV as HV0.
  arm_begin C HM HRC HX HF HV HP.
  pose proof (is6_extra _ _ _ _ Msc) as C100.
  pose proof HD as HD'. destruct HD' as (_ & Hex & _).
  change (arm6_pc LENEXT) with 0x1d148.
  destruct (Z.eq_dec (is_extra s) 0) as [E0|E0].
  - rewrite (arm_LENEXT_zero s c r E0).
    arm_symex ilS 4%nat [false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 16)] v r [is_extra s] NoVals F0
      (mkst R (Z_to_bv 64 0x1d148) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    destruct (lenext_ztail v C s c r R1 M Hmode HD RI HM0 HRC HX0 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl)
                ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1)) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  - arm_symex ilS 4%nat [true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 16)] v r [is_extra s] NoVals F0
      (mkst R (Z_to_bv 64 0x1d148) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    symex_reg HR1 (13%bv : reg) as G13.
    destruct (lenext_nz v C s c r R1 M Hmode HD RI E0 HM0 HRC HX0 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl)
                ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1) G13) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
Qed.
End FXG.

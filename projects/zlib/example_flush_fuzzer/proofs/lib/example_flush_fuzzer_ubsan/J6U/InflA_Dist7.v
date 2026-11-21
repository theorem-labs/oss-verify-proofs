(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Distext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Distext3.InflA_Distext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflDec6. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Dist6. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Dist6.InflA_Dist1. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Dist2 InflA_Dist3. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Dist6. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Dist6.InflA_Dist4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Dist6. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Dist6.InflA_Dist5. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Dist6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilDE : cfg := ilSx [0x20dd0; 0x20d74] [].

Definition de_pins : list (Z * expr) :=
  [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
   (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))].

Section DistCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Ltac de_side Rhold64 Rt1 Rt2 TAB HJ1 HA0 HA1 Hext LE GT :=
    rewrite ?idx0_probe by (first [exact Rhold64 | clear - Rt1; lia]);
    rewrite ?cent_reasm, ?cent_bits;
    repeat match goal with |- context [?x mod 2 ^ 64] =>
      lazymatch x with context [BITSv _ _] => rewrite (Z.mod_small x (2 ^ 64)) by (generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia) end end;
    first [ lazymatch goal with |- exists bs, _ => match goal with |- context [BITSv ?h ?n] => tab_read2 TAB (BITSv h n); clear - HJ1 Rt2 Hext; lia end end
          | lazymatch goal with |- context [if _ <? _ then 1 else 0] => generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; ub_ptr_side end
          | lazymatch goal with |- exists _, _ => idtac end
          | generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia
          | clear - LE; lia
          | clear - GT; lia
          | idtac ].

  Lemma dist_core : forall s c r R M,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIXc v R -> LVARS v (mkW s c r) R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20cf0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_DIST ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI HM HRC HX HF HV. pose proof HD as HD0. open_dfacts HD.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fixc HF. open_vars HV. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_distcode s) C HM Hofs) as TAB.
    pose proof (BITSv_bound (ir_hold r) (is_distbits s) ltac:(lia)) as HJ1.
    pose proof (is6_distbits _ _ _ _ Msc) as C124. pose proof (is6_distcode _ _ _ _ Msc) as C112.
    change (codeptr_addr 75438 77486 (cv_S v) (is_distcode s)) with (ctab6 v (is_distcode s)) in C112.
    set (last := dent1 s (ir_hold r)).
    pose proof (tab_root_entry DISTS _ _ _ (BITSv (ir_hold r) (is_distbits s)) TD HJ1) as (HB & _). change (cat _ _ _) with last in HB.
    pose proof (code_bits_range last) as Hcb. pose proof (code_val_range last) as Hval. pose proof (clo_range last) as Hclo.
    pose proof (cent_range last) as Hcent. pose proof (cent_shr8_range last) as Hc8.
    assert (Hh31 : 0 <= ir_have r < 2 ^ 31) by (clear - Rnh Rnx0 Rhv0 CI0; lia).
    assert (ED1 : DECODE1 (is_distcode s) (is_distbits s) (mkW s c r)
                  = if code_bits last <=? ir_bits r then ARun last (mkW s c r)
                    else (PULLBYTE ;; DECODE_k 7 (is_distcode s) (fun h => BITSv h (is_distbits s)) code_bits)%am (mkW s c r)).
    { unfold DECODE1. rewrite DECODE_k_S. rewrite code_at_cat. reflexivity. }
    rewrite arm_DIST_dec1, ED1.
    destruct (Z.leb_spec (code_bits last) (ir_bits r)) as [LE|GT].
    -
      arm_symexP (@nil (Z * expr)) ilDE 36%nat [false; false; false; true] [RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat)] de_pins
        [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 65536); (48%nat, 65536)] v r
        [is_distbits s; ctab6 v (is_distcode s); code_val last; clo last] NoVals F0
        (mkst R (Z_to_bv 64 0x20cf0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: de_side Rhold64 Rt1 Rt2 TAB HJ1 HA0 HA1 Hext LE GT.
      all: match goal with |- ?G => idtac "LEFTDE1" G end.
      assert (HJE : DJE v s (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (29%bv : reg) as Q29. rewrite mask_reg in Q29 by (clear - Rt1; lia).
        symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (31%bv : reg) as Q31.
        symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (17%bv : reg) as Q17.
        symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (14%bv : reg) as Q14.
        symex_reg HR1 (30%bv : reg) as Q30. rewrite ?idx0_probe in Q30 by (first [exact Rhold64 | clear - Rt1; lia]). rewrite ?cent_reasm in Q30.
        symex_reg HR1 (7%bv : reg) as Q7. rewrite ?idx0_probe in Q7 by (first [exact Rhold64 | clear - Rt1; lia]). rewrite ?cent_reasm in Q7.
        symex_reg HR1 (28%bv : reg) as Q28. rewrite ?idx0_probe in Q28 by (first [exact Rhold64 | clear - Rt1; lia]). rewrite ?cent_reasm, ?cent_bits in Q28.
        unfold DJE, DK. split; [split; [lfixc_close Hfr1 HR1|]|]; subst last; unfold dent1;
          regs_via Hfr1; first [exact Q11 | exact Q29 | exact Q31 | exact Q12 | exact Q16 | exact Q17 | exact Q5 | exact Q6 | exact Q15 | exact Q14 | exact Q30 | exact Q7 | exact Q28
                               | rewrite Q13; ub_ptr_side
                               | rewrite Q13; destruct (Z.ltb_spec 0 (ctab6 v (is_distcode s))); [reflexivity | exfalso; clear - HA0 H; lia]
                               | rewrite Q31; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q16; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q17; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q15; rewrite ?Z.mod_small by (clear - Rbits; lia); f_equal; lia
                               | match goal with |- ?G => idtac "DJE LEFT" G end]. }
      destruct (dist_Q v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD0 RI0 LE HM HRC HX HJE) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
    -
      arm_symexP (@nil (Z * expr)) ilDE 36%nat [false; false; false; false] [RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat)] de_pins
        [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 65536); (48%nat, 65536)] v r
        [is_distbits s; ctab6 v (is_distcode s); code_val last; clo last] NoVals F0
        (mkst R (Z_to_bv 64 0x20cf0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: de_side Rhold64 Rt1 Rt2 TAB HJ1 HA0 HA1 Hext LE GT.
      all: match goal with |- ?G => idtac "LEFTDE2" G end.
      assert (HJS : DJS v s (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (29%bv : reg) as Q29. rewrite mask_reg in Q29 by (clear - Rt1; lia).
        symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (31%bv : reg) as Q31.
        symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (17%bv : reg) as Q17.
        symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (14%bv : reg) as Q14.
        unfold DJS, DK. split; [split; [lfixc_close Hfr1 HR1|]|];
          regs_via Hfr1; first [exact Q11 | exact Q29 | exact Q31 | exact Q12 | exact Q16 | exact Q17 | exact Q5 | exact Q6 | exact Q15 | exact Q14
                               | rewrite Q13; destruct (Z.ltb_spec 0 (ctab6 v (is_distcode s))); [reflexivity | exfalso; clear - HA0 H; lia]
                               | rewrite Q31; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q16; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q17; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q15; rewrite ?Z.mod_small by (clear - Rbits; lia); f_equal; lia
                               | clear; lia | clear - Rbits; lia
                               | match goal with |- ?G => idtac "DJS LEFT" G end]. }
      pose proof (dec_loop v s c (is_distcode s) (fun h => BITSv h (is_distbits s)) code_bits 15 0x20d74 0x20dd0
                    (DJS v s (ir_bits r) (ir_have r) (ir_next r)) (DJE v s (ir_bits r) (ir_have r) (ir_next r)) C ltac:(lia)
                    (fun h Hh => need1_bound DISTS _ _ _ h TD Hh)
                    CI'
                    (dist1_step_H v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext TD Hext Hofs CI')
                    (dist1_step_E v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext TD Hext Hofs CI')
                    (dist1_dry v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext TD Hext Hofs CI')
                    7%nat r R1 M HM HRC HJS RI0
                    ltac:(cbv beta; change (code_at s (is_distcode s) (BITSv (ir_hold r) (is_distbits s))) with last; exact GT)
                    ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
      destruct ((PULLBYTE ;; DECODE_k 7 (is_distcode s) (fun h => BITSv h (is_distbits s)) code_bits)%am (mkW s c r))
        as [last1 w1 | w1 | rc w1]; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh1 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
        subst last1. change (code_at s (is_distcode s) (BITSv (ir_hold r1) (is_distbits s))) with (dent1 s (ir_hold r1)) in Hb1 |- *.
        destruct (dist_Q v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD0 RI1 (proj1 Hb1) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
        cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.
End DistCore.

Theorem arm_DIST_sim : arm_stmt DIST.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DIST) with (arm_DIST ivar_ref).
  pose proof (dist_facts_of_pinv v s c r Hmode HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  pose proof HP as HP'. open_pinv HP'.
  change (arm6_pc DIST) with 0x20cf0.
  exact (dist_core v C s c r R M Hmode HD RI HM HRC HX (LFIX_LFIXc v R HF) HV).
Qed.
End FXG.

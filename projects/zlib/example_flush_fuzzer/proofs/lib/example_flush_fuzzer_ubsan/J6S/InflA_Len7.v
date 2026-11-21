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
     InflA_Match2 InflA_Distext1 InflA_Distext2 InflDec6 InflA_Dist3 InflA_Dist7 InflA_Lenext2 InflA_Lenext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Len1 InflA_Len2 InflA_Len3 InflA_Len4 InflA_Len5 InflA_Len6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InffastSafe IfSpec IfSpec6 InflA_LenF.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilLA : cfg := ilSx [0x1e42c] [].
Definition ilLE : cfg := ilSx [0x1e4a4; 0x1e45c] [].

Section LenCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Lemma len_entry : forall s c r R M,
    ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r ->   (* 1.4: three entry tests *)
    len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R ->
    exists R1,
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e3a0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1e42c) (wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 0)) s6_rom)
      /\ LFIX v R1 /\ LVARS v (mkW s c r) R1
      /\ getr R1 12 = zw (is_lenbits s) /\ getr R1 15 = zw (ctab6 v (is_lencode s)) /\ getr R1 13 = zw (cv_S v + 7160).
  Proof.
    intros s c r R M Hslow HD RI HM HF HV. open_lfacts HD.
    open_ictx C. open_lmem HM. open_fix HF. open_vars HV. open_rinv RI. open_frame Mfr.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (is6_lenbits _ _ _ _ Msc) as C120. pose proof (is6_lencode _ _ _ _ Msc) as C104.
    change (codeptr_addr 75438 77486 (cv_S v) (is_lencode s)) with (ctab6 v (is_lencode s)) in C104.
    destruct (Z_lt_le_dec (ir_have r) 6) as [H6|H6].
    - arm_symex ilLA 12%nat [true] [RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] (@nil (Z * expr))
        [(45%nat, 16); (46%nat, 2 ^ 63)] v r [is_lenbits s; ctab6 v (is_lencode s)] NoVals F0
        (mkst R (Z_to_bv 64 0x1e3a0) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTLA1" G end.
      exists R1. split; [by_run Hms1|].
      symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (13%bv : reg) as Q13.
      split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1|].
      split; [exact Q12|]. split; [exact Q15 | exact Q13].
    - destruct (Z_lt_le_dec (ir_left r) 258) as [Hleft|Hleft].
      + arm_symex ilLA 12%nat [false; true] [RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] (@nil (Z * expr))
          [(45%nat, 16); (46%nat, 2 ^ 63)] v r [is_lenbits s; ctab6 v (is_lencode s)] NoVals F0
          (mkst R (Z_to_bv 64 0x1e3a0) M s6_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTLA2" G end.
        exists R1. split; [by_run Hms1|].
        symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (13%bv : reg) as Q13.
        split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1|].
        split; [exact Q12|]. split; [exact Q15 | exact Q13].
      + (* 1.4: the third test, li a2,7; bltu a2,s8: bits >= 8 goes to the slow path too *)
        assert (Hbits : 8 <= ir_bits r) by (clear - Hslow H6 Hleft; lia).
        arm_symex ilLA 14%nat [false; false; true] [RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] (@nil (Z * expr))
          [(45%nat, 16); (46%nat, 2 ^ 63)] v r [is_lenbits s; ctab6 v (is_lencode s)] NoVals F0
          (mkst R (Z_to_bv 64 0x1e3a0) M s6_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTLA3" G end.
        exists R1. split; [by_run Hms1|].
        symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (13%bv : reg) as Q13.
        split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1|].
        split; [exact Q12|]. split; [exact Q15 | exact Q13].
  Qed.

  Lemma len_core : forall s c r R M,
    ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r ->
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVARS v (mkW s c r) R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e3a0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_LEN ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hslow Hmode HD RI HM HRC HX HF HV.
    destruct (len_entry s c r R M Hslow HD RI HM HF HV) as (R0 & Hms0 & HF0 & HV0 & E12 & E15 & E13).
    clear HF HV. open_lfacts HD.
    open_ictx C. open_retc HRC. open_lx HX. open_fix HF0. open_vars HV0. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF0 HV0) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    set (s1 := iset_back s 0) in *.
    set (last := lent1 s1 (ir_hold r)).
    pose proof (tab_root_entry LENS _ _ _ (BITSv (ir_hold r) (is_lenbits s)) TL HJ1) as (HB & _). change (cat _ _ _) with last in HB.
    pose proof (code_bits_range last) as Hcb.
    assert (HD1 : len_facts v s1 c).
    { apply len_facts_back. unfold len_facts. refine (conj Hsane (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj CI' (conj _ (conj Hlofs (conj _ Hdofs)))))))))); eexists; split; eassumption. }
    assert (ED1 : DECODE1 (is_lencode s) (is_lenbits s) (mkW s1 c r)
                  = if code_bits last <=? ir_bits r then ARun last (mkW s1 c r)
                    else (PULLBYTE ;; DECODE_k 7 (is_lencode s1) (fun h => BITSv h (is_lenbits s1)) code_bits)%am (mkW s1 c r)).
    { unfold DECODE1. rewrite DECODE_k_S. rewrite code_at_cat. subst last s1. reflexivity. }
    rewrite (arm_LEN_dec1' s c r Hslow). change (iset_back s 0) with s1. rewrite ED1.
    set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 0)) in *.
    assert (HM1 : LMEM v (mkW s1 c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_back M (cv_S v) _ s _ (lm_sc _ _ _ HM)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC1 : RETC v (mkW s1 c r) M1) by (subst M1; retc_tower C HRC).
    assert (HX1 : LX v (mkW s1 c r)) by (apply (LX_step0 v s c r s1 c r HX NH NB); subst s1; try reflexivity; [exact Xlive | exact Xret | exact Xmsg]).
    pose proof (ctab6_cells v s1 c r M1 (is_lencode s) C HM1 Hlofs) as TAB1.
    open_lmem HM1. unfold mapped in *.
    assert (MF1 : MFRAME v (ir_put r) (ir_put r) M M1).
    { subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
    assert (SB1 : same_blocks s s1) by (subst s1; split; [reflexivity | split; reflexivity]).
    destruct (Z.leb_spec (code_bits last) (ir_bits r)) as [LE|GT].
    -
      arm_symex ilLE 16%nat [true] [RVal (EVar 47%nat)] [(12, EVar 45%nat); (15, EVar 46%nat); (13, EAdd (EVar 33%nat) (ELit 7160))]
        [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 16)] v r
        [is_lenbits s; ctab6 v (is_lencode s); code_bits last] NoVals F0
        (mkst R0 (Z_to_bv 64 0x1e42c) M1 s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: rewrite ?idx0_probe by (first [exact Rhold64 | clear - Rt1; lia]).
      all: try (subst last s1; unfold lent1; cbn [is_codes is_lencode is_lenbits iset_back]; tab_read TAB1 (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 HextL; lia).
      all: try (generalize HJ1; clear - HA0 HA1 Rt2 HextL; intro; lia).
      all: match goal with |- ?G => idtac "LEFTLE1" G end.
      assert (HJE : LJE v s1 (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (16%bv : reg) as Q16. rewrite mask_reg in Q16 by (clear - Rt1; lia).
        symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (26%bv : reg) as Q27. symex_reg HR1 (13%bv : reg) as Q13.
        symex_reg HR1 (17%bv : reg) as Q17. rewrite idx0_probe in Q17 by (first [exact Rhold64 | clear - Rt1; lia]).
        symex_reg HR1 (14%bv : reg) as Q14.
        unfold LJE, LK1. split; [split; [apply (LFIX_frame v R0 R1 _ HF0 Hfr1); reflexivity|]|]; subst last s1; unfold lent1; cbn [is_codes is_lencode is_lenbits iset_back];
          regs_via Hfr1; first [exact Q16 | exact Q15 | exact Q12 | exact Q27 | exact Q13 | rewrite Q17; f_equal; lia | exact Q14
                               | match goal with |- ?G => idtac "LJE LEFT" G end]. }
      destruct (len_Q v C s1 c r R1 M1 (ir_bits r) (ir_have r) (ir_next r) ltac:(exact Hmode) HD1 RI0 ltac:(reflexivity) LE
                  ltac:(constructor; assumption) HRC1 HX1 HJE) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms0 | eapply msteps_trans; [| exact Hms2]; by_run Hms1]|].
      exact (arm_post_chain v (mkW s c r) (mkW s1 c r) M M1 _ _ _ _ SB1 MF1 HPOST).
    -
      arm_symex ilLE 16%nat [false] [RVal (EVar 47%nat)] [(12, EVar 45%nat); (15, EVar 46%nat); (13, EAdd (EVar 33%nat) (ELit 7160))]
        [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 16)] v r
        [is_lenbits s; ctab6 v (is_lencode s); code_bits last] NoVals F0
        (mkst R0 (Z_to_bv 64 0x1e42c) M1 s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: rewrite ?idx0_probe by (first [exact Rhold64 | clear - Rt1; lia]).
      all: try (subst last s1; unfold lent1; cbn [is_codes is_lencode is_lenbits iset_back]; tab_read TAB1 (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 HextL; lia).
      all: try (generalize HJ1; clear - HA0 HA1 Rt2 HextL; intro; lia).
      all: match goal with |- ?G => idtac "LEFTLE2" G end.
      assert (HJS : LJS v s1 (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (16%bv : reg) as Q16. rewrite mask_reg in Q16 by (clear - Rt1; lia).
        symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (13%bv : reg) as Q13.
        unfold LJS, LK1. split; [split; [apply (LFIX_frame v R0 R1 _ HF0 Hfr1); reflexivity|]|]; subst s1; cbn [is_lencode is_lenbits iset_back];
          regs_via Hfr1; first [exact Q16 | exact Q15 | exact Q12 | exact Q6 | exact Q5 | exact Q13 | clear; lia | clear - Rbits; lia
                               | match goal with |- ?G => idtac "LJS LEFT" G end]. }
      pose proof (dec_loop v s1 c (is_lencode s1) (fun h => BITSv h (is_lenbits s1)) code_bits 15 0x1e45c 0x1e4a4
                    (LJS v s1 (ir_bits r) (ir_have r) (ir_next r)) (LJE v s1 (ir_bits r) (ir_have r) (ir_next r)) C ltac:(lia)
                    (fun h Hh => need1_bound LENS _ _ _ h TL Hh)
                    CI'
                    (len1_step_H v s1 c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 extL TL HextL Hlofs CI')
                    (len1_step_E v s1 c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 extL TL HextL Hlofs CI')
                    (len1_dry v s1 c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 extL TL HextL Hlofs CI')
                    7%nat r R1 M1 ltac:(constructor; assumption) HRC1 HJS RI0
                    ltac:(cbv beta; change (code_at s1 (is_lencode s1) (BITSv (ir_hold r) (is_lenbits s1))) with last; exact GT)
                    ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
      destruct ((PULLBYTE ;; DECODE_k 7 (is_lencode s1) (fun h => BITSv h (is_lenbits s1)) code_bits)%am (mkW s1 c r))
        as [last1 w1 | w1 | rc w1]; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh1 & Hb1 & HM1' & HRC1').
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        assert (HX1' : LX v (mkW s1 c r1)) by (apply (LX_step0 v s c r s1 c r1 HX NH NB); subst s1; try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]).
        subst last1. change (code_at s1 (is_lencode s1) (BITSv (ir_hold r1) (is_lenbits s1))) with (lent1 s1 (ir_hold r1)) in Hb1 |- *.
        destruct (len_Q v C s1 c r1 R2 M1 (ir_bits r) (ir_have r) (ir_next r) ltac:(exact Hmode) HD1 RI1 ltac:(reflexivity) (proj1 Hb1) HM1' HRC1' HX1' HJE) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms0 | eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1]|].
        apply (arm_post_chain v (mkW s c r) (mkW s1 c r) M M1 _ _ _ _ SB1 MF1).
        apply (arm_post_rebase v s1 c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1' & HRC1').
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        exists R2, M1, pc6_leave. split; [eapply msteps_trans; [exact Hms0 | eapply msteps_trans; [| exact Hms2]; by_run Hms1]|].
        apply (arm_post_chain v (mkW s c r) (mkW s1 c r) M M1 _ _ _ _ SB1 MF1).
        cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1'|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s1 c r1 HX NH NB); subst s1; try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
  Qed.
End LenCore.

Theorem arm_LEN_sim : inflate_fast_spec6 -> ffok_stmt -> fastok_stmt -> gfast_ob_stmt -> fframe_stmt -> arm_stmt LEN.
Proof.
  intros IFAST FFOK FASTOK GFOB FFRAME v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LEN) with (arm_LEN ivar_ref).
  pose proof (len_facts_of_pinv v s c r Hmode HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  pose proof HP as HP'. open_pinv HP'.
  change (arm6_pc LEN) with 0x1e3a0.
  destruct (Z_lt_le_dec (ir_have r) 6) as [Hh|Hh]; [exact (len_core v C s c r R M (or_introl Hh) Hmode HD RI HM HRC HX HF HV)|].
  destruct (Z_lt_le_dec (ir_left r) 258) as [Hl|Hl]; [exact (len_core v C s c r R M (or_intror (or_introl Hl)) Hmode HD RI HM HRC HX HF HV)|].
  (* 1.4: bits >= 8 also takes the slow path *)
  destruct (Z_lt_le_dec (ir_bits r) 8) as [Hb|Hb]; [| exact (len_core v C s c r R M (or_intror (or_intror Hb)) Hmode HD RI HM HRC HX HF HV)].
  exact (lenF_core v C IFAST FFOK FASTOK GFOB FFRAME s c r R M HP Hmode HD HM HRC HX HF HV Hh Hl Hb).
Qed.


Lemma len_facts_of_pinv_live : forall v s c r,
  codes_live (is_mode s) = true -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> len_facts v s c.
Proof.
  intros v s c r Hlive HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  pose proof (len_tab s PS Hlive) as LT. pose proof (dist_tab s PS Hlive) as DT.
  pose proof (sr_lofs s SR) as Hlofs. pose proof (sr_dofs s SR) as Hdofs.
  unfold len_facts. repeat (split; [assumption|]). exact Hdofs.
Qed.

Lemma len_facts_mode : forall v s c m, len_facts v s c -> len_facts v (iset_mode s m) c.
Proof.
  intros v s c m HD. destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & LT & Hlofs & DT & Hdofs).
  unfold len_facts. destruct s; cbn in *. repeat (split; [assumption || exact LT || exact DT|]). exact Hdofs.
Qed.

Section LenU.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.

  Lemma len__core : forall s c r R M,
    pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    is_mode s = LEN_ -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVARS v (mkW s c r) R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e398) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_LEN_ ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M HP Hmode HD RI HM HRC HX HF HV.
    unfold arm_LEN_. mstep1 set_mode_eq.
    pose proof HF as HF0. pose proof HV as HV0.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. pose proof RI as RI0. open_rinv RI.
    pose proof (pins_of_regs _ _ _ _ _ HF0 HV0) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    arm_symex ilS 4%nat (@nil bool) (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1e398) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16200)) in *.
    set (s1 := iset_mode s LEN).
    assert (HM1 : LMEM v (mkW s1 c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s LEN Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC1 : RETC v (mkW s1 c r) M1) by (subst M1; retc_tower C HRC).
    assert (HX1 : LX v (mkW s1 c r)) by (apply (LX_step0 v s c r s1 c r HX NH NB); subst s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]).
    assert (K : exists R' M' pc', msteps s6_segs (mkst R1 (Z_to_bv 64 0x1e3a0) M1 s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
                                 /\ arm_post v (mkW s1 c r) M1 (arm_LEN ivar_ref (mkW s1 c r)) R' M' pc').
    { destruct (Z_lt_le_dec (ir_have r) 6) as [Hh|Hh]; [| destruct (Z_lt_le_dec (ir_left r) 258) as [Hl|Hl];
                                                         [| destruct (Z_lt_le_dec (ir_bits r) 8) as [Hb|Hb]]].
      - exact (len_core v C s1 c r R1 M1 (or_introl Hh) ltac:(reflexivity) (len_facts_mode v s c LEN HD) RI0 HM1 HRC1 HX1
                 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl) ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1)).
      - exact (len_core v C s1 c r R1 M1 (or_intror (or_introl Hl)) ltac:(reflexivity) (len_facts_mode v s c LEN HD) RI0 HM1 HRC1 HX1
                 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl) ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1)).
      -
        exact (lenF_core v C IFAST FFOK FASTOK GFOB FFRAME s1 c r R1 M1 (pinv_LEN__LEN _ _ _ _ s c r HP Hmode) ltac:(reflexivity)
                 (len_facts_mode v s c LEN HD) HM1 HRC1 HX1 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl) ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1) Hh Hl Hb).
      - (* 1.4: bits >= 8 takes the slow path *)
        exact (len_core v C s1 c r R1 M1 (or_intror (or_intror Hb)) ltac:(reflexivity) (len_facts_mode v s c LEN HD) RI0 HM1 HRC1 HX1
                 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl) ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1)). }
    destruct K as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r) (mkW s1 c r) M M1); [subst s1; apply same_blocks_mode | | exact HPOST].
    cbn [w_r]. subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End LenU.

Theorem arm_LEN__sim : inflate_fast_spec6 -> ffok_stmt -> fastok_stmt -> gfast_ob_stmt -> fframe_stmt -> arm_stmt LEN_.
Proof.
  intros IFAST FFOK FASTOK GFOB FFRAME v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LEN_) with (arm_LEN_ ivar_ref).
  pose proof (len_facts_of_pinv_live v s c r ltac:(rewrite Hmode; reflexivity) HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  pose proof HP as HP'. open_pinv HP'.
  change (arm6_pc LEN_) with 0x1e398.
  exact (len__core v C IFAST FFOK FASTOK GFOB FFRAME s c r R M HP Hmode HD RI HM HRC HX HF HV).
Qed.
End FXG.

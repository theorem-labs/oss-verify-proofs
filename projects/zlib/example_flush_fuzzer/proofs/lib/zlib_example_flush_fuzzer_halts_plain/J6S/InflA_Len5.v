(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Distext1 InflA_Distext2 InflDec6 InflA_Dist3 InflA_Dist7 InflA_Lenext2 InflA_Lenext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflA_Len1 InflA_Len2 InflA_Len3 InflA_Len4.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition ilLT : cfg := ilSx [0x1e590] [].

Lemma opm1_term : forall op, 0 <= op < 256 -> (op = 0 \/ 16 <= op) -> 14 < (op + -1) mod 2 ^ 64.
Proof.
  intros op Hop [E|GE]; [rewrite E; change ((0 + -1) mod 2 ^ 64) with 18446744073709551615; lia|]. rewrite Z.mod_small by lia. lia.
Qed.
Lemma opm1_link : forall op, 1 <= op <= 15 -> (op + -1) mod 2 ^ 64 <= 14.
Proof. intros op Hop. rewrite Z.mod_small by lia. lia. Qed.

Section LenT.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Definition ltpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168)); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (27, EAdd (EVar 33%nat) (ELit 7160));
     (5, EVar 36%nat); (31, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EVar 41%nat);
     (7, EVar 45%nat); (16, EVar 46%nat); (14, EVar 46%nat); (17, EVar 47%nat); (15, EVar 48%nat);
     (30, EVar 49%nat); (28, EVar 50%nat)].
  Definition ltvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 63); (50%nat, 256); (51%nat, 256); (52%nat, 65536)].

  Lemma len_T : forall s c r R M b1 h1 n1 last,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    1 <= code_op last <= 15 - is_lenbits s -> code_bits last = is_lenbits s ->
    (forall j, 0 <= j < 2 ^ code_op last ->
       term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_lencode s)) ->
    wrap32 (code_bits last + code_bits (lent2 s last (ir_hold r))) <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LJE2 v s b1 h1 n1 last r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e56c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (len_res (lent2 s last (ir_hold r)) (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M b1 h1 n1 last Hmode HD RI Hbk LK LB SUB (ext' & TL' & LXT & Hext') Hneed HM HRC HX HJ. pose proof HD as HD0. open_lfacts HD.
    pose proof HJ as X. unfold LJE2, LK2 in X.
    destruct X as ((G2 & G25 & G10 & G11 & G21 & G19 & G24 & G3 & G4 & G18 & G1 & G9 & G12 & G13 & G27 & G7 & G16 & G14 & G17 & G15) & G22 & G5 & G31 & G6 & G30 & G28).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL') as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hlofs) as TAB.
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hlv.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    set (J := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_lencode s) J) in *.
    assert (Ehere : lent2 s last (ir_hold r) = here) by reflexivity. rewrite Ehere in Hneed, G28 |- *.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE.
    destruct (term_ok_LENS _ _ TE) as (Bh & _).
    pose proof (code_bits_range here) as Hcb. pose proof (code_op_range here) as Hop. pose proof (code_val_range here) as Hval.
    rewrite wrap32_id in Hneed by (clear - Bh Rt1 LB Hcb; lia).
    arm_symexP (@nil (Z * expr)) ilLT 20%nat (@nil bool)
      [RVal (EVar 51%nat); RVal (EVar 52%nat); RVal (ELit 18446744073709535436); RVal (ELit 75024)] ltpins ltvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_lencode s);
       ctab6 v (is_lencode s) + 4 * J; code_bits here; code_op here; code_val here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e56c) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: subst here J.
    all: try (tab_read TAB (code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)); clear - HJ2 LXT Hext' Hlv; lia).
    all: match goal with |- ?G => idtac "LEFTLT" G end.
    set (J := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_lencode s) J) in *.
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits last) RI ltac:(clear - Hneed Bh Rt1 LB; lia)) as [EW RI'].
    unfold rdrop. rewrite EW.
    set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits last))) (ir_bits r - code_bits last)) in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HM' : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r c r' M HM); subst r'; reflexivity).
    assert (HRC' : RETC v (mkW s c r') M) by (apply (RETC_regs v (mkW s c r)); [exact HRC | subst r'; reflexivity]).
    assert (HX' : LX v (mkW s c r')) by (apply (LX_step0 v s c r s c r' HX NH NB); subst r'; try reflexivity; [exact Xlive | exact Xret | exact Xmsg]).
    symex_reg HR1 (31%bv : reg) as Q31. change 18446744073709535436 with ((-16180) mod 2 ^ 64) in Q31. rewrite zw_neg_mod in Q31.
    symex_reg HR1 (29%bv : reg) as Q29. symex_reg HR1 (30%bv : reg) as Q30.
    symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (26%bv : reg) as Q27.
    symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (7%bv : reg) as Q7'. symex_reg HR1 (17%bv : reg) as Q17'.
    rewrite zalu_srl_small in Q23 by (clear - Rhold64 Rt1 LB; lia).
    rewrite szwrap32_small in Q13 by (clear - Hneed Bh Rbits Rt1 LB; lia).
    assert (HFR : LFREG v s r' here (is_back s + code_bits last) R1).
    { unfold LFREG, LFIX, INF_FRAME, A6_JTAB. subst r'. cbn [ir_put ir_left ir_out ir_hold ir_bits ir_have ir_next irset_bits irset_hold].
      rewrite Z.shiftr_div_pow2 by (clear - Rt1 LB; lia). rewrite Hbk, Z.add_0_l.
      regs_via Hfr1; first [exact Q31 | exact Q29 | exact Q30 | exact Q23 | exact Q13 | exact Q12 | exact Q27 | exact Q14 | exact Q7' | exact Q17'
                           | match goal with |- ?G => idtac "LFREG LEFT" G end]. }
    destruct (len_fin v C s c r' R1 M here (is_back s + code_bits last) (15 - is_lenbits s) Hmode HD0 RI' TE
                ltac:(subst r'; cbn; clear - Hneed; lia) HM' HRC' HX' HFR) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
    apply (arm_post_rebase v s c r c r'); [subst r'; reflexivity | exact HPOST].
  Qed.

  Definition lqpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (13, EVar 41%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat));
     (16, EVar 45%nat); (15, EVar 46%nat); (17, EVar 47%nat); (14, EVar 48%nat)].
  Definition lqvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 16); (49%nat, 256); (50%nat, 65536)].

  Lemma len_Q_term : forall s c r R M b0 h0 n0,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    let last := lent1 s (ir_hold r) in
    code_bits last <= ir_bits r -> term_ok LENS (is_lenbits s) last = true -> (code_op last = 0 \/ 16 <= code_op last) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e4a4) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (len_res last (is_back s) s c r) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 Hmode HD RI Hbk last Hlb TM OT HM HRC HX HJ. pose proof HD as HD0. open_lfacts HD.
    pose proof HJ as X. unfold LJE, LK1 in X.
    destruct X as ((HF & G18 & G1 & G23 & G9 & G26 & G16 & G15) & G22 & G12 & G27 & G13 & G17 & G14). open_fix HF.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hlofs) as TAB.
    pose proof (ones_range15 (is_lenbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    destruct (term_ok_LENS _ _ TM) as (Bh & _).
    arm_symexP (@nil (Z * expr)) ilLT 14%nat [true]
      [RVal (EVar 49%nat); RVal (EVar 50%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] lqpins lqvb v r
      [Z.ones (is_lenbits s); ctab6 v (is_lencode s); ctab6 v (is_lencode s) + 4 * BITSv (ir_hold r) (is_lenbits s); code_bits last;
       code_op last; code_val last] NoVals F0
      (mkst R (Z_to_bv 64 0x1e4a4) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: try (subst last; unfold lent1; tab_read TAB (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 HextL; lia).
    1: exact (opm1_term (code_op last) Hop OT).
    symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (27%bv : reg) as Q24. symex_reg HR1 (7%bv : reg) as Q7. symex_reg HR1 (17%bv : reg) as Q17'.
    assert (HFR : LFREG v s r last (is_back s) R1).
    { unfold LFREG. split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. rewrite Hbk.
      regs_via Hfr1; first [exact Q24 | exact Q16 | exact Q7 | exact Q17' | match goal with |- ?G => idtac "LFREG1 LEFT" G end]. }
    destruct (len_fin v C s c r R1 M last (is_back s) (is_lenbits s) Hmode HD0 RI0 TM Hlb HM HRC HX HFR) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.
End LenT.
End FXG.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflDec6 InflA_Match2 InflA_Dist3 InflA_Len5 InflA_Len3 InflA_Len4.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Dist6.

Module InflA_Len6.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.InflA_Distext2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist3 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len5.InflA_Len1 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len5.InflA_Len2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len3 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len4 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len5.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilLL : cfg := ilSx [0x20c78; 0x20be8; 0x20bec; 0x20c58] [].

Section LenQL.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Definition LQREG (s : inflate_state) (r : iregs) (last here J2 : Z) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 31 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r)
    /\ getr R 21 = zw (ir_bits r) /\ getr R 19 = zw (code_bits last) /\ getr R 11 = zw (ir_bits r) /\ getr R 16 = zw (ir_bits r)
    /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 17 = zw (ir_have r) /\ getr R 5 = zw (8 * ir_have r)
    /\ getr R 13 = zw (ctab6 v (is_lencode s)) /\ getr R 15 = zw 1
    /\ getr R 30 = zw (Z.ones (code_bits last + code_op last)) /\ getr R 7 = zw (code_bits last) /\ getr R 29 = zw (code_val last)
    /\ getr R 28 = zw (cent last / 2 ^ 8)
    /\ getr R 20 = zw (cent here) /\ getr R 22 = zw (cent here / 2 ^ 8)
    /\ getr R 23 = zw (code_bits here + code_bits last).

  Definition llpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (31, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat));
     (21, EVar 41%nat); (19, EVar 46%nat); (11, EVar 41%nat); (16, EVar 41%nat);
     (14, EAdd (EVar 43%nat) (EVar 44%nat)); (17, EVar 36%nat); (5, EMul (ELit 8) (EVar 36%nat));
     (13, EVar 48%nat); (15, ELit 1); (30, EVar 45%nat); (7, EVar 46%nat); (29, EVar 47%nat); (28, EVar 49%nat);
     (20, EVar 50%nat); (22, EVar 51%nat); (23, EAdd (EVar 52%nat) (EVar 46%nat))].
  Definition llvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 24); (50%nat, 2 ^ 32); (51%nat, 2 ^ 24); (52%nat, 16)].

  Lemma len_QL_pre : forall s c r R M b0 h0 n0,
    len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := lent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_lencode s) J2 in
    1 <= code_op last <= 15 - is_lenbits s -> code_bits last = is_lenbits s ->
    (exists ext, tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_lencode s)) ->
    code_bits here <= 15 ->
    LMEM v (mkW s c r) M -> LJE v s b0 h0 n0 r R ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20b50) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20be8) M s6u_rom)
      /\ LQREG s r last here J2 R1.
  Proof.
    intros s c r R M b0 h0 n0 HD RI last J2 here LK LB (ext' & TL' & LXT & Hext') Bh HM HJ. open_lfacts HD.
    pose proof HJ as X. unfold LJE, LK1 in X.
    destruct X as ((HF & G9 & G13 & G29 & G15 & G18 & G24 & G25 & G30) & G22 & G12 & G17 & G5 & G14 & G6 & G16 & G11 & G19 & G28 & G7). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G12 as P12.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hlofs) as TAB.
    pose proof (ones_range15 (is_lenbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    pose proof (cent_range last) as Hcent. pose proof (cent_shr8_range last) as Hc8.
    pose proof (code_bits_range here) as Hcb2. pose proof (code_val_range here) as Hval2. pose proof (clo_range here) as Hclo2.
    pose proof (cent_range here) as Hcent2. pose proof (cent_shr8_range here) as Hc82.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (land57344_cent last ltac:(clear - Rt1 LB; lia)) as L57344.
    pose proof (opm1_link (code_op last) ltac:(clear - LK Rt1; lia)) as OPM.
    arm_symexP (@nil (Z * expr)) ilLL 42%nat [false; false; false; false; false]
      [RVal (EVar 53%nat); RVal (EVar 54%nat)] lqpins
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 32); (48%nat, 2 ^ 24); (49%nat, 16); (53%nat, 65536); (54%nat, 65536)] v r
      [Z.ones (is_lenbits s); ctab6 v (is_lencode s); cent last; cent last / 2 ^ 8; code_bits last; 0; 0; 0; code_val here; clo here] NoVals F0
      (mkst R (Z_to_bv 64 0x20b50) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: rewrite ?cent_op, ?cent_val.
    all: try arm_side.
    all: rewrite ?idx2_probe by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    all: rewrite ?idx2_probe_w by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    all: rewrite ?cent_reasm, ?cent_bits.
    all: try (subst here J2; tab_read2 TAB (code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)); clear - HJ2 LXT Hext' Hval; lia).
    all: try (generalize HJ2; clear - HA0 HA1 LXT Hext' Hval; intro; lia).
    all: try ub_ptr_side.
    all: match goal with |- ?G => idtac "LEFTLQL" G end.
    exists R1. split; [by_run Hms1|].
    symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (21%bv : reg) as Q20. symex_reg HR1 (31%bv : reg) as Q31.
    symex_reg HR1 (30%bv : reg) as Q30. rewrite ?cent_op in Q30. rewrite mask_reg in Q30 by (clear - Rt1 LK LB; lia).
    symex_reg HR1 (29%bv : reg) as Q29. rewrite ?cent_val in Q29.
    symex_reg HR1 (20%bv : reg) as Q19. rewrite ?cent_reasm in Q19.
    symex_reg HR1 (22%bv : reg) as Q21. rewrite ?cent_reasm in Q21.
    symex_reg HR1 (23%bv : reg) as Q23. rewrite ?cent_reasm, ?cent_bits in Q23.
    unfold LQREG. split; [lfixc_close Hfr1 HR1|].
    regs_via Hfr1; first [exact Q18 | exact Q20 | exact Q31 | exact Q30 | exact Q29 | exact Q19 | exact Q21 | exact Q23
                         | rewrite Q23; f_equal; lia
                         | match goal with |- ?G => idtac "LQREG LEFT" G end].
  Qed.

  Ltac open_lqreg HQ :=
    destruct HQ as (HF & G9 & G22 & G12 & G31 & G6 & G20 & G18 & G11 & G16 & G14 & G17 & G5 & G13 & G15 & G30 & G7 & G29 & G28 & G19 & G21 & G23); open_fixc HF;
    let XF := fresh in pose proof HF as XF; unfold LFIXc, INF_FRAME in XF; destruct XF as (P2 & P27 & P8 & _);
    pose proof G9 as P9; pose proof G22 as P22; pose proof G12 as P12.

  Lemma len_QL_hit : forall s c r R M,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    let last := lent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_lencode s) J2 in
    1 <= code_op last <= 15 - is_lenbits s -> code_bits last = is_lenbits s ->
    (forall j, 0 <= j < 2 ^ code_op last -> term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_lencode s)) ->
    code_bits last + code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LQREG s r last here J2 R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20be8) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (len_res here (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI Hbk last J2 here LK LB SUB HXT LE HM HRC HX HQ. pose proof HD as HD0. open_lfacts HD. open_lqreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval. pose proof (cent_shr8_range last) as Hc8.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_LENS _ _ TE) as (Bh & _).
    pose proof (cent_range here) as Hcent2. pose proof (cent_shr8_range here) as Hc82. pose proof (code_bits_range here) as Hcb2.
    destruct HXT as (ext' & TL' & LXT & Hext').
    arm_symexP (@nil (Z * expr)) ilLL 3%nat [true] (@nil (option expr)) llpins llvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_lencode s); cent last / 2 ^ 8; cent here; cent here / 2 ^ 8; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x20be8) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLQH" G end.
    assert (HJE : LJE2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { unfold LJE2, LK2. change (lidx2 last (ir_hold r)) with J2. change (lent2 s last (ir_hold r)) with here.
      split; [split; [lfixc_close Hfr1 HR1|]|]; regs_via Hfr1; first [ rewrite (Hfr1 (19%bv : reg) eq_refl); rewrite G18; f_equal; lia
                                                               | rewrite (Hfr1 (23%bv : reg) eq_refl); exact G23
                                                               | match goal with |- ?G => idtac "LJE2 LEFT" G end]. }
    destruct (len_T v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI0 Hbk LK LB Rbits SUB (ex_intro _ ext' (conj TL' (conj LXT Hext')))
                ltac:(change (lent2 s last (ir_hold r)) with here; rewrite wrap32_id by (clear - Bh Rt1 LB Hcb2; lia); exact LE)
                HM HRC HX HJE) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.

  Lemma len_QL_loop : forall s c r R M,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    let last := lent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_lencode s) J2 in
    1 <= code_op last <= 15 - is_lenbits s -> code_bits last = is_lenbits s ->
    (forall j, 0 <= j < 2 ^ code_op last -> term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_lencode s)) ->
    ir_bits r < code_bits last + code_bits here ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LQREG s r last here J2 R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20be8) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M
           (match (PULLBYTE ;; DECODE_k 7 (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r) with
            | ARun here2 (mkW s2 c2 r2) => len_res here2 (is_back s + code_bits last) s c (rdrop r2 (code_bits last))
            | ALeave w2 => ALeave w2
            | ARet rc w2 => ARet rc w2
            end) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI Hbk last J2 here LK LB SUB HXT GT HM HRC HX HQ. pose proof HD as HD0. open_lfacts HD. open_lqreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI. open_lx HX.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval. pose proof (cent_shr8_range last) as Hc8.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_LENS _ _ TE) as (Bh & _).
    pose proof (cent_range here) as Hcent2. pose proof (cent_shr8_range here) as Hc82. pose proof (code_bits_range here) as Hcb2.
    destruct HXT as (ext' & TL' & LXT & Hext').
    assert (SUB' : forall j, 0 <= j < 2 ^ code_op last -> term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true) by exact SUB.
    arm_symexP (@nil (Z * expr)) ilLL 3%nat [false] (@nil (option expr)) llpins llvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_lencode s); cent last / 2 ^ 8; cent here; cent here / 2 ^ 8; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x20be8) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLQLL" G end.
    assert (HJS : LJS2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { unfold LJS2, LK2.
      split; [split; [lfixc_close Hfr1 HR1|]|]; regs_via Hfr1; first [ rewrite (Hfr1 (19%bv : reg) eq_refl); rewrite G18; f_equal; lia
                                                               | clear; lia | clear - Rbits; lia
                                                               | match goal with |- ?G => idtac "LJS2 LEFT" G end]. }
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (dec_loop v s c (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)) 30 0x20bec 0x20c58
                  (LJS2 v s (ir_bits r) (ir_have r) (ir_next r) last) (LJE2 v s (ir_bits r) (ir_have r) (ir_next r) last) C ltac:(lia)
                  (fun h Hh => need2_bound LENS _ _ _ last h TL' Hh LK LB SUB')
                  CI
                  (len2_step_H v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TL' Hext' Hlofs CI LK LB LXT)
                  (len2_step_E v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TL' Hext' Hlofs CI LK LB LXT)
                  (len2_dry v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TL' Hext' Hlofs CI LK LB)
                  7%nat r R1 M HM HRC HJS RI0
                  ltac:(cbv beta; change (code_at s (is_lencode s) (lidx2 last (ir_hold r))) with here; rewrite wrap32_id by (clear - Bh Rt1 LB Hcb2; lia); exact GT)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
    destruct ((PULLBYTE ;; DECODE_k 7 (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r))
      as [here2 w1 | w1 | rc w1]; [| | destruct NL].
    - destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh2 & Hb1 & HM1 & HRC1).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
      subst here2.
      destruct (len_T v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI1 Hbk LK LB Rbits SUB (ex_intro _ ext' (conj TL' (conj LXT Hext')))
                  ltac:(exact (proj1 Hb1)) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
      apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
    - destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
      cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
      split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
      apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.

  Lemma len_Q_link : forall s c r R M b0 h0 n0 ext,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    let last := lent1 s (ir_hold r) in
    code_bits last <= ir_bits r ->
    tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true -> ext <= cext (is_lencode s) ->
    1 <= code_op last <= 15 - is_lenbits s -> code_bits last = is_lenbits s -> code_val last + 2 ^ code_op last <= ext ->
    (forall j, 0 <= j < 2 ^ code_op last ->
       is_linkop (code_op (cat (is_codes s) (is_lencode s) (code_val last + j))) = false
       /\ term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20b50) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (len_after1 s last (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 ext' Hmode HD RI Hbk last Hlb TL' Hext' LK LB LXT SUB HM HRC HX HJ. pose proof HD as HD0. open_lfacts HD.
    open_ictx C. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    assert (L : 1 <= code_op last <= 15) by (clear - LK Rt1; lia).
    destruct (op_link_tests _ L) as (_ & _ & E240 & NZ).
    assert (E240b : (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)) = true).
    { replace (code_op last =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). rewrite E240. reflexivity. }
    assert (SUB' : forall j, 0 <= j < 2 ^ code_op last -> term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true)
      by (intros j Hj; exact (proj2 (SUB j Hj))).
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    set (J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_lencode s) J2) in *.
    pose proof (SUB' _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_LENS _ _ TE) as (Bh & _).
    pose proof (code_bits_range here) as Hcb2.
    assert (HXT : exists ext0, tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext0 = true
                    /\ code_val last + 2 ^ code_op last <= ext0 /\ ext0 <= cext (is_lencode s)) by (exists ext'; split; [exact TL' | split; [exact LXT | exact Hext']]).
    destruct (len_QL_pre s c r R M b0 h0 n0 HD0 RI0 LK LB HXT ltac:(subst here J2 last; clear - Bh Rt1; lia) HM HJ) as (R1 & Hms1 & HQ).
    assert (ED2 : DECODE2 (is_lencode s) last (mkW s c r)
                  = if wrap32 (code_bits last + code_bits here) <=? ir_bits r then ARun here (mkW s c r)
                    else (PULLBYTE ;; DECODE_k 7 (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r)).
    { unfold DECODE2. rewrite DECODE_k_S. rewrite code_at_cat. reflexivity. }
    rewrite wrap32_id in ED2 by (clear - Bh Rt1 LB Hcb2; lia).
    destruct (Z.leb_spec (code_bits last + code_bits here) (ir_bits r)) as [LE2|GT2].
    - rewrite (len_after1_link s last c r here r E240b ED2).
      destruct (len_QL_hit s c r R1 M Hmode HD0 RI0 Hbk LK LB SUB' HXT LE2 HM HRC HX HQ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
    - pose proof (DECODE_k_run (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) 8 (is_lencode s) (lidx2 last)
                    (fun h => wrap32 (code_bits last + code_bits h)) 30 s c r RI0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)
                    (fun h Hh => need2_bound LENS _ _ _ last h TL' Hh LK LB SUB') Cil Cinb) as DR.
      change (DECODE_k 8 (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h))) with (DECODE2 (is_lencode s) last) in DR.
      rewrite ED2 in DR.
      destruct (len_QL_loop s c r R1 M Hmode HD0 RI0 Hbk LK LB SUB' HXT GT2 HM HRC HX HQ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      change (lent1 s (ir_hold r)) with last in HPOST.
      destruct ((PULLBYTE ;; DECODE_k 7 (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r))
        as [here2 w1 | w1 | rc w1] eqn:EN; [| | destruct DR].
      + destruct DR as (r2 & -> & _). rewrite (len_after1_link s last c r here2 r2 E240b ltac:(first [exact ED2 | rewrite ED2; exact EN])). exact HPOST.
      + rewrite (len_after1_leave2 s last c r w1 E240b ltac:(first [exact ED2 | rewrite ED2; exact EN])). exact HPOST.
  Qed.

  Lemma len_Q : forall s c r R M b0 h0 n0,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    let last := lent1 s (ir_hold r) in
    code_bits last <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20b50) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (len_after1 s last (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 Hmode HD RI Hbk last Hlb HM HRC HX HJ. pose proof HD as HD0. open_lfacts HD.
    pose proof RI as RI0. open_rinv RI.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    pose proof (tab_root_entry LENS _ _ _ (BITSv (ir_hold r) (is_lenbits s)) TL HJ1) as RE. cbv beta in RE.
    change (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r) (is_lenbits s))) with last in RE.
    destruct RE as (HB & _ & _ & CASES).
    pose proof (code_op_range last) as Hop.
    destruct CASES as [[NL TM] | (L' & BB & V & XT & SUB)].
    - apply is_linkop_false in NL.
      assert (OT : code_op last = 0 \/ 16 <= code_op last) by (clear - NL Hop; lia).
      rewrite len_after1_term.
      2:{ destruct OT as [E|GE]; [rewrite E; reflexivity|].
          replace (Z.land (code_op last) 240 =? 0) with false by (rewrite <- op_lt16_240 by exact Hop; symmetry; apply Z.ltb_ge; exact GE).
          apply Bool.andb_false_r. }
      exact (len_Q_term v C s c r R M b0 h0 n0 Hmode HD0 RI0 Hbk Hlb TM OT HM HRC HX HJ).
    - exact (len_Q_link s c r R M b0 h0 n0 extL Hmode HD0 RI0 Hbk Hlb TL HextL L' BB XT SUB HM HRC HX HJ).
  Qed.
End LenQL.
End FXG.
End InflA_Len6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Distext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.InflA_Distext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflDec6 InflA_Match2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Distext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.InflA_Distext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Dist3. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Len5. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len5.InflA_Len1. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Len5. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len5.InflA_Len2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len3 InflA_Len4 InflA_Len5. Import InflA_Len6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InffastCtx IfSpec IfSpec6 InflA_LenF.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilLA : cfg := ilSx [0x20a78] [].
Definition ilLE : cfg := ilSx [0x20b50; 0x20af4] [].

Definition le_pins : list (Z * expr) :=
  [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
   (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))].

Section LenCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Lemma len_entry : forall s c r R M,
    ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r ->   (* 1.4: three entry tests *)
    len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> LFIXc v R -> LVARS v (mkW s c r) R ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20a78) (wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 0)) s6u_rom)
      /\ LFIXc v R1 /\ LVARS v (mkW s c r) R1
      /\ getr R1 11 = zw (is_lenbits s) /\ getr R1 13 = zw (cv_S v + 7160) /\ getr R1 12 = zw 31.
  Proof.
    intros s c r R M Hslow HD RI HM HF HV. open_lfacts HD.
    open_ictx C. open_lmem HM. open_fixc HF. open_vars HV. open_rinv RI. open_frame Mfr.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (is6_lenbits _ _ _ _ Msc) as C120.
    destruct (Z_lt_le_dec (ir_have r) 6) as [H6|H6].
    - arm_symexP (@nil (Z * expr)) ilLA 8%nat [true] [RVal (EVar 45%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] le_pins
        [(45%nat, 16)] v r [is_lenbits s] NoVals F0
        (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTLA1" G end.
      exists R1. split; [by_run Hms1|].
      symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (12%bv : reg) as Q12.
      split; [lfixc_close Hfr1 HR1|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1|].
      split; [exact Q11 | split; [exact Q13 | exact Q12]].
    - destruct (Z_lt_le_dec (ir_left r) 258) as [Hleft|Hleft].
      + arm_symexP (@nil (Z * expr)) ilLA 11%nat [false; true] [RVal (EVar 39%nat); RVal (EVar 45%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] le_pins
          [(45%nat, 16)] v r [is_lenbits s] NoVals F0
          (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTLA2" G end.
        exists R1. split; [by_run Hms1|].
        symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (12%bv : reg) as Q12.
        split; [lfixc_close Hfr1 HR1|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1|].
        split; [exact Q11 | split; [exact Q13 | exact Q12]].
      + (* 1.4: the third test, li a1,7; bltu a1,s3: bits >= 8 goes to the slow path too *)
        assert (Hbits : 8 <= ir_bits r) by (clear - Hslow H6 Hleft; lia).
        arm_symexP (@nil (Z * expr)) ilLA 13%nat [false; false; true] [RVal (EVar 39%nat); RVal (EVar 45%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] le_pins
          [(45%nat, 16)] v r [is_lenbits s] NoVals F0
          (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTLA3" G end.
        exists R1. split; [by_run Hms1|].
        symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (12%bv : reg) as Q12.
        split; [lfixc_close Hfr1 HR1|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1|].
        split; [exact Q11 | split; [exact Q13 | exact Q12]].
  Qed.

  Ltac le_side Rhold64 Rt1 Rt2 TAB HJ1 HA0 HA1 Hext LE GT :=
    rewrite ?idx0_probe by (first [exact Rhold64 | clear - Rt1; lia]);
    rewrite ?cent_reasm, ?cent_bits;
    repeat match goal with |- context [?x mod 2 ^ 64] =>
      lazymatch x with context [BITSv _ _] => rewrite (Z.mod_small x (2 ^ 64)) by (generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia) end end;
    first [ lazymatch goal with |- context [if _ <? _ then 1 else 0] => generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; ub_ptr_side end
          | lazymatch goal with |- exists _, _ => idtac end
          | generalize HJ1; clear - HA0 HA1 Rt2 Hext; intro; lia
          | clear - LE; lia
          | clear - GT; lia
          | idtac ].

  Lemma len_core : forall s c r R M,
    ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r ->
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIXc v R -> LVARS v (mkW s c r) R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_LEN ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hslow Hmode HD RI HM HRC HX HF HV.
    destruct (len_entry s c r R M Hslow HD RI HM HF HV) as (R0 & Hms0 & HF0 & HV0 & E11 & E13 & E12).
    clear HF HV. open_lfacts HD.
    open_ictx C. open_retc HRC. open_lx HX. open_fixc HF0. open_vars HV0. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    pose proof E11 as P11. pose proof E13 as P13. pose proof E12 as P12.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hh31 : 0 <= ir_have r < 2 ^ 31) by (clear - Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    set (s1 := iset_back s 0) in *.
    set (last := lent1 s1 (ir_hold r)).
    pose proof (tab_root_entry LENS _ _ _ (BITSv (ir_hold r) (is_lenbits s)) TL HJ1) as (HB & _). change (cat _ _ _) with last in HB.
    pose proof (code_bits_range last) as Hcb. pose proof (code_val_range last) as Hval. pose proof (clo_range last) as Hclo.
    pose proof (cent_range last) as Hcent. pose proof (cent_shr8_range last) as Hc8.
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
    assert (HX1 : LX v (mkW s1 c r)) by (apply (LX_step0 v s c r s1 c r HX NH NB); subst s1; try reflexivity; [exact Xlive | exact Xret | exact Xmsg | bk_side]).
    pose proof (ctab6_cells v s1 c r M1 (is_lencode s) C HM1 Hlofs) as TAB1.
    open_lmem HM1. unfold mapped in *.
    assert (C104 : cell s6u_segs M1 (cv_S v + 120) 8 (ctab6 v (is_lencode s))) by (exact (is6_lencode _ _ _ _ Msc)).
    assert (MF1 : MFRAME v (ir_put r) (ir_put r) M M1).
    { subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
    assert (SB1 : same_blocks s s1) by (subst s1; split; [reflexivity | split; reflexivity]).
    destruct (Z.leb_spec (code_bits last) (ir_bits r)) as [LE|GT].
    -
      arm_symexP (@nil (Z * expr)) ilLE 34%nat [false; false; false; true] [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat)]
        (le_pins ++ [(11, EVar 45%nat); (13, EAdd (EVar 33%nat) (ELit 7160)); (12, ELit 31)])
        [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 65536); (48%nat, 65536)] v r
        [is_lenbits s; ctab6 v (is_lencode s); code_val last; clo last] NoVals F0
        (mkst R0 (Z_to_bv 64 0x20a78) M1 s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: rewrite ?idx0_probe by (first [exact Rhold64 | clear - Rt1; lia]); rewrite ?cent_reasm, ?cent_bits.
      all: try (subst last s1; unfold lent1; cbn [is_codes is_lencode is_lenbits iset_back]; tab_read2 TAB1 (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 HextL; lia).
      all: le_side Rhold64 Rt1 Rt2 TAB1 HJ1 HA0 HA1 HextL LE GT.
      all: match goal with |- ?G => idtac "LEFTLE1" G end.
      assert (HJE : LJE v s1 (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (29%bv : reg) as Q29. rewrite mask_reg in Q29 by (clear - Rt1; lia).
        symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (30%bv : reg) as Q30.
        symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (5%bv : reg) as Q5.
        symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (11%bv : reg) as Q11.
        symex_reg HR1 (20%bv : reg) as Q19. rewrite ?cent_reasm in Q19.
        symex_reg HR1 (28%bv : reg) as Q28. rewrite ?cent_reasm in Q28.
        symex_reg HR1 (7%bv : reg) as Q7. rewrite ?cent_reasm, ?cent_bits in Q7.
        unfold LJE, LK1. split; [split; [lfixc_close Hfr1 HR1|]|]; subst last s1; unfold lent1; cbn [is_codes is_lencode is_lenbits iset_back];
          regs_via Hfr1; first [exact Q13 | exact Q29 | exact Q30 | exact Q12 | exact Q17 | exact Q5 | exact Q14 | exact Q6 | exact Q16 | exact Q11 | exact Q19 | exact Q28 | exact Q7
                               | rewrite Q15; destruct (Z.ltb_spec 0 (ctab6 v (is_lencode s))); [reflexivity | exfalso; clear - HA0 H; lia]
                               | rewrite Q30; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q17; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q5; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q16; rewrite ?Z.mod_small by (clear - Rbits; lia); f_equal; lia
                               | match goal with |- ?G => idtac "LJE LEFT" G end]. }
      destruct (len_Q v C s1 c r R1 M1 (ir_bits r) (ir_have r) (ir_next r) ltac:(exact Hmode) HD1 RI0 ltac:(reflexivity) LE
                  ltac:(constructor; assumption) HRC1 HX1 HJE) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms0 | eapply msteps_trans; [| exact Hms2]; by_run Hms1]|].
      exact (arm_post_chain v (mkW s c r) (mkW s1 c r) M M1 _ _ _ _ SB1 MF1 HPOST).
    -
      arm_symexP (@nil (Z * expr)) ilLE 34%nat [false; false; false; false] [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat)]
        (le_pins ++ [(11, EVar 45%nat); (13, EAdd (EVar 33%nat) (ELit 7160)); (12, ELit 31)])
        [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 65536); (48%nat, 65536)] v r
        [is_lenbits s; ctab6 v (is_lencode s); code_val last; clo last] NoVals F0
        (mkst R0 (Z_to_bv 64 0x20a78) M1 s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: rewrite ?idx0_probe by (first [exact Rhold64 | clear - Rt1; lia]); rewrite ?cent_reasm, ?cent_bits.
      all: try (subst last s1; unfold lent1; cbn [is_codes is_lencode is_lenbits iset_back]; tab_read2 TAB1 (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 HextL; lia).
      all: le_side Rhold64 Rt1 Rt2 TAB1 HJ1 HA0 HA1 HextL LE GT.
      all: match goal with |- ?G => idtac "LEFTLE2" G end.
      assert (HJS : LJS v s1 (ir_bits r) (ir_have r) (ir_next r) r R1).
      { symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (29%bv : reg) as Q29. rewrite mask_reg in Q29 by (clear - Rt1; lia).
        symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (30%bv : reg) as Q30.
        symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (5%bv : reg) as Q5.
        symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (11%bv : reg) as Q11.
        unfold LJS, LK1. split; [split; [lfixc_close Hfr1 HR1|]|]; subst s1; cbn [is_lencode is_lenbits iset_back];
          regs_via Hfr1; first [exact Q13 | exact Q29 | exact Q30 | exact Q12 | exact Q17 | exact Q5 | exact Q14 | exact Q6 | exact Q16 | exact Q11
                               | rewrite Q15; destruct (Z.ltb_spec 0 (ctab6 v (is_lencode s))); [reflexivity | exfalso; clear - HA0 H; lia]
                               | rewrite Q30; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q17; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q5; rewrite ?Z.mod_small by (clear - Hh31; lia); f_equal; lia
                               | rewrite Q16; rewrite ?Z.mod_small by (clear - Rbits; lia); f_equal; lia
                               | clear; lia | clear - Rbits; lia
                               | match goal with |- ?G => idtac "LJS LEFT" G end]. }
      pose proof (dec_loop v s1 c (is_lencode s1) (fun h => BITSv h (is_lenbits s1)) code_bits 15 0x20af4 0x20b50
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
        assert (HX1' : LX v (mkW s1 c r1)) by (apply (LX_step0 v s c r s1 c r1 HX NH NB); subst s1; try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
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
        apply (LX_step0 v s c r s1 c r1 HX NH NB); subst s1; try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.
End LenCore.

Theorem arm_LEN_sim : inflate_fast_spec6 -> ffok_stmt -> fastok_stmt -> gfast_ob_stmt -> fframe_stmt -> arm_stmt LEN.
Proof.
  intros IFAST FFOK FASTOK GFOB FFRAME v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LEN) with (arm_LEN ivar_ref).
  pose proof (len_facts_of_pinv v s c r Hmode HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  pose proof HP as HP'. open_pinv HP'.
  change (arm6_pc LEN) with 0x209d4.
  destruct (Z_lt_le_dec (ir_have r) 6) as [Hh|Hh]; [exact (len_core v C s c r R M (or_introl Hh) Hmode HD RI HM HRC HX (LFIX_LFIXc v R HF) HV)|].
  destruct (Z_lt_le_dec (ir_left r) 258) as [Hl|Hl]; [exact (len_core v C s c r R M (or_intror (or_introl Hl)) Hmode HD RI HM HRC HX (LFIX_LFIXc v R HF) HV)|].
  (* 1.4: bits >= 8 also takes the slow path *)
  destruct (Z_lt_le_dec (ir_bits r) 8) as [Hb|Hb]; [| exact (len_core v C s c r R M (or_intror (or_intror Hb)) Hmode HD RI HM HRC HX (LFIX_LFIXc v R HF) HV)].
  pose proof HF as HF0. unfold LFIX in HF0. destruct HF0 as (_ & _ & G13 & _).
  exact (lenF_core v C IFAST FFOK FASTOK GFOB FFRAME s c r R M HP Hmode HD HM HRC HX (LFIX_LFIXc v R HF) G13 HV Hh Hl Hb).
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
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIXc v R -> getr R 13 = zw (cv_ZP v) -> LVARS v (mkW s c r) R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x209cc) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_LEN_ ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M HP Hmode HD RI HM HRC HX HF G13 HV.
    unfold arm_LEN_. mstep1 set_mode_eq.
    pose proof HF as HF0. pose proof HV as HV0.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fixc HF. open_vars HV. pose proof RI as RI0. open_rinv RI.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    arm_symexP (@nil (Z * expr)) ilS 4%nat (@nil bool) (@nil (option expr)) le_pins (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x209cc) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16200)) in *.
    set (s1 := iset_mode s LEN).
    assert (HM1 : LMEM v (mkW s1 c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s LEN Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC1 : RETC v (mkW s1 c r) M1) by (subst M1; retc_tower C HRC).
    assert (HX1 : LX v (mkW s1 c r)) by (apply (LX_step0 v s c r s1 c r HX NH NB); subst s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side]).
    assert (K : exists R' M' pc', msteps s6u_segs (mkst R1 (Z_to_bv 64 0x209d4) M1 s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
                                 /\ arm_post v (mkW s1 c r) M1 (arm_LEN ivar_ref (mkW s1 c r)) R' M' pc').
    { destruct (Z_lt_le_dec (ir_have r) 6) as [Hh|Hh]; [| destruct (Z_lt_le_dec (ir_left r) 258) as [Hl|Hl];
                                                         [| destruct (Z_lt_le_dec (ir_bits r) 8) as [Hb|Hb]]].
      - exact (len_core v C s1 c r R1 M1 (or_introl Hh) ltac:(reflexivity) (len_facts_mode v s c LEN HD) RI0 HM1 HRC1 HX1
                 ltac:(lfixc_close Hfr1 HR1) ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1)).
      - exact (len_core v C s1 c r R1 M1 (or_intror (or_introl Hl)) ltac:(reflexivity) (len_facts_mode v s c LEN HD) RI0 HM1 HRC1 HX1
                 ltac:(lfixc_close Hfr1 HR1) ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1)).
      -
        exact (lenF_core v C IFAST FFOK FASTOK GFOB FFRAME s1 c r R1 M1 (pinv_LEN__LEN _ _ _ _ s c r HP Hmode) ltac:(reflexivity)
                 (len_facts_mode v s c LEN HD) HM1 HRC1 HX1 ltac:(lfixc_close Hfr1 HR1) ltac:(rewrite (Hfr1 (13%bv : reg) eq_refl); exact G13)
                 ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1) Hh Hl Hb).
      - (* 1.4: bits >= 8 takes the slow path *)
        exact (len_core v C s1 c r R1 M1 (or_intror (or_intror Hb)) ltac:(reflexivity) (len_facts_mode v s c LEN HD) RI0 HM1 HRC1 HX1
                 ltac:(lfixc_close Hfr1 HR1) ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1)). }
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
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  pose proof HP as HP'. open_pinv HP'.
  change (arm6_pc LEN_) with 0x209cc.
  pose proof HF as HF0. unfold LFIX in HF0. destruct HF0 as (_ & _ & G13 & _).
  exact (len__core v C IFAST FFOK FASTOK GFOB FFRAME s c r R M HP Hmode HD RI HM HRC HX (LFIX_LFIXc v R HF) G13 HV).
Qed.
End FXG.

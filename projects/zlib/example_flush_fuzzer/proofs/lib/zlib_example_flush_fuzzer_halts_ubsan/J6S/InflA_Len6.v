(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Distext1 InflA_Distext2 InflDec6 InflA_Dist3 InflA_Dist7 InflA_Lenext2 InflA_Lenext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflA_Len1 InflA_Len2 InflA_Len3 InflA_Len4 InflA_Len5.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilLL : cfg := ilSx [0x1e4f0; 0x1e56c; 0x1e504] [].

Section LenQL.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Definition LQREG (s : inflate_state) (r : iregs) (last here J2 : Z) (R : bvmap 5 word) : Prop :=
    (getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 10 = zw (cv_ZP v) /\ getr R 11 = zw (cv_flush v)
     /\ getr R 22 = zw (cv_S v + 168) /\ getr R 31 = zw (-16180) /\ getr R 29 = zw 30 /\ getr R 20 = zw 16209 /\ getr R 25 = zw A6_JTAB
     /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4)
    /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 23 = zw (ir_hold r) /\ getr R 13 = zw (ir_bits r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 27 = zw (cv_S v + 7160)
    /\ getr R 7 = zw (Z.ones (code_bits last + code_op last)) /\ getr R 16 = zw (code_bits last) /\ getr R 14 = zw (code_bits last)
    /\ getr R 17 = zw (code_val last) /\ getr R 15 = zw (ctab6 v (is_lencode s))
    /\ getr R 30 = zw (ctab6 v (is_lencode s) + 4 * J2) /\ getr R 28 = zw (code_bits here) /\ getr R 5 = zw (code_bits last + code_bits here).

  Definition llpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (20, ELit 16209); (25, ELit 0x12510);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (13, EVar 41%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (27, EAdd (EVar 33%nat) (ELit 7160));
     (7, EVar 45%nat); (16, EVar 46%nat); (14, EVar 46%nat); (17, EVar 47%nat); (15, EVar 48%nat); (30, EVar 49%nat); (28, EVar 50%nat);
     (5, EAdd (EVar 46%nat) (EVar 50%nat))].
  Definition llvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 63); (50%nat, 16)].

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
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e4a4) M s6_rom) (mkst R1 (Z_to_bv 64 0x1e4f0) M s6_rom)
      /\ LQREG s r last here J2 R1.
  Proof.
    intros s c r R M b0 h0 n0 HD RI last J2 here LK LB (ext' & TL' & LXT & Hext') Bh HM HJ. open_lfacts HD.
    pose proof HJ as X. unfold LJE, LK1 in X.
    destruct X as ((HF & G18 & G1 & G23 & G9 & G26 & G16 & G15) & G22 & G12 & G27 & G13 & G17 & G14). open_fix HF.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hlofs) as TAB.
    pose proof (ones_range15 (is_lenbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_lenbits s) ltac:(lia)) as HJ1.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    pose proof (code_bits_range here) as Hcb2.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    arm_symexP (@nil (Z * expr)) ilLL 24%nat [false]
      [RVal (EVar 49%nat); RVal (EVar 50%nat); RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 51%nat)] lqpins
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 16); (49%nat, 256); (50%nat, 65536); (51%nat, 16)] v r
      [Z.ones (is_lenbits s); ctab6 v (is_lencode s); ctab6 v (is_lencode s) + 4 * BITSv (ir_hold r) (is_lenbits s); code_bits last;
       code_op last; code_val last; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e4a4) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: rewrite ?idx2_probe by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    all: try (subst last; unfold lent1; tab_read TAB (BITSv (ir_hold r) (is_lenbits s)); clear - HJ1 Rt2 HextL; lia).
    all: try (subst here J2; tab_read TAB (code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)); clear - HJ2 LXT Hext' Hval; lia).
    all: try (generalize HJ2; clear - HA0 HA1 LXT Hext' Hval; intro; lia).
    all: try (apply opm1_link; clear - LK Rt1; lia).
    all: match goal with |- ?G => idtac "LEFTLQL" G end.
    exists R1. split; [by_run Hms1|].
    symex_reg HR1 (27%bv : reg) as Q24. symex_reg HR1 (7%bv : reg) as Q7. rewrite mask_reg in Q7 by (clear - Rt1 LK LB; lia).
    symex_reg HR1 (16%bv : reg) as Q16'. symex_reg HR1 (17%bv : reg) as Q17'. symex_reg HR1 (30%bv : reg) as Q30.
    rewrite idx2_probe in Q30 by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    symex_reg HR1 (28%bv : reg) as Q28. symex_reg HR1 (5%bv : reg) as Q5.
    unfold LQREG, INF_FRAME.
    regs_via Hfr1; first [exact Q24 | exact Q7 | exact Q16' | exact Q17' | rewrite Q30; subst J2; f_equal; lia | exact Q28 | exact Q5
                         | match goal with |- ?G => idtac "LQREG LEFT" G end].
  Qed.

  Ltac open_qreg HQ :=
    destruct HQ as ((G2 & G25 & G10 & G11 & G21 & G31 & G29 & G19 & G24 & G3 & G4) & G18 & G1 & G22 & G13 & G12 & G27 & G9 & G7 & G16 & G14 & G17 & G15 & G30 & G28 & G5); unfold INF_FRAME in G2.

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
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e4f0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (len_res here (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI Hbk last J2 here LK LB SUB HXT LE HM HRC HX HQ. pose proof HD as HD0. open_lfacts HD. open_qreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_LENS _ _ TE) as (Bh & _).
    destruct HXT as (ext' & TL' & LXT & Hext').
    arm_symexP (@nil (Z * expr)) ilLL 8%nat [true] (@nil (option expr)) llpins llvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_lencode s); ctab6 v (is_lencode s) + 4 * J2; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e4f0) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLQH" G end.
    assert (HJE : LJE2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (31%bv : reg) as Q31. symex_reg HR1 (6%bv : reg) as Q6.
      unfold LJE2, LK2, INF_FRAME. change (lidx2 last (ir_hold r)) with J2. change (lent2 s last (ir_hold r)) with here.
      regs_via Hfr1; first [exact Q5 | exact Q31 | exact Q6 | match goal with |- ?G => idtac "LJE2 LEFT" G end]. }
    destruct (len_T v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI0 Hbk LK LB SUB (ex_intro _ ext' (conj TL' (conj LXT Hext')))
                ltac:(change (lent2 s last (ir_hold r)) with here; rewrite wrap32_id by (clear - Bh Rt1 LB; pose proof (code_bits_range here); lia); exact LE)
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
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e4f0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M
           (match (PULLBYTE ;; DECODE_k 7 (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r) with
            | ARun here2 (mkW s2 c2 r2) => len_res here2 (is_back s + code_bits last) s c (rdrop r2 (code_bits last))
            | ALeave w2 => ALeave w2
            | ARet rc w2 => ARet rc w2
            end) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI Hbk last J2 here LK LB SUB HXT GT HM HRC HX HQ. pose proof HD as HD0. open_lfacts HD. open_qreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI. open_lx HX.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_LENS _ _ TE) as (Bh & _).
    destruct HXT as (ext' & TL' & LXT & Hext').
    assert (SUB' : forall j, 0 <= j < 2 ^ code_op last -> term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true) by exact SUB.
    arm_symexP (@nil (Z * expr)) ilLL 8%nat [false] (@nil (option expr)) llpins llvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_lencode s); ctab6 v (is_lencode s) + 4 * J2; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e4f0) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLQLL" G end.
    assert (HJS : LJS2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (9%bv : reg) as Q8. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (29%bv : reg) as Q29.
      unfold LJS2, LK2, INF_FRAME.
      regs_via Hfr1; first [exact Q5 | exact Q8 | exact Q6 | exact Q29 | clear; lia | clear - Rbits; lia | match goal with |- ?G => idtac "LJS2 LEFT" G end]. }
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (dec_loop v s c (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)) 30 0x1e504 0x1e56c
                  (LJS2 v s (ir_bits r) (ir_have r) (ir_next r) last) (LJE2 v s (ir_bits r) (ir_have r) (ir_next r) last) C ltac:(lia)
                  (fun h Hh => need2_bound LENS _ _ _ last h TL' Hh LK LB SUB')
                  CI
                  (len2_step_H v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TL' Hext' Hlofs CI LK LB LXT)
                  (len2_step_E v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TL' Hext' Hlofs CI LK LB LXT)
                  (len2_dry v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TL' Hext' Hlofs CI LK LB)
                  7%nat r R1 M HM HRC HJS RI0
                  ltac:(cbv beta; change (code_at s (is_lencode s) (lidx2 last (ir_hold r))) with here; rewrite wrap32_id by (clear - Bh Rt1 LB; pose proof (code_bits_range here); lia); exact GT)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
    destruct ((PULLBYTE ;; DECODE_k 7 (is_lencode s) (lidx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r))
      as [here2 w1 | w1 | rc w1]; [| | destruct NL].
    - destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh2 & Hb1 & HM1 & HRC1).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]).
      subst here2.
      destruct (len_T v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI1 Hbk LK LB SUB (ex_intro _ ext' (conj TL' (conj LXT Hext')))
                  ltac:(exact (proj1 Hb1)) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
      apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
    - destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
      cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
      split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
      apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
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
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e4a4) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
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
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e4a4) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
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

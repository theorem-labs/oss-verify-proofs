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
     InflA_Match2 InflA_Distext2 InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflDec6 InflA_Dist1 InflA_Dist2 InflA_Dist3 InflA_Dist4 InflA_Dist5.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilDL : cfg := ilSx [0x1e6b0; 0x1e724; 0x1e6c4] [].

Section DistQL.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition QREG (s : inflate_state) (r : iregs) (last here J2 : Z) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 23 = zw (ir_hold r) /\ getr R 13 = zw (ir_bits r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 18 = zw (cv_S v + 7160)
    /\ getr R 6 = zw (Z.ones (code_bits last + code_op last)) /\ getr R 14 = zw (code_bits last) /\ getr R 16 = zw (code_val last)
    /\ getr R 15 = zw (ctab6 v (is_distcode s))
    /\ getr R 28 = zw (ctab6 v (is_distcode s) + 4 * J2) /\ getr R 7 = zw (code_bits here) /\ getr R 17 = zw (code_bits last + code_bits here).

  Definition lpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (13, EVar 41%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (18, EAdd (EVar 33%nat) (ELit 7160));
     (6, EVar 45%nat); (14, EVar 46%nat); (16, EVar 47%nat); (15, EVar 48%nat); (28, EVar 49%nat); (7, EVar 50%nat);
     (17, EAdd (EVar 46%nat) (EVar 50%nat))].
  Definition lvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 63); (50%nat, 16)].

  Lemma dist_QL_pre : forall s c r R M b0 h0 n0,
    dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_distcode s) J2 in
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    code_bits here <= 15 ->
    LMEM v (mkW s c r) M -> DJE v s b0 h0 n0 r R ->
    exists R1,
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e66c) M s6_rom) (mkst R1 (Z_to_bv 64 0x1e6b0) M s6_rom)
      /\ QREG s r last here J2 R1.
  Proof.
    intros s c r R M b0 h0 n0 HD RI last J2 here LK LB (ext' & TD' & LXT & Hext') Bh HM HJ. open_dfacts HD.
    pose proof HJ as X. unfold DJE, DK in X.
    destruct X as ((HF & G18 & G1 & G23 & G9 & G26 & G17 & G15) & G22 & G12 & G27 & G13 & G16 & G14). open_fix HF.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_distcode s) C HM Hofs) as TAB.
    pose proof (ones_range15 (is_distbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_distbits s) ltac:(lia)) as HJ1.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    pose proof (code_bits_range here) as Hcb2.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    arm_symexP (@nil (Z * expr)) ilDL 20%nat [false]
      [RVal (EVar 49%nat); RVal (EVar 50%nat); RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 51%nat)] qpins
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 16); (49%nat, 256); (50%nat, 65536); (51%nat, 16)] v r
      [Z.ones (is_distbits s); ctab6 v (is_distcode s); ctab6 v (is_distcode s) + 4 * BITSv (ir_hold r) (is_distbits s); code_bits last;
       code_op last; code_val last; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e66c) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: rewrite ?idx2_probe by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    1-2: subst last; unfold dent1; tab_read TAB (BITSv (ir_hold r) (is_distbits s)); clear - HJ1 Rt2 Hext; lia.
    1: subst here J2; tab_read TAB (code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)); clear - HJ2 LXT Hext' Hval; lia.
    1: generalize HJ2; clear - HA0 HA1 LXT Hext' Hval; intro; lia.
    all: match goal with |- ?G => idtac "LEFTQL" G end.
    exists R1. split; [by_run Hms1|].
    symex_reg HR1 (18%bv : reg) as Q9. symex_reg HR1 (6%bv : reg) as Q6. rewrite mask_reg in Q6 by (clear - Rt1 LK LB; lia).
    symex_reg HR1 (16%bv : reg) as Q16'. symex_reg HR1 (28%bv : reg) as Q28.
    rewrite idx2_probe in Q28 by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    symex_reg HR1 (7%bv : reg) as Q7. symex_reg HR1 (17%bv : reg) as Q17'.
    unfold QREG. split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|].
    regs_via Hfr1; first [exact Q9 | exact Q6 | exact Q16' | rewrite Q28; subst J2; f_equal; lia | exact Q7 | exact Q17'
                         | match goal with |- ?G => idtac "QREG LEFT" G end].
  Qed.

  Ltac open_qreg HQ :=
    destruct HQ as (HF & G18 & G1 & G22 & G13 & G12 & G27 & G8 & G6 & G14 & G16 & G15 & G28 & G7 & G17); open_fix HF.

  Lemma dist_QL_hit : forall s c r R M,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_distcode s) J2 in
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s ->
    (forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    code_bits last + code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> QREG s r last here J2 R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e6b0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (dist_res here (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI last J2 here LK LB SUB HXT LE HM HRC HX HQ. pose proof HD as HD0. open_dfacts HD. open_qreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    destruct HXT as (ext' & TD' & LXT & Hext').
    arm_symexP (@nil (Z * expr)) ilDL 8%nat [true] (@nil (option expr)) lpins lvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_distcode s); ctab6 v (is_distcode s) + 4 * J2; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e6b0) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTQH" G end.
    assert (HJE : DJE2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (30%bv : reg) as Q30. symex_reg HR1 (5%bv : reg) as Q5.
      unfold DJE2, DK2, INF_FRAME. change (didx2 last (ir_hold r)) with J2. change (dent2 s last (ir_hold r)) with here.
      regs_via Hfr1; first [exact Q17 | exact Q30 | exact Q5 | match goal with |- ?G => idtac "DJE2 LEFT" G end]. }
    destruct (dist_T v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI0 LK LB SUB (ex_intro _ ext' (conj TD' (conj LXT Hext')))
                ltac:(change (dent2 s last (ir_hold r)) with here; rewrite wrap32_id by (clear - Bh Rt1 LB; pose proof (code_bits_range here); lia); exact LE)
                HM HRC HX HJE) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.

  Lemma dist_QL_loop : forall s c r R M,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_distcode s) J2 in
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s ->
    (forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    ir_bits r < code_bits last + code_bits here ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> QREG s r last here J2 R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e6b0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M
           (match (PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r) with
            | ARun here2 (mkW s2 c2 r2) => dist_res here2 (is_back s + code_bits last) s c (rdrop r2 (code_bits last))
            | ALeave w2 => ALeave w2
            | ARet rc w2 => ARet rc w2
            end) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI last J2 here LK LB SUB HXT GT HM HRC HX HQ. pose proof HD as HD0. open_dfacts HD. open_qreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI. open_lx HX.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    destruct HXT as (ext' & TD' & LXT & Hext').
    assert (SUB' : forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) by exact SUB.
    arm_symexP (@nil (Z * expr)) ilDL 8%nat [false] (@nil (option expr)) lpins lvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_distcode s); ctab6 v (is_distcode s) + 4 * J2; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e6b0) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTQLL" G end.
    assert (HJS : DJS2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (31%bv : reg) as Q31. symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (29%bv : reg) as Q29.
      unfold DJS2, DK2, INF_FRAME.
      regs_via Hfr1; first [exact Q17 | exact Q31 | exact Q5 | exact Q29 | clear; lia | clear - Rbits; lia | match goal with |- ?G => idtac "DJS2 LEFT" G end]. }
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (dec_loop v s c (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)) 30 0x1e6c4 0x1e724
                  (DJS2 v s (ir_bits r) (ir_have r) (ir_next r) last) (DJE2 v s (ir_bits r) (ir_have r) (ir_next r) last) C ltac:(lia)
                  (fun h Hh => need2_bound DISTS _ _ _ last h TD' Hh LK LB SUB')
                  CI
                  (dist2_step_H v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TD' Hext' Hofs CI LK LB LXT)
                  (dist2_step_E v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TD' Hext' Hofs CI LK LB LXT)
                  (dist2_dry v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TD' Hext' Hofs CI LK LB)
                  7%nat r R1 M HM HRC HJS RI0
                  ltac:(cbv beta; change (code_at s (is_distcode s) (didx2 last (ir_hold r))) with here; rewrite wrap32_id by (clear - Bh Rt1 LB; pose proof (code_bits_range here); lia); exact GT)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
    destruct ((PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r))
      as [here2 w1 | w1 | rc w1]; [| | destruct NL].
    - destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh2 & Hb1 & HM1 & HRC1).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]).
      subst here2.
      destruct (dist_T v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI1 LK LB SUB (ex_intro _ ext' (conj TD' (conj LXT Hext')))
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

  Lemma dist_Q_link : forall s c r R M b0 h0 n0 ext,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    code_bits last <= ir_bits r ->
    tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true -> ext <= cext (is_distcode s) ->
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s -> code_val last + 2 ^ code_op last <= ext ->
    (forall j, 0 <= j < 2 ^ code_op last ->
       is_linkop (code_op (cat (is_codes s) (is_distcode s) (code_val last + j))) = false
       /\ term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e66c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (dist_after1 s last (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 ext' Hmode HD RI last Hlb TD' Hext' LK LB LXT SUB HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    open_ictx C. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    assert (L : 1 <= code_op last <= 15) by (clear - LK Rt1; lia).
    destruct (op_link_tests _ L) as (_ & _ & E240 & _).
    assert (E240b : (Z.land (code_op last) 240 =? 0) = true) by (apply Z.eqb_eq; exact E240).
    assert (SUB' : forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true)
      by (intros j Hj; exact (proj2 (SUB j Hj))).
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    set (J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_distcode s) J2) in *.
    pose proof (SUB' _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    pose proof (code_bits_range here) as Hcb2.
    assert (HXT : exists ext0, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext0 = true
                    /\ code_val last + 2 ^ code_op last <= ext0 /\ ext0 <= cext (is_distcode s)) by (exists ext'; split; [exact TD' | split; [exact LXT | exact Hext']]).
    destruct (dist_QL_pre s c r R M b0 h0 n0 HD0 RI0 LK LB HXT ltac:(subst here J2 last; clear - Bh Rt1; lia) HM HJ) as (R1 & Hms1 & HQ).
    assert (ED2 : DECODE2 (is_distcode s) last (mkW s c r)
                  = if wrap32 (code_bits last + code_bits here) <=? ir_bits r then ARun here (mkW s c r)
                    else (PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r)).
    { unfold DECODE2. rewrite DECODE_k_S. rewrite code_at_cat. reflexivity. }
    rewrite wrap32_id in ED2 by (clear - Bh Rt1 LB Hcb2; lia).
    destruct (Z.leb_spec (code_bits last + code_bits here) (ir_bits r)) as [LE2|GT2].
    - rewrite (dist_after1_link s last c r here r E240b ED2).
      destruct (dist_QL_hit s c r R1 M Hmode HD0 RI0 LK LB SUB' HXT LE2 HM HRC HX HQ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
    - pose proof (DECODE_k_run (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) 8 (is_distcode s) (didx2 last)
                    (fun h => wrap32 (code_bits last + code_bits h)) 30 s c r RI0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)
                    (fun h Hh => need2_bound DISTS _ _ _ last h TD' Hh LK LB SUB') Cil Cinb) as DR.
      change (DECODE_k 8 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h))) with (DECODE2 (is_distcode s) last) in DR.
      rewrite ED2 in DR.
      destruct (dist_QL_loop s c r R1 M Hmode HD0 RI0 LK LB SUB' HXT GT2 HM HRC HX HQ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      change (dent1 s (ir_hold r)) with last in HPOST.
      destruct ((PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r))
        as [here2 w1 | w1 | rc w1] eqn:EN; [| | destruct DR].
      + destruct DR as (r2 & -> & _). rewrite (dist_after1_link s last c r here2 r2 E240b ltac:(first [exact ED2 | rewrite ED2; exact EN])). exact HPOST.
      + rewrite (dist_after1_leave2 s last c r w1 E240b ltac:(first [exact ED2 | rewrite ED2; exact EN])). exact HPOST.
  Qed.

  Lemma dist_Q : forall s c r R M b0 h0 n0,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    code_bits last <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e66c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (dist_after1 s last (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 Hmode HD RI last Hlb HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    pose proof RI as RI0. open_rinv RI.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (BITSv_bound (ir_hold r) (is_distbits s) ltac:(lia)) as HJ1.
    pose proof (tab_root_entry DISTS _ _ _ (BITSv (ir_hold r) (is_distbits s)) TD HJ1) as RE. cbv beta in RE.
    change (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r) (is_distbits s))) with last in RE.
    destruct RE as (HB & _ & _ & CASES).
    pose proof (code_op_range last) as Hop.
    destruct CASES as [[NL TM] | (L' & BB & V & XT & SUB)].
    - destruct (term_ok_DISTS _ _ TM) as (_ & CL).
      assert (O16 : 16 <= code_op last).
      { destruct CL as [(Oe & _) | (Ie & _)]; [exact (proj1 Oe)|].
        destruct (Z_lt_le_dec (code_op last) 16) as [LT|GE]; [| exact GE]. exfalso. apply Ie.
        assert (E : code_op last = 0 \/ 1 <= code_op last <= 15) by lia. destruct E as [E|E]; [rewrite E; reflexivity|].
        exact (proj1 (proj2 (op_link_tests _ E))). }
      rewrite dist_after1_term by (rewrite <- op_lt16_240 by exact Hop; apply Z.ltb_ge; exact O16).
      exact (dist_Q_term v C s c r R M b0 h0 n0 Hmode HD0 RI0 Hlb TM O16 HM HRC HX HJ).
    - exact (dist_Q_link s c r R M b0 h0 n0 ext Hmode HD0 RI0 Hlb TD Hext L' BB XT SUB HM HRC HX HJ).
  Qed.
End DistQL.
End FXG.

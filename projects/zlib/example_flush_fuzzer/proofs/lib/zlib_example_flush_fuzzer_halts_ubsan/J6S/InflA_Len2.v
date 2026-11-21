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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflNeed6 InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilL2 : cfg := ilSx [0x1e504; 0x1e56c] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section LenL2.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Hypothesis C : ictx v.
  Variables (b1 h1 n1 : Z).
  Hypothesis Hb1 : 0 <= b1.
  Hypothesis Hn1 : 0 <= n1.
  Variables (ext last : Z).
  Hypothesis TD : tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true.
  Hypothesis Hext : ext <= cext (is_lencode s).
  Hypothesis Hofs : cofs_ok (is_lencode s).
  Hypothesis CI : CINV (cv_NI v) (cv_NO v) c.
  Hypothesis LK : 1 <= code_op last <= 15 - is_lenbits s.
  Hypothesis LB : code_bits last = is_lenbits s.
  Hypothesis LXT : code_val last + 2 ^ code_op last <= ext.

  Local Abbreviation db := (is_lenbits s).
  Local Abbreviation A := (ctab6 v (is_lencode s)).
  Local Abbreviation lb := (code_bits last).
  Local Abbreviation lop := (code_op last).
  Local Abbreviation lv := (code_val last).
  Definition lidx2 (h : Z) : Z := lv + Z.shiftr (BITSv h (lb + lop)) lb.
  Definition lent2 (h : Z) : Z := cat (is_codes s) (is_lencode s) (lidx2 h).

  Definition LK2 (r : iregs) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 10 = zw (cv_ZP v) /\ getr R 11 = zw (cv_flush v)
    /\ getr R 22 = zw (cv_S v + 168) /\ getr R 20 = zw 16209 /\ getr R 25 = zw A6_JTAB /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4
    /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 27 = zw (cv_S v + 7160)
    /\ getr R 12 = zw h1 /\ getr R 13 = zw b1 /\ getr R 26 = zw (cv_I0 v + n1)
    /\ getr R 7 = zw (Z.ones (lb + lop)) /\ getr R 16 = zw lb /\ getr R 14 = zw lb /\ getr R 17 = zw lv /\ getr R 15 = zw A.
  Definition LJS2 (r : iregs) (R : bvmap 5 word) : Prop :=
    LK2 r R /\ getr R 23 = zw (ir_hold r) /\ getr R 5 = zw (ir_have r) /\ getr R 9 = zw (cv_I0 v + ir_next r)
    /\ getr R 6 = zw (ir_bits r) /\ getr R 29 = zw (ir_bits r)
    /\ b1 + 8 * (h1 - ir_have r) = ir_bits r /\ n1 + (h1 - ir_have r) = ir_next r /\ 0 <= h1 - ir_have r.
  Definition LJE2 (r : iregs) (R : bvmap 5 word) : Prop :=
    LK2 r R /\ getr R 23 = zw (ir_hold r) /\ getr R 5 = zw (ir_have r) /\ getr R 31 = zw (cv_I0 v + ir_next r)
    /\ getr R 6 = zw (ir_bits r)
    /\ getr R 30 = zw (A + 4 * lidx2 (ir_hold r)) /\ getr R 28 = zw (code_bits (lent2 (ir_hold r))).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold LJS2, LK2 in X;
    destruct X as ((G2 & G25 & G10 & G11 & G21 & G19 & G24 & G3 & G4 & G18 & G1 & G9 & G12 & G13 & G27 & G7 & G16 & G14 & G17 & G15)
                   & G22 & G5 & G23 & G6 & G29 & Ib & In & Ih).

  Definition lpins2 : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168)); (20, ELit 16209); (25, ELit 0x12510);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (27, EAdd (EVar 33%nat) (ELit 7160));
     (5, EVar 36%nat); (9, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EVar 41%nat); (29, EVar 41%nat);
     (7, EVar 45%nat); (16, EVar 46%nat); (14, EVar 46%nat); (17, EVar 47%nat); (15, EVar 48%nat);
     (12, EVar 49%nat); (13, EVar 50%nat); (26, EAdd (EVar 43%nat) (EVar 51%nat))].
  Definition lvb2 : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 31); (50%nat, 2 ^ 63); (51%nat, 2 ^ 31); (52%nat, 256)].

  Ltac l2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb :=
    cbn [famA]; rewrite ?bmod_get by exact Hby;
    rewrite ?idx2_pull by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]);
    lazymatch goal with
    | |- exists bs, rdn _ _ _ _ = Some bs /\ _ =>
        match goal with |- context [Z.shiftr (BITSv ?h (lb + lop)) lb] =>
          tab_read TAB (lv + Z.shiftr (BITSv h (lb + lop)) lb); pose proof (shiftr_BITSv_sub h lb lop ltac:(lia) ltac:(lia)); lia end
    | |- 0 <= _ /\ _ <= 2 ^ 64 =>
        match goal with |- context [Z.shiftr (BITSv ?h (lb + lop)) lb] =>
          generalize (shiftr_BITSv_sub h lb lop ltac:(lia) ltac:(lia)); clear - HA0 HA1 Hext LXT Hlv; intro; lia end
    | |- _ => try (rewrite wrap32_id in Hb by lia; exact Hb)
    end.

  Ltac lj2_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv :=
    let Q23 := fresh in let Q5 := fresh in let Q8 := fresh in let Q6 := fresh in let Q29 := fresh in
    let Q31 := fresh in let Q30 := fresh in let Q28 := fresh in
    symex_reg HR (23%bv : reg) as Q23; symex_reg HR (5%bv : reg) as Q5; symex_reg HR (9%bv : reg) as Q8;
    symex_reg HR (6%bv : reg) as Q6; symex_reg HR (29%bv : reg) as Q29; symex_reg HR (31%bv : reg) as Q31;
    symex_reg HR (30%bv : reg) as Q30; symex_reg HR (28%bv : reg) as Q28;
    cbn [famA] in Q23, Q30; rewrite ?bmod_get in Q23, Q30 by exact Hby;
    unfold LJS2, LJE2, LK2, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q23; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q5; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q8; f_equal; lia
          | rewrite Q31; f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q29; f_equal; lia
          | rewrite Q30; rewrite idx2_pull; [f_equal; lia | clear - Rbits; lia | clear - Hb64; lia | exact Rhold | exact Hby | clear - Rt1 LK LB; lia | clear - Rt1 LK LB; lia | exact Hlv]
          | rewrite Q28; reflexivity
          | lia
          | match goal with |- ?G => idtac "LJ2 LEFT" G end ].

  Lemma len2_step_H : forall r R M,
    LMEM v (mkW s c r) M -> LJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < wrap32 (lb + code_bits (lent2 (ir_hold (pull1 c r)))) ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1e504) M s6_rom) (mkst R1 (Z_to_bv 64 0x1e504) M s6_rom)
               /\ LJS2 (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (lb + lop) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hlv.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hofs) as TAB.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    pose proof (code_bits_range (lent2 (ir_hold (pull1 c r)))) as Hcb.
    unfold lent2, lidx2 in Hb, Hcb |- *. cbn [ir_hold pull1] in Hb, Hcb |- *.
    arm_symexP (@nil (Z * expr)) ilL2 20%nat [false; true] [RVal (EVar 52%nat)] lpins2 lvb2 v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1;
       code_bits (cat (is_codes s) (is_lencode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1e504) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: l2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb.
    all: match goal with |- ?G => idtac "LEFTL2H" G end.
    exists R1. split; [by_run Hms|].
    lj2_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv.
  Qed.

  Lemma len2_step_E : forall r R M,
    LMEM v (mkW s c r) M -> LJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    wrap32 (lb + code_bits (lent2 (ir_hold (pull1 c r)))) <= ir_bits r + 8 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1e504) M s6_rom) (mkst R1 (Z_to_bv 64 0x1e56c) M s6_rom)
               /\ LJE2 (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (lb + lop) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hlv.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hofs) as TAB.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    pose proof (code_bits_range (lent2 (ir_hold (pull1 c r)))) as Hcb.
    unfold lent2, lidx2 in Hb, Hcb |- *. cbn [ir_hold pull1] in Hb, Hcb |- *.
    arm_symexP (@nil (Z * expr)) ilL2 20%nat [false; false] [RVal (EVar 52%nat)] lpins2 lvb2 v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1;
       code_bits (cat (is_codes s) (is_lencode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1e504) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: l2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb.
    all: try (rewrite wrap32_id in Hb by lia; clear - Hb; lia).
    all: match goal with |- ?G => idtac "LEFTL2E" G end.
    exists R1. split; [by_run Hms|].
    lj2_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv.
  Qed.

  Lemma len2_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1e504) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_djs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (lb + lop) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hlv.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia). open_retc HRC.
    arm_symexP (@nil (Z * expr)) ilL2 14%nat [true] [RVal (EVar 52%nat)] lpins2
      [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 31); (50%nat, 2 ^ 63); (51%nat, 2 ^ 31); (52%nat, 2 ^ 64)] v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1e504) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTL2D" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (24%bv : reg) as G23'. symex_reg HR1 (18%bv : reg) as G9'. symex_reg HR1 (27%bv : reg) as G26'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. unfold INF_FRAME in G2. regs_via Hfr.
    all: first [ rewrite G9'; rewrite Hh; reflexivity
               | rewrite G23'; f_equal; clear - Ib Hh; lia
               | rewrite G26'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite G8'; apply zw_neg_mod
               | match goal with |- ?G => idtac "LDRY2 LEFT" G end ].
  Qed.
End LenL2.
End FXG.

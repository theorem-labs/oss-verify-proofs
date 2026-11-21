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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilD1 : cfg := ilSx [0x1e624; 0x1e66c] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section DistL1.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Hypothesis C : ictx v.
  Variables (b0 h0 n0 : Z).
  Hypothesis Hb0 : 0 <= b0.
  Hypothesis Hn0 : 0 <= n0.
  Variable ext : Z.
  Hypothesis TD : tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true.
  Hypothesis Hext : ext <= cext (is_distcode s).
  Hypothesis Hofs : cofs_ok (is_distcode s).
  Hypothesis CI : CINV (cv_NI v) (cv_NO v) c.

  Local Abbreviation db := (is_distbits s).
  Local Abbreviation A := (ctab6 v (is_distcode s)).
  Definition dent1 (h : Z) : Z := cat (is_codes s) (is_distcode s) (BITSv h db).

  Definition DK (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 24 = zw b0 /\ getr R 18 = zw h0 /\ getr R 27 = zw (cv_I0 v + n0)
    /\ getr R 17 = zw (Z.ones db) /\ getr R 15 = zw A.
  Definition DJS (r : iregs) (R : bvmap 5 word) : Prop :=
    DK r R /\ getr R 23 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 6 = zw (cv_I0 v + ir_next r)
    /\ getr R 5 = zw (ir_bits r) /\ getr R 13 = zw (ir_bits r)
    /\ b0 + 8 * (h0 - ir_have r) = ir_bits r /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition DJE (r : iregs) (R : bvmap 5 word) : Prop :=
    DK r R /\ getr R 23 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 13 = zw (ir_bits r)
    /\ getr R 16 = zw (A + 4 * BITSv (ir_hold r) db) /\ getr R 14 = zw (code_bits (dent1 (ir_hold r))).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold DJS, DK in X;
    destruct X as ((HF & G18 & G1 & G23 & G9 & G26 & G17 & G15) & G22 & G12 & G6 & G5 & G13 & Ib & In & Ih); open_fix HF.

  Definition dpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (12, EVar 36%nat); (6, EAdd (EVar 43%nat) (EVar 44%nat)); (5, EVar 41%nat); (13, EVar 41%nat);
     (17, EVar 45%nat); (15, EVar 46%nat);
     (24, EVar 47%nat); (18, EVar 48%nat); (27, EAdd (EVar 43%nat) (EVar 49%nat))].
  Definition dvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 256)].

  Ltac d1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext :=
    cbn [famA]; rewrite ?bmod_get by exact Hby;
    rewrite ?idx1_exec by (first [exact Rhold | exact Hby | clear - Rbits Hb64 Rt1; lia]);
    lazymatch goal with
    | |- exists bs, rdn _ _ _ _ = Some bs /\ _ => match goal with |- context [BITSv ?h ?n] => tab_read TAB (BITSv h n); pose proof (BITSv_bound h n ltac:(lia)); lia end
    | |- 0 <= _ /\ _ <= 2 ^ 64 => match goal with |- context [BITSv ?h ?n] => generalize (BITSv_bound h n ltac:(lia)); clear - HA0 HA1 Hext Rt2; intro; lia end
    | |- _ => idtac
    end.

  Ltac dj_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 :=
    let Q23 := fresh in let Q12 := fresh in let Q6 := fresh in let Q5 := fresh in let Q13 := fresh in
    let Q27 := fresh in let Q16 := fresh in let Q14 := fresh in
    symex_reg HR (23%bv : reg) as Q23; symex_reg HR (12%bv : reg) as Q12; symex_reg HR (6%bv : reg) as Q6;
    symex_reg HR (5%bv : reg) as Q5; symex_reg HR (13%bv : reg) as Q13; symex_reg HR (26%bv : reg) as Q27;
    symex_reg HR (16%bv : reg) as Q16; symex_reg HR (14%bv : reg) as Q14;
    cbn [famA] in Q23, Q16; rewrite ?bmod_get in Q23, Q16 by exact Hby;
    unfold DJS, DJE, DK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with HF : LFIX _ _ |- LFIX _ _ => apply (LFIX_frame _ _ _ _ HF Hfr); reflexivity end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q23; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q27; f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q13; rewrite ?szwrap32_small by (clear - Rbits Hb64; lia); f_equal; lia
          | rewrite Q16; rewrite idx1_exec; [f_equal; lia | clear - Rbits; lia | clear - Hb64; lia | exact Rhold | exact Hby | lia]
          | rewrite Q14; reflexivity
          | lia
          | match goal with |- ?G => idtac "DJ LEFT" G end ].

  Lemma dist1_step_H : forall r R M,
    LMEM v (mkW s c r) M -> DJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < code_bits (dent1 (ir_hold (pull1 c r))) ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1e624) M s6_rom) (mkst R1 (Z_to_bv 64 0x1e624) M s6_rom)
               /\ DJS (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_distcode s) C HM Hofs) as TAB.
    pose proof (ones_range15 db Rt1) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (dent1 (ir_hold (pull1 c r)))) as Hcb.
    unfold dent1 in Hb, Hcb |- *. cbn [ir_hold pull1] in Hb, Hcb |- *.
    arm_symexP (@nil (Z * expr)) ilD1 16%nat [false; true] [RVal (EVar 50%nat)] dpins dvb v r
      [Z.ones db; A; b0; h0; n0; code_bits (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1e624) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: d1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTD1H" G end.
    exists R1. split; [by_run Hms|].
    dj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma dist1_step_E : forall r R M,
    LMEM v (mkW s c r) M -> DJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    code_bits (dent1 (ir_hold (pull1 c r))) <= ir_bits r + 8 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1e624) M s6_rom) (mkst R1 (Z_to_bv 64 0x1e66c) M s6_rom)
               /\ DJE (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_distcode s) C HM Hofs) as TAB.
    pose proof (ones_range15 db Rt1) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (dent1 (ir_hold (pull1 c r)))) as Hcb.
    unfold dent1 in Hb, Hcb |- *. cbn [ir_hold pull1] in Hb, Hcb |- *.
    arm_symexP (@nil (Z * expr)) ilD1 16%nat [false; false] [RVal (EVar 50%nat)] dpins dvb v r
      [Z.ones db; A; b0; h0; n0; code_bits (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1e624) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: d1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTD1E" G end.
    exists R1. split; [by_run Hms|].
    dj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma dist1_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> DJS r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1e624) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_djs HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 db Rt1) as Hones.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilD1 14%nat [true] [RVal (EVar 50%nat)] dpins
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 2 ^ 64)] v r
      [Z.ones db; A; b0; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1e624) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTD1D" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (24%bv : reg) as G23'. symex_reg HR1 (18%bv : reg) as G9'. symex_reg HR1 (27%bv : reg) as G26'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite G9'; rewrite Hh; reflexivity
               | rewrite G23'; f_equal; clear - Ib Hh; lia
               | rewrite G26'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite G8'; apply zw_neg_mod
               | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End DistL1.
End FXG.

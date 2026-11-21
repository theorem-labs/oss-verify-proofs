(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Distext1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilXL : cfg := ilSx [0x1d164; 0x1d9e8] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section LenextLoop.
  Variable v : icv.
  Hypothesis C : ictx v.
  Variables (b0 h0 n0 ex : Z).
  Hypothesis Hex : 1 <= ex <= 15.
  Hypothesis Hb0 : 0 <= b0.
  Hypothesis Hn0 : 0 <= n0.

  Ltac open_xjs HJ :=
    let X := fresh in pose proof HJ as X; unfold XJS, XK in X;
    destruct X as ((HF & G18 & G1 & G13 & G23 & G9 & G26) & G22 & G14 & G12 & G16 & Ib & In & Ih); open_fix HF.

  Ltac xje_close HR Hfr c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let G22 := fresh in let G14 := fresh in let G12 := fresh in let G15 := fresh in let G16 := fresh in
    symex_reg HR (23%bv : reg) as G22; symex_reg HR (14%bv : reg) as G14; symex_reg HR (12%bv : reg) as G12;
    symex_reg HR (15%bv : reg) as G15; symex_reg HR (16%bv : reg) as G16;
    cbn [famA] in G22; rewrite bmod_get in G22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in G22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold XJS, XJE, XK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with HF : LFIX _ _ |- LFIX _ _ => apply (LFIX_frame _ _ _ _ HF Hfr); reflexivity end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G22; f_equal; lia
          | rewrite G14; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite G12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite G15; f_equal; lia
          | rewrite G16; f_equal; lia
          | lia
          | match goal with |- ?G => idtac "XJ LEFT" G end ].

  Lemma lenext_step_H : forall s c r R M,
    LMEM v (mkW s c r) M -> XJS v b0 h0 n0 ex c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < ex -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d164) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d164) M s6_rom)
               /\ XJS v b0 h0 n0 ex c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hh. open_xjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilXL 12%nat [true; true] (@nil (option expr)) xpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31)] v r [ex; b0; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d164) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXH" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hex; lia).
    xje_close HR1 Hfr c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma lenext_step_E : forall s c r R M,
    LMEM v (mkW s c r) M -> XJS v b0 h0 n0 ex c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < ex -> ex <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d164) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d9e8) M s6_rom)
               /\ XJE v b0 h0 n0 ex c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hb8 Hh. open_xjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilXL 12%nat [true; false] (@nil (option expr)) xpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31)] v r [ex; b0; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d164) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hex; lia).
    xje_close HR1 Hfr c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma lenext_dry : forall s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> XJS v b0 h0 n0 ex c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < ex -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d164) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros s c r R M HM HRC HJ RI CI Hb Hh. open_xjs HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilXL 12%nat [false] [RVal (EVar 49%nat)] xpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31); (49%nat, 2 ^ 64)] v r [ex; b0; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d164) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXD" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (24%bv : reg) as G23'. symex_reg HR1 (18%bv : reg) as G9'. symex_reg HR1 (27%bv : reg) as G26'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite G9'; rewrite Hh; reflexivity
               | rewrite G23'; f_equal; clear - Ib Hh; lia
               | rewrite G26'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite G8'; apply zw_neg_mod
               | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End LenextLoop.
End FXG.

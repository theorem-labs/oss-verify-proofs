(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Match2 InflA_Match3 InflA_Match5.

Module InflA_Distext1.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilX : cfg := ilSx [0x20f7c; 0x20fd0] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section DistextLoop.
  Variable v : icv.
  Hypothesis C : ictx v.
  Variables (b0 h0 n0 ex : Z).
  Hypothesis Hex : 1 <= ex <= 15.
  Hypothesis Hb0 : 0 <= b0.
  Hypothesis Hn0 : 0 <= n0.

  Definition XFIX (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 1 = zw 16209 /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
  Lemma LFIX_XFIX : forall R, LFIX v R -> XFIX R.
  Proof. intros R HF. unfold LFIX in HF. destruct HF as (G2 & G27 & G13 & G8 & G11 & G1 & G3 & G4). unfold XFIX. repeat split; assumption. Qed.

  Definition XK (r : iregs) (R : bvmap 5 word) : Prop :=
    XFIX R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 14 = zw ex /\ getr R 19 = zw b0 /\ getr R 12 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0).
  Definition XJS (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    XK r R /\ getr R 16 = zw ex /\ getr R 25 = zw (ir_hold r) /\ getr R 15 = zw (ir_bits r) /\ getr R 11 = zw (ir_bits r) /\ getr R 23 = zw (ir_have r)
    /\ getr R 5 = zw (cv_I0 v + ir_next r) /\ getr R 17 = zw (cv_I0 v + ir_next r)
    /\ b0 + 8 * (h0 - ir_have r) = ir_bits r /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition XJE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    XK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 11 = zw (ir_bits r) /\ getr R 23 = zw (ir_have r) /\ getr R 13 = zw (cv_I0 v + ir_next r).

  Ltac open_xfix HF :=
    let X := fresh in pose proof HF as X; unfold XFIX, INF_FRAME in X; destruct X as (G2 & G27 & G8 & G1 & G3 & G4).
  Ltac open_xjs HJ :=
    let X := fresh in pose proof HJ as X; unfold XJS, XK in X;
    destruct X as ((HF & G9 & G14 & G18 & G12 & G25) & G16 & G22 & G15 & G11 & G24 & G5 & G17 & Ib & In & Ih); open_xfix HF.

  Definition xpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (15, EVar 41%nat); (11, EVar 41%nat); (23, EVar 36%nat); (5, EAdd (EVar 43%nat) (EVar 44%nat)); (17, EAdd (EVar 43%nat) (EVar 44%nat));
     (14, EVar 45%nat); (16, EVar 45%nat); (19, EVar 46%nat); (12, EVar 47%nat); (26, EAdd (EVar 43%nat) (EVar 48%nat))].

  Ltac xfix_close Hfr HR :=
    unfold XFIX, INF_FRAME;
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with |- getr _ ?n = _ =>
      first [ rewrite (Hfr n eq_refl); assumption
            | let G := fresh "G" in symex_reg HR n as G; rewrite G; first [ reflexivity | assumption | apply zw_neg_mod | f_equal; lia ]
            | match goal with |- ?G => idtac "XFIX LEFT" G end ]
    end.

  Ltac xje_close HR Hfr c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let Q22 := fresh in let Q15 := fresh in let Q11 := fresh in let Q24 := fresh in let Q5 := fresh in let Q17 := fresh in let Q13 := fresh in
    symex_reg HR (25%bv : reg) as Q22; symex_reg HR (15%bv : reg) as Q15; symex_reg HR (11%bv : reg) as Q11; symex_reg HR (23%bv : reg) as Q24;
    symex_reg HR (5%bv : reg) as Q5; symex_reg HR (17%bv : reg) as Q17; symex_reg HR (13%bv : reg) as Q13;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold XJS, XJE, XK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- XFIX _ => xfix_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q22; f_equal; lia
          | rewrite Q15; f_equal; lia
          | rewrite Q11; f_equal; lia
          | rewrite Q24; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q17; f_equal; lia
          | rewrite Q13; f_equal; lia
          | lia
          | match goal with |- ?G => idtac "XJ LEFT" G end ].

  Lemma distext_step_H : forall s c r R M,
    LMEM v (mkW s c r) M -> XJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < ex -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20f7c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20f7c) M s6u_rom)
               /\ XJS c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hh. open_xjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilX 20%nat [false; false; false; true] (@nil (option expr)) xpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31)] v r [ex; b0; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20f7c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXH" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hex; lia).
    xje_close HR1 Hfr c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma distext_step_E : forall s c r R M,
    LMEM v (mkW s c r) M -> XJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < ex -> ex <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20f7c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20fd0) M s6u_rom)
               /\ XJE c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hb8 Hh. open_xjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilX 20%nat [false; false; false; false] (@nil (option expr)) xpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31)] v r [ex; b0; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20f7c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hex; lia).
    xje_close HR1 Hfr c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma distext_dry : forall s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> XJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < ex -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20f7c) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros s c r R M HM HRC HJ RI CI Hb Hh. open_xjs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilX 16%nat [true] [RVal (EVar 49%nat); RVal (EVar 35%nat)] xpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31); (49%nat, 2 ^ 64)] v r [ex; b0; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20f7c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXD" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (26%bv : reg) as Q25.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite Q24; rewrite Hh; reflexivity
               | rewrite Q18; f_equal; clear - Ib Hh; lia
               | rewrite Q25; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite Q26; apply zw_neg_mod
               | lazymatch goal with |- getr _ ?n = _ => let G := fresh in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption] end
               | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End DistextLoop.
End FXG.
End InflA_Distext1.

Module InflA_Distext2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Match2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Match3 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Match5 InflA_Distext1.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition dx_s (s : inflate_state) (r1 : iregs) : inflate_state :=
  iset_mode (iset_back (iset_offset s (is_offset s + ir_hold r1 mod 2 ^ is_extra s)) (swrap32 (is_back s + is_extra s))) MATCH.
Definition dx_r (s : inflate_state) (r1 : iregs) : iregs :=
  irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ is_extra s)) (ir_bits r1 - is_extra s).

Lemma arm_DISTEXT_run : forall s c r c1 r1,
  0 < is_extra s <= 15 -> 0 <= is_offset s -> is_offset s + 2 ^ is_extra s <= 2 ^ 32 ->
  NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c1 r1) ->
  is_extra s <= ir_bits r1 < 64 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  arm_DISTEXT ivar_ref (mkW s c r) = arm_MATCH ivar_ref (mkW (dx_s s r1) c1 (dx_r s r1)).
Proof.
  intros s c r c1 r1 Hex Hoff Hoe HN Hb Hh.
  assert (Hv : 0 <= ir_hold r1 mod 2 ^ is_extra s < 2 ^ is_extra s) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. rewrite add_back_eq. cbv beta iota.
  mstep1 set_mode_eq. unfold dx_s, dx_r, bkv. cbn [iv_aux ivar_ref]. irnorm.
  rewrite (BITSv_land (ir_hold r1) (is_extra s)), Z.land_ones by lia.
  rewrite wrap32_id by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap32_id by lia.
  reflexivity.
Qed.

Lemma arm_DISTEXT_zero : forall s c r,
  is_extra s = 0 -> arm_DISTEXT ivar_ref (mkW s c r) = arm_MATCH ivar_ref (mkW (iset_mode s MATCH) c r).
Proof.
  intros s c r H0. unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). rewrite H0. cbn [Z.eqb negb].
  mstep1 (@aret_eq unit). mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_DISTEXT_leave : forall s c r w1,
  is_extra s <> 0 -> NEEDBITS (is_extra s) (mkW s c r) = ALeave w1 -> arm_DISTEXT ivar_ref (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 H0 HN. unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. reflexivity.
Qed.



Lemma testbit_high64 : forall h m, 0 <= h < 2 ^ 64 -> 64 <= m -> Z.testbit h m = false.
Proof.
  intros h m Hh Hm. destruct (Z.eq_dec h 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [| lia]. apply (proj1 (Z.log2_lt_pow2 h 64 ltac:(lia))). lia.
Qed.
Lemma mask_exec : forall h e, 0 <= h < 2 ^ 64 -> 0 <= e < 32 ->
  Z.land h (Z.lxor (zaluw ALU_SLL (-1) e) (-1)) = h mod 2 ^ e.
Proof.
  intros h e Hh He. rewrite zaluw_sll_m1 by lia.
  replace (2 ^ 64 - 2 ^ e) with (Z.ldiff (Z.ones 64) (Z.ones e)).
  2:{ rewrite <- Z.sub_nocarry_ldiff.
      - unfold Z.ones. rewrite !Z.shiftl_1_l. lia.
      - apply Z.bits_inj'. intros m Hm. rewrite Z.ldiff_spec, Z.bits_0.
        destruct (Z_lt_le_dec m e); [| rewrite (Z.ones_spec_high e m) by lia; reflexivity].
        rewrite (Z.ones_spec_low e m), (Z.ones_spec_low 64 m) by lia. reflexivity. }
  rewrite Z.lxor_m1_r. rewrite <- Z.ldiff_land.
  rewrite <- (Z.land_ones h e) by lia.
  apply Z.bits_inj'. intros m Hm. rewrite Z.ldiff_spec, Z.ldiff_spec, Z.land_spec.
  destruct (Z_lt_le_dec m e).
  - rewrite (Z.ones_spec_low e m), (Z.ones_spec_low 64 m) by lia. cbn. rewrite andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high e m) by lia. destruct (Z_lt_le_dec m 64).
    + rewrite (Z.ones_spec_low 64 m) by lia. cbn. rewrite andb_false_r. reflexivity.
    + rewrite (Z.ones_spec_high 64 m) by lia. rewrite (testbit_high64 h m) by lia. reflexivity.
Qed.

Lemma le4_swrap32 : forall x, Z_to_le_bytes 4 (swrap32 x) = Z_to_le_bytes 4 x.
Proof. intros x. apply le4_eqm. unfold swrap32, two31. rewrite wrap32_mod. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.

Definition distext_facts (v : icv) (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  is_sane s = 1 /\ 3 <= is_length s <= 258 /\ 1 <= is_offset s /\ 0 <= is_extra s <= 15
  /\ is_offset s + Z.shiftl 1 (is_extra s) - 1 <= 32768 /\ - 2 ^ 31 <= is_back s < 2 ^ 31
  /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ arr_len (is_window s) = cv_WN v /\ (is_wsize s = 0 \/ is_wsize s = cv_WN v)
  /\ (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256)
  /\ RINV (cv_NI v) (cv_NO v) r /\ CINV (cv_NI v) (cv_NO v) c.

Lemma sinv_distext : forall s, sinv s -> is_mode s = DISTEXT ->
  3 <= is_length s <= 258 /\ 1 <= is_offset s /\ 0 <= is_extra s <= 15 /\ is_offset s + Z.shiftl 1 (is_extra s) - 1 <= 32768.
Proof. intros s H Hm. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & Q & _). exact (Q Hm). Qed.
Lemma sr_back : forall s, SRNGq s -> - 2 ^ 31 <= is_back s < 2 ^ 31.
Proof. intros s H. do 28 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.

Lemma distext_facts_of_pinv : forall v s c r,
  is_mode s = DISTEXT -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> distext_facts v s c r.
Proof.
  intros v s c r Hmode HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_distext s PS Hmode) as (Hlen & Hoff & Hex & Hoe). pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof (sr_back s SR) as Hback.
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  unfold distext_facts. repeat (split; [assumption|]). exact CI.
Qed.


Definition ilXA : cfg := CFG [] [] arm_rets (0x20f7c :: 0x20fd0 :: arm_stops) [].

Section DistextBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_df HD :=
    destruct HD as (Hsane & Hlen & Hoff & Hex & Hoe & Hback & Hwh & Hwn & Hwl & Hws & Hwb & RI & CI).

  Lemma distext_body : forall s c r1 R M b0 h0 n0,
    is_mode s = DISTEXT -> distext_facts v s c r1 -> is_extra s <> 0 -> is_extra s <= ir_bits r1 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> XJE v b0 h0 n0 (is_extra s) c r1 R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20fd0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M (arm_MATCH ivar_ref (mkW (dx_s s r1) c (dx_r s r1))) R' M' pc'.
  Proof.
    intros s c r1 R M b0 h0 n0 Hmode HD Hex0 Hbx HM HRC HX HJ. open_df HD.
    destruct HJ as ((HF & G9 & G14 & G18 & G12 & G25) & G22 & G11 & G24 & G13).
    pose proof HF as HF'. unfold XFIX, INF_FRAME in HF'. destruct HF' as (G2 & G27 & G8 & G1 & G3 & G4).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_offset _ _ _ _ Msc) as C96. pose proof (is6_back _ _ _ _ Msc) as C7148.
    replace (cv_S v + 7164) with (cv_S v + 7160 + 4) in C7148 by lia.
    assert (Hbm : 0 <= is_back s mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    assert (P2e : 0 < 2 ^ is_extra s <= 2 ^ 15) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.shiftl_1_l in Hoe.
    set (ex := is_extra s) in *.
    arm_symexP (@nil (Z * expr)) ilS 24%nat [false] [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 35%nat)]
      [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
       (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
       (11, EVar 41%nat); (23, EVar 36%nat); (13, EAdd (EVar 43%nat) (EVar 44%nat)); (14, EVar 45%nat)]
      [(45%nat, 16); (46%nat, 32769); (47%nat, 2 ^ 63); (48%nat, 2 ^ 32)] v r1
      [ex; is_offset s; cv_S v + 7160; is_back s mod 2 ^ 32] NoVals F0
      (mkst R (Z_to_bv 64 0x20fd0) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    rewrite (mask_exec (ir_hold r1) ex Rhold64 ltac:(lia)) in Hms1.
    rewrite (szwrap32_of_mod32 (is_back s) Hback) in Hms1.
    rewrite <- (le4_swrap32 (is_back s + ex)) in Hms1.
    replace (cv_S v + 7160 + 4) with (cv_S v + 7164) in Hms1 by lia.
    set (v1 := ir_hold r1 mod 2 ^ ex) in *.
    assert (Hv1 : 0 <= v1 < 2 ^ ex) by (subst v1; apply Z.mod_pos_bound; lia).
    set (M1 := wbytes M (zw (cv_S v + 112)) (Z_to_le_bytes 4 (is_offset s + v1))) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (is_back s + ex)))) in *.
    set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16204)) in *.
    set (s1 := iset_offset s (is_offset s + v1)). set (s2 := iset_back s1 (swrap32 (is_back s + ex))). set (s3 := iset_mode s2 MATCH).
    assert (Es3 : dx_s s r1 = s3) by (subst s3 s2 s1 v1 ex; reflexivity).
    assert (HM1 : LMEM v (mkW s1 c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M 112 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_offset M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW s2 c r1) M2).
    { apply (LMEM_store_scalar v C s1 c r1 _ M1 7164 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_back M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3' : LMEM v (mkW s3 c r1) M3).
    { apply (LMEM_store_scalar v C s2 c r1 _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M2 (cv_S v) _ s2 MATCH (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW (dx_s s r1) c (dx_r s r1)) M3).
    { rewrite Es3. apply (LMEM_regs v s3 c r1 c (dx_r s r1) M3 HM3'); reflexivity. }
    assert (HRC3 : RETC v (mkW (dx_s s r1) c (dx_r s r1)) M3).
    { subst M3 M2 M1. apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]. }
    assert (HX3 : LX v (mkW (dx_s s r1) c (dx_r s r1))).
    { rewrite Es3. apply (LX_step0 v s c r1 s3 c (dx_r s r1) HX NH NB); subst s3 s2 s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side]. }
    pose proof (hold_drop (ir_hold r1) (ir_bits r1) ex ltac:(lia) Rhold) as HD'.
    assert (HE3 : ENTRY v (mkW (dx_s s r1) c (dx_r s r1)) R1 M3).
    { split; [exact HM3|]. split; [exact HRC3|]. split; [exact HX3|].
      symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25.
      unfold LREG_arm, LVARS; cbn [w_r w_s]. unfold dx_r. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
      split; [| split; [| rewrite Es3; subst s3; cbn; intros Hb; exfalso; cbv in Hb; discriminate]].
      - lfix_close Hfr1 HR1.
      - regs_via Hfr1; first [exact Q24 | rewrite Q22; rewrite zalu_srl_small by (clear - Rhold64 Hex; lia); reflexivity
                             | rewrite Q18; rewrite szwrap32_small by (clear - Rbits Hbx Hex; lia); reflexivity | exact Q25 | match goal with |- ?G => idtac "DXREG LEFT" G end]. }
    assert (MF3 : match_facts v (dx_s s r1) c (dx_r s r1)).
    { rewrite Es3. unfold match_facts. subst s3 s2 s1. cbn. unfold dx_r. unfold RINV in *. cbn.
      refine (conj Hsane (conj _ (conj _ (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj _ CI)))))))));
        [clear - Hlen; lia | clear - Hoff Hoe Hv1; subst ex v1; lia | clear - RI HD' Hbx Hex; subst ex; lia]. }
    destruct (match_core v C (dx_s s r1) c (dx_r s r1) R1 M3 ltac:(rewrite Es3; reflexivity) HE3 MF3) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r1) (mkW (dx_s s r1) c (dx_r s r1)) M M3); [rewrite Es3; subst s3 s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. unfold dx_r. cbn [ir_put irset_bits irset_hold]. subst M3 M2 M1.
    do 3 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.
End DistextBody.
End FXG.
End InflA_Distext2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Match2 InflA_Match3 InflA_Match5. Import InflA_Distext1. Import InflA_Distext2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilXE : cfg := CFG [] [] arm_rets (0x20f54 :: arm_stops) [].

Definition LVX (v : icv) (w : iw) (R : bvmap 5 word) : Prop :=
  let r := w_r w in
  getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r) /\ getr R 26 = zw (cv_I0 v + ir_next r).
Definition xe_pins : list (Z * expr) :=
  [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (11, EVar 35%nat); (1, ELit 16209);
   (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))].

Section DistextCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_df HD :=
    destruct HD as (Hsane & Hlen & Hoff & Hex & Hoe & Hback & Hwh & Hwn & Hwl & Hws & Hwb & RI & CI).

  Lemma distext_core : forall s c r R M,
    is_mode s = DISTEXT -> distext_facts v s c r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVX v (mkW s c r) R ->
    getr R 14 = zw (is_extra s) -> getr R 12 = zw (ir_have r) ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20f54) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_DISTEXT ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD HM HRC HX HF HV G14 G12. pose proof HD as HD0. open_df HD.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF.
    pose proof HV as XV. unfold LVX in XV. cbn [w_r] in XV. destruct XV as (G9 & G22 & G18 & G25). open_rinv RI. open_cinv CI.
    pose proof HF as XF. unfold LFIX, INF_FRAME in XF. destruct XF as (P2 & P27 & P13 & P8 & P11 & P1 & _ & _).
    pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    pose proof (LFIX_XFIX v R HF) as HXF.
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    rewrite Z.shiftl_1_l in Hoe.
    destruct (Z.eq_dec (is_extra s) 0) as [E0|E0].
    -
      rewrite (arm_DISTEXT_zero s c r E0). rewrite E0 in G14.
      arm_symexP xe_pins ilXA 8%nat [true] (@nil (option expr)) [(14, ELit 0); (12, EVar 36%nat)] (@nil (nat * Z)) v r (@nil Z) NoVals F0
        (mkst R (Z_to_bv 64 0x20f54) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16204)) in *.
      assert (HM1 : LMEM v (mkW (iset_mode s MATCH) c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M (cv_S v) _ s MATCH Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HE1 : ENTRY v (mkW (iset_mode s MATCH) c r) R1 M1).
      { split; [exact HM1|]. split; [subst M1; retc_tower C HRC|]. split.
        - apply (LX_step0 v s c r _ c r HX NH NB); try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side].
        - unfold LREG_arm. split; [lfix_close Hfr1 HR1|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1; symex_reg HR1 (23%bv : reg) as Q24; exact Q24 | cbn; intros Hb; exfalso; cbv in Hb; discriminate]. }
      assert (MF1 : match_facts v (iset_mode s MATCH) c r).
      { unfold match_facts. cbn. rewrite E0 in Hoe. refine (conj Hsane (conj _ (conj _ (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj RI CI))))))))); [clear - Hlen; lia | clear - Hoff Hoe; cbn in Hoe; lia]. }
      destruct (match_core v C (iset_mode s MATCH) c r R1 M1 ltac:(reflexivity) HE1 MF1) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
      apply (arm_post_chain v (mkW s c r) (mkW (iset_mode s MATCH) c r) M M1); [apply same_blocks_mode | | exact HPOST].
      cbn [w_r]. subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    -
      assert (Hex1 : 1 <= is_extra s <= 15) by (clear - Hex E0; lia).
      assert (P2e : 0 < 2 ^ is_extra s) by (apply Z.pow_pos_nonneg; lia).
      destruct (Z_le_gt_dec (is_extra s) (ir_bits r)) as [GE|LT].
      +
        assert (HN : NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
        rewrite (arm_DISTEXT_run s c r c r ltac:(lia) ltac:(lia) ltac:(clear - Hoe P2e Hoff; lia) HN ltac:(clear - GE Rbits; lia) Rhold).
        arm_symexP xe_pins ilXA 10%nat [false; true] (@nil (option expr)) [(14, EVar 45%nat); (12, EVar 36%nat)] [(45%nat, 16)] v r [is_extra s] NoVals F0
          (mkst R (Z_to_bv 64 0x20f54) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        assert (HJ : XJE v (ir_bits r) (ir_have r) (ir_next r) (is_extra s) c r R1).
        { symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (11%bv : reg) as Q11.
          unfold XJE, XK. repeat match goal with |- _ /\ _ => split end;
            first [ lazymatch goal with |- XFIX _ _ => unfold XFIX, INF_FRAME; regs_via Hfr1 end
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                  | exact Q13 | exact Q24 | exact Q11
                  | match goal with |- ?G => idtac "XJE LEFT" G end ]. }
        destruct (distext_body v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD0 E0 GE HM HRC HX HJ) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
      +
        arm_symexP xe_pins ilXA 14%nat [false; false] (@nil (option expr)) [(14, EVar 45%nat); (12, EVar 36%nat)] [(45%nat, 16)] v r [is_extra s] NoVals F0
          (mkst R (Z_to_bv 64 0x20f54) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        assert (HJ : XJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s) c r R1).
        { symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (23%bv : reg) as Q24.
          symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (17%bv : reg) as Q17.
          unfold XJS, XK. repeat match goal with |- _ /\ _ => split end;
            first [ lazymatch goal with |- XFIX _ _ => unfold XFIX, INF_FRAME; regs_via Hfr1 end
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                  | rewrite Q16; rewrite ?Z.mod_small by (clear - Hex1; lia); reflexivity
                  | rewrite Q15; rewrite ?Z.mod_small by (clear - Rbits; lia); reflexivity
                  | exact Q11 | exact Q24 | exact Q5 | exact Q17 | clear; lia | clear - Rbits; lia
                  | match goal with |- ?G => idtac "XJS LEFT" G end ]. }
        pose proof (need_loop v (is_extra s) 0x20f7c 0x20fd0 (XJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s)) (XJE v (ir_bits r) (ir_have r) (ir_next r) (is_extra s)) C ltac:(lia)
                      (distext_step_H v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                      (distext_step_E v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                      (distext_dry v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                      8%nat s c r R1 M HM HRC HJ RI CI ltac:(lia) ltac:(cbn; clear - LT Rbits Hex1; lia)) as NL.
        change (NEEDBITS_k 8 (is_extra s)) with (NEEDBITS (is_extra s)) in NL.
        destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct NL].
        * destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
          destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
          pose proof RI1 as X. unfold RINV in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb1 & Rh1).
          rewrite (arm_DISTEXT_run s c r c r1 ltac:(lia) ltac:(lia) ltac:(clear - Hoe P2e Hoff; lia) EN ltac:(clear - Hb1 Rb1; lia) Rh1).
          assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
          assert (HD1 : distext_facts v s c r1) by (unfold distext_facts; rewrite Z.shiftl_1_l; exact (conj Hsane (conj Hlen (conj Hoff (conj Hex (conj Hoe (conj Hback (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj RI1 CI))))))))))))).
          destruct (distext_body v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD1 E0 ltac:(clear - Hb1; lia) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
          exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
          apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
        * destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
          destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
          rewrite (arm_DISTEXT_leave s c r _ E0 EN).
          exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
          cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
          split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
          apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.
End DistextCore.

Theorem arm_DISTEXT_sim : arm_stmt DISTEXT.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DISTEXT) with (arm_DISTEXT ivar_ref).
  pose proof (distext_facts_of_pinv v s c r Hmode HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  pose proof HM as HM0. pose proof HX as HX0. pose proof HF as HF0. pose proof HV as HV0.
  arm_begin C HM HRC HX HF HV HP.
  pose proof (is6_extra _ _ _ _ Msc) as C100.
  pose proof HD as HD'. destruct HD' as (_ & _ & _ & Hex & _).
  change (arm6_pc DISTEXT) with 0x1f1c8.
  arm_symex ilXE 6%nat (@nil bool) [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 16)] v r [is_extra s] NoVals F0
    (mkst R (Z_to_bv 64 0x1f1c8) M s6u_rom) R1 HR1 Hfr1 Hms1.
  all: try arm_side.
  symex_reg HR1 (14%bv : reg) as G14. symex_reg HR1 (12%bv : reg) as G12.
  destruct (distext_core v C s c r R1 M Hmode HD HM0 HRC HX0 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl)
              ltac:(unfold LVX; cbn [w_r]; regs_via Hfr1) G14 G12) as (R' & M' & pc' & Hms2 & HPOST).
  exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
Qed.
End FXG.

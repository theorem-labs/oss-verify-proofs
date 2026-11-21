(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflDec6 InflA_Dist3 InflA_Dist7.

Module InflA_Lenext1.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilXL : cfg := ilSx [0x1f16c; 0x1fd9c] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section LenextLoop.
  Variable v : icv.
  Hypothesis C : ictx v.
  Variables (b0 h0 n0 ex : Z).
  Hypothesis Hex : 1 <= ex <= 15.
  Hypothesis Hb0 : 0 <= b0.
  Hypothesis Hn0 : 0 <= n0.

  Definition NK (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 11 = zw ex /\ getr R 16 = zw ex /\ getr R 19 = zw b0 /\ getr R 12 = zw h0 /\ getr R 14 = zw (cv_I0 v + n0).
  Definition NJS (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    NK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 13 = zw (ir_bits r) /\ getr R 15 = zw (ir_bits r) /\ getr R 23 = zw (ir_have r)
    /\ getr R 5 = zw (cv_I0 v + ir_next r) /\ getr R 17 = zw (cv_I0 v + ir_next r)
    /\ b0 + 8 * (h0 - ir_have r) = ir_bits r /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition NJE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 11 = zw ex
    /\ getr R 25 = zw (ir_hold r) /\ getr R 13 = zw (ir_bits r) /\ getr R 23 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r).

  Ltac open_njs HJ :=
    let X := fresh in pose proof HJ as X; unfold NJS, NK in X;
    destruct X as ((HF & G9 & G11 & G16 & G18 & G12 & G14) & G22 & G13 & G15 & G24 & G5 & G17 & Ib & In & Ih); open_fixc HF.

  Definition xlpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (11, EVar 45%nat); (16, EVar 45%nat); (19, EVar 46%nat); (12, EVar 47%nat); (14, EAdd (EVar 43%nat) (EVar 48%nat));
     (25, EVar 40%nat); (13, EVar 41%nat); (15, EVar 41%nat); (23, EVar 36%nat);
     (5, EAdd (EVar 43%nat) (EVar 44%nat)); (17, EAdd (EVar 43%nat) (EVar 44%nat))].

  Ltac nje_close HR Hfr c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let Q22 := fresh in let Q13 := fresh in let Q15 := fresh in let Q24 := fresh in let Q5 := fresh in let Q25 := fresh in let Q17 := fresh in
    symex_reg HR (25%bv : reg) as Q22; symex_reg HR (13%bv : reg) as Q13; symex_reg HR (15%bv : reg) as Q15; symex_reg HR (23%bv : reg) as Q24;
    symex_reg HR (5%bv : reg) as Q5; symex_reg HR (26%bv : reg) as Q25; symex_reg HR (17%bv : reg) as Q17;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold NJS, NJE, NK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q22; f_equal; lia
          | rewrite Q13; f_equal; lia
          | rewrite Q15; f_equal; lia
          | rewrite Q24; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q25; f_equal; lia
          | rewrite Q17; f_equal; lia
          | lia
          | match goal with |- ?G => idtac "LJ LEFT" G end ].

  Lemma lenext_step_H : forall s c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < ex -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f16c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f16c) M s6u_rom)
               /\ NJS c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hh. open_njs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilXL 17%nat [true; true; true; true] (@nil (option expr)) xlpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31)] v r [ex; b0; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f16c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXH" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hex; lia).
    nje_close HR1 Hfr c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma lenext_step_E : forall s c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < ex -> ex <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f16c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fd9c) M s6u_rom)
               /\ NJE c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hb8 Hh. open_njs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilXL 18%nat [true; true; true; false] (@nil (option expr)) xlpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31)] v r [ex; b0; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f16c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hex; lia).
    nje_close HR1 Hfr c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma lenext_dry : forall s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < ex -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f16c) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros s c r R M HM HRC HJ RI CI Hb Hh. open_njs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilXL 14%nat [false] [RVal (EVar 49%nat); RVal (EVar 35%nat)] xlpins
      [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 31); (48%nat, 2 ^ 31); (49%nat, 2 ^ 64)] v r [ex; b0; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f16c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTXD" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (26%bv : reg) as Q25.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite Q24; rewrite Hh; reflexivity
               | rewrite (Hfr (23%bv : reg) eq_refl); rewrite G24; rewrite Hh; reflexivity
               | rewrite Q18; f_equal; clear - Ib Hh; lia
               | rewrite Q25; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite Q26; apply zw_neg_mod
               | lazymatch goal with |- getr _ ?n = _ => let G := fresh in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption] end
               | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End LenextLoop.
End FXG.
End InflA_Lenext1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Match2.

Module InflA_Lenext2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Distext3.InflA_Distext2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Distext3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflDec6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Match2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Distext3.InflA_Distext2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Dist3 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Dist7 InflA_Lenext1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition lx_len (s : inflate_state) (r1 : iregs) : Z := is_length s + ir_hold r1 mod 2 ^ is_extra s.
Definition lx_s (s : inflate_state) (r1 : iregs) : inflate_state :=
  iset_mode (iset_was (iset_back (iset_length s (lx_len s r1)) (swrap32 (is_back s + is_extra s))) (lx_len s r1)) DIST.
Definition lx_r (s : inflate_state) (r1 : iregs) : iregs :=
  irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ is_extra s)) (ir_bits r1 - is_extra s).

Lemma arm_LENEXT_run : forall s c r c1 r1,
  0 < is_extra s <= 15 -> 0 <= is_length s -> is_length s + 2 ^ is_extra s <= 2 ^ 32 ->
  NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c1 r1) ->
  is_extra s <= ir_bits r1 < 64 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  arm_LENEXT ivar_ref (mkW s c r) = arm_DIST ivar_ref (mkW (lx_s s r1) c1 (lx_r s r1)).
Proof.
  intros s c r c1 r1 Hex Hlen Hle HN Hb Hh.
  assert (Hv : 0 <= ir_hold r1 mod 2 ^ is_extra s < 2 ^ is_extra s) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. rewrite add_back_eq. cbv beta iota.
  rewrite abind_run. unfold aux. cbn [iv_aux ivar_ref bkv]. rewrite us_eq. cbv beta iota.
  mstep1 set_mode_eq. unfold lx_s, lx_r, lx_len. cbn [iv_aux ivar_ref]. irnorm.
  rewrite (BITSv_land (ir_hold r1) (is_extra s)), Z.land_ones by lia.
  rewrite wrap32_id by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap32_id by lia.
  destruct s; reflexivity.
Qed.

Lemma arm_LENEXT_zero : forall s c r,
  is_extra s = 0 -> arm_LENEXT ivar_ref (mkW s c r) = arm_DIST ivar_ref (mkW (iset_mode (iset_was s (is_length s)) DIST) c r).
Proof.
  intros s c r H0. unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). rewrite H0. cbn [Z.eqb negb].
  mstep1 (@aret_eq unit). rewrite abind_run. unfold aux. cbn [iv_aux ivar_ref]. rewrite us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_LENEXT_leave : forall s c r w1,
  is_extra s <> 0 -> NEEDBITS (is_extra s) (mkW s c r) = ALeave w1 -> arm_LENEXT ivar_ref (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 H0 HN. unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. reflexivity.
Qed.

Definition lenext_facts (v : icv) (s : inflate_state) (c : icall) : Prop :=
  3 <= is_length s /\ 0 <= is_extra s <= 15 /\ is_length s + Z.shiftl 1 (is_extra s) - 1 <= 258 /\ dist_facts v s c.

Lemma sinv_lenext : forall s, sinv s -> is_mode s = LENEXT ->
  3 <= is_length s /\ 0 <= is_extra s <= 15 /\ is_length s + Z.shiftl 1 (is_extra s) - 1 <= 258.
Proof. intros s H Hm. destruct H as (_ & _ & _ & _ & _ & _ & Q & _). exact (Q Hm). Qed.

Lemma lenext_facts_of_pinv : forall v s c r,
  is_mode s = LENEXT -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> lenext_facts v s c.
Proof.
  intros v s c r Hmode HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_lenext s PS Hmode) as (Hlen & Hex & Hle). pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof (sr_back s SR) as Hback.
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  pose proof (dist_tab s PS ltac:(rewrite Hmode; reflexivity)) as DT.
  pose proof (sr_dofs s SR) as Hofs.
  unfold lenext_facts, dist_facts. rewrite Z.shiftl_1_l in Hle.
  assert (Hlen' : 3 <= is_length s <= 258) by (pose proof (Z.pow_pos_nonneg 2 (is_extra s) ltac:(lia) ltac:(lia)); lia).
  rewrite Z.shiftl_1_l. repeat (split; [assumption|]). exact Hofs.
Qed.

Lemma dist_facts_lx : forall v s c L bk W,
  dist_facts v s c -> 3 <= L <= 258 ->
  dist_facts v (iset_mode (iset_was (iset_back (iset_length s L) (swrap32 bk)) W) DIST) c.
Proof.
  intros v s c L bk W HD HL. destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & DT & Hofs).
  unfold dist_facts. destruct s; cbn in *. pose proof (swrap32_range bk). repeat (split; [assumption || exact DT|]). exact Hofs.
Qed.
Lemma dist_facts_lz : forall v s c W,
  dist_facts v s c -> dist_facts v (iset_mode (iset_was s W) DIST) c.
Proof.
  intros v s c W HD. destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & DT & Hofs).
  unfold dist_facts. destruct s; cbn in *. repeat (split; [assumption || exact DT|]). exact Hofs.
Qed.


Section LenextBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lf HD :=
    destruct HD as (Hlen3 & Hex & Hle & HDD); pose proof HDD as HDD0;
    destruct HDD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Lemma lenext_body : forall s c r1 R M,
    is_mode s = LENEXT -> lenext_facts v s c -> RINV (cv_NI v) (cv_NO v) r1 -> is_extra s <> 0 -> is_extra s <= ir_bits r1 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> NJE v (is_extra s) c r1 R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fd9c) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M (arm_DIST ivar_ref (mkW (lx_s s r1) c (lx_r s r1))) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode HD RI Hex0 Hbx HM HRC HX HJ. open_lf HD.
    destruct HJ as (HF & G9 & G11 & G22 & G13 & G24 & G25). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G24 as P24. pose proof G25 as P25.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_length _ _ _ _ Msc) as C92. pose proof (is6_back _ _ _ _ Msc) as C7148.
    assert (Hbk : 0 <= is_back s <= 64) by (destruct Xbk as [XL _]; exact (XL Hmode)).
    assert (Hbm : is_back s mod 2 ^ 32 = is_back s) by (apply Z.mod_small; lia).
    assert (P2e : 0 < 2 ^ is_extra s <= 2 ^ 15) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.shiftl_1_l in Hle.
    set (ex := is_extra s) in *.
    arm_symexP (@nil (Z * expr)) ilS 24%nat [true] [RVal (EVar 46%nat); RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 47%nat)]
      [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
       (11, EVar 45%nat); (25, EVar 40%nat); (13, EVar 41%nat); (23, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))]
      [(45%nat, 16); (46%nat, 512); (47%nat, 2 ^ 32)] v r1
      [ex; is_length s; is_back s mod 2 ^ 32] NoVals F0
      (mkst R (Z_to_bv 64 0x1fd9c) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLB" G end.
    rewrite (mask_exec (ir_hold r1) ex Rhold64 ltac:(lia)) in Hms1.
    rewrite ?Hbm, ?(szwrap32_small (is_back s)) in Hms1 by (clear - Hbk; lia).
    rewrite <- (le4_swrap32 (is_back s + ex)) in Hms1.
    set (v1 := ir_hold r1 mod 2 ^ ex) in *.
    assert (Hv1 : 0 <= v1 < 2 ^ ex) by (subst v1; apply Z.mod_pos_bound; lia).
    set (L' := is_length s + v1) in *.
    rewrite (szwrap32_small L') in Hms1 by (subst L'; clear - Hlen Hv1 P2e; lia).
    set (M1 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 L')) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (is_back s + ex)))) in *.
    set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16202)) in *.
    set (M4 := wbytes M3 (zw (cv_S v + 7168)) (Z_to_le_bytes 4 L')) in *.
    set (s1 := iset_length s L'). set (s2 := iset_back s1 (swrap32 (is_back s + ex))). set (s3 := iset_mode s2 DIST). set (s4 := iset_was s3 L').
    assert (Es4 : lx_s s r1 = s4) by (subst s4 s3 s2 s1 L' v1 ex; unfold lx_s, lx_len; destruct s; reflexivity).
    assert (HM1 : LMEM v (mkW s1 c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M 108 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_length M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW s2 c r1) M2).
    { apply (LMEM_store_scalar v C s1 c r1 _ M1 7164 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_back M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW s3 c r1) M3).
    { apply (LMEM_store_scalar v C s2 c r1 _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M2 (cv_S v) _ s2 DIST (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM4' : LMEM v (mkW s4 c r1) M4).
    { apply (LMEM_store_scalar v C s3 c r1 _ M3 7168 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_was M3 (cv_S v) _ s3 _ (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    rewrite <- Es4 in HM4'.
    assert (HM4 : LMEM v (mkW (lx_s s r1) c (lx_r s r1)) M4) by (apply (LMEM_regs v (lx_s s r1) c r1 c (lx_r s r1) M4 HM4'); reflexivity).
    assert (HRC4 : RETC v (mkW (lx_s s r1) c (lx_r s r1)) M4).
    { subst M4 M3 M2 M1. apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]. }
    assert (HX4 : LX v (mkW (lx_s s r1) c (lx_r s r1))).
    { rewrite Es4. apply (LX_step0 v s c r1 s4 c (lx_r s r1) HX NH NB); subst s4 s3 s2 s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg |].
      cbn [is_mode is_back iset_was iset_mode iset_back iset_length]. rewrite swrap32_smallv by (clear - Hbk Hex; lia).
      unfold bk_ok. cbv [LENEXT DIST]. split; intros HE; clear - Hbk Hex HE; lia. }
    pose proof (hold_drop (ir_hold r1) (ir_bits r1) ex ltac:(lia) Rhold) as HD'.
    assert (RI4 : RINV (cv_NI v) (cv_NO v) (lx_r s r1)).
    { unfold lx_r, RINV in *. cbn. clear - RI HD' Hbx Hex Hex0. subst ex. lia. }
    symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18.
    assert (HF4 : LFIXc v R1) by (lfixc_close Hfr1 HR1).
    assert (HV4 : LVARS v (mkW (lx_s s r1) c (lx_r s r1)) R1).
    { unfold LVARS; cbn [w_r]. unfold lx_r. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
      regs_via Hfr1; first [rewrite Q22; rewrite zalu_srl_small by (clear - Rhold64 Hex; lia); reflexivity
                           | rewrite Q18; rewrite szwrap32_small by (clear - Rbits Hbx Hex; lia); reflexivity
                           | match goal with |- ?G => idtac "LV LEFT" G end]. }
    assert (HD4 : dist_facts v (lx_s s r1) c).
    { unfold lx_s. apply dist_facts_lx; [exact HDD0|]. unfold lx_len. subst ex v1. clear - Hlen3 Hle Hv1. lia. }
    destruct (dist_core v C (lx_s s r1) c (lx_r s r1) R1 M4 ltac:(rewrite Es4; reflexivity) HD4 RI4 HM4 HRC4 HX4 HF4 HV4)
      as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M4 M3 M2 M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r1) (mkW (lx_s s r1) c (lx_r s r1)) M M4); [rewrite Es4; subst s4 s3 s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. unfold lx_r. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
    do 4 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.

  Lemma lenext_ztail : forall s c r R M,
    is_mode s = LENEXT -> lenext_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIXc v R ->
    getr R 9 = zw (cv_P0 v + ir_put r) -> getr R 25 = zw (ir_hold r) -> getr R 19 = zw (ir_bits r) ->
    getr R 12 = zw (ir_have r) -> getr R 14 = zw (cv_I0 v + ir_next r) ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20cd4) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_DIST ivar_ref (mkW (iset_mode (iset_was s (is_length s)) DIST) c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI HM HRC HX HF P9 P22 P18 P12 P14. open_lf HD. open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_length _ _ _ _ Msc) as C92.
    arm_symexP (@nil (Z * expr)) ilS 9%nat (@nil bool) [RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 45%nat)]
      [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
       (25, EVar 40%nat); (19, EVar 41%nat); (12, EVar 36%nat); (14, EAdd (EVar 43%nat) (EVar 44%nat))]
      [(45%nat, 512)] v r [is_length s] NoVals F0
      (mkst R (Z_to_bv 64 0x20cd4) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLZ" G end.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16202)) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 7168)) (Z_to_le_bytes 4 (is_length s))) in *.
    set (s1 := iset_mode s DIST). set (s2 := iset_was s1 (is_length s)).
    assert (Es2 : iset_mode (iset_was s (is_length s)) DIST = s2) by (subst s2 s1; destruct s; reflexivity).
    rewrite Es2.
    assert (HM1 : LMEM v (mkW s1 c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s DIST Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW s2 c r) M2).
    { apply (LMEM_store_scalar v C s1 c r _ M1 7168 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_was M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC2 : RETC v (mkW s2 c r) M2) by (subst M2 M1; retc_tower C HRC).
    assert (HX2 : LX v (mkW s2 c r)).
    { apply (LX_step0 v s c r s2 c r HX NH NB); subst s2 s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side]. }
    assert (HF2 : LFIXc v R1) by (lfixc_close Hfr1 HR1).
    symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (26%bv : reg) as Q25.
    assert (HV2 : LVARS v (mkW s2 c r) R1) by (unfold LVARS; cbn [w_r]; regs_via Hfr1; first [exact Q24 | exact Q25]).
    assert (HD2 : dist_facts v s2 c).
    { subst s2 s1. replace (iset_was (iset_mode s DIST) (is_length s)) with (iset_mode (iset_was s (is_length s)) DIST) by (destruct s; reflexivity).
      apply dist_facts_lz. exact HDD0. }
    destruct (dist_core v C s2 c r R1 M2 ltac:(subst s2 s1; destruct s; reflexivity) HD2 RI0 HM2 HRC2 HX2 HF2 HV2)
      as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r) (mkW s2 c r) M M2); [subst s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. subst M2 M1.
    do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.
End LenextBody.
End FXG.
End InflA_Lenext2.

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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflDec6 InflA_Dist3 InflA_Dist7. Import InflA_Lenext1. Import InflA_Lenext2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilXLA : cfg := CFG [] [] arm_rets (0x1f16c :: 0x1fd9c :: arm_stops) [].

Section LenextCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lf HD :=
    destruct HD as (Hlen3 & Hex & Hle & HDD); pose proof HDD as HDD0;
    destruct HDD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition nz_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (19, EVar 41%nat); (11, EVar 45%nat); (12, EVar 36%nat); (14, EAdd (EVar 43%nat) (EVar 44%nat))].

  Lemma lenext_nz : forall s c r R M,
    is_mode s = LENEXT -> lenext_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_extra s <> 0 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIXc v R ->
    getr R 9 = zw (cv_P0 v + ir_put r) -> getr R 25 = zw (ir_hold r) -> getr R 19 = zw (ir_bits r) ->
    getr R 11 = zw (is_extra s) -> getr R 12 = zw (ir_have r) -> getr R 14 = zw (cv_I0 v + ir_next r) ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f148) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_LENEXT ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI E0 HM HRC HX HF P9 P22 P18 P11 P12 P14. pose proof HD as HD0. open_lf HD.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fixc HF. pose proof RI as RI0. open_rinv RI. pose proof CI as CI0'. open_cinv CI.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8.
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    rewrite Z.shiftl_1_l in Hle.
    assert (Hex1 : 1 <= is_extra s <= 15) by (clear - Hex E0; lia).
    assert (P2e : 0 < 2 ^ is_extra s) by (apply Z.pow_pos_nonneg; lia).
    assert (Hl32 : is_length s + 2 ^ is_extra s <= 2 ^ 32) by (clear - Hle Hlen3; lia).
    assert (Hh31 : 0 <= ir_have r < 2 ^ 31) by (clear - Rnh Rnx0 Rhv0 CI0; lia).
    destruct (Z_le_gt_dec (is_extra s) (ir_bits r)) as [GE|LT].
    +
      assert (HN : NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
      rewrite (arm_LENEXT_run s c r c r ltac:(clear - Hex1; lia) ltac:(lia) Hl32 HN ltac:(clear - GE Rbits; lia) Rhold).
      arm_symexP (@nil (Z * expr)) ilXLA 6%nat [true] (@nil (option expr)) nz_pins [(45%nat, 16)] v r [is_extra s] NoVals F0
        (mkst R (Z_to_bv 64 0x1f148) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTNZ1" G end.
      assert (HJ : NJE v (is_extra s) c r R1).
      { symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (26%bv : reg) as Q25.
        unfold NJE. split; [lfixc_close Hfr1 HR1|]. repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | exact Q13 | exact Q24 | exact Q25 ]. }
      destruct (lenext_body v C s c r R1 M Hmode HD0 RI0 E0 GE HM HRC HX HJ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
    +
      arm_symexP (@nil (Z * expr)) ilXLA 12%nat [false] (@nil (option expr)) nz_pins [(45%nat, 16)] v r [is_extra s] NoVals F0
        (mkst R (Z_to_bv 64 0x1f148) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTNZ2" G end.
      assert (HJ : NJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s) c r R1).
      { symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (23%bv : reg) as Q24.
        symex_reg HR1 (5%bv : reg) as Q5. symex_reg HR1 (17%bv : reg) as Q17.
        unfold NJS, NK. split; [split; [lfixc_close Hfr1 HR1|]|]; repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | rewrite Q16; rewrite ?Z.mod_small by (clear - Hex1; lia); reflexivity
                | rewrite Q15; rewrite ?Z.mod_small by (clear - Rbits; lia); reflexivity
                | exact Q13 | exact Q24 | exact Q5 | exact Q17 | clear; lia | clear - Rbits; lia
                | match goal with |- ?G => idtac "NJS LEFT" G end ]. }
      pose proof (need_loop v (is_extra s) 0x1f16c 0x1fd9c (NJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s)) (NJE v (is_extra s)) C ltac:(lia)
                    (lenext_step_H v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                    (lenext_step_E v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                    (lenext_dry v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                    8%nat s c r R1 M HM HRC HJ RI0 CI0' ltac:(lia) ltac:(cbn; clear - LT Rbits Hex1; lia)) as NL.
      change (NEEDBITS_k 8 (is_extra s)) with (NEEDBITS (is_extra s)) in NL.
      destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct NL].
      * destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        pose proof RI1 as X. unfold RINV in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb1 & Rh1).
        rewrite (arm_LENEXT_run s c r c r1 ltac:(clear - Hex1; lia) ltac:(lia) Hl32 EN ltac:(clear - Hb1 Rb1; lia) Rh1).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
        destruct (lenext_body v C s c r1 R2 M Hmode HD0 RI1 E0 ltac:(clear - Hb1; lia) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      * destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        rewrite (arm_LENEXT_leave s c r _ E0 EN).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
        cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.
End LenextCore.

Theorem arm_LENEXT_sim : arm_stmt LENEXT.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LENEXT) with (arm_LENEXT ivar_ref).
  pose proof (lenext_facts_of_pinv v s c r Hmode HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  pose proof HM as HM0. pose proof HX as HX0. pose proof HF as HF0. pose proof HV as HV0.
  arm_begin C HM HRC HX HF HV HP.
  pose proof (is6_extra _ _ _ _ Msc) as C100.
  pose proof HD as HD'. destruct HD' as (_ & Hex & _).
  change (arm6_pc LENEXT) with 0x1f134.
  destruct (Z.eq_dec (is_extra s) 0) as [E0|E0].
  - rewrite (arm_LENEXT_zero s c r E0).
    arm_symex ilS 6%nat [false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 16)] v r [is_extra s] NoVals F0
      (mkst R (Z_to_bv 64 0x1f134) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
    destruct (lenext_ztail v C s c r R1 M Hmode HD RI HM0 HRC HX0 ltac:(lfixc_close Hfr1 HR1)
                ltac:(rewrite (Hfr1 (9%bv : reg) eq_refl); exact G9) ltac:(rewrite (Hfr1 (25%bv : reg) eq_refl); exact G22)
                ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact G18) G12 G14) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  - arm_symex ilS 6%nat [true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 16)] v r [is_extra s] NoVals F0
      (mkst R (Z_to_bv 64 0x1f134) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    symex_reg HR1 (11%bv : reg) as G11'. symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
    destruct (lenext_nz v C s c r R1 M Hmode HD RI E0 HM0 HRC HX0 ltac:(lfixc_close Hfr1 HR1)
                ltac:(rewrite (Hfr1 (9%bv : reg) eq_refl); exact G9) ltac:(rewrite (Hfr1 (25%bv : reg) eq_refl); exact G22)
                ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact G18) G11' G12 G14) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
Qed.
End FXG.

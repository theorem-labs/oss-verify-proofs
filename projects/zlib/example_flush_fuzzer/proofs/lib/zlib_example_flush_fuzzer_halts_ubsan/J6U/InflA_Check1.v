(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilC : cfg := ilSx [0x1f3dc; 0x1fe8c] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section CheckLoop.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition LFIXa (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 1 = zw 16209 /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
  Lemma LFIX_LFIXa : forall R, LFIX v R -> LFIXa R.
  Proof. intros R HF. unfold LFIX in HF. destruct HF as (G2 & G27 & G13 & G8 & G11 & G1 & G3 & G4). unfold LFIXa. repeat split; assumption. Qed.
  Ltac open_fixa HF :=
    let X := fresh in pose proof HF as X; unfold LFIXa, INF_FRAME in X;
    destruct X as (G2 & G27 & G8 & G1 & G3 & G4).

  Definition CJS (wv h0 n0 b0 : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXa R /\ getr R 13 = zw (cv_ZP v) /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 14 = zw wv
    /\ getr R 27 = zw (ir_have r) /\ getr R 16 = zw (cv_I0 v + ir_next r) /\ getr R 11 = zw (cv_I0 v + ir_next r)
    /\ getr R 15 = zw (ir_bits r) /\ getr R 21 = zw (ir_bits r)
    /\ getr R 23 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 19 = zw b0
    /\ ir_have r + ir_next r = h0 + n0 /\ ir_bits r = b0 + 8 * (ir_next r - n0) /\ 0 <= h0 < 2 ^ 31 /\ 0 <= b0 /\ 0 <= n0.
  Definition CJE (wv : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXa R /\ getr R 13 = zw (cv_ZP v) /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 14 = zw wv
    /\ getr R 20 = zw (cv_I0 v + ir_next r) /\ getr R 27 = zw (ir_have r) /\ getr R 21 = zw (ir_bits r).

  Ltac open_cjs HJ :=
    let X := fresh in pose proof HJ as X; unfold CJS in X;
    destruct X as (HF & G13 & G9 & G22 & G14 & G26 & G16 & G11 & G15 & G20 & G24 & G25 & G18 & E1 & E2 & Hh0 & Hb0 & Hn00); open_fixa HF.

  Definition cjs_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (13, EVar 34%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (27, EVar 36%nat); (16, EAdd (EVar 43%nat) (EVar 44%nat)); (11, EAdd (EVar 43%nat) (EVar 44%nat)); (15, EVar 41%nat); (21, EVar 41%nat);
     (23, EVar 45%nat); (26, EAdd (EVar 43%nat) (EVar 46%nat)); (19, EVar 47%nat)].

  Ltac lfixa_close Hfr HR :=
    unfold LFIXa, INF_FRAME;
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with |- getr _ ?n = _ =>
      first [ rewrite (Hfr n eq_refl); assumption
            | let G := fresh "G" in symex_reg HR n as G; rewrite G; first [ reflexivity | assumption | apply zw_neg_mod | f_equal; lia ]
            | match goal with |- ?G => idtac "LFIXa LEFT" G end ]
    end.

  Ltac cjs_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00 :=
    let Q26 := fresh in let Q22 := fresh in let Q15 := fresh in let Q20 := fresh in let Q16 := fresh in let Q11 := fresh in let Q19 := fresh in
    symex_reg HR (27%bv : reg) as Q26; symex_reg HR (25%bv : reg) as Q22; symex_reg HR (15%bv : reg) as Q15; symex_reg HR (21%bv : reg) as Q20;
    symex_reg HR (16%bv : reg) as Q16; symex_reg HR (11%bv : reg) as Q11; symex_reg HR (20%bv : reg) as Q19;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold CJS, CJE, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- LFIXa _ => lfixa_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q26; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q22; f_equal; lia
          | rewrite Q15; f_equal; lia
          | rewrite Q20; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite Q16; f_equal; lia
          | rewrite Q11; f_equal; lia
          | rewrite Q19; f_equal; lia
          | clear - E1 E2 Hh0 Hb0 Hn00; lia
          | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR n as G; rewrite G; first [ reflexivity | assumption | f_equal; lia ] end
          | match goal with |- ?G => idtac "CJS LEFT" G end ].

  Lemma check_step_H : forall wv h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> CJS wv h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 32 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f3dc) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f3dc) M s6u_rom)
               /\ CJS wv h0 n0 b0 c (pull1 c r) R1.
  Proof.
    intros wv h0 n0 b0 s c r R M HM HJ RI CI Hb Hh. open_cjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP cjs_pins ilC 22%nat [true; true; true] (@nil (option expr)) (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1f3dc) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    cjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma check_step_E : forall wv h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> CJS wv h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> 32 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f3dc) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fe8c) M s6u_rom)
               /\ CJE wv c (pull1 c r) R1.
  Proof.
    intros wv h0 n0 b0 s c r R M HM HJ RI CI Hb Hb8 Hh. open_cjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP cjs_pins ilC 22%nat [true; true; false] (@nil (option expr)) (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1f3dc) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    cjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma check_dry : forall wv h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> CJS wv h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f3dc) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros wv h0 n0 b0 s c r R M HM HRC HJ RI CI Hb Hh. open_cjs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP cjs_pins ilC 16%nat [false] [RVal (EVar 48%nat); RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64)] v r
      [h0; n0; b0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f3dc) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. repeat match goal with |- _ /\ _ => split end;
      first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
            | rewrite Q26; apply zw_neg_mod
            | rewrite Q24; f_equal; clear - Hh; lia
            | rewrite Q18; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | rewrite Q25; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | lazymatch goal with |- getr _ ?n = _ => let G := fresh in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption] end
            | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.

  Lemma check_A : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) -> LMEM v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    exists R1,
      if 32 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1f3b8) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fe8c) M s6u_rom) /\ CJE (is_wrap s) c r R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1f3b8) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f3dc) M s6u_rom) /\ CJS (is_wrap s) (ir_have r) (ir_next r) (ir_bits r) c r R1.
  Proof.
    intros s c r R M Hw HM HF HV RI.
    open_ictx C. open_lmem HM. open_fix HF. open_vars HV. open_rinv RI. unfold mapped in *.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    pose proof (is6_wrap _ _ _ _ Msc) as C16. pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_ne0 _ Hw) as Hw0.
    pose proof (LFIX_LFIXa R HF) as HFa.
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    - arm_symex ilC 10%nat [false; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f3b8) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (14%bv : reg) as G14'. symex_reg HR1 (20%bv : reg) as G19'. symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (21%bv : reg) as G20'.
      unfold CJE. split; [lfixa_close Hfr HR1|]. regs_via Hfr; first [exact G14' | exact G19' | exact G26' | exact G20' | idtac].
    - arm_symex ilC 12%nat [false; false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f3b8) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (14%bv : reg) as G14'. symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (16%bv : reg) as G16'. symex_reg HR1 (11%bv : reg) as G11'.
      symex_reg HR1 (15%bv : reg) as G15'. symex_reg HR1 (21%bv : reg) as G20'.
      unfold CJS. split; [lfixa_close Hfr HR1|]. regs_via Hfr; first [exact G14' | exact G26' | exact G16' | exact G11' | exact G15' | exact G20' | idtac].
      + clear; lia.
      + clear; lia.
      + clear - Rhv0; lia.
      + clear - Rhv0 Rnh Rnx0 CI0; lia.
      + clear - Rbits; lia.
      + clear - Rnx0; lia.
  Qed.

  Lemma check_need : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    match NEEDBITS 32 (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f3b8) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fe8c) M s6u_rom)
        /\ CJE (is_wrap s) c r1 R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1 /\ 32 <= ir_bits r1
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f3b8) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
        /\ LREG_leave v (mkW s c r1) R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1
    | ARet _ _ => False
    end.
  Proof.
    intros s c r R M Hw HM HRC HF HV RI CI.
    pose proof RI as RI'. open_rinv RI'.
    destruct (check_A s c r R M Hw HM HF HV RI) as (R1 & HA).
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    - destruct HA as (Hms1 & CJE1). unfold NEEDBITS. rewrite NEEDBITS_k_done by (cbn; exact GE).
      exists r, R1. split; [reflexivity|]. split; [exact Hms1|]. split; [exact CJE1|]. split; [exact RI|]. split; [apply same5_refl | exact GE].
    - destruct HA as (Hms1 & CJS1).
      pose proof (need_loop v 32 0x1f3dc 0x1fe8c (CJS (is_wrap s) (ir_have r) (ir_next r) (ir_bits r)) (CJE (is_wrap s)) C ltac:(lia)
                    (check_step_H _ _ _ _) (check_step_E _ _ _ _) (check_dry _ _ _ _)
                    8%nat s c r R1 M HM HRC CJS1 RI CI LT ltac:(cbn; clear - LT Rbits; lia)) as NL.
      change (NEEDBITS_k 8 32) with (NEEDBITS 32) in NL.
      destruct (NEEDBITS 32 (mkW s c r)) as [[] w1 | w1 | rc w1]; [| | exact NL].
      + destruct NL as (r1 & R2 & E & Hms2 & CJE & RI1 & S5 & Hb1 & _). exists r1, R2.
        split; [exact E|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact CJE|]. split; [exact RI1|]. split; [exact S5 | clear - Hb1; lia].
      + destruct NL as (r1 & R2 & E & Hms2 & HL & RI1 & S5 & _). exists r1, R2.
        split; [exact E|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HL|]. split; [exact RI1 | exact S5].
  Qed.
End CheckLoop.
End FXG.

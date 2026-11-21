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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilC : cfg := ilSx [0x1d32c; 0x1dafc] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section CheckLoop.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition CJS (wv : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ LVR v r R /\ getr R 14 = zw (ir_bits r) /\ getr R 13 = zw wv /\ getr R 27 = zw (cv_I0 v + ir_next r).
  Definition CJE (wv : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ LVR v r R /\ getr R 13 = zw wv /\ getr R 27 = zw (cv_I0 v + ir_next r) /\ getr R 26 = zw (cv_I0 v + ir_next r).

  Ltac open_cjs HJ :=
    let X := fresh in pose proof HJ as X; unfold CJS, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G14 & G13 & G26); open_fix HF.

  Ltac cjs_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let G9 := fresh in let G22 := fresh in let G23 := fresh in let G13 := fresh in let G26 := fresh in let G27 := fresh in
    symex_reg HR (18%bv : reg) as G9; symex_reg HR (23%bv : reg) as G22; symex_reg HR (24%bv : reg) as G23;
    symex_reg HR (14%bv : reg) as G13; symex_reg HR (27%bv : reg) as G26; symex_reg HR (26%bv : reg) as G27;
    cbn [famA] in G22; rewrite bmod_get in G22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in G22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold CJS, CJE, LVR, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ apply (LFIX_frame v _ _ _ HF Hfr); reflexivity
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G9; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite G22; f_equal; lia
          | rewrite G23; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite G13; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite G26; f_equal; lia
          | rewrite G27; f_equal; lia
          | match goal with |- ?G => idtac "CJS LEFT" G end ].

  Lemma check_step_H : forall wv s c r R M,
    LMEM v (mkW s c r) M -> CJS wv c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 32 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d32c) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d32c) M s6_rom)
               /\ CJS wv c (pull1 c r) R1.
  Proof.
    intros wv s c r R M HM HJ RI CI Hb Hh. open_cjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symex ilC 14%nat [true; true] (@nil (option expr)) [(14, EVar 41%nat)] (@nil (nat * Z)) v r (@nil Z) NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1d32c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    cjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma check_step_E : forall wv s c r R M,
    LMEM v (mkW s c r) M -> CJS wv c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> 32 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d32c) M s6_rom) (mkst R1 (Z_to_bv 64 0x1dafc) M s6_rom)
               /\ CJE wv c (pull1 c r) R1.
  Proof.
    intros wv s c r R M HM HJ RI CI Hb Hb8 Hh. open_cjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symex ilC 14%nat [true; false] (@nil (option expr)) [(14, EVar 41%nat)] (@nil (nat * Z)) v r (@nil Z) NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1d32c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    cjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma check_dry : forall wv s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> CJS wv c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d32c) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros wv s c r R M HM HRC HJ RI CI Hb Hh. open_cjs HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    arm_symex ilC 8%nat [false] [RVal (EVar 45%nat)] [(14, EVar 41%nat)] [(45%nat, 2 ^ 64)] v r
      [ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d32c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr; first [exact G26 | rewrite G8'; apply zw_neg_mod].
  Qed.

  Lemma check_A : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) -> LMEM v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    exists R1,
      if 32 <=? ir_bits r
      then msteps s6_segs (mkst R (Z_to_bv 64 0x1d318) M s6_rom) (mkst R1 (Z_to_bv 64 0x1dafc) M s6_rom) /\ CJE (is_wrap s) c r R1
      else msteps s6_segs (mkst R (Z_to_bv 64 0x1d318) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d32c) M s6_rom) /\ CJS (is_wrap s) c r R1.
  Proof.
    intros s c r R M Hw HM HF HV RI.
    open_ictx C. open_lmem HM. open_fix HF. open_vars HV. open_rinv RI. unfold mapped in *.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    pose proof (is6_wrap _ _ _ _ Msc) as C16. pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_ne0 _ Hw) as Hw0.
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    - arm_symex ilC 8%nat [false; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d318) M s6_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (13%bv : reg) as G12'. symex_reg HR1 (26%bv : reg) as G27'.
      unfold CJE, LVR. split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr; first [exact G12' | exact G27'].
    - arm_symex ilC 8%nat [false; false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d318) M s6_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (13%bv : reg) as G12'. symex_reg HR1 (14%bv : reg) as G13'.
      unfold CJS, LVR. split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr; first [exact G13' | exact G12'].
  Qed.

  Lemma check_need : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    match NEEDBITS 32 (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 0x1d318) M s6_rom) (mkst R1 (Z_to_bv 64 0x1dafc) M s6_rom)
        /\ CJE (is_wrap s) c r1 R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1 /\ 32 <= ir_bits r1
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 0x1d318) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
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
      pose proof (need_loop v 32 0x1d32c 0x1dafc (CJS (is_wrap s)) (CJE (is_wrap s)) C ltac:(lia) (check_step_H (is_wrap s)) (check_step_E (is_wrap s)) (check_dry (is_wrap s))
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

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition pull1 (c : icall) (r : iregs) : iregs :=
  mkIR (ir_next r + 1) (ir_have r - 1) (ir_put r) (ir_left r)
       (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (ir_bits r + 8)
       (ir_in r) (ir_out r) (ir_ret r).

Lemma pull1_RINV : forall NI NO (s : inflate_state) c r,
  0 <= NI < 2 ^ 32 -> 0 <= NO < 2 ^ 32 ->
  RINV NI NO r -> CINV NI NO c -> ir_bits r + 8 < 64 -> 0 < ir_have r ->
  pullr c r = pull1 c r /\ RINV NI NO (pull1 c r).
Proof.
  intros NI NO s c r HNI HNO HR HC Hb Hh.
  pose proof HC as (Cil & _ & _ & _ & _ & _ & _ & _ & Cinb & _).
  pose proof (PULLBYTE_run NI NO HNI HNO s c r HR Hb Cil Cinb) as P.
  rewrite PULLBYTE_eq in P. replace (ir_have r =? 0) with false in P by (symmetry; apply Z.eqb_neq; lia).
  destruct P as (r' & E & HR' & S5 & _ & B1 & H1 & N1 & _ & Hh1).
  assert (E' : pullr c r = r') by congruence.
  assert (E2 : r' = pull1 c r).
  { destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5). unfold pull1. rewrite <- Q1, <- Q2, <- Q3, <- Q4, <- Q5, <- B1, <- H1, <- N1, <- Hh1. destruct r'; reflexivity. }
  rewrite E', E2. split; [reflexivity|]. rewrite <- E2. exact HR'.
Qed.

Definition LVR (v : icv) (r : iregs) (R : bvmap 5 word) : Prop :=
  getr R 18 = zw (ir_have r) /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
  /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r).

Section NeedLoop.
  Variable v : icv.
  Variables (n pcH pcE : Z).
  Variables (JS JE : icall -> iregs -> bvmap 5 word -> Prop).
  Local Abbreviation NI := (cv_NI v). Local Abbreviation NO := (cv_NO v).

  Hypothesis C : ictx v.
  Hypothesis Hn : 0 < n <= 56.
  Hypothesis STEP_H : forall s c r R M,
    LMEM v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pcH) M s6_rom)
               /\ JS c (pull1 c r) R1.
  Hypothesis STEP_E : forall s c r R M,
    LMEM v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pcE) M s6_rom)
               /\ JE c (pull1 c r) R1.
  Hypothesis DRY : forall s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.

  Lemma need_loop : forall k s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> n <= ir_bits r + 8 * Z.of_nat k ->
    match NEEDBITS_k k n (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pcE) M s6_rom)
        /\ JE c r1 R1 /\ RINV NI NO r1 /\ same5 r r1 /\ n <= ir_bits r1 < n + 8
        /\ LMEM v (mkW s c r1) M /\ RETC v (mkW s c r1) M
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
        /\ LREG_leave v (mkW s c r1) R1 /\ RINV NI NO r1 /\ same5 r r1 /\ ir_have r1 = 0 /\ ir_bits r1 < n
        /\ LMEM v (mkW s c r1) M /\ RETC v (mkW s c r1) M
    | ARet _ _ => False
    end.
  Proof.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    induction k as [|k IH]; intros s c r R M HM HRC HJ HR HC Hb Hk.
    { exfalso. cbn in Hk. lia. }
    rewrite NEEDBITS_k_S. replace (ir_bits r <? n) with true by (symmetry; apply Z.ltb_lt; exact Hb).
    pose proof HR as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11').
    destruct (Z.eqb_spec (ir_have r) 0) as [Hz|Hz].
    - destruct (DRY s c r R M HM HRC HJ HR HC Hb Hz) as (R1 & Hms & HL).
      exists r, R1. split; [reflexivity|]. split; [exact Hms|]. split; [exact HL|]. split; [exact HR|].
      split; [apply same5_refl|]. split; [exact Hz|]. split; [exact Hb|]. split; [exact HM | exact HRC].
    - destruct (pull1_RINV NI NO s c r ltac:(lia) ltac:(lia) HR HC ltac:(lia) ltac:(lia)) as [Ep HR1].
      rewrite Ep.
      assert (HM1 : LMEM v (mkW s c (pull1 c r)) M) by (apply (LMEM_regs v s c r c (pull1 c r) M HM); reflexivity).
      assert (HRC1 : RETC v (mkW s c (pull1 c r)) M) by (eapply RETC_regs; [exact HRC | reflexivity]).
      assert (S5 : same5 r (pull1 c r)) by (repeat split; reflexivity).
      destruct (Z_lt_le_dec (ir_bits r + 8) n) as [LT|GE].
      + destruct (STEP_H s c r R M HM HJ HR HC LT ltac:(lia)) as (R1 & Hms1 & HJ1).
        specialize (IH s c (pull1 c r) R1 M HM1 HRC1 HJ1 HR1 HC ltac:(cbn; lia) ltac:(cbn; cbn in Hk; lia)).
        destruct (NEEDBITS_k k n (mkW s c (pull1 c r))) as [[] w2 | w2 | rc w2]; [| | exact IH].
        * destruct IH as (r2 & R2 & -> & Hms2 & HJ2 & HR2 & S2 & B2 & HM2 & HRC2). exists r2, R2.
          split; [reflexivity|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HJ2|]. split; [exact HR2|].
          split; [exact (same5_trans _ _ _ S5 S2)|]. split; [exact B2|]. split; [exact HM2 | exact HRC2].
        * destruct IH as (r2 & R2 & -> & Hms2 & HL2 & HR2 & S2 & Z2 & B2 & HM2 & HRC2). exists r2, R2.
          split; [reflexivity|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HL2|]. split; [exact HR2|].
          split; [exact (same5_trans _ _ _ S5 S2)|]. split; [exact Z2|]. split; [exact B2|]. split; [exact HM2 | exact HRC2].
      + destruct (STEP_E s c r R M HM HJ HR HC Hb GE ltac:(lia)) as (R1 & Hms1 & HJ1).
        rewrite NEEDBITS_k_done by (cbn; lia).
        exists (pull1 c r), R1. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HJ1|]. split; [exact HR1|].
        split; [exact S5|]. split; [cbn; lia|]. split; [exact HM1 | exact HRC1].
  Qed.
End NeedLoop.
End FXG.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundAlu StepSoundMem PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepA PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module VdStep.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Ltac inv_of Hof :=
  repeat match type of Hof with
  | context [match r5_of_reg ?r with _ => _ end] =>
      let d := fresh "d" in let Hd := fresh "Hd" in
      destruct (r5_of_reg r) as [d|] eqn:Hd; [apply reg_of_r5_of_reg in Hd; subst r | discriminate Hof]
  | context [match ?x with _ => _ end] => is_var x; destruct x
  end;
  first [discriminate Hof | injection Hof; intros; subst | idtac].

Lemma m_branch : forall E st ms model (w : bv 32) (i : instr) c rs1 rs2 off npci,
  st_ok segs OPS E st ms model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  of_instr i = Some (IBranch c rs1 rs2 off) ->
  (if branch_taken c (den E (getr st rs1)) (den E (getr st rs2)) then pc_add (s_pc st) off = Some npci else npci = pc4 st) ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok segs OPS E (setpc st npci) ms' model.
Proof.
  intros E st ms model w i c rs1 rs2 off npci HS Hpc Hf He Hd Hof HN.
  rewrite (step_exec segs ms w i Hf He Hd).
  destruct i; cbn [of_instr] in Hof; try discriminate Hof; inv_of Hof.
  cbn [Sem.exec].
  rewrite <- (StepA.getr_den segs OPS E st ms model _ HS), <- (StepA.getr_den segs OPS E st ms model _ HS).
  destruct (branch_taken _ _ _).
  - destruct (StepA.case_pc_gen segs OPS E st ms model (Sem.c_pc (core_of ms) + sext 64 imm)%bv npci HS) as (c' & m' & IE & HS').
    { rewrite (pc_add_ok _ _ _ HN), wbv_w_of_imm, (StepA.pc_core segs OPS E st ms model HS). reflexivity. }
    rewrite IE. eexists. split; [reflexivity| exact HS'].
  - subst npci. destruct (StepA.case_pc4 segs OPS E st ms model HS Hpc) as (c' & m' & IE & HS').
    rewrite IE. eexists. split; [reflexivity| exact HS'].
Qed.

Lemma m_addi : forall E st ms model (w : bv 32) (i : instr) rd rs1 v (x : sv),
  st_ok segs OPS E st ms model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  of_instr i = Some (IOpImm ALU_ADD rd rs1 v) ->
  den E x = (den E (getr st rs1) + wbv v)%bv ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok segs OPS E (setpc (setr st rd x) (pc4 st)) ms' model.
Proof.
  intros E st ms model w i rd rs1 v x HS Hpc Hf He Hd Hof HX.
  rewrite (step_exec segs ms w i Hf He Hd).
  destruct i; cbn [of_instr] in Hof; try discriminate Hof; inv_of Hof.
  - cbn [Sem.exec].
    destruct (StepA.case_reg segs OPS E st ms model rd x _ HS Hpc HX) as (c' & m' & IE & HS').
    rewrite (StepA.getr_den segs OPS E st ms model _ HS), wbv_w_of_imm in IE. cbn [alu64 alu]. rewrite IE. eexists. split; [reflexivity| exact HS'].
  - cbn [Sem.exec].
    destruct (StepA.case_reg segs OPS E st ms model rd x _ HS Hpc HX) as (c' & m' & IE & HS').
    rewrite (StepA.getr_den segs OPS E st ms model _ HS), wbv_w_of_uimm in IE. cbn [alu64 alu]. rewrite IE. eexists. split; [reflexivity| exact HS'].
Qed.

End WithSegs.
End VdStep.

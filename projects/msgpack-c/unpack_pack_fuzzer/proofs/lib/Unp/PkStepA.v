(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout OpsBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib PkStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS UB.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkStepA.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.
Variable CH : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAW : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CH os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.

Lemma oracle_ILoad_a : forall E st ms model (w : bv 32) (i : instr) sz sx rd rs1 off A z (v : sv),
  st_ok segs OPS E st ms model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  of_instr i = Some (ILoad sz sx rd rs1 off) ->
  den E (sv_alu ALU_ADD (getr st rs1) (VL off)) = Z_to_bv 64 A -> 0 <= A -> A + to_Z (msize_bytes sz) <= two64 ->
  rdZ (bmem_of segs (ms_mem ms)) A (Z.to_nat (to_Z (msize_bytes sz))) = Some z ->
  den E v = ext_word sx 0 (to_Z (msize_bytes sz)) (Z_to_bv 64 z) ->
  (forall j, 0 <= j < to_Z (msize_bytes sz) -> CH (insts E (s_ops st)) (ms_mem ms) model (A + j)) ->
  exists ms' mo', mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                  st_ok segs OPS E (setpc (setr st rd v) (pc4 st)) ms' mo'.
Proof.
  intros E st ms model w i sz sx rd rs1 off A z v HS Hpc Hf He Hd Hof HA A0 A1 RD Hv HCH.
  destruct (PkStep.oracle_ILoad segs OPS E st ms model w i sz sx rd rs1 off A z v HS Hpc Hf He Hd Hof HA A0 A1 RD Hv) as (ms' & STEP & MEM & ST2).
  destruct (of_instr_ILoad i sz sx rd rs1 off Hof) as (rd' & rs1' & imm & -> & Hrd & Hrs1 & ->).
  destruct (AccStep.st_ok_account segs OPS CH LAW E (setpc (setr st rd v) (pc4 st)) ms ms' model w _ Hf He Hd STEP ST2) as (mo' & AS & ST3).
  { intros a n j [Ha Hn] Hj. cbn [Acc.mem_acc] in *. subst a n.
    change (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) with (core_of ms).
    rewrite (ea_den segs OPS E st ms model rs1 rs1' _ imm HS Hrs1), HA.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    assert (W8 : 1 <= to_Z (msize_bytes sz) <= 8) by (destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
    rewrite Z.mod_small by lia.
    rewrite MEM. cbn [setpc s_ops]. rewrite StepAcc.s_ops_setr.
    apply HCH. replace (Z.of_nat (Acc.msz_nat sz)) with (to_Z (msize_bytes sz)) in Hj by (destruct sz; reflexivity). exact Hj. }
  exists ms', mo'. split; [exact AS|]. split; [exact MEM| exact ST3].
Qed.

Lemma oracle_ILoad_mp : forall (MP : Model -> Prop),
  (forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo') ->
  forall E st ms model (w : bv 32) (i : instr) sz sx rd rs1 off A z (v : sv),
  st_ok segs OPS E st ms model -> MP model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  of_instr i = Some (ILoad sz sx rd rs1 off) ->
  den E (sv_alu ALU_ADD (getr st rs1) (VL off)) = Z_to_bv 64 A -> 0 <= A -> A + to_Z (msize_bytes sz) <= two64 ->
  rdZ (bmem_of segs (ms_mem ms)) A (Z.to_nat (to_Z (msize_bytes sz))) = Some z ->
  den E v = ext_word sx 0 (to_Z (msize_bytes sz)) (Z_to_bv 64 z) ->
  (forall j, 0 <= j < to_Z (msize_bytes sz) -> CH (insts E (s_ops st)) (ms_mem ms) model (A + j)) ->
  exists ms' mo', mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                  st_ok segs OPS E (setpc (setr st rd v) (pc4 st)) ms' mo' /\ MP mo'.
Proof.
  intros MP HMPA E st ms model w i sz sx rd rs1 off A z v HS HMP Hpc Hf He Hd Hof HA A0 A1 RD Hv HCH.
  destruct (PkStep.oracle_ILoad segs OPS E st ms model w i sz sx rd rs1 off A z v HS Hpc Hf He Hd Hof HA A0 A1 RD Hv) as (ms' & STEP & MEM & ST2).
  destruct (of_instr_ILoad i sz sx rd rs1 off Hof) as (rd' & rs1' & imm & -> & Hrd & Hrs1 & ->).
  destruct (AccStep.st_ok_account_mp segs OPS CH LAW MP HMPA E (setpc (setr st rd v) (pc4 st)) ms ms' model w _ Hf He Hd STEP ST2 HMP) as (mo' & AS & ST3 & MP3).
  { intros a n j [Ha Hn] Hj. cbn [Acc.mem_acc] in *. subst a n.
    change (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) with (core_of ms).
    rewrite (ea_den segs OPS E st ms model rs1 rs1' _ imm HS Hrs1), HA.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    assert (W8 : 1 <= to_Z (msize_bytes sz) <= 8) by (destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
    rewrite Z.mod_small by lia.
    rewrite MEM. cbn [setpc s_ops]. rewrite StepAcc.s_ops_setr.
    apply HCH. replace (Z.of_nat (Acc.msz_nat sz)) with (to_Z (msize_bytes sz)) in Hj by (destruct sz; reflexivity). exact Hj. }
  exists ms', mo'. split; [exact AS|]. split; [exact MEM|]. split; [exact ST3| exact MP3].
Qed.

End WithSegs.
End PkStepA.

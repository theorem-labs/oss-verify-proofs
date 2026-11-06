(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the assembly of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command): the top loop by downward induction on the pass and the chain of segment statements to the function's contract, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v (rt_G_allX by induction, tfib_lib_x_body) and A/ACh6.v (segment statements composed into the contract). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the head of a pass m >= 32 is not reached, at any FP state: lt_body asks m < 32 (the latch at 0x8699c leaves
   after pass 31) *)
Lemma LT_LH_vacuous : forall m, (32 <= m)%nat -> LTA_LH B MT m.
Proof.
intros m Hm fx1. unfold LT_LH_stmt. intros * _ _ HBODY. exfalso.
destruct HBODY as (_ & _ & _ & _ & _ & _ & Hm32 & _). lia.
Qed.

(* the top loop, by downward induction on the pass (cgif A/ACfj.v:157-163, rt_G_allX): one pass is the chain
   head -> send_message -> words_of -> the four checks -> check_round_trip -> the frees and the latch, which goes to
   the next head or to the second rec_clear; every statement holds at every FP state (the LTA forms), because a
   callee may return at another one (apost_baseF) *)
Lemma lt_loop :
  (forall m, LTA_SM B MT m -> LTA_LH B MT m) ->
  (forall m, LTA_W B MT m -> LTA_SM B MT m) ->
  (forall m, LTA_K B MT m -> LTA_W B MT m) ->
  (forall m, LTA_RT B MT m -> LTA_K B MT m) ->
  (forall m, LTA_F B MT m -> LTA_RT B MT m) ->
  (forall m, LTA_LH B MT (Datatypes.S m) -> LTA_Z B MT -> LTA_F B MT m) ->
  LTA_Z B MT ->
  forall m, LTA_LH B MT m.
Proof.
intros HLH HSM HW HK HRT HF HZ.
assert (H : forall d m, (32 <= m + d)%nat -> LTA_LH B MT m).
{ induction d as [|d IH]; intros m Hmd.
  - apply LT_LH_vacuous. lia.
  - exact (HLH m (HSM m (HW m (HK m (HRT m (HF m (IH (Datatypes.S m) ltac:(lia)) HZ)))))). }
intros m. exact (H 32%nat m ltac:(lia)).
Qed.

(* the whole function from its segments, each given at every FP state *)
Lemma lt_assemble :
  (LTA_RC1 B MT -> LTA_ENTRY B MT) ->
  (LTA_A B MT -> LTA_RC1 B MT) ->
  (LTA_LH B MT 0 -> LTA_Z B MT -> LTA_A B MT) ->
  (forall m, LTA_SM B MT m -> LTA_LH B MT m) ->
  (forall m, LTA_W B MT m -> LTA_SM B MT m) ->
  (forall m, LTA_K B MT m -> LTA_W B MT m) ->
  (forall m, LTA_RT B MT m -> LTA_K B MT m) ->
  (forall m, LTA_F B MT m -> LTA_RT B MT m) ->
  (forall m, LTA_LH B MT (Datatypes.S m) -> LTA_Z B MT -> LTA_F B MT m) ->
  (LTA_Z2 B MT -> LTA_Z B MT) ->
  LTA_Z2 B MT ->
  LTA_ENTRY B MT.
Proof.
intros HE HRC1 HA HLH HSM HW HK HRT HF HRC2 HZ2.
exact (HE (HRC1 (HA (lt_loop HLH HSM HW HK HRT HF (HRC2 HZ2) 0%nat) (HRC2 HZ2)))).
Qed.

(* the contract from the walk's entry statement at the ambient FP state: lt_base is the statement's premises but
   rounding mode 0, which is the entry statement's second premise; lt_post is the statement's post *)
Lemma lt_adapter : LTA_ENTRY B MT -> tLLVMFuzzerTestOneInput_spec B MT.
Proof.
intros HE. unfold tLLVMFuzzerTestOneInput_spec.
intros ly S W regs mem md ch p n pl j H1 HSP HF0 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
exact (HE fx (mkLCX ly S W regs mem md ch p n pl j)
  (conj H1 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
    (conj H13 (conj H14 (conj H15 HSP)))))))))))))) HF0).
Qed.

End e.
End f.
End d.

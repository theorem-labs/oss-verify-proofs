(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes MonadX Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Malloc Monad SjModel AtpModel ElModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_iface Sj_stage2_iface Sj_stage2_rootnum Sj_num_closed El_defs El_h3 El_top El_act El_a22 El_arm8 El_arm22 El_arm23 El_arm24 El_arm26 El_arm28.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem el_stage2t_closed : stage2t_stmt.
Proof. exact (stage2t_of_contracts rmalloc_spec rfree_spec_proof slowf_closed pff_closed). Qed.

Theorem rfuzz_one_of_slots :
  (forall sel, 0 <= sel < 8 -> throw_slot (cast_site sel) 0x3bf00) -> throw_slot 0x3c458 0x3bed8 -> throw_slot 0x3c4c8 0x3bf38 ->
  arm_stmt 25 0x3bf3c -> arm_stmt 29 0x3bf18 -> arm_stmt 30 0x3bf74 -> arm_stmt 31 0x3bf54 ->
  rfuzz_one_stmt.
Proof.
  intros T22 T23 T24 A25 A29 A30 A31.
  exact (rfuzz_one_of_parts rmalloc_spec rfree_spec_proof el_stage2t_closed
           (el_act_of_arms arm8_proof (arm22_proof T22) (arm23_proof T23) (arm24_proof T24) A25 (arm26_proof rmalloc_spec rfree_spec_proof) arm28_proof A29 A30 A31)).
Qed.
End WithCeiling0.

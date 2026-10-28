(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes MonadX Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Malloc Monad SjModel AtpModel ElModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_iface Sj_stage2_iface Sj_stage2_rootnum Sj_num_closed El_defs El_h3 El_top El_act El_a22 El_arm8 El_arm22 El_arm23 El_arm24 El_arm26 El_arm28.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_throw_site El_armd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem el_stage2t_closed : stage2t_stmt.
Proof. exact (stage2t_of_contracts rmalloc_spec rfree_spec_proof slowfu_closed pffu_closed). Qed.

Theorem rfuzz_one_of_slots :
  (forall sel, 0 <= sel < 8 -> throw_slot (cast_site sel) (cast_D sel) 0x3c378 (cast_XP sel) xr_none) ->
  throw_slot 0x3d968 0 0x3c344 xp_none xr_none -> throw_slot 0x3f010 64 0x3c3ec xp_end xr_end ->
  arm_stmt 25 0x3c324 -> arm_stmt 29 0x3c354 -> arm_stmt 30 0x3c3b0 -> arm_stmt 31 0x3c444 ->
  rfuzz_one_stmt.
Proof.
  intros T22 T23 T24 A25 A29 A30 A31.
  assert (ARMS : forall a, 0 <= a < 32 -> a <> 27 -> arm_stmt a (el_target a)).
  { intros a Ha N27.
    destruct (Z_lt_dec a 22) as [L|L].
    - destruct (Z.eq_dec a 8) as [->|N8]; [change (el_target 8) with 0x3c494; exact arm8_proof| exact (arm_dead a ltac:(lia) N8)].
    - assert (C : a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
      + change (el_target 22) with 0x3c36c. exact (arm22_proof T22).
      + change (el_target 23) with 0x3c33c. exact (arm23_proof T23).
      + change (el_target 24) with 0x3c3e4. exact (arm24_proof T24).
      + change (el_target 25) with 0x3c324. exact A25.
      + change (el_target 26) with 0x3c4dc. exact (arm26_proof rmalloc_spec rfree_spec_proof).
      + change (el_target 28) with 0x3c4c8. exact arm28_proof.
      + change (el_target 29) with 0x3c354. exact A29.
      + change (el_target 30) with 0x3c3b0. exact A30.
      + change (el_target 31) with 0x3c444. exact A31. }
  exact (rfuzz_one_of_parts rmalloc_spec rfree_spec_proof el_stage2t_closed (el_act_of_arms ARMS)).
Qed.
End WithCeiling0.

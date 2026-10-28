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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_key El_armk El_dump_iface El_osd El_arm31 El_throw_site El_xglue El_slots El_ins_iface El_esc_iface El_os_put El_setfill El_os_ins El_dump_top El_esc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem rfuzz_one_closed : dump_stmt -> rfuzz_one_stmt.
Proof.
  intros D.
  exact (rfuzz_one_of_slots throw_slot_cast throw_slot_begin throw_slot_end arm25_proof arm29_proof arm30_proof (arm31_proof D)).
Qed.

Theorem rfuzz_one_of_ins : ins_ul_stmt -> ins_u_stmt -> ins_l_stmt -> ins_i_stmt -> ins_d_stmt -> setfill_stmt -> rfuzz_one_stmt.
Proof.
  intros IUL IU IL INSI INSD SETF.
  exact (rfuzz_one_closed (dump_of_parts os_putX_proof IUL IU IL INSD (esc_of_parts os_putX_proof SETF INSI))).
Qed.

Theorem rfuzz_one_of_insd : ins_d_stmt -> rfuzz_one_stmt.
Proof.
  intros INSD. exact (rfuzz_one_of_ins ins_ul_proof ins_u_proof ins_l_proof ins_i_proof INSD setfill_proof).
Qed.
End WithCeiling0.

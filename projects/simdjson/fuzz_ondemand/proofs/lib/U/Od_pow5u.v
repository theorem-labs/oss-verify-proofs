(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Sj_num_walk Od_pow5.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma upow5_image : ro_bytes_b usegs OT_POW5 (u64s OD_POW5_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma upow5_len : Z.of_nat (length (u64s OD_POW5_WORDS)) = 10416%Z.
Proof. rewrite u64s_length. unfold OD_POW5_WORDS. rewrite length_map. vm_compute. reflexivity. Qed.

Lemma upow5_at : forall m, mem_inv usegs m -> bytes_at usegs m OT_POW5 (u64s OD_POW5_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold OT_POW5; lia | rewrite upow5_len; unfold OT_POW5; lia |].
  apply ro_bytes_b_sound. exact upow5_image.
Qed.

Lemma upow5_read : forall (m : mem) j, mem_inv usegs m -> 0 <= j < 1302 ->
  exists v, ov_read_bytes usegs m (wa (84088 + 8 * j)) 8 = Some (le8 v).
Proof.
  intros m j MI Hj. eexists.
  apply (bytes_read8_at usegs m OT_POW5 (u64s OD_POW5_WORDS) (8 * j)%Z); [apply upow5_at; exact MI | lia | rewrite upow5_len; lia |].
  unfold wa, OT_POW5. f_equal.
Qed.

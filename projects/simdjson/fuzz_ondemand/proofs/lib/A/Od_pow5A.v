(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Sj_num_walk Od_pow5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition AT_POW5 : Z := 150848.

Lemma apow5_image : ro_bytes_b asegs AT_POW5 (u64s OD_POW5_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma apow5_len : Z.of_nat (length (u64s OD_POW5_WORDS)) = 10416%Z.
Proof. rewrite u64s_length. unfold OD_POW5_WORDS. rewrite length_map. vm_compute. reflexivity. Qed.
Lemma apow5_at : forall m, mem_inv asegs m -> bytes_at asegs m AT_POW5 (u64s OD_POW5_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold AT_POW5; lia | rewrite apow5_len; unfold AT_POW5; lia |].
  apply ro_bytes_b_sound. exact apow5_image.
Qed.

Lemma apow5_read : forall (m : mem) o, mem_inv asegs m -> 0 <= o -> o + 8 <= 10416 ->
  exists v, ov_read_bytes asegs m (wa (150848 + o)) 8 = Some (le8 v).
Proof.
  intros m o MI Ho Ho8. eexists.
  apply (bytes_read8_at asegs m AT_POW5 (u64s OD_POW5_WORDS) o); [apply apow5_at; exact MI | lia | rewrite apow5_len; lia |].
  unfold wa, AT_POW5. reflexivity.
Qed.

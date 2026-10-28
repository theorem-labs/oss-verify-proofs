(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BothPopFree.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

Definition asan_popfree_head : Z := 0x97908.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word ASEGS (Z_to_bv 64 asan_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem asan_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments asan_popfree_head.
Proof.
  apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.


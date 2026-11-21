(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bba14 : bv 32 := 0x0004b503.
Lemma F_bba14 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbbfe0 : word) = Some W_bba14.
Proof. vm_refl. Qed.
Lemma D_bba14 : decode_any W_bba14 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bba18 : bv 32 := 0x00848493.
Lemma F_bba18 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbbfe4 : word) = Some W_bba18.
Proof. vm_refl. Qed.
Lemma D_bba18 : decode_any W_bba18 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bba1c : bv 32 := 0xfe051ce3.
Lemma F_bba1c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbbfe8 : word) = Some W_bba1c.
Proof. vm_refl. Qed.
Lemma D_bba1c : decode_any W_bba1c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_bbad0 : bv 32 := 0x00b53023.
Lemma F_bbad0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbc09c : word) = Some W_bbad0.
Proof. vm_refl. Qed.
Lemma D_bbad0 : decode_any W_bbad0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbad4 : bv 32 := 0x00158593.
Lemma F_bbad4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbc0a0 : word) = Some W_bbad4.
Proof. vm_refl. Qed.
Lemma D_bbad4 : decode_any W_bbad4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbad8 : bv 32 := 0xfff5c683.
Lemma F_bbad8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbc0a4 : word) = Some W_bbad8.
Proof. vm_refl. Qed.
Lemma D_bbad8 : decode_any W_bbad8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbadc : bv 32 := 0xfec68ae3.
Lemma F_bbadc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbc0a8 : word) = Some W_bbadc.
Proof. vm_refl. Qed.
Lemma D_bbadc : decode_any W_bbadc = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbae0 : bv 32 := 0xfe069ae3.
Lemma F_bbae0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xbc0ac : word) = Some W_bbae0.
Proof. vm_refl. Qed.
Lemma D_bbae0 : decode_any W_bbae0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

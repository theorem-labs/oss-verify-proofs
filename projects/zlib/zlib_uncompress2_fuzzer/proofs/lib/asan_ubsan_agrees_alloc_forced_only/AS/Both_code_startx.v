(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bcec0 : bv 32 := 0x0004b503.
Lemma F_bcec0 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd4ec : word) = Some W_bcec0.
Proof. vm_refl. Qed.
Lemma D_bcec0 : decode_any W_bcec0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcec4 : bv 32 := 0x00848493.
Lemma F_bcec4 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd4f0 : word) = Some W_bcec4.
Proof. vm_refl. Qed.
Lemma D_bcec4 : decode_any W_bcec4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcec8 : bv 32 := 0xfe051ce3.
Lemma F_bcec8 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd4f4 : word) = Some W_bcec8.
Proof. vm_refl. Qed.
Lemma D_bcec8 : decode_any W_bcec8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_bcf7c : bv 32 := 0x00b53023.
Lemma F_bcf7c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd5a8 : word) = Some W_bcf7c.
Proof. vm_refl. Qed.
Lemma D_bcf7c : decode_any W_bcf7c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcf80 : bv 32 := 0x00158593.
Lemma F_bcf80 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd5ac : word) = Some W_bcf80.
Proof. vm_refl. Qed.
Lemma D_bcf80 : decode_any W_bcf80 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcf84 : bv 32 := 0xfff5c683.
Lemma F_bcf84 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd5b0 : word) = Some W_bcf84.
Proof. vm_refl. Qed.
Lemma D_bcf84 : decode_any W_bcf84 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcf88 : bv 32 := 0xfec68ae3.
Lemma F_bcf88 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd5b4 : word) = Some W_bcf88.
Proof. vm_refl. Qed.
Lemma D_bcf88 : decode_any W_bcf88 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcf8c : bv 32 := 0xfe069ae3.
Lemma F_bcf8c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xbd5b8 : word) = Some W_bcf8c.
Proof. vm_refl. Qed.
Lemma D_bcf8c : decode_any W_bcf8c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

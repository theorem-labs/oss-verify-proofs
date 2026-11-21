(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bcc74 : bv 32 := 0x0004b503.
Lemma F_bcc74 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd24c : word) = Some W_bcc74.
Proof. vm_refl. Qed.
Lemma D_bcc74 : decode_any W_bcc74 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcc78 : bv 32 := 0x00848493.
Lemma F_bcc78 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd250 : word) = Some W_bcc78.
Proof. vm_refl. Qed.
Lemma D_bcc78 : decode_any W_bcc78 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcc7c : bv 32 := 0xfe051ce3.
Lemma F_bcc7c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd254 : word) = Some W_bcc7c.
Proof. vm_refl. Qed.
Lemma D_bcc7c : decode_any W_bcc7c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_bcd30 : bv 32 := 0x00b53023.
Lemma F_bcd30 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd308 : word) = Some W_bcd30.
Proof. vm_refl. Qed.
Lemma D_bcd30 : decode_any W_bcd30 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcd34 : bv 32 := 0x00158593.
Lemma F_bcd34 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd30c : word) = Some W_bcd34.
Proof. vm_refl. Qed.
Lemma D_bcd34 : decode_any W_bcd34 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcd38 : bv 32 := 0xfff5c683.
Lemma F_bcd38 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd310 : word) = Some W_bcd38.
Proof. vm_refl. Qed.
Lemma D_bcd38 : decode_any W_bcd38 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcd3c : bv 32 := 0xfec68ae3.
Lemma F_bcd3c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd314 : word) = Some W_bcd3c.
Proof. vm_refl. Qed.
Lemma D_bcd3c : decode_any W_bcd3c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcd40 : bv 32 := 0xfe069ae3.
Lemma F_bcd40 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xbd318 : word) = Some W_bcd40.
Proof. vm_refl. Qed.
Lemma D_bcd40 : decode_any W_bcd40 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

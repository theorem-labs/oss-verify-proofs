(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bb7d0 : bv 32 := 0x0004b503.
Lemma F_bb7d0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbd4c : word) = Some W_bb7d0.
Proof. vm_refl. Qed.
Lemma D_bb7d0 : decode_any W_bb7d0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bb7d4 : bv 32 := 0x00848493.
Lemma F_bb7d4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbd50 : word) = Some W_bb7d4.
Proof. vm_refl. Qed.
Lemma D_bb7d4 : decode_any W_bb7d4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bb7d8 : bv 32 := 0xfe051ce3.
Lemma F_bb7d8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbd54 : word) = Some W_bb7d8.
Proof. vm_refl. Qed.
Lemma D_bb7d8 : decode_any W_bb7d8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_bb88c : bv 32 := 0x00b53023.
Lemma F_bb88c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbe08 : word) = Some W_bb88c.
Proof. vm_refl. Qed.
Lemma D_bb88c : decode_any W_bb88c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bb890 : bv 32 := 0x00158593.
Lemma F_bb890 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbe0c : word) = Some W_bb890.
Proof. vm_refl. Qed.
Lemma D_bb890 : decode_any W_bb890 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bb894 : bv 32 := 0xfff5c683.
Lemma F_bb894 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbe10 : word) = Some W_bb894.
Proof. vm_refl. Qed.
Lemma D_bb894 : decode_any W_bb894 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bb898 : bv 32 := 0xfec68ae3.
Lemma F_bb898 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbe14 : word) = Some W_bb898.
Proof. vm_refl. Qed.
Lemma D_bb898 : decode_any W_bb898 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bb89c : bv 32 := 0xfe069ae3.
Lemma F_bb89c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xbbe18 : word) = Some W_bb89c.
Proof. vm_refl. Qed.
Lemma D_bb89c : decode_any W_bb89c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

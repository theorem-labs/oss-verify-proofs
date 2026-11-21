(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.World Require Import Tgt_zlib_uncompress3_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bbae0 : bv 32 := 0x0004b503.
Lemma F_bbae0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc0ac : word) = Some W_bbae0.
Proof. vm_refl. Qed.
Lemma D_bbae0 : decode_any W_bbae0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbae4 : bv 32 := 0x00848493.
Lemma F_bbae4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc0b0 : word) = Some W_bbae4.
Proof. vm_refl. Qed.
Lemma D_bbae4 : decode_any W_bbae4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbae8 : bv 32 := 0xfe051ce3.
Lemma F_bbae8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc0b4 : word) = Some W_bbae8.
Proof. vm_refl. Qed.
Lemma D_bbae8 : decode_any W_bbae8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_bbb9c : bv 32 := 0x00b53023.
Lemma F_bbb9c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc168 : word) = Some W_bbb9c.
Proof. vm_refl. Qed.
Lemma D_bbb9c : decode_any W_bbb9c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbba0 : bv 32 := 0x00158593.
Lemma F_bbba0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc16c : word) = Some W_bbba0.
Proof. vm_refl. Qed.
Lemma D_bbba0 : decode_any W_bbba0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbba4 : bv 32 := 0xfff5c683.
Lemma F_bbba4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc170 : word) = Some W_bbba4.
Proof. vm_refl. Qed.
Lemma D_bbba4 : decode_any W_bbba4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbba8 : bv 32 := 0xfec68ae3.
Lemma F_bbba8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc174 : word) = Some W_bbba8.
Proof. vm_refl. Qed.
Lemma D_bbba8 : decode_any W_bbba8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbbac : bv 32 := 0xfe069ae3.
Lemma F_bbbac : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xbc178 : word) = Some W_bbbac.
Proof. vm_refl. Qed.
Lemma D_bbbac : decode_any W_bbbac = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

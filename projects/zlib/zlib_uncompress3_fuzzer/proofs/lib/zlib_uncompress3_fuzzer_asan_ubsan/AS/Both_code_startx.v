(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.World Require Import Tgt_zlib_uncompress3_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bcfac : bv 32 := 0x0004b503.
Lemma F_bcfac : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd5d8 : word) = Some W_bcfac.
Proof. vm_refl. Qed.
Lemma D_bcfac : decode_any W_bcfac = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcfb0 : bv 32 := 0x00848493.
Lemma F_bcfb0 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd5dc : word) = Some W_bcfb0.
Proof. vm_refl. Qed.
Lemma D_bcfb0 : decode_any W_bcfb0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bcfb4 : bv 32 := 0xfe051ce3.
Lemma F_bcfb4 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd5e0 : word) = Some W_bcfb4.
Proof. vm_refl. Qed.
Lemma D_bcfb4 : decode_any W_bcfb4 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_bd068 : bv 32 := 0x00b53023.
Lemma F_bd068 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd694 : word) = Some W_bd068.
Proof. vm_refl. Qed.
Lemma D_bd068 : decode_any W_bd068 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd06c : bv 32 := 0x00158593.
Lemma F_bd06c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd698 : word) = Some W_bd06c.
Proof. vm_refl. Qed.
Lemma D_bd06c : decode_any W_bd06c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd070 : bv 32 := 0xfff5c683.
Lemma F_bd070 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd69c : word) = Some W_bd070.
Proof. vm_refl. Qed.
Lemma D_bd070 : decode_any W_bd070 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd074 : bv 32 := 0xfec68ae3.
Lemma F_bd074 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd6a0 : word) = Some W_bd074.
Proof. vm_refl. Qed.
Lemma D_bd074 : decode_any W_bd074 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd078 : bv 32 := 0xfe069ae3.
Lemma F_bd078 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xbd6a4 : word) = Some W_bd078.
Proof. vm_refl. Qed.
Lemma D_bd078 : decode_any W_bd078 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

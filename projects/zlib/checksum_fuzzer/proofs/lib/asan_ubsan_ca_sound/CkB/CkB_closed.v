(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkB Require Import CkBImg CkBIface CrcB_cop CrcB_gen CrcB_comb CrcB_z FuzzB_d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem ck_fuzz_B : ck_fuzz_stmtA.
Proof.
  exact (ck_fuzz_proofA crc32_z_proofA crc32_proofA crc32_null_proofA crc32_combine_proofA crc32_combine_gen_proofA crc32_combine_op_proofA).
Qed.


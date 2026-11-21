(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.CkA Require Import CkAImg CkAIface CrcA_cop CrcA_gen CrcA_comb CrcA_z FuzzA_d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem ck_fuzz_A : ck_fuzz_stmtA.
Proof.
  exact (ck_fuzz_proofA crc32_z_proofA crc32_proofA crc32_null_proofA crc32_combine_proofA crc32_combine_gen_proofA crc32_combine_op_proofA).
Qed.


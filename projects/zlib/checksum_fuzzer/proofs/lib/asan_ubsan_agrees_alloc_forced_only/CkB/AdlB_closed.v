(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkB Require Import CkBIface AdlB_wrap AdlB_z AdlB_comb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem adler32_z_A : adler32_z_stmtA. Proof. exact adler32_z_proofA. Qed.
Theorem adler32_z_null_A : adler32_z_null_stmtA. Proof. exact adler32_z_null_proofA. Qed.
Theorem adler32_A : adler32_stmtA. Proof. exact (adler32_proofA adler32_z_proofA). Qed.
Theorem adler32_null_A : adler32_null_stmtA. Proof. exact (adler32_null_proofA adler32_z_null_proofA). Qed.
Theorem adler32_combine_A : adler32_combine_stmtA. Proof. exact adler32_combine_proofA. Qed.


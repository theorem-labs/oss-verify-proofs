(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require DrvTop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require DrvTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Theorem ubsan_base : strong_universal_error_free_T_scfg (alloc_only_cfg false) SRC0 UBSAN.
Proof.
  exact (ubsan_base_of OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.DrvTop.p_main_proof
                       OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.DrvTop.u_main_proof).
Qed.

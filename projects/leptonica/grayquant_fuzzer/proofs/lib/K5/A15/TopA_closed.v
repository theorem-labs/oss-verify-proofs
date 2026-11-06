(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.leptonica.grayquant_fuzzer.images Require Asan.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_s3s.

Theorem s3s_of_conetop : (rt_contracts RTA -> rt_gaps RTA -> fuzz_one_cps RTA LIB_A) ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof. intros CONE. exact (s3s_A15_of_cone (CONE rta_rc rta_gaps)). Qed.

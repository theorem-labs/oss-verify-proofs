(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Cf_iface Cf_top Cf_fuzz.

Theorem cf_cone : forall RT, art_facts RT -> rt_contracts RT -> rt_gaps RT ->
  returnError_cps RT e_returnErrorPtr -> pixDeserialize_cps RT -> pixDestroy_cps RT -> cf_fuzz_one_cps RT.
Proof.
  intros RT AF RC GP RERR DESER DESTROY.
  exact (cf_fuzz_ok RT AF RC GP DESER DESTROY (l_colorfillCreate_closed RT AF GP RERR) (l_colorfillDestroy_closed RT AF GP)).
Qed.

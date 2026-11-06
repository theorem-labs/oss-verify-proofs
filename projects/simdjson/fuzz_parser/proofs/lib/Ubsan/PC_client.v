(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw RMalloc_iface ROpNew_iface ROpNew ROpNew_nt RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PU_iface UbsanClosed PC_s12iface PC_parse PC_s1bridge PC_fuzz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import ProgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem ubsan_client_mod_stage2 : (forall rc : runConstT, @stage2_stmt rc) -> ubsan_client_stmt.
Proof.
  intros S2 rc.
  exact (@fuzz_proof rc (opnew_nt_proof rmalloc_spec) (opdelete_arr_proof rfree_spec_proof) (opdelete_proof rfree_spec_proof)
           (parse_proof (@s1l_proof rc) (S2 rc))).
Qed.
Print Assumptions ubsan_client_mod_stage2.

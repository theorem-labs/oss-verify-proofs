(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_iface Pj_stmts Pj_ser_defs Pj_ser_str Pj_ser_key Pj_ser_closed Pj_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rfuzz_one_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, rfuzz_one_stmt.
Proof. intros CE RN. exact (rfuzz_one_of_ser (ser_closed rmalloc_spec rfree_spec_proof (str_proof rmalloc_spec rfree_spec_proof) (key_proof rmalloc_spec rfree_spec_proof) TAPE_MAX_DEPTH)). Qed.


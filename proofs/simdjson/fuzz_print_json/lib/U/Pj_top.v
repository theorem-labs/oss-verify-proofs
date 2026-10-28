(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_iface Sj_stage2_iface Sj_stage2_rootnum Sj_num_closed Pj_stmts Pj_lftoi Pj_okarm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem stage2t_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, stage2t_stmt.
Proof. intros CE RN. exact (stage2t_of_contracts rmalloc_spec rfree_spec_proof slowfu_closed pffu_closed). Qed.

Theorem rfuzz_one_of_ser : forall {CE__ : Ceiling} {RN__ : RunRnd}, ser_stmt TAPE_MAX_DEPTH -> rfuzz_one_stmt.
Proof. intros CE RN SER. exact (rfuzz_one_of_parts rmalloc_spec rfree_spec_proof stage2t_closed (pj_okarm_proof rfree_spec_proof SER)). Qed.


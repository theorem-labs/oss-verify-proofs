(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_iface El_os_insd El_closed.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rfuzz_one_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, rfuzz_one_stmt.
Proof. intros CE RN. exact (rfuzz_one_of_insd ins_d_proof). Qed.

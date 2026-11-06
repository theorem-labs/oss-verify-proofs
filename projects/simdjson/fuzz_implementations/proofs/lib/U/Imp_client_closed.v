(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_iface Pj_stmts Pj_ser_defs Pj_ser_str Pj_ser_key Pj_ser_closed Imp_iface Imp_okarm Imp_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rfuzz_one_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, rfuzz_one_stmt.
Proof.
  intros CE RN.
  exact (rfuzz_one_of_okarm (imp_okarm_proof rmalloc_spec rfree_spec_proof
           (ser_closed rmalloc_spec rfree_spec_proof (str_proof rmalloc_spec rfree_spec_proof) (key_proof rmalloc_spec rfree_spec_proof) TAPE_MAX_DEPTH))).
Qed.

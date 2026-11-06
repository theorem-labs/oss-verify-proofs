(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocU Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Sj_iface Sj_stage2_iface Sj_stage2_rootnum Sj_num_closed Dmp_pj_iface Dmp_lftoi Dmp_okarm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem stage2t_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, stage2t_stmt.
Proof. intros CE RN. exact (stage2t_of_contracts rmalloc_spec rfree_spec_proof slowfu_closed pffu_closed). Qed.

Theorem rfuzz_one_of_pj : forall {CE__ : Ceiling} {RN__ : RunRnd}, pj_root_stmt -> rfuzz_one_stmt.
Proof. intros CE RN PJ. exact (rfuzz_one_premise rmalloc_spec rfree_spec_proof stage2t_closed (dmp_okarm_proof PJ)). Qed.

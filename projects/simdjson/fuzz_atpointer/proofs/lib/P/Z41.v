(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zi1 Zhj Zha.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zq5 Zwn Zz2 Zqj Z44 Z72 Z50 Z76.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem stage2t_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, stage2t_stmt.
Proof. intros CE RN. exact (stage2t_of_contracts rmalloc_spec rfree_spec_proof slowf_closed pff_closed). Qed.

Theorem rfuzz_one_t2 : forall {CE__ : Ceiling} {RN__ : RunRnd}, (forall E, aenv_ok E -> atp_root_stmt E) -> rfuzz_one_stmt.
Proof. intros CE RN ROOT. exact (rfuzz_one_of_parts rmalloc_spec rfree_spec_proof stage2t_closed ROOT). Qed.

Theorem rfuzz_one_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, rfuzz_one_stmt.
Proof. intros CE RN. exact (rfuzz_one_t2 (atp_root rmalloc_spec rfree_spec_proof)). Qed.


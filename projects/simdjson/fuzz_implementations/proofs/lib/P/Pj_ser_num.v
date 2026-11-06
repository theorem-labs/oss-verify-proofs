(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Pj_ser_defs Pj_num_defs Pj_tochars Pj_ser_atom Pj_ser_dbl Pj_ser_u64 Pj_ser_i64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem dbl_closed : rmalloc_stmt -> rfree_stmt -> dbl_stmt.
Proof. intros HM HF. exact (dbl_proof HM HF tochars_proof). Qed.

Theorem num_arms : rmalloc_stmt -> rfree_stmt -> i64_stmt /\ u64_stmt /\ dbl_stmt /\ null_stmt /\ false_stmt.
Proof.
  intros HM HF.
  split; [exact (i64_proof HM HF)|]. split; [exact (u64_proof HM HF)|]. split; [exact (dbl_closed HM HF)|].
  split; [exact (null_proof HM HF)| exact (false_proof HM HF)].
Qed.

End WithCeiling0.

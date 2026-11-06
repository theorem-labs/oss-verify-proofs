(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_sf_helpers.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_sf_helpers2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_mul_core1.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_sf_helpers3.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_div_wide.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Lemma half_iter_range : forall x b, 0 <= half_iter x b < 18446744073709551616.
Proof.
  intros. unfold half_iter, shl64, mul64, mulhu, sub64.
  apply Z_lor_range.
  - apply (zr_shiftr _ 63). apply SoftFloat.wrap64_range. lia.
  - apply SoftFloat.wrap64_range.
Qed.
Ltac hi_rng X := let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply half_iter_range).
Ltac mulhu_rng X := let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply mulhu_range; (change (inr64 _) || idtac); zrange).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

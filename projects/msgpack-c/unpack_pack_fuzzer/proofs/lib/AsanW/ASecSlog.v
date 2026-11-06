(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ABase AModelFacts APrimFacts. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache3. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ASecFacts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma slog_facts : forall ms, 73728 <= ms <= 4293926912 -> ms mod 4096 = 0 ->
  0 <= cb_sm ms < 2^64 /\ 32 <= cb_clz (cb_sm ms) <= 47.
Proof.
  intros ms R _. destruct (cb_clz_sm ms ltac:(lia)) as [E1 E2]. rewrite E2, E1.
  assert (P16 : 16 <= Z.log2 ms). { change 16 with (Z.log2 65536). apply Z.log2_le_mono. lia. }
  assert (P31 : Z.log2 ms <= 31). { apply Z.lt_succ_r. change (Z.succ 31) with 32. apply Z.log2_lt_pow2; lia. }
  assert (B : 2^17 <= 2^(Z.log2 ms + 1) <= 2^32) by (split; apply Z.pow_le_mono_r; lia). lia.
Qed.
End CANSEC1.

Module TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import ABase.TwinB AModelFacts.TwinB APrimFacts.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache3. Import ASecFacts.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma slog_facts : forall ms, 73728 <= ms <= 4293926912 -> ms mod 4096 = 0 ->
  0 <= cb_sm ms < 2^64 /\ 32 <= cb_clz (cb_sm ms) <= 47.
Proof.
  intros ms R _. destruct (cb_clz_sm ms ltac:(lia)) as [E1 E2]. rewrite E2, E1.
  assert (P16 : 16 <= Z.log2 ms). { change 16 with (Z.log2 65536). apply Z.log2_le_mono. lia. }
  assert (P31 : Z.log2 ms <= 31). { apply Z.lt_succ_r. change (Z.succ 31) with 32. apply Z.log2_lt_pow2; lia. }
  assert (B : 2^17 <= 2^(Z.log2 ms + 1) <= 2^32) by (split; apply Z.pow_le_mono_r; lia). lia.
Qed.
End CANSEC1.
End TwinB.

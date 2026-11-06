(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanRep AsanWf1 AsanWf2 AsanBudget AsanBudget2 AsanBudget3.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_rtok5 BF_refill_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Lemma regions_bytes_same : forall a b, (forall c, get_region b c = get_region a c) -> regions_bytes b = regions_bytes a.
Proof.
  intros a b GR. unfold regions_bytes. generalize classes30. intros l. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH, GR. reflexivity.
Qed.

Lemma refill_room_of_binv : forall E (Pq : list Z) (Dq : list batch) a c,
  AWf E Pq Dq a -> binv a -> 1 <= c <= kLargestClassID -> 0 <= as_nprim_ever a <= 12000 ->
  refill_room a c /\ room a c.
Proof.
  intros E Pq Dq a c WF HBI Hc NP.
  pose proof (rooms_of_binv E Pq Dq a c WF HBI Hc NP) as (R1 & R2 & R3 & R5). pose proof (M2_sharp a HBI) as M.
  split; [| exact R1].
  unfold refill_room. cbv zeta. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [| exact R5].
  unfold gapR, kBatchPages, kUserMapSize, kFreeArrayMapSize. clear -M NP. lia.
Qed.

(* [comment removed for export] *)
Lemma refill_room_transport : forall a b c,
  (forall c', get_region b c' = get_region a c') -> as_nprim_ever b = as_nprim_ever a ->
  refill_room a c /\ room a c -> refill_room b c /\ room b c.
Proof.
  intros a b c GR NP [R RM]. unfold refill_room, room, gapR in *. cbv zeta in *. rewrite !GR, NP.
  rewrite (regions_bytes_same a b GR). exact (conj R RM).
Qed.

End RC__1.

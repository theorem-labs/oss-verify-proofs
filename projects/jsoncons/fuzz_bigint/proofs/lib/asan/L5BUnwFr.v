(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, auxv_above_friend and u64_at_two, which read the old ten-pair auxv, are removed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0 L5OpmodSpecsAB0 L5UnwindSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5BUF.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma landed_regs_by_index (R0 R' : bvmap 5 word) (sp rt8 : Z) :
  getr R' (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (sp + 16) -> getr R' (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 rt8 ->
  (forall k, In k [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))) ->
  L5OMA.landed_regs R0 R' sp rt8.
Proof.
  intros H2 H8 KR. unfold L5OMA.landed_regs.
  split. { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). exact H2. }
  split. { replace (8%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 8)) by (apply bv_eq; reflexivity). exact H8. }
  intros x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
End L5BUF.

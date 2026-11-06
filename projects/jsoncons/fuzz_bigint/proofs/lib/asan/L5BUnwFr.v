(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

Lemma u64_at_two M a v v' :
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M a v' ->
  map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 v)) = map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 v')).
Proof. unfold L5.u64_at. intros H1 H2. rewrite H1 in H2. apply (f_equal (fun o => match o with Some l => map bv_unsigned l | None => [] end)) in H2. exact H2. Qed.

Lemma auxv_above_friend M S av uid rnd hw :
  L5.u64_at RSEGS M (S + 8) L5OMA.OMF1_RET ->
  (forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)) ->
  av mod 8 = 0 -> S mod 16 = 0 -> S <= av -> S + 16 <= av.
Proof.
  intros RA AUXV AV8 S16 LE.
  destruct (Z_le_gt_dec (S + 16) av) as [OK|GT]; [exact OK|exfalso].
  assert (CASES : av = S \/ av = S + 8).
  { pose proof (Z_div_mod_eq_full av 8) as E1. pose proof (Z_div_mod_eq_full S 16) as E2. rewrite AV8 in E1. rewrite S16 in E2. clear - E1 E2 LE GT. lia. }
  destruct CASES as [E|E].
  - pose proof (AUXV 1%nat ltac:(lia)) as C. cbn [nth L5USA.auxv20A] in C. change (Z.of_nat 1) with 1 in C. replace (av + 8 * 1) with (S + 8) in C by (clear - E; lia).
    pose proof (u64_at_two _ _ _ _ RA C) as X. vm_compute in X. discriminate X.
  - pose proof (AUXV 0%nat ltac:(lia)) as C. cbn [nth L5USA.auxv20A] in C. change (Z.of_nat 0) with 0 in C. replace (av + 8 * 0) with (S + 8) in C by (clear - E; lia).
    pose proof (u64_at_two _ _ _ _ RA C) as X. vm_compute in X. discriminate X.
Qed.
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

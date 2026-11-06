(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_lkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma land_m4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
Lemma u8arr_sub_CB : forall m A bs k n,
  u8arr asegs m A bs -> (k + n <= length bs)%nat ->
  rw_cells asegs m (A + Z.of_nat k) [CB n (firstn n (skipn k bs))].
Proof.
  intros m A bs k n [B W] Hkn.
  assert (LF : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [split|].
  - cbn. split; [exact LF| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite <- (firstn_skipn k bs) in B. apply bytes_at_app in B. destruct B as [_ B]. rewrite length_firstn in B.
    replace (Nat.min k (length bs)) with k in B by lia.
    rewrite <- (firstn_skipn n (skipn k bs)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. destruct W as (W0 & W1 & W2). split; [lia|]. split; [lia|].
    intros i Hi. replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W2. lia.
Qed.

Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A HA. unfold rw_cells, cells_at, bytes_at, wr_at. cbn.
  repeat split; try lia; try exact I.
  all: try (intros i Hi; exfalso; lia).
Qed.

Lemma CB_u8arr : forall m A n bs, rw_cells asegs m A [CB n bs] -> u8arr asegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[WF B] W]. cbn in WF. destruct WF as [LEN _].
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W.
  split; [| exact LEN]. split; [exact B|]. rewrite LEN. exact W.
Qed.

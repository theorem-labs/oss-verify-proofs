(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_cache_defs R_prim_defs R_popfree_T R_getfrom R_return.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma carve_nth_new : forall ws total auser size (i j : nat),
  (j < i)%nat -> Z.of_nat i <= total -> total <= Z.of_nat (length ws) ->
  nth_error (carve ws total auser size i) (Z.to_nat (total - 1 - Z.of_nat j)) =
  Some (Z_to_bv 64 ((auser + Z.of_nat j * size) / 16)).
Proof.
  intros ws total auser size i. induction i as [|i IH]; intros j Hj Hi Hl; [lia|].
  cbn [carve]. destruct (Nat.eq_dec j i) as [->|Hne].
  - apply nth_error_upd_same. rewrite carve_length. lia.
  - rewrite nth_error_upd_other by lia. apply IH; lia.
Qed.

Lemma carve_nth_other : forall ws total auser size (i : nat) (k : nat),
  Z.of_nat i <= total -> (Z.of_nat k < total - Z.of_nat i \/ total <= Z.of_nat k) ->
  nth_error (carve ws total auser size i) k = nth_error ws k.
Proof.
  intros ws total auser size i. induction i as [|i IH]; intros k Hi Hk; [reflexivity|].
  cbn [carve]. rewrite nth_error_upd_other by lia. apply IH; lia.
Qed.

Lemma carve_new_cp_ok : forall x, 0 <= x < 2^32 -> cp_ok (x / 16).
Proof. intros x Hx. unfold cp_ok. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.

Lemma dest_nth_copied : forall ws chs base (i j : nat),
  (j < i)%nat -> (i <= length chs)%nat ->
  nth_error (dest ws chs base i) j = Some (sx32 (nth (Z.to_nat base + j) ws (Z_to_bv 64 0))).
Proof.
  intros ws chs base i. induction i as [|i IH]; intros j Hj Hi; [lia|].
  cbn [dest]. destruct (Nat.eq_dec j i) as [->|Hne].
  - apply nth_error_upd_same. rewrite dest_length. lia.
  - rewrite nth_error_upd_other by lia. apply IH; lia.
Qed.

Lemma dest_nth_kept : forall ws chs base (i j : nat), (i <= j)%nat -> nth_error (dest ws chs base i) j = nth_error chs j.
Proof.
  intros ws chs base i. induction i as [|i IH]; intros j Hj; [reflexivity|].
  cbn [dest]. rewrite nth_error_upd_other by lia. apply IH; lia.
Qed.

Lemma dest2_nth_lo : forall ws chs nf cb (i k : nat), (k < Z.to_nat nf)%nat ->
  nth_error (dest2 ws chs nf cb i) k = nth_error ws k.
Proof.
  intros ws chs nf cb i. induction i as [|i IH]; intros k Hk; [reflexivity|].
  cbn [dest2]. rewrite nth_error_upd_other by lia. apply IH; lia.
Qed.

Lemma dest2_nth_mid : forall ws chs nf cb (i j : nat), (j < i)%nat -> (Z.to_nat nf + i <= length ws)%nat ->
  nth_error (dest2 ws chs nf cb i) (Z.to_nat nf + j) = Some (sx32 (nth (Z.to_nat cb + j) chs (Z_to_bv 64 0))).
Proof.
  intros ws chs nf cb i. induction i as [|i IH]; intros j Hj Hl; [lia|].
  cbn [dest2]. destruct (Nat.eq_dec j i) as [->|Hne].
  - apply nth_error_upd_same. rewrite dest2_length. lia.
  - rewrite nth_error_upd_other by lia. apply IH; lia.
Qed.

Lemma dest2_nth_hi : forall ws chs nf cb (i k : nat), (Z.to_nat nf + i <= k)%nat ->
  nth_error (dest2 ws chs nf cb i) k = nth_error ws k.
Proof.
  intros ws chs nf cb i. induction i as [|i IH]; intros k Hk; [reflexivity|].
  cbn [dest2]. rewrite nth_error_upd_other by lia. apply IH; lia.
Qed.

Lemma sx32_zw : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx32_cp : forall z, cp_ok z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z [H1 H2]. apply sx32_zw. lia. Qed.

Lemma fl_prefix_nth : forall (fl : list Z) ws (k : nat),
  firstn (length fl) ws = map zw fl -> (k < length fl)%nat ->
  nth k ws (Z_to_bv 64 0) = zw (nth k fl 0).
Proof.
  intros fl ws k Hp Hk.
  assert (E : nth k (firstn (length fl) ws) (Z_to_bv 64 0) = nth k ws (Z_to_bv 64 0)).
  { rewrite nth_firstn. destruct (Nat.ltb_spec k (length fl)); [reflexivity| lia]. }
  rewrite <- E, Hp. rewrite (nth_indep (map zw fl) (Z_to_bv 64 0) (zw 0)) by (rewrite map_length; exact Hk).
  apply map_nth.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint draw_loop (fuel : nat) (pl : list Z) (size rolling result : Z) : Z * Z :=
  match fuel with
  | O => (result, size)
  | S f =>
    if (0 <? rolling) && (0 <? size) then
      let next := Znth (size - 1) pl in
      draw_loop f pl (size - 1) (rolling / 2^8) (Z.lor (u32 (result * 2^8)) next)
    else (result, size)
  end.

(* [comment removed for export] *)
Definition uint32Range (pl : list Z) (size min max : Z) : Z * Z :=
  let range := u32 (max - min) in
  let '(result, size') := draw_loop 4%nat pl size range 0 in
  if range =? 2^32 - 1 then (result, size')
  else (u32 (min + result mod (range + 1)), size').

(* [comment removed for export] *)
Definition int32Range (pl : list Z) (size min max : Z) : Z * Z :=
  if min <? 0 then
    let '(r, size') := uint32Range pl size 0 (max - min) in (r + min, size')
  else uint32Range pl size min max.

Lemma lor_byte a b : 0 <= a -> 0 <= b < 256 -> Z.lor (a * 2^8) b = a * 2^8 + b.
Proof.
  intros. rewrite <- Z.lxor_lor.
  - symmetry. apply Z.add_nocarry_lxor.
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8).
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b); [apply andb_false_r|lia|].
      destruct (Z.eq_dec b 0). subst; simpl; lia. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^8); [simpl; lia|]. apply Z.pow_le_mono_r; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8).
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b); [apply andb_false_r|lia|].
      destruct (Z.eq_dec b 0). subst; simpl; lia. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^8); [simpl; lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma draw_loop_spec fuel : forall pl size rolling result,
  all_bytes pl -> 0 <= size -> 0 <= rolling < 2^(8 * Z.of_nat fuel) ->
  8 * Z.of_nat fuel <= 32 -> 0 <= result < 2^(32 - 8 * Z.of_nat fuel) ->
  let '(r, size') := draw_loop fuel pl size rolling result in
  0 <= size' <= size /\ 0 <= r < 2^32 /\ (rolling = 0 -> r = result /\ size' = size).
Proof.
  induction fuel; intros pl size rolling result HB Hs Hr Hf Hres; cbn [draw_loop].
  - cbn [Z.of_nat] in *. rewrite Z.mul_0_r, Z.sub_0_r in Hres. rewrite Z.mul_0_r, Z.pow_0_r in Hr. lia.
  - assert (Hp : 2^(8 * Z.of_nat (S fuel)) = 2^8 * 2^(8 * Z.of_nat fuel)).
    { replace (8 * Z.of_nat (S fuel)) with (8 + 8 * Z.of_nat fuel) by lia. apply Z.pow_add_r; lia. }
    assert (Hq : 2^(32 - 8 * Z.of_nat fuel) = 2^8 * 2^(32 - 8 * Z.of_nat (S fuel))).
    { replace (32 - 8 * Z.of_nat fuel) with (8 + (32 - 8 * Z.of_nat (S fuel))) by lia. apply Z.pow_add_r; lia. }
    assert (2^(32 - 8 * Z.of_nat fuel) <= 2^32) by (apply Z.pow_le_mono_r; lia).
    destruct (Z.ltb_spec 0 rolling); destruct (Z.ltb_spec 0 size); cbn [andb]; try lia.
    pose proof (HB (size - 1)) as Hb.
    rewrite Hp in *.
    assert (0 < 2^(8 * Z.of_nat fuel)) by (apply pow2_pos; lia).
    rewrite (u32_id (result * 2^8)) by (change (2^8) with 256 in *; nia).
    rewrite lor_byte by lia.
    specialize (IHfuel pl (size - 1) (rolling / 2^8) (result * 2^8 + Znth (size - 1) pl) HB ltac:(lia)).
    destruct (draw_loop fuel pl (size - 1) (rolling / 2^8) (result * 2^8 + Znth (size - 1) pl)) as [r size'].
    assert (0 <= rolling / 2^8 < 2^(8 * Z.of_nat fuel)).
    { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; [lia|]. lia. }
    change (2^8) with 256 in *.
    destruct IHfuel as (A & B & C); try nia.
Qed.

Lemma uint32Range_spec pl size min max :
  all_bytes pl -> 0 <= size -> 0 <= min <= max -> max < 2^32 ->
  let '(r, size') := uint32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size /\ (min = max -> size' = size).
Proof.
  intros HB Hs Hmm Hmax. unfold uint32Range.
  rewrite (u32_id (max - min)) by lia.
  pose proof (draw_loop_spec 4 pl size (max - min) 0 HB Hs) as DL.
  destruct (draw_loop 4 pl size (max - min) 0) as [r size'].
  destruct DL as (A & B & C); try (simpl; lia).
  destruct (Z.eqb_spec (max - min) (2^32 - 1)).
  - repeat split; try lia.
  - pose proof (Z.mod_pos_bound r (max - min + 1) ltac:(lia)).
    rewrite u32_id by lia. repeat split; try lia.
Qed.

Lemma int32Range_spec pl size min max :
  all_bytes pl -> 0 <= size -> -2^31 <= min <= max -> max < 2^31 ->
  let '(r, size') := int32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size.
Proof.
  intros HB Hs Hmm Hmax. change (2^31) with 2147483648 in *. unfold int32Range. destruct (Z.ltb_spec min 0).
  - pose proof (uint32Range_spec pl size 0 (max - min) HB Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size 0 (max - min)) as [r size']. lia.
  - pose proof (uint32Range_spec pl size min max HB Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size min max) as [r size']. lia.
Qed.

(* [comment removed for export] *)
Lemma draw_loop_size fuel : forall pl size rolling result,
  0 <= size -> let '(_, size') := draw_loop fuel pl size rolling result in 0 <= size' <= size.
Proof.
  induction fuel; intros pl size rolling result Hs; cbn [draw_loop]; [lia|].
  destruct (Z.ltb_spec 0 rolling); destruct (Z.ltb_spec 0 size); cbn [andb]; try lia.
  specialize (IHfuel pl (size - 1) (rolling / 2^8) (Z.lor (u32 (result * 2^8)) (Znth (size - 1) pl)) ltac:(lia)).
  destruct (draw_loop fuel pl (size - 1) (rolling / 2^8) (Z.lor (u32 (result * 2^8)) (Znth (size - 1) pl))) as [r size'].
  lia.
Qed.

Lemma uint32Range_range pl size min max :
  0 <= size -> 0 <= min <= max -> max < 2^32 -> max - min < 2^32 - 1 ->
  let '(r, size') := uint32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size.
Proof.
  intros Hs Hmm Hmax Hr. change (2^32) with 4294967296 in *. unfold uint32Range.
  rewrite (u32_id (max - min)) by (change (2^32) with 4294967296; lia).
  pose proof (draw_loop_size 4 pl size (max - min) 0 Hs) as DL.
  destruct (draw_loop 4 pl size (max - min) 0) as [r size'].
  change (2^32) with 4294967296.
  destruct (Z.eqb_spec (max - min) (4294967296 - 1)); [lia|].
  pose proof (Z.mod_pos_bound r (max - min + 1) ltac:(lia)).
  rewrite u32_id by (change (2^32) with 4294967296; lia). lia.
Qed.

Lemma int32Range_range pl size min max :
  0 <= size -> -2^31 <= min <= max -> max < 2^31 -> max - min < 2^32 - 1 ->
  let '(r, size') := int32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size.
Proof.
  intros Hs Hmm Hmax Hr. change (2^31) with 2147483648 in *. change (2^32) with 4294967296 in *.
  unfold int32Range. destruct (Z.ltb_spec min 0).
  - pose proof (uint32Range_range pl size 0 (max - min) Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)
                  ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size 0 (max - min)) as [r size']. lia.
  - pose proof (uint32Range_range pl size min max Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)
                  ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size min max) as [r size']. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition producer_contract (size newSize : Z) : Z * Z :=
  let eff := Z.min newSize size in (size - eff, eff).

(* [comment removed for export] *)
Definition reserve_data_prefix (pl : list Z) (size : Z) : Z * Z :=
  let '(slice, size1) := uint32Range pl size 0 size in
  producer_contract size1 slice.

Lemma producer_contract_range size newSize : 0 <= size -> 0 <= newSize ->
  let '(rem, eff) := producer_contract size newSize in 0 <= rem /\ 0 <= eff /\ rem + eff = size.
Proof. intros H1 H2. unfold producer_contract. lia. Qed.

Lemma reserve_data_prefix_range pl size : 0 <= size < 2^32 - 1 ->
  let '(rem, eff) := reserve_data_prefix pl size in 0 <= rem /\ 0 <= eff /\ rem + eff <= size.
Proof.
  intros H. unfold reserve_data_prefix.
  pose proof (uint32Range_range pl size 0 size ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as U.
  destruct (uint32Range pl size 0 size) as [slice size1]. unfold producer_contract. lia.
Qed.

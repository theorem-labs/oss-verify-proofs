(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition kLowShadowBeg : Z := kShadowBase.                          (* [comment removed for export] *)
Definition kLowShadowEnd : Z := mem_to_shadow kLowMemEnd.              (* [comment removed for export] *)
Definition kLowShadowMapBeg : Z := kShadowBase - kPageSize.           (* [comment removed for export] *)
Definition kLowAppEnd : Z := kLowShadowMapBeg.                        (* [comment removed for export] *)
Definition kHighShadowBeg : Z := mem_to_shadow kHighMemBeg.            (* [comment removed for export] *)
Definition kHighShadowEnd : Z := mem_to_shadow kHighMemEnd.            (* [comment removed for export] *)
Definition kShadowGapBeg : Z := kLowShadowEnd + 1.                     (* [comment removed for export] *)
Definition kShadowGapEnd : Z := kHighShadowBeg - 1.
(* [comment removed for export] *)
Definition low_shadow_map : Z * Z := (kLowShadowMapBeg, 2^28).
Definition shadow_gap_map : Z * Z := (kShadowGapBeg, 2^41).
Definition high_shadow_map : Z * Z := (kHighShadowBeg, kHighShadowEnd + 1 - kHighShadowBeg).

Lemma kLowShadowEnd_val : kLowShadowEnd = 0x8fff6fff. Proof. reflexivity. Qed.
Lemma kLowAppEnd_val : kLowAppEnd = 0x7fff7000. Proof. reflexivity. Qed.
Lemma kHighShadowBeg_val : kHighShadowBeg = 0x2008fff7000. Proof. reflexivity. Qed.
Lemma kHighShadowEnd_val : kHighShadowEnd = 0x10007fff7fff. Proof. reflexivity. Qed.
Lemma kShadowGapBeg_val : kShadowGapBeg = 0x8fff7000. Proof. reflexivity. Qed.
Lemma high_shadow_map_val : high_shadow_map = (0x2008fff7000, 0xdfff0001000). Proof. reflexivity. Qed.
Lemma shadow_maps_contiguous : kLowShadowMapBeg + 2^28 = kShadowGapBeg /\ kShadowGapBeg + 2^41 = kHighShadowBeg
  /\ kHighShadowEnd + 1 = kHighMemBeg.
Proof. repeat split; reflexivity. Qed.

Section RC.
Context {RC__ : RunCeiling}.

(* [comment removed for export] *)
Definition app_mem (r n : Z) : Prop :=
  (0 < r /\ r + n <= kLowAppEnd) \/ (kHighMemBeg <= r /\ r + n <= alloc_ceiling).
Definition app_mem_b (r n : Z) : bool :=
  ((0 <? r) && (r + n <=? kLowAppEnd)) || ((kHighMemBeg <=? r) && (r + n <=? alloc_ceiling)).

Lemma app_mem_b_iff : forall r n, app_mem_b r n = true <-> app_mem r n.
Proof. intros r n. unfold app_mem_b, app_mem. rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le, Z.ltb_lt. tauto. Qed.

(* [comment removed for export] *)
Lemma alloc_ceiling_le_high_end : alloc_ceiling <= kHighMemEnd + 1 - 8388608.
Proof. pose proof alloc_ceiling_range. unfold kHighMemEnd. lia. Qed.
Lemma kHighMemBeg_lt_ceiling : kHighMemBeg + 2^46 <= alloc_ceiling.
Proof. pose proof alloc_ceiling_range. rewrite kHighMemBeg_val. lia. Qed.

(* [comment removed for export] *)
Lemma app_mem_in_mem : forall r n a, app_mem r n -> 0 <= n -> r <= a < r + n -> addr_is_in_mem a = true.
Proof.
  intros r n a H Hn Ha. unfold addr_is_in_mem. pose proof alloc_ceiling_le_high_end as C.
  unfold app_mem, kLowAppEnd, kLowShadowMapBeg, kLowMemEnd, kShadowBase, kPageSize in H. unfold kLowMemEnd, kShadowBase.
  rewrite Bool.orb_true_iff, Bool.andb_true_iff, !Z.leb_le. lia.
Qed.

Lemma app_mem_not_shadow : forall r n a, app_mem r n -> 0 <= n -> r <= a < r + n ->
  a < kLowShadowMapBeg \/ kHighShadowEnd < a.
Proof.
  intros r n a H Hn Ha. unfold app_mem, kLowAppEnd in H. rewrite kHighShadowEnd_val. rewrite kHighMemBeg_val in H.
  unfold kLowShadowMapBeg, kShadowBase, kPageSize in *. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_of_app_low : forall r n a, 0 < r -> r + n <= kLowAppEnd -> 0 <= n -> r <= a < r + n ->
  kLowShadowBeg <= mem_to_shadow a <= kLowShadowEnd.
Proof.
  intros r n a Hr Hn Hn0 Ha. rewrite kLowAppEnd_val in Hn.
  assert (A0 : 0 <= a / 8) by (apply Z.div_pos; lia).
  assert (A1 : a / 8 <= kLowMemEnd / 8) by (apply Z.div_le_mono; [lia| unfold kLowMemEnd, kShadowBase; lia]).
  unfold kLowShadowBeg, kLowShadowEnd, mem_to_shadow. lia.
Qed.
Lemma shadow_of_app_high : forall r n a, kHighMemBeg <= r -> r + n <= alloc_ceiling -> 0 <= n -> r <= a < r + n ->
  kHighShadowBeg <= mem_to_shadow a <= kHighShadowEnd.
Proof.
  intros r n a Hr Hn Hn0 Ha. pose proof alloc_ceiling_le_high_end as C.
  assert (A0 : kHighMemBeg / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (A1 : a / 8 <= kHighMemEnd / 8) by (apply Z.div_le_mono; lia).
  unfold kHighShadowBeg, kHighShadowEnd, mem_to_shadow. lia.
Qed.
Lemma shadow_of_app_mem : forall r n a, app_mem r n -> 0 <= n -> r <= a < r + n ->
  (kLowShadowBeg <= mem_to_shadow a <= kLowShadowEnd) \/ (kHighShadowBeg <= mem_to_shadow a <= kHighShadowEnd).
Proof.
  intros r n a [[H1 H2]|[H1 H2]] Hn Ha; [left; eapply shadow_of_app_low; eauto| right; eapply shadow_of_app_high; eauto].
Qed.

(* [comment removed for export] *)
Lemma shadow_disjoint_app : forall r n a r' n' a', app_mem r n -> 0 <= n -> r <= a < r + n ->
  app_mem r' n' -> 0 <= n' -> r' <= a' < r' + n' -> mem_to_shadow a <> a'.
Proof.
  intros r n a r' n' a' H Hn Ha H' Hn' Ha'.
  pose proof (shadow_of_app_mem r n a H Hn Ha) as S. pose proof (app_mem_not_shadow r' n' a' H' Hn' Ha') as A.
  rewrite kLowShadowEnd_val, kHighShadowBeg_val, kHighShadowEnd_val in S. unfold kLowShadowBeg, kShadowBase in S.
  rewrite kHighShadowEnd_val in A. unfold kLowShadowMapBeg, kShadowBase, kPageSize in A. lia.
Qed.

(* [comment removed for export] *)
Definition app_addr (a : Z) : Prop := (0 < a /\ a < kLowAppEnd) \/ (kHighMemBeg <= a /\ a < alloc_ceiling).
Definition sh_band (a : Z) : Prop := (kLowShadowBeg <= a <= kLowShadowEnd) \/ (kHighShadowBeg <= a <= kHighShadowEnd).

Lemma app_mem_addr : forall r n a, app_mem r n -> r <= a < r + n -> app_addr a.
Proof. intros r n a H Ha. unfold app_mem in H. unfold app_addr. lia. Qed.

(* [comment removed for export] *)
Lemma sh_band_of_granule : forall x, (0 <= x < kLowAppEnd \/ kHighMemBeg <= x <= kHighMemEnd) -> sh_band (mem_to_shadow x).
Proof.
  intros x [Hx|Hx]; unfold sh_band.
  - left. assert (A0 : 0 <= x / 8) by (apply Z.div_pos; lia).
    assert (A1 : x / 8 <= kLowMemEnd / 8) by (apply Z.div_le_mono; [lia| rewrite kLowAppEnd_val in Hx; unfold kLowMemEnd, kShadowBase; lia]).
    unfold kLowShadowBeg, kLowShadowEnd, mem_to_shadow. lia.
  - right. assert (A0 : kHighMemBeg / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (A1 : x / 8 <= kHighMemEnd / 8) by (apply Z.div_le_mono; lia).
    unfold kHighShadowBeg, kHighShadowEnd, mem_to_shadow. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_band_not_app : forall a, sh_band a -> ~ app_addr a.
Proof.
  intros a H H'. unfold sh_band, app_addr in *. pose proof alloc_ceiling_le_high_end.
  rewrite kLowShadowEnd_val, kHighShadowBeg_val, kHighShadowEnd_val, kLowAppEnd_val, kHighMemBeg_val in *.
  unfold kLowShadowBeg, kShadowBase, kHighMemEnd in *. lia.
Qed.
Lemma sh_band_below_ceiling : forall a, sh_band a -> kLowAppEnd < a < kHighMemBeg.
Proof.
  intros a H. unfold sh_band in H. rewrite kLowShadowEnd_val, kHighShadowBeg_val, kHighShadowEnd_val, kLowAppEnd_val, kHighMemBeg_val in *.
  unfold kLowShadowBeg, kShadowBase in *. lia.
Qed.
Lemma app_addr_below_ceiling : forall a, app_addr a -> 0 < a < alloc_ceiling.
Proof. intros a H. unfold app_addr in H. pose proof kHighMemBeg_lt_ceiling. rewrite kLowAppEnd_val, kHighMemBeg_val in *. lia. Qed.

End RC.

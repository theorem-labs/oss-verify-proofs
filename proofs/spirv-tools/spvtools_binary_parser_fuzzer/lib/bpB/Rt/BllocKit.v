(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocWf.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac hci :=
  try (lazymatch goal with HH : HeapCeil |- _ =>
         repeat (match goal with
                 | |- context [?X] => is_evar X; let T := type of X in constr_eq T HeapCeil; unify X HH
                 end)
       end).

Lemma region_beg_eq : forall st c, region_beg st c = as_space_beg st + c * 2^32.
Proof. intros st c. unfold region_beg, kRegionSizeLog. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma free_array_base_eq : forall st c, free_array_base st c = region_beg st c + kFreeArrayOffset.
Proof. reflexivity. Qed.

Lemma compact_to_addr_eq : forall st c cp, compact_to_addr st c cp = region_beg st c + cp * 16.
Proof. intros st c cp. unfold compact_to_addr, kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. lia. Qed.

Lemma shiftl4 : forall cp, Z.shiftl cp kCompactPtrScale = cp * 16.
Proof. intros cp. unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. lia. Qed.

Lemma regions_disjoint : forall st c c', 0 <= c -> 0 <= c' -> c <> c' ->
  region_beg st c + 2^32 <= region_beg st c' \/ region_beg st c' + 2^32 <= region_beg st c.
Proof. intros st c c' Hc Hc' Hne. rewrite !region_beg_eq. nia. Qed.

Lemma region_in_space : forall st c, 0 <= c < 32 ->
  as_space_beg st <= region_beg st c /\ region_beg st c + 2^32 <= as_space_beg st + kSpaceSize.
Proof. intros st c Hc. rewrite region_beg_eq. unfold kSpaceSize. nia. Qed.

Lemma class_of_addr_region : forall st c off, 0 <= c < 32 -> 0 <= off < 2^32 ->
  class_of_addr st (region_beg st c + off) = c.
Proof.
  intros st c off Hc Hoff. unfold class_of_addr, kRegionSizeLog. rewrite region_beg_eq.
  replace (as_space_beg st + c * 2^32 + off - as_space_beg st) with (off + c * 2^32) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia.
  rewrite Z.add_0_l. rewrite Z.land_ones with (n := 5) by lia. change (Z.ones 5) with 31. apply Z.mod_small. lia.
Qed.

Lemma in_primary_region : forall st c off, 0 <= c < 32 -> 0 <= off < 2^32 ->
  in_primary st (region_beg st c + off) = true.
Proof.
  intros st c off Hc Hoff. unfold in_primary. pose proof (region_in_space st c Hc).
  apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Definition carved (st : astate) (c a : Z) : Prop :=
  0 <= c < kNumClasses /\ class_size c <> 0 /\ 0 <= a - region_beg st c
  /\ (a - region_beg st c) mod class_size c = 0
  /\ a - region_beg st c + class_size c <= rg_allocated_user (get_region st c).

Lemma carved_range : forall st c a, WF st -> carved st c a ->
  region_beg st c <= a /\ a + class_size c <= region_beg st c + kFreeArrayOffset /\ 0 < class_size c <= 65536.
Proof.
  intros st c a W (Hc & Hsz & H0 & Hm & Hle). pose proof (WF_region st c W Hc) as RO.
  pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_bound _ _ RO). pose proof (class_size_table_facts c Hc).
  unfold kUserMapSize in *. lia.
Qed.

Lemma carved_sep : forall st c a c' a', WF st -> carved st c a -> carved st c' a' ->
  (c = c' /\ a = a') \/ a + class_size c <= a' \/ a' + class_size c' <= a.
Proof.
  intros st c a c' a' W Ca Ca'.
  pose proof (carved_range st c a W Ca) as (R1 & R2 & R3). pose proof (carved_range st c' a' W Ca') as (R1' & R2' & R3').
  destruct Ca as (Hc & Hsz & H0 & Hm & Hle). destruct Ca' as (Hc' & Hsz' & H0' & Hm' & Hle').
  destruct (Z.eq_dec c c') as [<-|Hne].
  - destruct (Z.eq_dec a a') as [<-|Hna]; [left; auto| right].
    destruct (proj1 (Z.mod_divide (a - region_beg st c) (class_size c) Hsz) Hm) as [q Hq].
    destruct (proj1 (Z.mod_divide (a' - region_beg st c) (class_size c) Hsz) Hm') as [q' Hq'].
    assert (q <> q') by (intros ->; lia).
    destruct (Z.lt_ge_cases q q'); nia.
  - right. unfold kFreeArrayOffset in *.
    destruct (regions_disjoint st c c' ltac:(lia) ltac:(lia) Hne); lia.
Qed.

Lemma mult_below : forall s x y, 0 < s -> x mod s = 0 -> y mod s = 0 -> x < y -> x + s <= y.
Proof.
  intros s x y Hs Hx Hy Hlt.
  destruct (proj1 (Z.mod_divide x s ltac:(lia)) Hx) as [q ->].
  destruct (proj1 (Z.mod_divide y s ltac:(lia)) Hy) as [q' ->].
  assert (q < q') by nia. nia.
Qed.

Lemma carved_of_elem : forall st c cp, WF st -> 0 <= c < kNumClasses ->
  0 <= cp -> Z.shiftl cp kCompactPtrScale < rg_allocated_user (get_region st c) ->
  class_size c <> 0 -> Z.shiftl cp kCompactPtrScale mod class_size c = 0 ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st c cp W Hc A B C D. rewrite shiftl4 in *. rewrite compact_to_addr_eq. unfold carved.
  replace (region_beg st c + cp * 16 - region_beg st c) with (cp * 16) by lia.
  pose proof (class_size_table_facts c Hc) as T. pose proof (ro_alloc_mod _ _ (WF_region st c W Hc) C) as AM.
  repeat split; try lia. apply mult_below; lia.
Qed.

Lemma carved_free : forall st c cp, WF st -> 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st c cp W Hc Hin. pose proof (ro_fa_elems _ _ (WF_region st c W Hc) cp Hin) as (A & B & C & D).
  apply carved_of_elem; assumption.
Qed.

Lemma carved_cache : forall st c cp, WF st -> 0 <= c < kNumClasses -> In cp (pc_chunks (get_pc st c)) ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st c cp W Hc Hin. pose proof (co_elems _ _ (WF_cache st c W Hc) cp Hin) as (A & B & C & D).
  apply carved_of_elem; assumption.
Qed.

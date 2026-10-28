(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk StreamSim AsanPlanSoundSums ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCellEx_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Fixpoint art_rseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match seg_rom segs a with Some _ => art_rseg_ok segs (a + 1)%bv n' | None => false end
  end.

Lemma art_bv_succ : forall a : word, U a + 1 < 2 ^ 64 -> U (a + 1)%bv = U a + 1.
Proof.
  intros a H. rewrite bv_add_unsigned. change (bv_unsigned (1 : bv 64)%bv) with 1. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2 ^ 64) in R. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma art_rseg_pt : forall segs n (a : word), U a + Z.of_nat n < 2 ^ 64 -> art_rseg_ok segs a n = true ->
  forall x : word, U a <= U x < U a + Z.of_nat n -> seg_rom segs x <> None.
Proof.
  induction n as [|n IH]; intros a Hn OK x Hx; [lia|].
  cbn [art_rseg_ok] in OK. destruct (seg_rom segs a) as [b|] eqn:E; [|discriminate].
  destruct (Z.eq_dec (U x) (U a)) as [Ex|Nx].
  - apply bv_eq in Ex. subst x. rewrite E. discriminate.
  - apply (IH (a + 1)%bv); [rewrite art_bv_succ by lia; lia | exact OK | rewrite art_bv_succ by lia; lia].
Qed.

Lemma art_rdn_defined_v : forall n (M : word -> option byte) a, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall x : word, a <= U x < a + Z.of_nat n -> M x <> None \/ seg_rom ASEGS x <> None) ->
  exists bs, rdn ASEGS M (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros M a Ha Hn D; [exists []; split; reflexivity|].
  cbn [rdn]. assert (Ua : U (Z_to_bv 64 a : word) = a) by (apply art_u_lit; lia).
  assert (exists b, match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom ASEGS (Z_to_bv 64 a) end = Some b) as (b & Eb).
  { destruct (D (Z_to_bv 64 a) ltac:(rewrite Ua; lia)) as [N|N].
    - destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|congruence].
    - destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. destruct (seg_rom ASEGS (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|congruence]. }
  rewrite Eb.
  replace ((Z_to_bv 64 a + 1)%bv : word) with (Z_to_bv 64 (a + 1) : word).
  2:{ apply bv_eq. rewrite bv_add_unsigned, Ua. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      change (bv_unsigned (1 : bv 64)%bv) with 1. rewrite !Z.mod_small by lia. reflexivity. }
  destruct (IH M (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply D; lia)) as (bs & R & Lb).
  rewrite R. exists (b :: bs). split; [reflexivity|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma art_rseg_secwin : art_rseg_ok ASEGS (Z_to_bv 64 0x13c618) 1024 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma art_wseg_secwin : wseg_ok ASEGS (Z_to_bv 64 0x13c618) 1024 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma art_img_cell_exists : forall (M : word -> option byte) a (n : nat), (n <= 8)%nat -> 0x13c618 <= a -> a + Z.of_nat n <= 0x13c618 + 1024 ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ cellA M a n v.
Proof.
  intros M a n Hn8 Ha Hn.
  destruct (art_rdn_defined_v n M a ltac:(lia) ltac:(lia)) as (bs & R & Lb).
  { intros x Hx. right. apply (art_rseg_pt ASEGS 1024 (Z_to_bv 64 0x13c618)); [rewrite art_u_lit by lia; lia | exact art_rseg_secwin | rewrite art_u_lit by lia; lia]. }
  exists (bytes_le_to_Z bs). split.
  - pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B. split; [exact B0|exact B].
  - unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.

Lemma art_img_wr : forall (M : word -> option byte) a n, 0x13c618 <= a -> 0 <= n -> a + n <= 0x13c618 + 1024 -> wrA M a n.
Proof.
  intros M a n Ha Hn0 Hn d k Hd Hk.
  apply (store_ok_window ASEGS M (Z_to_bv 64 0x13c618) (Z_to_bv 64 (a + d)) 1024%nat k 0x13c618 (0x13c618 + 1024));
    first [exact art_wseg_secwin | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.

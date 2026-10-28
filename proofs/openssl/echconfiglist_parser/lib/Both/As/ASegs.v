(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Module RefMemImage.
  Module Ref.
    Definition loaded_segments := AsanUbsan.M.loaded_segments.
  End Ref.
  Definition RefMemImage_loaded_segments := AsanUbsan.AsanUbsan_loaded_segments.
  Definition RefMemImage_segment_000 := AsanUbsan.AsanUbsan_segment_000.
  Definition RefMemImage_segment_001 := AsanUbsan.AsanUbsan_segment_001.
  Definition RefMemImage_segment_002 := AsanUbsan.AsanUbsan_segment_002.
  Definition RefMemImage_segment_003 := AsanUbsan.AsanUbsan_segment_003.
End RefMemImage.

Module AgentMemImage.
  Module Agent.
    Definition loaded_segments := AsanUbsan.M.loaded_segments.
  End Agent.
End AgentMemImage.

Definition asegs := RefMemImage.Ref.loaded_segments.

(* [comment removed for export] *)
Definition AIMG_LO  : Z := 0x10000.    (* [comment removed for export] *)
Definition ARO_HI   : Z := 0x195000.    (* [comment removed for export] *)
Definition ATEXT_LO : Z := 0x195000.    (* [comment removed for export] *)
Definition ATEXT_HI : Z := 0x571000.
Definition ARW_LO   : Z := 0x571000.   (* [comment removed for export] *)
Definition ARW1_HI  : Z := 0x5ea000.   (* [comment removed for export] *)
Definition AIMG_TOP : Z := 0xc04000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ALOWSH  : word * word := (Z_to_bv 64 0x7fff7000,    Z_to_bv 64 0x10000000).     (* [comment removed for export] *)
Definition AHIGHSH : word * word := (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000).  (* [comment removed for export] *)
Definition AGAP    : word * word := (Z_to_bv 64 0x8fff7000,    Z_to_bv 64 0x20000000000).  (* [comment removed for export] *)
Definition ASHADOW_BASE : Z := 0x7fff8000.                                                  (* [comment removed for export] *)

Lemma asegs_nowrap : segs_nowrapb asegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asegs_below_top : forall seg, In seg asegs ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= AIMG_TOP)%Z.
Proof.
  intros seg Hin. unfold asegs, RefMemImage.Ref.loaded_segments, M.loaded_segments, AsanUbsan_loaded_segments in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn -[Z.add Z.le Z.of_N]; unfold AIMG_TOP; lia.
Qed.

Lemma asegs_above_lo : forall seg, In seg asegs ->
  (AIMG_LO <= Z.of_N (seg_base seg))%Z.
Proof.
  intros seg Hin. unfold asegs, RefMemImage.Ref.loaded_segments, M.loaded_segments, AsanUbsan_loaded_segments in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn -[Z.le Z.of_N]; unfold AIMG_LO; lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_ranges_okb_asan_fixed : lazy_ranges_okb asegs [ALOWSH; AHIGHSH; AGAP] = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lazy_ranges_okb_asan_fixed' : lazy_ranges_okb asegs [ALOWSH; AGAP; AHIGHSH] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lazy_ranges_okb_asan_nil : lazy_ranges_okb asegs [] = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lazy_range_okb_above_image : forall (lo sz : word),
  (AIMG_TOP <= bv_unsigned lo)%Z ->
  (bv_unsigned lo + bv_unsigned sz <= 2 ^ 64)%Z ->
  lazy_range_okb asegs (lo, sz) = true.
Proof.
  intros lo sz Hlo Hnw. apply (lazy_range_okb_above asegs lo sz AIMG_TOP); [| exact Hlo | exact Hnw].
  exact asegs_below_top.
Qed.

(* [comment removed for export] *)
Lemma lazy_range_okb_below_image : forall (lo sz : word),
  (bv_unsigned lo + bv_unsigned sz <= AIMG_LO)%Z ->
  lazy_range_okb asegs (lo, sz) = true.
Proof.
  intros lo sz Hhi. apply lazy_range_okb_intro; [unfold AIMG_LO in Hhi; lia|].
  intros seg Hin. right. pose proof (asegs_above_lo seg Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_range_okb_outside_image : forall (lo sz : word),
  (bv_unsigned lo + bv_unsigned sz <= AIMG_LO \/ AIMG_TOP <= bv_unsigned lo)%Z ->
  (bv_unsigned lo + bv_unsigned sz <= 2 ^ 64)%Z ->
  lazy_range_okb asegs (lo, sz) = true.
Proof.
  intros lo sz [H|H] Hnw; [apply lazy_range_okb_below_image; exact H | apply lazy_range_okb_above_image; assumption].
Qed.

Lemma lazy_ranges_okb_cons_above : forall (lo sz : word) L,
  lazy_ranges_okb asegs L = true ->
  (AIMG_TOP <= bv_unsigned lo)%Z ->
  (bv_unsigned lo + bv_unsigned sz <= 2 ^ 64)%Z ->
  lazy_ranges_okb asegs ((lo, sz) :: L) = true.
Proof.
  intros lo sz L HL Hlo Hnw. apply (proj2 (lazy_ranges_okb_cons asegs (lo, sz) L)).
  split; [apply lazy_range_okb_above_image; assumption | exact HL].
Qed.

Lemma lazy_ranges_okb_cons_outside : forall (lo sz : word) L,
  lazy_ranges_okb asegs L = true ->
  (bv_unsigned lo + bv_unsigned sz <= AIMG_LO \/ AIMG_TOP <= bv_unsigned lo)%Z ->
  (bv_unsigned lo + bv_unsigned sz <= 2 ^ 64)%Z ->
  lazy_ranges_okb asegs ((lo, sz) :: L) = true.
Proof.
  intros lo sz L HL Hout Hnw. apply (proj2 (lazy_ranges_okb_cons asegs (lo, sz) L)).
  split; [apply lazy_range_okb_outside_image; assumption | exact HL].
Qed.

(* [comment removed for export] *)
Lemma shadow_of_image_in_low : forall a : Z,
  (AIMG_LO <= a < AIMG_TOP)%Z ->
  (0x7fff7000 <= ASHADOW_BASE + a / 8 < 0x7fff7000 + 0x10000000)%Z.
Proof. intros a Ha. unfold AIMG_LO, AIMG_TOP, ASHADOW_BASE in *. lia. Qed.

Lemma shadow_of_low_in_low : forall a : Z,
  (0 <= a < 0x7fff7000)%Z ->
  (0x7fff7000 <= ASHADOW_BASE + a / 8 < 0x7fff7000 + 0x10000000)%Z.
Proof. intros a Ha. unfold ASHADOW_BASE in *. lia. Qed.

Lemma shadow_of_high_in_high : forall a : Z,
  (0x10007fff8000 <= a < 2 ^ 47)%Z ->
  (0x2008fff7000 <= ASHADOW_BASE + a / 8 < 0x2008fff7000 + 0xdfff0001000)%Z.
Proof. intros a Ha. unfold ASHADOW_BASE in *. lia. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.
Module NatCellEx.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRunsMem.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Fixpoint art_segs_in (segs : list Segment) (lo hi : Z) : bool :=
  match segs with
  | [] => true
  | s :: r => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi) && art_segs_in r lo hi
  end.

Lemma art_find_segment_none : forall segs lo hi x, art_segs_in segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s r IH]; intros lo hi x H Hx; [reflexivity|]. cbn [art_segs_in] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x H3 Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma art_asegs_in : art_segs_in ASEGS 0x10000 0x6b6000 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma art_wview_off : forall (M : word -> option byte) (x : word), (U x < 0x10000 \/ 0x6b6000 <= U x) -> wview ASEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x) as [b|]; [reflexivity|].
  rewrite (art_find_segment_none ASEGS 0x10000 0x6b6000 (U x) art_asegs_in Hx). reflexivity.
Qed.

Lemma art_rdn_defined : forall n (M : word -> option byte) a, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall x : word, a <= U x < a + Z.of_nat n -> M x <> None) ->
  exists bs, rdn ASEGS M (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros M a Ha Hn D; [exists []; split; reflexivity|].
  cbn [rdn]. assert (Ua : U (Z_to_bv 64 a : word) = a) by (apply art_u_lit; lia).
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|exfalso; apply (D (Z_to_bv 64 a)); [rewrite Ua; lia|exact E]].
  replace ((Z_to_bv 64 a + 1)%bv : word) with (Z_to_bv 64 (a + 1) : word).
  2:{ apply bv_eq. rewrite bv_add_unsigned, Ua. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      change (bv_unsigned (1 : bv 64)%bv) with 1. rewrite !Z.mod_small by lia. reflexivity. }
  destruct (IH M (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply D; lia)) as (bs & R & Lb).
  rewrite R. exists (b :: bs). split; [reflexivity|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma art_cell_exists : forall (M : word -> option byte) a (n : nat), (n <= 8)%nat -> (a + Z.of_nat n <= 0x10000 \/ 0x6b6000 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  wrA M a (Z.of_nat n) -> exists v, 0 <= v < 2 ^ 64 /\ cellA M a n v.
Proof.
  intros M a n Hn8 Hoff Ha Hn W.
  destruct (art_rdn_defined n M a Ha Hn) as (bs & R & Lb).
  { intros x Hx. pose proof (art_wr_wview ASEGS M a (Z.of_nat n) Ha Hn W x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
  exists (bytes_le_to_Z bs). split.
  - pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. split; [exact B0|]. eapply Z.lt_le_trans; [exact B|]. apply Z.pow_le_mono_r; lia.
  - unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.

(* [comment removed for export] *)
Lemma art_cell_exists_b : forall (M : word -> option byte) a (n : nat), (n <= 8)%nat -> (a + Z.of_nat n <= 0x10000 \/ 0x6b6000 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  wrA M a (Z.of_nat n) -> exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ cellA M a n v.
Proof.
  intros M a n Hn8 Hoff Ha Hn W.
  destruct (art_rdn_defined n M a Ha Hn) as (bs & R & Lb).
  { intros x Hx. pose proof (art_wr_wview ASEGS M a (Z.of_nat n) Ha Hn W x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
  exists (bytes_le_to_Z bs). split.
  - pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B. split; [exact B0|exact B].
  - unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.

End NatCellEx.
From Stdlib Require ZArith List Lia Bool. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0086. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
Module NatByteCell.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0086. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0086.NatFp OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0136.NatCellEx.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_seg_rom_off : forall x : word, (U x < 0x10000 \/ 0x6b6000 <= U x) -> seg_rom ASEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (art_find_segment_none ASEGS 0x10000 0x6b6000 (U x) art_asegs_in Hx). reflexivity.
Qed.

Lemma art_byte_of_cell1 : forall (M : word -> option byte) a v, (a < 0x10000 \/ 0x6b6000 <= a) -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  cellA M a 1 v -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Ha Ha' Hv C. unfold cell in C. cbn [rdn] in C. rewrite art_bytes1 in C by lia.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
  - injection C as C. rewrite C. reflexivity.
  - rewrite art_seg_rom_off in C by (rewrite art_u_lit by lia; exact Ha). discriminate C.
Qed.

Lemma art_cell1_iff_byte : forall (M : word -> option byte) a v, (a < 0x10000 \/ 0x6b6000 <= a) -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  (cellA M a 1 v <-> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v)).
Proof. intros M a v Ha Ha' Hv. split; [apply art_byte_of_cell1; assumption|apply art_cell1_of_byte; exact Hv]. Qed.

End NatByteCell.
Module NatImgCell.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRunsMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0136.NatCellEx.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
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
Lemma art_rseg_secwin : art_rseg_ok ASEGS (Z_to_bv 64 0x15c458) 1024 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma art_wseg_secwin : wseg_ok ASEGS (Z_to_bv 64 0x15c458) 1024 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma art_img_cell_exists : forall (M : word -> option byte) a (n : nat), (n <= 8)%nat -> 0x15c458 <= a -> a + Z.of_nat n <= 0x15c458 + 1024 ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ cellA M a n v.
Proof.
  intros M a n Hn8 Ha Hn.
  destruct (art_rdn_defined_v n M a ltac:(lia) ltac:(lia)) as (bs & R & Lb).
  { intros x Hx. right. apply (art_rseg_pt ASEGS 1024 (Z_to_bv 64 0x15c458)); [rewrite art_u_lit by lia; lia | exact art_rseg_secwin | rewrite art_u_lit by lia; lia]. }
  exists (bytes_le_to_Z bs). split.
  - pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B. split; [exact B0|exact B].
  - unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.

Lemma art_img_wr : forall (M : word -> option byte) a n, 0x15c458 <= a -> 0 <= n -> a + n <= 0x15c458 + 1024 -> wrA M a n.
Proof.
  intros M a n Ha Hn0 Hn d k Hd Hk.
  apply (store_ok_window ASEGS M (Z_to_bv 64 0x15c458) (Z_to_bv 64 (a + d)) 1024%nat k 0x15c458 (0x15c458 + 1024));
    first [exact art_wseg_secwin | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.

End NatImgCell.

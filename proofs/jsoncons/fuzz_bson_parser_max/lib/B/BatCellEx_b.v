(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanPlanSoundSums ArtMem ArtRuns ArtRunsMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
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

Lemma art_asegs_in : art_segs_in ASEGS 0x10000 0x696000 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma art_wview_off : forall (M : word -> option byte) (x : word), (U x < 0x10000 \/ 0x696000 <= U x) -> wview ASEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x) as [b|]; [reflexivity|].
  rewrite (art_find_segment_none ASEGS 0x10000 0x696000 (U x) art_asegs_in Hx). reflexivity.
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
Lemma art_cell_exists : forall (M : word -> option byte) a (n : nat), (n <= 8)%nat -> (a + Z.of_nat n <= 0x10000 \/ 0x696000 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
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
Lemma art_cell_exists_b : forall (M : word -> option byte) a (n : nat), (n <= 8)%nat -> (a + Z.of_nat n <= 0x10000 \/ 0x696000 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  wrA M a (Z.of_nat n) -> exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ cellA M a n v.
Proof.
  intros M a n Hn8 Hoff Ha Hn W.
  destruct (art_rdn_defined n M a Ha Hn) as (bs & R & Lb).
  { intros x Hx. pose proof (art_wr_wview ASEGS M a (Z.of_nat n) Ha Hn W x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
  exists (bytes_le_to_Z bs). split.
  - pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B. split; [exact B0|exact B].
  - unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.

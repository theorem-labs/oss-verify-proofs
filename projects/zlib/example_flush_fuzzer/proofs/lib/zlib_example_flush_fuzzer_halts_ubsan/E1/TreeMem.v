(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2 SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel DSLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Export TreeModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.

Lemma arrays_fc : forall m S s t, dsl_arrays segs m S s ->
  cells segs m (S + toff t) 4 2 (tsize t) (arr_get (tree_fc s t)).
Proof. intros m S s [| |] H; unfold dsl_arrays in H; cbn [toff tsize tree_fc]; tauto. Qed.

Lemma arrays_dl : forall m S s t, dsl_arrays segs m S s ->
  cells segs m (S + toff t + 2) 4 2 (tsize t) (arr_get (tree_dl s t)).
Proof.
  intros m S s [| |] H; unfold dsl_arrays in H; cbn [toff tsize tree_dl];
  [replace (S + 212 + 2) with (S + 214) by lia | replace (S + 2504 + 2) with (S + 2506) by lia
  | replace (S + 2748 + 2) with (S + 2750) by lia]; tauto.
Qed.

Lemma arrays_heap : forall m S s, dsl_arrays segs m S s -> cells segs m (S + 3008) 4 4 573 (arr_get (ds_heap s)).
Proof. intros m S s H. unfold dsl_arrays in H. tauto. Qed.

Lemma arrays_depth : forall m S s, dsl_arrays segs m S s -> cells segs m (S + 5308) 1 1 573 (arr_get (ds_depth s)).
Proof. intros m S s H. unfold dsl_arrays in H. tauto. Qed.

Lemma arrays_bl_count : forall m S s, dsl_arrays segs m S s -> cells segs m (S + 2976) 2 2 16 (arr_get (ds_bl_count s)).
Proof. intros m S s H. unfold dsl_arrays in H. tauto. Qed.


Local Ltac other Hc lo :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; apply cell_write_other; rewrite ?length_Z_to_le_bytes;
  [exact (Hc j Hj) | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia].

Lemma arrays_heap_set : forall m S s i v,
  dsl_arrays segs m S s -> tree_lens s -> 0 <= i < 573 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_arrays segs (wbytes m (zw (S + 3008 + 4 * i)) (Z_to_le_bytes 4 v)) S (heap_set s i v).
Proof.
  intros m S s i v H HL Hi HS0 HS1. unfold dsl_SIZE in HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & L8 & _).
  unfold dsl_arrays, heap_set. dsred.
  split; [other A1 0|]. split; [other A2 0|]. split; [other A3 0|]. split; [other A4 0|].
  split; [other A5 0|]. split; [other A6 0|]. split; [other A7 0|].
  split; [|other A9 0].
  pose proof (cells_write_cell segs m (S + 3008) 4 4 573 (arr_get (ds_heap s)) i v A8 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
  replace (S + 3008 + 4 * i) with (S + 3008 + 4 * i) in Hc by lia.
  intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L8.
  pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
  destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 573); cbn [andb]; subst; try lia; exact Hcj.
Qed.

Lemma arrays_depth_set : forall m S s i v,
  dsl_arrays segs m S s -> tree_lens s -> 0 <= i < 573 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_arrays segs (wbytes m (zw (S + 5308 + i)) (Z_to_le_bytes 1 v)) S (depth_set s i v).
Proof.
  intros m S s i v H HL Hi HS0 HS1. unfold dsl_SIZE in HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & L9).
  unfold dsl_arrays, depth_set. dsred.
  split; [other A1 0|]. split; [other A2 0|]. split; [other A3 0|]. split; [other A4 0|].
  split; [other A5 0|]. split; [other A6 0|]. split; [other A7 0|]. split; [other A8 0|].
  pose proof (cells_write_cell segs m (S + 5308) 1 1 573 (arr_get (ds_depth s)) i (wrap8 v) A9 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
  replace (S + 5308 + 1 * i) with (S + 5308 + i) in Hc by lia.
  assert (E : Z_to_le_bytes 1 (wrap8 v) = Z_to_le_bytes 1 v).
  { rewrite <- (SymExec.Z_to_le_bytes_mod 1 v). rewrite wrap8_mod. reflexivity. }
  rewrite E in Hc.
  intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L9.
  pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
  destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 573); cbn [andb]; subst; try lia; exact Hcj.
Qed.

Lemma arrays_bl_count_set : forall m S s i v,
  dsl_arrays segs m S s -> tree_lens s -> 0 <= i < 16 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_arrays segs (wbytes m (zw (S + 2976 + 2 * i)) (Z_to_le_bytes 2 v)) S (bl_count_set s i v).
Proof.
  intros m S s i v H HL Hi HS0 HS1. unfold dsl_SIZE in HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof HL as (_ & _ & _ & _ & _ & _ & L7 & _).
  unfold dsl_arrays, bl_count_set. dsred.
  split; [other A1 0|]. split; [other A2 0|]. split; [other A3 0|]. split; [other A4 0|].
  split; [other A5 0|]. split; [other A6 0|].
  split; [| split; [other A8 0 | other A9 0]].
  pose proof (cells_write_cell segs m (S + 2976) 2 2 16 (arr_get (ds_bl_count s)) i (wrap16 v) A7 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
  assert (E : Z_to_le_bytes 2 (wrap16 v) = Z_to_le_bytes 2 v).
  { rewrite <- (SymExec.Z_to_le_bytes_mod 2 v). rewrite wrap16_mod. reflexivity. }
  rewrite E in Hc.
  intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L7.
  pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
  destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 16); cbn [andb]; subst; try lia; exact Hcj.
Qed.

Lemma arrays_set_fc : forall m S s t i v,
  dsl_arrays segs m S s -> tree_lens s -> 0 <= i < tsize t -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_arrays segs (wbytes m (zw (S + toff t + 4 * i)) (Z_to_le_bytes 2 v)) S (set_tree_fc s t (arr_set (tree_fc s t) i (wrap16 v))).
Proof.
  intros m S s t i v H HL Hi HS0 HS1. unfold dsl_SIZE in HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & _).
  assert (E : Z_to_le_bytes 2 (wrap16 v) = Z_to_le_bytes 2 v).
  { rewrite <- (SymExec.Z_to_le_bytes_mod 2 v). rewrite wrap16_mod. reflexivity. }
  destruct t; cbn [toff tsize tree_fc set_tree_fc] in *; unfold dsl_arrays; dsred.
  - pose proof (cells_write_cell segs m (S + 212) 4 2 573 (arr_get (ds_dyn_ltree_fc s)) i (wrap16 v) A1 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
    rewrite E in Hc.
    split.
    { intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L1.
      pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
      destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 573); cbn [andb]; subst; try lia; exact Hcj. }
    split.
    { intros j Hj. assert (4 * j + 4 <= 4 * i \/ 4 * i + 2 <= 4 * j + 2) by lia.
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact (A2 j Hj). }
    split; [other A3 0|]. split; [other A4 0|]. split; [other A5 0|]. split; [other A6 0|].
    split; [other A7 0|]. split; [other A8 0 | other A9 0].
  - pose proof (cells_write_cell segs m (S + 2504) 4 2 61 (arr_get (ds_dyn_dtree_fc s)) i (wrap16 v) A3 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
    rewrite E in Hc.
    split; [other A1 0|]. split; [other A2 0|].
    split.
    { intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L3.
      pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
      destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 61); cbn [andb]; subst; try lia; exact Hcj. }
    split.
    { intros j Hj. assert (4 * j + 4 <= 4 * i \/ 4 * i + 2 <= 4 * j + 2) by lia.
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact (A4 j Hj). }
    split; [other A5 0|]. split; [other A6 0|]. split; [other A7 0|]. split; [other A8 0 | other A9 0].
  - pose proof (cells_write_cell segs m (S + 2748) 4 2 39 (arr_get (ds_bl_tree_fc s)) i (wrap16 v) A5 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
    rewrite E in Hc.
    split; [other A1 0|]. split; [other A2 0|]. split; [other A3 0|]. split; [other A4 0|].
    split.
    { intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L5.
      pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
      destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 39); cbn [andb]; subst; try lia; exact Hcj. }
    split.
    { intros j Hj. assert (4 * j + 4 <= 4 * i \/ 4 * i + 2 <= 4 * j + 2) by lia.
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact (A6 j Hj). }
    split; [other A7 0|]. split; [other A8 0 | other A9 0].
Qed.

Lemma arrays_set_dl : forall m S s t i v,
  dsl_arrays segs m S s -> tree_lens s -> 0 <= i < tsize t -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_arrays segs (wbytes m (zw (S + toff t + 4 * i + 2)) (Z_to_le_bytes 2 v)) S (set_tree_dl s t (arr_set (tree_dl s t) i (wrap16 v))).
Proof.
  intros m S s t i v H HL Hi HS0 HS1. unfold dsl_SIZE in HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & _).
  assert (E : Z_to_le_bytes 2 (wrap16 v) = Z_to_le_bytes 2 v).
  { rewrite <- (SymExec.Z_to_le_bytes_mod 2 v). rewrite wrap16_mod. reflexivity. }
  destruct t; cbn [toff tsize tree_dl set_tree_dl] in *; unfold dsl_arrays; dsred.
  - pose proof (cells_write_cell segs m (S + 214) 4 2 573 (arr_get (ds_dyn_ltree_dl s)) i (wrap16 v) A2 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
    rewrite E in Hc. replace (S + 214 + 4 * i) with (S + 212 + 4 * i + 2) in Hc by lia.
    split.
    { intros j Hj. assert (4 * j + 2 <= 4 * i + 2 \/ 4 * i + 2 + 2 <= 4 * j) by lia.
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact (A1 j Hj). }
    split.
    { intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L2.
      pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
      destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 573); cbn [andb]; subst; try lia; exact Hcj. }
    split; [other A3 0|]. split; [other A4 0|]. split; [other A5 0|]. split; [other A6 0|].
    split; [other A7 0|]. split; [other A8 0 | other A9 0].
  - pose proof (cells_write_cell segs m (S + 2506) 4 2 61 (arr_get (ds_dyn_dtree_dl s)) i (wrap16 v) A4 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
    rewrite E in Hc. replace (S + 2506 + 4 * i) with (S + 2504 + 4 * i + 2) in Hc by lia.
    split; [other A1 0|]. split; [other A2 0|].
    split.
    { intros j Hj. assert (4 * j + 2 <= 4 * i + 2 \/ 4 * i + 2 + 2 <= 4 * j) by lia.
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact (A3 j Hj). }
    split.
    { intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L4.
      pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
      destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 61); cbn [andb]; subst; try lia; exact Hcj. }
    split; [other A5 0|]. split; [other A6 0|]. split; [other A7 0|]. split; [other A8 0 | other A9 0].
  - pose proof (cells_write_cell segs m (S + 2750) 4 2 39 (arr_get (ds_bl_tree_dl s)) i (wrap16 v) A6 ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia)) as Hc.
    rewrite E in Hc. replace (S + 2750 + 4 * i) with (S + 2748 + 4 * i + 2) in Hc by lia.
    split; [other A1 0|]. split; [other A2 0|]. split; [other A3 0|]. split; [other A4 0|].
    split.
    { intros j Hj. assert (4 * j + 2 <= 4 * i + 2 \/ 4 * i + 2 + 2 <= 4 * j) by lia.
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact (A5 j Hj). }
    split.
    { intros j Hj. unfold cell. rewrite arr_get_set. unfold arr_inb. rewrite L6.
      pose proof (Hc j Hj) as Hcj. unfold cell in Hcj. cbn beta in Hcj.
      destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i 39); cbn [andb]; subst; try lia; exact Hcj. }
    split; [other A7 0|]. split; [other A8 0 | other A9 0].
Qed.

Lemma arrays_write_other : forall m S s (b : Z) bs,
  dsl_arrays segs m S s -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (S + dsl_SIZE <= b \/ b + Z.of_nat (length bs) <= S) ->
  dsl_arrays segs (wbytes m (zw b) bs) S s.
Proof.
  intros m S s b bs H HS0 HS1 Hb0 Hb1 Hd. unfold dsl_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold dsl_arrays.
  repeat split;
    (eapply cells_write_other; [eassumption | cbn; lia | lia | lia | lia | lia | lia]).
Qed.

Lemma arrays_agree_out : forall F m m' S s,
  dsl_arrays segs m S s -> agree_out F m m' ->
  disj_franges F (S + 212) 2694 -> disj_franges F (S + 2976) 2324 -> disj_franges F (S + 5308) 573 ->
  0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dsl_arrays segs m' S s.
Proof.
  intros F m m' S s H Hag D1 D2 D3 HS0 HS1. unfold dsl_SIZE in HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold dsl_arrays.
  assert (G : forall P st w n f lo len, cells segs m P st w n f -> disj_franges F lo len ->
             lo <= P -> P + st * n <= lo + len -> Z.of_nat w <= st -> 0 <= P -> P + st * n <= 2 ^ 64 -> 0 <= n ->
             cells segs m' P st w n f).
  { intros P st w n f lo len Hc HD H1 H2 H3 H4 H5 H6.
    refine (cells_agree_out segs F m m' P st w n f Hag _ H3 H4 H5 Hc).
    intros x Hx. apply HD. nia. }
  split; [eapply (G _ _ _ _ _ (S + 212) 2694 A1 D1); cbn; lia|].
  split; [eapply (G _ _ _ _ _ (S + 212) 2694 A2 D1); cbn; lia|].
  split; [eapply (G _ _ _ _ _ (S + 212) 2694 A3 D1); cbn; lia|].
  split; [eapply (G _ _ _ _ _ (S + 212) 2694 A4 D1); cbn; lia|].
  split; [eapply (G _ _ _ _ _ (S + 212) 2694 A5 D1); cbn; lia|].
  split; [eapply (G _ _ _ _ _ (S + 212) 2694 A6 D1); cbn; lia|].
  split; [eapply (G _ _ _ _ _ (S + 2976) 2324 A7 D2); cbn; lia|].
  split; [eapply (G _ _ _ _ _ (S + 2976) 2324 A8 D2); cbn; lia|].
  eapply (G _ _ _ _ _ (S + 5308) 573 A9 D3); cbn; lia.
Qed.

Fixpoint layout_gap (L : list (Z * nat)) (lo hi : Z) : bool :=
  match L with
  | [] => true
  | (o, w) :: L' => ((o + Z.of_nat w <=? lo) || (hi <=? o)) && layout_gap L' lo hi
  end.

Lemma fields_write_gap : forall mem S L vs size lo hi (b : Z) bs,
  fields segs mem S L vs -> layout_within L size = true -> layout_gap L lo hi = true ->
  S + lo <= b -> b + Z.of_nat (length bs) <= S + hi ->
  0 <= S -> 0 <= lo -> S + size <= 2 ^ 64 -> S + hi <= 2 ^ 64 ->
  fields segs (wbytes mem (zw b) bs) S L vs.
Proof.
  intros mem S L. induction L as [|[o w] L' IH]; intros vs size lo hi b bs Hf HW HG Hlo Hhi HS0 Hlo0 HS1 HS2.
  - destruct vs; [exact I | destruct Hf].
  - destruct vs as [|v vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_within layout_gap] in HW, HG.
    apply andb_prop in HW as [HW HW']. apply andb_prop in HW as [H0 H1].
    apply andb_prop in HG as [HG HG'].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    split; [| exact (IH vs' size lo hi b bs Hf' HW' HG' Hlo Hhi HS0 Hlo0 HS1 HS2)].
    apply Bool.orb_prop in HG as [HG|HG]; apply Z.leb_le in HG;
      (apply cell_write_other; [exact Hc | lia | lia | lia | lia | lia]).
Qed.

Lemma dsl_gap_trees : layout_gap dsl_layout 212 2904 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dsl_gap_heap : layout_gap dsl_layout 2976 5300 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dsl_gap_depth : layout_gap dsl_layout 5308 5881 = true. Proof. vm_compute. reflexivity. Qed.

Section Scalars.
Variables SL SD SB : Z.
Local Notation dscal := (dsl_scalars segs SL SD SB).

Lemma scalars_write_trees : forall m S p s (b : Z) bs,
  dscal m S p s -> S + 212 <= b -> b + Z.of_nat (length bs) <= S + 2904 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes m (zw b) bs) S p s.
Proof.
  intros m S p s b bs H Hlo Hhi HS0 HS1. unfold dsl_scalars in *. unfold dsl_SIZE in HS1.
  eapply (fields_write_gap m S dsl_layout _ dsl_SIZE 212 2904 b bs H dsl_layout_within dsl_gap_trees);
    unfold dsl_SIZE; lia.
Qed.

Lemma scalars_write_heapzone : forall m S p s (b : Z) bs,
  dscal m S p s -> S + 2976 <= b -> b + Z.of_nat (length bs) <= S + 5300 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes m (zw b) bs) S p s.
Proof.
  intros m S p s b bs H Hlo Hhi HS0 HS1. unfold dsl_scalars in *. unfold dsl_SIZE in HS1.
  eapply (fields_write_gap m S dsl_layout _ dsl_SIZE 2976 5300 b bs H dsl_layout_within dsl_gap_heap);
    unfold dsl_SIZE; lia.
Qed.

Lemma scalars_write_depth : forall m S p s (b : Z) bs,
  dscal m S p s -> S + 5308 <= b -> b + Z.of_nat (length bs) <= S + 5881 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes m (zw b) bs) S p s.
Proof.
  intros m S p s b bs H Hlo Hhi HS0 HS1. unfold dsl_scalars in *. unfold dsl_SIZE in HS1.
  eapply (fields_write_gap m S dsl_layout _ dsl_SIZE 5308 5881 b bs H dsl_layout_within dsl_gap_depth);
    unfold dsl_SIZE; lia.
Qed.

Lemma scalars_heap_set : forall m S p s i v,
  dscal m S p s -> 0 <= i < 573 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes m (zw (S + 3008 + 4 * i)) (Z_to_le_bytes 4 v)) S p s.
Proof.
  intros m S p s i v H Hi HS0 HS1. apply scalars_write_heapzone; rewrite ?length_Z_to_le_bytes; try lia. exact H.
Qed.
Lemma scalars_depth_set : forall m S p s i v,
  dscal m S p s -> 0 <= i < 573 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes m (zw (S + 5308 + i)) (Z_to_le_bytes 1 v)) S p s.
Proof.
  intros m S p s i v H Hi HS0 HS1. apply scalars_write_depth; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H.
Qed.
Lemma scalars_bl_count_set : forall m S p s i v,
  dscal m S p s -> 0 <= i < 16 -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes m (zw (S + 2976 + 2 * i)) (Z_to_le_bytes 2 v)) S p s.
Proof.
  intros m S p s i v H Hi HS0 HS1. apply scalars_write_heapzone; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H.
Qed.
Lemma scalars_tree_set : forall m S p s t i half v,
  dscal m S p s -> 0 <= i < tsize t -> (half = 0 \/ half = 2) -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes m (zw (S + toff t + 4 * i + half)) (Z_to_le_bytes 2 v)) S p s.
Proof.
  intros m S p s t i half v H Hi Hh HS0 HS1. pose proof (toff_tsize t).
  apply scalars_write_trees; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H.
Qed.

Lemma scalars_set_tree_fc : forall m S p s t a, dscal m S p (set_tree_fc s t a) <-> dscal m S p s.
Proof. intros m S p s [| |] a; unfold dsl_scalars; reflexivity. Qed.
Lemma scalars_set_tree_dl : forall m S p s t a, dscal m S p (set_tree_dl s t a) <-> dscal m S p s.
Proof. intros m S p s [| |] a; unfold dsl_scalars; reflexivity. Qed.
Lemma scalars_set_pending_buf : forall m S p s a, dscal m S p (set_pending_buf s a) <-> dscal m S p s.
Proof. intros. unfold dsl_scalars. reflexivity. Qed.
End Scalars.


Lemma u32_read_at : forall mem P n f i a v,
  cells segs mem P 4 4 n f -> 0 <= i < n -> 0 <= f i < 2 ^ 32 -> a = P + 4 * i -> v = f i ->
  exists bs, rdn segs mem (zw a) 4 = Some bs /\ bytes_le_to_Z bs = v.
Proof.
  intros mem P n f i a v Hc Hi Hf -> ->. apply (cells_read_small segs mem P 4 4 n f i Hc Hi). cbn. lia.
Qed.

Lemma fc_read_at : forall mem P n f i a v,
  cells segs mem P 4 2 n f -> 0 <= i < n -> 0 <= f i < 65536 -> a = P + 4 * i -> v = f i ->
  exists bs, rdn segs mem (zw a) 2 = Some bs /\ bytes_le_to_Z bs = v.
Proof.
  intros mem P n f i a v Hc Hi Hf -> ->. apply (cells_read_small segs mem P 4 2 n f i Hc Hi). cbn. lia.
Qed.

End WithSegs.

Definition hv (h : arr) (i : Z) : Z := (arr_get h i) mod 573.
Lemma hv_range : forall h i, 0 <= hv h i < 573.
Proof. intros. unfold hv. apply Z.mod_pos_bound. lia. Qed.
Lemma hv_get : forall h i, 0 <= arr_get h i < 573 -> hv h i = arr_get h i.
Proof. intros h i H. unfold hv. apply Z.mod_small. exact H. Qed.

Section Reads.
Variable segs : list Segment.
Lemma hv_read : forall mem P n h i a,
  cells segs mem P 4 4 n (arr_get h) -> 0 <= i < n -> 0 <= arr_get h i < 573 -> a = P + 4 * i ->
  exists bs, rdn segs mem (zw a) 4 = Some bs /\ bytes_le_to_Z bs = hv h i.
Proof.
  intros mem P n h i a Hc Hi Hr ->. rewrite hv_get by exact Hr.
  apply (cells_read_small segs mem P 4 4 n (arr_get h) i Hc Hi). cbn. lia.
Qed.
Lemma pb_read4 : forall mem P n (t : arr) i a,
  cells segs mem P 4 2 n (arr_get t) -> 0 <= i < n -> 0 <= arr_get t i < 65536 -> a = P + 4 * i ->
  exists bs, rdn segs mem (zw a) 2 = Some bs /\ bytes_le_to_Z bs = pb t i.
Proof.
  intros mem P n t i a Hc Hi Hr ->. unfold pb. rewrite Z.mod_small by exact Hr.
  apply (cells_read_small segs mem P 4 2 n (arr_get t) i Hc Hi). cbn. lia.
Qed.
Lemma wb_read1 : forall mem P n (d : arr) i a,
  cells segs mem P 1 1 n (arr_get d) -> 0 <= i < n -> 0 <= arr_get d i < 256 -> a = P + i ->
  exists bs, rdn segs mem (zw a) 1 = Some bs /\ bytes_le_to_Z bs = wb d i.
Proof.
  intros mem P n d i a Hc Hi Hr ->. unfold wb. rewrite Z.mod_small by exact Hr.
  replace (P + i) with (P + 1 * i) by lia.
  apply (cells_read_small segs mem P 1 1 n (arr_get d) i Hc Hi). cbn. lia.
Qed.
End Reads.

End FXG.
Ltac arr_range_auto :=
  first [ lia
        | match goal with
          | R : forall j, _ -> 0 <= arr_get ?a j < _ |- 0 <= arr_get ?a _ < _ => apply R; lia
          | R : forall j, _ -> 0 <= arr_get ?a j < _ |- 0 <= arr_get ?a _ < _ =>
              eapply (fun j H => proj1 (conj (R j H) I)); lia
          end
        | match goal with
          | R : forall j, _ -> 0 <= arr_get ?a j < ?B |- 0 <= arr_get ?a ?i < ?C =>
              let H := fresh in pose proof (R i) as H; lia
          end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_read_hook ::=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = ?v =>
      match v with
      | hv ?h ?i =>
          match goal with H : cells sg m ?P 4 4%nat ?len (arr_get h) |- _ =>
            eapply (hv_read sg m P len h i a H); [lia | arr_range_auto | lia] end
      | pb ?t ?i =>
          match goal with H : cells sg m ?P 4 2%nat ?len (arr_get t) |- _ =>
            eapply (pb_read4 sg m P len t i a H); [lia | arr_range_auto | lia] end
      | wb ?d ?i =>
          match goal with H : cells sg m ?P 1 1%nat ?len (arr_get d) |- _ =>
            eapply (wb_read1 sg m P len d i a H); [lia | arr_range_auto | lia] end
      | _ =>
      match goal with
      | H : cell sg m a n _ |- _ =>
          eapply (cell_read_at sg m a n _ v H); rewrite ?Z.mod_small by cells_range_auto; lia
      | H : cells sg m ?P 1 1%nat ?len ?f |- _ =>
          eapply (bytes_read_at sg m P len f (a - P) a v H);
            [ lia | cells_range_auto | lia | first [reflexivity | f_equal; lia] ]
      | H : cells sg m ?P 2 2%nat ?len ?f |- _ =>
          eapply (u16_read_at sg m P len f ((a - P) / 2) a v H);
            [ lia | cells_range_auto | lia | first [reflexivity | f_equal; lia] ]
      | H : cells sg m ?P 4 4%nat ?len ?f |- _ =>
          eapply (u32_read_at sg m P len f ((a - P) / 4) a v H);
            [ lia | cells_range_auto | lia | first [reflexivity | f_equal; lia] ]
      | H : cells sg m ?P 4 2%nat ?len ?f |- _ =>
          eapply (fc_read_at sg m P len f ((a - P) / 4) a v H);
            [ lia | cells_range_auto | lia | first [reflexivity | f_equal; lia] ]
      end end
  end.

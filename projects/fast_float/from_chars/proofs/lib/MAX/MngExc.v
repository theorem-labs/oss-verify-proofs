(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage MngSurgery.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition PW (L : layout) (s : astate) : Prop := pairwise ranges_disjoint (map (cell_range L) (image s)).

Definition repr_x (L : layout) (s : astate) (bv : byteview) (EXC : list loc) : Prop :=
  layout_ok L s /\ PW L s /\
  Forall (fun c => In (mc_loc c) EXC \/ cell_holds L bv c) (image s) /\
  Forall (range_mapped L bv) (footprint s).

Lemma repr_x_of_repr : forall L s bv, WF s -> repr L s bv -> repr_x L s bv [].
Proof.
  intros L s bv HW (HL & HC & HF). split; [exact HL|]. split; [exact (image_cells_disjoint s L HW HL)|]. split; [|exact HF].
  apply Forall_forall. intros c Hc. right. exact (proj1 (Forall_forall _ _) HC c Hc).
Qed.

Lemma repr_of_repr_x : forall L s bv, repr_x L s bv [] -> repr L s bv.
Proof.
  intros L s bv (HL & _ & HC & HF). split; [exact HL|]. split; [|exact HF].
  apply Forall_forall. intros c Hc. destruct (proj1 (Forall_forall _ _) HC c Hc) as [[]|H]. exact H.
Qed.

(* [comment removed for export] *)
Lemma repr_x_step : forall L s s' bv bv' EXC EXC' (Cnew : list mcell),
  repr_x L s bv EXC -> layout_ok L s' -> PW L s' -> Forall (range_mapped L bv') (footprint s') ->
  (forall c, In c (image s') -> (In c (image s) /\ ~ In (mc_loc c) EXC) \/ In c Cnew \/ In (mc_loc c) EXC') ->
  (forall c, In c Cnew -> In c (image s')) ->
  Forall (cell_holds L bv') Cnew ->
  (forall a, bv' a <> bv a -> (exists c', In c' Cnew /\ in_rng (cell_range L c') a) \/
                            (forall c, In c (image s') -> ~ In (mc_loc c) EXC' -> ~ in_rng (cell_range L c) a)) ->
  repr_x L s' bv' EXC'.
Proof.
  intros L s s' bv bv' EXC EXC' Cnew (HL & HPW & HC & HF) HL' HPW' HF' Hcov HNin HNew HWO.
  split; [exact HL'|]. split; [exact HPW'|]. split; [|exact HF'].
  apply Forall_forall. intros c Hc. destruct (In_dec loc_eq_dec (mc_loc c) EXC') as [He|He]; [left; exact He|]. right.
  destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn]; [exact (proj1 (Forall_forall _ _) HNew c Hn)|].
  destruct (Hcov c Hc) as [(H1 & H1e) | [H1|H1]]; [| contradiction | contradiction].
  destruct (proj1 (Forall_forall _ _) HC c H1) as [He0|Hh]; [contradiction|].
  apply (cell_holds_frame L bv bv' c (image_cell_width s c H1) Hh).
  intros a Ha. destruct (option_Z_eq_dec (bv' a) (bv a)) as [E|E]; [exact E|]. exfalso.
  destruct (HWO a E) as [(c' & Hc' & Ha') | Hj].
  - assert (Hne : c <> c') by (intros ->; exact (Hn Hc')).
    pose proof (pairwise_map_In _ (cell_range L) _ _ _ HPW' Hc (HNin c' Hc') Hne) as D.
    pose proof (image_cell_width s' c Hc) as W1. pose proof (image_cell_width s' c' (HNin c' Hc')) as W2.
    unfold ranges_disjoint, in_rng, cell_range in *. cbn [fst snd] in *. lia.
  - exact (Hj c Hc He Ha).
Qed.

(* [comment removed for export] *)
Lemma PW_perm : forall L (l l' : list mcell), Permutation l l' ->
  pairwise ranges_disjoint (map (cell_range L) l) -> pairwise ranges_disjoint (map (cell_range L) l').
Proof.
  intros L l l' HP H. apply (pairwise_perm ranges_disjoint (map (cell_range L) l)); [exact ranges_disjoint_sym' | apply Permutation_map; exact HP | exact H].
Qed.

Lemma msc_ranges : forall L q x y, (exists a, x = Some (MUsed a) \/ x = Some (MFree None None)) -> (exists b, y = Some (MUsed b) \/ y = Some (MFree None None)) ->
  map (cell_range L) (meta_slot_cells q x) = map (cell_range L) (meta_slot_cells q y).
Proof. intros L q x y (a & [->| ->]) (b & [->| ->]); reflexivity. Qed.

(* [comment removed for export] *)
Lemma PW_setm : forall L s g am am', KS s -> MT s g = Some (MUsed am) ->
  map (cell_range L) (group_cells g am') = map (cell_range L) (group_cells g am) -> PW L s -> PW L (set_meta s g (MUsed am')).
Proof.
  intros L s g am am' HK Hg Hgc HPW. destruct (image_setm_ks s g am am' HK Hg) as (U & P1 & P2).
  unfold PW in *. apply (PW_perm L _ _ (Permutation_sym P2)). apply (PW_perm L _ _ P1) in HPW.
  rewrite !map_app in *. rewrite Hgc.
  replace (map (cell_range L) (meta_slot_cells g (Some (MUsed am')))) with (map (cell_range L) (meta_slot_cells g (Some (MUsed am)))) by reflexivity.
  exact HPW.
Qed.

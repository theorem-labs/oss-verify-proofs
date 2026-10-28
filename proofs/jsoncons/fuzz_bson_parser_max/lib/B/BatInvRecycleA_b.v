(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatSecAllocPost_b BatFxQ_b
     BatRecycle2C_b BatRecycle3L_b BatRecycle5A_b BatRecycle5I_b BatRecycle5T_b BatInv_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition art_sec_b (s : art_sec) : Z * Z := (sc_map s, sc_msize s).

(* [comment removed for export] *)
Definition art_rel_key (e : art_rel) : Z * Z := match e with REP c w _ _ _ => (c, w) | RES mb _ _ _ _ => (0, mb) | REB wb => (24, wb) end.

Definition art_rg_ok (G : art_rg) : Prop :=
  (forall c, 1 <= c <= 30 -> Z.of_nat (length (cl_cache (rg_cls G c))) <= art_ic_mc c)
  /\ (forall b b', In b (rg_bl G) -> In b' (rg_bl G) -> fst b = fst b' -> b = b').

Lemma art_rg_ok_step : forall e G, art_rg_ok G -> art_rel_pre G e -> art_rg_ok (art_rel_step e G).
Proof.
  intros e G (CK & INJ) PRE. destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_step art_rel_pre] in *.
  - split; [|exact INJ]. cbn [rg_cls]. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
    + rewrite art_cls_upd_same. apply art_cls_dealloc_cache_le; [apply CK; exact Hc'|lia].
    + rewrite art_cls_upd_other by exact NE. apply CK. exact Hc'.
  - split; [exact CK|]. cbn [rg_bl]. intros b b' Hb Hb'. apply INJ; eapply art_swap_remove_in; eassumption.
  - split; [|exact INJ]. cbn [rg_cls]. intros c' Hc'. destruct (Z.eq_dec c' 24) as [->|NE].
    + rewrite art_cls_upd_same. apply art_cls_dealloc_cache_le; [apply CK; exact Hc'|lia].
    + rewrite art_cls_upd_other by exact NE. apply CK. exact Hc'.
Qed.

(* [comment removed for export] *)
Lemma art_pre_cls_other : forall G c0 w0 c w sz, art_rg_ok G -> 1 <= c0 <= 30 -> (c0, w0) <> (c, w) ->
  art_cptr_ok sz (cl_au (rg_cls G c)) w -> ~ In w (cl_cache (rg_cls G c) ++ cl_free (rg_cls G c)) ->
  art_cptr_ok sz (cl_au (art_cls_upd (rg_cls G) c0 (art_cls_dealloc c0 w0 (rg_cls G c0)) c)) w
  /\ ~ In w (cl_cache (art_cls_upd (rg_cls G) c0 (art_cls_dealloc c0 w0 (rg_cls G c0)) c) ++ cl_free (art_cls_upd (rg_cls G) c0 (art_cls_dealloc c0 w0 (rg_cls G c0)) c)).
Proof.
  intros G c0 w0 c w sz (CK & _) Hc0 NE OKw NIN. destruct (Z.eq_dec c c0) as [->|NEc].
  - rewrite art_cls_upd_same. destruct (art_cls_dealloc_au c0 w0 (rg_cls G c0)) as (Ea & _). rewrite Ea. split; [exact OKw|].
    intros Hin. apply (art_cls_dealloc_in c0 w0 (rg_cls G c0) w (CK c0 Hc0) ltac:(lia)) in Hin. destruct Hin as [E|Hin]; [apply NE; rewrite E; reflexivity|exact (NIN Hin)].
  - rewrite art_cls_upd_other by exact NEc. split; assumption.
Qed.

Lemma art_rel_pre_other : forall e0 e G, art_rg_ok G -> art_rel_pre G e0 -> art_rel_pre G e -> art_rel_key e0 <> art_rel_key e -> art_rel_pre (art_rel_step e0 G) e.
Proof.
  intros e0 e G OK P0 P NE. pose proof OK as (CK & INJ).
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_pre art_rel_key] in P, NE |- *.
  - destruct P as (Hc & OKw & NIN & REST).
    destruct e0 as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step art_rel_pre art_rel_key rg_cls] in P0, NE |- *.
    + destruct P0 as (Hc0 & _). destruct (art_pre_cls_other G c0 w0 c w _ OK Hc0 NE OKw NIN) as (X1 & X2). split; [exact Hc|]. split; [exact X1|]. split; [exact X2|exact REST].
    + split; [exact Hc|]. split; [exact OKw|]. split; [exact NIN|exact REST].
    + destruct (art_pre_cls_other G 24 wb0 c w _ OK ltac:(lia) NE OKw NIN) as (X1 & X2). split; [exact Hc|]. split; [exact X1|]. split; [exact X2|exact REST].
  - destruct P as (Hin & REST).
    destruct e0 as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step art_rel_pre art_rel_key rg_bl] in P0, NE |- *; try (split; [exact Hin|exact REST]).
    destruct P0 as (Hin0 & _). split; [|exact REST].
    pose proof (art_bl_idx_nth (rg_bl G) mb0 ms0 Hin0 INJ) as Hn.
    apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hn; discriminate|exact Hin|].
    rewrite (nth_error_nth _ _ (0, 0) Hn). intros E. apply NE. injection E as E1 _. rewrite E1. reflexivity.
  - destruct P as (OKw & NIN).
    destruct e0 as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step art_rel_pre art_rel_key rg_cls] in P0, NE |- *.
    + destruct P0 as (Hc0 & _). exact (art_pre_cls_other G c0 w0 24 wb _ OK Hc0 NE OKw NIN).
    + split; assumption.
    + exact (art_pre_cls_other G 24 wb0 24 wb _ OK ltac:(lia) NE OKw NIN).
Qed.

Lemma art_rels_pre_intro : forall es G, art_rg_ok G -> (forall e, In e es -> art_rel_pre G e) -> List.NoDup (map art_rel_key es) -> art_rels_pre G es.
Proof.
  induction es as [|e0 r IH]; intros G OK PRE ND; cbn [art_rels_pre]; [exact I|].
  cbn [map] in ND. inversion ND as [|? ? Hnin NDr]; subst.
  split; [apply PRE; left; reflexivity|].
  apply IH; [apply art_rg_ok_step; [exact OK|apply PRE; left; reflexivity]| |exact NDr].
  intros e He. apply art_rel_pre_other; [exact OK|apply PRE; left; reflexivity|apply PRE; right; exact He|].
  intros E. apply Hnin. rewrite E. apply in_map. exact He.
Qed.

(* [comment removed for export] *)
Lemma art_nodup_map_of : forall (A B C : Type) (f : A -> B) (g : A -> C) (l : list A),
  (forall x y, In x l -> In y l -> g x = g y -> f x = f y) -> List.NoDup (map f l) -> List.NoDup (map g l).
Proof.
  intros A B C f g l. induction l as [|a r IH]; intros INJ ND; cbn [map] in *; [constructor|].
  inversion ND as [|? ? Hnin NDr]; subst. constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Ey & Hy). apply Hnin. rewrite <- (INJ y a (or_intror Hy) (or_introl eq_refl) Ey). apply in_map. exact Hy.
  - apply IH; [|exact NDr]. intros x y Hx Hy. apply INJ; right; assumption.
Qed.

Lemma art_nodup_flat_snoc : forall (A B : Type) (f : A -> list B) (g : A -> B) (l : list A),
  List.NoDup (flat_map f l) -> List.NoDup (map g l) -> (forall b b', In b l -> In b' l -> ~ In (g b) (f b')) ->
  List.NoDup (flat_map (fun b => f b ++ [g b]) l).
Proof.
  intros A B f g l. induction l as [|a r IH]; intros NDf NDg NX; cbn [flat_map map] in *; [constructor|].
  inversion NDg as [|? ? Hnin NDr]; subst.
  apply NoDup_app_remove_l in NDf as NDfr. pose proof NDf as NDf0.
  assert (IHr : List.NoDup (flat_map (fun b => f b ++ [g b]) r)) by (apply IH; [exact NDfr|exact NDr|intros b b' Hb Hb'; apply NX; right; assumption]).
  rewrite <- app_assoc. cbn [app].
  assert (INr : forall x, In x (flat_map (fun b => f b ++ [g b]) r) -> In x (flat_map f r) \/ In x (map g r)).
  { intros x Hx. apply in_flat_map in Hx. destruct Hx as (b & Hb & Hx). apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]].
    - left. apply in_flat_map. exists b. split; assumption.
    - right. apply in_map. exact Hb. }
  apply List.NoDup_app; [exact (NoDup_app_remove_r _ _ NDf0)| |].
  - constructor; [|exact IHr]. intros Hx. destruct (INr _ Hx) as [Hx'|Hx']; [|exact (Hnin Hx')].
    apply in_flat_map in Hx'. destruct Hx' as (b' & Hb' & Hx'). exact (NX a b' (or_introl eq_refl) (or_intror Hb') Hx').
  - intros x Hx [<-|Hx2]; [exact (NX a a (or_introl eq_refl) (or_introl eq_refl) Hx)|].
    destruct (INr _ Hx2) as [Hx'|Hx'].
    + revert Hx Hx'. clear - NDf0. intros Hx Hx'. induction (f a) as [|y s IHs]; [destruct Hx|]. cbn [app] in NDf0. inversion NDf0 as [|? ? Hn Nd]; subst.
      destruct Hx as [<-|Hx]; [apply Hn; apply in_or_app; right; exact Hx'|exact (IHs Nd Hx)].
    + apply in_map_iff in Hx'. destruct Hx' as (b' & Eb' & Hb'). rewrite <- Eb' in Hx. exact (NX b' a (or_intror Hb') (or_introl eq_refl) Hx).
Qed.

(* [comment removed for export] *)
Lemma art_swap_remove_map : forall (A B : Type) (f : A -> B) (d : A) i l, map f (art_swap_remove d i l) = art_swap_remove (f d) i (map f l).
Proof.
  intros A B f d i l. unfold art_swap_remove. rewrite map_map, length_map. apply map_ext. intros j. symmetry. apply map_nth.
Qed.

(* [comment removed for export] *)
Lemma art_chunk_apart : forall spb c w c' w', 1 <= c <= 30 -> 1 <= c' <= 30 ->
  0 <= w -> 16 * w + AsanTab.class_size c <= 3758096384 -> (exists i, 16 * w = AsanTab.class_size c * i) ->
  0 <= w' -> 16 * w' + AsanTab.class_size c' <= 3758096384 -> (exists i, 16 * w' = AsanTab.class_size c' * i) ->
  (c, w) <> (c', w') ->
  apart (spb + c * 2 ^ 32 + 16 * w) (AsanTab.class_size c) (spb + c' * 2 ^ 32 + 16 * w') (AsanTab.class_size c').
Proof.
  intros spb c w c' w' Hc Hc' Hw Hwu (i & Ei) Hw' Hwu' (i' & Ei') NE. unfold apart.
  destruct (art_class_size_facts c Hc) as (S1 & _). destruct (art_class_size_facts c' Hc') as (S1' & _).
  destruct (Z.eq_dec c c') as [->|NEc]; [|lia].
  assert (NEw : w <> w') by (intros ->; apply NE; reflexivity).
  assert (NEi : i <> i') by (intros ->; apply NEw; lia).
  set (sz := AsanTab.class_size c') in *. rewrite Ei, Ei'. nia.
Qed.

(* [comment removed for export] *)
Lemma art_rels_sep_intro : forall spb es,
  (forall e e', In e es -> In e' es -> art_rel_key e <> art_rel_key e' -> art_zapart spb e (fst (art_rel_zone spb e')) (snd (art_rel_zone spb e'))) ->
  List.NoDup (map art_rel_key es) -> art_rels_sep spb es.
Proof.
  intros spb es. induction es as [|e0 r IH]; intros Z ND; cbn [art_rels_sep]; [exact I|].
  cbn [map] in ND. inversion ND as [|? ? Hn Nd]; subst. split.
  - apply Forall_forall. intros e' He'. apply Z; [left; reflexivity|right; exact He'|]. intros E. apply Hn. rewrite E. apply in_map. exact He'.
  - apply IH; [|exact Nd]. intros e e' He He'. apply Z; right; assumption.
Qed.

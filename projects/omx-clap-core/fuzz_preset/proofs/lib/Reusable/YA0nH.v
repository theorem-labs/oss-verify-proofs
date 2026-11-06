(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YA0nH.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YA0nH.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YA0nH.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* The step relation over a GENERAL world preorder. YA0n.SRr fixes the continuation's worlds to wle, where the hidden
   set only shrinks. A secondary recycle needs more: after its madvise of the dead shadow hull's interior, the walk
   continues in a world where that interior is HIDDEN and dropped from the allowance, so that the released hull stops
   counting in MInv's budget. SRrG is SRr with the relation a parameter (any preorder containing wle); its lemmas are
   YA0n.v's and YG0d.v's, unchanged in proof. wle' (the hidden set may grow only inside a fixed zone RZ) is that
   instance, and SRr_SRrG lifts every SRr fact into it. Additive: no existing text changes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0n YK0i YK15 YK0j YK18 YK0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YK05 YA0i YA0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

Section d. Context {fx : YK11.FPState}.
Section e.
Variable segs : list Segment.
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).

Variable Rel : world segs -> world segs -> Prop.
Hypothesis Rel_refl : forall W, Rel W W.
Hypothesis Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3.

Definition SRrG (W : world segs) (c : config) (Q : world segs -> config -> Prop) : Prop :=
  AIw W (cfg_model c) ->
  forall T, (forall W' c', Rel W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
  srealizes segs c T.

Lemma SRrG_ret : forall W c (Q : world segs -> config -> Prop), Q W c -> SRrG W c Q.
Proof. intros W c Q HQ HI T HK. exact (HK W c (Rel_refl W) HI HQ). Qed.

Lemma SRrG_bind : forall W c (R Q : world segs -> config -> Prop),
  SRrG W c R -> (forall W' c', Rel W W' -> R W' c' -> SRrG W' c' Q) -> SRrG W c Q.
Proof.
  intros W c R Q H1 H2 HI T HK. apply (H1 HI T). intros W' c' Hle HI' HR.
  apply (H2 W' c' Hle HR HI' T). intros W'' c'' Hle' HI'' HQ.
  exact (HK W'' c'' (Rel_trans _ _ _ Hle Hle') HI'' HQ).
Qed.

Lemma SRrG_mono : forall W c (Q Q' : world segs -> config -> Prop),
  SRrG W c Q -> (forall W' c', Rel W W' -> Q W' c' -> Q' W' c') -> SRrG W c Q'.
Proof.
  intros W c Q Q' H HQQ HI T HK. apply (H HI T). intros W' c' Hle HI' HQ.
  exact (HK W' c' Hle HI' (HQQ W' c' Hle HQ)).
Qed.

Lemma SRrG_srealizes : forall W c Q T,
  SRrG W c Q -> AIw W (cfg_model c) ->
  (forall W' c', Rel W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros W c Q T H HI HK. exact (H HI T HK). Qed.

Lemma SRrG_case : forall (P : Prop) W c Q,
  (P \/ ~ P) -> (P -> SRrG W c Q) -> (~ P -> SRrG W c Q) -> SRrG W c Q.
Proof. intros P W c Q [p|np] H1 H2; auto. Qed.

Lemma SRrG_use_AI : forall W c Q, (AIw W (cfg_model c) -> SRrG W c Q) -> SRrG W c Q.
Proof. intros W c Q H HI. exact (H HI HI). Qed.

Lemma SRrG_world_le : forall W W' c Q,
  Rel W W' -> (AIw W (cfg_model c) -> AIw W' (cfg_model c)) -> SRrG W' c Q -> SRrG W c Q.
Proof.
  intros W W' c Q Hle Htr H HI T HK. apply (H (Htr HI) T).
  intros W'' c'' Hle' HI'' HQ. exact (HK W'' c'' (Rel_trans _ _ _ Hle Hle') HI'' HQ).
Qed.

Lemma SRrG_node : forall W c (I : Type) (nx : I -> config) (i0 : I) Q,
  node_ok segs c I (fun _ => []) nx ->
  (forall i, AIw W (cfg_model c) -> AIw W (cfg_model (nx i))) ->
  (forall i, SRrG W (nx i) Q) ->
  SRrG W c Q.
Proof.
  intros W c I nx i0 Q Hnode HIt H HI T HK.
  assert (HT0 : T []).
  { eapply srealizes_nonempty. apply (H i0 (HIt i0 HI) T HK). }
  apply (srz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hnode).
    intros i. apply (H i (HIt i HI) T HK).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intros Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

Lemma SRrG_nodeI : forall W c (I : Type) (nx : I -> config) (i0 : I) Q,
  (AIw W (cfg_model c) -> node_ok segs c I (fun _ => []) nx /\ (forall i, AIw W (cfg_model (nx i)))) ->
  (forall i, SRrG W (nx i) Q) ->
  SRrG W c Q.
Proof.
  intros W c I nx i0 Q Hn H HI. destruct (Hn HI) as [Hnode HIt].
  apply (SRrG_node W c I nx i0 Q Hnode); [intros i _; exact (HIt i) | exact H | exact HI].
Qed.

Lemma SRrG_node_tnil : forall W c (I : Type) (nx : I -> config) (sp : I -> bool) (i0 : I) Q,
  node_ok segs c I (fun _ => []) nx ->
  (forall i, AIw W (cfg_model c) -> AIw W (cfg_model (nx i))) ->
  sp i0 = false ->
  (forall i, sp i = true -> AIw W (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) ->
  (forall i, sp i = false -> SRrG W (nx i) Q) ->
  SRrG W c Q.
Proof.
  intros W c I nx sp i0 Q Hnode HIt Hi0 Hspin Hk HI T HK.
  assert (HT0 : T []).
  { eapply srealizes_nonempty. apply (Hk i0 Hi0 (HIt i0 HI) T HK). }
  apply (srz_conseq segs c (t_alt (fun i : I => t_emit [] (if sp i then t_nil else T)))).
  - apply (srz_node segs c I (fun _ => []) nx (fun i => if sp i then t_nil else T) i0 Hnode).
    intros i. destruct (sp i) eqn:Hs.
    + exact (Hspin i Hs (HIt i HI)).
    + exact (Hk i Hs (HIt i HI) T HK).
  - intro tr. split.
    + intros [i Hi]. destruct (sp i).
      * apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. exact HT0.
      * exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intros Htr. exists i0. rewrite Hi0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

Lemma SRrG_tnil : forall W c (P : world segs -> config -> Prop),
  SRrG W c P -> (forall W' c', Rel W W' -> P W' c' -> AIw W' (cfg_model c') -> srealizes segs c' t_nil) ->
  AIw W (cfg_model c) -> srealizes segs c t_nil.
Proof. intros W c P H HP HI. apply (H HI t_nil). intros W' c' Hle HI' HP'. exact (HP W' c' Hle HP' HI'). Qed.

(* The lift: every existing SRr fact is an SRrG fact, for any relation containing wle. *)
Lemma SRr_SRrG : (forall W W', wle W W' -> Rel W W') ->
  forall W c Q, SRr segs W c Q -> SRrG W c Q.
Proof.
  intros Hsub W c Q H HI T HK. apply (H HI T). intros W' c' Hle HI' HQ. exact (HK W' c' (Hsub _ _ Hle) HI' HQ).
Qed.
End e.

(* ---------------------------------------------------------------------------- *)
(* The F1 instance: the hidden set may grow only inside a fixed zone RZ.           *)
Section f.
Variable segs : list Segment.
Variable RZ : Z -> Prop.

(* The hidden set may grow only inside the set DS. wle' is its instance at the zone RZ; a step states its EXACT set
   (the shadow of the dead extents) and lifts into wle' by wle_in_mono, which keeps the composition relation fixed. *)
Definition wle_in (DS : Z -> Prop) (W W' : world segs) : Prop :=
  forall a : word, w_H W' a = true -> w_H W a = true \/ DS (bv_unsigned a).

Lemma wle_in_mono : forall (DS DS' : Z -> Prop) W W',
  (forall a, DS a -> DS' a) -> wle_in DS W W' -> wle_in DS' W W'.
Proof. intros DS DS' W W' Hsub H a Ha. destruct (H a Ha) as [H1 | H2]; [left; exact H1 | right; exact (Hsub _ H2)]. Qed.

Definition wle' (W W' : world segs) : Prop := wle_in RZ W W'.

Lemma wle'_wle_in : forall W W', wle' W W' <-> wle_in RZ W W'.
Proof. intros W W'. reflexivity. Qed.

Lemma wle'_refl : forall W, wle' W W.
Proof. intros W a Ha. left. exact Ha. Qed.

Lemma wle'_trans : forall W1 W2 W3, wle' W1 W2 -> wle' W2 W3 -> wle' W1 W3.
Proof.
  intros W1 W2 W3 H12 H23 a Ha. destruct (H23 a Ha) as [H2 | Hz]; [exact (H12 a H2) | right; exact Hz].
Qed.

Lemma wle_wle' : forall W W', wle W W' -> wle' W W'.
Proof. intros W W' Hle a Ha. left. exact (Hle a Ha). Qed.

Definition SRr' : world segs -> config -> (world segs -> config -> Prop) -> Prop := SRrG segs wle'.

Lemma SRr_SRr' : forall W c Q, SRr segs W c Q -> SRr' W c Q.
Proof. exact (SRr_SRrG segs wle' wle_wle'). Qed.
End f.
End d.

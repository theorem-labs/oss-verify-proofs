(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0e.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Local Abbreviation AIw W md := (AI segs (w_H W) (w_A W) md).
Lemma srz_node_all_tnil : forall c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx ->
(forall i, srealizes segs (nx i) t_nil) ->
srealizes segs c t_nil.
Proof.
intros c I nx i0 Hnode Hall.
apply (srz_conseq segs c (t_alt (fun i : I => t_emit [] t_nil))).
- apply (srz_node segs c I (fun _ => []) nx (fun _ => t_nil) i0 Hnode). exact Hall.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq t_nil eq_refl tr) Hi).
+ intros Htr. exists i0. exact (proj2 (t_emit_nil_eq t_nil eq_refl tr) Htr).
Qed.
Lemma SRr_node_tnil_w : forall (W : world segs) c (I : Type) (nx : I -> config) (sp : I -> bool) (Wi : I -> world segs) (i0 : I) Q,
node_ok segs c I (fun _ => []) nx ->
(forall i, AIw W (cfg_model c) -> wle W (Wi i) /\ AIw (Wi i) (cfg_model (nx i))) ->
sp i0 = false ->
(forall i, sp i = true -> AIw (Wi i) (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) ->
(forall i, sp i = false -> SRr segs (Wi i) (nx i) Q) ->
SRr segs W c Q.
Proof.
intros W c I nx sp Wi i0 Q Hnode HIt Hi0 Hspin Hk HI T HK.
assert (HKi : forall i W' c', wle (Wi i) W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T).
{ intros i W' c' Hle HI' HQ. exact (HK W' c' (wle_trans segs _ _ _ (proj1 (HIt i HI)) Hle) HI' HQ). }
assert (HT0 : T []).
{ eapply srealizes_nonempty. apply (Hk i0 Hi0 (proj2 (HIt i0 HI)) T (HKi i0)). }
apply (srz_conseq segs c (t_alt (fun i : I => t_emit [] (if sp i then t_nil else T)))).
- apply (srz_node segs c I (fun _ => []) nx (fun i => if sp i then t_nil else T) i0 Hnode).
intros i. destruct (sp i) eqn:Hs.
+ exact (Hspin i Hs (proj2 (HIt i HI))).
+ exact (Hk i Hs (proj2 (HIt i HI)) T (HKi i)).
- intro tr. split.
+ intros [i Hi]. destruct (sp i).
* apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. exact HT0.
* exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros Htr. exists i0. rewrite Hi0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.
Theorem amreal_silent_node {R : Type} : forall (t : itree astate R) (W : world segs) c (I : Type) (nx : I -> config) (sp : I -> bool)
(Wi : I -> world segs) (i0 : I) (Q : R -> world segs -> config -> Prop),
node_ok segs c I (fun _ => []) nx ->
(forall i, AIw W (cfg_model c) -> wle W (Wi i) /\ AIw (Wi i) (cfg_model (nx i))) ->
sp i0 = false ->
(forall i, sp i = true -> AIw (Wi i) (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) ->
(forall i, sp i = false -> amreal segs t (Wi i) (nx i) Q) ->
amreal segs t W c Q.
Proof.
intros t W c I nx sp Wi i0 Q Hnode HIt Hi0 Hspin Hk. destruct t as [r | q s k | pc | f]; cbn in *.
- exact (SRr_node_tnil_w W c I nx sp Wi i0 _ Hnode HIt Hi0 Hspin Hk).
- exact (SRr_node_tnil_w W c I nx sp Wi i0 _ Hnode HIt Hi0 Hspin Hk).
- intros HI. apply (srz_node_all_tnil c I nx i0 Hnode). intros i. destruct (sp i) eqn:Hs.
+ exact (Hspin i Hs (proj2 (HIt i HI))).
+ exact (Hk i Hs (proj2 (HIt i HI))).
- exact Logic.I.
Qed.
Lemma node_all_spin : forall (W : world segs) c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx ->
(forall i, AIw W (cfg_model c) -> AIw W (cfg_model (nx i))) ->
(forall i, AIw W (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) ->
AIw W (cfg_model c) -> srealizes segs c t_nil.
Proof.
intros W c I nx i0 Hnode HIt Hall HI. apply (srz_node_all_tnil c I nx i0 Hnode). intros i. exact (Hall i (HIt i HI)).
Qed.
End b.
End a.

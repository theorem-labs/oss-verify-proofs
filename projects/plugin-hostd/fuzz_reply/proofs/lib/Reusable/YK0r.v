(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK0r.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Lemma path_eqb_false_ne : forall p q, path_eqb p q = false <-> p <> q.
Proof.
intros p q. split.
- intros H E. apply path_eqb_eq in E. congruence.
- intros H. destruct (path_eqb p q) eqn:E; [|reflexivity]. apply path_eqb_eq in E. contradiction.
Qed.
Lemma path_eqb_sym : forall p q, path_eqb p q = path_eqb q p.
Proof.
intros p q. destruct (path_eqb p q) eqn:E.
- apply path_eqb_eq in E. subst q. symmetry. apply path_eqb_refl.
- symmetry. apply path_eqb_false_ne. apply path_eqb_false_ne in E. congruence.
Qed.
Lemma path_ltb_tri : forall p q, path_ltb p q = false -> path_eqb p q = false -> path_ltb q p = true.
Proof.
induction p as [|a p IH]; intros [|b q] Hlt Heq; cbn in *; try discriminate; try reflexivity.
apply Bool.orb_false_iff in Hlt as [H1 H2].
unfold bv_ltu, bv_eqb in *.
destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
- cbn [andb] in H2, Heq. apply Bool.orb_true_iff. right.
rewrite (proj2 (Z.eqb_eq _ _) (eq_sym E)). cbn [andb]. exact (IH q H2 Heq).
- apply Bool.orb_true_iff. left. apply Z.ltb_lt. apply Z.ltb_ge in H1. lia.
Qed.
Lemma path_ltb_irrefl : forall p, path_ltb p p = false.
Proof.
induction p as [|a p IH]; [reflexivity|]. cbn. unfold bv_ltu, bv_eqb. rewrite Z.ltb_irrefl, Z.eqb_refl. exact IH.
Qed.
Lemma fs_lookup_remove_other : forall fs p q, q <> p -> fs_lookup (fs_remove fs p) q = fs_lookup fs q.
Proof.
induction fs as [|[k d] r IH]; intros p q Hne; [reflexivity|].
cbn [fs_remove]. destruct (path_eqb p k) eqn:Epk.
- apply path_eqb_eq in Epk. subst k. cbn [fs_lookup].
rewrite (proj2 (path_eqb_false_ne q p) Hne). reflexivity.
- cbn [fs_lookup]. destruct (path_eqb q k); [reflexivity | exact (IH p q Hne)].
Qed.
Lemma fs_lookup_set_same : forall fs p d, fs_lookup (fs_set fs p d) p = Some d.
Proof.
induction fs as [|[k e] r IH]; intros p d.
- cbn [fs_set fs_lookup]. rewrite path_eqb_refl. reflexivity.
- cbn [fs_set]. destruct (path_ltb p k).
+ cbn [fs_lookup]. rewrite path_eqb_refl. reflexivity.
+ destruct (path_eqb p k) eqn:E.
* cbn [fs_lookup]. rewrite path_eqb_refl. reflexivity.
* cbn [fs_lookup]. rewrite E. apply IH.
Qed.
Lemma fs_lookup_set_other : forall fs p d q, q <> p -> fs_lookup (fs_set fs p d) q = fs_lookup fs q.
Proof.
induction fs as [|[k e] r IH]; intros p d q Hne.
- cbn [fs_set fs_lookup]. rewrite (proj2 (path_eqb_false_ne q p) Hne). reflexivity.
- cbn [fs_set]. destruct (path_ltb p k).
+ cbn [fs_lookup]. rewrite (proj2 (path_eqb_false_ne q p) Hne). reflexivity.
+ destruct (path_eqb p k) eqn:E.
* apply path_eqb_eq in E. subst k. cbn [fs_lookup]. rewrite (proj2 (path_eqb_false_ne q p) Hne). reflexivity.
* cbn [fs_lookup]. destruct (path_eqb q k); [reflexivity | exact (IH p d q Hne)].
Qed.
Lemma fs_set_lt_head : forall fs a p d,
fs_lt_head a fs = true -> path_ltb a p = true -> fs_lt_head a (fs_set fs p d) = true.
Proof.
intros [|[k e] r] a p d Hh Hap; cbn [fs_set].
- exact Hap.
- destruct (path_ltb p k); [exact Hap|]. destruct (path_eqb p k); [exact Hap | exact Hh].
Qed.
Lemma fs_set_sorted : forall fs p d, fs_sorted fs = true -> fs_sorted (fs_set fs p d) = true.
Proof.
induction fs as [|[k e] r IH]; intros p d Hs; [reflexivity|].
pose proof Hs as Hs0. rewrite fs_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hk Hr].
cbn [fs_set]. destruct (path_ltb p k) eqn:Elt.
- rewrite fs_sorted_cons. cbn [fs_lt_head]. rewrite Elt. exact Hs0.
- destruct (path_eqb p k) eqn:Eeq.
+ apply path_eqb_eq in Eeq. subst k. rewrite fs_sorted_cons, Hk. exact Hr.
+ rewrite fs_sorted_cons, Bool.andb_true_iff. split; [|exact (IH p d Hr)].
apply fs_set_lt_head; [exact Hk | exact (path_ltb_tri p k Elt Eeq)].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC QKyU QPa2 QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QCiC QKyU QPa2 QOb0.Mq0.
Import ListNotations.
Open Scope Z_scope.

Lemma zsum_nil : zsum [] = 0. Proof. reflexivity. Qed.
Lemma zsum_cons x l : zsum (x :: l) = x + zsum l. Proof. reflexivity. Qed.
Lemma zsum_app l1 l2 : zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [|x l1 IH]; [cbn [app]; rewrite zsum_nil; lia|]. cbn [app]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_perm l l' : Permutation l l' -> zsum l = zsum l'.
Proof. induction 1; rewrite ?zsum_cons; lia. Qed.

Lemma zsum_map_perm {A} (f : A -> Z) l l' : Permutation l l' -> zsum (map f l) = zsum (map f l').
Proof. intros P. apply zsum_perm. apply Permutation_map. exact P. Qed.

Lemma zsum_map_le {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof.
induction l as [|x l IH]; intros H; cbn [map]; [rewrite zsum_nil; lia|]. rewrite !zsum_cons.
pose proof (H x (or_introl eq_refl)). assert (zsum (map f l) <= zsum (map g l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsum_map_const {A} (k : Z) (l : list A) : zsum (map (fun _ => k) l) = k * zlen l.
Proof. unfold zlen. induction l as [|x l IH]; cbn [map length]; [rewrite zsum_nil; lia|]. rewrite zsum_cons, IH. lia. Qed.

Lemma zlen_cons {A} (x : A) l : zlen (x :: l) = 1 + zlen l. Proof. unfold zlen. cbn. lia. Qed.
Lemma zlen_app {A} (l1 l2 : list A) : zlen (l1 ++ l2) = zlen l1 + zlen l2. Proof. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_nonneg {A} (l : list A) : 0 <= zlen l. Proof. unfold zlen. lia. Qed.

Lemma zcount_eq_zsum {A} (p : A -> bool) l : zcount p l = zsum (map (fun x => if p x then 1 else 0) l).
Proof. unfold zcount, zlen. induction l as [|x l IH]; cbn [map List.filter length]; [rewrite zsum_nil; reflexivity|]. destruct (p x); cbn [length]; rewrite ?zsum_cons, <- IH; lia. Qed.

Lemma zcount_cons {A} (p : A -> bool) x l : zcount p (x :: l) = (if p x then 1 else 0) + zcount p l.
Proof. rewrite !zcount_eq_zsum. cbn [map]. rewrite zsum_cons. reflexivity. Qed.
Lemma zcount_app {A} (p : A -> bool) l1 l2 : zcount p (l1 ++ l2) = zcount p l1 + zcount p l2.
Proof. rewrite !zcount_eq_zsum, map_app, zsum_app. reflexivity. Qed.
Lemma zcount_nonneg {A} (p : A -> bool) l : 0 <= zcount p l. Proof. unfold zcount. apply zlen_nonneg. Qed.

Lemma zcount_perm {A} (p : A -> bool) l l' : Permutation l l' -> zcount p l = zcount p l'.
Proof. intros P. rewrite !zcount_eq_zsum. apply zsum_map_perm. exact P. Qed.

Section MTL.
Context `{Countable K} `{EqDecision K} {V : Type}.
Implicit Types m : gmap K V.

Definition msum (f : K * V -> Z) m : Z := zsum (map f (map_to_list m)).

End MTL.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy7F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy7F. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcxL.
Local Set Keyed Unification.

Import ListNotations.
Local Open Scope Z_scope.

Record ctrl_eq (st st' : mstate) : Prop := mkCE {
ce_ctx : s_ctx st' = s_ctx st;
ce_regions : s_regions st' = s_regions st;
ce_next_rid : s_next_rid st' = s_next_rid st;
ce_metas : s_metas st' = s_metas st;
ce_areas : s_areas st' = s_areas st;
ce_groups : s_groups st' = s_groups st;
ce_slots : s_slots st' = s_slots st;
ce_secret : s_secret st' = s_secret st;
ce_reserved : s_reserved st' = s_reserved st
}.

Section VIEWS.
Variables st st' : mstate.

End VIEWS.

Section CTRL.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis CE : ctrl_eq st st'.

Let HC := ce_ctx _ _ CE. Let HR := ce_regions _ _ CE. Let HN := ce_next_rid _ _ CE. Let HM := ce_metas _ _ CE.
Let HA := ce_areas _ _ CE. Let HG := ce_groups _ _ CE. Let HS := ce_slots _ _ CE. Let HX := ce_secret _ _ CE. Let HV := ce_reserved _ _ CE.

End CTRL.


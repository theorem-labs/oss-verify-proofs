(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition pdef (t : ptrie) (p : positive) : bool :=
  match pget t p with Some _ => true | None => false end.
Definition zdef (a : zarr) (i : Z) : bool := pdef a (pos_of_Z i).

Lemma zdef_znew : forall i, zdef znew i = false.
Proof. intros i. unfold zdef, pdef, znew. rewrite pget_leaf. reflexivity. Qed.

Lemma zdef_zset_same : forall a i v, zdef (zset a i v) i = true.
Proof. intros. unfold zdef, pdef, zset. rewrite pget_pset_same. reflexivity. Qed.

Lemma zdef_zset_other : forall a i v j, j <> i -> zdef (zset a i v) j = zdef a j.
Proof.
  intros a i v j H. unfold zdef, pdef, zset. rewrite pget_pset_other; [reflexivity|].
  intros E. apply H. apply pos_of_Z_inj. exact E.
Qed.

Lemma zdef_zset : forall a i v j, zdef (zset a i v) j = ((j =? i) || zdef a j)%bool.
Proof.
  intros. destruct (Z.eqb_spec j i) as [->|H]; cbn [orb].
  - apply zdef_zset_same.
  - apply zdef_zset_other. exact H.
Qed.

(* [comment removed for export] *)
Lemma zdef_zset_mono : forall a i v j, zdef a j = true -> zdef (zset a i v) j = true.
Proof. intros. rewrite zdef_zset, H. apply orb_true_r. Qed.

(* [comment removed for export] *)
Lemma zdef_zincr : forall a i j, zdef (zincr a i) j = ((j =? i) || zdef a j)%bool.
Proof. intros. unfold zincr. apply zdef_zset. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zdefr (a : zarr) (lo n : Z) : Prop := forall i, lo <= i < lo + n -> zdef a i = true.

(* [comment removed for export] *)
Lemma zdefr_mono : forall a lo n i v, zdefr a lo n -> zdefr (zset a i v) lo n.
Proof. intros a lo n i v H j Hj. apply zdef_zset_mono. apply H. exact Hj. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zbok (a : zarr) : Prop := forall i, 0 <= zget a i < 256.

Lemma zbok_znew : zbok znew.
Proof. intros i. rewrite zget_znew. lia. Qed.
Lemma zbok_zset : forall a i v, zbok a -> 0 <= v < 256 -> zbok (zset a i v).
Proof. intros a i v H Hv j. rewrite zget_zset. destruct (j =? i); [exact Hv| apply H]. Qed.
Lemma zbok_wr8 : forall a o v, zbok a -> zbok (wr8 a o v).
Proof. intros. unfold wr8. apply zbok_zset; [assumption|]. apply Z.mod_pos_bound. lia. Qed.
Lemma zbok_wr16 : forall a o v, zbok a -> zbok (wr16 a o v).
Proof. intros. unfold wr16. apply zbok_zset; [apply zbok_zset; [assumption|]|]; apply Z.mod_pos_bound; lia. Qed.
Lemma zbok_wr32 : forall a i v, zbok a -> zbok (wr32 a i v).
Proof.
  intros. unfold wr32. repeat (apply zbok_zset; [|apply Z.mod_pos_bound; lia]). assumption.
Qed.
Lemma zbok_of_list_at : forall l a lo, zbok a -> Forall (fun v => 0 <= v < 256) l -> zbok (zarr_of_list_at a lo l).
Proof.
  induction l as [|x l IH]; intros a lo Ha Hl; cbn; [exact Ha|].
  inversion Hl; subst. apply IH; [apply zbok_zset; assumption| assumption].
Qed.
Lemma zbok_rd8 : forall a o, zbok a -> 0 <= rd8 a o < 256.
Proof. intros a o H. unfold rd8. apply H. Qed.
Lemma zbok_rd16 : forall a o, zbok a -> 0 <= rd16 a o < 65536.
Proof. intros a o H. unfold rd16. pose proof (H o). pose proof (H (o + 1)). lia. Qed.
Lemma zbok_rd32 : forall a i, zbok a -> 0 <= rd32 a i < 4294967296.
Proof.
  intros a i H. unfold rd32.
  pose proof (H (4 * i)). pose proof (H (4 * i + 1)). pose proof (H (4 * i + 2)). pose proof (H (4 * i + 3)). lia.
Qed.

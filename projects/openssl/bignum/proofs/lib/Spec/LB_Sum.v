(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MI_Inv LB_Inv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Lemma zsum_map_ext {A} (f g : A -> Z) l : (forall x, In x l -> f x = g x) -> zsum (map f l) = zsum (map g l).
Proof. intros H. f_equal. apply map_ext_in. exact H. Qed.

Lemma zsum_map_le {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof.
  induction l as [|x l IH]; intros H; cbn [map]; [rewrite zsum_nil; lia|]. rewrite !zsum_cons.
  pose proof (H x (or_introl eq_refl)). assert (zsum (map f l) <= zsum (map g l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsum_map_nonneg {A} (f : A -> Z) l : (forall x, In x l -> 0 <= f x) -> 0 <= zsum (map f l).
Proof. intros H. induction l as [|x l IH]; cbn [map]; [rewrite zsum_nil; lia|]. rewrite zsum_cons. pose proof (H x (or_introl eq_refl)). assert (0 <= zsum (map f l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia. Qed.

Lemma zsum_map_add {A} (f g : A -> Z) l : zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. induction l as [|x l IH]; cbn [map]; [rewrite !zsum_nil; reflexivity|]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_map_mul {A} (k : Z) (f : A -> Z) l : zsum (map (fun x => k * f x) l) = k * zsum (map f l).
Proof. induction l as [|x l IH]; cbn [map]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_map_const {A} (k : Z) (l : list A) : zsum (map (fun _ => k) l) = k * zlen l.
Proof. unfold zlen. induction l as [|x l IH]; cbn [map length]; [rewrite zsum_nil; lia|]. rewrite zsum_cons, IH. lia. Qed.

Lemma zsum_map_filter {A} (p : A -> bool) (f : A -> Z) l :
  zsum (map f (List.filter p l)) = zsum (map (fun x => if p x then f x else 0) l).
Proof. induction l as [|x l IH]; cbn [map List.filter]; [reflexivity|]. destruct (p x); cbn [map]; rewrite ?zsum_cons, IH; lia. Qed.

Lemma zsum_flat_map {A B} (g : A -> list B) (f : B -> Z) l :
  zsum (map f (flat_map g l)) = zsum (map (fun a => zsum (map f (g a))) l).
Proof. induction l as [|x l IH]; cbn [map flat_map]; [reflexivity|]. rewrite map_app, zsum_app, zsum_cons, IH. reflexivity. Qed.

Lemma zsum_map_remove {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (g : A -> Z) y l :
  In y l -> (forall x, In x l -> 0 <= g x) -> exists l', Permutation l (y :: l') /\ zsum (map g l) = g y + zsum (map g l').
Proof.
  intros Hin Hg. apply in_split in Hin as (l1 & l2 & ->). exists (l1 ++ l2). split; [apply Permutation_sym; apply Permutation_middle|].
  rewrite !map_app, !zsum_app. cbn [map]. rewrite zsum_cons. lia.
Qed.

Lemma zsum_inj_le {A B} (eqB : forall x y : B, {x = y} + {x <> y}) (f : A -> Z) (g : B -> Z) (h : A -> B) :
  forall (l1 : list A) (l2 : list B),
  List.NoDup l1 -> (forall x, In x l1 -> In (h x) l2 /\ f x <= g (h x)) ->
  (forall x y, In x l1 -> In y l1 -> h x = h y -> x = y) ->
  (forall y, In y l2 -> 0 <= g y) ->
  zsum (map f l1) <= zsum (map g l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 ND H INJ POS; cbn [map].
  - rewrite zsum_nil. apply zsum_map_nonneg. exact POS.
  - rewrite zsum_cons. apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (H a (or_introl eq_refl)) as [Hin Hle].
    destruct (zsum_map_remove eqB g (h a) l2 Hin POS) as (l2' & P & E). rewrite E.
    assert (IH' : zsum (map f l1) <= zsum (map g l2')).
    { apply IH; [exact ND| | intros x y Hx Hy; apply INJ; right; assumption| intros y Hy; apply POS; eapply Permutation_in; [apply Permutation_sym; exact P| right; exact Hy]].
      intros x Hx. destruct (H x (or_intror Hx)) as [Hin2 Hle2]. split; [| exact Hle2].
      pose proof (Permutation_in _ P Hin2) as [E2|Hin3]; [| exact Hin3].
      exfalso. apply NI. rewrite (INJ a x (or_introl eq_refl) (or_intror Hx) E2). exact Hx. }
    lia.
Qed.

Lemma zlen_nil {A} : zlen (@nil A) = 0. Proof. reflexivity. Qed.
Lemma zlen_cons {A} (x : A) l : zlen (x :: l) = 1 + zlen l. Proof. unfold zlen. cbn. lia. Qed.
Lemma zlen_app {A} (l1 l2 : list A) : zlen (l1 ++ l2) = zlen l1 + zlen l2. Proof. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_nonneg {A} (l : list A) : 0 <= zlen l. Proof. unfold zlen. lia. Qed.
Lemma zlen_map {A B} (f : A -> B) l : zlen (map f l) = zlen l. Proof. unfold zlen. rewrite length_map. reflexivity. Qed.

Lemma zcount_eq_zsum {A} (p : A -> bool) l : zcount p l = zsum (map (fun x => if p x then 1 else 0) l).
Proof. unfold zcount, zlen. induction l as [|x l IH]; cbn [map List.filter length]; [rewrite zsum_nil; reflexivity|]. destruct (p x); cbn [length]; rewrite ?zsum_cons, <- IH; lia. Qed.
Lemma zcount_nil {A} (p : A -> bool) : zcount p [] = 0. Proof. reflexivity. Qed.
Lemma zcount_cons {A} (p : A -> bool) x l : zcount p (x :: l) = (if p x then 1 else 0) + zcount p l.
Proof. rewrite !zcount_eq_zsum. cbn [map]. rewrite zsum_cons. reflexivity. Qed.
Lemma zcount_app {A} (p : A -> bool) l1 l2 : zcount p (l1 ++ l2) = zcount p l1 + zcount p l2.
Proof. rewrite !zcount_eq_zsum, map_app, zsum_app. reflexivity. Qed.
Lemma zcount_nonneg {A} (p : A -> bool) l : 0 <= zcount p l. Proof. unfold zcount. apply zlen_nonneg. Qed.
Lemma zcount_le_len {A} (p : A -> bool) l : zcount p l <= zlen l.
Proof. induction l as [|x l IH]; [cbv; discriminate|]. rewrite zcount_cons, zlen_cons. destruct (p x); lia. Qed.
Lemma zcount_perm {A} (p : A -> bool) l l' : Permutation l l' -> zcount p l = zcount p l'.
Proof. intros P. rewrite !zcount_eq_zsum. apply zsum_map_perm. exact P. Qed.
Lemma zcount_ext {A} (p q : A -> bool) l : (forall x, In x l -> p x = q x) -> zcount p l = zcount q l.
Proof. intros H. rewrite !zcount_eq_zsum. apply zsum_map_ext. intros x Hx. rewrite (H x Hx). reflexivity. Qed.
Lemma zcount_mono {A} (p q : A -> bool) l : (forall x, In x l -> p x = true -> q x = true) -> zcount p l <= zcount q l.
Proof.
  intros H. rewrite !zcount_eq_zsum. apply zsum_map_le. intros x Hx. specialize (H x Hx). destruct (p x); [rewrite H by reflexivity; lia| destruct (q x); lia].
Qed.
Lemma zcount_false {A} (p : A -> bool) l : (forall x, In x l -> p x = false) -> zcount p l = 0.
Proof. intros H. rewrite zcount_eq_zsum. induction l as [|x l IH]; cbn [map]; [apply zsum_nil|]. rewrite zsum_cons, (H x (or_introl eq_refl)), IH; [lia|]. intros y Hy; apply H; right; exact Hy. Qed.

Lemma zcount_inj_le {A B} (eqB : forall x y : B, {x = y} + {x <> y}) (p : A -> bool) (q : B -> bool) (h : A -> B) l1 l2 :
  List.NoDup l1 -> (forall x, In x l1 -> p x = true -> In (h x) l2 /\ q (h x) = true) ->
  (forall x y, In x l1 -> In y l1 -> p x = true -> p y = true -> h x = h y -> x = y) ->
  zcount p l1 <= zcount q l2.
Proof.
  intros ND H INJ. unfold zcount at 1. unfold zlen.
  transitivity (zsum (map (fun _ => 1) (List.filter p l1))); [rewrite zsum_map_const; unfold zlen; lia|].
  rewrite zcount_eq_zsum. apply (zsum_inj_le eqB (fun _ => 1) _ h).
  - apply List.NoDup_filter. exact ND.
  - intros x Hx. apply filter_In in Hx as [Hx Hp]. destruct (H x Hx Hp) as [Hin Hq]. rewrite Hq. auto with zarith.
  - intros x y Hx Hy. apply filter_In in Hx as [Hx Hp]. apply filter_In in Hy as [Hy Hq]. apply INJ; assumption.
  - intros y _. destruct (q y); lia.
Qed.

Section MTL.
Context `{Countable K} `{EqDecision K} {V : Type}.
Implicit Types m : gmap K V.

Lemma mtl_nodup m : List.NoDup (map_to_list m).
Proof. apply NoDup_ListNoDup. apply NoDup_map_to_list. Qed.
Lemma mtl_nodup_keys m : List.NoDup (map fst (map_to_list m)).
Proof. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. Qed.
Lemma mtl_in m k v : In (k, v) (map_to_list m) <-> m !! k = Some v.
Proof. rewrite <- list_elem_of_In. apply elem_of_map_to_list. Qed.
Lemma mtl_insert m k v : m !! k = None -> Permutation (map_to_list (<[k := v]> m)) ((k, v) :: map_to_list m).
Proof. intros Hk. apply map_to_list_insert. exact Hk. Qed.
Lemma mtl_delete m k v : m !! k = Some v -> Permutation (map_to_list m) ((k, v) :: map_to_list (delete k m)).
Proof. intros Hk. rewrite <- (insert_delete_id m k v Hk) at 1. apply map_to_list_insert. apply lookup_delete_eq. Qed.
Lemma mtl_insert_old m k v v0 : m !! k = Some v0 ->
  Permutation (map_to_list (<[k := v]> m)) ((k, v) :: map_to_list (delete k m)).
Proof. intros Hk. rewrite <- (insert_delete_eq m k v). apply map_to_list_insert. apply lookup_delete_eq. Qed.

Definition msum (f : K * V -> Z) m : Z := zsum (map f (map_to_list m)).
Lemma msum_insert f m k v : m !! k = None -> msum f (<[k := v]> m) = f (k, v) + msum f m.
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_insert m k v Hk)). cbn [map]. apply zsum_cons. Qed.
Lemma msum_delete f m k v : m !! k = Some v -> msum f m = f (k, v) + msum f (delete k m).
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_delete m k v Hk)). cbn [map]. apply zsum_cons. Qed.
Lemma msum_insert_old f m k v v0 : m !! k = Some v0 -> msum f (<[k := v]> m) = f (k, v) + msum f m - f (k, v0).
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_insert_old m k v v0 Hk)). cbn [map]. rewrite zsum_cons. pose proof (msum_delete f m k v0 Hk) as E. unfold msum in E. lia. Qed.
Lemma msum_ext f g m : (forall k v, m !! k = Some v -> f (k, v) = g (k, v)) -> msum f m = msum g m.
Proof. intros Hfg. unfold msum. apply zsum_map_ext. intros [k v] Hin. apply Hfg. apply mtl_in. exact Hin. Qed.
Lemma msum_nonneg f m : (forall k v, m !! k = Some v -> 0 <= f (k, v)) -> 0 <= msum f m.
Proof. intros Hf. unfold msum. apply zsum_map_nonneg. intros [k v] Hin. apply Hf. apply mtl_in. exact Hin. Qed.
End MTL.

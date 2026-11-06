(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition murmur_M : Z := 0xc6a4a7935bd1e995.
Definition murmur_seed : Z := 0x9747b28c9747b28c.
Definition murmur_M8 : Z := 0x35253c9ade8f4ca8.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition uw (z : Z) : Z := bv_unsigned (Z_to_bv 64 z).
Definition murmur_mix (h k : Z) : Z :=
  let x6 := uw k * murmur_M in
  let x7 := Z.shiftr (uw x6) 47 in
  let x8 := Z.lxor (uw x7) (uw x6) in
  let x9 := uw x8 * murmur_M in
  let x10 := Z.lxor (uw x9) (uw h) in
  uw x10 * murmur_M.
(* [comment removed for export] *)
Definition depot_hashC (ws : list Z) : Z :=
  let n := Z.of_nat (length ws) in
  let tag := Z.shiftr (uw n) 32 in
  let x0 := Z.land (uw n) 4294967295 in
  let x1 := uw x0 * murmur_M8 in
  let h0 := Z.lxor (uw x1) murmur_seed in
  let h1 := fold_left murmur_mix ws h0 in
  let h2 := murmur_mix h1 tag in
  let x18 := Z.shiftr (uw h2) 47 in let x19 := Z.lxor (uw x18) (uw h2) in let h3 := uw x19 * murmur_M in
  let x21 := Z.shiftr (uw h3) 47 in Z.lxor (uw x21) (uw h3).
Definition depot_bucket (k : list Z) : Z := depot_hashC k mod 2^20.
(* [comment removed for export] *)
Fixpoint depot_findC (D : list (list Z)) (h : Z) (i : Z) : option Z :=
  match D with [] => None | d :: D' => if Z.eqb (depot_hashC d) h then Some i else depot_findC D' h (i + 1) end.
Definition depot_putC (D : list (list Z)) (k : list Z) : list (list Z) * Z :=
  match depot_findC D (depot_hashC k) 1 with Some id => (D, id) | None => (D ++ [k], Z.of_nat (length D) + 1) end.
(* [comment removed for export] *)
Definition depot_off (D : list (list Z)) (i : nat) : Z := fold_right (fun k acc => 1 + Z.of_nat (length k) + acc) 0 (firstn i D).
Definition depot_total (D : list (list Z)) : Z := depot_off D (length D).
(* [comment removed for export] *)
Fixpoint depot_headC (D : list (list Z)) (b : Z) (i : Z) (cur : Z) : Z :=
  match D with [] => cur | d :: D' => depot_headC D' b (i + 1) (if Z.eqb (depot_bucket d) b then i else cur) end.
Definition depot_linkC (D : list (list Z)) (i : nat) : Z := depot_headC (firstn i D) (depot_bucket (nth i D [])) 1 0.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition site_keys (pcs sites : list Z) : list (list Z) :=
  flat_map (fun pc => [pc] :: map (fun ra => [pc; ra]) sites) pcs.
Lemma site_keys_in2 : forall pcs sites pc ra, In pc pcs -> In ra sites -> In [pc; ra] (site_keys pcs sites).
Proof.
  intros pcs sites pc ra Hp Hr. unfold site_keys. apply in_flat_map. exists pc. split; [exact Hp|].
  right. apply in_map_iff. exists ra. split; [reflexivity| exact Hr].
Qed.
Lemma site_keys_in1 : forall pcs sites pc, In pc pcs -> In [pc] (site_keys pcs sites).
Proof. intros pcs sites pc Hp. unfold site_keys. apply in_flat_map. exists pc. split; [exact Hp| left; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma elem_of_In {A} (x : A) (l : list A) : x ∈ l <-> In x l.
Proof.
  split.
  - induction 1; [left; reflexivity| right; assumption].
  - induction l as [|y l IH]; cbn; [tauto|]. intros [->|H]; [constructor| constructor; exact (IH H)].
Qed.
Lemma NoDup_List {A} (l : list A) : NoDup l <-> List.NoDup l.
Proof.
  split.
  - induction 1 as [|x l NI ND IH]; [constructor|]. constructor; [| exact IH]. intros Hin. apply NI. apply elem_of_In. exact Hin.
  - induction 1 as [|x l NI ND IH]; [constructor|]. constructor; [| exact IH]. intros Hin. apply NI. apply elem_of_In. exact Hin.
Qed.

(* [comment removed for export] *)
Fixpoint zmemb (x : Z) (l : list Z) : bool := match l with [] => false | y :: l' => Z.eqb x y || zmemb x l' end.
Fixpoint znodupb (l : list Z) : bool := match l with [] => true | x :: l' => negb (zmemb x l') && znodupb l' end.
Lemma zmemb_false : forall x l, zmemb x l = false -> ~ In x l.
Proof.
  induction l as [|y l IH]; cbn; intros H; [tauto|]. apply Bool.orb_false_iff in H as [H1 H2].
  intros [E|Hin]; [subst; rewrite Z.eqb_refl in H1; discriminate| exact (IH H2 Hin)].
Qed.
Lemma znodupb_sound : forall l, znodupb l = true -> NoDup l.
Proof.
  intros l H. apply NoDup_List. revert H. induction l as [|x l IH]; cbn; intros H; [constructor|]. apply andb_prop in H as [H1 H2].
  constructor; [| exact (IH H2)]. apply zmemb_false. destruct (zmemb x l); [discriminate| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma depot_findC_bound : forall D h i id, depot_findC D h i = Some id -> i <= id < i + Z.of_nat (length D).
Proof.
  induction D as [|d D IH]; cbn; intros h i id H; [discriminate|].
  destruct (Z.eqb (depot_hashC d) h); [injection H as <-; lia|]. apply IH in H. lia.
Qed.
Lemma depot_putC_cases : forall D k,
  (fst (depot_putC D k) = D /\ 1 <= snd (depot_putC D k) <= Z.of_nat (length D)) \/
  (fst (depot_putC D k) = D ++ [k] /\ snd (depot_putC D k) = Z.of_nat (length D) + 1 /\
   depot_findC D (depot_hashC k) 1 = None).
Proof.
  intros D k. unfold depot_putC. destruct (depot_findC D (depot_hashC k) 1) as [id|] eqn:E; cbn.
  - left. split; [reflexivity|]. apply depot_findC_bound in E. lia.
  - right. repeat split; reflexivity.
Qed.
Lemma depot_findC_none : forall D h i, depot_findC D h i = None -> ~ In h (map depot_hashC D).
Proof.
  induction D as [|d D IH]; cbn; intros h i H; [tauto|].
  destruct (Z.eqb_spec (depot_hashC d) h); [discriminate|]. intros [E|Hin]; [congruence| exact (IH _ _ H Hin)].
Qed.
Lemma depot_putC_incl : forall U D k, incl D U -> In k U -> incl (fst (depot_putC D k)) U.
Proof.
  intros U D k HD Hk. destruct (depot_putC_cases D k) as [[-> _]|(-> & _ & _)]; [exact HD|].
  apply incl_app; [exact HD|]. intros x [<-|[]]. exact Hk.
Qed.
Lemma nodup_map_inj : forall (f : list Z -> Z) U x y, List.NoDup (map f U) -> In x U -> In y U -> f x = f y -> x = y.
Proof.
  induction U as [|u U IH]; cbn; intros x y ND Hx Hy E; [tauto|].
  apply List.NoDup_cons_iff in ND as [NI ND'].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | | exact (IH x y ND' Hx Hy E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.
Lemma nodup_map_of_incl : forall (f : list Z -> Z) U D, NoDup (map f U) -> incl D U -> NoDup D -> NoDup (map f D).
Proof.
  intros f U D NU INC ND. apply NoDup_List. apply NoDup_List in NU. apply NoDup_List in ND. revert INC ND.
  induction D as [|x D IH]; cbn; intros INC ND; [constructor|].
  apply List.NoDup_cons_iff in ND as [NI ND']. constructor.
  - intros Hin. apply in_map_iff in Hin as (y & E & Hy). apply NI.
    rewrite (nodup_map_inj f U x y NU ltac:(apply INC; left; reflexivity) ltac:(apply INC; right; exact Hy) (eq_sym E)). exact Hy.
  - apply IH; [intros z Hz; apply INC; right; exact Hz| exact ND'].
Qed.
Lemma depot_putC_nodup : forall D k, NoDup D -> NoDup (fst (depot_putC D k)).
Proof.
  intros D k ND. destruct (depot_putC_cases D k) as [[-> _]|(-> & _ & NF)]; [exact ND|].
  apply NoDup_List. apply NoDup_List in ND. apply List.NoDup_app; [exact ND| repeat constructor; cbn; tauto|].
  intros a Ha [E|[]]. subst. apply (depot_findC_none D (depot_hashC a) 1 NF). apply in_map. exact Ha.
Qed.
Lemma depot_putC_nonnil : forall D k, D <> [] -> fst (depot_putC D k) <> [].
Proof. intros D k ND. destruct (depot_putC_cases D k) as [[-> _]|(-> & _ & _)]; [exact ND| destruct D; cbn; discriminate]. Qed.
Lemma depot_putC_id_range : forall D k, 1 <= snd (depot_putC D k) <= Z.of_nat (length D) + 1.
Proof. intros D k. destruct (depot_putC_cases D k) as [[_ B]|(_ & -> & _)]; lia. Qed.
Lemma nodup_incl_length : forall (D U : list (list Z)), NoDup D -> incl D U -> (length D <= length U)%nat.
Proof. intros D U ND INC. apply List.NoDup_incl_length; [apply NoDup_List; exact ND| exact INC]. Qed.

(* [comment removed for export] *)
Lemma depot_off_bound : forall D i, Forall (fun k => (1 <= length k <= 255)%nat) D -> 0 <= depot_off D i <= 256 * Z.of_nat i.
Proof.
  intros D i F. unfold depot_off. revert i. induction D as [|d D IH]; intros [|i].
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - inversion F as [|a l Hd F']; subst. specialize (IH F' i). cbn [firstn fold_right]. cbn [firstn] in IH.
    replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia. lia.
Qed.
Lemma depot_total_bound : forall D, Forall (fun k => (1 <= length k <= 255)%nat) D -> 0 <= depot_total D <= 256 * Z.of_nat (length D).
Proof. intros D F. unfold depot_total. apply depot_off_bound. exact F. Qed.

(* [comment removed for export] *)
Lemma depot_universe_bounds : forall U D,
  Forall (fun k => (1 <= length k <= 255)%nat) U -> (length U <= 2048)%nat -> NoDup D -> incl D U ->
  Z.of_nat (length D) <= 2048 /\ Forall (fun k => (1 <= length k <= 255)%nat) D /\ 0 <= depot_total D <= 256 * Z.of_nat (length D).
Proof.
  intros U D FU LU ND INC.
  assert (FD : Forall (fun k => (1 <= length k <= 255)%nat) D).
  { apply Forall_forall. intros k Hk. exact (proj1 (Forall_forall _ _) FU k (INC k Hk)). }
  pose proof (nodup_incl_length D U ND INC). split; [lia|]. split; [exact FD| apply depot_total_bound; exact FD].
Qed.

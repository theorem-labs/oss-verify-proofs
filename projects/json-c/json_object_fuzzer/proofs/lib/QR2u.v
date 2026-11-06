(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzwR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzwR.
Import ListNotations.
Open Scope Z_scope.

Definition put_list {X} (d : X) (l : list X) (i : nat) (x : X) : list X :=
firstn i l ++ repeat d (i - length l) ++ [x] ++ skipn (S i) l.
Definition ins_list {X} (l : list X) (i : nat) (x : X) : list X := firstn i l ++ [x] ++ skipn i l.
Definition del_list {X} (l : list X) (i c : nat) : list X := firstn i l ++ skipn (i + c) l.

Lemma put_kids_eq : forall ks i v, put_kids ks i v = put_list None ks i v.
Proof. reflexivity. Qed.
Lemma ins_kids_eq : forall ks i v, ins_kids ks i v = if (i <? length ks)%nat then ins_list ks i v else put_list None ks i v.
Proof. reflexivity. Qed.
Lemma del_kids_eq : forall ks i c, del_kids ks i c = del_list ks i c.
Proof. reflexivity. Qed.

Lemma put_list_length : forall {X} (d : X) l i x, length (put_list d l i x) = Nat.max (length l) (S i).
Proof. intros. unfold put_list. rewrite !length_app, firstn_length, repeat_length, length_skipn. cbn [length]. lia. Qed.
Lemma ins_list_length : forall {X} (l : list X) i x, (i <= length l)%nat -> length (ins_list l i x) = S (length l).
Proof. intros. unfold ins_list. rewrite !length_app, firstn_length, length_skipn. cbn [length]. lia. Qed.
Lemma del_list_length : forall {X} (l : list X) i c, (i + c <= length l)%nat -> length (del_list l i c) = (length l - c)%nat.
Proof. intros. unfold del_list. rewrite length_app, firstn_length, length_skipn. lia. Qed.

Lemma put_list_lt : forall {X} (d : X) l i x, (i < length l)%nat -> put_list d l i x = upd l i x.
Proof.
intros X d l i x Hi. unfold put_list. replace (i - length l)%nat with 0%nat by lia. cbn [repeat app].
rewrite upd_firstn_skipn by exact Hi. reflexivity.
Qed.

Lemma put_list_ge : forall {X} (d : X) l i x, (length l <= i)%nat -> put_list d l i x = l ++ repeat d (i - length l) ++ [x].
Proof.
intros X d l i x Hi. unfold put_list. rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite app_nil_r. reflexivity.
Qed.
Lemma put_list_map : forall {X Y} (f : X -> Y) d l i x, map f (put_list d l i x) = put_list (f d) (map f l) i (f x).
Proof.
intros. unfold put_list. rewrite !map_app, firstn_map, skipn_map, map_repeat, length_map. reflexivity.
Qed.
Lemma ins_list_map : forall {X Y} (f : X -> Y) l i x, map f (ins_list l i x) = ins_list (map f l) i (f x).
Proof. intros. unfold ins_list. rewrite !map_app, firstn_map, skipn_map. reflexivity. Qed.
Lemma del_list_map : forall {X Y} (f : X -> Y) l i c, map f (del_list l i c) = del_list (map f l) i c.
Proof. intros. unfold del_list. rewrite map_app, firstn_map, skipn_map. reflexivity. Qed.

Lemma concat_repeat_nil : forall {X} k, concat (repeat (@nil X) k) = [].
Proof. intros X k; induction k; cbn; auto. Qed.
Lemma concat_put_list : forall {X} (bss : list (list X)) i bs,
concat (put_list [] bss i bs) = concat (firstn i bss) ++ bs ++ concat (skipn (S i) bss).
Proof.
intros. unfold put_list. rewrite !concat_app, concat_repeat_nil. cbn [concat app]. rewrite app_nil_r. reflexivity.
Qed.
Lemma concat_ins_list : forall {X} (bss : list (list X)) i bs,
concat (ins_list bss i bs) = concat (firstn i bss) ++ bs ++ concat (skipn i bss).
Proof. intros. unfold ins_list. rewrite !concat_app. cbn [concat]. rewrite app_nil_r. reflexivity. Qed.
Lemma concat_del_list : forall {X} (bss : list (list X)) i c,
concat (del_list bss i c) = concat (firstn i bss) ++ concat (skipn (i + c) bss).
Proof. intros. unfold del_list. rewrite concat_app. reflexivity. Qed.
Lemma concat_firstn_skipn : forall {X} (bss : list (list X)) i, concat bss = concat (firstn i bss) ++ concat (skipn i bss).
Proof. intros. rewrite <- concat_app, firstn_skipn. reflexivity. Qed.

Lemma concat_range3 : forall {X} (bss : list (list X)) i j, (i <= j)%nat ->
concat bss = concat (firstn i bss) ++ concat (firstn (j - i) (skipn i bss)) ++ concat (skipn j bss).
Proof.
intros X bss i j Hij. rewrite (concat_firstn_skipn bss i) at 1. f_equal.
rewrite (concat_firstn_skipn (skipn i bss) (j - i)). rewrite skipn_skipn. replace (j - i + i)%nat with j by lia. reflexivity.
Qed.

Section Akids.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation akids := (akids segs fn).
Notation jopt := (jopt segs fn).

#[using="Type"] Lemma akids_nil : forall (m : word -> option byte), akids m [] [] [].
Proof. intros; exact I. Qed.

#[using="Type"] Lemma akids_nth : forall m ks vs bss j v,
akids m ks vs bss -> nth_error vs j = Some v ->
exists k bs, nth_error ks j = Some k /\ nth_error bss j = Some bs /\ jopt k m bs v.
Proof.
intros m ks; induction ks as [|k0 ks IH]; intros [|v0 vs] [|bs0 bss] j v KIDS Hj; try (destruct KIDS; fail); [destruct j; discriminate|].
destruct KIDS as [K1 K2]. destruct j as [|j].
- cbn in Hj. injection Hj as ->. exists k0, bs0. split; [reflexivity|]. split; [reflexivity|]. destruct k0; exact K1.
- cbn in Hj. destruct (IH vs bss j v K2 Hj) as (k & bs & H1 & H2 & H3). exists k, bs. cbn. auto.
Qed.

#[using="Type"] Lemma akids_nth_null : forall m ks vs bss j,
akids m ks vs bss -> nth_error vs j = Some 0 -> nth_error ks j = Some None /\ nth_error bss j = Some [].
Proof.
intros m ks vs bss j KIDS Hj. destruct (akids_nth m ks vs bss j 0 KIDS Hj) as (k & bs & H1 & H2 & H3).
destruct k as [s|]; cbn in H3; [destruct H3 as [H _]; exfalso; apply H; reflexivity|].
destruct H3 as [_ ->]. split; [exact H1 | exact H2].
Qed.

#[using="Type"] Lemma akids_split : forall m ks vs bss i,
akids m ks vs bss ->
akids m (firstn i ks) (firstn i vs) (firstn i bss) /\ akids m (skipn i ks) (skipn i vs) (skipn i bss).
Proof.
intros m ks vs bss i KIDS. destruct (akids_length segs fn _ _ _ _ KIDS) as [L1 L2].
apply (akids_app_inv segs fn m (firstn i ks) (firstn i vs) (firstn i bss) (skipn i ks) (skipn i vs) (skipn i bss)).
- rewrite !firstn_length. lia.
- rewrite !firstn_length. lia.
- rewrite !firstn_skipn. exact KIDS.
Qed.

#[using="Type"] Lemma akids_gap : forall (m : word -> option byte) k, akids m (repeat None k) (repeat 0 k) (repeat [] k).
Proof. intros m k; induction k as [|k IH]; cbn; [exact I|]. split; [split; reflexivity | exact IH]. Qed.

#[using="Type"] Lemma akids_put : forall m ks vs bss i v bs x,
akids m ks vs bss -> jopt v m bs x ->
akids m (put_list None ks i v) (put_list 0 vs i x) (put_list [] bss i bs).
Proof.
intros m ks vs bss i v bs x KIDS J. destruct (akids_length segs fn _ _ _ _ KIDS) as [L1 L2].
unfold put_list. rewrite L1, L2.
destruct (akids_split m ks vs bss i KIDS) as [KA KB].
apply akids_app; [exact KA|]. apply akids_app; [apply akids_gap|].
change (akids m ([v] ++ skipn (S i) ks) ([x] ++ skipn (S i) vs) ([bs] ++ skipn (S i) bss)).
apply akids_app; [apply akids_one; exact J|].
destruct (akids_split m ks vs bss (S i) KIDS) as [_ KC]. exact KC.
Qed.

#[using="Type"] Lemma akids_ins : forall m ks vs bss i v bs x,
akids m ks vs bss -> jopt v m bs x ->
akids m (ins_list ks i v) (ins_list vs i x) (ins_list bss i bs).
Proof.
intros m ks vs bss i v bs x KIDS J. unfold ins_list.
destruct (akids_split m ks vs bss i KIDS) as [KA KB].
apply akids_app; [exact KA|].
change (akids m ([v] ++ skipn i ks) ([x] ++ skipn i vs) ([bs] ++ skipn i bss)).
apply akids_app; [apply akids_one; exact J | exact KB].
Qed.

#[using="Type"] Lemma akids_del : forall m ks vs bss i c,
akids m ks vs bss -> akids m (del_list ks i c) (del_list vs i c) (del_list bss i c).
Proof.
intros m ks vs bss i c KIDS. unfold del_list.
destruct (akids_split m ks vs bss i KIDS) as [KA _]. destruct (akids_split m ks vs bss (i + c) KIDS) as [_ KB].
apply akids_app; [exact KA | exact KB].
Qed.

#[using="Type"] Lemma akids_outside : forall m ks vs bss i j,
akids m ks vs bss ->
akids m (firstn i ks ++ skipn j ks) (firstn i vs ++ skipn j vs) (firstn i bss ++ skipn j bss).
Proof.
intros m ks vs bss i j KIDS.
destruct (akids_split m ks vs bss i KIDS) as [KA _]. destruct (akids_split m ks vs bss j KIDS) as [_ KB].
apply akids_app; [exact KA | exact KB].
Qed.

#[using="Type"] Lemma akids_blocks_incl_j : forall (bss : list (list blk)) j bs,
nth_error bss j = Some bs -> incl bs (concat bss).
Proof.
intros bss j bs Hj b Hb. apply in_concat. exists bs. split; [| exact Hb].
eapply nth_error_In. exact Hj.
Qed.

#[using="Type"] Lemma akids_put_rm : forall m ks vs bss i v bs x,
length vs = length ks -> length bss = length ks ->
akids m (firstn i ks ++ skipn (S i) ks) (firstn i vs ++ skipn (S i) vs) (firstn i bss ++ skipn (S i) bss) ->
jopt v m bs x ->
akids m (put_list None ks i v) (put_list 0 vs i x) (put_list [] bss i bs).
Proof.
intros m ks vs bss i v bs x L1 L2 KIDS J. unfold put_list. rewrite L1, L2.
destruct (akids_app_inv segs fn m (firstn i ks) (firstn i vs) (firstn i bss) _ _ _
ltac:(rewrite !length_firstn; lia) ltac:(rewrite !length_firstn; lia) KIDS) as [KA KB].
apply akids_app; [exact KA|]. apply akids_app; [apply akids_gap|].
change (akids m ([v] ++ skipn (S i) ks) ([x] ++ skipn (S i) vs) ([bs] ++ skipn (S i) bss)).
apply akids_app; [apply akids_one; exact J | exact KB].
Qed.

#[using="Type"] Lemma akids_rm : forall m ks vs bss i,
akids m ks vs bss -> akids m (firstn i ks ++ skipn (S i) ks) (firstn i vs ++ skipn (S i) vs) (firstn i bss ++ skipn (S i) bss).
Proof. intros. apply akids_outside. assumption. Qed.
End Akids.

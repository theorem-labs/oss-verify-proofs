(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ub_rot_right_npf (ns : NS) (pp p : Z) : option NS :=
  plr ← get_right ns p ;
  ns1 ← set_left ns pp plr ;
  ns2 ← (if plr =? 0 then Some ns1 else set_parent ns1 plr pp) ;
  ns3 ← set_right ns2 p pp ;
  set_parent ns3 pp p.

(* [comment removed for export] *)
Definition ub_set_child (ns : NS) (h gpp gppl gp q : Z) : option NS :=
  if gpp =? h then set_parent ns h q
  else if gppl =? gp then set_left ns gpp q
  else set_right ns gpp q.

Definition ub_rotate_left (ns : NS) (h gp q gpp : Z) : option NS :=
  gppl ← get_left ns gpp ;
  ns4 ← rb_rot_left_npf ns gp q ;
  ns5 ← set_parent ns4 q gpp ;
  ub_set_child ns5 h gpp gppl gp q.

Definition ub_rotate_right (ns : NS) (h gp q gpp : Z) : option NS :=
  gppl ← get_left ns gpp ;
  ns4 ← ub_rot_right_npf ns gp q ;
  ns5 ← set_parent ns4 q gpp ;
  ub_set_child ns5 h gpp gppl gp q.

(* [comment removed for export] *)
Lemma store_Some_inv ns a off v ns' : store ns a off v = Some ns' ->
  exists nd, ns !! a = Some nd /\ ns' = <[a := set_field off v nd]> ns.
Proof. unfold store. destruct (ns !! a) as [nd|]; cbn; [| discriminate]. intros H. injection H as <-. eauto. Qed.

Lemma load_store_other ns a off v ns' b off' :
  store ns a off v = Some ns' -> (a <> b \/ off <> off') ->
  (off =? OFF_PARENT) || (off =? OFF_LEFT) || (off =? OFF_RIGHT) || (off =? OFF_COLOR) = true ->
  (off' =? OFF_PARENT) || (off' =? OFF_LEFT) || (off' =? OFF_RIGHT) || (off' =? OFF_COLOR) = true ->
  load ns' b off' = load ns b off'.
Proof.
  intros ST NE O1 O2. destruct (store_Some_inv _ _ _ _ _ ST) as (nd & L & ->).
  unfold load. destruct (Z.eq_dec a b) as [<-|NEab].
  - rewrite L. rewrite lookup_insert_eq. cbn. f_equal. destruct NE as [NE|NE]; [exfalso; exact (NE eq_refl)|].
    unfold get_field, set_field, OFF_PARENT, OFF_LEFT, OFF_RIGHT, OFF_COLOR in *.
    destruct (Z.eqb_spec off 0); destruct (Z.eqb_spec off 8); destruct (Z.eqb_spec off 16); destruct (Z.eqb_spec off 24);
    destruct (Z.eqb_spec off' 0); destruct (Z.eqb_spec off' 8); destruct (Z.eqb_spec off' 16); destruct (Z.eqb_spec off' 24);
    subst; cbn in *; try reflexivity; try lia; try discriminate.
  - rewrite lookup_insert_ne by exact NEab. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_store_comm ns a off v b off' v' :
  (a <> b \/ off <> off') ->
  (off =? OFF_PARENT) || (off =? OFF_LEFT) || (off =? OFF_RIGHT) || (off =? OFF_COLOR) = true ->
  (off' =? OFF_PARENT) || (off' =? OFF_LEFT) || (off' =? OFF_RIGHT) || (off' =? OFF_COLOR) = true ->
  (ns1 ← store ns a off v ; store ns1 b off' v') = (ns1 ← store ns b off' v' ; store ns1 a off v).
Proof.
  intros NE O1 O2. unfold store.
  destruct (ns !! a) as [nda|] eqn:La; destruct (ns !! b) as [ndb|] eqn:Lb; cbn.
  - destruct (Z.eq_dec a b) as [<-|NEab].
    + rewrite La in Lb. injection Lb as <-. rewrite !lookup_insert_eq. cbn. f_equal. rewrite !insert_insert_eq. f_equal.
      destruct NE as [NE|NE]; [exfalso; exact (NE eq_refl)|].
      unfold set_field, OFF_PARENT, OFF_LEFT, OFF_RIGHT, OFF_COLOR in *.
      destruct (Z.eqb_spec off 0); destruct (Z.eqb_spec off 8); destruct (Z.eqb_spec off 16); destruct (Z.eqb_spec off 24);
      destruct (Z.eqb_spec off' 0); destruct (Z.eqb_spec off' 8); destruct (Z.eqb_spec off' 16); destruct (Z.eqb_spec off' 24);
      subst; cbn in *; try reflexivity; try lia; try discriminate.
    + rewrite lookup_insert_ne by exact NEab. rewrite lookup_insert_ne by (intros E; apply NEab; symmetry; exact E).
      rewrite La, Lb. cbn. f_equal. apply insert_insert_ne. intros E; apply NEab; symmetry; exact E.
  - destruct (Z.eq_dec a b) as [<-|NEab]; [rewrite La in Lb; discriminate|].
    rewrite lookup_insert_ne by exact NEab. rewrite Lb. reflexivity.
  - destruct (Z.eq_dec a b) as [<-|NEab]; [rewrite La in Lb; discriminate|].
    rewrite lookup_insert_ne by (intros E; apply NEab; symmetry; exact E). rewrite La. reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ub_rot_right_npf_eq ns pp p ns4 c :
  rb_rot_right_npf ns pp p = Some (ns4, c) -> ub_rot_right_npf ns pp p = Some ns4 /\ get_left ns4 p = Some c.
Proof.
  unfold rb_rot_right_npf, ub_rot_right_npf. intros H.
  destruct (get_right ns p) as [plr|]; cbn in *; [| discriminate].
  destruct (set_left ns pp plr) as [ns1|]; cbn in *; [| discriminate].
  destruct (if plr =? 0 then Some ns1 else set_parent ns1 plr pp) as [ns2|]; cbn in *; [| discriminate].
  destruct (get_left ns2 p) as [c'|] eqn:GL; cbn in *; [| discriminate].
  destruct (set_right ns2 p pp) as [ns3|] eqn:S3; cbn in *; [| discriminate].
  destruct (set_parent ns3 pp p) as [ns4'|] eqn:S4; cbn in *; [| discriminate].
  injection H as <- <-. split; [reflexivity|].
  unfold get_left in *. rewrite (load_store_other _ _ _ _ _ _ _ S4) by (first [right; unfold OFF_PARENT, OFF_LEFT; lia | reflexivity]).
  rewrite (load_store_other _ _ _ _ _ _ _ S3) by (first [right; unfold OFF_RIGHT, OFF_LEFT; lia | reflexivity]). exact GL.
Qed.

Lemma bind_ext {A B} (m : option A) (k1 k2 : A -> option B) :
  (forall x, k1 x = k2 x) -> (x ← m ; k1 x) = (x ← m ; k2 x).
Proof. intros E. destruct m; cbn; [apply E| reflexivity]. Qed.

Local Ltac under := apply bind_ext; intros ?.
Local Ltac offs := first [left; assumption | right; unfold OFF_PARENT, OFF_LEFT, OFF_RIGHT, OFF_COLOR; lia | reflexivity].

(* [comment removed for export] *)
Lemma store_store_comm_k {R} ns a off v b off' v' (K : NS -> option R) :
  (a <> b \/ off <> off') ->
  (off =? OFF_PARENT) || (off =? OFF_LEFT) || (off =? OFF_RIGHT) || (off =? OFF_COLOR) = true ->
  (off' =? OFF_PARENT) || (off' =? OFF_LEFT) || (off' =? OFF_RIGHT) || (off' =? OFF_COLOR) = true ->
  (ns1 ← store ns a off v ; ns2 ← store ns1 b off' v' ; K ns2) = (ns1 ← store ns b off' v' ; ns2 ← store ns1 a off v ; K ns2).
Proof.
  intros NE O1 O2.
  transitivity (ns2 ← (ns1 ← store ns a off v ; store ns1 b off' v') ; K ns2); [rewrite obind_assoc; reflexivity|].
  rewrite (store_store_comm ns a off v b off' v' NE O1 O2). rewrite obind_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ub_rotate_left_eq0 ns h gp q c gpp :
  get_left ns q = Some c -> get_parent ns gp = Some gpp ->
  rb_rotate_left_full ns h gp q c = (ns5 ← ub_rotate_left ns h gp q gpp ; set_color ns5 q BLACK).
Proof.
  intros GL GP. unfold rb_rotate_left_full, ub_rotate_left, rb_rot_left_npf, rb_set_child_black, ub_set_child.
  rewrite GP. cbn [mbind option_bind]. rewrite GL.
  (* [comment removed for export] *)
  rewrite !obind_assoc. under. cbn [mbind option_bind]. rewrite !obind_assoc. under. rewrite !obind_assoc. under.
  (* [comment removed for export] *)
  rewrite !obind_assoc.
  unfold set_parent, set_left, set_right.
  rewrite (store_store_comm_k x1 q OFF_LEFT gp gp OFF_PARENT q) by offs.
  under. rewrite (store_store_comm_k _ q OFF_PARENT gpp q OFF_LEFT gp) by offs.
  rewrite ?obind_assoc. under. rewrite ?obind_assoc. under. rewrite ?obind_assoc. reflexivity.
Qed.

Lemma ub_rotate_right_eq0 ns h gp q gpp :
  get_parent ns gp = Some gpp ->
  rb_rotate_right_full ns h gp q = (ns5 ← ub_rotate_right ns h gp q gpp ; set_color ns5 q BLACK).
Proof.
  intros GP. unfold rb_rotate_right_full, ub_rotate_right, ub_rot_right_npf, rb_set_child_black, ub_set_child.
  rewrite GP. cbn [mbind option_bind].
  destruct (get_right ns q) as [a5|]; destruct (get_left ns gpp) as [a4|]; cbn [mbind option_bind]; try reflexivity.
  rewrite ?obind_assoc. under. rewrite ?obind_assoc. under.
  unfold set_parent, set_left, set_right. rewrite ?obind_assoc.
  rewrite (store_store_comm_k _ q OFF_RIGHT gp gp OFF_PARENT q) by offs.
  under. rewrite (store_store_comm_k _ q OFF_PARENT gpp q OFF_RIGHT gp) by offs.
  rewrite ?obind_assoc. under. rewrite ?obind_assoc. under. rewrite ?obind_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ub_rotate_left_eq ns h gp q c ns6 :
  rb_rotate_left_full ns h gp q c = Some ns6 -> get_left ns q = Some c ->
  exists gpp ns5, get_parent ns gp = Some gpp /\ ub_rotate_left ns h gp q gpp = Some ns5 /\ set_color ns5 q BLACK = Some ns6.
Proof.
  intros H GL.
  destruct (get_parent ns gp) as [gpp|] eqn:GP.
  2:{ exfalso. unfold rb_rotate_left_full in H. rewrite GP in H. discriminate. }
  rewrite (ub_rotate_left_eq0 ns h gp q c gpp GL GP) in H.
  destruct (ub_rotate_left ns h gp q gpp) as [ns5|] eqn:U; [| discriminate]. cbn in H.
  exists gpp, ns5. split; [reflexivity| split; [exact U| exact H]].
Qed.

Lemma ub_rotate_right_eq ns h gp q ns6 :
  rb_rotate_right_full ns h gp q = Some ns6 ->
  exists gpp ns5, get_parent ns gp = Some gpp /\ ub_rotate_right ns h gp q gpp = Some ns5 /\ set_color ns5 q BLACK = Some ns6.
Proof.
  intros H.
  destruct (get_parent ns gp) as [gpp|] eqn:GP.
  2:{ exfalso. unfold rb_rotate_right_full in H. rewrite GP in H. discriminate. }
  rewrite (ub_rotate_right_eq0 ns h gp q gpp GP) in H.
  destruct (ub_rotate_right ns h gp q gpp) as [ns5|] eqn:U; [| discriminate]. cbn in H.
  exists gpp, ns5. split; [reflexivity| split; [exact U| exact H]].
Qed.


(* [comment removed for export] *)
Lemma cols_ok_set X ns a nd nd' : cols_ok X ns -> ns !! a = Some nd -> (n_col nd' = n_col nd \/ col_ok nd') ->
  cols_ok X (<[a := nd']> ns).
Proof.
  intros CO L H b ndb Lb NI. destruct (decide (b = a)) as [->|NE].
  - rewrite lookup_insert_eq in Lb. injection Lb as <-.
    destruct H as [E|OK]; [| exact OK]. unfold col_ok. rewrite E. exact (CO a nd L NI).
  - rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E). exact (CO b ndb Lb NI).
Qed.

Lemma cols_ok_clear ns a nd nd' : cols_ok [a] ns -> ns !! a = Some nd -> col_ok nd' -> cols_ok [] (<[a := nd']> ns).
Proof.
  intros CO L OK b ndb Lb _. destruct (decide (b = a)) as [->|NE].
  - rewrite lookup_insert_eq in Lb. injection Lb as <-. exact OK.
  - rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E). apply (CO b ndb Lb). rewrite elem_of_cons, elem_of_nil. intros [E|F]; [exact (NE E)| exact F].
Qed.

(* [comment removed for export] *)
Lemma cols_ok_store_link X ns a off v ns' : cols_ok X ns -> store ns a off v = Some ns' ->
  (off = OFF_PARENT \/ off = OFF_LEFT \/ off = OFF_RIGHT) -> cols_ok X ns'.
Proof.
  intros CO ST OFF. destruct (store_Some_inv _ _ _ _ _ ST) as (nd & L & ->).
  eapply cols_ok_set; [exact CO| exact L| left].
  unfold set_field, OFF_PARENT, OFF_LEFT, OFF_RIGHT in *. destruct OFF as [->|[->| ->]]; reflexivity.
Qed.

Lemma insert_commit_cols X ns h new ll nd ns' : cols_ok X ns -> insert_commit ns h new ll nd = Some ns' -> cols_ok X ns'.
Proof.
  intros CO IC. unfold insert_commit in IC. destruct (nd =? 0); [discriminate|].
  destruct (if nd =? h then _ else _) as [ns3|] eqn:E3; [cbn in IC| discriminate].
  assert (CO3 : cols_ok X ns3).
  { destruct (nd =? h).
    - destruct (set_parent ns h new) as [ns1|] eqn:S1; [cbn in E3| discriminate].
      destruct (set_left ns1 h new) as [ns2|] eqn:S2; [cbn in E3| discriminate].
      eapply cols_ok_store_link; [| exact E3| unfold OFF_RIGHT; lia].
      eapply cols_ok_store_link; [| exact S2| unfold OFF_LEFT; lia].
      eapply cols_ok_store_link; [exact CO| exact S1| unfold OFF_PARENT; lia].
    - destruct ll.
      + destruct (set_left ns nd new) as [ns1|] eqn:S1; [cbn in E3| discriminate].
        pose proof (cols_ok_store_link _ _ _ _ _ _ CO S1 ltac:(unfold OFF_LEFT; lia)) as CO1.
        destruct (get_left ns1 h) as [hl|]; [cbn in E3| discriminate].
        destruct (nd =? hl); [| injection E3 as <-; exact CO1].
        eapply cols_ok_store_link; [exact CO1| exact E3| unfold OFF_LEFT; lia].
      + destruct (set_right ns nd new) as [ns1|] eqn:S1; [cbn in E3| discriminate].
        pose proof (cols_ok_store_link _ _ _ _ _ _ CO S1 ltac:(unfold OFF_RIGHT; lia)) as CO1.
        destruct (get_right ns1 h) as [hr|]; [cbn in E3| discriminate].
        destruct (nd =? hr); [| injection E3 as <-; exact CO1].
        eapply cols_ok_store_link; [exact CO1| exact E3| unfold OFF_RIGHT; lia]. }
  destruct (set_parent ns3 new nd) as [ns4|] eqn:S4; [cbn in IC| discriminate].
  destruct (set_left ns4 new 0) as [ns5|] eqn:S5; [cbn in IC| discriminate].
  eapply cols_ok_store_link; [| exact IC| unfold OFF_RIGHT; lia].
  eapply cols_ok_store_link; [| exact S5| unfold OFF_LEFT; lia].
  eapply cols_ok_store_link; [exact CO3| exact S4| unfold OFF_PARENT; lia].
Qed.

(* [comment removed for export] *)
Lemma oloop_body_Some {A R} fuel (body : A -> option (A + R)) x r :
  oloop fuel body x = Some r -> exists s, body x = Some s.
Proof. destruct fuel; cbn; [discriminate|]. destruct (body x); [intros; eexists; reflexivity| discriminate]. Qed.


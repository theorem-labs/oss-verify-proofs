(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocInv_defs MallocInv_sep.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_error_nth : forall (l : list Z) k x d, nth_error l k = Some x -> nth k l d = x.
Proof. intros l k x d H. apply nth_error_nth with (d := d) in H. exact H. Qed.

Lemma nth_error_app_l : forall {T} (l1 l2 : list T) k, (k < length l1)%nat -> nth_error (l1 ++ l2) k = nth_error l1 k.
Proof. intros. apply nth_error_app1. assumption. Qed.

Lemma nth_error_app_r : forall {T} (l1 l2 : list T) k, (length l1 <= k)%nat -> nth_error (l1 ++ l2) k = nth_error l2 (k - length l1).
Proof. intros. apply nth_error_app2. assumption. Qed.

Lemma nth_app_l : forall (l1 l2 : list Z) k d, (k < length l1)%nat -> nth k (l1 ++ l2) d = nth k l1 d.
Proof. intros. apply app_nth1. assumption. Qed.

Lemma nth_app_r : forall (l1 l2 : list Z) k d, (length l1 <= k)%nat -> nth k (l1 ++ l2) d = nth (k - length l1) l2 d.
Proof. intros. apply app_nth2. assumption. Qed.

Lemma hd_nth : forall (l : list Z) d, hd d l = nth 0 l d.
Proof. intros [|x l] d; reflexivity. Qed.

Lemma last_nth : forall (l : list Z) d, l <> [] -> last l d = nth (length l - 1) l d.
Proof.
  induction l as [|x l IH]; intros d Hne; [contradiction|].
  destruct l as [|y l']; [reflexivity|].
  cbn [length]. replace (S (S (length l')) - 1)%nat with (S (length l')) by llia.
  change (last (x :: y :: l') d) with (last (y :: l') d). rewrite IH by discriminate.
  cbn [length]. replace (S (length l') - 1)%nat with (length l') by llia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod_small_nat : forall a n, (a < n)%nat -> (a mod n = a)%nat.
Proof. intros. apply Nat.mod_small. assumption. Qed.

Lemma succ_mod_last : forall n, (0 < n)%nat -> (S (n - 1) mod n = 0)%nat.
Proof. intros n Hn. replace (S (n - 1)) with n by llia. apply Nat.Div0.mod_same. Qed.

Lemma succ_mod_mid : forall k n, (S k < n)%nat -> (S k mod n = S k)%nat.
Proof. intros. apply Nat.mod_small. llia. Qed.

Lemma pred_mod_0 : forall n, (0 < n)%nat -> ((0 + n - 1) mod n = n - 1)%nat.
Proof. intros n Hn. rewrite Nat.add_0_l. apply Nat.mod_small. llia. Qed.

Lemma pred_mod_mid : forall k n, (0 < k < n)%nat -> ((k + n - 1) mod n = k - 1)%nat.
Proof.
  intros k n Hk. replace (k + n - 1)%nat with ((k - 1) + 1 * n)%nat by llia.
  rewrite Nat.Div0.mod_add. apply Nat.mod_small. llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DLL.
  Variable A : astate.

  (* [comment removed for export] *)
  Definition dll_at (l : list Z) (k : nat) (x : Z) : Prop :=
    exists mt, a_meta A x = Some mt /\
      mt_next mt = nth (S k mod length l) l 0 /\
      mt_prev mt = nth ((k + length l - 1) mod length l)%nat l 0.

  Lemma dll_intro : forall l, (forall k x, nth_error l k = Some x -> dll_at l k x) -> dll A l.
  Proof. intros l H. exact H. Qed.

  Lemma dll_elim : forall l k x, dll A l -> nth_error l k = Some x -> dll_at l k x.
  Proof. intros l k x H Hk. exact (H k x Hk). Qed.

  (* [comment removed for export] *)
  Lemma dll_single : forall x mt, a_meta A x = Some mt -> mt_next mt = x -> mt_prev mt = x -> dll A [x].
  Proof.
    intros x mt Hx Hn Hp k y Hk. destruct k as [|k]; [| cbn in Hk; destruct k; discriminate].
    cbn in Hk. injection Hk as <-. exists mt. cbn. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma dll_at_spec : forall l k x, (k < length l)%nat ->
    dll_at l k x <->
    exists mt, a_meta A x = Some mt /\
      mt_next mt = (if (S k <? length l)%nat then nth (S k) l 0 else nth 0 l 0) /\
      mt_prev mt = (if (0 <? k)%nat then nth (k - 1) l 0 else nth (length l - 1) l 0).
  Proof.
    intros l k x Hk. unfold dll_at.
    assert (En : (S k mod length l)%nat = if (S k <? length l)%nat then S k else 0%nat).
    { destruct (S k <? length l)%nat eqn:E; [apply Nat.ltb_lt in E; apply Nat.mod_small; llia | apply Nat.ltb_ge in E].
      replace (S k) with (length l) by llia. apply Nat.Div0.mod_same. }
    assert (Ep : ((k + length l - 1) mod length l)%nat = if (0 <? k)%nat then (k - 1)%nat else (length l - 1)%nat).
    { destruct (0 <? k)%nat eqn:E; [apply Nat.ltb_lt in E; apply pred_mod_mid; llia | apply Nat.ltb_ge in E].
      replace k with 0%nat by llia. apply pred_mod_0. llia. }
    rewrite En, Ep.
    split; intros (mt & H1 & H2 & H3); exists mt; (split; [exact H1|]); split.
    - destruct (S k <? length l)%nat; exact H2.
    - destruct (0 <? k)%nat; exact H3.
    - destruct (S k <? length l)%nat; exact H2.
    - destruct (0 <? k)%nat; exact H3.
  Qed.
End DLL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Ops.
  Variables (A A' : astate).

  (* [comment removed for export] *)
  Lemma dll_rotate : forall h rest, dll A (h :: rest) -> dll A (rest ++ [h]).
  Proof.
    intros h rest Hd k x Hk.
    set (n := length (h :: rest)).
    assert (Hlen : length (rest ++ [h]) = n) by (unfold n; rewrite length_app; cbn; llia).
    assert (Hkn : (k < n)%nat) by (rewrite <- Hlen; apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
    (* [comment removed for export] *)
    assert (Horig : nth_error (h :: rest) (S k mod n) = Some x).
    { destruct (Nat.eq_dec (S k) n) as [E | NE].
      - rewrite E, Nat.Div0.mod_same. cbn. rewrite nth_error_app_r in Hk by (unfold n in E; cbn in E; llia).
        replace (k - length rest)%nat with 0%nat in Hk by (unfold n in E; cbn in E; llia). cbn in Hk. exact Hk.
      - rewrite Nat.mod_small by llia. cbn. rewrite nth_error_app_l in Hk by (unfold n in *; cbn in *; llia). exact Hk. }
    destruct (Hd _ _ Horig) as (mt & Hx & Hn & Hp). exists mt. split; [exact Hx|].
    rewrite Hlen. change (length (h :: rest)) with n in Hn, Hp.
    assert (ROT : forall j, (j < n)%nat -> nth j (rest ++ [h]) 0 = nth (S j mod n) (h :: rest) 0).
    { intros j Hj. destruct (Nat.eq_dec (S j) n) as [E | NE'].
      - rewrite E, Nat.Div0.mod_same. cbn. rewrite nth_app_r by (unfold n in E; cbn in E; llia).
        replace (j - length rest)%nat with 0%nat by (unfold n in E; cbn in E; llia). reflexivity.
      - rewrite Nat.mod_small by llia. cbn. rewrite nth_app_l by (unfold n in *; cbn in *; llia). reflexivity. }
    split.
    - rewrite Hn. rewrite ROT by (apply Nat.mod_upper_bound; llia). reflexivity.
    - rewrite Hp. rewrite ROT by (apply Nat.mod_upper_bound; llia). f_equal.
      destruct (Nat.eq_dec k 0) as [-> | Kp].
      + rewrite pred_mod_0, succ_mod_last by llia.
        destruct (Nat.eq_dec n 1) as [E1|NE1]; [rewrite E1; reflexivity|].
        rewrite (Nat.mod_small 1) by llia. rewrite pred_mod_mid by llia. reflexivity.
      + rewrite (pred_mod_mid k n) by llia. replace (S (k - 1)) with k by llia. rewrite (Nat.mod_small k) by llia.
        destruct (Nat.eq_dec (S k) n) as [E|NE].
        * rewrite E, Nat.Div0.mod_same. rewrite pred_mod_0 by llia. llia.
        * rewrite (Nat.mod_small (S k)) by llia. rewrite pred_mod_mid by llia. llia.
  Qed.

  (* [comment removed for export] *)
  Lemma dll_snoc : forall l m,
    l <> [] -> dll A l ->
    (forall k x mt, nth_error l k = Some x -> a_meta A x = Some mt ->
       exists mt', a_meta A' x = Some mt' /\
         mt_next mt' = (if (S k =? length l)%nat then m else mt_next mt) /\
         mt_prev mt' = (if (k =? 0)%nat then m else mt_prev mt)) ->
    (exists mt', a_meta A' m = Some mt' /\ mt_next mt' = hd 0 l /\ mt_prev mt' = last l 0) ->
    dll A' (l ++ [m]).
  Proof.
    intros l m Hne Hd Hold (mtm & Hm & Hmn & Hmp).
    assert (Hn0 : (0 < length l)%nat) by (destruct l; [contradiction | cbn; llia]).
    intros k x Hk.
    assert (Hkb : (k < length (l ++ [m]))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
    apply (proj2 (dll_at_spec A' (l ++ [m]) k x Hkb)). rewrite length_app in Hkb. cbn [length] in Hkb.
    rewrite length_app. cbn [length].
    destruct (Nat.lt_ge_cases k (length l)) as [Hkl | Hkl].
    - (* [comment removed for export] *)
      rewrite nth_error_app_l in Hk by exact Hkl.
      destruct (Hd k x Hk) as (mt & Hx & Hxn & Hxp).
      destruct (Hold k x mt Hk Hx) as (mt' & Hx' & Hn' & Hp'). exists mt'. split; [exact Hx'|].
      split.
      + rewrite Hn'. destruct (Nat.eq_dec (S k) (length l)) as [E | NE].
        * rewrite (proj2 (Nat.eqb_eq _ _) E). replace (S k <? length l + 1)%nat with true by (symmetry; apply Nat.ltb_lt; llia).
          rewrite nth_app_r by llia. replace (S k - length l)%nat with 0%nat by llia. reflexivity.
        * rewrite (proj2 (Nat.eqb_neq _ _) NE). replace (S k <? length l + 1)%nat with true by (symmetry; apply Nat.ltb_lt; llia).
          rewrite nth_app_l by llia. rewrite Hxn. rewrite Nat.mod_small by llia. reflexivity.
      + rewrite Hp'. destruct (Nat.eq_dec k 0) as [-> | NE].
        * cbn [Nat.eqb]. replace (0 <? 0)%nat with false by reflexivity.
          rewrite nth_app_r by llia. replace (length l + 1 - 1 - length l)%nat with 0%nat by llia. reflexivity.
        * rewrite (proj2 (Nat.eqb_neq _ _) NE). replace (0 <? k)%nat with true by (symmetry; apply Nat.ltb_lt; llia).
          rewrite nth_app_l by llia. rewrite Hxp. rewrite pred_mod_mid by llia. reflexivity.
    - (* [comment removed for export] *)
      rewrite nth_error_app_r in Hk by exact Hkl.
      assert (k = length l) by (destruct (k - length l)%nat eqn:E; [llia | cbn in Hk; destruct n; discriminate]). subst k.
      rewrite Nat.sub_diag in Hk. cbn in Hk. injection Hk as <-.
      exists mtm. split; [exact Hm|]. split.
      + rewrite Hmn. replace (S (length l) <? length l + 1)%nat with false by (symmetry; apply Nat.ltb_ge; llia).
        rewrite nth_app_l by llia. apply hd_nth.
      + rewrite Hmp. replace (0 <? length l)%nat with true by (symmetry; apply Nat.ltb_lt; llia).
        rewrite nth_app_l by llia. rewrite last_nth by exact Hne. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dll_single' : forall m mt, a_meta A' m = Some mt -> mt_next mt = m -> mt_prev mt = m -> dll A' [m].
  Proof. intros. eapply dll_single; eauto. Qed.

  (* [comment removed for export] *)
  Lemma dll_remove : forall l1 x l2,
    let l := l1 ++ x :: l2 in
    let n := length l in
    let i := length l1 in
    let xn := nth (S i mod n) l 0 in
    let xp := nth ((i + n - 1) mod n)%nat l 0 in
    NoDup l -> l1 ++ l2 <> [] -> dll A l ->
    (forall k y mt, nth_error (l1 ++ l2) k = Some y -> a_meta A y = Some mt ->
       exists mt', a_meta A' y = Some mt' /\
         mt_next mt' = (if y =? xp then xn else mt_next mt) /\
         mt_prev mt' = (if y =? xn then xp else mt_prev mt)) ->
    dll A' (l1 ++ l2).
  Proof.
    intros l1 x l2 l n i xn xp Hnd Hne Hd Hnew.
    assert (Hn : n = S (length l1 + length l2)) by (unfold n, l; rewrite length_app; cbn; llia).
    assert (Hi : (i < n)%nat) by (unfold i; llia).
    assert (Hn2 : (2 <= n)%nat).
    { assert (Hl12 : (0 < length l1 + length l2)%nat) by (rewrite <- length_app; destruct (l1 ++ l2); [exfalso; apply Hne; reflexivity | cbn; llia]). llia. }
    (* [comment removed for export] *)
    assert (POS : forall k, (k < length l1 + length l2)%nat ->
              nth_error (l1 ++ l2) k = nth_error l (if (k <? i)%nat then k else S k) /\
              nth k (l1 ++ l2) 0 = nth (if (k <? i)%nat then k else S k) l 0).
    { intros k Hk. unfold l, i. destruct (k <? length l1)%nat eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E].
      - rewrite nth_error_app_l, nth_app_l by llia. rewrite nth_error_app_l, nth_app_l by llia. auto.
      - rewrite nth_error_app_r, nth_app_r by llia. rewrite nth_error_app_r, nth_app_r by llia.
        replace (S k - length l1)%nat with (S (k - length l1)) by llia. cbn. auto. }
    (* [comment removed for export] *)
    assert (INJ : forall a b, (a < n)%nat -> (b < n)%nat -> nth a l 0 = nth b l 0 -> a = b).
    { intros a b Ha Hb E. apply (proj1 (NoDup_nth l 0) Hnd a b Ha Hb E). }
    assert (Hx : nth i l 0 = x) by (unfold l, i; rewrite nth_app_r by llia; rewrite Nat.sub_diag; reflexivity).
    intros k y Hk.
    assert (Hkb : (k < length (l1 ++ l2))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
    rewrite length_app in Hkb.
    apply (proj2 (dll_at_spec A' (l1 ++ l2) k y ltac:(rewrite length_app; exact Hkb))). rewrite length_app.
    destruct (POS k Hkb) as [P1 P2]. rewrite P1 in Hk.
    set (k0 := if (k <? i)%nat then k else S k) in *.
    assert (Hk0 : (k0 < n)%nat /\ k0 <> i) by (subst k0; destruct (k <? i)%nat eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; llia).
    destruct (Hd k0 y Hk) as (mt & Hy & Hyn & Hyp). fold n in Hyn, Hyp.
    destruct (Hnew k y mt ltac:(rewrite P1; exact Hk) Hy) as (mt' & Hy' & Hn' & Hp').
    pose proof (nth_error_nth l k0 y 0 Hk) as Ey.
    exists mt'. split; [exact Hy'|]. split.
    - (* [comment removed for export] *) rewrite Hn', Hyn. unfold xp, xn.
      destruct (Z.eqb_spec y (nth ((i + n - 1) mod n) l 0)) as [E | NE].
      + (* [comment removed for export] *)
        rewrite <- Ey in E. apply INJ in E; [| llia | apply Nat.mod_upper_bound; llia].
        destruct (S k <? length l1 + length l2)%nat eqn:L; [apply Nat.ltb_lt in L | apply Nat.ltb_ge in L].
        * destruct (POS (S k) L) as [_ ->].
          destruct (Nat.eq_dec i 0) as [I0 | I0].
          { exfalso. rewrite I0, pred_mod_0 in E by llia. subst k0. rewrite I0 in *. cbn in E. llia. }
          rewrite pred_mod_mid in E by llia.
          assert (k = i - 1)%nat by (subst k0; destruct (k <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E2]; llia). subst k.
          replace (S (i - 1) <? i)%nat with false by (symmetry; apply Nat.ltb_ge; llia).
          replace (S (S (i - 1))) with (S i) by llia. rewrite Nat.mod_small by llia. reflexivity.
        * (* [comment removed for export] *)
          assert (k = length l1 + length l2 - 1)%nat by llia. subst k.
          destruct (Nat.eq_dec i 0) as [I0 | I0].
          -- (* [comment removed for export] *)
             rewrite I0. rewrite (Nat.mod_small 1) by llia. destruct (POS 0%nat ltac:(llia)) as [_ ->]. rewrite I0. cbn. reflexivity.
          -- (* [comment removed for export] *)
             rewrite pred_mod_mid in E by llia.
             assert (i = n - 1)%nat by (subst k0; destruct (length l1 + length l2 - 1 <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E2]; llia).
             replace (S i) with n by llia. rewrite Nat.Div0.mod_same.
             destruct (POS 0%nat ltac:(llia)) as [_ ->]. replace (0 <? i)%nat with true by (symmetry; apply Nat.ltb_lt; llia). reflexivity.
      + (* [comment removed for export] *)
        destruct (S k <? length l1 + length l2)%nat eqn:L; [apply Nat.ltb_lt in L | apply Nat.ltb_ge in L].
        * destruct (POS (S k) L) as [_ ->]. f_equal.
          assert (S k0 mod n <> i)%nat.
          { intros E. apply NE. rewrite <- Ey. f_equal.
            destruct (Nat.eq_dec (S k0) n) as [E2|E2].
            - rewrite E2, Nat.Div0.mod_same in E. rewrite <- E, pred_mod_0 by llia. llia.
            - rewrite Nat.mod_small in E by llia. rewrite <- E, pred_mod_mid by llia. llia. }
          subst k0. destruct (k <? i)%nat eqn:E1; [apply Nat.ltb_lt in E1 | apply Nat.ltb_ge in E1].
          -- rewrite Nat.mod_small in H |- * by llia.
             destruct (S k <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2; reflexivity | apply Nat.ltb_ge in E2; exfalso; llia].
          -- replace (S k <? i)%nat with false by (symmetry; apply Nat.ltb_ge; llia). rewrite Nat.mod_small by llia. reflexivity.
        * assert (k = length l1 + length l2 - 1)%nat by llia. subst k.
          destruct (POS 0%nat ltac:(llia)) as [_ ->].
          subst k0. destruct (length l1 + length l2 - 1 <? i)%nat eqn:E1; [apply Nat.ltb_lt in E1 | apply Nat.ltb_ge in E1].
          -- (* [comment removed for export] *)
             exfalso. apply NE. rewrite <- Ey. f_equal. rewrite pred_mod_mid by llia. llia.
          -- replace (S (S (length l1 + length l2 - 1))) with n by llia. rewrite Nat.Div0.mod_same.
             destruct (Nat.eq_dec i 0) as [I0|I0]; [| replace (0 <? i)%nat with true by (symmetry; apply Nat.ltb_lt; llia); reflexivity].
             exfalso. apply NE. rewrite <- Ey. f_equal. rewrite I0, pred_mod_0 by llia. llia.
    - (* [comment removed for export] *) rewrite Hp', Hyp. unfold xp, xn.
      destruct (Z.eqb_spec y (nth (S i mod n) l 0)) as [E | NE].
      + rewrite <- Ey in E. apply INJ in E; [| llia | apply Nat.mod_upper_bound; llia].
        destruct (0 <? k)%nat eqn:L; [apply Nat.ltb_lt in L | apply Nat.ltb_ge in L].
        * destruct (POS (k - 1)%nat ltac:(llia)) as [_ ->].
          destruct (Nat.eq_dec (S i) n) as [In | In].
          { exfalso. rewrite In, Nat.Div0.mod_same in E. subst k0. destruct (k <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2|]; llia. }
          rewrite Nat.mod_small in E by llia.
          assert (k = i) by (subst k0; destruct (k <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E2]; llia). subst k.
          replace (i - 1 <? i)%nat with true by (symmetry; apply Nat.ltb_lt; llia).
          destruct (Nat.eq_dec i 0) as [I0|I0]; [llia|]. rewrite pred_mod_mid by llia. reflexivity.
        * assert (k = 0)%nat by llia. subst k.
          destruct (Nat.eq_dec (S i) n) as [In | In].
          -- (* [comment removed for export] *)
             destruct (POS (length l1 + length l2 - 1)%nat ltac:(llia)) as [_ ->].
             replace (length l1 + length l2 - 1 <? i)%nat with true by (symmetry; apply Nat.ltb_lt; llia).
             rewrite pred_mod_mid by llia. f_equal. llia.
          -- rewrite Nat.mod_small in E by llia.
             assert (i = 0)%nat by (subst k0; destruct (0 <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E2]; cbn in E; llia).
             rewrite H, pred_mod_0 by llia.
             destruct (POS (length l1 + length l2 - 1)%nat ltac:(llia)) as [_ ->].
             replace (length l1 + length l2 - 1 <? i)%nat with false by (symmetry; apply Nat.ltb_ge; llia). f_equal. llia.
      + destruct (0 <? k)%nat eqn:L; [apply Nat.ltb_lt in L | apply Nat.ltb_ge in L].
        * destruct (POS (k - 1)%nat ltac:(llia)) as [_ ->]. f_equal.
          subst k0. destruct (k <? i)%nat eqn:E1; [apply Nat.ltb_lt in E1 | apply Nat.ltb_ge in E1].
          -- replace (k - 1 <? i)%nat with true by (symmetry; apply Nat.ltb_lt; llia). rewrite pred_mod_mid by llia. reflexivity.
          -- rewrite pred_mod_mid by llia.
             destruct (k - 1 <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E2; llia].
             exfalso. apply NE. rewrite <- Ey. f_equal. assert (k = i) by llia. subst k. rewrite Nat.mod_small by llia. reflexivity.
        * assert (k = 0)%nat by llia. subst k.
          destruct (POS (length l1 + length l2 - 1)%nat ltac:(llia)) as [_ ->].
          subst k0. destruct (0 <? i)%nat eqn:E1; [apply Nat.ltb_lt in E1 | apply Nat.ltb_ge in E1].
          -- rewrite pred_mod_0 by llia.
             destruct (length l1 + length l2 - 1 <? i)%nat eqn:E2; [apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E2; f_equal; llia].
             exfalso. apply NE. rewrite <- Ey. f_equal. assert (i = n - 1)%nat by llia. rewrite H. replace (S (n-1)) with n by llia. rewrite Nat.Div0.mod_same. reflexivity.
          -- exfalso. apply NE. rewrite <- Ey. f_equal. assert (i = 0)%nat by llia. rewrite H. rewrite Nat.mod_small by llia. reflexivity.
  Qed.
End Ops.

End WithLayout.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition links := option (option sptr * option sptr).
Definition lkmap := sptr -> links.
Definition lk_set (lk : lkmap) (p : sptr) (v : option sptr * option sptr) : lkmap :=
fun q => if sptr_eqb q p then Some v else lk q.
Lemma lk_set_same lk p v : lk_set lk p v p = Some v.
Proof. unfold lk_set. rewrite sptr_eqb_refl. reflexivity. Qed.
Lemma lk_set_other lk p v q : q <> p -> lk_set lk p v q = lk q.
Proof. intros H. unfold lk_set. destruct (sptr_eqb q p) eqn:E; [apply sptr_eqb_eq in E; congruence | reflexivity]. Qed.
Lemma chain_ext lk lk' prev l first :
(forall x, In x l -> lk' x = lk x) -> chain lk prev l first -> chain lk' prev l first.
Proof.
revert prev. induction l as [|x rest IH]; intros prev Hext H; cbn in *; [exact I|].
destruct H as [Hx Hr]. split.
- rewrite Hext by (left; reflexivity). exact Hx.
- apply IH; [intros y Hy; apply Hext; right; exact Hy | exact Hr].
Qed.
Lemma cycle_ok_ext lk lk' ms :
(forall x, In x ms -> lk' x = lk x) -> cycle_ok lk ms -> cycle_ok lk' ms.
Proof.
intros Hext [Hnd H]. split; [exact Hnd|]. destruct ms as [|m0 rest]; [exact H|].
apply chain_ext with lk; assumption.
Qed.
Lemma ring_ok_ext lk lk' hd ms :
(forall x, In x ms -> lk' x = lk x) -> ring_ok lk hd ms -> ring_ok lk' hd ms.
Proof. intros Hext [Hc Hh]. split; [eapply cycle_ok_ext; eauto | exact Hh]. Qed.
Lemma chain_links lk prev l first x :
chain lk prev l first -> In x l -> exists pr nx, lk x = Some (Some pr, Some nx).
Proof.
revert prev. induction l as [|y rest IH]; intros prev H Hin; [destruct Hin|].
cbn in H. destruct H as [Hy Hr]. destruct Hin as [<-|Hin].
- eexists _, _. exact Hy.
- eapply IH; eauto.
Qed.
Lemma cycle_links lk ms x :
cycle_ok lk ms -> In x ms -> exists pr nx, lk x = Some (Some pr, Some nx).
Proof.
intros [_ H] Hin. destruct ms as [|m0 rest]; [destruct Hin|]. eapply chain_links; eauto.
Qed.
Lemma ring_links lk hd ms x :
ring_ok lk hd ms -> In x ms -> exists pr nx, lk x = Some (Some pr, Some nx).
Proof. intros [Hc _] Hin. eapply cycle_links; eauto. Qed.
Lemma ring_head lk hd ms : ring_ok lk hd ms -> hd = hd_error ms.
Proof. intros [_ H]. exact H. Qed.
Lemma ring_head_In lk h ms : ring_ok lk (Some h) ms -> In h ms /\ exists rest, ms = h :: rest.
Proof.
intros [_ Hh]. destruct ms as [|m0 rest]; [discriminate|]. cbn in Hh.
injection Hh as ->. split; [left; reflexivity | exists rest; reflexivity].
Qed.
Lemma ring_None lk ms : ring_ok lk None ms -> ms = [].
Proof. intros [_ Hh]. destruct ms; [reflexivity | discriminate]. Qed.
Lemma ring_nil lk hd : ring_ok lk hd [] -> hd = None.
Proof. intros [_ Hh]. exact Hh. Qed.
Lemma ring_ok_nil lk : ring_ok lk None [].
Proof. split; [split; [constructor | exact I] | reflexivity]. Qed.
Lemma last_indep {T} (l : list T) d d' : l <> [] -> last l d = last l d'.
Proof.
induction l as [|x [|y t] IH]; intros H; [congruence | reflexivity |].
cbn [last]. apply IH. discriminate.
Qed.
Lemma last_cons {T} (x : T) l d : last (x :: l) d = last l x.
Proof.
destruct l as [|y t]; [reflexivity|].
change (last (y :: t) d = last (y :: t) x). apply last_indep. discriminate.
Qed.
Lemma last_app_single {T} (l : list T) (a d : T) : last (l ++ [a]) d = a.
Proof. induction l as [|x [|y t] IH]; cbn in *; auto. Qed.
Lemma In_last {T} (l : list T) d : l <> [] -> In (last l d) l.
Proof.
induction l as [|x [|y t] IH]; intros H; [congruence | left; reflexivity |].
right. apply IH. discriminate.
Qed.
Lemma hd_app_indep {T} (l : list T) d d' r : l <> [] -> hd d (l ++ r) = hd d' l.
Proof. destruct l; [congruence | reflexivity]. Qed.
Lemma hd_app {T} (d : T) l r : hd d (l ++ r) = hd (hd d r) l.
Proof. destruct l; reflexivity. Qed.
Lemma chain_app lk prev l1 l2 first :
chain lk prev (l1 ++ l2) first <-> chain lk prev l1 (hd first l2) /\ chain lk (last l1 prev) l2 first.
Proof.
revert prev. induction l1 as [|x rest IH]; intros prev.
- cbn. tauto.
- cbn [app chain]. rewrite last_cons, hd_app, (IH x). tauto.
Qed.
Lemma chain_next lk prev l first x pr nx :
chain lk prev l first -> In x l -> lk x = Some (pr, nx) ->
exists l1 l2, l = l1 ++ x :: l2 /\ nx = Some (hd first l2) /\ pr = Some (last l1 prev).
Proof.
revert prev. induction l as [|y rest IH]; intros prev Hc Hin Hx; [destruct Hin|].
cbn in Hc. destruct Hc as [Hy Hr]. destruct (sptr_eq_dec x y) as [<-|Hne].
- exists [], rest. rewrite Hx in Hy. injection Hy as -> ->. repeat split; reflexivity.
- destruct Hin as [->|Hin]; [congruence|].
destruct (IH y Hr Hin Hx) as (l1 & l2 & -> & Hn & Hp).
exists (y :: l1), l2. repeat split; try assumption.
rewrite Hp. f_equal. symmetry. apply last_cons.
Qed.
Lemma cycle_rotate lk x l : cycle_ok lk (x :: l) -> cycle_ok lk (l ++ [x]).
Proof.
intros [Hnd Hc]. split. apply NoDup_app_single; inversion Hnd; subst; assumption.
destruct l as [|y l'].
- cbn in *. exact Hc.
- cbn [app]. rewrite last_cons, last_app_single.
cbn [chain] in Hc. rewrite last_cons in Hc. destruct Hc as [Hx Hrest].
change (chain lk x ((y :: l') ++ [x]) y). apply chain_app. split.
+ cbn [hd]. exact Hrest.
+ cbn [chain hd] in Hx |- *. split; [|exact I]. exact Hx.
Qed.
Lemma cycle_rotate_n lk l1 l2 : cycle_ok lk (l1 ++ l2) -> cycle_ok lk (l2 ++ l1).
Proof.
revert l2. induction l1 as [|x rest IH]; intros l2 H.
- rewrite app_nil_r. exact H.
- cbn in H. apply cycle_rotate in H. rewrite <- app_assoc in H. apply IH in H.
rewrite <- app_assoc in H. exact H.
Qed.
Lemma chain_snoc lk lk' p p' l f f' m :
chain lk p l f -> NoDup l -> l <> [] -> ~ In m l ->
(forall x pr nx, In x l -> lk x = Some (pr, nx) ->
lk' x = Some ((if sptr_eqb x (hd m l) then Some p' else pr),
(if sptr_eqb x (last l m) then Some m else nx))) ->
lk' m = Some (Some (last l m), Some f') ->
chain lk' p' (l ++ [m]) f'.
Proof.
revert p p'. induction l as [|x rest IH]; intros p p' Hc Hnd Hne Hm Hupd Hlm; [congruence|].
cbn [chain] in Hc. destruct Hc as [Hx Hrest].
inversion Hnd as [|x' rest' Hxn Hndr]; subst.
cbn [app chain]. split.
- rewrite (Hupd x _ _ (or_introl eq_refl) Hx). cbn [hd]. rewrite sptr_eqb_refl.
destruct rest as [|y rest'].
+ cbn. rewrite sptr_eqb_refl. reflexivity.
+ rewrite last_cons.
assert (E : sptr_eqb x (last (y :: rest') x) = false).
{ apply sptr_eqb_neq. intros Heq. apply Hxn. rewrite Heq at 1. apply In_last. discriminate. }
rewrite E. reflexivity.
- destruct rest as [|y rest'].
+ cbn. split; [|exact I]. rewrite Hlm. reflexivity.
+ apply (IH x x).
* exact Hrest.
* exact Hndr.
* discriminate.
* intros Hin. apply Hm. right. exact Hin.
* intros z pr nx Hz Hlz. rewrite (Hupd z pr nx (or_intror Hz) Hlz).
cbn [hd]. rewrite last_cons, (last_indep (y :: rest') x m) by discriminate.
assert (E : sptr_eqb z x = false) by (apply sptr_eqb_neq; intros ->; exact (Hxn Hz)).
rewrite E. destruct (sptr_eqb z y) eqn:Ezy; [|reflexivity].
apply sptr_eqb_eq in Ezy. subst z. cbn [chain] in Hrest. destruct Hrest as [Hy _].
rewrite Hy in Hlz. injection Hlz as <- <-. reflexivity.
* rewrite Hlm. rewrite last_cons, (last_indep (y :: rest') x m) by discriminate. reflexivity.
Qed.
Lemma cycle_snoc lk lk' ms m :
cycle_ok lk ms -> ms <> [] -> ~ In m ms ->
(forall x pr nx, In x ms -> lk x = Some (pr, nx) ->
lk' x = Some ((if sptr_eqb x (hd m ms) then Some m else pr),
(if sptr_eqb x (last ms m) then Some m else nx))) ->
lk' m = Some (Some (last ms m), Some (hd m ms)) ->
cycle_ok lk' (ms ++ [m]).
Proof.
intros [Hnd Hc] Hne Hm Hupd Hlm. split; [apply NoDup_app_single; assumption|].
destruct ms as [|m0 rest]; [congruence|]. cbn [app]. rewrite last_cons, last_app_single.
change (chain lk' m ((m0 :: rest) ++ [m]) m0).
rewrite (last_indep (m0 :: rest) m0 m) in Hc by discriminate.
eapply chain_snoc; eauto.
Qed.
Lemma chain_retarget lk lk' p l x y :
chain lk p l x -> NoDup l -> l <> [] -> (forall z, In z l -> z <> y) ->
(forall z pr nx, In z l -> lk z = Some (pr, nx) ->
lk' z = Some ((if sptr_eqb z y then Some (last l y) else pr),
(if sptr_eqb z (last l y) then Some y else nx))) ->
chain lk' p l y.
Proof.
revert p. induction l as [|z l IH]; intros p Hc Hnd Hne Hny Hupd; [congruence|].
cbn [chain] in Hc |- *. destruct Hc as [Hz Hl]. inversion Hnd as [|z' l' Hzn Hndl]; subst.
assert (Ezy : sptr_eqb z y = false) by (apply sptr_eqb_neq; apply Hny; left; reflexivity).
split.
- rewrite (Hupd z _ _ (or_introl eq_refl) Hz), Ezy. destruct l as [|w l''].
+ cbn. rewrite sptr_eqb_refl. reflexivity.
+ rewrite last_cons.
assert (E : sptr_eqb z (last (w :: l'') z) = false).
{ apply sptr_eqb_neq. intros Heq. apply Hzn. rewrite Heq at 1. apply In_last. discriminate. }
rewrite E. reflexivity.
- destruct l as [|w l'']; [exact I|].
apply IH; auto.
+ discriminate.
+ intros u Hu. apply Hny. right. exact Hu.
+ intros u pr nx Hu Hlu. rewrite last_cons, (last_indep (w :: l'') z y) in Hupd by discriminate.
apply Hupd; [right; exact Hu | exact Hlu].
Qed.
Lemma cycle_remove_first lk lk' x ms :
cycle_ok lk (x :: ms) -> ms <> [] ->
(forall y pr nx, In y ms -> lk y = Some (pr, nx) ->
lk' y = Some ((if sptr_eqb y (hd x ms) then Some (last ms x) else pr),
(if sptr_eqb y (last ms x) then Some (hd x ms) else nx))) ->
cycle_ok lk' ms.
Proof.
intros [Hnd Hc] Hne Hupd. inversion Hnd as [|x' ms' Hxn Hndm]; subst.
split; [exact Hndm|]. destruct ms as [|y rest]; [congruence|].
cbn [chain] in Hc. rewrite last_cons in Hc. destruct Hc as [Hx [Hy Hrest]].
cbn [hd] in Hupd.
rewrite (last_indep (y :: rest) x y) in Hupd by discriminate.
inversion Hndm as [|y' rest' Hyn Hndr]; subst.
cbn [chain]. split.
- rewrite (Hupd y _ _ (or_introl eq_refl) Hy), sptr_eqb_refl.
destruct rest as [|w rest''].
+ cbn. rewrite sptr_eqb_refl. reflexivity.
+ rewrite last_cons.
assert (E : sptr_eqb y (last (w :: rest'') y) = false).
{ apply sptr_eqb_neq. intros Heq. apply Hyn. rewrite Heq at 1. apply In_last. discriminate. }
rewrite E. reflexivity.
- destruct rest as [|w rest'']; [exact I|].
eapply chain_retarget.
+ exact Hrest.
+ exact Hndr.
+ discriminate.
+ intros z Hz ->. exact (Hyn Hz).
+ intros z pr nx Hz Hlz. rewrite (Hupd z _ _ (or_intror Hz) Hlz).
rewrite last_cons. reflexivity.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rejects {R} (t : M R) : Prop :=
match t with SVis (EUndef _) _ => True | _ => False end.

Definition is_peek (e : ev) : bool := match e with EPeek _ _ _ => true | _ => false end.
Definition is_undef (e : ev) : bool := match e with EUndef _ => true | _ => false end.

#[using="Type"] Lemma rejects_inv {R} (t : M R) : rejects t -> exists w k, t = SVis (EUndef w) k.
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; try tauto. intros _. eauto. Qed.

#[using="Type"] Lemma rejects_bind {R S} (t : M R) (f : R -> M S) : rejects t -> rejects (sbind t f).
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.

Fixpoint ftree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
match t with
| SRet r => Post L r
| SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> ftree L (k v) Post
| SVis (EUndef _) _ => False
| SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a)
end.

Fixpoint ptree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
match t with
| SRet r => Post L r
| SVis (EPeek _ _ _) k => False
| SVis (EUndef _) _ => False
| SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ptree (event_post L e a) (k a) Post else rejects (k a)
end.
End RC__1.

Ltac case_ans :=
match goal with
| |- context [if answer_ok ?L ?e ?a then _ else _] => destruct (answer_ok L e a) eqn:?
| H : context [if answer_ok ?L ?e ?a then _ else _] |- _ => destruct (answer_ok L e a) eqn:?
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ftree_ret {R} L (r : R) Post : Post L r -> ftree L (SRet r) Post.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ftree_vis {R} L e (k : Z -> M R) Post :
is_peek e = false -> is_undef e = false ->
event_pre L e ->
(forall a, answer_ok L e a = true -> ftree (event_post L e a) (k a) Post) ->
(forall a, answer_ok L e a = false -> rejects (k a)) ->
ftree L (SVis e k) Post.
Proof.
intros Hp Hu He Hk Hr. destruct e; cbn in Hp, Hu; try discriminate; cbn [ftree]; split; auto;
intros a; case_ans; auto.
Qed.

#[using="Type"] Lemma ftree_peek {R} L p c h (k : Z -> M R) Post :
(forall v, 0 <= v < 256 -> ftree L (k v) Post) -> ftree L (SVis (EPeek p c h) k) Post.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ftree_mono {R} (Post Post' : mled -> R -> Prop) :
(forall L r, Post L r -> Post' L r) -> forall t L, ftree L t Post -> ftree L t Post'.
Proof.
intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
case_ans; [apply IH; exact Hk| exact Hk]).
- intros v Hv. apply IH. apply H. exact Hv.
- exact H.
Qed.

#[using="Type"] Lemma ftree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
ftree L t Post -> (forall L' r, Post L' r -> ftree L' (f r) Q) -> ftree L (sbind t f) Q.
Proof.
revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
- apply Hf. exact H.
- destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
case_ans; [apply IH; [exact Hk| exact Hf]|];
apply rejects_bind; exact Hk).
+ intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
+ destruct H.
Qed.

#[using="Type"] Lemma rejects_bad_answer {R} (b : M R) : rejects (bad_answer b).
Proof. exact I. Qed.

#[using="Type"] Lemma ftree_guard {R} L tag (c : bool) (k bail : M R) Post :
c = true -> ftree L k Post -> ftree L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

#[using="Type"] Lemma ftree_guard_inv {R} L tag (c : bool) (k bail : M R) Post :
ftree L (guard tag c k bail) Post -> c = true /\ ftree L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

#[using="Type"] Lemma ptree_mono {R} (Post Post' : mled -> R -> Prop) :
(forall L r, Post L r -> Post' L r) -> forall t L, ptree L t Post -> ptree L t Post'.
Proof.
intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
case_ans; [apply IH; exact Hk| exact Hk]); exact H.
Qed.

#[using="Type"] Lemma ptree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
ptree L t Post -> (forall L' r, Post L' r -> ptree L' (f r) Q) -> ptree L (sbind t f) Q.
Proof.
revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
- apply Hf. exact H.
- destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
case_ans; [apply IH; [exact Hk| exact Hf]|];
apply rejects_bind; exact Hk); exact H.
Qed.

#[using="Type"] Lemma ptree_ctree_ok {R} : forall (t : M R) L Post, ptree L t Post -> ctree_ok L t Post.
Proof.
induction t as [r|e k IH]; intros L Post H; cbn [ftree ptree follow sbind] in *; [exact H|].
destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros z Hz; specialize (Hk z); rewrite Hz in Hk; apply IH; exact Hk);
destruct H.
Qed.

#[using="Type"] Lemma ptree_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strel RR t1 t2 -> forall L (P1 : mled -> R1 -> Prop) (P2 : mled -> R2 -> Prop),
(forall L' r1 r2, RR r1 r2 -> P1 L' r1 -> P2 L' r2) ->
ptree L t1 P1 -> ptree L t2 P2.
Proof.
induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L P1 P2 HP H; cbn [ftree ptree follow sbind] in *.
- eapply HP; eauto.
- destruct e; try exact H. all: destruct H as [He H]; split; [exact He|]; intros a; specialize (H a);
case_ans; [eapply IH; eauto|].
all: specialize (Hk a); destruct (rejects_inv _ H) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

#[using="Hpans"] Lemma ftree_prun {R} : forall (t : M R) L Post o,
ftree L t Post -> ptree L (prun pans pupd o t) (fun L' x => Post L' (snd x)).
Proof.
induction t as [r|e k IH]; intros L Post o H; cbn [ftree ptree follow sbind] in *.
- exact H.
- unfold prun. destruct e; cbn [eruns psel];
try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
case_ans; [apply IH; exact Hk|];
destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E; exact I).
+ apply IH. apply H. apply Hpans.
+ destruct H.
Qed.
End PRUN.

#[using="Type"] Lemma ptree_follow {R} : forall (t : M R) L Post ans r,
ptree L t Post -> follow t ans = Some r -> exists L', cpath L t L' r /\ Post L' r.
Proof.
induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ftree ptree follow sbind] in *.
- inversion Hf; subst. exists L. split; [constructor| exact H].
- destruct e; try (destruct H; fail); try contradiction.
all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
specialize (Hk a); case_ans;
[ destruct (IH a _ _ _ _ Hk Hf) as (L' & Hp & HP); exists L'; split; [econstructor; eauto| exact HP]
| destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

#[using="Type"] Lemma ptree_cpath {R} : forall (t : M R) L Post L' r,
ptree L t Post -> cpath L t L' r -> Post L' r.
Proof.
induction t as [r0|e k IH]; intros L Post L' r H Hp; cbn [ftree ptree follow sbind] in *.
- inversion Hp; subst. exact H.
- inversion Hp; subst. destruct e; try contradiction.
all: destruct H as [He Hk];
match goal with Ha : answer_ok _ _ ?z = true |- _ => specialize (Hk z); rewrite Ha in Hk; eapply IH; eauto end.
Qed.

#[using="Type"] Lemma strel_cpath {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strel RR t1 t2 -> forall L L' r2, cpath L t2 L' r2 -> exists r1, cpath L t1 L' r1 /\ RR r1 r2.
Proof.
induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L L' r Hp.
- inversion Hp; subst. exists r1. split; [constructor| exact Hr].
- inversion Hp; subst.
match goal with Hc : cpath _ (k2 ?z) _ _ |- _ =>
destruct (IH z _ _ _ Hc) as (r1 & Hp1 & Hr1); exists r1; split; [econstructor; eauto| exact Hr1] end.
Qed.

#[using="Type"] Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strel RR t1 t2 -> forall ans,
match follow t1 ans, follow t2 ans with
| Some r1, Some r2 => RR r1 r2
| None, None => True
| _, _ => False
end.
Proof.
induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans; cbn.
- exact Hr.
- destruct e; destruct ans; cbn; auto; apply IH.
Qed.

End RC__2.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2.
Import ListNotations.
Local Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition hl_ticks (hl : list (Z * N)) (t : N) : Prop := forall ch, In ch hl -> (snd ch <= t)%N.

#[using="Type"] Lemma stale_hav_add_some cov t hl b tk :
hl_ticks hl t ->
stale (hav_add cov t hl) b (Some tk) = ((b <? cov) && (tk <? t)%N) || stale hl b (Some tk).
Proof.
intros Ht. unfold hav_add, stale. cbn [existsb fst snd].
destruct ((b <? cov) && (tk <? t)%N) eqn:E; cbn [orb]; [reflexivity|].
induction hl as [|[c h] hl IH]; [reflexivity|].
assert (Hh : (h <= t)%N) by (apply (Ht (c, h)); left; reflexivity).
assert (IH' : existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) (filter (fun ch : Z * N => cov <? fst ch) hl)
= existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) hl).
{ apply IH. intros ch Hin. apply Ht. right. exact Hin. }
rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd].
- rewrite IH'. reflexivity.
- rewrite IH'. destruct ((b <? c) && (tk <? h)%N) eqn:E2; cbn; [|reflexivity].
exfalso. apply Bool.andb_true_iff in E2 as [E2 E3]. apply Z.ltb_lt in E2. apply N.ltb_lt in E3.
assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
apply Bool.andb_false_iff in E as [E|E]; [apply Z.ltb_ge in E; lia| apply N.ltb_ge in E; lia].
Qed.

#[using="Type"] Lemma stale_hav_add_none cov t hl b :
stale (hav_add cov t hl) b None = (b <? cov) || stale hl b None.
Proof.
unfold hav_add, stale. cbn [existsb fst snd]. rewrite Bool.andb_true_r.
destruct (b <? cov) eqn:E; cbn [orb]; [reflexivity|].
induction hl as [|[c h] hl IH]; [reflexivity|].
rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd]; rewrite ?Bool.andb_true_r.
- rewrite IH. reflexivity.
- rewrite IH. destruct (Z.ltb_spec b c); cbn; [|reflexivity]. exfalso.
assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
apply Z.ltb_ge in E. lia.
Qed.

#[using="Type"] Lemma havoc_units_lookup x y t h u :
let u0 := x / 16 in let u1 := (y - 1) / 16 in
let lastcov := (if y mod 16 =? 0 then 16 else y mod 16) in
(havoc_units x y t h) !! u =
if (u0 <=? u) && (u <=? u1) then Some (hav_add (if u =? u1 then lastcov else 16) t (default [] (h !! u))) else h !! u.
Proof.
cbn zeta. unfold havoc_units.
set (u0 := x / 16). set (u1 := (y - 1) / 16). set (lastcov := if y mod 16 =? 0 then 16 else y mod 16).
set (F := fun acc : Z * gmap Z (list (Z * N)) => let (u2, h0) := acc in (u2 + 1, <[u2 := hav_add (if u2 =? u1 then lastcov else 16) t (default [] (h0 !! u2))]> h0)).
destruct (Z.lt_ge_cases (u1 - u0 + 1) 0) as [Hneg|Hnn].
-
destruct (u1 - u0 + 1) eqn:E; try lia. cbn.
destruct (Z.leb_spec u0 u), (Z.leb_spec u u1); cbn; try reflexivity. lia.
- assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (u0, h) in fst r = u0 + n /\
forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v).
{ intros n Hn. apply (Z_iter_ind F (fun n r => fst r = u0 + n /\ forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v)); [| | exact Hn].
- cbn. split; [lia|]. intros v. destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + 0)); cbn; try reflexivity. lia.
- intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
destruct (Z.eq_dec v (u0 + k)) as [->|NE].
+ rewrite lookup_insert_eq. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + (k + 1))); cbn; try lia.
f_equal. f_equal. rewrite IH. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + k)); cbn; try lia. reflexivity.
+ rewrite lookup_insert_ne by congruence. rewrite IH.
destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + k)), (Z.ltb_spec v (u0 + (k + 1))); cbn; try reflexivity; lia. }
destruct (GEN (u1 - u0 + 1) Hnn) as [_ G]. rewrite G.
destruct (Z.leb_spec u0 u), (Z.ltb_spec u (u0 + (u1 - u0 + 1))), (Z.leb_spec u u1); cbn; try reflexivity; lia.
Qed.

#[using="Type"] Lemma havoc_pages_lookup p0 p1 t h pg :
(havoc_pages p0 p1 t h) !! pg = if (p0 <=? pg) && (pg <? p1) then Some t else h !! pg.
Proof.
unfold havoc_pages.
set (F := fun acc : Z * gmap Z N => let (pg0, h0) := acc in (pg0 + 1, <[pg0 := t]> h0)).
destruct (Z.lt_ge_cases (p1 - p0) 0) as [Hneg|Hnn].
- destruct (p1 - p0) eqn:E; try lia. cbn. destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg p1); cbn; try reflexivity. lia.
- assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (p0, h) in fst r = p0 + n /\
forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v).
{ intros n Hn. apply (Z_iter_ind F (fun n r => fst r = p0 + n /\ forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v)); [| | exact Hn].
- cbn. split; [lia|]. intros v. destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + 0)); cbn; try reflexivity. lia.
- intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
destruct (Z.eq_dec v (p0 + k)) as [->|NE].
+ rewrite lookup_insert_eq. destruct (Z.leb_spec p0 (p0 + k)), (Z.ltb_spec (p0 + k) (p0 + (k + 1))); cbn; try lia. reflexivity.
+ rewrite lookup_insert_ne by congruence. rewrite IH.
destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + k)), (Z.ltb_spec v (p0 + (k + 1))); cbn; try reflexivity; lia. }
destruct (GEN (p1 - p0) Hnn) as [_ G]. rewrite G.
destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg (p0 + (p1 - p0))), (Z.ltb_spec pg p1); cbn; try reflexivity; lia.
Qed.

#[using="Type"] Lemma div16_mono a b : a <= b -> a / 16 <= b / 16.
Proof. intros. apply Z.div_le_mono; lia. Qed.

#[using="Type"] Lemma havoc_units_in x y t h o tko :
x mod 16 = 0 -> x <= o < y ->
match tko with Some tk => (tk < t)%N | None => True end ->
stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = true.
Proof.
intros Hx Ho Htk. rewrite havoc_units_lookup.
assert (U0 : x / 16 <= o / 16) by (apply div16_mono; lia).
assert (U1 : o / 16 <= (y - 1) / 16) by (apply div16_mono; lia).
destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); try lia. cbn [andb default].
cbn [default id]. unfold hav_add, stale. cbn [existsb fst snd].
match goal with |- (?a && ?b) || _ = true => enough (E : a && b = true) by (rewrite E; reflexivity) end.
apply Bool.andb_true_iff. split.
- apply Z.ltb_lt. destruct (Z.eqb_spec (o / 16) ((y - 1) / 16)) as [E|NE].
+ destruct (Z.eqb_spec (y mod 16) 0) as [Ey|Ny].
* pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
*
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)).
pose proof (Z.div_mod y 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
assert (y / 16 = (y - 1) / 16 \/ y / 16 = (y - 1) / 16 + 1) by (pose proof (div16_mono (y - 1) y ltac:(lia)); pose proof (div16_mono y (y - 1 + 16) ltac:(lia)); rewrite <- Z.div_add in * by lia; nia).
lia.
+ pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
- destruct tko as [tk|]; [apply N.ltb_lt; exact Htk| reflexivity].
Qed.

#[using="Type"] Lemma havoc_units_out x y t h o tko :
x mod 16 = 0 -> ~ (x <= o < y) ->
match tko with Some tk => hl_ticks (default [] (h !! (o / 16))) t | None => True end ->
stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = stale (default [] (h !! (o / 16))) (o mod 16) tko.
Proof.
intros Hx Ho Htk. rewrite havoc_units_lookup.
destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); cbn [andb]; try reflexivity.
cbn [default id].

assert (Hoy : y <= o).
{ destruct (Z.lt_ge_cases o x); [|lia]. exfalso.
pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.mod_pos_bound o 16 ltac:(lia)). nia. }
assert (E : o / 16 = (y - 1) / 16) by (pose proof (div16_mono (y - 1) o ltac:(lia)); lia).
rewrite E, Z.eqb_refl.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)). pose proof (Z.div_mod y 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
assert (Ny : y mod 16 <> 0 /\ y mod 16 <= o mod 16) by nia.
destruct (Z.eqb_spec (y mod 16) 0) as [|_]; [lia|].
destruct tko as [tk|].
- rewrite stale_hav_add_some by (rewrite <- E; exact Htk). destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
- rewrite stale_hav_add_none. destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
Qed.

#[using="Type"] Lemma hav_add_ticks cov t hl : hl_ticks hl t -> hl_ticks (hav_add cov t hl) t.
Proof.
intros H ch Hin. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
apply H. apply list_elem_of_In. apply list_elem_of_In in Hin. apply list_elem_of_filter in Hin. tauto.
Qed.

#[using="Type"] Lemma havoc_units_ticks x y t h :
(forall u hl, h !! u = Some hl -> hl_ticks hl t) ->
forall u hl, havoc_units x y t h !! u = Some hl -> hl_ticks hl t.
Proof.
intros Hh u hl. rewrite havoc_units_lookup. destruct (_ && _).
- intros E. inversion E. subst. apply hav_add_ticks. destruct (h !! u) as [hl0|] eqn:E0; cbn; [eapply Hh; exact E0| intros ? []].
- apply Hh.
Qed.

#[using="Type"] Lemma havoc_units_default_ticks x y t h o :
(forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (havoc_units x y t h !! o)) t.
Proof.
intros Hh. destruct (havoc_units x y t h !! o) as [hl|] eqn:E; cbn; [eapply havoc_units_ticks; eauto| intros ? []].
Qed.

#[using="Type"] Lemma default_ticks (h : gmap Z (list (Z * N))) t o :
(forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (h !! o)) t.
Proof. intros Hh. destruct (h !! o) as [hl|] eqn:E; cbn; [eapply Hh; eauto| intros ? []]. Qed.

Section HAVOC.
Variables (p : aptr) (n : Z) (st : mstate).
Hypothesis Al : snd p mod 16 = 0.
Hypothesis Hn : 0 < n.
Let sh := get_shadow st (fst p).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).
Let a := snd p.
Let b := snd p + n.
Let t := s_tick st.
Let fp := (a + 4095) / 4096.
Let lp := b / 4096.

#[using="Hn"] Lemma havoc_shadow :
get_shadow (havoc p n st) (fst p) =
mkShadow (r_cells sh)
(if fp <? lp then
(if lp * 4096 <? b then havoc_units (lp * 4096) b t (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh)
else (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh))
else havoc_units a b t (r_hav sh))
(if fp <? lp then havoc_pages fp lp t (r_havp sh) else r_havp sh).
Proof.
unfold havoc. destruct (Z.leb_spec n 0); [lia|]. rewrite get_shadow_upd_shadow, N.eqb_refl.
subst sh a b t fp lp. destruct (_ <? _); [|reflexivity]. destruct (_ <? _); destruct (_ <? _); reflexivity.
Qed.

#[using="Type"] Lemma havoc_other_region rid : rid <> fst p -> get_shadow (havoc p n st) rid = get_shadow st rid.
Proof.
intros NE. unfold havoc. destruct (n <=? 0); [reflexivity|]. rewrite get_shadow_upd_shadow.
destruct (N.eqb_spec rid (fst p)); [congruence| reflexivity].
Qed.

#[using="n st b t lp"] Lemma fp_ge : a <= fp * 4096.
Proof. subst fp. pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)). lia. Qed.
#[using="st a t fp"] Lemma lp_le : lp * 4096 <= b.
Proof. subst lp. pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. Qed.
#[using="Type"] Lemma fp_al : (fp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.
#[using="Type"] Lemma lp_al : (lp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.

#[using="Al Hn TK t fp lp"] Lemma havoc_stale_out o tko :
~ (a <= o < b) ->
match tko with Some tk => True | None => True end ->
let sh' := get_shadow (havoc p n st) (fst p) in
stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko
= stale_pg (r_havp sh !! (o / 4096)) tko || stale (default [] (r_hav sh !! (o / 16))) (o mod 16) tko.
Proof.
intros Ho _. rewrite havoc_shadow. cbn [r_hav r_havp].
pose proof fp_ge. pose proof lp_le.
assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
{ intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
destruct (Z.ltb_spec fp lp).
- f_equal.
+ rewrite havoc_pages_lookup. destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); cbn [andb]; try reflexivity.
exfalso. apply Ho. pose proof (Z.div_mod o 4096 ltac:(lia)). pose proof (Z.mod_pos_bound o 4096 ltac:(lia)). nia.
+ destruct (Z.ltb_spec (lp * 4096) b); destruct (Z.ltb_spec a (fp * 4096)).
* rewrite havoc_units_out; [| apply lp_al| lia| apply TKo; apply havoc_units_ticks; exact TK].
rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
* rewrite havoc_units_out; [reflexivity| apply lp_al| lia| apply TKo; exact TK].
* rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
* reflexivity.
- f_equal. rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
Qed.

#[using="Al Hn sh TK fp lp"] Lemma havoc_stale_in o tko :
a <= o < b ->
match tko with Some tk => (tk < t)%N | None => True end ->
let sh' := get_shadow (havoc p n st) (fst p) in
stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko = true.
Proof.
intros Ho Htk. rewrite havoc_shadow. cbn [r_hav r_havp].
pose proof fp_ge. pose proof lp_le.
assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
{ intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
apply Bool.orb_true_iff.
destruct (Z.ltb_spec fp lp).
- destruct (Z.lt_ge_cases o (fp * 4096)) as [Hhead|Hnh].
+ right. destruct (Z.ltb_spec a (fp * 4096)); [|lia].
destruct (Z.ltb_spec (lp * 4096) b).
* rewrite havoc_units_out; [| apply lp_al| nia| apply TKo; apply havoc_units_ticks; exact TK].
apply havoc_units_in; [exact Al| lia| exact Htk].
* apply havoc_units_in; [exact Al| lia| exact Htk].
+ destruct (Z.lt_ge_cases o (lp * 4096)) as [Hmid|Htail].
* left. rewrite havoc_pages_lookup.
assert (fp <= o / 4096 < lp).
{ split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); try lia. cbn [andb].
destruct tko as [tk|]; cbn; [apply N.ltb_lt; exact Htk| reflexivity].
* right. destruct (Z.ltb_spec (lp * 4096) b); [|lia].
apply havoc_units_in; [apply lp_al| lia| exact Htk].
- right. apply havoc_units_in; [exact Al| lia| exact Htk].
Qed.

#[using="Al Hn sh TK t fp lp"] Lemma cell_read_havoc_out q :
~ (fst q = fst p /\ a <= snd q < b) ->
cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
intros Hq. destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
- rewrite E. assert (Ho : ~ (a <= snd q < b)) by tauto.
unfold cell_read. pose proof (havoc_stale_out (snd q)) as SO. cbn zeta in SO.
replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
subst sh. destruct (r_cells (get_shadow st (fst p)) !! snd q) as [[v tk]|].
+ rewrite (SO (Some tk) Ho I). reflexivity.
+ rewrite (SO None Ho I). reflexivity.
- rewrite havoc_other_region by exact NE. reflexivity.
Qed.

#[using="Al Hn TK fp lp"] Lemma cell_read_havoc_in q :
fst q = fst p -> a <= snd q < b ->
(forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < t)%N) ->
exists h, cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = Unknown h.
Proof.
intros E Ho Htk. rewrite E. unfold cell_read.
replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
pose proof (havoc_stale_in (snd q)) as SI. cbn zeta in SI.
destruct (r_cells sh !! snd q) as [[v tk]|] eqn:Ec.
- rewrite (SI (Some tk) Ho (Htk v tk eq_refl)). eauto.
- rewrite (SI None Ho I). eauto.
Qed.

#[using="Hn sh a b t fp lp"] Lemma havoc_cells rid : r_cells (get_shadow (havoc p n st) rid) = r_cells (get_shadow st rid).
Proof.
destruct (N.eq_dec rid (fst p)) as [->|NE]; [rewrite havoc_shadow; reflexivity| rewrite havoc_other_region by exact NE; reflexivity].
Qed.

#[using="Hn sh TK a b fp lp"] Lemma havoc_ticks rid :
(forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl t) ->
(forall pg tk, r_havp (get_shadow st rid) !! pg = Some tk -> (tk <= t)%N) ->
(forall u hl, r_hav (get_shadow (havoc p n st) rid) !! u = Some hl -> hl_ticks hl t)
/\ (forall pg tk, r_havp (get_shadow (havoc p n st) rid) !! pg = Some tk -> (tk <= t)%N).
Proof.
intros H1 H2. destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite havoc_other_region by exact NE; auto].
rewrite havoc_shadow. cbn [r_hav r_havp]. split.
- destruct (fp <? lp); [| apply havoc_units_ticks; exact TK].
destruct (lp * 4096 <? b); destruct (a <? fp * 4096); repeat apply havoc_units_ticks; exact TK.
- destruct (fp <? lp); [| exact H2]. intros pg tk. rewrite havoc_pages_lookup. destruct (_ && _); [| apply H2].
intros X. inversion X. lia.
Qed.
End HAVOC.

Section HDR.
Variables (bp : aptr) (st : mstate).
Hypothesis Al : snd bp mod 16 = 0.
Let sh := get_shadow st (fst bp).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).

#[using="Type"] Lemma hdr_havoc_shadow :
get_shadow (hdr_havoc bp st) (fst bp) =
mkShadow (r_cells sh) (<[snd bp / 16 := hav_add 12 (s_tick st) (default [] (r_hav sh !! (snd bp / 16)))]> (r_hav sh)) (r_havp sh).
Proof. unfold hdr_havoc. rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma hdr_havoc_other_region rid : rid <> fst bp -> get_shadow (hdr_havoc bp st) rid = get_shadow st rid.
Proof. intros NE. unfold hdr_havoc. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst bp)); [congruence| reflexivity]. Qed.

#[using="Al sh TK"] Lemma cell_read_hdr_havoc_out q :
~ (fst q = fst bp /\ snd bp <= snd q < snd bp + 12) ->
cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
intros Hq. destruct (N.eq_dec (fst q) (fst bp)) as [E|NE]; [| rewrite hdr_havoc_other_region by exact NE; reflexivity].
rewrite E. rewrite hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
destruct (Z.eq_dec (snd q / 16) (snd bp / 16)) as [Eu|Nu].
- rewrite Eu, lookup_insert_eq. cbn [default id].
assert (Hb : 12 <= snd q mod 16).
{ pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (snd q) 16 ltac:(lia)).
assert (~ (snd bp <= snd q < snd bp + 12)) by tauto. nia. }
destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|].
+ rewrite stale_hav_add_some by (apply default_ticks; exact TK). destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [andb orb]. rewrite <- Eu. reflexivity.
+ rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [orb]. rewrite <- Eu. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Al"] Lemma cell_read_hdr_havoc_in q :
fst q = fst bp -> snd bp <= snd q < snd bp + 12 ->
(forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < s_tick st)%N) ->
exists h, cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = Unknown h.
Proof.
intros E Ho Htk. rewrite E, hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
assert (Eu : snd q / 16 = snd bp / 16).
{ pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). symmetry. apply Z.div_unique with (r := snd q - snd bp); lia. }
rewrite Eu, lookup_insert_eq. cbn [default id].
assert (Hb : snd q mod 16 < 12).
{ pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). nia. }
destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|] eqn:Ec.
- unfold hav_add, stale. cbn [existsb fst snd].
destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. rewrite (proj2 (N.ltb_lt _ _)) by (eapply Htk; reflexivity).
cbn [andb orb]. rewrite Bool.orb_true_r. eauto.
- rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. cbn [orb]. rewrite Bool.orb_true_r. eauto.
Qed.

#[using="sh"] Lemma hdr_havoc_cells rid : r_cells (get_shadow (hdr_havoc bp st) rid) = r_cells (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [rewrite hdr_havoc_shadow; reflexivity| rewrite hdr_havoc_other_region by exact NE; reflexivity]. Qed.

#[using="sh TK"] Lemma hdr_havoc_ticks rid :
(forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl (s_tick st)) ->
(forall u hl, r_hav (get_shadow (hdr_havoc bp st) rid) !! u = Some hl -> hl_ticks hl (s_tick st))
/\ r_havp (get_shadow (hdr_havoc bp st) rid) = r_havp (get_shadow st rid).
Proof.
intros H1. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [| rewrite hdr_havoc_other_region by exact NE; auto].
rewrite hdr_havoc_shadow. cbn [r_hav r_havp]. split; [| reflexivity].
intros u hl. destruct (Z.eq_dec u (snd bp / 16)) as [->|Nu].
- rewrite lookup_insert_eq. intros X. inversion X. subst. apply hav_add_ticks. apply default_ticks. exact TK.
- rewrite lookup_insert_ne by congruence. apply H1.
Qed.
End HDR.

End RC__1.

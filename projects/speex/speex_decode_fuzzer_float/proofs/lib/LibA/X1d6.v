(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Inductive oexp : Set :=
| OV (i : nat) | OC (c : Z) | OAdd (a b : oexp) | OSub (a b : oexp) | OMul (c : Z) (a : oexp) | OMulR (a : oexp) (c : Z).
Inductive oform : Set :=
| FLe (a b : oexp) | FLt (a b : oexp) | FEq (a b : oexp) | FGe (a b : oexp) | FGt (a b : oexp)
| FAnd (f g : oform) | FOr (f g : oform)
| FToNat (a b : oexp)
| FNLe (n m : nat) | FNLt (n m : nat) | FNEq (n m : nat)
| FTrue | FFalse.

Fixpoint onth (i : nat) (env : list Z) : Z :=
match env with [] => 0 | v :: env' => match i with O => v | S j => onth j env' end end.
Fixpoint oeval (env : list Z) (e : oexp) : Z :=
match e with
| OV i => onth i env | OC c => c
| OAdd a b => oeval env a + oeval env b | OSub a b => oeval env a - oeval env b
| OMul c a => c * oeval env a | OMulR a c => oeval env a * c
end.
Fixpoint ointerp (env : list Z) (f : oform) : Prop :=
match f with
| FLe a b => oeval env a <= oeval env b | FLt a b => oeval env a < oeval env b
| FEq a b => oeval env a = oeval env b
| FGe a b => oeval env a >= oeval env b | FGt a b => oeval env a > oeval env b
| FAnd f g => ointerp env f /\ ointerp env g | FOr f g => ointerp env f \/ ointerp env g
| FToNat a b => Z.to_nat (oeval env a) = Z.to_nat (oeval env b)
| FNLe n m => (n <= m)%nat | FNLt n m => (n < m)%nat | FNEq n m => n = m
| FTrue => True | FFalse => False
end.
Fixpoint oimp (env : list Z) (hs : list oform) (G : Prop) : Prop :=
match hs with [] => G | h :: t => ointerp env h -> oimp env t G end.
Lemma onth_nth i : forall env, onth i env = nth i env 0.
Proof. induction i as [|i IH]; intros [|v env]; cbn; auto. Qed.

Strategy expand [onth oeval ointerp oimp].

Fixpoint zipadd (a b : list Z) : list Z :=
match a, b with [], _ => b | _, [] => a | x :: a', y :: b' => (x + y) :: zipadd a' b' end.
Fixpoint dot (cs env : list Z) : Z :=
match cs with [] => 0 | k :: cs' => k * hd 0 env + dot cs' (tl env) end.
Fixpoint unit_at (i : nat) : list Z := match i with O => [1] | S j => 0 :: unit_at j end.
Definition nf : Set := (list Z * Z)%type.
Definition nf_add (a b : nf) : nf := (zipadd (fst a) (fst b), snd a + snd b).
Definition nf_scale (k : Z) (a : nf) : nf := (map (Z.mul k) (fst a), k * snd a).
Definition nf_sub (a b : nf) : nf := nf_add a (nf_scale (-1) b).
Fixpoint norm (e : oexp) : nf :=
match e with
| OV i => (unit_at i, 0) | OC c => ([], c)
| OAdd a b => nf_add (norm a) (norm b) | OSub a b => nf_sub (norm a) (norm b)
| OMul c a => nf_scale c (norm a) | OMulR a c => nf_scale c (norm a)
end.
Definition nf_eval (env : list Z) (a : nf) : Z := dot (fst a) env + snd a.

Lemma dot_zipadd a : forall b env, dot (zipadd a b) env = dot a env + dot b env.
Proof. induction a as [|x a IH]; intros [|y b] env; cbn; try lia. rewrite IH. lia. Qed.
Lemma dot_scale k cs : forall env, dot (map (Z.mul k) cs) env = k * dot cs env.
Proof. induction cs as [|c cs IH]; intros env; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma nth_hd_tl i : forall env : list Z, nth (S i) env 0 = nth i (tl env) 0.
Proof. intros [|v env]; cbn; [destruct i|]; reflexivity. Qed.
Lemma dot_unit i : forall env, dot (unit_at i) env = nth i env 0.
Proof. induction i as [|i IH]; intros env. - destruct env; cbn [unit_at dot hd tl nth]; lia. - cbn [unit_at dot]. rewrite IH, nth_hd_tl. lia. Qed.
Lemma nf_add_ok env a b : nf_eval env (nf_add a b) = nf_eval env a + nf_eval env b.
Proof. unfold nf_eval, nf_add; cbn [fst snd]. rewrite dot_zipadd. lia. Qed.
Lemma nf_scale_ok env k a : nf_eval env (nf_scale k a) = k * nf_eval env a.
Proof. unfold nf_eval, nf_scale; cbn [fst snd]. rewrite dot_scale. lia. Qed.
Lemma nf_sub_ok env a b : nf_eval env (nf_sub a b) = nf_eval env a - nf_eval env b.
Proof. unfold nf_sub. rewrite nf_add_ok, nf_scale_ok. lia. Qed.
Lemma norm_ok env e : oeval env e = nf_eval env (norm e).
Proof.
induction e; cbn [oeval norm]; rewrite ?onth_nth, ?nf_add_ok, ?nf_sub_ok, ?nf_scale_ok, <- ?IHe1, <- ?IHe2, <- ?IHe; try reflexivity.
all: unfold nf_eval; cbn [fst snd]; rewrite ?dot_unit; cbn [dot]; lia.
Qed.

Definition bnd : Set := list (option Z * option Z).
Definition b_ok (v : Z) (b : option Z * option Z) : Prop :=
match fst b with Some l => l <= v | None => True end /\ match snd b with Some h => v <= h | None => True end.
Fixpoint bounds_ok (env : list Z) (bs : bnd) : Prop :=
match bs with [] => True | b :: bs' => b_ok (hd 0 env) b /\ bounds_ok (tl env) bs' end.
Fixpoint ub_dot (cs : list Z) (bs : bnd) : option Z :=
match cs with
| [] => Some 0
| k :: cs' =>
let b := hd (None, None) bs in
match ub_dot cs' (tl bs) with
| None => None
| Some r => if k =? 0 then Some r
else match (if 0 <? k then snd b else fst b) with Some h => Some (k * h + r) | None => None end
end
end.
Lemma ub_dot_ok cs : forall bs env u, bounds_ok env bs -> ub_dot cs bs = Some u -> dot cs env <= u.
Proof.
induction cs as [|k cs IH]; intros bs env u OK E; cbn in *.
- inversion E; lia.
- destruct (ub_dot cs (tl bs)) as [r|] eqn:Er; [|discriminate].
assert (OK' : bounds_ok (tl env) (tl bs)) by (destruct bs; cbn in *; tauto).
specialize (IH _ _ _ OK' Er).
destruct (Z.eqb_spec k 0) as [->|NZ]; [inversion E; subst; lia|].
assert (B : b_ok (hd 0 env) (hd (None, None) bs)) by (destruct bs; cbn in *; [split; exact I|tauto]).
destruct B as [BL BH]. destruct (Z.ltb_spec 0 k).
+ destruct (snd (hd (None, None) bs)); [|discriminate]. inversion E; subst. nia.
+ destruct (fst (hd (None, None) bs)); [|discriminate]. inversion E; subst. nia.
Qed.

Definition le0b (bs : bnd) (a : nf) : bool :=
match ub_dot (fst a) bs with Some u => u + snd a <=? 0 | None => false end.
Lemma le0b_ok bs env a : bounds_ok env bs -> le0b bs a = true -> nf_eval env a <= 0.
Proof.
unfold le0b, nf_eval. intros OK E. destruct (ub_dot (fst a) bs) as [u|] eqn:Eu; [|discriminate].
apply Z.leb_le in E. pose proof (ub_dot_ok _ _ _ _ OK Eu). lia.
Qed.
Definition nf1 : nf := ([], 1).

Fixpoint zero_at (i : nat) (cs : list Z) : list Z :=
match cs with [] => [] | k :: cs' => match i with O => 0 :: cs' | S j => k :: zero_at j cs' end end.
Lemma dot_zero_at i : forall cs env, dot cs env = nth i cs 0 * nth i env 0 + dot (zero_at i cs) env.
Proof.
induction i as [|i IH]; intros [|k cs] env; cbn [zero_at dot nth]; try lia.
- destruct env; cbn [hd tl nth]; lia.
- rewrite (IH cs (tl env)). destruct env as [|v env]; cbn [hd tl nth]; [destruct i|]; lia.
Qed.
Definition omin (a : option Z) (h : Z) : option Z := match a with Some x => Some (Z.min x h) | None => Some h end.
Definition omax (a : option Z) (l : Z) : option Z := match a with Some x => Some (Z.max x l) | None => Some l end.
Fixpoint upd (i : nat) (f : option Z * option Z -> option Z * option Z) (bs : bnd) : bnd :=
match i with
| O => f (hd (None, None) bs) :: tl bs
| S j => hd (None, None) bs :: upd j f (tl bs)
end.
Lemma upd_ok i f : forall bs env, bounds_ok env bs -> (forall b, b_ok (nth i env 0) b -> b_ok (nth i env 0) (f b)) -> bounds_ok env (upd i f bs).
Proof.
induction i as [|i IH]; intros bs env OK Hf; cbn [upd bounds_ok].
- assert (nth 0 env 0 = hd 0 env) as E0 by (destruct env; reflexivity). rewrite E0 in Hf.
destruct bs; cbn in *; [split; [apply Hf; split; exact I|exact I]|]. destruct OK. split; auto.
- rewrite nth_hd_tl in Hf. destruct bs as [|b bs]; cbn [hd tl].
+ split; [split; exact I|]. apply IH; [exact I|exact Hf].
+ cbn in OK. destruct OK. split; [assumption|]. apply IH; assumption.
Qed.
Definition prop_at (a : nf) (bs : bnd) (i : nat) : bnd :=
let k := nth i (fst a) 0 in
if (k =? 1) || (k =? -1) then
match ub_dot (map (Z.mul (-1)) (zero_at i (fst a))) bs with
| Some u => if k =? 1 then upd i (fun b => (fst b, omin (snd b) (u - snd a))) bs
else upd i (fun b => (omax (fst b) (snd a - u), snd b)) bs
| None => bs
end
else bs.
Lemma prop_at_ok a env i bs : bounds_ok env bs -> nf_eval env a <= 0 -> bounds_ok env (prop_at a bs i).
Proof.
unfold prop_at, nf_eval. intros OK H. rewrite (dot_zero_at i) in H.
destruct ((nth i (fst a) 0 =? 1) || (nth i (fst a) 0 =? -1)) eqn:Ek; [|assumption].
destruct (ub_dot _ bs) as [u|] eqn:Eu; [|assumption].
pose proof (ub_dot_ok _ _ _ _ OK Eu) as U. rewrite dot_scale in U.
destruct (Z.eqb_spec (nth i (fst a) 0) 1) as [E1|N1].
- rewrite E1 in H. apply upd_ok; [assumption|]. intros [lo hi] [BL BH]; unfold b_ok, omin in *; cbn [fst snd] in *. split; [assumption|]. destruct hi; lia.
- apply orb_prop in Ek. destruct Ek as [Ek|Ek]; [discriminate|]. apply Z.eqb_eq in Ek. rewrite Ek in H.
apply upd_ok; [assumption|]. intros [lo hi] [BL BH]; unfold b_ok, omax in *; cbn [fst snd] in *. split; [|assumption]. destruct lo; lia.
Qed.
Definition add_le0 (bs : bnd) (a : nf) : bnd := fold_left (prop_at a) (seq 0 (length (fst a))) bs.
Lemma add_le0_ok bs env a : bounds_ok env bs -> nf_eval env a <= 0 -> bounds_ok env (add_le0 bs a).
Proof.
unfold add_le0. intros OK H. revert bs OK. induction (seq 0 (length (fst a))) as [|i l IH]; intros bs OK; cbn [fold_left]; [assumption|].
apply IH. apply prop_at_ok; assumption.
Qed.

Lemma dot_zero cs : forall env, forallb (Z.eqb 0) cs = true -> dot cs env = 0.
Proof. induction cs as [|c cs IH]; intros env E; cbn [forallb dot] in *; [reflexivity|]. apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. subst c. rewrite IH by assumption. lia. Qed.
Definition ost : Set := (bnd * list nf)%type.
Definition le0 (st : ost) (a : nf) : bool :=
le0b (fst st) a || existsb (fun h => le0b (fst st) (nf_sub a h)) (snd st)
|| ((length (snd st) <=? 16)%nat
&& existsb (fun h1 => existsb (fun h2 => le0b (fst st) (nf_sub a (nf_add h1 h2))) (snd st)) (snd st)).
Definition st_ok (env : list Z) (st : ost) : Prop :=
bounds_ok env (fst st) /\ forall h, In h (snd st) -> nf_eval env h <= 0.
Lemma le0_ok st env a : st_ok env st -> le0 st a = true -> nf_eval env a <= 0.
Proof.
intros [OKb OKf] E. unfold le0 in E. apply orb_prop in E. destruct E as [E|E]; [apply orb_prop in E; destruct E as [E|E]|].
- eapply le0b_ok; eassumption.
- apply existsb_exists in E. destruct E as [h [Hin E]]. apply (le0b_ok _ _ _ OKb) in E. rewrite nf_sub_ok in E.
pose proof (OKf _ Hin). lia.
- apply andb_prop in E. destruct E as [_ E].
apply existsb_exists in E. destruct E as [h1 [Hin1 E]]. apply existsb_exists in E. destruct E as [h2 [Hin2 E]].
apply (le0b_ok _ _ _ OKb) in E. rewrite nf_sub_ok, nf_add_ok in E. pose proof (OKf _ Hin1). pose proof (OKf _ Hin2). lia.
Qed.
Fixpoint odec (st : ost) (f : oform) : bool :=
match f with
| FLe a b => le0 st (nf_sub (norm a) (norm b))
| FLt a b => le0 st (nf_add (nf_sub (norm a) (norm b)) nf1)
| FEq a b => le0 st (nf_sub (norm a) (norm b)) && le0 st (nf_sub (norm b) (norm a))
| FGe a b => le0 st (nf_sub (norm b) (norm a))
| FGt a b => le0 st (nf_add (nf_sub (norm b) (norm a)) nf1)
| FAnd f g => odec st f && odec st g
| FOr f g => odec st f || odec st g
| FToNat a b => le0 st (nf_sub (norm a) (norm b)) && le0 st (nf_sub (norm b) (norm a))
| FNLe n m => Nat.leb n m | FNLt n m => Nat.ltb n m | FNEq n m => Nat.eqb n m
| FTrue => true | FFalse => false
end.
Lemma odec_ok st env f : st_ok env st -> odec st f = true -> ointerp env f.
Proof.
intros OK. induction f; cbn [odec ointerp]; intros E;
repeat match goal with
| E : _ && _ = true |- _ => apply andb_prop in E; destruct E
| E : le0 _ _ = true |- _ => apply (le0_ok _ _ _ OK) in E; rewrite ?nf_add_ok, ?nf_sub_ok, <- ?norm_ok in E
end; try (unfold nf_eval, nf1 in *; cbn [fst snd dot] in *; lia).
- split; auto.
- apply orb_prop in E. destruct E; [left|right]; auto.
- apply Nat.leb_le; assumption.
- apply Nat.ltb_lt; assumption.
- apply Nat.eqb_eq; assumption.
Qed.
Definition add_fact (st : ost) (a : nf) : ost := (add_le0 (fst st) a, a :: snd st).
Lemma add_fact_ok st env a : st_ok env st -> nf_eval env a <= 0 -> st_ok env (add_fact st a).
Proof.
intros [OKb OKf] H. split; cbn [add_fact fst snd]; [apply add_le0_ok; assumption|].
intros h [<-|Hin]; [assumption|apply OKf; assumption].
Qed.
Fixpoint add_hyp (st : ost) (f : oform) : ost :=
match f with
| FLe a b => add_fact st (nf_sub (norm a) (norm b))
| FLt a b => add_fact st (nf_add (nf_sub (norm a) (norm b)) nf1)
| FEq a b => add_fact (add_fact st (nf_sub (norm a) (norm b))) (nf_sub (norm b) (norm a))
| FGe a b => add_fact st (nf_sub (norm b) (norm a))
| FGt a b => add_fact st (nf_add (nf_sub (norm b) (norm a)) nf1)
| FAnd f g => add_hyp (add_hyp st f) g
| _ => st
end.
Lemma add_hyp_ok env f : forall st, st_ok env st -> ointerp env f -> st_ok env (add_hyp st f).
Proof.
induction f; intros st OK H; cbn [add_hyp ointerp] in *;
try (repeat apply add_fact_ok; try assumption; rewrite ?nf_add_ok, ?nf_sub_ok, <- ?norm_ok; unfold nf_eval, nf1; cbn [fst snd dot]; lia).
destruct H. auto.
Qed.

Definition is_or (f : oform) : bool := match f with FOr _ _ => true | _ => false end.
Definition add_all (st : ost) (hs : list oform) : ost := fold_left add_hyp hs st.
Definition reprop (st : ost) : ost := (fold_left add_le0 (snd st) (fst st), snd st).
Fixpoint split_or (st : ost) (ors : list oform) (g : oform) : bool :=
match ors with
| [] => odec st g
| FOr f1 f2 :: t => split_or (reprop (add_hyp st f1)) t g && split_or (reprop (add_hyp st f2)) t g
| _ :: t => split_or st t g
end.
Definition os_check0 (hs : list oform) (g : oform) : bool :=
split_or (reprop (add_all ([], []) (filter (fun f => negb (is_or f)) hs))) (filter is_or hs) g.
Lemma add_all_ok env hs : forall st, st_ok env st -> Forall (ointerp env) hs -> st_ok env (add_all st hs).
Proof.
unfold add_all. induction hs as [|h t IH]; intros st OK F; cbn [fold_left]; [assumption|].
inversion F; subst. apply IH; [apply add_hyp_ok|]; assumption.
Qed.
Lemma reprop_ok env st : st_ok env st -> st_ok env (reprop st).
Proof.
intros [OKb OKf]. split; cbn [reprop fst snd]; [|assumption].
revert OKb. generalize (fst st). induction (snd st) as [|h t IH]; intros bs OKb; cbn [fold_left]; [assumption|].
apply IH; [intros; apply OKf; right; assumption|]. apply add_le0_ok; [assumption|apply OKf; left; reflexivity].
Qed.
Lemma split_or_ok env g ors : forall st, st_ok env st -> Forall (ointerp env) ors -> split_or st ors g = true -> ointerp env g.
Proof.
induction ors as [|h t IH]; intros st OK F E; cbn [split_or] in E.
- eapply odec_ok; eassumption.
- inversion F as [|? ? Hh Ft]; subst. destruct h; try (eapply IH; eassumption).
apply andb_prop in E. destruct E as [E1 E2]. cbn [ointerp] in Hh. destruct Hh as [Hh|Hh].
+ eapply IH; [| |exact E1]; [apply reprop_ok, add_hyp_ok|]; assumption.
+ eapply IH; [| |exact E2]; [apply reprop_ok, add_hyp_ok|]; assumption.
Qed.
Lemma oimp_intro env G hs : (Forall (ointerp env) hs -> G) -> oimp env hs G.
Proof.
induction hs as [|h t IH]; cbn [oimp]; intros K; [apply K; constructor|].
intros H. apply IH. intros F. apply K. constructor; assumption.
Qed.
Lemma Forall_filter {A} (P : A -> Prop) f l : Forall P l -> Forall P (filter f l).
Proof. induction 1; cbn; [constructor|]. destruct (f x); [constructor|]; assumption. Qed.
Theorem os_sound (env : list Z) (hs : list oform) (g : oform) : os_check0 hs g = true -> oimp env hs (ointerp env g).
Proof.
intros E. apply oimp_intro. intros F. unfold os_check0 in E. eapply split_or_ok; [| |exact E].
- apply reprop_ok, add_all_ok; [split; [exact I|intros h []]|apply Forall_filter; assumption].
- apply Forall_filter; assumption.
Qed.

Definition mbnd : Set := list (option (Z * N) * option (Z * N)).
Fixpoint m_ub_dot (cs : list Z) (bs : mbnd) : option (Z * N) :=
match cs with
| [] => Some (0, 0%N)
| k :: cs' =>
let b := hd (None, None) bs in
match m_ub_dot cs' (tl bs) with
| None => None
| Some (r, m) => if k =? 0 then Some (r, m)
else match (if 0 <? k then snd b else fst b) with Some (h, mh) => Some (k * h + r, N.lor m mh) | None => None end
end
end.
Definition m_le0b (bs : mbnd) (a : nf) : option N :=
match m_ub_dot (fst a) bs with Some (u, m) => if u + snd a <=? 0 then Some m else None | None => None end.
Definition m_omin (a : option (Z * N)) (h : Z) (m : N) : option (Z * N) :=
match a with Some (x, mx) => if h <? x then Some (h, m) else Some (x, mx) | None => Some (h, m) end.
Definition m_omax (a : option (Z * N)) (l : Z) (m : N) : option (Z * N) :=
match a with Some (x, mx) => if x <? l then Some (l, m) else Some (x, mx) | None => Some (l, m) end.
Fixpoint m_upd (i : nat) (f : option (Z * N) * option (Z * N) -> option (Z * N) * option (Z * N)) (bs : mbnd) : mbnd :=
match i with
| O => f (hd (None, None) bs) :: tl bs
| S j => hd (None, None) bs :: m_upd j f (tl bs)
end.
Definition m_prop_at (a : nf) (ma : N) (bs : mbnd) (i : nat) : mbnd :=
let k := nth i (fst a) 0 in
if (k =? 1) || (k =? -1) then
match m_ub_dot (map (Z.mul (-1)) (zero_at i (fst a))) bs with
| Some (u, m) => if k =? 1 then m_upd i (fun b => (fst b, m_omin (snd b) (u - snd a) (N.lor m ma))) bs
else m_upd i (fun b => (m_omax (fst b) (snd a - u) (N.lor m ma), snd b)) bs
| None => bs
end
else bs.
Definition m_add_le0 (bs : mbnd) (am : nf * N) : mbnd := fold_left (m_prop_at (fst am) (snd am)) (seq 0 (length (fst (fst am)))) bs.
Definition most : Set := (mbnd * list (nf * N))%type.
Definition ofirst {A} (a b : option A) : option A := match a with Some _ => a | None => b end.
Fixpoint m_find {A} (f : A -> option N) (l : list A) : option N :=
match l with [] => None | x :: l' => ofirst (f x) (m_find f l') end.
Definition m_or (a : option N) (m : N) : option N := match a with Some x => Some (N.lor x m) | None => None end.
Definition m_le0 (st : most) (a : nf) : option N :=
ofirst (m_le0b (fst st) a)
(ofirst (m_find (fun h => m_or (m_le0b (fst st) (nf_sub a (fst h))) (snd h)) (snd st))
(if (length (snd st) <=? 16)%nat
then m_find (fun h1 => m_find (fun h2 => m_or (m_le0b (fst st) (nf_sub a (nf_add (fst h1) (fst h2)))) (N.lor (snd h1) (snd h2))) (snd st)) (snd st)
else None)).
Definition m_and (a b : option N) : option N := match a, b with Some x, Some y => Some (N.lor x y) | _, _ => None end.
Fixpoint m_odec (st : most) (f : oform) : option N :=
match f with
| FLe a b => m_le0 st (nf_sub (norm a) (norm b))
| FLt a b => m_le0 st (nf_add (nf_sub (norm a) (norm b)) nf1)
| FEq a b | FToNat a b => m_and (m_le0 st (nf_sub (norm a) (norm b))) (m_le0 st (nf_sub (norm b) (norm a)))
| FGe a b => m_le0 st (nf_sub (norm b) (norm a))
| FGt a b => m_le0 st (nf_add (nf_sub (norm b) (norm a)) nf1)
| FAnd f g => m_and (m_odec st f) (m_odec st g)
| FOr f g => ofirst (m_odec st f) (m_odec st g)
| FNLe n m => if Nat.leb n m then Some 0%N else None
| FNLt n m => if Nat.ltb n m then Some 0%N else None
| FNEq n m => if Nat.eqb n m then Some 0%N else None
| FTrue => Some 0%N | FFalse => None
end.
Definition m_add_fact (st : most) (a : nf) (m : N) : most := (m_add_le0 (fst st) (a, m), (a, m) :: snd st).
Fixpoint m_add_hyp (m : N) (st : most) (f : oform) : most :=
match f with
| FLe a b => m_add_fact st (nf_sub (norm a) (norm b)) m
| FLt a b => m_add_fact st (nf_add (nf_sub (norm a) (norm b)) nf1) m
| FEq a b => m_add_fact (m_add_fact st (nf_sub (norm a) (norm b)) m) (nf_sub (norm b) (norm a)) m
| FGe a b => m_add_fact st (nf_sub (norm b) (norm a)) m
| FGt a b => m_add_fact st (nf_add (nf_sub (norm b) (norm a)) nf1) m
| FAnd f g => m_add_hyp m (m_add_hyp m st f) g
| _ => st
end.
Definition m_reprop (st : most) : most := (fold_left m_add_le0 (snd st) (fst st), snd st).
Fixpoint m_split_or (st : most) (ors : list (oform * N)) (g : oform) : option N :=
match ors with
| [] => m_odec st g
| (FOr f1 f2, m) :: t => m_and (m_split_or (m_reprop (m_add_hyp m st f1)) t g) (m_split_or (m_reprop (m_add_hyp m st f2)) t g)
| _ :: t => m_split_or st t g
end.
Fixpoint m_number (i : N) (hs : list oform) : list (oform * N) :=
match hs with [] => [] | h :: t => (h, N.shiftl 1 i) :: m_number (N.succ i) t end.
Definition os_core (hs : list oform) (g : oform) : option N :=
let hm := m_number 0 hs in
let lin := filter (fun p => negb (is_or (fst p))) hm in
m_split_or (m_reprop (fold_left (fun st p => m_add_hyp (snd p) st (fst p)) lin ([], []))) (filter (fun p => is_or (fst p)) hm) g.

Module OffL2.
Import Ltac2.
Ltac2 mk (c : constr) (args : constr list) : constr := Constr.Unsafe.make (Constr.Unsafe.App c (Array.of_list args)).
Ltac2 gfuns () : constr list :=
[constr:(Z.of_nat); constr:(Z.pow); constr:(Z.add); constr:(Z.mul); constr:(Z.sub); constr:(Nat.mul); constr:(Nat.add);
constr:(Z.opp)].
Ltac2 Type refs := { r_Z_add : constr; r_Z_sub : constr; r_Z_mul : constr; r_Z_of_nat : constr; r_Z_to_nat : constr; r_and : constr; r_or : constr; r_Z_le : constr; r_Z_lt : constr; r_Z_ge : constr; r_Z_gt : constr; r_eq : constr; r_Z : constr; r_nat : constr; r_le : constr; r_lt : constr; r_True : constr; r_False : constr; r_Nat_mul : constr; r_Nat_add : constr; r_OV : constr; r_OC : constr; r_OAdd : constr; r_OSub : constr; r_OMul : constr; r_OMulR : constr; r_FLe : constr; r_FLt : constr; r_FEq : constr; r_FGe : constr; r_FGt : constr; r_FAnd : constr; r_FOr : constr; r_FToNat : constr; r_FNLe : constr; r_FNLt : constr; r_FNEq : constr; r_FTrue : constr; r_FFalse : constr; r_S : constr; r_O : constr; r_nil : constr; r_cons : constr; r_oform : constr; r_os_check0 : constr; r_true : constr; r_Nat2Z_is_nonneg : constr; r_Nat2Z_inj_mul : constr; r_Nat2Z_inj_add : constr; r_f_equal : constr; r_bool : constr; r_os_sound : constr; r_os_core : constr; r_xI : constr; r_ointerp : constr; r_Z0 : constr; r_gf : constr list; mutable r_bad : bool; mutable r_used : int list; mutable r_abs : bool; mutable r_shift : int }.
Ltac2 mk_refs () : refs := { r_Z_add := constr:(Z.add); r_Z_sub := constr:(Z.sub); r_Z_mul := constr:(Z.mul); r_Z_of_nat := constr:(Z.of_nat); r_Z_to_nat := constr:(Z.to_nat); r_and := constr:(and); r_or := constr:(or); r_Z_le := constr:(Z.le); r_Z_lt := constr:(Z.lt); r_Z_ge := constr:(Z.ge); r_Z_gt := constr:(Z.gt); r_eq := constr:(@eq); r_Z := constr:(Z); r_nat := constr:(nat); r_le := constr:(le); r_lt := constr:(lt); r_True := constr:(True); r_False := constr:(False); r_Nat_mul := constr:(Nat.mul); r_Nat_add := constr:(Nat.add); r_OV := constr:(OV); r_OC := constr:(OC); r_OAdd := constr:(OAdd); r_OSub := constr:(OSub); r_OMul := constr:(OMul); r_OMulR := constr:(OMulR); r_FLe := constr:(FLe); r_FLt := constr:(FLt); r_FEq := constr:(FEq); r_FGe := constr:(FGe); r_FGt := constr:(FGt); r_FAnd := constr:(FAnd); r_FOr := constr:(FOr); r_FToNat := constr:(FToNat); r_FNLe := constr:(FNLe); r_FNLt := constr:(FNLt); r_FNEq := constr:(FNEq); r_FTrue := constr:(FTrue); r_FFalse := constr:(FFalse); r_S := constr:(S); r_O := constr:(O); r_nil := constr:(@nil); r_cons := constr:(@cons); r_oform := constr:(oform); r_os_check0 := constr:(os_check0); r_true := constr:(true); r_Nat2Z_is_nonneg := constr:(Nat2Z.is_nonneg); r_Nat2Z_inj_mul := constr:(Nat2Z.inj_mul); r_Nat2Z_inj_add := constr:(Nat2Z.inj_add); r_f_equal := constr:(@f_equal); r_bool := constr:(bool); r_os_sound := constr:(os_sound); r_os_core := constr:(os_core); r_xI := constr:(xI); r_ointerp := constr:(ointerp); r_Z0 := constr:(Z0); r_gf := gfuns (); r_bad := false; r_used := []; r_abs := false; r_shift := 0 }.

Ltac2 rec ground (gf : constr list) (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Constructor _ _ => true
| Constr.Unsafe.App f args =>
if (match Constr.Unsafe.kind f with
| Constr.Unsafe.Constructor _ _ => true
| Constr.Unsafe.Constant _ _ => List.exist (Constr.equal f) gf
| _ => false end)
then Array.for_all (ground gf) args else false
| _ => false
end.

Ltac2 Type table := { mutable t_atoms : constr list; mutable t_n : int; mutable t_nat : constr;
mutable t_look : (constr * int * constr) list; mutable t_queue : constr list }.
Ltac2 new_table (rf : refs) : table := { t_atoms := []; t_n := 0; t_nat := rf.(r_O); t_look := []; t_queue := [] }.
Ltac2 rec find_mtf (t : constr) (seen : (constr * int * constr) list) (l : (constr * int * constr) list)
: ((int * constr) * (constr * int * constr) list) option :=
match l with
| [] => None
| e :: l' =>
let (x, i, ov) := e in
if Constr.equal x t then Some ((i, ov), e :: List.append (List.rev seen) l') else find_mtf t (e :: seen) l'
end.

Ltac2 rel_of (rf : refs) (i : int) (t : constr) : constr :=
if rf.(r_abs) then Constr.Unsafe.make (Constr.Unsafe.Rel (Int.add (Int.add i 1) (rf.(r_shift)))) else t.

Ltac2 atom (rf : refs) (tb : table) (fresh : bool) (t : constr) : constr * constr :=
match find_mtf t [] (tb.(t_look)) with
| Some r => let (io, l) := r in let (i, ov) := io in tb.(t_look) := l; rf.(r_used) := i :: rf.(r_used); (ov, rel_of rf i t)
| None =>
if fresh then
(let i := tb.(t_n) in
let ov := mk (rf.(r_OV)) [tb.(t_nat)] in
tb.(t_atoms) := t :: tb.(t_atoms); tb.(t_n) := Int.add i 1; tb.(t_nat) := mk (rf.(r_S)) [tb.(t_nat)];
tb.(t_look) := (t, i, ov) :: tb.(t_look); tb.(t_queue) := t :: tb.(t_queue);
rf.(r_used) := i :: rf.(r_used); (ov, rel_of rf i t))
else (rf.(r_bad) := true; (rf.(r_O), t))
end.

Ltac2 rec rexp0 (rf : refs) (tb : table) (fresh : bool) (t : constr) : bool * constr * constr :=
if rf.(r_bad) then (false, rf.(r_O), t) else
let mkat (t : constr) : bool * constr * constr := let (ov, ab) := atom rf tb fresh t in (false, ov, ab) in
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if Int.equal (Array.length args) 2 then
(let a := Array.get args 0 in let b := Array.get args 1 in
let isadd := Constr.equal f (rf.(r_Z_add)) in
if Bool.or isadd (Constr.equal f (rf.(r_Z_sub))) then
(let (ga, ra, aa) := rexp0 rf tb fresh a in
let (gb, rb, ab) := rexp0 rf tb fresh b in
if Bool.and ga gb then (true, t, t) else
(false, mk (if isadd then rf.(r_OAdd) else rf.(r_OSub))
[(if ga then mk (rf.(r_OC)) [a] else ra); (if gb then mk (rf.(r_OC)) [b] else rb)],
(if rf.(r_abs) then mk f [aa; ab] else t)))
else if Constr.equal f (rf.(r_Z_mul)) then
(let (ga, ra, aa) := rexp0 rf tb fresh a in
if ga then
(let (gb, rb, ab) := rexp0 rf tb fresh b in
if gb then (true, t, t) else (false, mk (rf.(r_OMul)) [a; rb], (if rf.(r_abs) then mk f [a; ab] else t)))
else if ground (rf.(r_gf)) b then (false, mk (rf.(r_OMulR)) [ra; b], (if rf.(r_abs) then mk f [aa; b] else t))
else mkat t)
else if ground (rf.(r_gf)) t then (true, t, t) else mkat t)
else if ground (rf.(r_gf)) t then (true, t, t) else mkat t
| Constr.Unsafe.Constructor _ _ => (true, t, t)
| _ => mkat t
end.
Ltac2 rexp (rf : refs) (tb : table) (fresh : bool) (t : constr) : constr * constr :=
let (g, r, ab) := rexp0 rf tb fresh t in ((if g then mk (rf.(r_OC)) [t] else r), ab).
Ltac2 to_nat_arg (rf : refs) (t : constr) : constr option :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if Bool.and (Constr.equal f (rf.(r_Z_to_nat))) (Int.equal (Array.length args) 1) then Some (Array.get args 0) else None
| _ => None
end.

Ltac2 rec rform2 (rf : refs) (tb : table) (fresh : bool) (t : constr) : constr * constr :=
if rf.(r_bad) then (rf.(r_O), t) else
let bad () : constr * constr := rf.(r_bad) := true; (rf.(r_FFalse), t) in
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
let n := Array.length args in
if Int.equal n 2 then
(let a := Array.get args 0 in let b := Array.get args 1 in
let bin (c : constr) : constr * constr :=
let (ra, aa) := rexp rf tb fresh a in let (rb, ab) := rexp rf tb fresh b in
(mk c [ra; rb], (if rf.(r_abs) then mk f [aa; ab] else t)) in
let con (c : constr) : constr * constr :=
let (ra, aa) := rform2 rf tb fresh a in let (rb, ab) := rform2 rf tb fresh b in
(mk c [ra; rb], (if rf.(r_abs) then mk f [aa; ab] else t)) in
if Constr.equal f (rf.(r_and)) then con (rf.(r_FAnd))
else if Constr.equal f (rf.(r_or)) then con (rf.(r_FOr))
else if Constr.equal f (rf.(r_Z_le)) then bin (rf.(r_FLe))
else if Constr.equal f (rf.(r_Z_lt)) then bin (rf.(r_FLt))
else if Constr.equal f (rf.(r_Z_ge)) then bin (rf.(r_FGe))
else if Constr.equal f (rf.(r_Z_gt)) then bin (rf.(r_FGt))
else if Constr.equal f (rf.(r_le)) then
(if Bool.and (ground (rf.(r_gf)) a) (ground (rf.(r_gf)) b) then (mk (rf.(r_FNLe)) [a; b], t) else bad ())
else if Constr.equal f (rf.(r_lt)) then
(if Bool.and (ground (rf.(r_gf)) a) (ground (rf.(r_gf)) b) then (mk (rf.(r_FNLt)) [a; b], t) else bad ())
else bad ())
else if Int.equal n 3 then
(if Constr.equal f (rf.(r_eq)) then
(let ty := Array.get args 0 in let a := Array.get args 1 in let b := Array.get args 2 in
if Constr.equal ty (rf.(r_Z)) then
(let (ra, aa) := rexp rf tb fresh a in let (rb, ab) := rexp rf tb fresh b in
(mk (rf.(r_FEq)) [ra; rb], (if rf.(r_abs) then mk f [ty; aa; ab] else t)))
else if Constr.equal ty (rf.(r_nat)) then
(if Bool.and (ground (rf.(r_gf)) a) (ground (rf.(r_gf)) b) then (mk (rf.(r_FNEq)) [a; b], t)
else match to_nat_arg rf a with
| Some a' => match to_nat_arg rf b with
| Some b' =>
let (ra, aa) := rexp rf tb fresh a' in let (rb, ab) := rexp rf tb fresh b' in
(mk (rf.(r_FToNat)) [ra; rb],
(if rf.(r_abs) then mk f [ty; mk (rf.(r_Z_to_nat)) [aa]; mk (rf.(r_Z_to_nat)) [ab]] else t))
| None => bad () end
| None => bad () end)
else bad ())
else bad ())
else bad ()
| _ => if Constr.equal t (rf.(r_True)) then (rf.(r_FTrue), t)
else if Constr.equal t (rf.(r_False)) then (rf.(r_FFalse), t) else bad ()
end.
Ltac2 rform (rf : refs) (tb : table) (fresh : bool) (t : constr) : constr := let (r, _) := rform2 rf tb fresh t in r.
Ltac2 rec mk_list (rf : refs) (ty : constr) (l : constr list) : constr :=
match l with [] => mk (rf.(r_nil)) [ty] | x :: l' => mk (rf.(r_cons)) [ty; x; mk_list rf ty l'] end.
Ltac2 check (rf : refs) (hs : constr list) (g : constr) : bool :=
Constr.equal (Std.eval_vm None (mk (rf.(r_os_check0)) [mk_list rf (rf.(r_oform)) hs; g])) (rf.(r_true)).

Ltac2 Type cand := { c_pf : constr; c_ty : constr; c_form : constr; c_idx : int list }.
Ltac2 forms (l : cand list) : constr list := List.map (fun (c : cand) => c.(c_form)) l.
Ltac2 is_for (rf : refs) (f : constr) : bool :=
match Constr.Unsafe.kind f with
| Constr.Unsafe.App h _ => Constr.equal h (rf.(r_FOr))
| _ => false
end.

Ltac2 rec split_at (n : int) (l : 'a list) : 'a list * 'a list :=
if Int.le n 0 then ([], l) else
match l with [] => ([], []) | x :: l' => let (a, b) := split_at (Int.sub n 1) l' in (x :: a, b) end.
Ltac2 rec ddmin (rf : refs) (g : constr) (fixed : cand list) (l : cand list) : cand list :=
match l with
| [] => []
| _ :: _ =>
if check rf (forms fixed) g then [] else
if Int.equal (List.length l) 1 then l else
let (l1, l2) := split_at (Int.div (List.length l) 2) l in
let r1 := ddmin rf g (List.append fixed l2) l1 in
let r2 := ddmin rf g (List.append fixed r1) l2 in
List.append r1 r2
end.

Ltac2 try_cand (rf : refs) (tb : table) (pf : unit -> constr) (ty : constr) (acc : cand list) : cand list :=
let s1 := tb.(t_atoms) in let s2 := tb.(t_n) in let s3 := tb.(t_nat) in let s4 := tb.(t_look) in let s5 := tb.(t_queue) in
rf.(r_bad) := false; rf.(r_used) := [];
let f := rform rf tb true ty in
if rf.(r_bad) then
(rf.(r_bad) := false; tb.(t_atoms) := s1; tb.(t_n) := s2; tb.(t_nat) := s3; tb.(t_look) := s4; tb.(t_queue) := s5; acc)
else { c_pf := pf (); c_ty := ty; c_form := f; c_idx := rf.(r_used) } :: acc.

Ltac2 rec arith_shape (rf : refs) (ty : constr) : bool :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
let n := Array.length args in
if Int.equal n 2 then
(if Bool.or (Constr.equal f (rf.(r_and))) (Constr.equal f (rf.(r_or)))
then Bool.and (arith_shape rf (Array.get args 0)) (arith_shape rf (Array.get args 1))
else List.exist (Constr.equal f) [rf.(r_Z_le); rf.(r_Z_lt); rf.(r_Z_ge); rf.(r_Z_gt)])
else if Int.equal n 3 then
(if Constr.equal f (rf.(r_eq)) then Bool.or (Constr.equal (Array.get args 0) (rf.(r_Z))) (Constr.equal (Array.get args 0) (rf.(r_nat)))
else false)
else false
| _ => false
end.
Ltac2 is_nat_eq (rf : refs) (ty : constr) : (constr * constr) option :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
if Bool.and (Int.equal (Array.length args) 3) (Bool.and (Constr.equal f (rf.(r_eq))) (Constr.equal (Array.get args 0) (rf.(r_nat))))
then Some (Array.get args 1, Array.get args 2) else None
| _ => None
end.
Ltac2 of_nat_arg (rf : refs) (t : constr) : constr option :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if Bool.and (Constr.equal f (rf.(r_Z_of_nat))) (Int.equal (Array.length args) 1) then Some (Array.get args 0) else None
| _ => None
end.

Ltac2 all_hyps (rf : refs) (tb : table) : cand list :=
List.rev (List.fold_left (fun (acc : cand list) (h : ident * constr option * constr) =>
let (id, _, ty) := h in
if arith_shape rf ty then
(match is_nat_eq rf ty with
| Some ab =>
let (a, b) := ab in
if Bool.and (ground (rf.(r_gf)) a) (ground (rf.(r_gf)) b) then acc else
try_cand rf tb (fun () => mk (rf.(r_f_equal)) [(rf.(r_nat)); (rf.(r_Z)); (rf.(r_Z_of_nat)); a; b; Control.hyp id])
(mk (rf.(r_eq)) [(rf.(r_Z)); mk (rf.(r_Z_of_nat)) [a]; mk (rf.(r_Z_of_nat)) [b]]) acc
| None => try_cand rf tb (fun () => Control.hyp id) ty acc
end)
else acc) [] (Control.hyps ())).

Ltac2 rec virtuals (rf : refs) (tb : table) (acc : cand list) : cand list :=
match tb.(t_queue) with
| [] => acc
| t :: q =>
tb.(t_queue) := q;
let acc :=
match of_nat_arg rf t with
| None => acc
| Some n =>
let zn (x : constr) : constr := mk (rf.(r_Z_of_nat)) [x] in
let acc := try_cand rf tb (fun () => mk (rf.(r_Nat2Z_is_nonneg)) [n]) (mk (rf.(r_Z_le)) [rf.(r_Z0); t]) acc in
match Constr.Unsafe.kind n with
| Constr.Unsafe.App f args =>
if Int.equal (Array.length args) 2 then
(let a := Array.get args 0 in let b := Array.get args 1 in
if Constr.equal f (rf.(r_Nat_mul)) then
(if Bool.or (ground (rf.(r_gf)) a) (ground (rf.(r_gf)) b) then
try_cand rf tb (fun () => mk (rf.(r_Nat2Z_inj_mul)) [a; b])
(mk (rf.(r_eq)) [rf.(r_Z); t; mk (rf.(r_Z_mul)) [zn a; zn b]]) acc
else acc)
else if Constr.equal f (rf.(r_Nat_add)) then
try_cand rf tb (fun () => mk (rf.(r_Nat2Z_inj_add)) [a; b])
(mk (rf.(r_eq)) [rf.(r_Z); t; mk (rf.(r_Z_add)) [zn a; zn b]]) acc
else acc)
else acc
| _ => acc
end
end in
virtuals rf tb acc
end.

Ltac2 reached (k : int) (reach : int list) (i : int) : bool := if Int.lt i k then true else List.exist (Int.equal i) reach.
Ltac2 rec closure (k : int) (rounds : int) (reach : int list) (sel : cand list) (rest : cand list) : cand list :=
if Int.le rounds 0 then List.rev sel else
let (yes, no) := List.partition (fun (c : cand) => List.exist (reached k reach) (c.(c_idx))) rest in
match yes with
| [] => List.rev sel
| _ :: _ =>
let reach := List.fold_left (fun (r : int list) (c : cand) => List.append (c.(c_idx)) r) reach yes in
closure k (Int.sub rounds 1) reach (List.append (List.rev yes) sel) no
end.

Ltac2 finish_abs (rf : refs) (hs : cand list) : unit :=
let tb := new_table rf in
let k := List.length hs in
rf.(r_abs) := true; rf.(r_shift) := k;
let (g, tg) := rform2 rf tb true (Control.goal ()) in
let fts := List.mapi (fun (j : int) (c : cand) => rf.(r_shift) := j; rform2 rf tb true (c.(c_ty))) hs in
rf.(r_abs) := false;
let n := tb.(t_n) in
let rel (i : int) : constr := Constr.Unsafe.make (Constr.Unsafe.Rel i) in
let rec envl (i : int) : constr list := if Int.ge i n then [] else rel (Int.add (Int.add i 1) k) :: envl (Int.add i 1) in
let rec hvars (j : int) : constr list := if Int.gt j k then [] else rel (Int.add (Int.sub k j) 1) :: hvars (Int.add j 1) in
let env := mk_list rf (rf.(r_Z)) (envl 0) in
let l := mk_list rf (rf.(r_oform)) (List.map (fun (p : constr * constr) => let (f, _) := p in f) fts) in
let ety := mk (rf.(r_eq)) [(rf.(r_bool)); mk (rf.(r_os_check0)) [l; g]; (rf.(r_true))] in
let er := Constr.Unsafe.make (Constr.Unsafe.Cast constr:(@eq_refl bool true) Constr.Cast.vm ety) in
let body := Constr.Unsafe.make (Constr.Unsafe.Cast (mk (rf.(r_os_sound)) (List.append [env; l; g; er] (hvars 1))) Constr.Cast.default tg) in
let lam (ty : constr) (b : constr) : constr :=
Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.unsafe_make None Constr.Binder.Relevant ty) b) in
let body := List.fold_right (fun (p : constr * constr) (b : constr) => let (_, t) := p in lam t b) fts body in
let rec wrap (i : int) (b : constr) : constr := if Int.ge i n then b else wrap (Int.add i 1) (lam (rf.(r_Z)) b) in
let f := wrap 0 body in
let t := mk f (List.append (tb.(t_atoms)) (List.map (fun (c : cand) => c.(c_pf)) hs)) in
Control.refine (fun () => t).
Ltac2 finish_inline (rf : refs) (hs : cand list) : unit :=

let tb := new_table rf in
let g := rform rf tb true (Control.goal ()) in
let fs := List.map (fun (c : cand) => rform rf tb true (c.(c_ty))) hs in
let env := mk_list rf (rf.(r_Z)) (List.rev (tb.(t_atoms))) in
let l := mk_list rf (rf.(r_oform)) fs in
let ety := mk (rf.(r_eq)) [(rf.(r_bool)); mk (rf.(r_os_check0)) [l; g]; (rf.(r_true))] in
let er := Constr.Unsafe.make (Constr.Unsafe.Cast constr:(@eq_refl bool true) Constr.Cast.vm ety) in
let t := mk (rf.(r_os_sound)) (List.append [env; l; g; er] (List.map (fun (c : cand) => c.(c_pf)) hs)) in
Control.refine (fun () => t).

Ltac2 mutable os_abstract () : bool := false.
Ltac2 finish (rf : refs) (hs : cand list) : unit := if os_abstract () then finish_abs rf hs else finish_inline rf hs.

Ltac2 rec pos_bits (rf : refs) (cur : int) (p : constr) : int list :=
match Constr.Unsafe.kind p with
| Constr.Unsafe.App c args =>
let r := pos_bits rf (Int.add cur 1) (Array.get args 0) in
if Constr.equal c (rf.(r_xI)) then cur :: r else r
| _ => [cur]
end.
Ltac2 core (rf : refs) (hs : constr list) (g : constr) : int list option :=
let r := Std.eval_vm None (mk (rf.(r_os_core)) [mk_list rf (rf.(r_oform)) hs; g]) in
match Constr.Unsafe.kind r with
| Constr.Unsafe.App _ args =>
if Int.equal (Array.length args) 2 then
(match Constr.Unsafe.kind (Array.get args 1) with
| Constr.Unsafe.App _ pa => Some (pos_bits rf 0 (Array.get pa 0))
| _ => Some []
end)
else None
| _ => None
end.
Ltac2 rec select (i : int) (idx : int list) (l : cand list) : cand list :=
match l with
| [] => []
| c :: l' => if List.exist (Int.equal i) idx then c :: select (Int.add i 1) idx l' else select (Int.add i 1) idx l'
end.

Ltac2 solve_with (rf : refs) (g : constr) (cs : cand list) : cand list option :=
let (ors, lin) := List.partition (fun (c : cand) => is_for rf (c.(c_form))) cs in
if Int.gt (List.length lin) 24 then None else
let (ors2, _) := split_at 2 ors in
let l := List.append lin ors2 in
match l with
| [] => None
| _ :: _ =>
match core rf (forms l) g with
| None => None
| Some idx =>
let sub := select 0 idx l in
if check rf (forms sub) g then Some sub
else if check rf (forms l) g then Some (ddmin rf g [] l) else None
end
end.
Ltac2 os_lia () : unit :=
let rf := mk_refs () in
let tb := new_table rf in
let g := rform rf tb true (Control.goal ()) in
if rf.(r_bad) then Control.zero Not_found else
if check rf [] g then finish rf [] else
let k := tb.(t_n) in
if Int.equal k 0 then Control.zero Not_found else
let hyps := all_hyps rf tb in
let all := List.append hyps (List.rev (virtuals rf tb [])) in
let ca := List.filter (fun (c : cand) => List.for_all (fun (i : int) => Int.lt i k) (c.(c_idx))) all in
match solve_with rf g ca with
| Some hs => finish rf hs
| None =>
let cb := closure k 3 [] [] all in
match (if Int.lt (List.length ca) (List.length cb) then solve_with rf g cb else None) with
| Some hs => finish rf hs
| None => Control.zero Not_found
end
end.
End OffL2.
Ltac os_lia := lazymatch goal with |- ?g => tryif has_evar g then fail else ltac2:(Control.enter OffL2.os_lia) end.

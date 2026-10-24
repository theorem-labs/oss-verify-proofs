(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState}.
Definition t_bot : TSet := fun _ => False.
Lemma t_alt2_congr : forall A A' B B',
t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). tauto. Qed.
Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_comm : forall A B, t_eq (t_alt2 A B) (t_alt2 B A).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_assoc : forall A B C, t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof. intros A B C tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_absorb : forall A B, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_mono : forall (A A' B B' : TSet) tr,
(A tr -> A' tr) -> (B tr -> B' tr) -> t_alt2 A B tr -> t_alt2 A' B' tr.
Proof. intros A A' B B' tr HA HB [H|H]; [left|right]; auto. Qed.
Definition fallible (q : kreq) : bool :=
match q with
| KMmapRW _ | KMmapNone _ | KBrkGrow _ | KMprotect _ => true
| KMremap _ _ _ => true
| _ => false
end.
Definition spurious (q : kreq) : bool :=
match q with
| KMremap _ _ _ => true
| _ => false
end.
Definition canon (q : kreq) : Z :=
match q with
| KJunk p => p mod 256
| _ => 1
end.
Lemma canon_answer_ok : forall q, answer_ok q (canon q).
Proof. intros q. destruct q; cbn; try exact I. apply Z.mod_pos_bound. lia. Qed.
Lemma answer_ok_kernel : forall q z, fallible q = true -> answer_ok q z.
Proof. intros q z H; destruct q; cbn in *; try exact I; discriminate. Qed.
Fixpoint tset {S A : Type} (t : itree S A) (K : A -> TSet) : TSet :=
match t with
| IRet a => K a
| IFail _ => t_bot
| IAsk q _ k =>
if fallible q
then (if spurious q then t_alt2 (tset (k 0) K) (tset (k 1) K)
else tset (k 1) K)
else tset (k (canon q)) K
end.
Lemma tset_ret {S A} (a : A) (K : A -> TSet) : tset (S:=S) (IRet a) K = K a.
Proof. reflexivity. Qed.
Lemma tset_fail {S A} f (K : A -> TSet) : tset (S:=S) (A:=A) (IFail f) K = t_bot.
Proof. reflexivity. Qed.
Lemma tset_ask_fallible {S A} q (s : S) k (K : A -> TSet) :
fallible q = true -> spurious q = true -> tset (IAsk q s k) K = t_alt2 (tset (k 0) K) (tset (k 1) K).
Proof. intros H H'. cbn. rewrite H, H'. reflexivity. Qed.
Lemma tset_ask_granted {S A} q (s : S) k (K : A -> TSet) :
fallible q = true -> spurious q = false -> tset (IAsk q s k) K = tset (k 1) K.
Proof. intros H H'. cbn. rewrite H, H'. reflexivity. Qed.
Lemma tset_ask_canon {S A} q (s : S) k (K : A -> TSet) :
fallible q = false -> tset (IAsk q s k) K = tset (k (canon q)) K.
Proof. intros H. cbn. rewrite H. reflexivity. Qed.
Lemma tset_mono {S A} : forall (t : itree S A) (K K' : A -> TSet) tr,
(forall a tr, K a tr -> K' a tr) -> tset t K tr -> tset t K' tr.
Proof.
induction t as [a | q s k IH | f]; intros K K' tr HK H; cbn in *.
- apply HK, H.
- destruct (fallible q); [destruct (spurious q)|].
+ destruct H as [H|H]; [left|right]; eapply IH; eauto.
+ eapply IH; eauto.
+ eapply IH; eauto.
- exact H.
Qed.
Lemma tset_congr {S A} : forall (t : itree S A) (K K' : A -> TSet),
(forall a, t_eq (K a) (K' a)) -> t_eq (tset t K) (tset t K').
Proof.
intros t K K' HK tr. split; apply tset_mono; intros a tr' H; apply (HK a); exact H.
Qed.
Lemma tset_ibind {S A B} : forall (t : itree S A) (f : A -> itree S B) (K : B -> TSet),
tset (ibind t f) K = tset t (fun a => tset (f a) K).
Proof.
induction t as [a | q s k IH | e]; intros f K; cbn; [reflexivity | | reflexivity].
destruct (fallible q); [destruct (spurious q)|]; rewrite ?IH; reflexivity.
Qed.
Lemma tset_mbind {A B} : forall (m : M A) (f : A -> M B) (s : astate) (K : B * astate -> TSet),
tset (bind m f s) K = tset (m s) (fun r => tset (let '(a, s') := r in f a s') K).
Proof. intros m f s K. unfold bind. apply tset_ibind. Qed.
Lemma tset_mbind_eq {A B} : forall (m : M A) (f : A -> M B) (s : astate) (K : B * astate -> TSet),
t_eq (tset (bind m f s) K) (tset (m s) (fun r => tset (f (fst r) (snd r)) K)).
Proof.
intros m f s K. rewrite tset_mbind. apply tset_congr. intros [a s']. apply t_eq_refl.
Qed.
Lemma tset_const {A} : forall (t : itree astate A) (T : TSet),
safe t -> t_eq (tset t (fun _ => T)) T.
Proof.
induction t as [a | q s k IH | f]; intros T Hs; cbn in *.
- apply t_eq_refl.
- destruct (fallible q) eqn:Hf; [destruct (spurious q)|].
+ eapply t_eq_trans; [| apply t_alt2_idem].
apply t_alt2_congr; apply IH; apply Hs; apply answer_ok_kernel; exact Hf.
+ apply IH. apply Hs. apply answer_ok_kernel; exact Hf.
+ apply IH. apply Hs. apply canon_answer_ok.
- destruct Hs.
Qed.
Lemma tset_const_on {A} : forall (t : itree astate A) (K : A -> TSet) (T : TSet),
safe t -> (forall a, t_eq (K a) T) -> t_eq (tset t K) T.
Proof.
intros t K T Hs HK. eapply t_eq_trans; [apply tset_congr; exact HK | apply tset_const; exact Hs].
Qed.
Fixpoint jinv {A : Type} (K : A -> TSet) (t : itree astate A) : Prop :=
match t with
| IRet _ => True
| IFail _ => True
| IAsk (KJunk p) _ k =>
(forall z, 0 <= z < 256 -> t_eq (tset (k z) K) (tset (k (p mod 256)) K)) /\
(forall z, 0 <= z < 256 -> jinv K (k z))
| IAsk q _ k => if fallible q then jinv K (k 0) /\ jinv K (k 1) else jinv K (k 1)
end.
Fixpoint jfree {S A : Type} (t : itree S A) : Prop :=
match t with
| IRet _ => True
| IFail _ => True
| IAsk (KJunk _) _ _ => False
| IAsk q _ k => if fallible q then jfree (k 0) /\ jfree (k 1) else jfree (k 1)
end.
Lemma jfree_jinv {A} : forall (t : itree astate A) K, jfree t -> jinv K t.
Proof.
induction t as [a | q s k IH | f]; intros K H; cbn in *; try exact I.
destruct q; cbn in *; try (destruct H as [H0 H1]; split; apply IH; assumption); try (apply IH; exact H). destruct H.
Qed.
Lemma jinv_const {A} : forall (t : itree astate A) (T : TSet), safe t -> jinv (fun _ => T) t.
Proof.
induction t as [a | q s k IH | f]; intros T Hs; cbn in *; try exact I.
destruct q; cbn; try (split; apply IH; apply Hs; exact I); try (apply IH; apply Hs; exact I).
split.
- intros z Hz. eapply t_eq_trans; [apply tset_const; apply Hs; exact Hz|].
apply t_eq_sym. apply tset_const. apply Hs. cbn. apply Z.mod_pos_bound. lia.
- intros z Hz. apply IH. apply Hs. exact Hz.
Qed.
Lemma tsim_inv {A B} (R : A -> B -> Prop) (t : itree astate A) (u : itree astate B) :
tsim R t u ->
match t, u with
| IRet a, IRet b => R a b
| IAsk q _ k, IAsk q' _ k' =>
match q with
| KJunk _ => (exists p', q' = KJunk p') /\ forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> tsim R (k z) (k' z')
| _ => q = q' /\ forall z, tsim R (k z) (k' z)
end
| IFail _, IFail _ => True
| _, _ => False
end.
Proof.
intros H. destruct t as [a | q s k | f]; destruct u as [b | q' s' k' | f']; cbn in H;
try exact H; try (destruct q; exact H).
destruct q; destruct q'; cbn in H; try exact H; try (destruct H as [E _]; discriminate).
split; [eexists; reflexivity | exact H].
Qed.
Lemma tsim_tset {A B} : forall (R : A -> B -> Prop) (t : itree astate A) (u : itree astate B)
(K : A -> TSet) (K' : B -> TSet),
tsim R t u -> (forall a b, R a b -> t_eq (K a) (K' b)) -> t_eq (tset t K) (tset u K').
Proof.
intros R t; induction t as [a | q s k IH | f]; intros u K K' Hs HK; apply tsim_inv in Hs;
destruct u as [b | q' s' k' | f']; try contradiction.
- cbn. apply HK. exact Hs.
- destruct q;
try (destruct Hs as [<- Hk]; cbn; first [ apply t_alt2_congr; apply IH; auto | apply IH; auto ]).
destruct Hs as [[p' ->] Hk]. cbn. apply IH; [| exact HK]. apply Hk; apply Z.mod_pos_bound; lia.
- cbn. apply t_eq_refl.
Qed.
Lemma tsim_jinv {A} : forall (R : A -> A -> Prop) (t u : itree astate A) (K : A -> TSet),
tsim R t u -> (forall a b, R a b -> t_eq (K a) (K b)) -> jinv K t.
Proof.
intros R t; induction t as [a | q s k IH | f]; intros u K Hs HK; apply tsim_inv in Hs;
destruct u as [b | q' s' k' | f']; try contradiction; cbn; try exact I.
destruct q as [|np| |ln|ln|pg|r ln|mr mol mnl|p]; cbn;
try (destruct Hs as [<- Hk]; first [split; eapply IH; eauto | eapply IH; eauto]; fail).
destruct Hs as [[p' ->] Hk].
assert (Hm : 0 <= p mod 256 < 256) by (apply Z.mod_pos_bound; lia).
split.
- intros z Hz. eapply t_eq_trans.
+ eapply (tsim_tset R); [apply (Hk z z); auto | exact HK].
+ apply t_eq_sym. eapply (tsim_tset R); [apply (Hk (p mod 256) z); auto | exact HK].
- intros z Hz. eapply IH; [apply (Hk z z); auto | exact HK].
Qed.
Lemma tsim_mono {A B} : forall (R R' : A -> B -> Prop) (t : itree astate A) (u : itree astate B),
(forall a b, R a b -> R' a b) -> tsim R t u -> tsim R' t u.
Proof.
intros R R' t; induction t as [a | q s k IH | f]; intros u HR Hs; apply tsim_inv in Hs;
destruct u as [b | q' s' k' | f']; try contradiction.
- cbn. auto.
- destruct q; try (destruct Hs as [<- Hk]; cbn; split; [reflexivity | intros z; apply IH; auto]; fail).
destruct Hs as [[p' ->] Hk]. cbn. intros z z' Hz Hz'. apply IH; auto.
- exact I.
Qed.
Lemma tsim_ret {A B} : forall (R : A -> B -> Prop) a b, R a b -> tsim R (IRet (S:=astate) a) (IRet b).
Proof. intros R a b H. exact H. Qed.
Lemma tsim_ibind {A B C D} :
forall (R : A -> B -> Prop) (R' : C -> D -> Prop)
(t : itree astate A) (u : itree astate B) (f : A -> itree astate C) (g : B -> itree astate D),
tsim R t u -> (forall a b, R a b -> tsim R' (f a) (g b)) -> tsim R' (ibind t f) (ibind u g).
Proof.
intros R R' t; induction t as [a | q s k IH | e]; intros u f g Hs Hf; apply tsim_inv in Hs;
destruct u as [b | q' s' k' | e']; try contradiction.
- cbn. apply Hf. exact Hs.
- destruct q; try (destruct Hs as [<- Hk]; cbn; split; [reflexivity | intros z; apply IH; auto]; fail).
destruct Hs as [[p' ->] Hk]. cbn. intros z z' Hz Hz'. apply IH; auto.
- cbn. exact I.
Qed.
Lemma tsim_mbind {A B C D} :
forall (R : A * astate -> B * astate -> Prop) (R' : C * astate -> D * astate -> Prop)
(m : M A) (m' : M B) (f : A -> M C) (g : B -> M D) (s t : astate),
tsim R (m s) (m' t) ->
(forall a s1 b t1, R (a, s1) (b, t1) -> tsim R' (f a s1) (g b t1)) ->
tsim R' (bind m f s) (bind m' g t).
Proof.
intros R R' m m' f g s t Hm Hf. unfold bind. eapply tsim_ibind; [exact Hm|].
intros [a s1] [b t1] H. apply Hf. exact H.
Qed.
Lemma safe_ibind {A B} : forall (t : itree astate A) (f : A -> itree astate B),
safe t -> (forall a, safe (f a)) -> safe (ibind t f).
Proof.
induction t as [a | q s k IH | e]; intros f Hs Hf; cbn in *; [apply Hf | | destruct Hs].
intros z Hz. apply IH; [apply Hs; exact Hz | exact Hf].
Qed.
Fixpoint leaves {S A : Type} (P : A -> Prop) (t : itree S A) : Prop :=
match t with
| IRet a => P a
| IFail _ => True
| IAsk q _ k => forall z, answer_ok q z -> leaves P (k z)
end.
Lemma safe_ibind_leaves {A B} : forall (P : A -> Prop) (t : itree astate A) (f : A -> itree astate B),
safe t -> leaves P t -> (forall a, P a -> safe (f a)) -> safe (ibind t f).
Proof.
induction t as [a | q s k IH | e]; intros f Hs Hl Hf; cbn in *; [apply Hf; exact Hl | | destruct Hs].
intros z Hz. apply IH; [apply Hs; exact Hz | apply Hl; exact Hz | exact Hf].
Qed.
Lemma leaves_mono {S A} : forall (P Q : A -> Prop) (t : itree S A),
(forall a, P a -> Q a) -> leaves P t -> leaves Q t.
Proof.
induction t as [a | q s k IH | e]; intros HPQ H; cbn in *; auto.
Qed.
End c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
Section d. Context {fx : YK11.FPState}.
Lemma itok_leaves {A} : forall (t : itree astate A) (Q : A -> Prop), itok t Q -> leaves Q t.
Proof.
induction t as [a | q s k IH | e]; intros Q H; cbn in *; [exact H | | exact I].
intros z Hz. apply IH. apply (proj2 H). exact Hz.
Qed.
Lemma leaves_ibind {A B} : forall (P : A -> Prop) (Q : B -> Prop) (t : itree astate A) (f : A -> itree astate B),
leaves P t -> (forall a, P a -> leaves Q (f a)) -> leaves Q (ibind t f).
Proof.
induction t as [a | q s k IH | e]; intros f Hl Hf; cbn in *; [apply Hf; exact Hl | | exact I].
intros z Hz. apply IH; [apply Hl; exact Hz | exact Hf].
Qed.
Fixpoint gtree {A : Type} (G : astate -> kreq -> Prop) (t : itree astate A) : Prop :=
match t with
| IRet _ => True
| IFail _ => True
| IAsk (KJunk p) s k => forall z, 0 <= z < 256 -> gtree G (k z)
| IAsk q s k => if fallible q then G s q /\ gtree G (k 0) /\ gtree G (k 1) else gtree G (k 1)
end.
Lemma gtree_mono {A} : forall (G G' : astate -> kreq -> Prop) (t : itree astate A),
(forall s q, G s q -> G' s q) -> gtree G t -> gtree G' t.
Proof.
induction t as [a | q s k IH | e]; intros HG H; cbn in *; auto.
destruct q; cbn in *; try (destruct H as (H1 & H2 & H3); repeat split; auto; fail); auto;
intros z Hz; apply IH; auto.
Qed.
Definition canswer (q : kreq) (z : Z) : Prop :=
match q with
| KJunk _ => 0 <= z < 256
| _ => if fallible q then z = 0 \/ z = 1 else z = 1
end.
Lemma canswer_answer_ok : forall q z, canswer q z -> answer_ok q z.
Proof. intros q z H. destruct q; cbn in *; auto; exact I. Qed.
Fixpoint cpath {A : Type} (t : itree astate A) (tr : list (kreq * Z)) (a : A) : Prop :=
match t, tr with
| IRet a', [] => a' = a
| IAsk q _ k, (q', z) :: tr' => q' = q /\ canswer q z /\ cpath (k z) tr' a
| _, _ => False
end.
Lemma cpath_yields {A} : forall (t : itree astate A) tr a, cpath t tr a -> yields t tr a.
Proof.
induction t as [a' | q s k IH | f]; intros [|[q' z] tr] a H; cbn in *; try exact H; try contradiction.
destruct H as (-> & Hc & H). split; [reflexivity|]. split; [apply canswer_answer_ok; exact Hc | apply IH; exact H].
Qed.
Lemma cpath_ibind {A B} : forall (t : itree astate A) (f : A -> itree astate B) tr1 a tr2 b,
cpath t tr1 a -> cpath (f a) tr2 b -> cpath (ibind t f) (tr1 ++ tr2) b.
Proof.
induction t as [a' | q s k IH | e]; intros f [|[q' z] tr1] a tr2 b H1 H2; cbn in *; try contradiction.
- subst a'. exact H2.
- destruct H1 as (-> & Hc & H1). split; [reflexivity|]. split; [exact Hc|]. eapply IH; eauto.
Qed.
Lemma cpath_ibind_inv {A B} : forall (t : itree astate A) (f : A -> itree astate B) tr b,
cpath (ibind t f) tr b -> exists tr1 a tr2, tr = tr1 ++ tr2 /\ cpath t tr1 a /\ cpath (f a) tr2 b.
Proof.
induction t as [a' | q s k IH | e]; intros f tr b H; cbn in H.
- exists [], a', tr. cbn. auto.
- destruct tr as [|[q' z] tr]; [destruct H|]. destruct H as (-> & Hc & H).
destruct (IH z f tr b H) as (tr1 & a & tr2 & -> & H1 & H2).
exists ((q, z) :: tr1), a, tr2. cbn. auto.
- destruct tr; destruct H.
Qed.
Lemma leaves_cpath {A} : forall (P : A -> Prop) (t : itree astate A) tr a,
leaves P t -> cpath t tr a -> P a.
Proof.
induction t as [a' | q s k IH | e]; intros [|[q' z] tr] a Hl H; cbn in *; try contradiction.
- subst a'. exact Hl.
- destruct H as (-> & Hc & H). eapply IH; [apply Hl; apply canswer_answer_ok; exact Hc | exact H].
Qed.
Lemma jinv_after {A B} : forall (K : B -> TSet) (t : itree astate A) (f : A -> itree astate B) tr a,
jinv K (ibind t f) -> cpath t tr a -> jinv K (f a).
Proof.
intros K t; induction t as [a' | q s k IH | e]; intros f [|[q' z] tr] a Hj H; cbn in H; try contradiction.
- subst a'. exact Hj.
- destruct H as (-> & Hc & H). cbn in Hj.
destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in Hc, Hj;
first [   destruct Hj as [Heq Hj]; eapply IH; [apply Hj; exact Hc | exact H]
|   destruct Hj as [H0 H1]; destruct Hc as [-> | ->]; (eapply IH; [| exact H]; assumption)
|   subst z; eapply IH; [| exact H]; assumption ].
Qed.
Lemma gtree_after {A B} : forall (G : astate -> kreq -> Prop) (t : itree astate A) (f : A -> itree astate B) tr a,
gtree G (ibind t f) -> cpath t tr a -> gtree G (f a).
Proof.
intros G t; induction t as [a' | q s k IH | e]; intros f [|[q' z] tr] a Hg H; cbn in H; try contradiction.
- subst a'. exact Hg.
- destruct H as (-> & Hc & H). cbn in Hg.
destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in Hc, Hg;
first [   eapply IH; [apply Hg; exact Hc | exact H]
| destruct Hg as (_ & H0 & H1); destruct Hc as [-> | ->]; (eapply IH; [| exact H]; assumption)
| subst z; eapply IH; [| exact H]; assumption ].
Qed.
Lemma jinv_ibind {A B} : forall (K : B -> TSet) (t : itree astate A) (f : A -> itree astate B),
jinv (fun a => tset (f a) K) t ->
(forall tr a, cpath t tr a -> jinv K (f a)) ->
jinv K (ibind t f).
Proof.
intros K t; induction t as [a' | q s k IH | e]; intros f Hj Hf; cbn in *.
- apply (Hf []). reflexivity.
- assert (REC : forall z, canswer q z -> jinv (fun a => tset (f a) K) (k z) -> jinv K (ibind (k z) f)).
{ intros z Hc Hz. apply IH; [exact Hz|]. intros tr a Hp. apply (Hf ((q, z) :: tr)). cbn. auto. }
destruct q; cbn in REC, Hj |- *;
try (destruct Hj as [H0 H1]; split; apply REC; auto; fail);
try (apply REC; [reflexivity | exact Hj]; fail).
destruct Hj as [Heq Hj]. split.
+ intros z Hz. rewrite !tset_ibind. apply Heq. exact Hz.
+ intros z Hz. apply REC; [exact Hz | apply Hj; exact Hz].
- exact I.
Qed.
Lemma gtree_ibind {A B} : forall (G : astate -> kreq -> Prop) (t : itree astate A) (f : A -> itree astate B),
gtree G t ->
(forall tr a, cpath t tr a -> gtree G (f a)) ->
gtree G (ibind t f).
Proof.
intros G t; induction t as [a' | q s k IH | e]; intros f Hg Hf; cbn in *.
- apply (Hf []). reflexivity.
- assert (REC : forall z, canswer q z -> gtree G (k z) -> gtree G (ibind (k z) f)).
{ intros z Hc Hz. apply IH; [exact Hz|]. intros tr a Hp. apply (Hf ((q, z) :: tr)). cbn. auto. }
destruct q; cbn in REC, Hg |- *;
try (destruct Hg as (G0 & H0 & H1); split; [exact G0 | split; apply REC; auto]; fail);
try (apply REC; [reflexivity | exact Hg]; fail).
intros z Hz. apply REC; [exact Hz | apply Hg; exact Hz].
- exact I.
Qed.
Lemma jinv_mbind {A B} : forall (K : B * astate -> TSet) (m : M A) (f : A -> M B) (s : astate),
jinv (fun r => tset (f (fst r) (snd r)) K) (m s) ->
(forall tr a s', cpath (m s) tr (a, s') -> jinv K (f a s')) ->
jinv K (bind m f s).
Proof.
intros K m f s Hj Hf. unfold bind. apply jinv_ibind.
- clear Hf. revert Hj. generalize (m s). intros t.
induction t as [[a s'] | q s0 k IH | e]; intros Hj; cbn in *; try exact I.
destruct q; cbn in *; try (destruct Hj as [H0 H1]; split; apply IH; assumption); try (apply IH; exact Hj).
destruct Hj as [Heq Hj]. split; [| intros z Hz; apply IH; apply Hj; exact Hz].
intros z Hz. eapply t_eq_trans; [| eapply t_eq_trans; [apply (Heq z Hz)|]];
apply tset_congr; intros [a s']; apply t_eq_refl.
- intros tr [a s'] H. apply (Hf tr). exact H.
Qed.
Lemma gtree_mbind {A B} : forall (G : astate -> kreq -> Prop) (m : M A) (f : A -> M B) (s : astate),
gtree G (m s) -> (forall tr a s', cpath (m s) tr (a, s') -> gtree G (f a s')) -> gtree G (bind m f s).
Proof.
intros G m f s Hg Hf. unfold bind. apply gtree_ibind; [exact Hg|]. intros tr [a s'] H. apply (Hf tr). exact H.
Qed.
End d.

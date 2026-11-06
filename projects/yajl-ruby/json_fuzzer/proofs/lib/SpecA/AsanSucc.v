(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Definition agrant (e : aev) (a : aans) : Prop :=
  match a with AnsOk _ => True | AnsErr _ => False end.

Fixpoint gall {R} (G : R -> Prop) (t : stree aev aans (astate * aout R)) : Prop :=
  match t with
  | SRet (_, o) => match o with ONorm r => G r | OSpin => False | OUndef _ => True end
  | SVis e k => forall a, agrant e a -> gall G (k a)
  end.

Definition gok {R} (m : AM R) (G : R -> Prop) : Prop := forall s, gall G (m s).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gall_mono : forall {R} (G G' : R -> Prop) t, gall G t -> (forall r, G r -> G' r) -> gall G' t.
Proof.
  intros R G G' t; induction t as [[s o]|e k IH]; cbn; intros H HG; [destruct o; auto| intros a Ha; apply (IH a); auto].
Qed.

Lemma gall_sbind : forall {R S} (G : S -> Prop) (t : stree aev aans (astate * aout R)) (f : astate * aout R -> stree aev aans (astate * aout S)),
  gall (fun _ => True) t ->
  (forall s r, gall G (f (s, ONorm r))) -> (forall s w, gall G (f (s, OUndef w))) ->
  gall G (sbind t f).
Proof.
  intros R S G t; induction t as [[s o]|e k IH]; cbn; intros f Ht Hn Hu.
  - destruct o as [r| |w]; [apply Hn| destruct Ht| apply Hu].
  - intros a Ha. apply IH; auto.
Qed.

Lemma gok_ret : forall {R} (G : R -> Prop) r, G r -> gok (aret r) G.
Proof. intros R G r Hr s. cbn. exact Hr. Qed.
Lemma gok_undef : forall {R} (G : R -> Prop) w, gok (@aundef_ R w) G.
Proof. intros R G w s. cbn. exact I. Qed.
Lemma gok_upd : forall f, gok (aupd f) (fun _ => True).
Proof. intros f s. cbn. exact I. Qed.
Lemma gok_get : gok aget (fun _ => True).
Proof. intros s. cbn. exact I. Qed.
Lemma gok_check : forall b tag, gok (acheck b tag) (fun _ => True).
Proof. intros b tag s. unfold acheck. destruct b; cbn; exact I. Qed.
Lemma gok_mono : forall {R} (m : AM R) (G G' : R -> Prop), gok m G -> (forall r, G r -> G' r) -> gok m G'.
Proof. intros R m G G' H HG s. eapply gall_mono; [apply H| exact HG]. Qed.
Lemma gok_true : forall {R} (m : AM R) (G : R -> Prop), gok m G -> gok m (fun _ => True).
Proof. intros R m G H. eapply gok_mono; [exact H| auto]. Qed.

Lemma gok_bind : forall {R S} (m : AM R) (f : R -> AM S) (G1 : R -> Prop) (G2 : S -> Prop),
  gok m G1 -> (forall r, G1 r -> gok (f r) G2) -> gok (abind m f) G2.
Proof.
  intros R S m f G1 G2 Hm Hf s. unfold abind.
  assert (K : forall t : stree aev aans (astate * aout R), gall G1 t ->
             gall G2 (sbind t (fun p => match snd p with ONorm r => f r (fst p) | OSpin => SRet (fst p, OSpin) | OUndef w => SRet (fst p, OUndef w) end))).
  { induction t as [[s0 o]|e k IH]; cbn; intros Ht.
    - destruct o as [r| |w]; cbn; [apply Hf; exact Ht| destruct Ht| exact I].
    - intros a Ha. apply IH. auto. }
  apply K. apply Hm.
Qed.
Lemma gok_seq : forall {R S} (m : AM R) (k : AM S) (G1 : R -> Prop) (G2 : S -> Prop),
  gok m G1 -> gok k G2 -> gok (abind m (fun _ => k)) G2.
Proof. intros R S m k G1 G2 Hm Hk. eapply gok_bind; [exact Hm| intros; exact Hk]. Qed.

(* [comment removed for export] *)
Lemma gok_get_bind : forall {S} (f : astate -> AM S) (G : S -> Prop), (forall s, gok (f s) G) -> gok (abind aget f) G.
Proof. intros S f G H. eapply gok_bind; [apply gok_get| intros r _; apply H]. Qed.

Lemma gok_if : forall {R} (b : bool) (m1 m2 : AM R) G, gok m1 G -> gok m2 G -> gok (if b then m1 else m2) G.
Proof. intros R b m1 m2 G H1 H2. destruct b; assumption. Qed.

Create HintDb gok.
Ltac gleaf := first [exact I | reflexivity | eexists; reflexivity].
Ltac gpost r Hr := cbn beta in Hr; lazymatch type of Hr with ex _ => destruct Hr as [? Hr]; try subst r | _ = _ => try subst r | _ => idtac end.
(* [comment removed for export] *)
Ltac gauto := repeat first
  [ progress (cbv beta iota delta [negb andb orb])
  | match goal with H : true = false |- _ => discriminate H | H : false = true |- _ => discriminate H end
  | apply gok_undef
  | apply gok_ret; gleaf
  | apply gok_upd
  | apply gok_check
  | solve [eauto 2 with gok]
  | match goal with |- gok (abind aget _) _ => apply gok_get_bind; intros ? end
  | match goal with |- gok (abind _ (fun _ => _)) _ => eapply (gok_seq _ _ (fun _ => True)); [solve [gauto]|] end
  | match goal with |- gok (abind _ _) _ => eapply gok_bind; [solve [apply gok_get | eauto 2 with gok]| let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; gpost r Hr] end
  | match goal with |- gok (abind _ _) _ => eapply (gok_bind _ _ (fun _ => True)); [solve [gauto]| intros ? _] end
  | match goal with |- gok (if ?b then _ else _) _ => first [is_var b; destruct b | destruct b eqn:? | apply gok_if] end
  | match goal with |- gok (match ?x with _ => _ end) _ => first [is_var x; destruct x | destruct x eqn:?] end
  | match goal with |- gok (let '(_, _) := ?x in _) _ => destruct x eqn:? end ].

(* [comment removed for export] *)
(* [comment removed for export] *)

Section OPS.
Variable E : aenv.

Lemma gok_call : forall e, gok (acall e) (fun a => agrant e a).
Proof. intros e s. cbn. intros a Ha. exact Ha. Qed.

Lemma gok_mmap_fixed : forall addr len, gok (call_mmap_fixed addr len) (fun b => b = true).
Proof.
  intros addr len. unfold call_mmap_fixed. eapply gok_bind; [apply gok_call|].
  intros [r|e] Ha; [| destruct Ha]. destruct (r =? addr); [apply gok_ret; reflexivity| apply gok_undef].
Qed.
Lemma gok_mmap_anon : forall len, gok (call_mmap_anon E len) (fun r => exists a, r = Some a).
Proof.
  intros len. unfold call_mmap_anon. apply gok_get_bind. intros s0. eapply gok_bind; [apply gok_call|].
  intros [r|e] Ha; [| destruct Ha]. repeat (apply gok_if; [| apply gok_undef]). apply gok_ret. exists r; reflexivity.
Qed.
Lemma gok_mmap_ordie : forall len fl, gok (call_mmap_ordie E len fl) (fun _ => True).
Proof.
  intros len fl. unfold call_mmap_ordie. apply gok_get_bind. intros s0. eapply gok_bind; [apply gok_call|].
  intros [r|e] Ha; [| destruct Ha]. repeat (apply gok_if; [| apply gok_undef]). apply gok_ret. exact I.
Qed.
Lemma gok_munmap : forall addr len, gok (call_munmap addr len) (fun _ => True).
Proof.
  intros addr len. unfold call_munmap. eapply gok_bind; [apply gok_call|].
  intros [r|e] Ha; [| destruct Ha]. destruct (r =? 0); [apply gok_ret; exact I| apply gok_undef].
Qed.
Hint Resolve gok_mmap_fixed gok_mmap_anon gok_mmap_ordie gok_munmap : gok.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gok_store_alloc_once : forall count, gok (store_alloc_once E count) (fun _ => True).
Proof. intros count. unfold store_alloc_once. gauto. Qed.
Hint Resolve gok_store_alloc_once : gok.
Lemma gok_store_alloc : forall count, gok (store_alloc E count) (fun _ => True).
Proof. intros count. unfold store_alloc. gauto. Qed.
Hint Resolve gok_store_alloc : gok.
Lemma gok_depot_put : forall key, gok (depot_put E key) (fun _ => True).
Proof. intros key. unfold depot_put. gauto. Qed.
Hint Resolve gok_depot_put : gok.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gok_ensure_free_array_space : forall c nf, gok (ensure_free_array_space E c nf) (fun b => b = true).
Proof. intros c nf. unfold ensure_free_array_space. gauto. Qed.
Hint Resolve gok_ensure_free_array_space : gok.
Lemma gok_populate_free_array : forall c rq, gok (populate_free_array E c rq) (fun b => b = true).
Proof.
  intros c rq. unfold populate_free_array. apply gok_get_bind. intros s0.
  eapply gok_bind with (G1 := fun b => b = true); [gauto|]. intros ok1 ->. gauto.
Qed.
Hint Resolve gok_populate_free_array : gok.
Lemma gok_get_from_allocator : forall c n, gok (get_from_allocator E c n) (fun r => exists l, r = Some l).
Proof.
  intros c n. unfold get_from_allocator. apply gok_get_bind. intros s0.
  eapply gok_bind with (G1 := fun b => b = true); [gauto|]. intros ok ->. gauto.
Qed.
Hint Resolve gok_get_from_allocator : gok.
Lemma gok_refill : forall c, gok (refill E c) (fun b => b = true).
Proof. intros c. unfold refill, init_cache. gauto. Qed.
Hint Resolve gok_refill : gok.
Lemma gok_cache_pop : forall c, gok (cache_pop E c) (fun r => exists a, r = Some a).
Proof.
  intros c. unfold cache_pop. apply gok_get_bind. intros s0.
  eapply gok_bind with (G1 := fun b => b = true); [gauto|]. intros ok ->. gauto.
Qed.
Hint Resolve gok_cache_pop : gok.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gok_sec_alloc : forall nd, gok (sec_alloc E nd) (fun r => exists a, r = Some a).
Proof. intros nd. unfold sec_alloc. gauto. Qed.
Hint Resolve gok_sec_alloc : gok.
Lemma gok_poison_zero : forall u L, gok (poison_zero u L) (fun _ => True).
Proof. intros u L. unfold poison_zero. apply gok_ret. exact I. Qed.
Hint Resolve gok_poison_zero : gok.

Theorem gok_amalloc_core : forall key n, gok (amalloc_core E key n) (fun r => exists p, r = Some p).
Proof.
  intros key n. unfold amalloc_core. eapply gok_seq; [apply gok_check|]. eapply gok_seq; [apply gok_upd|].
  eapply gok_bind with (G1 := fun r => exists a, r = Some a); [gauto|]. intros ab (a & ->). gauto.
Qed.
Hint Resolve gok_amalloc_core : gok.
Theorem gok_amalloc : forall key n, gok (amalloc E key n) (fun r => exists p, r = Some p).
Proof. intros key n. unfold amalloc. apply gok_amalloc_core. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gok_return_to_allocator : forall c chunks, gok (return_to_allocator E c chunks) (fun _ => True).
Proof. intros c chunks. unfold return_to_allocator. gauto. Qed.
Hint Resolve gok_return_to_allocator : gok.
Lemma gok_local_dealloc : forall c p, gok (local_dealloc E c p) (fun _ => True).
Proof. intros c p. unfold local_dealloc, init_cache. gauto. Qed.
Hint Resolve gok_local_dealloc : gok.
Lemma gok_large_dealloc : forall p, gok (large_dealloc p) (fun _ => True).
Proof. intros p. unfold large_dealloc. gauto. Qed.
Hint Resolve gok_large_dealloc : gok.
Lemma gok_qcb_recycle : forall m, gok (qcb_recycle E m) (fun _ => True).
Proof. intros m. unfold qcb_recycle. gauto. Qed.
Hint Resolve gok_qcb_recycle : gok.
Lemma gok_recycle_items : forall items, gok (recycle_items E items) (fun _ => True).
Proof. induction items as [|x rest IH]; cbn; gauto. Qed.
Hint Resolve gok_recycle_items : gok.
Lemma gok_do_recycle : forall bs, gok (do_recycle E bs) (fun _ => True).
Proof. induction bs as [|b rest IH]; cbn; gauto. Qed.
Hint Resolve gok_do_recycle : gok.
Lemma gok_recycle : gok (recycle E) (fun _ => True).
Proof. unfold recycle. gauto. Qed.
Hint Resolve gok_recycle : gok.
Lemma gok_drain_if_needed : gok (drain_if_needed E) (fun _ => True).
Proof. unfold drain_if_needed. gauto. Qed.
Hint Resolve gok_drain_if_needed : gok.
(* [comment removed for export] *)
Theorem gok_arealloc_null : forall key n, gok (arealloc E key 0 n) (fun r => exists q, r = Some q).
Proof. intros key n. unfold arealloc, ia_init. eapply gok_seq; [apply gok_upd|]. cbn [Z.eqb]. apply gok_amalloc_core. Qed.

End OPS.
End RC__1.

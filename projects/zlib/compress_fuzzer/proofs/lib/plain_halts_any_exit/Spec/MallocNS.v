(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ev_okR (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap _ _ _ flags => Z.land flags MAP_FIXED = 0 -> is_err z = false
  | EMprotect _ _ _ => z = 0
  | EUndef _ => False
  | _ => True
  end.

Inductive rpath {R : Type} : M R -> R -> Prop :=
| rp_ret (r : R) : rpath (ret r) r
| rp_vis (e : ev) (k : Z -> M R) (z : Z) (r : R) : ev_okR e z -> rpath (k z) r -> rpath (SVis e k) r.

Definition NS {R : Type} (P : R -> Prop) (t : M R) : Prop := forall r, rpath t r -> P r.

Lemma NS_ret : forall {R} (P : R -> Prop) r, P r -> NS P (ret r).
Proof. intros R P r HP r' Hp. inversion Hp; subst. exact HP. Qed.

Lemma NS_vis : forall {R} (P : R -> Prop) e (k : Z -> M R), (forall z, ev_okR e z -> NS P (k z)) -> NS P (SVis e k).
Proof. intros R P e k Hk r Hp. inversion Hp; subst. eapply Hk; eassumption. Qed.

Lemma NS_undef : forall {R} (P : R -> Prop) u (k : Z -> M R), NS P (SVis (EUndef u) k).
Proof. intros R P u k r Hp. inversion Hp; subst. cbn in *. contradiction. Qed.

Lemma NS_bad_answer : forall {R} (P : R -> Prop) (bail : M R), NS P (bad_answer bail).
Proof. intros. unfold bad_answer. apply NS_undef. Qed.

Lemma NS_guard : forall {R} (P : R -> Prop) tag c (k bail : M R), (c = true -> NS P k) -> NS P (guard tag c k bail).
Proof. intros R P tag c k bail Hk. unfold guard. destruct c; [apply Hk; reflexivity | apply NS_undef]. Qed.

Lemma NS_sbind : forall {A R} (Q : A -> Prop) (P : R -> Prop) (t : M A) (f : A -> M R),
  NS Q t -> (forall a, Q a -> NS P (f a)) -> NS P (sbind t f).
Proof.
  intros A R Q P t. induction t as [a|e k IH]; intros f Ht Hf.
  - rewrite sbind_ret_l. apply Hf. apply Ht. constructor.
  - rewrite sbind_vis. apply NS_vis. intros z Hz. apply IH; [| exact Hf]. intros a Ha. apply Ht. econstructor; eassumption.
Qed.

Lemma NS_if : forall {R} (P : R -> Prop) (c : bool) (t1 t2 : M R), (c = true -> NS P t1) -> (c = false -> NS P t2) -> NS P (if c then t1 else t2).
Proof. intros R P c t1 t2 H1 H2. destruct c; [apply H1 | apply H2]; reflexivity. Qed.

Ltac ns_leaf K :=
  cbv zeta;
  repeat first
    [ apply NS_undef
    | apply NS_bad_answer
    | apply K
    | match goal with
      | |- NS _ (guard _ _ _ _) => apply NS_guard; intros _
      | |- NS _ (if ?c then _ else _) => apply NS_if; intros ?
      | |- NS _ (match ?x with _ => _ end) => destruct x eqn:?
      | |- NS _ (let '(_, _) := ?x in _) => destruct x eqn:?
      end ].

Ltac ns_dead :=
  exfalso;
  match goal with
  | Hz : Z.land _ MAP_FIXED = 0 -> is_err ?z = false, H : is_err ?z = true |- _ => rewrite (Hz eq_refl) in H; discriminate H
  | H : _ || _ = false |- _ => cbn in H; discriminate H
  | H : (?i <? 0) = true, Hi : 0 <= ?i |- _ => apply Z.ltb_lt in H; lia
  end.

Section K.
  Context {R : Type}.
  Variable P : R -> Prop.

  Lemma NS_queue : forall h m st (k : mstate -> M R) bail, (forall st', NS P (k st')) -> NS P (queue h m st k bail).
  Proof. intros h m st k bail Hk. unfold queue. ns_leaf Hk. Qed.

  Lemma NS_free_meta : forall m st (k : mstate -> M R) bail, (forall st', NS P (k st')) -> NS P (free_meta m st k bail).
  Proof. intros m st k bail Hk. unfold free_meta. apply NS_queue. exact Hk. Qed.

  Lemma NS_activate_group : forall m st (k : mstate -> Z -> M R) bail, (forall st' v, NS P (k st' v)) -> NS P (activate_group m st k bail).
  Proof. intros m st k bail Hk. unfold activate_group. ns_leaf Hk. Qed.

  Lemma NS_am_take : forall st (k : mstate -> optr -> M R) bail, (forall st' m, NS P (k st' (Some m))) -> NS P (am_take st k bail).
  Proof. intros st k bail Hk. unfold am_take. ns_leaf Hk. Qed.

  Lemma NS_am_carve : forall st p (k : mstate -> optr -> M R) bail, (forall st' m, NS P (k st' (Some m))) -> NS P (am_carve st p k bail).
  Proof. intros st p k bail Hk. unfold am_carve. cbv zeta. apply NS_am_take. exact Hk. Qed.

  Lemma NS_am_finish : forall st nu (k : mstate -> optr -> M R) bail, (forall st' m, NS P (k st' (Some m))) -> NS P (am_finish st nu k bail).
  Proof.
    intros st nu k bail Hk. unfold am_finish. ns_leaf Hk.

    apply NS_vis. intros z Hz. cbn in Hz. subst z. ns_leaf Hk.
    all: try (apply NS_am_carve; exact Hk).
    all: exfalso; match goal with H : _ || _ = false |- _ => cbn in H; discriminate H | _ => idtac end.
  Qed.

  Lemma NS_am_after_brk : forall st nu (k : mstate -> optr -> M R) bail, (forall st' m, NS P (k st' (Some m))) -> NS P (am_after_brk st nu k bail).
  Proof.
    intros st nu k bail Hk. unfold am_after_brk. ns_leaf Hk.
    - apply NS_vis. intros z Hz. cbn [ev_okR] in Hz. ns_leaf Hk.
      all: try (apply NS_am_finish; exact Hk).
      all: ns_dead.
    - apply NS_am_finish. exact Hk.
  Qed.

  Lemma NS_alloc_meta : forall st (k : mstate -> optr -> M R) bail, (forall st' m, NS P (k st' (Some m))) -> NS P (alloc_meta st k bail).
  Proof.
    intros st k bail Hk. unfold alloc_meta. ns_leaf Hk.
    all: try (apply NS_am_take; exact Hk).
    all: try (apply NS_am_after_brk; exact Hk).

    all: repeat (apply NS_vis; intros ? ?; ns_leaf Hk; try (apply NS_am_after_brk; exact Hk); try (apply NS_am_take; exact Hk)).
  Qed.

  Lemma NS_try_avail : forall sc st (k : mstate -> Z -> M R) bail, (forall st' v, NS P (k st' v)) -> NS P (try_avail sc st k bail).
  Proof.
    intros sc st k bail Hk. unfold try_avail, ta_fin. ns_leaf Hk.
    all: try (apply NS_activate_group; intros st' v; ns_leaf Hk).
  Qed.

  Lemma NS_ag_tail : forall lay st sc m p cnt ai (k : mstate -> optr -> M R), (forall st' g, NS P (k st' (Some g))) -> NS P (ag_tail lay st sc m p cnt ai k).
  Proof. intros lay st sc m p cnt ai k Hk. unfold ag_tail. cbv zeta. apply Hk. Qed.

  Lemma NS_alloc_group : forall lay (aslot : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req (k : mstate -> optr -> M R) bail,
    (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1, (forall st' idx, 0 <= idx -> NS P (k1 st' idx)) -> NS P (aslot st1 sc1 req1 k1 bail1)) ->
    (forall st' g, NS P (k st' (Some g))) ->
    NS P (alloc_group R lay aslot st sc req k bail).
  Proof.
    intros lay aslot st sc req k bail Haslot Hk. unfold alloc_group. cbv zeta.
    apply NS_alloc_meta. intros st1 m. ns_leaf Hk.

    all: try (apply NS_vis; intros zz Hzz; cbn [ev_okR] in Hzz; ns_leaf Hk).
    all: try (apply Haslot; intros st' idx Hidx; ns_leaf Hk).
    all: try (apply NS_ag_tail; exact Hk).
    all: try (apply NS_free_meta; intros st''; ns_leaf Hk).
    all: try ns_dead.
  Qed.

  Lemma ctz32_nonneg : forall x, 0 <= ctz32 x.
  Proof. intros x. unfold ctz32. apply Z.log2_nonneg. Qed.

  Lemma NS_alloc_slot : forall lay f st sc req (k : mstate -> Z -> M R) bail,
    (forall st' idx, 0 <= idx -> NS P (k st' idx)) -> NS P (alloc_slot lay f st sc req k bail).
  Proof.
    intros lay f. induction f as [|f IH]; intros st sc req k bail Hk.
    - cbn [alloc_slot]. apply NS_undef.
    - cbn [alloc_slot]. apply NS_try_avail. intros st1 first. ns_leaf Hk.
      + apply ctz32_nonneg.
      + apply (NS_alloc_group lay (alloc_slot lay f)); [intros; apply IH; assumption|].
        intros st2 g. cbv beta. apply NS_queue. intros st4. apply Hk. lia.
  Qed.

  Lemma NS_malloc_small_ctrl : forall lay st n (k : mstate -> option (aptr * Z) -> M R) bail,
    (forall st' g idx, NS P (k st' (Some (g, idx)))) -> NS P (malloc_small_ctrl lay st n k bail).
  Proof.
    intros lay st n k bail Hk. unfold malloc_small_ctrl. ns_leaf Hk.
    all: try (apply NS_alloc_slot; intros st' idx Hidx; ns_leaf Hk; ns_dead).
  Qed.

End K.

Lemma NS_malloc_core : forall lay st n, size_overflows n = false ->
  NS (fun r => snd r <> None) (malloc_core lay st n).
Proof.
  intros lay st n Hov. unfold malloc_core. rewrite Hov. cbv beta iota zeta.
  assert (K : forall st' g idx, NS (fun r : mstate * option (aptr * Z) => snd r <> None) (ret (st', Some (g, idx)))).
  { intros. apply NS_ret. cbn. discriminate. }
  ns_leaf K.

  all: try (apply NS_malloc_small_ctrl; exact K).
  all: try (apply NS_vis; intros zz Hzz; cbn [ev_okR] in Hzz; ns_leaf K).
  all: try (apply NS_alloc_meta; intros st3 g; ns_leaf K).
  all: try ns_dead.
Qed.

Theorem cmalloc_someR : forall cs n, size_overflows n = false -> NS (fun r => snd r <> None) (cmalloc cs n).
Proof.
  intros cs n Hov. unfold cmalloc.
  eapply NS_sbind; [apply (NS_malloc_core lay_none cs n Hov)|].
  intros [st1 r] Hr. cbn in Hr. apply NS_ret. cbn. destruct r as [[g idx]|]; [discriminate | exfalso; apply Hr; reflexivity].
Qed.

Corollary cmalloc_rpath_some : forall cs n cs' r, size_overflows n = false -> rpath (cmalloc cs n) (cs', r) -> exists c, r = Some c.
Proof.
  intros cs n cs' r Hov Hp. pose proof (cmalloc_someR cs n Hov (cs', r) Hp) as H. cbn in H. destruct r as [c|]; [exists c; reflexivity | exfalso; apply H; reflexivity].
Qed.


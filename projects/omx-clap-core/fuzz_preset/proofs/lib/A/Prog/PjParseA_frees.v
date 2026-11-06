(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_parse_frees.v, with only its comments or blank lines changed. *)
(* Theorem Labs, 2026-10: fuzz_preset pj_parse, image A' (RELOCATED unchanged from a Theorem Labs lane's image-B' batch-kit rebind
   5134b312d551 lib/B/Prog/pj_parse_frees.v; image-free): pj_free's order list under a grant oracle ok is
   the all-granted one when the reading under ok made the all-granted reading's result and trace. Proves no function
   (kind: pure model lemma).

   pjf_frees_same: PresetReqAt.pj_frees sm ok x = PresetReqAt.pj_frees sm [] x when jr_value sm 0 x ok has the result
   and trace of jr_value sm 0 x []. Route:
   - pjf_upto_fuel generalises PresetFreeFo.acc_fuel from an accepted run to any run whose all-granted calls ok grants
     (PjGrammar.ok_upto ok (calls tr0), tr0 the all-granted trace): jfv / jfl read ok only through grow, jr_name and
     jrv, and each of those then gives what it gives under [] with ok advanced past its calls (PjGrammar.agrees).
   - pjf_nil_nofail: a reading under [] has no EFail in its trace (every jalloc / jrealloc is granted under []).
   - when ok refuses one of the all-granted calls, PjGrammar.agrees' second clause ends the trace under ok with an
     EFail; that trace is the all-granted one, which has none. So that case cannot happen. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PresetReqAt.
Import ListNotations.

(* ================================================================ a reading under [] has no EFail *)

Definition pjf_nf {A : Type} (m : M A) : Prop :=
  snd (m []) = [] /\ (forall n, ~ In (EFail n) (snd (fst (m [])))).

Ltac pjf_noin := let n := fresh "n" in let Hin := fresh "Hin" in
  intros n Hin;
  cbv beta iota zeta delta [jret jrefuse jfree jalloc jrealloc take fst snd In] in Hin;
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
  first [discriminate | contradiction].

Lemma pjf_nf_ret : forall A (a : A), pjf_nf (jret a).
Proof. intros A a. split; [reflexivity|pjf_noin]. Qed.

Lemma pjf_nf_refuse : forall A, pjf_nf (@jrefuse A).
Proof. intros A. split; [reflexivity|pjf_noin]. Qed.

Lemma pjf_nf_free : forall n, pjf_nf (jfree n).
Proof. intros n. split; [reflexivity|pjf_noin]. Qed.

Lemma pjf_nf_alloc : forall n, pjf_nf (jalloc n).
Proof. intros n. split; [reflexivity|pjf_noin]. Qed.

Lemma pjf_nf_realloc : forall m n, pjf_nf (jrealloc m n).
Proof. intros m n. split; [reflexivity|pjf_noin]. Qed.

Lemma pjf_nf_bind : forall A B (m : M A) (k : A -> M B),
  pjf_nf m -> (forall a, pjf_nf (k a)) -> pjf_nf (jbind m k).
Proof.
  intros A B m k Hm Hk. unfold pjf_nf in Hm, Hk |- *. unfold jbind.
  destruct (m []) as [[r t] o] eqn:E. destruct Hm as [Hm1 Hm2]. cbn [fst snd] in Hm1, Hm2. subst o.
  destruct r as [a|]; cbv beta iota.
  - destruct (Hk a) as [Hk1 Hk2]. destruct (k a []) as [[r1 t1] o1] eqn:E1.
    cbn [fst snd] in Hk1, Hk2 |- *. split; [exact Hk1|].
    intros n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (Hm2 n Hin)|exact (Hk2 n Hin)].
  - cbn [fst snd]. split; [reflexivity|exact Hm2].
Qed.

Ltac pjf_t := repeat (cbv beta iota zeta; match goal with
  | |- pjf_nf (jbind _ _) => apply pjf_nf_bind
  | |- forall p : (_ * _), _ => intros [? ?]
  | |- forall _, _ => intros ?
  | |- pjf_nf (jret _) => apply pjf_nf_ret
  | |- pjf_nf jrefuse => apply pjf_nf_refuse
  | |- pjf_nf (jalloc _) => apply pjf_nf_alloc
  | |- pjf_nf (jrealloc _ _) => apply pjf_nf_realloc
  | |- pjf_nf (jfree _) => apply pjf_nf_free
  | |- pjf_nf (jr_cont _ _ _ _) => unfold jr_cont
  | H : forall d x, pjf_nf (jrv _ _ d x) |- pjf_nf (jrv _ _ _ _) => apply H
  | H : forall d o n cap acc y, pjf_nf (jrl _ _ d o n cap acc y) |- pjf_nf (jrl _ _ _ _ _ _ _ _) => apply H
  | H : forall z, pjf_nf (jr_string z) |- pjf_nf (jr_string _) => apply H
  | |- pjf_nf (match ?t with _ => _ end) => destruct t
  end).

Lemma pjf_nf_jr_string : forall z, pjf_nf (jr_string z).
Proof. intros z. unfold jr_string. pjf_t. Qed.

Lemma pjf_nf_grow : forall o n cap, pjf_nf (grow o n cap).
Proof. intros o n cap. unfold grow. pjf_t. Qed.

Lemma pjf_nf_jr_name : forall o y, pjf_nf (jr_name o y).
Proof. pose proof pjf_nf_jr_string. intros o y. unfold jr_name. pjf_t. Qed.

Lemma pjf_nf_lit : forall w v x, pjf_nf (lit w v x).
Proof. intros w v x. unfold lit. pjf_t. Qed.

Lemma pjf_nf_jr_number : forall sm x, pjf_nf (jr_number sm x).
Proof. intros sm x. unfold jr_number. pjf_t. Qed.

Lemma pjf_nf_fuel : forall sm f,
  (forall d x, pjf_nf (jrv sm f d x)) /\ (forall d o n cap acc y, pjf_nf (jrl sm f d o n cap acc y)).
Proof.
  intros sm f. pose proof pjf_nf_jr_string as HS.
  induction f as [|f [IHv IHl]].
  - split; intros; apply pjf_nf_refuse.
  - split.
    + intros d x. cbn [jrv]. pjf_t; first [apply pjf_nf_lit | apply pjf_nf_jr_number].
    + intros d o n cap acc y. cbn [jrl]. pjf_t; first [apply pjf_nf_grow | apply pjf_nf_jr_name].
Qed.

Lemma pjf_nil_nofail_fuel : forall sm f d x n, ~ In (EFail n) (snd (fst (jrv sm f d x []))).
Proof.
  intros sm f d x n. pose proof (proj1 (pjf_nf_fuel sm f) d x) as H. unfold pjf_nf in H.
  destruct H as [_ H]. exact (H n).
Qed.

Lemma pjf_nil_nofail : forall sm d x n, ~ In (EFail n) (snd (fst (jr_value sm d x []))).
Proof. intros sm d x n. unfold jr_value. exact (pjf_nil_nofail_fuel sm _ d x n). Qed.

(* ================================================================ jfv / jfl when ok grants the all-granted calls *)

Lemma pjf_upto_bind : forall A B (m : M A) (k : A -> M B) (ok : list bool) (r : option A) (t : list ev)
  (o : list bool),
  agrees m -> m [] = (r, t, o) -> ok_upto ok (calls (snd (fst (jbind m k [])))) ->
  o = [] /\ m ok = (r, t, skipn (calls t) ok) /\ ok_upto ok (calls t) /\
  (forall a, r = Some a -> ok_upto (skipn (calls t) ok) (calls (snd (fst (k a []))))).
Proof.
  intros A B m k ok r t o Hm E Hu.
  pose proof (agrees_nil A m Hm) as N. rewrite E in N. cbn [fst snd] in N. injection N as No. subst o.
  pose proof (proj1 (Hm ok)) as H1. rewrite E in H1. cbn [fst snd] in H1.
  unfold jbind in Hu. rewrite E in Hu.
  destruct r as [a|]; cbv beta iota in Hu.
  - destruct (k a []) as [[r1 t1] o1] eqn:Ek. cbn [fst snd] in Hu. rewrite calls_app in Hu.
    assert (Ht : ok_upto ok (calls t)) by (eapply ok_upto_le; [exact Hu|lia]).
    split; [reflexivity|]. split; [exact (H1 Ht)|]. split; [exact Ht|].
    intros a' Ha. injection Ha as <-. rewrite Ek. cbn [fst snd].
    exact (ok_upto_skipn ok (calls t) (calls t1) Hu).
  - cbn [fst snd] in Hu.
    split; [reflexivity|]. split; [exact (H1 Hu)|]. split; [exact Hu|].
    intros a' Ha. discriminate Ha.
Qed.

Lemma pjf_cont_upto : forall (loop : nat -> bool -> nat -> nat -> list (list Z * jv) -> list Z -> M (jv * list Z))
  (floop : nat -> bool -> nat -> nat -> list Z -> list Z -> list bool -> list Z) d o x ok,
  (forall d' o' n cap acc af y ok1, ok_upto ok1 (calls (snd (fst (loop d' o' n cap acc y [])))) ->
     floop d' o' n cap af y ok1 = floop d' o' n cap af y []) ->
  ok_upto ok (calls (snd (fst (jr_cont loop d o x [])))) -> jf_cont floop d o x ok = jf_cont floop d o x [].
Proof.
  intros loop floop d o x ok H Hu. unfold jr_cont in Hu. unfold jf_cont.
  revert Hu. destruct (Nat.ltb MAXD (S d)); intros Hu; cbv beta iota zeta in Hu |- *; [reflexivity|].
  revert Hu. destruct (skip (tl x)) as [|c r]; intros Hu; cbv beta iota zeta in Hu |- *.
  - exact (H _ _ _ _ _ _ _ _ Hu).
  - revert Hu. destruct (c =? closer o)%Z; intros Hu; cbv beta iota zeta in Hu |- *; [reflexivity|].
    exact (H _ _ _ _ _ _ _ _ Hu).
Qed.

(* jfv / jfl under ok are as under [] when ok grants every call of the all-granted reading *)
Lemma pjf_upto_fuel : forall sm f,
  (forall d x ok, ok_upto ok (calls (snd (fst (jrv sm f d x [])))) -> jfv sm f d x ok = jfv sm f d x []) /\
  (forall d o n cap acc af y ok, ok_upto ok (calls (snd (fst (jrl sm f d o n cap acc y [])))) ->
     jfl sm f d o n cap af y ok = jfl sm f d o n cap af y []).
Proof.
  intros sm f. induction f as [|f [IHv IHl]].
  - split; intros; reflexivity.
  - split.
    + intros d x ok Hu.
      pose proof (proj1 (proj1 (agrees_fuel sm (S f)) d x ok) Hu) as Ec.
      cbn [jfv]. cbn [jrv] in Hu. revert Hu.
      destruct (skip x) as [|b y]; intros Hu; cbv beta iota in Hu |- *; [reflexivity|].
      revert Hu. destruct (b =? 123)%Z; [|destruct (b =? 91)%Z]; intros Hu; cbv beta iota in Hu |- *.
      * exact (pjf_cont_upto (jrl sm f) (jfl sm f) d true (b :: y) ok IHl Hu).
      * exact (pjf_cont_upto (jrl sm f) (jfl sm f) d false (b :: y) ok IHl Hu).
      * rewrite Ec. reflexivity.
    + intros d o n cap acc af y ok Hu. cbn [jrl] in Hu. cbn [jfl].
      destruct (grow o n cap []) as [[rg tg] okg] eqn:E0.
      destruct (pjf_upto_bind _ _ _ _ ok rg tg okg (agrees_grow o n cap) E0 Hu) as (-> & Eg & _ & Kg).
      rewrite Eg. destruct rg as [cap1|]; cbv beta iota zeta; [|reflexivity].
      specialize (Kg cap1 eq_refl). cbv beta in Kg.
      destruct (jr_name o y []) as [[rn tn] okn] eqn:E1.
      destruct (pjf_upto_bind _ _ _ _ _ rn tn okn (agrees_jr_name o y) E1 Kg) as (-> & En & _ & Kn).
      rewrite En. destruct rn as [[nm y1]|]; cbv beta iota zeta; [|reflexivity].
      specialize (Kn (nm, y1) eq_refl). cbv beta iota in Kn.
      destruct (jrv sm f d y1 []) as [[rv tv] okv] eqn:E2.
      destruct (pjf_upto_bind _ _ _ _ _ rv tv okv (proj1 (agrees_fuel sm f) d y1) E2 Kn) as (-> & Ev & Huv & Kv).
      rewrite (IHv d y1 (skipn (calls tn) (skipn (calls tg) ok))) by (rewrite E2; exact Huv).
      rewrite Ev. destruct rv as [[v r]|]; cbv beta iota zeta; [|reflexivity].
      specialize (Kv (v, r) eq_refl). cbv beta iota in Kv.
      revert Kv. destruct (skip r) as [|c r1]; intros Kv; cbv beta iota zeta in Kv |- *; [reflexivity|].
      revert Kv. destruct (c =? 44)%Z; intros Kv; cbv beta iota zeta in Kv |- *; [|reflexivity].
      exact (IHl _ _ _ _ _ _ _ _ Kv).
Qed.

(* ================================================================ the lemma *)

(* When the reading under ok made exactly the all-granted reading's result and trace, pj_free's order list under ok
   is the all-granted one. *)
Lemma pjf_frees_same : forall (sm : list Z -> Z * Z) (x : list Z) (ok : list bool) res tr okr,
  PjGrammar.jr_value sm 0 x ok = (res, tr, okr) ->
  fst (PjGrammar.jr_value sm 0 x []) = (res, tr) ->
  PresetReqAt.pj_frees sm ok x = PresetReqAt.pj_frees sm [] x.
Proof.
  intros sm x ok res tr okr E1 E2. unfold pj_frees. unfold jr_value in E1, E2.
  destruct (ok_upto_dec ok (calls (snd (fst (jrv sm (S (2 * length x)) 0%nat x [])))))
    as [Hu|(j & Hj & Hf & Hu)].
  - exact (proj1 (pjf_upto_fuel sm (S (2 * length x))) 0%nat x ok Hu).
  - exfalso.
    destruct (proj2 (proj1 (agrees_fuel sm (S (2 * length x))) 0%nat x ok) j Hj Hf Hu)
      as (P & e & rest & Em & _ & _ & _).
    rewrite E1 in Em. injection Em as Hr Ht Hk.
    apply (pjf_nil_nofail_fuel sm (S (2 * length x)) 0%nat x (esize e)).
    rewrite E2. cbn [snd]. rewrite Ht. apply in_or_app. right. left. reflexivity.
Qed.

Print Assumptions pjf_nil_nofail.
Print Assumptions pjf_upto_fuel.
Print Assumptions pjf_frees_same.

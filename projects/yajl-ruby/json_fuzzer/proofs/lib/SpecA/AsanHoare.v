(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Fixpoint sall {Ev An R} (P : R -> Prop) (t : stree Ev An R) : Prop :=
  match t with
  | SRet r => P r
  | SVis _ k => forall a, sall P (k a)
  end.

Lemma sall_mono : forall {Ev An R} (P Q : R -> Prop) (t : stree Ev An R),
  sall P t -> (forall r, P r -> Q r) -> sall Q t.
Proof. intros Ev An R P Q t; induction t as [r|e k IH]; cbn; intros HP HPQ; [auto|]. intros a. apply (IH a); auto. Qed.

Lemma sall_sbind : forall {Ev An R S} (Q : S -> Prop) (t : stree Ev An R) (f : R -> stree Ev An S),
  sall (fun r => sall Q (f r)) t -> sall Q (sbind t f).
Proof. intros Ev An R S Q t; induction t as [r|e k IH]; cbn; intros f Hs; [auto|]. intros a. apply IH. auto. Qed.

Lemma sall_smap : forall {Ev An R S} (Q : S -> Prop) (t : stree Ev An R) (f : R -> S),
  sall (fun r => Q (f r)) t -> sall Q (smap f t).
Proof. intros. unfold smap. apply sall_sbind. eapply sall_mono; [exact H|]. intros r Hr; cbn; exact Hr. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition undef_ok (w : aundef) : Prop :=
  match w with UBadAnswer => True | UPlacement _ => True | _ => False end.

Definition leaf_ok {R} (Q : astate -> R -> Prop) (o : astate * aout R) : Prop :=
  match snd o with
  | ONorm r => Q (fst o) r
  | OSpin => True
  | OUndef w => undef_ok w
  end.

Definition hoare {R} (P : astate -> Prop) (m : AM R) (Q : astate -> R -> Prop) : Prop :=
  forall s, P s -> sall (leaf_ok Q) (m s).

Lemma hoare_conseq : forall {R} (P P' : astate -> Prop) (m : AM R) (Q Q' : astate -> R -> Prop),
  hoare P m Q -> (forall s, P' s -> P s) -> (forall s r, Q s r -> Q' s r) -> hoare P' m Q'.
Proof.
  intros R P P' m Q Q' H HP HQ s Hs. eapply sall_mono; [apply H, HP, Hs|].
  intros [s' [r| |w]]; cbn; auto.
Qed.

Lemma sall_conj : forall {Ev An R} (P Q : R -> Prop) (t : stree Ev An R),
  sall P t -> sall Q t -> sall (fun r => P r /\ Q r) t.
Proof. intros Ev An R P Q t; induction t as [r|e k IH]; cbn; intros HP HQ; [auto|]. intros a. apply IH; auto. Qed.

Lemma hoare_conj : forall {R} (P : astate -> Prop) (m : AM R) (Q1 Q2 : astate -> R -> Prop),
  hoare P m Q1 -> hoare P m Q2 -> hoare P m (fun s r => Q1 s r /\ Q2 s r).
Proof.
  intros R P m Q1 Q2 H1 H2 s Hs. pose proof (sall_conj _ _ _ (H1 s Hs) (H2 s Hs)) as H.
  eapply sall_mono; [exact H|]. intros [s' [r| |w]]; cbn; tauto.
Qed.

Lemma hoare_ret : forall {R} (P : astate -> Prop) (r : R) Q,
  (forall s, P s -> Q s r) -> hoare P (aret r) Q.
Proof. intros R P r Q H s Hs. cbn. auto. Qed.

Lemma hoare_bind : forall {R S} (P : astate -> Prop) (m : AM R) (f : R -> AM S) Q (Rr : astate -> S -> Prop),
  hoare P m Q -> (forall r, hoare (fun s => Q s r) (f r) Rr) -> hoare P (abind m f) Rr.
Proof.
  intros R S P m f Q Rr Hm Hf s Hs. unfold abind. apply sall_sbind.
  eapply sall_mono; [apply Hm, Hs|]. intros [s' [r| |w]] H; cbn in *.
  - apply Hf. exact H.
  - exact I.
  - exact H.
Qed.

Lemma hoare_get : forall (P : astate -> Prop) Q, (forall s, P s -> Q s s) -> hoare P aget Q.
Proof. intros P Q H s Hs; cbn; auto. Qed.
Lemma hoare_upd : forall (P : astate -> Prop) f Q, (forall s, P s -> Q (f s) tt) -> hoare P (aupd f) Q.
Proof. intros P f Q H s Hs; cbn; auto. Qed.
Lemma hoare_put : forall (P : astate -> Prop) s' Q, (forall s, P s -> Q s' tt) -> hoare P (aput s') Q.
Proof. intros P s' Q H s Hs; cbn. apply (H s Hs). Qed.
Lemma hoare_spin : forall {R} (P : astate -> Prop) (Q : astate -> R -> Prop), hoare P aspin Q.
Proof. intros R P Q s Hs; cbn; exact I. Qed.
Lemma hoare_undef : forall {R} (P : astate -> Prop) w (Q : astate -> R -> Prop), undef_ok w -> hoare P (aundef_ w) Q.
Proof. intros R P w Q Hw s Hs; cbn; exact Hw. Qed.
Lemma hoare_call : forall (P : astate -> Prop) e Q, (forall s a, P s -> Q s a) -> hoare P (acall e) Q.
Proof. intros P e Q H s Hs; cbn; auto. Qed.
Lemma hoare_check : forall (P : astate -> Prop) b tag Q,
  (forall s, P s -> b = true /\ Q s tt) -> hoare P (acheck b tag) Q.
Proof.
  intros P b tag Q H s Hs. destruct (H s Hs) as [Hb HQ]. unfold acheck. rewrite Hb. cbn. exact HQ.
Qed.
Lemma hoare_false : forall {R} (m : AM R) Q, hoare (fun _ => False) m Q.
Proof. intros R m Q s []. Qed.

(* [comment removed for export] *)
Lemma hoare_pre : forall {R} (P : astate -> Prop) (m : AM R) Q,
  (forall s, P s -> hoare (fun s' => s' = s) m Q) -> hoare P m Q.
Proof. intros R P m Q H s Hs. apply (H s Hs s eq_refl). Qed.

Lemma hoare_if : forall {R} (P : astate -> Prop) (b : bool) (m1 m2 : AM R) Q,
  (b = true -> hoare P m1 Q) -> (b = false -> hoare P m2 Q) -> hoare P (if b then m1 else m2) Q.
Proof. intros R P b m1 m2 Q H1 H2. destruct b; auto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hoare_get_bind : forall {S} (P : astate -> Prop) (f : astate -> AM S) Q,
  (forall s, P s -> hoare (fun s' => s' = s) (f s) Q) -> hoare P (abind aget f) Q.
Proof.
  intros S P f Q H. eapply hoare_bind with (Q := fun s r => P s /\ r = s).
  - apply hoare_get. auto.
  - intros r s [Hs ->]. apply (H s Hs s eq_refl).
Qed.

Lemma hoare_upd_bind : forall {S} (P : astate -> Prop) g (f : unit -> AM S) Q,
  hoare (fun s' => exists s, P s /\ s' = g s) (f tt) Q -> hoare P (abind (aupd g) f) Q.
Proof.
  intros S P g f Q H. eapply hoare_bind with (Q := fun s' r => exists s, P s /\ s' = g s).
  - apply hoare_upd. intros s Hs. exists s; auto.
  - intros []. exact H.
Qed.

(* [comment removed for export] *)
Definition preserves {R} (I : astate -> Prop) (m : AM R) : Prop := hoare I m (fun s _ => I s).

Lemma preserves_bind : forall {R S} I (m : AM R) (f : R -> AM S),
  preserves I m -> (forall r, preserves I (f r)) -> preserves I (abind m f).
Proof. intros R S I m f Hm Hf. eapply hoare_bind; [exact Hm|]. intros r. exact (Hf r). Qed.
Lemma preserves_ret : forall {R} I (r : R), preserves I (aret r).
Proof. intros; apply hoare_ret; auto. Qed.
Lemma preserves_get_bind : forall {S} I (f : astate -> AM S),
  (forall s, I s -> hoare (fun s' => s' = s) (f s) (fun s _ => I s)) -> preserves I (abind aget f).
Proof. intros S I f H. apply hoare_get_bind. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_okW {R} (Q : astate -> R -> Prop) (o : astate * aout R) : Prop :=
  match o with
  | (s', ONorm r) => Q s' r
  | _ => True
  end.

Definition hoareW {R} (P : astate -> Prop) (m : AM R) (Q : astate -> R -> Prop) : Prop :=
  forall s, P s -> sall (leaf_okW Q) (m s).

Lemma hoare_conjW : forall {R} (P : astate -> Prop) (m : AM R) (Q1 Q2 : astate -> R -> Prop),
  hoare P m Q1 -> hoareW P m Q2 -> hoare P m (fun s r => Q1 s r /\ Q2 s r).
Proof.
  intros R P m Q1 Q2 H1 H2 s Hs. pose proof (sall_conj _ _ _ (H1 s Hs) (H2 s Hs)) as H.
  eapply sall_mono; [exact H|]. intros [s' [r| |w]]; cbn; tauto.
Qed.

Lemma hoareW_of_hoare : forall {R} (P : astate -> Prop) (m : AM R) Q, hoare P m Q -> hoareW P m Q.
Proof. intros R P m Q H s Hs. eapply sall_mono; [exact (H s Hs)|]. intros [s' [r| |w]]; cbn; auto. Qed.

Lemma hoareW_conseq : forall {R} (P P' : astate -> Prop) (m : AM R) (Q Q' : astate -> R -> Prop),
  hoareW P m Q -> (forall s, P' s -> P s) -> (forall s r, Q s r -> Q' s r) -> hoareW P' m Q'.
Proof.
  intros R P P' m Q Q' H HP HQ s Hs. eapply sall_mono; [apply H, HP, Hs|]. intros [s' [r| |w]]; cbn; auto.
Qed.
Lemma hoareW_ret : forall {R} (P : astate -> Prop) (r : R) Q, (forall s, P s -> Q s r) -> hoareW P (aret r) Q.
Proof. intros R P r Q H s Hs. cbn. auto. Qed.
Lemma hoareW_bind : forall {R S} (P : astate -> Prop) (m : AM R) (f : R -> AM S) Q (Rr : astate -> S -> Prop),
  hoareW P m Q -> (forall r, hoareW (fun s => Q s r) (f r) Rr) -> hoareW P (abind m f) Rr.
Proof.
  intros R S P m f Q Rr Hm Hf s Hs. unfold abind. apply sall_sbind.
  eapply sall_mono; [apply Hm, Hs|]. intros [s' [r| |w]] H; cbn in *; [apply Hf; exact H| exact I| exact I].
Qed.
Lemma hoareW_get : forall (P : astate -> Prop) Q, (forall s, P s -> Q s s) -> hoareW P aget Q.
Proof. intros P Q H s Hs; cbn; auto. Qed.
Lemma hoareW_upd : forall (P : astate -> Prop) f Q, (forall s, P s -> Q (f s) tt) -> hoareW P (aupd f) Q.
Proof. intros P f Q H s Hs; cbn; auto. Qed.
Lemma hoareW_spin : forall {R} (P : astate -> Prop) (Q : astate -> R -> Prop), hoareW P aspin Q.
Proof. intros R P Q s Hs; cbn; exact I. Qed.
Lemma hoareW_undef : forall {R} (P : astate -> Prop) w (Q : astate -> R -> Prop), hoareW P (aundef_ w) Q.
Proof. intros R P w Q s Hs; cbn; exact I. Qed.
Lemma hoareW_call : forall (P : astate -> Prop) e Q, (forall s a, P s -> Q s a) -> hoareW P (acall e) Q.
Proof. intros P e Q H s Hs; cbn; auto. Qed.
Lemma hoareW_check : forall (P : astate -> Prop) b tag Q, (forall s, P s -> Q s tt) -> hoareW P (acheck b tag) Q.
Proof. intros P b tag Q H. unfold acheck. destruct b; [apply hoareW_ret; exact H| apply hoareW_undef]. Qed.
Lemma hoareW_pre : forall {R} (P : astate -> Prop) (m : AM R) Q,
  (forall s, P s -> hoareW (fun s' => s' = s) m Q) -> hoareW P m Q.
Proof. intros R P m Q H s Hs. apply (H s Hs s eq_refl). Qed.
Lemma hoareW_get_bind : forall {S} (P : astate -> Prop) (f : astate -> AM S) Q,
  (forall s, P s -> hoareW (fun s' => s' = s) (f s) Q) -> hoareW P (abind aget f) Q.
Proof.
  intros S P f Q H. eapply hoareW_bind with (Q := fun s r => P s /\ r = s).
  - apply hoareW_get. auto.
  - intros r s [Hs ->]. apply (H s Hs s eq_refl).
Qed.
Lemma hoareW_upd_bind : forall {S} (P : astate -> Prop) g (f : unit -> AM S) Q,
  hoareW (fun s' => exists s, P s /\ s' = g s) (f tt) Q -> hoareW P (abind (aupd g) f) Q.
Proof.
  intros S P g f Q H. eapply hoareW_bind with (Q := fun s' r => exists s, P s /\ s' = g s).
  - apply hoareW_upd. intros s Hs. exists s; auto.
  - intros []. exact H.
Qed.

(* [comment removed for export] *)
Definition monoW {X} (Rl : astate -> astate -> Prop) (m : AM X) : Prop :=
  forall s0, hoareW (fun s => s = s0) m (fun s' _ => Rl s0 s').

Lemma monoW_bind : forall {X Y} (Rl : astate -> astate -> Prop) (m : AM X) (f : X -> AM Y),
  (forall a b c, Rl a b -> Rl b c -> Rl a c) ->
  monoW Rl m -> (forall x, monoW Rl (f x)) -> monoW Rl (abind m f).
Proof.
  intros X Y Rl m f TR Hm Hf s0. eapply hoareW_bind; [apply Hm|]. intros x. apply hoareW_pre. intros s1 H01.
  eapply hoareW_conseq; [apply (Hf x s1)| auto| intros s r H; exact (TR _ _ _ H01 H)].
Qed.
Lemma monoW_ret : forall {X} (Rl : astate -> astate -> Prop) (x : X), (forall a, Rl a a) -> monoW Rl (aret x).
Proof. intros X Rl x RF s0. apply hoareW_ret. intros s ->. apply RF. Qed.
Lemma monoW_get : forall (Rl : astate -> astate -> Prop), (forall a, Rl a a) -> monoW Rl aget.
Proof. intros Rl RF s0. apply hoareW_get. intros s ->. apply RF. Qed.
Lemma monoW_call : forall (Rl : astate -> astate -> Prop) e, (forall a, Rl a a) -> monoW Rl (acall e).
Proof. intros Rl e RF s0. apply hoareW_call. intros s a ->. apply RF. Qed.
Lemma monoW_check : forall (Rl : astate -> astate -> Prop) b t, (forall a, Rl a a) -> monoW Rl (acheck b t).
Proof. intros Rl b t RF s0. apply hoareW_check. intros s ->. apply RF. Qed.
Lemma monoW_spin : forall {X} (Rl : astate -> astate -> Prop), monoW Rl (@aspin X).
Proof. intros X Rl s0. apply hoareW_spin. Qed.
Lemma monoW_undef : forall {X} (Rl : astate -> astate -> Prop) w, monoW Rl (@aundef_ X w).
Proof. intros X Rl w s0. apply hoareW_undef. Qed.
Lemma monoW_upd : forall (Rl : astate -> astate -> Prop) f, (forall s, Rl s (f s)) -> monoW Rl (aupd f).
Proof. intros Rl f H s0. apply hoareW_upd. intros s ->. apply H. Qed.
Lemma monoW_get_bind : forall {Y} (Rl : astate -> astate -> Prop) (f : astate -> AM Y),
  (forall s, monoW Rl (f s)) -> monoW Rl (abind aget f).
Proof. intros Y Rl f H s0. apply hoareW_get_bind. intros s ->. apply H. Qed.
Lemma monoW_if : forall {X} (Rl : astate -> astate -> Prop) (b : bool) (m1 m2 : AM X),
  monoW Rl m1 -> monoW Rl m2 -> monoW Rl (if b then m1 else m2).
Proof. intros X Rl b m1 m2 H1 H2. destruct b; auto. Qed.

End RC__1.
Ltac hw_step RF TR :=
  lazymatch goal with
  | |- monoW _ (abind aget _) => apply monoW_get_bind; intros
  | |- monoW _ (abind (aupd _) _) => apply monoW_bind; [exact TR| apply monoW_upd |intros]
  | |- monoW _ (abind _ _) => apply monoW_bind; [exact TR| |intros]
  | |- monoW _ (aret _) => apply monoW_ret; exact RF
  | |- monoW _ aget => apply monoW_get; exact RF
  | |- monoW _ (acall _) => apply monoW_call; exact RF
  | |- monoW _ (acheck _ _) => apply monoW_check; exact RF
  | |- monoW _ aspin => apply monoW_spin
  | |- monoW _ (aundef_ _) => apply monoW_undef
  | |- monoW _ (aupd _) => apply monoW_upd
  | |- monoW _ (if ?b then _ else _) => first [apply monoW_if | destruct b]
  | |- monoW _ (match ?x with _ => _ end) => destruct x
  end.
Ltac hw RF TR := repeat (hw_step RF TR).

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition presW {X} (I : astate -> Prop) (m : AM X) : Prop := hoareW I m (fun s _ => I s).

Lemma presW_bind : forall {X Y} I (m : AM X) (f : X -> AM Y),
  presW I m -> (forall x, presW I (f x)) -> presW I (abind m f).
Proof. intros X Y I m f Hm Hf. eapply hoareW_bind; [exact Hm|]. intros x. exact (Hf x). Qed.
Lemma presW_get_bind : forall {Y} I (f : astate -> AM Y),
  (forall s, I s -> presW I (f s)) -> presW I (abind aget f).
Proof.
  intros Y I f H. apply hoareW_get_bind. intros s Hs. eapply hoareW_conseq; [apply (H s Hs)| intros s' ->; exact Hs| auto].
Qed.
Lemma presW_ret : forall {X} I (x : X), presW I (aret x).
Proof. intros X I x. apply hoareW_ret. auto. Qed.
Lemma presW_get : forall I, hoareW I aget (fun s _ => I s).
Proof. intros I. apply hoareW_get. auto. Qed.
Lemma presW_call : forall I e, hoareW I (acall e) (fun s _ => I s).
Proof. intros I e. apply hoareW_call. auto. Qed.
Lemma presW_check : forall I b t, presW I (acheck b t).
Proof. intros I b t. apply hoareW_check. auto. Qed.
Lemma presW_spin : forall {X} I, presW I (@aspin X).
Proof. intros X I. apply hoareW_spin. Qed.
Lemma presW_undef : forall {X} I w, presW I (@aundef_ X w).
Proof. intros X I w. apply hoareW_undef. Qed.
Lemma presW_upd : forall I f, (forall s, I s -> I (f s)) -> presW I (aupd f).
Proof. intros I f H. apply hoareW_upd. exact H. Qed.
Lemma presW_if : forall {X} I (b : bool) (m1 m2 : AM X), presW I m1 -> presW I m2 -> presW I (if b then m1 else m2).
Proof. intros X I b m1 m2 H1 H2. destruct b; auto. Qed.

End RC__2.
Ltac pw_step :=
  lazymatch goal with
  | |- presW _ (abind aget _) => apply presW_get_bind; intros
  | |- presW _ (abind _ _) => apply presW_bind; [|intros]
  | |- presW _ (aret _) => apply presW_ret
  | |- presW _ aget => apply presW_get
  | |- presW _ (acall _) => apply presW_call
  | |- presW _ (acheck _ _) => apply presW_check
  | |- presW _ aspin => apply presW_spin
  | |- presW _ (aundef_ _) => apply presW_undef
  | |- presW _ (aupd _) => apply presW_upd; intros
  | |- presW _ (if ?b then _ else _) => first [apply presW_if | destruct b]   (* [comment removed for export] *)
  | |- presW _ (let x := _ in _) => lazy zeta
  | |- presW _ (let '(_, _) := ?x in _) => destruct x
  | |- presW _ (match ?x with _ => _ end) => destruct x
  | |- hoareW _ aget (fun _ _ => _) => apply presW_get
  | |- hoareW _ (acall _) (fun _ _ => _) => apply presW_call
  end.
Ltac pw := repeat pw_step.

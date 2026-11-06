(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Notation tpathN := (tpath nstep).
Notation texitN := (texit nstep nexit).
Notation ttraceN := (ttrace nstep nexit).

Section Calc.

Definition sound {X : Type} (t : itree node (exc X)) (mo : Model) (P : list event -> X -> Model -> Prop) : Prop :=
  (forall tr r mo1, tpathN t mo tr r mo1 -> exists x, r = Ok x /\ P tr x mo1)
  /\ (forall tr, texitN t mo tr -> False).

Definition det {X : Type} (t : itree node (exc X)) (mo : Model) (E : list event) (x0 : X) (R : Model -> Prop) : Prop :=
  sound t mo (fun tr x mo1 => tr = E /\ x = x0 /\ R mo1).

Definition ex {X : Type} (t : itree node (exc X)) (mo : Model) (E : list event) (x : X) (R : Model -> Prop) : Prop :=
  exists mo1, tpathN t mo E (Ok x) mo1 /\ R mo1.

Definition xsound {X : Type} (t : itree node (exc X)) (mo : Model) (F : list event -> Prop) : Prop :=
  (forall tr r mo1, tpathN t mo tr r mo1 -> False)
  /\ (forall tr, texitN t mo tr -> F tr).

Lemma sound_conseq : forall {X} (t : itree node (exc X)) mo (P Q : list event -> X -> Model -> Prop),
  sound t mo P -> (forall tr x mo1, P tr x mo1 -> Q tr x mo1) -> sound t mo Q.
Proof.
  intros X t mo P Q [H1 H2] HPQ. split; [|exact H2].
  intros tr r mo1 Hp. destruct (H1 _ _ _ Hp) as (x & -> & HP). exists x. split; [reflexivity|]. apply HPQ. exact HP.
Qed.

Lemma sound_ret : forall {X} (x : X) mo (P : list event -> X -> Model -> Prop), P [] x mo -> sound (Ret (Ok x)) mo P.
Proof.
  intros X x mo P HP. split.
  - intros tr r mo1 H. cbn in H. destruct H as (<- & -> & ->). exists x. split; [reflexivity|exact HP].
  - intros tr H. cbn in H. exact H.
Qed.

Lemma sound_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo
    (P : list event -> X -> Model -> Prop) (Q : list event -> Y -> Model -> Prop),
  sound t mo P ->
  (forall tr x mo1, P tr x mo1 -> sound (f x) mo1 (fun tr2 y mo2 => Q (tr ++ tr2) y mo2)) ->
  sound (ebind t f) mo Q.
Proof.
  intros X Y t f mo P Q [H1 H2] Hf. split.
  - intros tr r mo2 Hp. apply tpath_ebind in Hp as [[Hu _]|(tr1 & a & mo1 & tr2 & Ha & Hb & ->)].
    + destruct (H1 _ _ _ Hu) as (x & Hx & _). discriminate Hx.
    + destruct (H1 _ _ _ Ha) as (x & Hx & HP). injection Hx as <-.
      destruct (Hf _ _ _ HP) as [G1 _]. exact (G1 _ _ _ Hb).
  - intros tr Hx. apply texit_ebind in Hx as [Hx|(tr1 & a & mo1 & tr2 & Ha & Hb & ->)].
    + exact (H2 _ Hx).
    + destruct (H1 _ _ _ Ha) as (x & Hx & HP). injection Hx as <-.
      destruct (Hf _ _ _ HP) as [_ G2]. exact (G2 _ Hb).
Qed.

Lemma det_ret : forall {X} (x : X) mo (R : Model -> Prop), R mo -> det (Ret (Ok x)) mo [] x R.
Proof. intros. apply sound_ret. auto. Qed.

Lemma det_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo E1 x R1 E2 y (R2 : Model -> Prop),
  det t mo E1 x R1 -> (forall mo1, R1 mo1 -> det (f x) mo1 E2 y R2) -> det (ebind t f) mo (E1 ++ E2) y R2.
Proof.
  intros X Y t f mo E1 x R1 E2 y R2 Ht Hf. unfold det. eapply sound_ebind; [exact Ht|].
  intros tr x' mo1 (-> & -> & HR). eapply sound_conseq; [exact (Hf _ HR)|].
  intros tr2 y' mo2 (-> & -> & H2). auto.
Qed.

Lemma det_conseq : forall {X} (t : itree node (exc X)) mo E x (R R' : Model -> Prop),
  det t mo E x R -> (forall mo1, R mo1 -> R' mo1) -> det t mo E x R'.
Proof. intros X t mo E x R R' H HR. eapply sound_conseq; [exact H|]. intros tr x' mo1 (-> & -> & H1). auto. Qed.

Lemma ex_ret : forall {X} (x : X) mo (R : Model -> Prop), R mo -> ex (Ret (Ok x)) mo [] x R.
Proof. intros X x mo R HR. exists mo. split; [cbn; auto|exact HR]. Qed.

Lemma ex_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo E1 x R1 E2 y (R2 : Model -> Prop),
  ex t mo E1 x R1 -> (forall mo1, R1 mo1 -> ex (f x) mo1 E2 y R2) -> ex (ebind t f) mo (E1 ++ E2) y R2.
Proof.
  intros X Y t f mo E1 x R1 E2 y R2 (mo1 & Hp & HR) Hf. destruct (Hf _ HR) as (mo2 & Hp2 & HR2).
  exists mo2. split; [|exact HR2]. apply tpath_ebind. right. exists E1, x, mo1, E2. auto.
Qed.

Lemma ex_conseq : forall {X} (t : itree node (exc X)) mo E x (R R' : Model -> Prop),
  ex t mo E x R -> (forall mo1, R mo1 -> R' mo1) -> ex t mo E x R'.
Proof. intros X t mo E x R R' (mo1 & Hp & HR) H. exists mo1. auto. Qed.

(* [comment removed for export] *)
Lemma sound_enode : forall {X} n (pl : resp -> option X) mo (P : list event -> X -> Model -> Prop),
  (forall rsp mo1 evs, nstep n mo rsp mo1 evs -> exists x, pl rsp = Some x /\ P evs x mo1) ->
  (forall code mo', nexit n mo code mo' -> False) ->
  sound (enode n pl) mo P.
Proof.
  intros X n pl mo P Hs Hx. split.
  - intros tr r mo1 Hp. apply tpath_enode in Hp as (rsp & Hst & ->).
    destruct (Hs _ _ _ Hst) as (x & -> & HP). exists x. auto.
  - intros tr H. apply texit_enode in H as (code & mo' & He & _). exact (Hx _ _ He).
Qed.

Lemma ex_enode : forall {X} n (pl : resp -> option X) mo rsp mo1 evs x (R : Model -> Prop),
  nstep n mo rsp mo1 evs -> pl rsp = Some x -> R mo1 -> ex (enode n pl) mo evs x R.
Proof.
  intros X n pl mo rsp mo1 evs x R Hst Hpl HR. exists mo1. split; [|exact HR].
  apply tpath_enode. exists rsp. rewrite Hpl. auto.
Qed.

(* [comment removed for export] *)
Lemma xsound_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo
    (P : list event -> X -> Model -> Prop) (F : list event -> Prop),
  sound t mo P ->
  (forall tr x mo1, P tr x mo1 -> xsound (f x) mo1 (fun tr2 => F (tr ++ tr2))) ->
  xsound (ebind t f) mo F.
Proof.
  intros X Y t f mo P F [H1 H2] Hf. split.
  - intros tr r mo2 Hp. apply tpath_ebind in Hp as [[Hu _]|(tr1 & a & mo1 & tr2 & Ha & Hb & ->)].
    + destruct (H1 _ _ _ Hu) as (x & Hx & _). discriminate Hx.
    + destruct (H1 _ _ _ Ha) as (x & Hx & HP). injection Hx as <-.
      destruct (Hf _ _ _ HP) as [G1 _]. exact (G1 _ _ _ Hb).
  - intros tr Hx. apply texit_ebind in Hx as [Hx|(tr1 & a & mo1 & tr2 & Ha & Hb & ->)].
    + destruct (H2 _ Hx).
    + destruct (H1 _ _ _ Ha) as (x & Hx & HP). injection Hx as <-.
      destruct (Hf _ _ _ HP) as [_ G2]. exact (G2 _ Hb).
Qed.

Lemma xsound_outer : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo F,
  xsound t mo F -> xsound (ebind t f) mo F.
Proof.
  intros X Y t f mo F [H1 H2]. split.
  - intros tr r mo2 Hp. apply tpath_ebind in Hp as [[Hu _]|(tr1 & a & mo1 & tr2 & Ha & _)]; eapply H1; eassumption.
  - intros tr Hx. apply texit_ebind in Hx as [Hx|(tr1 & a & mo1 & tr2 & Ha & _)]; [exact (H2 _ Hx)|]. exfalso. eapply H1; eassumption.
Qed.

Lemma texit_ebind_ex : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo E1 x (R : Model -> Prop) E2,
  ex t mo E1 x R -> (forall mo1, R mo1 -> texitN (f x) mo1 E2) -> texitN (ebind t f) mo (E1 ++ E2).
Proof.
  intros X Y t f mo E1 x R E2 (mo1 & Hp & HR) Hf. apply texit_ebind. right. exists E1, x, mo1, E2. auto.
Qed.

Lemma texit_ebind_outer : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo E,
  texitN t mo E -> texitN (ebind t f) mo E.
Proof. intros. apply texit_ebind. left. assumption. Qed.

(* [comment removed for export] *)
Lemma xsound_exit : forall {X} c (pl : resp -> option X) mo,
  xsound (enode (NExit c) pl) mo (fun tr => tr = [ExitEv (Nodes.exit_code c) (m_fs mo)]).
Proof.
  intros X c pl mo. split.
  - intros tr r mo1 Hp. apply tpath_enode in Hp as (rsp & Hst & _). exact Hst.
  - intros tr Hx. apply texit_enode in Hx as (code & mo' & [-> ->] & ->). reflexivity.
Qed.

Lemma texit_exit : forall {X} c (pl : resp -> option X) mo,
  texitN (enode (NExit c) pl) mo [ExitEv (Nodes.exit_code c) (m_fs mo)].
Proof.
  intros X c pl mo. apply texit_enode. exists (Nodes.exit_code c), (with_halted (Nodes.exit_code c) mo).
  split; [split; reflexivity|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma xsound_ttrace : forall {X} (t : itree node (exc X)) mo F tr, xsound t mo F -> ttraceN t mo tr -> F tr.
Proof.
  intros X t mo F tr [H1 H2] Ht. apply ttrace_split in Ht as [Hx|(r & mo' & Hp)]; [exact (H2 _ Hx)|]. exfalso. eapply H1; eassumption.
Qed.
Lemma texit_ttrace : forall {X} (t : itree node (exc X)) mo tr, texitN t mo tr -> ttraceN t mo tr.
Proof. intros X t mo tr H. apply ttrace_split. left. exact H. Qed.

(* [comment removed for export] *)
Definition run1 {X : Type} (t : itree node (exc X)) (mo : Model) (E : list event) (x : X) (R : Model -> Prop) : Prop :=
  det t mo E x R /\ ex t mo E x R.

Lemma run1_ret : forall {X} (x : X) mo (R : Model -> Prop), R mo -> run1 (Ret (Ok x)) mo [] x R.
Proof. intros. split; [apply det_ret|apply ex_ret]; assumption. Qed.

Lemma run1_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo E1 x R1 E2 y (R2 : Model -> Prop),
  run1 t mo E1 x R1 -> (forall mo1, R1 mo1 -> run1 (f x) mo1 E2 y R2) -> run1 (ebind t f) mo (E1 ++ E2) y R2.
Proof.
  intros X Y t f mo E1 x R1 E2 y R2 [Hd He] Hf. split.
  - eapply det_ebind; [exact Hd|]. intros mo1 H1. exact (proj1 (Hf _ H1)).
  - eapply ex_ebind; [exact He|]. intros mo1 H1. exact (proj2 (Hf _ H1)).
Qed.

Lemma run1_conseq : forall {X} (t : itree node (exc X)) mo E x (R R' : Model -> Prop),
  run1 t mo E x R -> (forall mo1, R mo1 -> R' mo1) -> run1 t mo E x R'.
Proof. intros X t mo E x R R' [Hd He] H. split; [eapply det_conseq|eapply ex_conseq]; eauto. Qed.

Lemma run1_eq : forall {X} (t t' : itree node (exc X)) mo E E' x x' (R : Model -> Prop),
  run1 t mo E x R -> t' = t -> E' = E -> x' = x -> run1 t' mo E' x' R.
Proof. intros. subst. assumption. Qed.

(* [comment removed for export] *)
Lemma run1_enode : forall {X} n (pl : resp -> option X) mo E x,
  (forall rsp mo1 evs, nstep n mo rsp mo1 evs -> pl rsp = Some x /\ mo1 = mo /\ evs = E) ->
  (exists rsp, nstep n mo rsp mo E) ->
  (forall code mo', nexit n mo code mo' -> False) ->
  run1 (enode n pl) mo E x (eq mo).
Proof.
  intros X n pl mo E x Hs (rsp & Hst) Hx. split.
  - apply sound_enode; [|exact Hx]. intros rsp' mo1 evs H. destruct (Hs _ _ _ H) as (Hp & -> & ->). exists x. auto.
  - destruct (Hs _ _ _ Hst) as (Hp & _ & _). eapply ex_enode; [exact Hst|exact Hp|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma run1_enode_mo : forall {X} n (pl : resp -> option X) mo mo' E x,
  (forall rsp mo1 evs, nstep n mo rsp mo1 evs -> pl rsp = Some x /\ mo1 = mo' /\ evs = E) ->
  (exists rsp, nstep n mo rsp mo' E) ->
  (forall code mo2, nexit n mo code mo2 -> False) ->
  run1 (enode n pl) mo E x (eq mo').
Proof.
  intros X n pl mo mo' E x Hs (rsp & Hst) Hx. split.
  - apply sound_enode; [|exact Hx]. intros rsp' mo1 evs H. destruct (Hs _ _ _ H) as (Hp & -> & ->). exists x. auto.
  - destruct (Hs _ _ _ Hst) as (Hp & _ & _). eapply ex_enode; [exact Hst|exact Hp|reflexivity].
Qed.

(* [comment removed for export] *)
Definition xrun {X : Type} (t : itree node (exc X)) (mo : Model) (E : list event) : Prop :=
  xsound t mo (fun tr => tr = E) /\ texitN t mo E.

Lemma xrun_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo E1 x (R : Model -> Prop) E2,
  run1 t mo E1 x R -> (forall mo1, R mo1 -> xrun (f x) mo1 E2) -> xrun (ebind t f) mo (E1 ++ E2).
Proof.
  intros X Y t f mo E1 x R E2 [Hd He] Hf. split.
  - eapply xsound_ebind; [exact Hd|]. intros tr x' mo1 (-> & -> & HR). destruct (Hf _ HR) as [[G1 G2] _]. split; [exact G1|].
    intros tr2 H2. rewrite (G2 _ H2). reflexivity.
  - eapply texit_ebind_ex; [exact He|]. intros mo1 HR. exact (proj2 (Hf _ HR)).
Qed.

Lemma xrun_outer : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) mo E, xrun t mo E -> xrun (ebind t f) mo E.
Proof. intros X Y t f mo E [H1 H2]. split; [apply xsound_outer; exact H1|apply texit_ebind_outer; exact H2]. Qed.

Lemma xrun_exit : forall {X} c (pl : resp -> option X) mo, xrun (enode (NExit c) pl) mo [ExitEv (Nodes.exit_code c) (m_fs mo)].
Proof. intros. split; [apply xsound_exit|apply texit_exit]. Qed.

(* [comment removed for export] *)
Lemma xsound_no_leaf : forall {X} (t : itree node (exc X)) mo F, xsound t mo F -> forall tr r mo1, ~ tpathN t mo tr r mo1.
Proof. intros X t mo F [H _] tr r mo1 Hp. exact (H _ _ _ Hp). Qed.

End Calc.

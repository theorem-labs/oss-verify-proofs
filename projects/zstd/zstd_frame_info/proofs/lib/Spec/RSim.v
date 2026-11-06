(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Monad.
Import ListNotations.
Import ITree.Exc.

Local Notation M := Monad.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Glob.
Variable step : node -> Model -> resp -> Model -> list event -> Prop.
Variable Phi : node -> Model -> Prop.

Fixpoint tglob {R} (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => Phi n mo /\ forall rsp mo' evs, step n mo rsp mo' evs -> tglob (k rsp) mo'
  end.

#[using="Type"] Lemma tglob_bind_l : forall {A B} (t : itree node A) (f : A -> itree node B) mo,
  tglob (ITree.bind node t f) mo -> tglob t mo.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo H; cbn in *; [exact I|].
  destruct H as [Hn Hk]. split; [exact Hn|]. intros rsp mo' evs Hst. eapply IH. exact (Hk _ _ _ Hst).
Qed.

#[using="Type"] Lemma tglob_bind_r : forall {A B} (t : itree node A) (f : A -> itree node B) mo tr r mo',
  tglob (ITree.bind node t f) mo -> tpath step t mo tr r mo' -> tglob (f r) mo'.
Proof.
  intros A B t. induction t as [r0|n k IH]; intros f mo tr r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exact H.
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    eapply IH; [exact (Hk _ _ _ Hst)| exact Hp].
Qed.

#[using="Type"] Lemma tglob_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo,
  tglob t mo -> (forall tr r mo', tpath step t mo tr r mo' -> tglob (f r) mo') -> tglob (ITree.bind node t f) mo.
Proof.
  intros A B t. induction t as [r0|n k IH]; intros f mo H Hf; cbn in *.
  - apply (Hf []). repeat split; reflexivity.
  - destruct H as [Hn Hk]. split; [exact Hn|]. intros rsp mo' evs Hst. apply IH; [exact (Hk _ _ _ Hst)|].
    intros tr r mo'' Hp. apply (Hf (evs ++ tr)). exists rsp, mo', evs, tr. auto.
Qed.

#[using="Type"] Lemma tglob_ebind_l : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo,
  tglob (ebind t f) mo -> tglob t mo.
Proof. intros A B t f mo H. unfold ebind in H. eapply tglob_bind_l. exact H. Qed.

#[using="Type"] Lemma tglob_ebind_r : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo tr a mo',
  tglob (ebind t f) mo -> tpath step t mo tr (Ok a) mo' -> tglob (f a) mo'.
Proof. intros A B t f mo tr a mo' H Hp. unfold ebind in H. exact (tglob_bind_r _ _ _ _ _ _ H Hp). Qed.

#[using="Type"] Lemma tglob_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo,
  tglob t mo -> (forall tr a mo', tpath step t mo tr (Ok a) mo' -> tglob (f a) mo') -> tglob (ebind t f) mo.
Proof.
  intros A B t f mo H Hf. unfold ebind. apply tglob_bind; [exact H|].
  intros tr [|a] mo' Hp; cbn; [exact I| exact (Hf _ _ _ Hp)].
Qed.

#[using="Type"] Lemma tglob_vis : forall {R} n (k : resp -> itree node R) mo,
  tglob (Vis n k) mo <-> (Phi n mo /\ forall rsp mo' evs, step n mo rsp mo' evs -> tglob (k rsp) mo').
Proof. intros; cbn; tauto. Qed.

End Glob.

Lemma tglob_mono : forall step (Phi Phi' : node -> Model -> Prop) {R} (t : itree node R) mo,
  (forall n mo1, Phi n mo1 -> Phi' n mo1) -> tglob step Phi t mo -> tglob step Phi' t mo.
Proof.
  intros step Phi Phi' R t. induction t as [r|n k IH]; intros mo HP H; cbn in *; [exact I|].
  destruct H as [Hn Hk]. split; [apply HP; exact Hn|]. intros rsp mo' evs Hst. apply IH; [exact HP| exact (Hk _ _ _ Hst)].
Qed.

Lemma tglob_trivial : forall step (Phi : node -> Model -> Prop) {R} (t : itree node R) mo,
  (forall n mo1, Phi n mo1) -> tglob step Phi t mo.
Proof.
  intros step Phi R t. induction t as [r|n k IH]; intros mo HP; cbn; [exact I|].
  split; [apply HP|]. intros; apply IH; exact HP.
Qed.

(* [comment removed for export] *)
Lemma tglob_substep : forall (step step' : node -> Model -> resp -> Model -> list event -> Prop) Phi {R} (t : itree node R) mo,
  (forall n mo1 rsp mo2 evs, step' n mo1 rsp mo2 evs -> step n mo1 rsp mo2 evs) ->
  tglob step Phi t mo -> tglob step' Phi t mo.
Proof.
  intros step step' Phi R t. induction t as [r|n k IH]; intros mo Hs H; cbn in *; [exact I|].
  destruct H as [Hn Hk]. split; [exact Hn|]. intros rsp mo' evs Hst. apply IH; [exact Hs| exact (Hk _ _ _ (Hs _ _ _ _ _ Hst))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stot.
Context {St : Type}.
Variable step : node -> Model -> resp -> Model -> list event -> Prop.
Variable texit_ : forall R, itree node R -> Model -> list event -> Prop.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOT {A} (t : itree node (exc (A * St))) (mo : Model) (Post : A -> St -> Model -> Prop) : Prop :=
  (forall tr r mo', tpath step t mo tr r mo' -> tr = [] /\ exists a s', r = Ok (a, s') /\ Post a s' mo')
  /\ (forall tr, ~ texit_ _ t mo tr)
  /\ (exists r mo', tpath step t mo [] r mo').

#[using="Type"] Lemma STOT_mono {A} (t : itree node (exc (A * St))) mo (P P' : A -> St -> Model -> Prop) :
  STOT t mo P -> (forall a s mo1, P a s mo1 -> P' a s mo1) -> STOT t mo P'.
Proof.
  intros (S1 & S2 & S3) HP. split; [| split; [exact S2| exact S3]].
  intros tr r mo' Hp. destruct (S1 _ _ _ Hp) as (-> & a & s' & -> & H). split; [reflexivity|]. exists a, s'. auto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma STOT_path {A} (t : itree node (exc (A * St))) mo (P : A -> St -> Model -> Prop) :
  STOT t mo P -> STOT t mo (fun a s' mo' => P a s' mo' /\ tpath step t mo [] (Ok (a, s')) mo').
Proof.
  intros (S1 & S2 & S3). split; [| split; [exact S2| exact S3]].
  intros tr r mo' Hp. destruct (S1 _ _ _ Hp) as (E & a & s' & Er & H). split; [exact E|]. exists a, s'. split; [exact Er|]. split; [exact H|].
  subst tr r. exact Hp.
Qed.
End Stot.

Arguments STOT {St} step texit_ {A} t mo Post.

Section StotRules.
Context {St : Type}.
Variable step : node -> Model -> resp -> Model -> list event -> Prop.
Variable exit_ : node -> Model -> word -> Model -> Prop.
Local Notation STOT := (STOT step (fun R0 => texit (R:=R0) step exit_)).

#[using="Type"] Lemma STOT_ret {A} (a : A) (s : St) mo : STOT (mret a s) mo (fun a' s' mo' => a' = a /\ s' = s /\ mo' = mo).
Proof.
  split; [| split].
  - intros tr r mo' Hp. cbn in Hp. destruct Hp as (<- & -> & ->). split; [reflexivity|]. exists a, s. auto.
  - intros tr Hx. exact Hx.
  - exists (Ok (a, s)), mo. cbn. auto.
Qed.

#[using="Type"] Lemma STOT_upd (f : St -> St) (s : St) mo : STOT (mupd f s) mo (fun _ s' mo' => s' = f s /\ mo' = mo).
Proof.
  split; [| split].
  - intros tr r mo' Hp. cbn in Hp. destruct Hp as (<- & -> & ->). split; [reflexivity|]. exists tt, (f s). auto.
  - intros tr Hx. exact Hx.
  - exists (Ok (tt, f s)), mo. cbn. auto.
Qed.

#[using="Type"] Lemma STOT_get (s : St) mo : STOT (mget s) mo (fun a s' mo' => a = s /\ s' = s /\ mo' = mo).
Proof.
  split; [| split].
  - intros tr r mo' Hp. cbn in Hp. destruct Hp as (<- & -> & ->). split; [reflexivity|]. exists s, s. auto.
  - intros tr Hx. exact Hx.
  - exists (Ok (s, s)), mo. cbn. auto.
Qed.

#[using="Type"] Lemma STOT_bind {A B} (m : M St A) (k : A -> M St B) (s : St) mo (P1 : A -> St -> Model -> Prop) (P : B -> St -> Model -> Prop) :
  STOT (m s) mo P1 -> (forall a s' mo', P1 a s' mo' -> STOT (k a s') mo' P) -> STOT (mbind m k s) mo P.
Proof.
  intros (S1 & S2 & (r0 & mo0 & S3)) Hk. split; [| split].
  - intros tr r mo' Hp. unfold mbind in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[Hp ->]|(tr1 & [a s1] & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + destruct (S1 _ _ _ Hp) as (_ & a & s' & E & _). discriminate.
    + destruct (S1 _ _ _ Hp1) as (-> & a' & s'' & E & HP1). injection E as <- <-. cbn [fst snd] in Hp2.
      destruct (Hk _ _ _ HP1) as (K1 & _ & _). destruct (K1 _ _ _ Hp2) as (-> & b & s2 & -> & HP). split; [reflexivity|]. exists b, s2. auto.
  - intros tr Hx. unfold mbind in Hx. apply texit_ebind in Hx. destruct Hx as [Hx|(tr1 & [a s1] & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + exact (S2 _ Hx).
    + destruct (S1 _ _ _ Hp1) as (-> & a' & s'' & E & HP1). injection E as <- <-. cbn [fst snd] in Hx2.
      destruct (Hk _ _ _ HP1) as (_ & K2 & _). exact (K2 _ Hx2).
  - destruct (S1 _ _ _ S3) as (_ & a & s' & -> & HP1). destruct (Hk _ _ _ HP1) as (_ & _ & (r1 & mo1 & K3)).
    exists r1, mo1. unfold mbind. apply tpath_ebind. destruct r1 as [|[b s2]].
    + exfalso. destruct (Hk _ _ _ HP1) as (K1 & _ & _). destruct (K1 _ _ _ K3) as (_ & ? & ? & E & _). discriminate.
    + right. exists [], (a, s'), mo0, []. auto.
Qed.

#[using="Type"] Lemma STOT_seq {A B} (m : M St A) (k : A -> M St B) (s : St) mo (P : B -> St -> Model -> Prop) :
  (exists P1, STOT (m s) mo P1 /\ forall a s' mo', P1 a s' mo' -> STOT (k a s') mo' P) -> STOT (mbind m k s) mo P.
Proof. intros (P1 & H1 & H2). eapply STOT_bind; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma STOT_sys {A} (n : node) (dec : resp -> option A) (s : St) mo (P : A -> St -> Model -> Prop) :
  (forall rsp mo' evs, step n mo rsp mo' evs -> evs = [] /\ exists a, dec rsp = Some a /\ P a s mo') ->
  (forall code mo', ~ exit_ n mo code mo') ->
  (exists rsp mo' evs, step n mo rsp mo' evs) ->
  STOT (msys n dec s) mo P.
Proof.
  intros Hst Hne (rsp0 & mo0 & evs0 & Hex). split; [| split].
  - intros tr r mo' Hp. unfold msys in Hp. apply tpath_enode in Hp. destruct Hp as (rsp & Hs & ->).
    destruct (Hst _ _ _ Hs) as (-> & a & -> & HP). split; [reflexivity|]. exists a, s. auto.
  - intros tr Hx. unfold msys in Hx. apply texit_enode in Hx. destruct Hx as (code & mo' & Hx & _). exact (Hne _ _ Hx).
  - destruct (Hst _ _ _ Hex) as (-> & a & Hd & _). exists (Ok (a, s)), mo0. unfold msys. apply tpath_enode. exists rsp0. rewrite Hd. auto.
Qed.
End StotRules.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RES {A B Sa Sb} (Q : A -> B -> Sa -> Model -> Sb -> Model -> Prop)
    (ra : exc (A * Sa)) (moa : Model) (rb : exc (B * Sb)) (mob : Model) : Prop :=
  match ra, rb with
  | Ok (a, sa), Ok (b, sb) => Q a b sa moa sb mob
  | Unr, Unr => True
  | _, _ => False
  end.

Section Half.
Context {Sa Sb : Type}.
Variables (stepa stepb : node -> Model -> resp -> Model -> list event -> Prop).
Variables (exita exitb : node -> Model -> word -> Model -> Prop).
Variables (Phia Phib : node -> Model -> Prop).

Local Notation rel := (Sa -> Model -> Sb -> Model -> Prop).
Local Notation Ga := (tglob stepa Phia).
Local Notation Gb := (tglob stepb Phib).

(* [comment removed for export] *)
Definition hsim {A B} (R : rel) (ma : M Sa A) (mb : M Sb B) (Q : A -> B -> rel) : Prop :=
  forall sa moa sb mob, R sa moa sb mob -> Ga (ma sa) moa -> Gb (mb sb) mob ->
    (forall tr ra moa', tpath stepa (ma sa) moa tr ra moa' ->
       exists rb mob', tpath stepb (mb sb) mob tr rb mob' /\ RES Q ra moa' rb mob')
    /\ (forall tr, texit stepa exita (ma sa) moa tr -> texit stepb exitb (mb sb) mob tr).

#[using="Type"] Lemma hsim_conseq {A B} (R R' : rel) (ma : M Sa A) (mb : M Sb B) (Q Q' : A -> B -> rel) :
  hsim R ma mb Q ->
  (forall sa moa sb mob, R' sa moa sb mob -> R sa moa sb mob) ->
  (forall a b sa moa sb mob, Q a b sa moa sb mob -> Q' a b sa moa sb mob) ->
  hsim R' ma mb Q'.
Proof.
  intros H HR HQ sa moa sb mob HR' Ga0 Gb0. destruct (H sa moa sb mob (HR _ _ _ _ HR') Ga0 Gb0) as [HP HE]. split; [|exact HE].
  intros tr ra moa' Hp. destruct (HP tr ra moa' Hp) as (rb & mob' & Hpb & HRes).
  exists rb, mob'. split; [exact Hpb|]. destruct ra as [|[a sa']]; destruct rb as [|[b sb']]; cbn in *; auto.
Qed.

#[using="Type"] Lemma hsim_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
  (forall sa moa sb mob, R sa moa sb mob -> Q a b sa moa sb mob) -> hsim R (mret a) (mret b) Q.
Proof.
  intros H sa moa sb mob HR _ _. split.
  - intros tr ra moa' Hp. cbn in Hp. destruct Hp as (<- & -> & ->).
    exists (Ok (b, sb)), mob. split; [cbn; repeat split; reflexivity|]. cbn. apply H. exact HR.
  - intros tr Hx. destruct Hx.
Qed.

#[using="Type"] Lemma hsim_munr {A B} (R : rel) (Q : A -> B -> rel) : hsim R (munr (A:=A)) (munr (A:=B)) Q.
Proof.
  intros sa moa sb mob HR _ _. split.
  - intros tr ra moa' Hp. cbn in Hp. destruct Hp as (<- & -> & ->). exists Unr, mob. split; [cbn; repeat split; reflexivity| exact I].
  - intros tr Hx. destruct Hx.
Qed.

#[using="Type"] Lemma hsim_false {A B} (ma : M Sa A) (mb : M Sb B) Q : hsim (fun _ _ _ _ => False) ma mb Q.
Proof. intros sa moa sb mob []. Qed.

#[using="Type"] Lemma hsim_bind {A B A' B'} (R : rel) (ma : M Sa A) (mb : M Sb B) (Q1 : A -> B -> rel)
      (ka : A -> M Sa A') (kb : B -> M Sb B') (Q : A' -> B' -> rel) :
  hsim R ma mb Q1 -> (forall a b, hsim (Q1 a b) (ka a) (kb b) Q) ->
  hsim R (mbind ma ka) (mbind mb kb) Q.
Proof.
  intros H1 H2 sa moa sb mob HR Ga0 Gb0.
  pose proof (tglob_ebind_l stepa Phia _ _ _ Ga0) as Ga1. pose proof (tglob_ebind_l stepb Phib _ _ _ Gb0) as Gb1.
  destruct (H1 sa moa sb mob HR Ga1 Gb1) as [HP1 HE1]. split.
  - intros tr r moa'' Hp. unfold mbind in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[Hp ->]|(tr1 & [a sa'] & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + destruct (HP1 _ _ _ Hp) as (rb & mob' & Hpb & HRes). destruct rb as [|[b sb']]; [|destruct HRes].
      exists Unr, mob'. split; [| exact I]. unfold mbind. apply tpath_ebind. left. auto.
    + destruct (HP1 _ _ _ Hp1) as (rb & mob1 & Hpb1 & HRes). destruct rb as [|[b sb']]; [destruct HRes|]. cbn in HRes. cbn [fst snd] in Hp2.
      pose proof (tglob_ebind_r stepa Phia _ _ _ _ _ _ Ga0 Hp1) as Ga2. pose proof (tglob_ebind_r stepb Phib _ _ _ _ _ _ Gb0 Hpb1) as Gb2.
      cbn [fst snd] in Ga2, Gb2.
      destruct (H2 a b sa' mo1 sb' mob1 HRes Ga2 Gb2) as [HP2 _].
      destruct (HP2 _ _ _ Hp2) as (rb & mob'' & Hpb2 & HRes2).
      exists rb, mob''. split; [| exact HRes2]. unfold mbind. apply tpath_ebind.
      destruct rb as [|[b' sb'']].
      * destruct r as [|[a' sa'']]; [|destruct HRes2].
        (* [comment removed for export] *)
        right. exists tr1, (b, sb'), mob1, tr2. auto.
      * right. exists tr1, (b, sb'), mob1, tr2. auto.
  - intros tr Hx. unfold mbind in Hx. apply texit_ebind in Hx. destruct Hx as [Hx|(tr1 & [a sa'] & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + unfold mbind. apply texit_ebind. left. exact (HE1 _ Hx).
    + destruct (HP1 _ _ _ Hp1) as (rb & mob1 & Hpb1 & HRes). destruct rb as [|[b sb']]; [destruct HRes|]. cbn in HRes. cbn [fst snd] in Hx2.
      pose proof (tglob_ebind_r stepa Phia _ _ _ _ _ _ Ga0 Hp1) as Ga2. pose proof (tglob_ebind_r stepb Phib _ _ _ _ _ _ Gb0 Hpb1) as Gb2.
      cbn [fst snd] in Ga2, Gb2.
      destruct (H2 a b sa' mo1 sb' mob1 HRes Ga2 Gb2) as [_ HE2].
      unfold mbind. apply texit_ebind. right. exists tr1, (b, sb'), mob1, tr2. auto.
Qed.

#[using="Type"] Lemma hsim_pure {A B} (R : rel) (phi : Prop) (ma : M Sa A) (mb : M Sb B) Q :
  (phi -> hsim R ma mb Q) -> hsim (fun sa moa sb mob => phi /\ R sa moa sb mob) ma mb Q.
Proof. intros H sa moa sb mob [Hphi HR]. exact (H Hphi sa moa sb mob HR). Qed.

#[using="Type"] Lemma hsim_exI {A B X} (R : X -> rel) (ma : M Sa A) (mb : M Sb B) Q :
  (forall x, hsim (R x) ma mb Q) -> hsim (fun sa moa sb mob => exists x, R x sa moa sb mob) ma mb Q.
Proof. intros H sa moa sb mob [x HR]. exact (H x sa moa sb mob HR). Qed.

#[using="Type"] Lemma hsim_pointwise {A B} (R : rel) (ma : M Sa A) (mb : M Sb B) Q :
  (forall sa moa sb mob, R sa moa sb mob ->
     hsim (fun sa' moa' sb' mob' => sa' = sa /\ moa' = moa /\ sb' = sb /\ mob' = mob) ma mb Q) ->
  hsim R ma mb Q.
Proof. intros H sa moa sb mob HR. apply (H sa moa sb mob HR). repeat split; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hsim_glob {A B} (R : rel) (ma : M Sa A) (mb : M Sb B) Q :
  hsim (fun sa moa sb mob => R sa moa sb mob /\ Ga (ma sa) moa /\ Gb (mb sb) mob) ma mb Q -> hsim R ma mb Q.
Proof. intros H sa moa sb mob HR Ga0 Gb0. apply (H sa moa sb mob); auto. Qed.

#[using="Type"] Lemma hsim_get (R : rel) :
  hsim R mget mget (fun a b sa moa sb mob => a = sa /\ b = sb /\ R sa moa sb mob).
Proof.
  intros sa moa sb mob HR _ _. split; [|intros tr []].
  intros tr ra moa' Hp. cbn in Hp. destruct Hp as (<- & -> & ->).
  exists (Ok (sb, sb)), mob. split; [cbn; repeat split; reflexivity|]. cbn. auto.
Qed.

#[using="Type"] Lemma hsim_upd (R : rel) (Q : unit -> unit -> rel) (fa : Sa -> Sa) (fb : Sb -> Sb) :
  (forall sa moa sb mob, R sa moa sb mob -> Q tt tt (fa sa) moa (fb sb) mob) ->
  hsim R (mupd fa) (mupd fb) Q.
Proof.
  intros H sa moa sb mob HR _ _. split; [|intros tr []].
  intros tr ra moa' Hp. cbn in Hp. destruct Hp as (<- & -> & ->).
  exists (Ok (tt, fb sb)), mob. split; [cbn; repeat split; reflexivity|]. cbn. apply H. exact HR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hsim_loop {X Y A B} (I : X -> Y -> rel) (Q : A -> B -> rel)
      (bodya : X -> M Sa (X + A)) (bodyb : Y -> M Sb (Y + B)) :
  (forall x y, hsim (I x y) (bodya x) (bodyb y)
     (fun r r' sa moa sb mob => match r, r' with
                                | inl x', inl y' => I x' y' sa moa sb mob
                                | inr a, inr b => Q a b sa moa sb mob
                                | _, _ => False
                                end)) ->
  forall fuel x y, hsim (I x y) (mloop fuel bodya x) (mloop fuel bodyb y) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x y; cbn [mloop].
  - apply hsim_munr.
  - eapply hsim_bind; [apply Hb|]. intros [x'|a] [y'|b]; cbn beta.
    + apply IH.
    + apply hsim_false.
    + apply hsim_false.
    + apply hsim_ret. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hsim_silent {A B} (R : rel) (ma : M Sa A) (mb : M Sb B) (Q : A -> B -> rel) :
  (forall sa moa sb mob, R sa moa sb mob -> Ga (ma sa) moa -> Gb (mb sb) mob ->
     exists Pa Pb, STOT stepa (fun R0 => texit (R:=R0) stepa exita) (ma sa) moa Pa
               /\ STOT stepb (fun R0 => texit (R:=R0) stepb exitb) (mb sb) mob Pb
               /\ forall a sa' moa' b sb' mob', Pa a sa' moa' -> Pb b sb' mob' -> Q a b sa' moa' sb' mob') ->
  hsim R ma mb Q.
Proof.
  intros H sa moa sb mob HR Ga0 Gb0.
  destruct (H sa moa sb mob HR Ga0 Gb0) as (Pa & Pb & (A1 & A2 & A3) & (B1 & B2 & (rb & mob' & B3)) & HQ). split.
  - intros tr ra moa' Hp. destruct (A1 _ _ _ Hp) as (-> & a & sa' & -> & HPa).
    destruct (B1 _ _ _ B3) as (_ & b & sb' & -> & HPb).
    exists (Ok (b, sb')), mob'. split; [exact B3|]. cbn. apply HQ; assumption.
  - intros tr Hx. destruct (A2 _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hsim_node {A B} (na nb : node) (deca : resp -> option A) (decb : resp -> option B) (R : rel) (Q : A -> B -> rel) :
  (forall sa moa sb mob, R sa moa sb mob -> Phia na moa -> Phib nb mob ->
     (forall rspa moa' evs, stepa na moa rspa moa' evs ->
        exists rspb mob', stepb nb mob rspb mob' evs /\
          match deca rspa, decb rspb with
          | Some a, Some b => Q a b sa moa' sb mob'
          | None, None => True
          | _, _ => False
          end)
     /\ (forall code moa', exita na moa code moa' ->
        exists mob', exitb nb mob code mob' /\ m_fs mob' = m_fs moa')) ->
  hsim R (msys na deca) (msys nb decb) Q.
Proof.
  intros H sa moa sb mob HR Ga0 Gb0.
  unfold msys in Ga0, Gb0. unfold enode in Ga0, Gb0. apply tglob_vis in Ga0 as [Pa _]. apply tglob_vis in Gb0 as [Pb _].
  destruct (H _ _ _ _ HR Pa Pb) as [HS HX]. split.
  - intros tr ra moa' Hp. unfold msys in Hp. apply tpath_enode in Hp. destruct Hp as (rsp & Hst & ->).
    destruct (HS rsp moa' tr Hst) as (rspb & mob' & Hstb & HM).
    exists (match decb rspb with Some b => Ok (b, sb) | None => Unr end), mob'. split.
    + unfold msys. apply tpath_enode. exists rspb. split; [exact Hstb|]. destruct (decb rspb); reflexivity.
    + destruct (deca rsp) as [a|]; destruct (decb rspb) as [b|]; cbn; auto.
  - intros tr Hx. unfold msys in Hx. apply texit_enode in Hx. destruct Hx as (code & moa' & Hex & ->).
    destruct (HX code moa' Hex) as (mob' & Hexb & Efs).
    unfold msys. apply texit_enode. exists code, mob'. rewrite Efs. auto.
Qed.

End Half.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Both.
Context {S1 S2 : Type}.
Variables (step1 step2 : node -> Model -> resp -> Model -> list event -> Prop).
Variables (exit1 exit2 : node -> Model -> word -> Model -> Prop).
Variables (Phi1 Phi2 : node -> Model -> Prop).

Definition rel : Type := S1 -> Model -> S2 -> Model -> Prop.

Definition fl (R : rel) : S2 -> Model -> S1 -> Model -> Prop := fun s2 mo2 s1 mo1 => R s1 mo1 s2 mo2.
Definition flQ {A B} (Q : A -> B -> rel) : B -> A -> S2 -> Model -> S1 -> Model -> Prop := fun b a => fl (Q a b).

Local Notation hsim12 := (hsim step1 step2 exit1 exit2 Phi1 Phi2).
Local Notation hsim21 := (hsim step2 step1 exit2 exit1 Phi2 Phi1).

Definition rsim {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q : A -> B -> rel) : Prop :=
  hsim12 R m1 m2 Q /\ hsim21 (fl R) m2 m1 (flQ Q).

#[using="Type"] Lemma RES_fl {A B} (Q : A -> B -> rel) r1 mo1 r2 mo2 : RES (flQ Q) r2 mo2 r1 mo1 <-> RES Q r1 mo1 r2 mo2.
Proof. destruct r1 as [|[a s1]]; destruct r2 as [|[b s2]]; cbn; tauto. Qed.

#[using="Type"] Lemma rsim_conseq {A B} (R R' : rel) (m1 : M S1 A) (m2 : M S2 B) (Q Q' : A -> B -> rel) :
  rsim R m1 m2 Q ->
  (forall s1 mo1 s2 mo2, R' s1 mo1 s2 mo2 -> R s1 mo1 s2 mo2) ->
  (forall a b s1 mo1 s2 mo2, Q a b s1 mo1 s2 mo2 -> Q' a b s1 mo1 s2 mo2) ->
  rsim R' m1 m2 Q'.
Proof.
  intros [H1 H2] HR HQ. split.
  - eapply hsim_conseq; [exact H1| exact HR| exact HQ].
  - eapply hsim_conseq; [exact H2| intros; apply HR; assumption| intros b a s2 mo2 s1 mo1; unfold flQ, fl; apply HQ].
Qed.

#[using="Type"] Lemma rsim_pre {A B} (R R' : rel) (m1 : M S1 A) (m2 : M S2 B) (Q : A -> B -> rel) :
  rsim R m1 m2 Q -> (forall s1 mo1 s2 mo2, R' s1 mo1 s2 mo2 -> R s1 mo1 s2 mo2) -> rsim R' m1 m2 Q.
Proof. intros H HR. eapply rsim_conseq; eauto. Qed.

#[using="Type"] Lemma rsim_post {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q Q' : A -> B -> rel) :
  rsim R m1 m2 Q -> (forall a b s1 mo1 s2 mo2, Q a b s1 mo1 s2 mo2 -> Q' a b s1 mo1 s2 mo2) -> rsim R m1 m2 Q'.
Proof. intros H HQ. eapply rsim_conseq; eauto. Qed.

#[using="Type"] Lemma rsim_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> Q a b s1 mo1 s2 mo2) -> rsim R (mret a) (mret b) Q.
Proof. intros H. split; apply hsim_ret; [exact H| intros s2 mo2 s1 mo1; unfold flQ, fl; apply H]. Qed.

#[using="Type"] Lemma rsim_munr {A B} (R : rel) (Q : A -> B -> rel) : rsim R (munr (A:=A)) (munr (A:=B)) Q.
Proof. split; apply hsim_munr. Qed.

#[using="Type"] Lemma rsim_false {A B} (m1 : M S1 A) (m2 : M S2 B) Q : rsim (fun _ _ _ _ => False) m1 m2 Q.
Proof. split; [apply hsim_false| intros s2 mo2 s1 mo1 []]. Qed.

#[using="Type"] Lemma rsim_bind {A B A' B'} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q1 : A -> B -> rel)
      (k1 : A -> M S1 A') (k2 : B -> M S2 B') (Q : A' -> B' -> rel) :
  rsim R m1 m2 Q1 -> (forall a b, rsim (Q1 a b) (k1 a) (k2 b) Q) ->
  rsim R (mbind m1 k1) (mbind m2 k2) Q.
Proof.
  intros [H1 H1'] H2. split.
  - eapply hsim_bind; [exact H1|]. intros a b. exact (proj1 (H2 a b)).
  - eapply hsim_bind; [exact H1'|]. intros b a. exact (proj2 (H2 a b)).
Qed.

#[using="Type"] Lemma rsim_seq {A B A' B'} (R R1 : rel) (m1 : M S1 A) (m2 : M S2 B)
      (k1 : A -> M S1 A') (k2 : B -> M S2 B') (Q : A' -> B' -> rel) :
  rsim R m1 m2 (fun _ _ => R1) -> (forall a b, rsim R1 (k1 a) (k2 b) Q) ->
  rsim R (mbind m1 k1) (mbind m2 k2) Q.
Proof. intros H1 H2. eapply rsim_bind; [exact H1|]. intros a b. apply H2. Qed.

#[using="Type"] Lemma rsim_pure {A B} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 B) Q :
  (phi -> rsim R m1 m2 Q) -> rsim (fun s1 mo1 s2 mo2 => phi /\ R s1 mo1 s2 mo2) m1 m2 Q.
Proof.
  intros H. split.
  - apply hsim_pure. intros Hphi. exact (proj1 (H Hphi)).
  - intros s2 mo2 s1 mo1 [Hphi HR]. exact (proj2 (H Hphi) s2 mo2 s1 mo1 HR).
Qed.

#[using="Type"] Lemma rsim_pure_l {A B} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 B) Q :
  (phi -> rsim R m1 m2 Q) -> rsim (fun s1 mo1 s2 mo2 => phi /\ R s1 mo1 s2 mo2) m1 m2 Q.
Proof. apply rsim_pure. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsim_bind_eq {A A' B'} (R : rel) (m1 : M S1 A) (m2 : M S2 A) (R1 : A -> rel)
      (k1 : A -> M S1 A') (k2 : A -> M S2 B') (Q : A' -> B' -> rel) :
  rsim R m1 m2 (fun a b s1 mo1 s2 mo2 => a = b /\ R1 a s1 mo1 s2 mo2) ->
  (forall a, rsim (R1 a) (k1 a) (k2 a) Q) ->
  rsim R (mbind m1 k1) (mbind m2 k2) Q.
Proof.
  intros H1 H2. eapply rsim_bind; [exact H1|]. intros a b.
  apply (rsim_pure (R1 a) (a = b)). intros <-. apply H2.
Qed.

#[using="Type"] Lemma rsim_exI {A B X} (R : X -> rel) (m1 : M S1 A) (m2 : M S2 B) Q :
  (forall x, rsim (R x) m1 m2 Q) -> rsim (fun s1 mo1 s2 mo2 => exists x, R x s1 mo1 s2 mo2) m1 m2 Q.
Proof.
  intros H. split.
  - apply hsim_exI. intros x. exact (proj1 (H x)).
  - intros s2 mo2 s1 mo1 [x HR]. exact (proj2 (H x) s2 mo2 s1 mo1 HR).
Qed.

#[using="Type"] Lemma rsim_pointwise {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) Q :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 ->
     rsim (fun s1' mo1' s2' mo2' => s1' = s1 /\ mo1' = mo1 /\ s2' = s2 /\ mo2' = mo2) m1 m2 Q) ->
  rsim R m1 m2 Q.
Proof.
  intros H. split.
  - intros s1 mo1 s2 mo2 HR. apply (proj1 (H s1 mo1 s2 mo2 HR)). repeat split; reflexivity.
  - apply hsim_pointwise. intros s2 mo2 s1 mo1 HR.
    eapply hsim_conseq; [exact (proj2 (H s1 mo1 s2 mo2 HR))| | intros; assumption].
    intros s2' mo2' s1' mo1' (-> & -> & -> & ->). unfold fl. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsim_glob {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) Q :
  rsim (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ tglob step1 Phi1 (m1 s1) mo1 /\ tglob step2 Phi2 (m2 s2) mo2) m1 m2 Q ->
  rsim R m1 m2 Q.
Proof.
  intros [H1 H2]. split.
  - apply hsim_glob. exact H1.
  - apply hsim_glob. eapply hsim_conseq; [exact H2| | intros; assumption].
    intros s2 mo2 s1 mo1 (HR & G2 & G1). unfold fl. auto.
Qed.

#[using="Type"] Lemma rsim_if {A B} (b : bool) (R : rel) (m1 m1' : M S1 A) (m2 m2' : M S2 B) Q :
  (b = true -> rsim R m1 m2 Q) -> (b = false -> rsim R m1' m2' Q) ->
  rsim R (if b then m1 else m1') (if b then m2 else m2') Q.
Proof. intros H1 H2. destruct b; auto. Qed.

#[using="Type"] Lemma rsim_get (R : rel) :
  rsim R mget mget (fun a b s1 mo1 s2 mo2 => a = s1 /\ b = s2 /\ R s1 mo1 s2 mo2).
Proof.
  split.
  - apply hsim_get.
  - eapply hsim_conseq; [apply hsim_get| intros; eassumption|].
    intros b a s2 mo2 s1 mo1 (-> & -> & HR). unfold flQ, fl. auto.
Qed.

#[using="Type"] Lemma rsim_upd (R : rel) (Q : unit -> unit -> rel) (f1 : S1 -> S1) (f2 : S2 -> S2) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> Q tt tt (f1 s1) mo1 (f2 s2) mo2) ->
  rsim R (mupd f1) (mupd f2) Q.
Proof. intros H. split; apply hsim_upd; [exact H| intros s2 mo2 s1 mo1; unfold flQ, fl; apply H]. Qed.

#[using="Type"] Lemma rsim_loop {X Y A B} (I : X -> Y -> rel) (Q : A -> B -> rel)
      (body1 : X -> M S1 (X + A)) (body2 : Y -> M S2 (Y + B)) :
  (forall x y, rsim (I x y) (body1 x) (body2 y)
     (fun r r' s1 mo1 s2 mo2 => match r, r' with
                                | inl x', inl y' => I x' y' s1 mo1 s2 mo2
                                | inr a, inr b => Q a b s1 mo1 s2 mo2
                                | _, _ => False
                                end)) ->
  forall fuel x y, rsim (I x y) (mloop fuel body1 x) (mloop fuel body2 y) Q.
Proof.
  intros Hb fuel x y. split.
  - apply (hsim_loop step1 step2 exit1 exit2 Phi1 Phi2 I Q). intros x' y'. exact (proj1 (Hb x' y')).
  - apply (hsim_loop step2 step1 exit2 exit1 Phi2 Phi1 (fun y0 x0 => fl (I x0 y0)) (flQ Q)).
    intros y' x'. eapply hsim_conseq; [exact (proj2 (Hb x' y'))| intros; assumption|].
    intros [y1|b] [x1|a] s2 mo2 s1 mo1; unfold flQ, fl; cbn; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsim_silent {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q : A -> B -> rel) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> tglob step1 Phi1 (m1 s1) mo1 -> tglob step2 Phi2 (m2 s2) mo2 ->
     exists P1 P2, STOT step1 (fun R0 => texit (R:=R0) step1 exit1) (m1 s1) mo1 P1
               /\ STOT step2 (fun R0 => texit (R:=R0) step2 exit2) (m2 s2) mo2 P2
               /\ forall a s1' mo1' b s2' mo2', P1 a s1' mo1' -> P2 b s2' mo2' -> Q a b s1' mo1' s2' mo2') ->
  rsim R m1 m2 Q.
Proof.
  intros H. split.
  - apply hsim_silent. exact H.
  - apply hsim_silent. intros s2 mo2 s1 mo1 HR G2 G1.
    destruct (H s1 mo1 s2 mo2 HR G1 G2) as (P1 & P2 & T1 & T2 & HQ).
    exists P2, P1. split; [exact T2|]. split; [exact T1|]. intros; unfold flQ, fl; apply HQ; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsim_node {A B} (n1 n2 : node) (dec1 : resp -> option A) (dec2 : resp -> option B) (R : rel) (Q : A -> B -> rel) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> Phi1 n1 mo1 -> Phi2 n2 mo2 ->
     (forall rsp1 mo1' evs, step1 n1 mo1 rsp1 mo1' evs ->
        exists rsp2 mo2', step2 n2 mo2 rsp2 mo2' evs /\
          match dec1 rsp1, dec2 rsp2 with
          | Some a, Some b => Q a b s1 mo1' s2 mo2'
          | None, None => True
          | _, _ => False
          end)
     /\ (forall rsp2 mo2' evs, step2 n2 mo2 rsp2 mo2' evs ->
        exists rsp1 mo1', step1 n1 mo1 rsp1 mo1' evs /\
          match dec1 rsp1, dec2 rsp2 with
          | Some a, Some b => Q a b s1 mo1' s2 mo2'
          | None, None => True
          | _, _ => False
          end)
     /\ (forall code mo1', exit1 n1 mo1 code mo1' -> exists mo2', exit2 n2 mo2 code mo2' /\ m_fs mo2' = m_fs mo1')
     /\ (forall code mo2', exit2 n2 mo2 code mo2' -> exists mo1', exit1 n1 mo1 code mo1' /\ m_fs mo1' = m_fs mo2')) ->
  rsim R (msys n1 dec1) (msys n2 dec2) Q.
Proof.
  intros H. split.
  - apply hsim_node. intros s1 mo1 s2 mo2 HR P1 P2. destruct (H _ _ _ _ HR P1 P2) as (A1 & _ & A3 & _). auto.
  - apply hsim_node. intros s2 mo2 s1 mo1 HR P2 P1. destruct (H _ _ _ _ HR P1 P2) as (_ & A2 & _ & A4). split; [|exact A4].
    intros rsp2 mo2' evs Hst. destruct (A2 _ _ _ Hst) as (rsp1 & mo1' & Hst1 & HM). exists rsp1, mo1'. split; [exact Hst1|].
    destruct (dec1 rsp1); destruct (dec2 rsp2); unfold flQ, fl; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rsim_ttrace {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) Q s1 mo1 s2 mo2 :
  rsim R m1 m2 Q -> R s1 mo1 s2 mo2 -> tglob step1 Phi1 (m1 s1) mo1 -> tglob step2 Phi2 (m2 s2) mo2 ->
  (forall tr r mo', ~ tpath step1 (m1 s1) mo1 tr r mo') ->
  (forall tr, ttrace step1 exit1 (m1 s1) mo1 tr <-> ttrace step2 exit2 (m2 s2) mo2 tr)
  /\ (forall tr r mo', ~ tpath step2 (m2 s2) mo2 tr r mo').
Proof.
  intros [H12 H21] HR G1 G2 NL.
  destruct (H12 _ _ _ _ HR G1 G2) as [P12 E12]. destruct (H21 _ _ _ _ HR G2 G1) as [P21 E21].
  assert (NL2 : forall tr r mo', ~ tpath step2 (m2 s2) mo2 tr r mo').
  { intros tr r mo' Hp. destruct (P21 _ _ _ Hp) as (r1 & mo1' & Hp1 & _). exact (NL _ _ _ Hp1). }
  split; [| exact NL2].
  intros tr. rewrite !ttrace_split. split.
  - intros [Hx|(r & mo' & Hp)]; [left; exact (E12 _ Hx)| destruct (NL _ _ _ Hp)].
  - intros [Hx|(r & mo' & Hp)]; [left; exact (E21 _ Hx)| destruct (NL2 _ _ _ Hp)].
Qed.

End Both.

Arguments rel S1 S2 : clear implicits.
Arguments rsim {S1 S2} step1 step2 exit1 exit2 Phi1 Phi2 {A B} R m1 m2 Q.

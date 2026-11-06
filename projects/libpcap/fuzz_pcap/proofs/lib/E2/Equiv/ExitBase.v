(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import HaltsAdq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tall {R} (NP : node -> Prop) (P : R -> Prop) (t : itree node R) : Prop :=
  match t with
  | Ret r => P r
  | Vis n k => NP n /\ forall rsp, tall NP P (k rsp)
  end.

Lemma tall_mono : forall {R} (NP NP' : node -> Prop) (P P' : R -> Prop) (t : itree node R),
  (forall n, NP n -> NP' n) -> (forall r, P r -> P' r) -> tall NP P t -> tall NP' P' t.
Proof.
  intros R NP NP' P P' t HN HP. induction t as [r|n k IH]; cbn; [apply HP|].
  intros [H1 H2]. split; [apply HN; exact H1|]. intros rsp. apply IH. apply H2.
Qed.

Lemma tall_bind : forall {A B} NP (P : B -> Prop) (t : itree node A) (f : A -> itree node B),
  tall NP (fun a => tall NP P (f a)) t -> tall NP P (ITree.bind node t f).
Proof.
  intros A B NP P t f. induction t as [r|n k IH]; cbn; [auto|].
  intros [H1 H2]. split; [exact H1|]. intros rsp. apply IH. apply H2.
Qed.

(* [comment removed for export] *)
Definition exit_status (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

(* [comment removed for export] *)
Definition exits_ok (S : word -> Prop) (n : node) : Prop :=
  match n with NExit c => S (exit_status c) | _ => True end.

(* [comment removed for export] *)
Definition noexit (n : node) : Prop := match n with NExit _ => False | _ => True end.

Lemma noexit_exits_ok : forall S n, noexit n -> exits_ok S n.
Proof. intros S n. destruct n; cbn; auto; contradiction. Qed.

(* [comment removed for export] *)
Lemma tall_exits_in : forall {R} (S : word -> Prop) (P : R -> Prop) (t : itree node R) mo,
  tall (exits_ok S) P t -> exits_in nstep nexit t mo S.
Proof.
  intros R S P t. induction t as [r|n k IH]; intros mo H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split.
  - intros code mo' Hx. destruct (nexit_code n mo code mo' Hx) as (c & -> & ->). exact H1.
  - intros rsp mo' evs _. apply IH. apply H2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MAll.
Context {St : Type}.
Variable NP : node -> Prop.

Definition lift_leaf {A} (P : A -> Prop) (r : exc (A * St)) : Prop :=
  match r with Unr => True | Ok p => P (fst p) end.

Definition mall {A} (m : M St A) (P : A -> Prop) : Prop :=
  forall s, tall NP (lift_leaf P) (m s).

#[using="Type"] Lemma mall_ret {A} (a : A) (P : A -> Prop) : P a -> mall (mret a) P.
Proof. intros H s. exact H. Qed.

#[using="Type"] Lemma mall_unr {A} (P : A -> Prop) : mall (munr (A:=A)) P.
Proof. intros s. exact I. Qed.

#[using="Type"] Lemma mall_get (P : St -> Prop) : (forall s, P s) -> mall mget P.
Proof. intros H s. apply H. Qed.

#[using="Type"] Lemma mall_put s' (P : unit -> Prop) : P tt -> mall (mput s') P.
Proof. intros H s. exact H. Qed.

#[using="Type"] Lemma mall_upd f (P : unit -> Prop) : P tt -> mall (mupd f) P.
Proof. intros H s. exact H. Qed.

#[using="Type"] Lemma mall_mono {A} (m : M St A) (P P' : A -> Prop) :
  mall m P -> (forall a, P a -> P' a) -> mall m P'.
Proof.
  intros H HP s. eapply tall_mono; [intros n Hn; exact Hn| |exact (H s)].
  intros [|[a s']]; cbn; auto.
Qed.

#[using="Type"] Lemma mall_bind {A B} (m : M St A) (f : A -> M St B) (Q : A -> Prop) (P : B -> Prop) :
  mall m Q -> (forall a, Q a -> mall (f a) P) -> mall (mbind m f) P.
Proof.
  intros Hm Hf s. unfold mbind, ebind. apply tall_bind.
  eapply tall_mono; [intros n Hn; exact Hn| |exact (Hm s)].
  intros [|[a s']]; cbn; [intros _; exact I|]. intros Ha. exact (Hf a Ha s').
Qed.

#[using="Type"] Lemma mall_sys {A} n (dec : resp -> option A) (P : A -> Prop) :
  NP n -> (forall rsp a, dec rsp = Some a -> P a) -> mall (msys n dec) P.
Proof.
  intros Hn Hd s. unfold msys, enode. cbn. split; [exact Hn|]. intros rsp.
  destruct (dec rsp) as [a|] eqn:E; cbn; [exact (Hd rsp a E)| exact I].
Qed.

#[using="Type"] Lemma mall_loop {X R} (body : X -> M St (X + R)) (P : R -> Prop) :
  (forall x, mall (body x) (fun r => match r with inl _ => True | inr v => P v end)) ->
  forall fuel x, mall (mloop fuel body x) P.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply mall_unr|].
  eapply mall_bind; [apply Hb|]. intros [x'|v] Hr; [apply IH| apply mall_ret; exact Hr].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mall_bind_true {A B} (m : M St A) (f : A -> M St B) (P : B -> Prop) :
  mall m (fun _ => True) -> (forall a, mall (f a) P) -> mall (mbind m f) P.
Proof. intros Hm Hf. eapply mall_bind; [exact Hm|]. intros a _. apply Hf. Qed.

#[using="Type"] Lemma mall_sys_true {A} n (dec : resp -> option A) : NP n -> mall (msys n dec) (fun _ => True).
Proof. intros Hn. apply mall_sys; [exact Hn|]. intros; exact I. Qed.

#[using="Type"] Lemma mall_true {A} (m : M St A) (P : A -> Prop) : mall m P -> mall m (fun _ => True).
Proof. intros H. eapply mall_mono; [exact H|]. intros; exact I. Qed.
End MAll.

(* [comment removed for export] *)
Definition mne {St A} (m : M St A) : Prop := mall noexit m (fun _ => True).

Lemma mne_mall {St A} (S : word -> Prop) (m : M St A) : mne m -> mall (exits_ok S) m (fun _ => True).
Proof. intros H s. eapply tall_mono; [apply noexit_exits_ok| intros r Hr; exact Hr| exact (H s)]. Qed.

Lemma mne_ret {St A} (a : A) : mne (St:=St) (mret a).
Proof. apply mall_ret. exact I. Qed.
Lemma mne_unr {St A} : mne (St:=St) (munr (A:=A)).
Proof. apply mall_unr. Qed.
Lemma mne_get {St} : mne (St:=St) mget.
Proof. apply mall_get. intros; exact I. Qed.
Lemma mne_put {St} s : mne (St:=St) (mput s).
Proof. apply mall_put. exact I. Qed.
Lemma mne_upd {St} f : mne (St:=St) (mupd f).
Proof. apply mall_upd. exact I. Qed.
Lemma mne_bind {St A B} (m : M St A) (f : A -> M St B) : mne m -> (forall a, mne (f a)) -> mne (mbind m f).
Proof. intros Hm Hf. apply mall_bind_true; assumption. Qed.
Lemma mne_sys {St A} n (dec : resp -> option A) : noexit n -> mne (St:=St) (msys n dec).
Proof. intros Hn. apply mall_sys_true. exact Hn. Qed.
Lemma mne_loop {St X R} (body : X -> M St (X + R)) : (forall x, mne (body x)) -> forall fuel x, mne (mloop fuel body x).
Proof. intros Hb fuel x. apply mall_loop. intros x'. eapply mall_mono; [apply Hb|]. intros [|]; auto. Qed.
Lemma mne_when {St} b (m : M St unit) : mne m -> mne (mwhen b m).
Proof. intros H. destruct b; cbn; [exact H| apply mne_ret]. Qed.
Lemma mne_assert {St} b : mne (St:=St) (massert b).
Proof. destruct b; cbn; [apply mne_ret| apply mne_unr]. Qed.

Create HintDb mne discriminated.

(* [comment removed for export] *)
Ltac destruct_inner x :=
  lazymatch x with
  | match ?y with _ => _ end => destruct_inner y
  | _ => destruct x
  end.
Ltac mne_node :=
  first [ exact I
        | cbn; exact I
        | repeat (lazymatch goal with |- noexit (match ?x with _ => _ end) => destruct_inner x end); first [exact I | cbn; exact I] ].
(* [comment removed for export] *)
Ltac mne_extra := fail.
Ltac mne_step :=
  lazymatch goal with
  | |- mne (mbind _ _) => apply mne_bind; [| intros ?]
  | |- mne (mret _) => apply mne_ret
  | |- mne munr => apply mne_unr
  | |- mne mget => apply mne_get
  | |- mne (mput _) => apply mne_put
  | |- mne (mupd _) => apply mne_upd
  | |- mne (mwhen _ _) => apply mne_when
  | |- mne (massert _) => apply mne_assert
  | |- mne (msys _ _) => apply mne_sys; mne_node
  | |- mne (mloop _ _ _) => apply mne_loop; intros ?
  | |- mne (match ?x with _ => _ end) => destruct x
  | |- mne (let _ := _ in _) => cbv zeta
  | |- mne _ => first [ mne_extra | solve [auto with mne nocore] ]
  end.
Ltac mne_go := repeat (cbv beta; mne_step).

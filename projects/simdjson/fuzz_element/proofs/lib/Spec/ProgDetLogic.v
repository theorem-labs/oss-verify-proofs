(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Monad Prog ProgDetIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Definition Pn (n : node) (mo : Model) : Prop := nsafe n mo /\ no_enomem n mo /\ minv mo /\ m_halted mo = None.

Definition ans_ok (n : node) (rsp : resp) : Prop :=
  match n with
  | NMmap _ _ _ flags => Z.land flags MAP_FIXED_Z = 0%Z -> errno_of (eff_ret rsp) = None
  | NMprotect _ _ _ => errno_of (eff_ret rsp) = None
  | _ => True
  end.

Definition openable_b (p : list byte) (fs : Fs) : bool :=
  if (path_max <=? length p)%nat then false
  else match p with
       | [] => false
       | _ :: _ => if path_eqb p dot_path then true
                   else match fs_lookup fs p with None => false | Some _ => true end
       end.

Definition fd_free_b (fds : list (word * FdEntry)) : bool :=
  match fd_lookup fds (alloc_fd fds) with None => true | Some _ => false end.

Definition open_admits (p : list byte) (mo : Model) : bool := openable_b p (m_fs mo) && fd_free_b (m_fds mo).

Definition osel (sel : option bool) (n : node) (mo : Model) (rsp : resp) : Prop :=
  match sel, n with
  | Some b, NOpen p =>
      if b && open_admits p mo then errno_of (eff_ret rsp) = None else errno_of (eff_ret rsp) <> None
  | _, _ => True
  end.

Definition stepR (sel : option bool) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  Pn n mo /\ nstep n mo rsp mo' evs /\ osel sel n mo rsp.

Definition nprog (sel : option bool) (n : node) (mo : Model) : Prop :=
  Pn n mo -> (exists rsp mo' evs, stepR sel n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo').

Lemma tpath_stepR_nstep : forall sel {R} (t : itree node R) mo tr r mo',
  tpath (stepR sel) t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof.
  intros sel R t. induction t as [r0|n k IH|kc IHc]; intros mo tr r mo' H; cbn in *; [exact H| |destruct H as [z H]; exists z; apply IHc; exact H].
  destruct H as (rsp & mo1 & evs & tr' & (_ & Hst & _) & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|].
  split; [eapply IH; exact Hp| reflexivity].
Qed.

Lemma texit_stepR_nstep : forall sel {R} (t : itree node R) mo tr,
  texit (stepR sel) nexit t mo tr -> texit nstep nexit t mo tr.
Proof.
  intros sel R t. induction t as [r0|n k IH|kc IHc]; intros mo tr H; cbn in *; [exact H| |destruct H as [z H]; exists z; apply IHc; exact H].
  destruct H as [Hx|(rsp & mo1 & evs & tr' & (_ & Hst & _) & Hp & ->)]; [left; exact Hx|].
  right. exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [eapply IH; exact Hp| reflexivity].
Qed.

Lemma ans_ok_of_no_enomem : forall n mo rsp mo' evs, no_enomem n mo -> nstep n mo rsp mo' evs -> ans_ok n rsp.
Proof.
  intros n mo rsp mo' evs Hn Hst. destruct n; cbn in *; try exact I.
  - intros Hf. exact (proj1 Hn Hf _ _ _ Hst).
  - exact (proj1 Hn _ _ _ Hst).
Qed.

Lemma stepR_ans_ok : forall sel n mo rsp mo' evs, stepR sel n mo rsp mo' evs -> ans_ok n rsp.
Proof. intros sel n mo rsp mo' evs ((_ & Hn & _) & Hst & _). eapply ans_ok_of_no_enomem; eassumption. Qed.

Lemma texit_nstep_stepR : forall {R} (t : itree node R) mo tr,
  tsafe nstep Pn t mo -> texit nstep nexit t mo tr -> texit (stepR None) nexit t mo tr.
Proof.
  intros R t. induction t as [r0|n k IH|kc IHc]; intros mo tr Hs H; cbn in *; [exact H| |destruct H as [z H]; exists z; apply IHc; [apply Hs| exact H]].
  destruct Hs as [Hn Hk].
  destruct H as [Hx|(rsp & mo1 & evs & tr' & Hst & Hp & ->)]; [left; exact Hx|].
  right. exists rsp, mo1, evs, tr'. split; [split; [exact Hn| split; [exact Hst| exact I]]|].
  split; [eapply IH; [eapply Hk; exact Hst| exact Hp]| reflexivity].
Qed.

Lemma tsafe_Pn : forall {R} (t : itree node R) mo,
  tsafe nstep nsafe t mo -> tsafe nstep no_enomem t mo -> minv mo -> m_halted mo = None -> tsafe nstep Pn t mo.
Proof.
  intros R t. induction t as [r0|n k IH|kc IHc]; intros mo H1 H2 Hmi Hh; cbn in *; [exact I| |intros z; apply IHc; auto].
  destruct H1 as [Hs1 Hk1]. destruct H2 as [Hs2 Hk2]. split; [split; [exact Hs1| split; [exact Hs2| split; assumption]]|].
  intros rsp mo' evs Hst. destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hs1 Hst) as [Hh' Hmi'].
  apply IH; eauto.
Qed.

Lemma leaves_unreachable_m_stepR : forall sel {R} (t : itree node R) mo,
  leaves_unreachable_m nstep t mo -> leaves_unreachable_m (stepR sel) t mo.
Proof. intros sel R t mo H tr r mo' Hp. exact (H tr r mo' (tpath_stepR_nstep sel t mo tr r mo' Hp)). Qed.

Section Logic.
Variable sel : option bool.
Variable X : list event -> Prop.

Fixpoint twfE {R} (t : itree node (exc R)) (mo : Model) (tr : list event)
    (P : R -> Model -> list event -> Prop) : Prop :=
  match t with
  | Ret r => match r with Unr => True | Ok a => P a mo tr end
  | Vis n k => nprog sel n mo
             /\ (forall code mo', nexit n mo code mo' -> X (tr ++ [ExitEv code (m_fs mo')]))
             /\ (forall rsp mo' evs, stepR sel n mo rsp mo' evs -> twfE (k rsp) mo' (tr ++ evs) P)
  | Cho k => forall z, twfE (k z) mo tr P
  end.

Lemma twfE_mono : forall {R} (t : itree node (exc R)) mo tr (P P' : R -> Model -> list event -> Prop),
  twfE t mo tr P -> (forall r mo1 tr1, P r mo1 tr1 -> P' r mo1 tr1) -> twfE t mo tr P'.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo tr P P' H HP; cbn in *.
  - destruct r; [exact I| apply HP; exact H].
  - destruct H as (Hp & Hx & Hk). split; [exact Hp|]. split; [exact Hx|].
    intros rsp mo' evs Hst. eapply IH; [apply Hk; exact Hst| exact HP].
  - intros z. eapply IHc; [apply H| exact HP].
Qed.

Lemma twfE_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo tr P,
  twfE t mo tr (fun a mo1 tr1 => twfE (f a) mo1 tr1 P) -> twfE (ebind t f) mo tr P.
Proof.
  intros A B t. induction t as [r|n k IH|kc IHc]; intros f mo tr P H; cbn in *.
  - destruct r; [exact I| exact H].
  - destruct H as (Hp & Hx & Hk). split; [exact Hp|]. split; [exact Hx|].
    intros rsp mo' evs Hst. apply IH. apply Hk. exact Hst.
  - intros z. apply IHc. apply H.
Qed.

Lemma twfE_tpath : forall {R} (t : itree node (exc R)) mo tr0 P tr r mo',
  twfE t mo tr0 P -> tpath (stepR sel) t mo tr (Ok r) mo' -> P r mo' (tr0 ++ tr).
Proof.
  intros R t. induction t as [r0|n k IH|kc IHc]; intros mo tr0 P tr r mo' H Hp; cbn in *.
  - destruct Hp as (-> & -> & ->). rewrite app_nil_r. exact H.
  - destruct H as (_ & _ & Hk). destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    rewrite app_assoc. eapply IH; [apply Hk; exact Hst| exact Hp].
  - destruct Hp as [z Hp]. eapply IHc; [apply H| exact Hp].
Qed.

Lemma twfE_texit : forall {R} (t : itree node (exc R)) mo tr0 P tr,
  twfE t mo tr0 P -> texit (stepR sel) nexit t mo tr -> X (tr0 ++ tr).
Proof.
  intros R t. induction t as [r0|n k IH|kc IHc]; intros mo tr0 P tr H Hx; cbn in *; [destruct Hx| |destruct Hx as [z Hx]; eapply IHc; [apply H| exact Hx]].
  destruct H as (_ & HX & Hk). destruct Hx as [(code & mo' & Hex & ->)|(rsp & mo1 & evs & tr' & Hst & Hx & ->)].
  - exact (HX _ _ Hex).
  - rewrite app_assoc. eapply IH; [apply Hk; exact Hst| exact Hx].
Qed.

Lemma twfE_exists : forall {R} (t : itree node (exc R)) mo tr0 P,
  twfE t mo tr0 P -> tsafe nstep Pn t mo -> leaves_unreachable_m nstep t mo ->
  exists tr, texit (stepR sel) nexit t mo tr.
Proof.
  intros R t. induction t as [r0|n k IH|kc IHc]; intros mo tr0 P H Hs Hl; cycle 2.
  {
    cbn in H, Hs. destruct (IHc 0%Z mo tr0 P (H 0%Z) (Hs 0%Z) (proj1 (leaves_unreachable_m_cho _ _ kc mo) Hl 0%Z)) as (tr & Hx).
    exists tr. cbn. exists 0%Z. exact Hx. }
  - exfalso. apply (Hl [] r0 mo). cbn. repeat split; reflexivity.
  - cbn in H. destruct H as (Hp & _ & Hk). destruct Hs as [(Hsf & Hne & Hmi & Hh) Hks].
    destruct (Hp (conj Hsf (conj Hne (conj Hmi Hh)))) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    + destruct (IH rsp mo' (tr0 ++ evs) P (Hk _ _ _ Hst) (Hks _ _ _ (proj1 (proj2 Hst)))
                  (leaves_unreachable_m_step _ _ n k mo rsp mo' evs Hl (proj1 (proj2 Hst)))) as (tr' & Hx).
      exists (evs ++ tr'). cbn. right. exists rsp, mo', evs, tr'. split; [exact Hst|]. split; [exact Hx| reflexivity].
    + exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [exact Hex| reflexivity].
Qed.

Lemma twfE_resolves : forall {R} (t' t : itree node (exc R)), resolves t' t ->
  forall mo tr P, twfE t mo tr P -> twfE t' mo tr P.
Proof.
  intros R t' t Hr. induction Hr as [r|n k k' Hk IH|k z t'' H IH]; intros mo tr P HT; cbn in *.
  - exact HT.
  - destruct HT as (Hp & Hx & Hk'). split; [exact Hp|]. split; [exact Hx|]. intros rsp mo' evs Hst. apply IH. apply Hk'. exact Hst.
  - apply IH. apply HT.
Qed.

Section MSpecE.
Context {St : Type}.

Definition assnE : Type := St -> Model -> list event -> Prop.

Definition mspecE {A} (P : assnE) (m : M St A) (Q : A -> assnE) : Prop :=
  forall s mo tr, P s mo tr -> twfE (m s) mo tr (fun p mo' tr' => Q (fst p) (snd p) mo' tr').

Lemma mspecE_ret {A} (a : A) (P : assnE) (Q : A -> assnE) :
  (forall s mo tr, P s mo tr -> Q a s mo tr) -> mspecE P (mret a) Q.
Proof. intros H s mo tr HP. cbn. apply H. exact HP. Qed.

Lemma mspecE_bind {A B} (m : M St A) (f : A -> M St B) (P : assnE) (Q1 : A -> assnE) (Q : B -> assnE) :
  mspecE P m Q1 -> (forall a, mspecE (Q1 a) (f a) Q) -> mspecE P (mbind m f) Q.
Proof.
  intros Hm Hf s mo tr HP. unfold mbind. apply twfE_ebind.
  eapply twfE_mono; [exact (Hm s mo tr HP)|]. intros [a s1] mo1 tr1 H1. cbn in *. exact (Hf a s1 mo1 tr1 H1).
Qed.

Lemma mspecE_seq {A B} (m : M St A) (f : A -> M St B) (P R : assnE) (Q : B -> assnE) :
  mspecE P m (fun _ => R) -> (forall a, mspecE R (f a) Q) -> mspecE P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecE_bind; [exact Hm|]. intros a. apply Hf. Qed.

Lemma mspecE_conseq {A} (m : M St A) (P P' : assnE) (Q Q' : A -> assnE) :
  mspecE P m Q -> (forall s mo tr, P' s mo tr -> P s mo tr) ->
  (forall a s mo tr, Q a s mo tr -> Q' a s mo tr) -> mspecE P' m Q'.
Proof.
  intros Hm HP HQ s mo tr HP'. eapply twfE_mono; [exact (Hm s mo tr (HP _ _ _ HP'))|].
  intros [a s1] mo1 tr1; cbn; auto.
Qed.

Lemma mspecE_pre {A} (m : M St A) (P P' : assnE) (Q : A -> assnE) :
  mspecE P m Q -> (forall s mo tr, P' s mo tr -> P s mo tr) -> mspecE P' m Q.
Proof. intros Hm HP. eapply mspecE_conseq; eauto. Qed.

Lemma mspecE_post {A} (m : M St A) (P : assnE) (Q Q' : A -> assnE) :
  mspecE P m Q -> (forall a s mo tr, Q a s mo tr -> Q' a s mo tr) -> mspecE P m Q'.
Proof. intros Hm HQ. eapply mspecE_conseq; eauto. Qed.

Lemma mspecE_munr {A} (P : assnE) (Q : A -> assnE) : mspecE P munr Q.
Proof. intros s mo tr _. exact I. Qed.

Lemma mspecE_cho (P : assnE) : mspecE P mcho (fun _ s mo tr => P s mo tr).
Proof. intros s mo tr HP z. cbn. exact HP. Qed.

Lemma mspecE_chok {B} (k : Z -> M St B) (P : assnE) (Q : B -> assnE) :
  (forall z, mspecE P (k z) Q) -> mspecE P (mbind mcho k) Q.
Proof. intros H s mo tr HP. rewrite mbind_mcho. intros z. exact (H z s mo tr HP). Qed.

Lemma mspecE_false {A} (m : M St A) (Q : A -> assnE) : mspecE (fun _ _ _ => False) m Q.
Proof. intros s mo tr []. Qed.

Lemma mspecE_get (P : assnE) (Q : St -> assnE) :
  (forall s mo tr, P s mo tr -> Q s s mo tr) -> mspecE P mget Q.
Proof. intros H s mo tr HP. cbn. apply H. exact HP. Qed.

Lemma mspecE_put (P : assnE) (s1 : St) (Q : unit -> assnE) :
  (forall s mo tr, P s mo tr -> Q tt s1 mo tr) -> mspecE P (mput s1) Q.
Proof. intros H s mo tr HP. cbn. exact (H s mo tr HP). Qed.

Lemma mspecE_upd (P : assnE) (f : St -> St) (Q : unit -> assnE) :
  (forall s mo tr, P s mo tr -> Q tt (f s) mo tr) -> mspecE P (mupd f) Q.
Proof. intros H s mo tr HP. cbn. apply H. exact HP. Qed.

Lemma mspecE_if {A} (b : bool) (m1 m2 : M St A) (P : assnE) Q :
  (b = true -> mspecE P m1 Q) -> (b = false -> mspecE P m2 Q) -> mspecE P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma mspecE_exI {A Y} (P : Y -> assnE) (m : M St A) (Q : A -> assnE) :
  (forall y, mspecE (P y) m Q) -> mspecE (fun s mo tr => exists y, P y s mo tr) m Q.
Proof. intros H s mo tr [y HP]. exact (H y s mo tr HP). Qed.

Lemma mspecE_pure {A} (P : assnE) (phi : Prop) (m : M St A) (Q : A -> assnE) :
  (phi -> mspecE P m Q) -> mspecE (fun s mo tr => P s mo tr /\ phi) m Q.
Proof. intros H s mo tr [HP Hphi]. exact (H Hphi s mo tr HP). Qed.

Lemma mspecE_pointwise {A} (P : assnE) (m : M St A) (Q : A -> assnE) :
  (forall s mo tr, P s mo tr -> mspecE (fun s' mo' tr' => s' = s /\ mo' = mo /\ tr' = tr) m Q) -> mspecE P m Q.
Proof. intros H s mo tr HP. apply (H s mo tr HP). auto. Qed.

Lemma mspecE_loop {Y R} (body : Y -> M St (Y + R)) (I : Y -> assnE) (Q : R -> assnE) :
  (forall y, mspecE (I y) (body y) (fun r => match r with inl y' => I y' | inr v => Q v end)) ->
  forall fuel y, mspecE (I y) (mloop fuel body y) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros y.
  - apply mspecE_munr.
  - cbn [mloop]. eapply mspecE_bind; [apply Hb|]. intros [y'|v]; [apply IH| apply mspecE_ret; auto].
Qed.

Lemma mspecE_sys {A} (n : node) (dec : resp -> option A) (P : assnE) (Q : A -> assnE) :
  (forall s mo tr, P s mo tr ->
     nprog sel n mo
     /\ (forall code mo', nexit n mo code mo' -> X (tr ++ [ExitEv code (m_fs mo')]))
     /\ (forall rsp mo' evs a, stepR sel n mo rsp mo' evs -> dec rsp = Some a -> Q a s mo' (tr ++ evs))) ->
  mspecE P (msys n dec) Q.
Proof.
  intros H s mo tr HP. destruct (H s mo tr HP) as (Hp & Hx & Hk). unfold msys, enode. cbn.
  split; [exact Hp|]. split; [exact Hx|]. intros rsp mo' evs Hst.
  specialize (Hk rsp mo' evs). destruct (dec rsp) as [a|]; [exact (Hk a Hst eq_refl)| exact I].
Qed.

End MSpecE.
End Logic.

Arguments assnE St : clear implicits.

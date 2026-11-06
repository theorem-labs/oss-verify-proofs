(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qx.
Import ListNotations.
Import X1bs.Exc.

Definition ans_ok (n : node) (rsp : resp) : Prop :=
match n with
| NMmap _ _ _ flags => Z.land flags 16 = 0%Z -> errno_of (eff_ret rsp) = None
| NMprotect _ _ _ => errno_of (eff_ret rsp) = None
| _ => True
end.
Definition ok_all (n : node) (rsp : resp) : Prop := True.

Definition no_enomem (n : node) (mo : Model) : Prop :=
match n with
| NMmap _ _ _ flags => Z.land flags 16 = 0%Z ->
forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
| NMprotect _ _ _ => forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
| _ => True
end.

Lemma ans_ok_of_no_enomem : forall n mo rsp mo' evs, no_enomem n mo -> nstep n mo rsp mo' evs -> ans_ok n rsp.
Proof.
intros n mo rsp mo' evs Hn Hst. destruct n; cbn in *; try exact I.
- intros Hf. exact (Hn Hf _ _ _ Hst).
- exact (Hn _ _ _ Hst).
Qed.

Section G.
Context {ok : node -> resp -> Prop}.

Fixpoint twfG {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
match t with
| Ret r => P r mo
| Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> ok n rsp -> twfG (k rsp) mo' P
end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
twfG t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twfG t mo P'.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
- apply HP. exact H.
- destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst Hok. eapply IH; eauto.
Qed.

Lemma twf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
twfG t mo (fun a mo1 => twfG (f a) mo1 P) -> twfG (X1bs.bind node t f) mo P.
Proof.
intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
- exact H.
- destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst Hok. apply IH. eapply Hk; eauto.
Qed.

Definition etwfG {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
twfG t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
etwfG t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwfG t mo Q'.
Proof.
intros A t mo Q Q' H HQ. unfold etwfG in *. eapply twf_mono; [exact H|].
intros [|a] mo1; cbn; auto.
Qed.

Lemma etwf_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
etwfG t mo (fun a mo1 => etwfG (f a) mo1 Q) -> etwfG (ebind t f) mo Q.
Proof.
intros A B t f mo Q H. unfold etwfG, ebind in *. apply twf_bind.
eapply twf_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

Lemma etwf_ret : forall {A} (a : A) mo (Q : A -> Model -> Prop), Q a mo -> etwfG (Ret (Ok a)) mo Q.
Proof. intros A a mo Q H. exact H. Qed.

Lemma etwf_enode : forall {A} n (pl : resp -> option A) mo (Q : A -> Model -> Prop),
nsafe n mo ->
(forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, pl rsp = Some a /\ Q a mo') ->
etwfG (enode n pl) mo Q.
Proof.
intros A n pl mo Q Hs Hk. unfold etwfG, enode. cbn. split; [exact Hs|].
intros rsp mo' evs Hst _. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

End G.

Arguments twfG ok {R} t mo P.
Arguments etwfG ok {A} t mo Q.

Notation twf := (twfG ans_ok).
Notation etwf := (etwfG ans_ok).
Notation twfU := (twfG ok_all).
Notation etwfU := (etwfG ok_all).

Lemma twfG_weaken : forall ok {R} (t : itree node R) mo P, twfU t mo P -> twfG ok t mo P.
Proof.
intros ok R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact H|].
destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst _. apply IH. exact (Hk rsp mo' evs Hst I).
Qed.

Lemma twfU_tsafe : forall {R} (t : itree node R) mo P, twfU t mo P -> tsafe nstep nsafe t mo.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact I|].
destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH. exact (Hk rsp mo' evs Hst I).
Qed.

Lemma twfU_tpath : forall {R} (t : itree node R) mo P tr r mo',
twfU t mo P -> tpath nstep t mo tr r mo' -> P r mo'.
Proof.
intros R t. induction t as [r0|n k IH]; intros mo P tr r mo' H Hp; cbn in *.
- destruct Hp as (<- & -> & ->). exact H.
- destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
eapply IH; [exact (Hk rsp mo1 evs Hst I)| exact Hp].
Qed.

Lemma etwfU_leaves : forall {A} (t : itree node (exc A)) mo,
etwfU t mo (fun _ _ => False) -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
intros A t mo H. split.
- intros tr r mo' Hp. pose proof (twfU_tpath t mo _ tr r mo' H Hp) as HP. destruct r; exact HP.
- eapply twfU_tsafe. exact H.
Qed.

Lemma twf_tsafe : forall {R} (t : itree node R) mo P,
twf t mo P -> tsafe nstep no_enomem t mo -> tsafe nstep nsafe t mo.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P H Hne; cbn in *; [exact I|].
destruct H as [Hs Hk]. destruct Hne as [Hn Hnk]. split; [exact Hs|]. intros rsp mo' evs Hst.
eapply IH; [eapply Hk; [exact Hst| eapply ans_ok_of_no_enomem; eassumption]| exact (Hnk _ _ _ Hst)].
Qed.

Lemma twf_tpath : forall {R} (t : itree node R) mo P tr r mo',
twf t mo P -> tsafe nstep no_enomem t mo -> tpath nstep t mo tr r mo' -> P r mo'.
Proof.
intros R t. induction t as [r0|n k IH]; intros mo P tr r mo' H Hne Hp; cbn in *.
- destruct Hp as (<- & -> & ->). exact H.
- destruct H as [_ Hk]. destruct Hne as [Hn Hnk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
eapply IH; [eapply Hk; [exact Hst| eapply ans_ok_of_no_enomem; eassumption]| exact (Hnk _ _ _ Hst)| exact Hp].
Qed.

Lemma etwf_leaves : forall {A} (t : itree node (exc A)) mo,
etwf t mo (fun _ _ => False) -> tsafe nstep no_enomem t mo ->
leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
intros A t mo H Hne. split.
- intros tr r mo' Hp. pose proof (twf_tpath t mo _ tr r mo' H Hne Hp) as HP. destruct r; exact HP.
- eapply twf_tsafe; eassumption.
Qed.

Fixpoint twfA {R} (t : itree node R) (P : R -> Prop) : Prop :=
match t with
| Ret r => P r
| Vis n k => forall rsp, ans_ok n rsp -> twfA (k rsp) P
end.

Lemma twfA_mono : forall {R} (t : itree node R) (P P' : R -> Prop), twfA t P -> (forall r, P r -> P' r) -> twfA t P'.
Proof. intros R t. induction t as [r|n k IH]; intros P P' H HP; cbn in *; [auto|]. intros rsp Ha. eapply IH; eauto. Qed.

Lemma twfA_bind : forall {A B} (t : itree node A) (f : A -> itree node B) (P : B -> Prop),
twfA t (fun a => twfA (f a) P) -> twfA (X1bs.bind node t f) P.
Proof. intros A B t. induction t as [r|n k IH]; intros f P H; cbn in *; [exact H|]. intros rsp Ha. apply IH. apply H. exact Ha. Qed.

Lemma twf_conjA : forall {R} (t : itree node R) mo (P : R -> Model -> Prop) (P2 : R -> Prop),
twf t mo P -> twfA t P2 -> twf t mo (fun r mo1 => P r mo1 /\ P2 r).
Proof.
intros R t. induction t as [r|n k IH]; intros mo P P2 H H2; cbn in *; [split; assumption|].
destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst Ha. apply IH; [eapply Hk; eauto| apply H2; exact Ha].
Qed.

Definition etwfA {A} (t : itree node (exc A)) (Q : A -> Prop) : Prop :=
twfA t (fun r => match r with Unr => True | Ok a => Q a end).

Lemma etwfA_mono : forall {A} (t : itree node (exc A)) (Q Q' : A -> Prop), etwfA t Q -> (forall a, Q a -> Q' a) -> etwfA t Q'.
Proof. intros A t Q Q' H HQ. unfold etwfA in *. eapply twfA_mono; [exact H|]. intros [|a]; cbn; auto. Qed.

Lemma etwfA_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q,
etwfA t (fun a => etwfA (f a) Q) -> etwfA (ebind t f) Q.
Proof.
intros A B t f Q H. unfold etwfA, ebind in *. apply twfA_bind.
eapply twfA_mono; [exact H|]. intros [|a] Ha; cbn; [exact I| exact Ha].
Qed.

Lemma etwfA_enode : forall {A} n (pl : resp -> option A) (Q : A -> Prop),
(forall rsp a, ans_ok n rsp -> pl rsp = Some a -> Q a) -> etwfA (enode n pl) Q.
Proof.
intros A n pl Q H. unfold etwfA, enode. cbn. intros rsp Ha. specialize (H rsp).
destruct (pl rsp) as [a|]; cbn; [exact (H a Ha eq_refl)| exact I].
Qed.

Lemma etwf_conjA : forall {A} (t : itree node (exc A)) mo (Q : A -> Model -> Prop) (Q2 : A -> Prop),
etwf t mo Q -> etwfA t Q2 -> etwf t mo (fun a mo1 => Q a mo1 /\ Q2 a).
Proof.
intros A t mo Q Q2 H H2. unfold etwfG, etwfA in *.
eapply twf_mono; [exact (twf_conjA t mo _ _ H H2)|]. intros [|a] mo1 [H1 H3]; cbn in *; [exact H1| split; assumption].
Qed.

Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Section GM.
Context {ok : node -> resp -> Prop}.

Definition mspecG {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
forall s mo, P s mo -> etwfG ok (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Local Notation mspec := mspecG.

#[using="Type"] Lemma mspec_ret {A} (a : A) (P : assn) (Q : A -> assn) :
(forall s mo, P s mo -> Q a s mo) -> mspec P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

#[using="Type"] Lemma mspec_bind {A B} (m : M St A) (f : A -> M St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (mbind m f) Q.
Proof.
intros Hm Hf s mo HP. unfold mbind. apply etwf_ebind.
eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

#[using="Type"] Lemma mspec_conseq {A} (m : M St A) (P P' : assn) (Q Q' : A -> assn) :
mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P' m Q'.
Proof.
intros Hm HP HQ s mo HP'. eapply etwf_mono; [exact (Hm s mo (HP _ _ HP'))|].
intros [a s1] mo1; cbn; auto.
Qed.

#[using="Type"] Lemma mspec_pre {A} (m : M St A) (P P' : assn) (Q : A -> assn) :
mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> mspec P' m Q.
Proof. intros Hm HP. eapply mspec_conseq; eauto. Qed.

#[using="Type"] Lemma mspec_post {A} (m : M St A) (P : assn) (Q Q' : A -> assn) :
mspec P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P m Q'.
Proof. intros Hm HQ. eapply mspec_conseq; eauto. Qed.

#[using="Type"] Lemma mspec_munr {A} (Q : A -> assn) : mspec (fun _ _ => False) munr Q.
Proof. intros s mo []. Qed.

#[using="Type"] Lemma mspec_false {A} (m : M St A) (Q : A -> assn) : mspec (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

#[using="Type"] Lemma mspec_get (P : assn) : mspec P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

#[using="Type"] Lemma mspec_put (P : assn) (s1 : St) : mspec P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

#[using="Type"] Lemma mspec_upd (P : assn) (f : St -> St) : mspec P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

#[using="Type"] Lemma mspec_upd' (P : assn) (Q : unit -> assn) (f : St -> St) :
(forall s mo, P s mo -> Q tt (f s) mo) -> mspec P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

#[using="Type"] Lemma mspec_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
(forall s mo, P s mo ->
nsafe n mo /\
forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
mspec P (msys n dec) Q.
Proof.
intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
intros rsp mo' evs Hst _. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

#[using="Type"] Lemma mspec_if {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
(b = true -> mspec P m1 Q) -> (b = false -> mspec P m2 Q) -> mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

#[using="Type"] Lemma mspec_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
mspec (fun s mo => P s mo /\ b = true) m1 Q -> mspec (fun s mo => P s mo /\ b = false) m2 Q ->
mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

#[using="Type"] Lemma mspec_exI {A X} (P : X -> assn) (m : M St A) (Q : A -> assn) :
(forall x, mspec (P x) m Q) -> mspec (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

#[using="Type"] Lemma mspec_pure {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
(phi -> mspec P m Q) -> mspec (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

#[using="Type"] Lemma mspec_pure_l {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
(phi -> mspec P m Q) -> mspec (fun s mo => phi /\ P s mo) m Q.
Proof. intros H s mo [Hphi HP]. exact (H Hphi s mo HP). Qed.

#[using="Type"] Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
(forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

#[using="Type"] Lemma mspec_when (b : bool) (m : M St unit) (P : assn) (Q : unit -> assn) :
(b = true -> mspec P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspec P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspec_ret. apply H2. reflexivity. Qed.

#[using="Type"] Lemma mspec_loop {X R} (body : X -> M St (X + R)) (I : X -> assn) (Q : R -> assn) (meas : X -> nat) :
(forall x, mspec (I x) (body x)
(fun r s mo => match r with
| inl x' => I x' s mo /\ (meas x' < meas x)%nat
| inr v => Q v s mo
end)) ->
forall fuel x, (meas x < fuel)%nat -> mspec (I x) (mloop fuel body x) Q.
Proof.
intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
cbn [mloop]. eapply mspec_bind; [apply Hb|].
intros [x'|v]; cbn.
- intros s mo [HI Hm]. apply (IH x'); [lia| exact HI].
- apply mspec_ret. auto.
Qed.

#[using="Type"] Lemma mspec_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
mspec P m (fun _ => R) -> (forall a, mspec R (f a) Q) -> mspec P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspec_bind; [exact Hm|]. intros a. apply Hf. Qed.

End GM.

#[using="Type"] Lemma mspecG_weaken ok {A} (P : assn) (m : M St A) (Q : A -> assn) : mspecG (ok:=ok_all) P m Q -> mspecG (ok:=ok) P m Q.
Proof. intros H s mo HP. apply twfG_weaken. exact (H s mo HP). Qed.

#[using="Type"] Lemma mspec_program {A} (P : assn) (m : M St A) s mo :
mspecG (ok:=ans_ok) P m (fun _ _ _ => False) -> P s mo ->
forall {B} (f : A * St -> itree node (exc B)),
tsafe nstep no_enomem (ebind (m s) f) mo ->
leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
intros Hm HP B f Hne. apply etwf_leaves; [| exact Hne]. apply etwf_ebind.
eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.

#[using="Type"] Lemma mspecU_program {A} (P : assn) (m : M St A) s mo :
mspecG (ok:=ok_all) P m (fun _ _ _ => False) -> P s mo ->
forall {B} (f : A * St -> itree node (exc B)),
leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
intros Hm HP B f. apply etwfU_leaves. apply etwf_ebind.
eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.

Definition mspecA {A} (m : M St A) (Q : A -> Prop) : Prop := forall s, etwfA (m s) (fun p => Q (fst p)).

#[using="Type"] Lemma mspecA_ret {A} (a : A) (Q : A -> Prop) : Q a -> mspecA (mret a) Q.
Proof. intros H s. exact H. Qed.

#[using="Type"] Lemma mspecA_munr {A} (Q : A -> Prop) : mspecA munr Q.
Proof. intros s. exact I. Qed.

#[using="Type"] Lemma mspecA_true {A} (m : M St A) : mspecA m (fun _ => True).
Proof.
intros s. unfold etwfA. generalize (m s). intros t. induction t as [[|a]|n k IH]; cbn; auto.
Qed.

#[using="Type"] Lemma mspecA_bind {A B} (m : M St A) (f : A -> M St B) (Q1 : A -> Prop) (Q : B -> Prop) :
mspecA m Q1 -> (forall a, Q1 a -> mspecA (f a) Q) -> mspecA (mbind m f) Q.
Proof.
intros Hm Hf s. unfold mbind. apply etwfA_ebind.
eapply etwfA_mono; [exact (Hm s)|]. intros [a s1] H1. cbn in *. exact (Hf a H1 s1).
Qed.

#[using="Type"] Lemma mspecA_post {A} (m : M St A) (Q Q' : A -> Prop) : mspecA m Q -> (forall a, Q a -> Q' a) -> mspecA m Q'.
Proof. intros Hm HQ s. eapply etwfA_mono; [exact (Hm s)|]. intros [a s1]; cbn; auto. Qed.

#[using="Type"] Lemma mspecA_if {A} (b : bool) (m1 m2 : M St A) Q :
(b = true -> mspecA m1 Q) -> (b = false -> mspecA m2 Q) -> mspecA (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

#[using="Type"] Lemma mspecA_sys {A} (n : node) (dec : resp -> option A) (Q : A -> Prop) :
(forall rsp a, ans_ok n rsp -> dec rsp = Some a -> Q a) -> mspecA (msys n dec) Q.
Proof.
intros H s. unfold msys. apply etwfA_enode. intros rsp [a s'] Ha E. cbn [fst].
destruct (dec rsp) as [a'|] eqn:Ed; [|discriminate]. injection E as <- <-. exact (H rsp a' Ha Ed).
Qed.

#[using="Type"] Lemma mspec_conjA {A} (P : assn) (m : M St A) (Q : A -> assn) (Q2 : A -> Prop) :
mspecG (ok:=ans_ok) P m Q -> mspecA m Q2 -> mspecG (ok:=ans_ok) P m (fun a s mo => Q a s mo /\ Q2 a).
Proof.
intros H H2 s mo HP. eapply etwf_mono; [exact (etwf_conjA _ _ _ _ (H s mo HP) (H2 s))|].
intros [a s1] mo1; cbn; auto.
Qed.

#[using="Type"] Lemma mspec_some {A} (P : assn) (m : M St (option A)) (Q : option A -> assn) :
mspecG (ok:=ans_ok) P m Q -> mspecA m (fun r => r <> None) ->
mspecG (ok:=ans_ok) P m (fun r s mo => match r with Some _ => Q r s mo | None => False end).
Proof.
intros H H2. eapply mspec_post; [exact (mspec_conjA _ _ _ _ H H2)|]. intros [a|] s mo [HQ Hn]; [exact HQ| congruence].
Qed.

End MSpec.

Arguments assn St : clear implicits.
Arguments mspecG {St} ok {A} P m Q.
Arguments mspecA {St A} m Q.

Notation mspec := (mspecG ans_ok).
Notation mspecU := (mspecG ok_all).

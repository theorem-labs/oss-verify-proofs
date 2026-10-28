(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnModel BnTree.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Safe.
Context {ptr : Type}.

Fixpoint safe {A} (t : btree ptr A) (X : @blocks ptr) (Q : A -> @blocks ptr -> Prop) : Prop :=
  match t with
  | TRet a => Q a X
  | TUnr => False
  | TMalloc n k => ok_bn X n /\ forall p, ~ In p (map fst X) -> safe (k (Some p)) ((p, n) :: X) Q
  | TFree p k => exists m X', Permutation X ((p, m) :: X') /\ safe k X' Q
  end.

Lemma safe_of_wp : forall {A} (t : btree ptr A) X Q, wp t X Q -> safe t X Q.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q H; cbn [wp safe] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & _ & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

Lemma safe_mono : forall {A} (t : btree ptr A) X (Q Q' : A -> @blocks ptr -> Prop),
  safe t X Q -> (forall a X', Q a X' -> Q' a X') -> safe t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q Q' H HQ; cbn [safe] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. eapply IH; [apply H; exact Hq| exact HQ].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. eapply IH; [exact H| exact HQ].
Qed.

Lemma safe_bind : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) X Q,
  safe m X (fun a X' => safe (f a) X' Q) -> safe (tbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH]; intros f X Q H; cbn [safe tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

Lemma safe_bind_inv : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) X Q,
  safe (tbind m f) X Q -> safe m X (fun a X' => safe (f a) X' Q).
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH]; intros f X Q H; cbn [safe tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma safe_leaves : forall {A} (t : btree ptr A) (phi : A -> Prop) X Q,
  leaves t phi -> safe t X Q -> safe t X (fun a X' => Q a X' /\ phi a).
Proof.
  intros A t phi. induction t as [a| |n k IH|p k IH]; intros X Q HL H; cbn [safe leaves] in *.
  - split; [exact H | exact HL].
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH; [apply HL | apply H; exact Hq].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH; [exact HL | exact H].
Qed.

End Safe.

(* [comment removed for export] *)
Lemma bptr_fresh : forall l : list bptr, exists p : bptr, ~ In p l.
Proof.
  intros l.
  assert (H : forall l : list bptr, exists z : Z, forall q, In q l -> snd q < z).
  { induction l0 as [|q l0 [z Hz]]; [exists 0; intros q []|].
    exists (Z.max z (snd q + 1)). intros q' [<-|Hin]; [lia| specialize (Hz q' Hin); lia]. }
  destruct (H l) as [z Hz]. exists ((0%N, 0), z). intros Hin. specialize (Hz _ Hin). cbn in Hz. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ImplA.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
(* [comment removed for export] *)
Local Notation PMc := (@ar_PMc AR).
Local Notation PMc_ms := (@ar_PMc_ms AR).

Definition implA {A} (t : btree bptr A) (Σ : rts RT) (Q : A -> rts RT -> machine_state -> Prop) (ms : machine_state) : Prop :=
  forall (X : @blocks bptr) (Φ : A -> @blocks bptr -> Prop), safe t X Φ ->
    cps bsegs (ASTA RT Σ PMc (eq ms)) (fun c => exists a X' Σ', Φ a X' /\ ASTA RT Σ' PMc (Q a Σ') c).

Lemma PMc_mat_stable : forall Σ, mat_stable (fun mo => ARTM RT Σ mo /\ PMc mo).
Proof. intros Σ. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact PMc_ms]. Qed.

(* [comment removed for export] *)
Lemma asta_evtA : forall Σ Pm Q, (forall ms, Pm ms -> evt bsegs Q ms) ->
  cps bsegs (ASTA RT Σ PMc Pm) (ASTA RT Σ PMc Q).
Proof.
  intros Σ Pm Q H. unfold ASTA.
  apply (ast_evt bsegs SEGTOP_A asegs_wx asegs_below); [apply PMc_mat_stable| exact H].
Qed.

Lemma implA_evt : forall {A} (t : btree bptr A) Σ Q (P : machine_state -> Prop) ms,
  evt bsegs P ms -> (forall ms', P ms' -> implA t Σ Q ms') -> implA t Σ Q ms.
Proof.
  intros A t Σ Q P ms HE HK X Φ S T c Hc Hk.
  apply (asta_evtA Σ (eq ms) P ltac:(intros ms0 <-; exact HE) T c Hc).
  intros c' Hc'. destruct (ASTA_unpack RT Σ PMc P c' Hc') as (ms' & HP & Hc'').
  exact (HK ms' HP X Φ S T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma cps_from_evt : forall Σ (P : machine_state -> Prop) (Q : config -> Prop) ms,
  evt bsegs P ms -> (forall ms', P ms' -> cps bsegs (ASTA RT Σ PMc (eq ms')) Q) -> cps bsegs (ASTA RT Σ PMc (eq ms)) Q.
Proof.
  intros Σ P Q ms HE HK T c Hc Hk.
  apply (asta_evtA Σ (eq ms) P ltac:(intros ms0 <-; exact HE) T c Hc).
  intros c' Hc'. destruct (ASTA_unpack RT Σ PMc P c' Hc') as (ms' & HP & Hc'').
  exact (HK ms' HP T c' Hc'' Hk).
Qed.

Lemma cps_from_evt' : forall Σ (Q : config -> Prop) ms,
  evt bsegs (fun ms' => cps bsegs (ASTA RT Σ PMc (eq ms')) Q) ms -> cps bsegs (ASTA RT Σ PMc (eq ms)) Q.
Proof. intros Σ Q ms H. eapply cps_from_evt; [exact H|]. intros ms' H'. exact H'. Qed.

(* [comment removed for export] *)
Lemma cps_step_same : forall Σ ms (R : machine_state -> Prop) (Q : config -> Prop),
  cps bsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R) ->
  (forall ms', R ms' -> cps bsegs (ASTA RT Σ PMc (eq ms')) Q) ->
  cps bsegs (ASTA RT Σ PMc (eq ms)) Q.
Proof.
  intros Σ ms R Q H1 H2. eapply cps_seq; [exact H1|]. intros T c Hc Hk.
  destruct (ASTA_unpack RT Σ PMc R c Hc) as (ms' & HR & Hc'). exact (H2 ms' HR T c Hc' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_from_evt : forall {A} (t : btree bptr A) Σ Q ms,
  evt bsegs (fun ms' => implA t Σ Q ms') ms -> implA t Σ Q ms.
Proof. intros A t Σ Q ms H. eapply implA_evt; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implA_ret : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  Q a Σ ms -> implA (TRet a) Σ Q ms.
Proof.
  intros A a Σ Q ms HQ X Φ S T c Hc Hk. cbn [safe] in S. apply Hk. exists a, X, Σ. split; [exact S|].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. exact HQ.
Qed.

Lemma implA_ret_evt : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  evt bsegs (Q a Σ) ms -> implA (TRet a) Σ Q ms.
Proof. intros A a Σ Q ms H. eapply implA_evt; [exact H|]. intros ms' HQ. apply implA_ret. exact HQ. Qed.

Lemma implA_unr : forall {A} Σ (Q : A -> rts RT -> machine_state -> Prop) ms, implA TUnr Σ Q ms.
Proof. intros A Σ Q ms X Φ []. Qed.

Lemma implA_mono : forall {A} (t : btree bptr A) Σ (Q Q' : A -> rts RT -> machine_state -> Prop) ms,
  implA t Σ Q ms -> (forall a Σ' ms', Q a Σ' ms' -> Q' a Σ' ms') -> implA t Σ Q' ms.
Proof.
  intros A t Σ Q Q' ms H HQ X Φ S T c Hc Hk. apply (H X Φ S T c Hc).
  intros c' (a & X' & Σ' & HΦ & Hc'). apply Hk. exists a, X', Σ'. split; [exact HΦ|].
  eapply ASTA_conseq; [exact Hc'|]. intros ms0. apply HQ.
Qed.

(* [comment removed for export] *)
Lemma implA_bind : forall {A B} (m : btree bptr A) (f : A -> btree bptr B) Σ Q1 Q ms,
  implA m Σ Q1 ms ->
  (forall a Σ' ms', Q1 a Σ' ms' -> implA (f a) Σ' Q ms') ->
  implA (tbind m f) Σ Q ms.
Proof.
  intros A B m f Σ Q1 Q ms Hm Hf X Φ S T c Hc Hk.
  apply safe_bind_inv in S.
  apply (Hm X (fun a X' => safe (f a) X' Φ) S T c Hc).
  intros c' (a & X' & Σ' & S' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HQ1 & Hc'').
  exact (Hf a Σ' ms' HQ1 X' Φ S' T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_step : forall {A} (t : btree bptr A) Σ Q ms (R : rts RT -> machine_state -> Prop),
  cps bsegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c) ->
  (forall Σ' ms', R Σ' ms' -> implA t Σ' Q ms') ->
  implA t Σ Q ms.
Proof.
  intros A t Σ Q ms R H1 H2 X Φ S T c Hc Hk.
  apply (H1 T c Hc). intros c' (Σ' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  exact (H2 Σ' ms' HR X Φ S T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_step_same : forall {A} (t : btree bptr A) Σ Q ms (R : machine_state -> Prop),
  cps bsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R) ->
  (forall ms', R ms' -> implA t Σ Q ms') ->
  implA t Σ Q ms.
Proof.
  intros A t Σ Q ms R H1 H2. eapply (implA_step t Σ Q ms (fun Σ' ms' => Σ' = Σ /\ R ms')).
  - eapply cps_conseq; [exact H1 | intros c Hc; exact Hc |]. intros c Hc. exists Σ.
    eapply ASTA_conseq; [exact Hc|]. intros ms0 HR. split; [reflexivity | exact HR].
  - intros Σ' ms' [-> HR]. exact (H2 ms' HR).
Qed.

(* [comment removed for export] *)
Lemma implA_malloc : forall {A} n (k : option bptr -> btree bptr A) Σ Q ms (avoid : list bptr) (R : rts RT -> machine_state -> Prop),
  (0 <= n <= BSZ -> cps bsegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c)) ->
  (forall p Σ' ms', 0 <= n <= BSZ -> ~ In p avoid -> R Σ' ms' -> implA (k (Some p)) Σ' Q ms') ->
  implA (TMalloc n k) Σ Q ms.
Proof.
  intros A n k Σ Q ms avoid R H1 H2 X Φ S T c Hc Hk. cbn [safe] in S. destruct S as ((_ & Hn & _) & S).
  apply (H1 Hn T c Hc). intros c' (Σ' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  destruct (bptr_fresh (avoid ++ map fst X)) as [p Hp].
  assert (Hp1 : ~ In p avoid) by (intros Hin; apply Hp; apply in_or_app; left; exact Hin).
  assert (Hp2 : ~ In p (map fst X)) by (intros Hin; apply Hp; apply in_or_app; right; exact Hin).
  exact (H2 p Σ' ms' Hn Hp1 HR ((p, n) :: X) Φ (S p Hp2) T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_free : forall {A} p (k : btree bptr A) Σ Q ms (R : rts RT -> machine_state -> Prop),
  cps bsegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c) ->
  (forall Σ' ms', R Σ' ms' -> implA k Σ' Q ms') ->
  implA (TFree p k) Σ Q ms.
Proof.
  intros A p k Σ Q ms R H1 H2 X Φ S T c Hc Hk. cbn [safe] in S. destruct S as (m0 & X' & _ & S).
  apply (H1 T c Hc). intros c' (Σ' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  exact (H2 Σ' ms' HR X' Φ S T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implA_leaves : forall {A} (t : btree bptr A) (phi : A -> Prop) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  leaves t phi -> implA t Σ Q ms -> implA t Σ (fun a Σ' ms' => Q a Σ' ms' /\ phi a) ms.
Proof.
  intros A t phi Σ Q ms HL H X Φ S T c Hc Hk.
  apply (H X (fun a X' => Φ a X' /\ phi a) (safe_leaves t phi X Φ HL S) T c Hc).
  intros c' (a & X' & Σ' & (HΦ & Hphi) & Hc'). apply Hk. exists a, X', Σ'. split; [exact HΦ|].
  eapply ASTA_conseq; [exact Hc'|]. intros ms0 HQ. split; [exact HQ | exact Hphi].
Qed.

Lemma implA_run : forall {A} (t : btree bptr A) Σ Q ms X (Φ : A -> @blocks bptr -> Prop),
  implA t Σ Q ms -> wp t X Φ ->
  cps bsegs (ASTA RT Σ PMc (eq ms)) (fun c => exists a X' Σ', Φ a X' /\ ASTA RT Σ' PMc (Q a Σ') c).
Proof. intros A t Σ Q ms X Φ H W. exact (H X Φ (safe_of_wp t X Φ W)). Qed.

End ImplA.

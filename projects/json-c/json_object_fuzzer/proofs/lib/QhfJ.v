(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Inv.
Context {R : Type} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat).

#[using="Type"] Lemma ecost_nonneg e : esz_ok e -> 0 <= ecost e.
Proof.
destruct e; cbn; intros H; try lia.
- destruct (addr =? 0); unfold PGSZ; lia.
- destruct (is_fixed flags); [unfold PGSZ; lia|]. destruct (H eq_refl) as [A B]. pose proof (QYTG.Mq0.round_up_pg_ge len). lia.
Qed.

#[using="Type"] Lemma KSUM_W_floor L t κ W D : KSUM isS P Wf Df L t κ W D -> Wf <= W.
Proof. intros H. destruct H; try lia. pose proof (ecost_nonneg e H0). lia. Qed.

#[using="Type"] Lemma KSUM_ret_inv' L (r : R) κ W D : KSUM isS P Wf Df L (SRet r) κ W D -> κ = ksingle (isS r) /\ Wf <= W /\ (Df <= D)%nat /\ P r.
Proof. intros H. inversion H; subst; auto. Qed.

#[using="Type"] Lemma KSUM_peek_inv L p c h k κ W D : KSUM isS P Wf Df L (SVis (EPeek p c h) k) κ W D ->
Wf <= W /\ forall v, 0 <= v < 256 -> KSUM isS P Wf Df L (k v) κ W D.
Proof. intros H. inversion H; subst; [discriminate| auto]. Qed.

#[using="Type"] Lemma KSUM_vis_inv L e k κ W D : KSUM isS P Wf Df L (SVis e k) κ W D -> is_peek e = false ->
exists kf kt W0 D0, eks e = true /\ esz_ok e /\ Wf <= W0 /\ W = W0 + ecost e /\ D = S D0
/\ (forall z, answer_ok L e z = true -> eclass e z = false -> KSUM isS P Wf Df (event_post L e z) (k z) kf W0 D0)
/\ (forall z, answer_ok L e z = true -> eclass e z = true  -> KSUM isS P Wf Df (event_post L e z) (k z) kt W0 D0)
/\ (egrant e = false -> kt = kf)
/\ κ = (if egrant e then kt else kf).
Proof. intros H NP. inversion H; subst; [| discriminate]. exists kf, kt, W0, D0. repeat match goal with |- _ /\ _ => split end; auto. Qed.
End Inv.

#[using="Type"] Lemma KSUM_strel {R1 R2} (isS1 : R1 -> bool) (isS2 : R2 -> bool) (P1 : R1 -> Prop) (P2 : R2 -> Prop) (Wf : Z) (Df : nat) (RR : R1 -> R2 -> Prop) t1 t2 :
strel RR t1 t2 -> (forall r1 r2, RR r1 r2 -> isS1 r1 = isS2 r2) -> (forall r1 r2, RR r1 r2 -> P1 r1 -> P2 r2) ->
forall L κ W D, KSUM isS1 P1 Wf Df L t1 κ W D -> KSUM isS2 P2 Wf Df L t2 κ W D.
Proof.
intros H HR HP. induction H as [r1 r2 Hr| e k1 k2 Hk IH]; intros L κ W D K.
- apply KSUM_ret_inv' in K as (-> & HW & HD & HP1). rewrite (HR _ _ Hr). constructor; [exact (HP _ _ Hr HP1)| exact HW| exact HD].
- destruct (is_peek e) eqn:EP.
+ destruct e; cbn in EP; try discriminate. apply KSUM_peek_inv in K as [HW K]. apply ks_peek; [exact HW|]. intros v Hv. apply IH. apply K. exact Hv.
+ apply KSUM_vis_inv in K as (kf & kt & W0 & D0 & EK & SZ & HW & -> & -> & Hf & Ht & Hle & ->); [| exact EP].
constructor; auto.
Qed.

Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

#[using="Hpans"] Lemma KSUM_prun {R} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat) : forall (t : M R) L κ W D o,
KSUM isS P Wf Df L t κ W D -> KSUM (fun x : O * R => isS (snd x)) (fun x => P (snd x)) Wf Df L (prun pans pupd o t) κ W D.
Proof.
induction t as [r|e k IH]; intros L κ W D o K.
- apply KSUM_ret_inv' in K as (-> & HW & HD & HP). unfold prun. rewrite eruns_ret. constructor; [exact HP| exact HW| exact HD].
- unfold prun. destruct (is_peek e) eqn:EP.
+ destruct e; cbn in EP; try discriminate. apply KSUM_peek_inv in K as [HW K]. cbn [eruns psel]. apply IH. apply K. apply Hpans.
+ apply KSUM_vis_inv in K as (kf & kt & W0 & D0 & EK & SZ & HW & -> & -> & Hf & Ht & Hle & ->); [| exact EP].
destruct e; cbn in EP; try discriminate; cbn [eruns psel]; constructor; auto; intros z A C; apply IH; auto.
Qed.
End PRUN.

#[using="Type"] Lemma KSUM_sbind_ret {R S} (isS1 : R -> bool) (isS2 : S -> bool) (P1 : R -> Prop) (P2 : S -> Prop) (Wf : Z) (Df : nat) (g : R -> S) :
(forall r, isS2 (g r) = isS1 r) -> (forall r, P1 r -> P2 (g r)) ->
forall (t : M R) L κ W D, KSUM isS1 P1 Wf Df L t κ W D -> KSUM isS2 P2 Wf Df L (sbind t (fun r => SRet (g r))) κ W D.
Proof.
intros Hg HP t. induction t as [r|e k IH]; intros L κ W D K; cbn [sbind].
- apply KSUM_ret_inv' in K as (-> & HW & HD & HP1). rewrite <- Hg. constructor; [exact (HP _ HP1)| exact HW| exact HD].
- destruct (is_peek e) eqn:EP.
+ destruct e; cbn in EP; try discriminate. apply KSUM_peek_inv in K as [HW K]. apply ks_peek; [exact HW|]. intros v Hv. apply IH. apply K. exact Hv.
+ apply KSUM_vis_inv in K as (kf & kt & W0 & D0 & EK & SZ & HW & -> & -> & Hf & Ht & Hle & ->); [| exact EP].
constructor; auto.
Qed.

#[using="Type"] Lemma KSUM_sbind_same {R S} (isS1 : R -> bool) (isS2 : S -> bool) (P1 : R -> Prop) (P2 : S -> Prop) (Wf : Z) (Df : nat) (f : R -> M S) :
(forall L r W D, P1 r -> Wf <= W -> (Df <= D)%nat -> KSUM isS2 P2 Wf Df L (f r) (ksingle (isS1 r)) W D) ->
forall (t : M R) L κ W D, KSUM isS1 P1 Wf Df L t κ W D -> KSUM isS2 P2 Wf Df L (sbind t f) κ W D.
Proof.
intros Hf t. induction t as [r|e k IH]; intros L κ W D K; cbn [sbind].
- apply KSUM_ret_inv' in K as (-> & HW & HD & HP1). apply Hf; [exact HP1| exact HW| exact HD].
- destruct (is_peek e) eqn:EP.
+ destruct e; cbn in EP; try discriminate. apply KSUM_peek_inv in K as [HW K]. apply ks_peek; [exact HW|]. intros v Hv. apply IH. apply K. exact Hv.
+ apply KSUM_vis_inv in K as (kf & kt & W0 & D0 & EK & SZ & HW & -> & -> & Hf' & Ht & Hle & ->); [| exact EP].
constructor; auto.
Qed.

#[using="Type"] Lemma rd8_ks {R} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat) L st q (k : Z -> M R) κ W D :
Wf <= W -> (forall v, KSUM isS P Wf Df L (k v) κ W D) -> KSUM isS P Wf Df L (rd8 st q k) κ W D.
Proof.
intros HW H. unfold rd8. destruct (cell_read _ _) as [v|h].
- apply H.
- apply ks_peek; [exact HW|]. intros v Hv. unfold peek_answer_ok.
destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H.
Qed.

#[using="Type"] Lemma rd16_ks {R} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat) L st q (k : Z -> M R) κ W D :
Wf <= W -> (forall v, KSUM isS P Wf Df L (k v) κ W D) -> KSUM isS P Wf Df L (rd16 st q k) κ W D.
Proof. intros HW H. unfold rd16. apply rd8_ks; [exact HW|]. intros b0. apply rd8_ks; [exact HW|]. intros b1. apply H. Qed.

End RC__1.

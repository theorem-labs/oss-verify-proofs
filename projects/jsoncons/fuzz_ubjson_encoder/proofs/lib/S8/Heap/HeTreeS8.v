(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMTREE.
Context {RUNp : RunP}.

Fixpoint apw {R} (w : ev -> Z) (t : M R) (c : Z) (n : nat) (Q : Z -> nat -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Q c n r
  | SVis (EUndef _) _ => True
  | SVis e k => forall z, apw w (k z) (c + w e) (S n) Q
  end.

Inductive cpathw {R} (w : ev -> Z) : mled -> M R -> mled -> R -> Z -> nat -> Prop :=
| cpw_ret L r : cpathw w L (SRet r) L r 0 0
| cpw_vis L e k z L' r c n :
    answer_ok L e z = true -> cpathw w (event_post L e z) (k z) L' r c n -> cpathw w L (SVis e k) L' r (w e + c) (S n).

Definition evfit (lim : Z) (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap a len prot flags => if (prot =? PROT_RW) && (a =? 0) then is_err z = false -> mmap_len len <= lim else True
  | _ => True
  end.

Inductive cpathf {R} (lim : Z) (w : ev -> Z) : mled -> M R -> mled -> R -> Z -> nat -> Prop :=
| cpf_ret L r : cpathf lim w L (SRet r) L r 0 0
| cpf_vis L e k z L' r c n :
    answer_ok L e z = true -> evfit lim e z -> cpathf lim w (event_post L e z) (k z) L' r c n -> cpathf lim w L (SVis e k) L' r (w e + c) (S n).

Lemma cpathf_cpathw {R} (lim : Z) (w : ev -> Z) : forall (t : M R) L L' r c n, cpathf lim w L t L' r c n -> cpathw w L t L' r c n.
Proof. intros t L L' r c n P. induction P; econstructor; eauto. Qed.

Lemma cmalloc_big_fit (lim : Z) (w : ev -> Z) : forall cs n L L' cs' p c k,
  MMAP_THRESHOLD <= n -> size_overflows n = false ->
  cpathf lim w L (cmalloc cs n) L' (cs', Some p) c k -> mmap_len (n + IB + UNIT) <= lim.
Proof.
  intros cs n L L' cs' p c k Hn Hso P. unfold cmalloc, malloc_core in P. rewrite Hso in P.
  replace (MMAP_THRESHOLD <=? n) with true in P by (symmetry; apply Z.leb_le; exact Hn).
  cbn [sbind] in P. inversion P as [|L0 e0 k0 z L0' r0 c0 n0 Hans Hfit P']; subst. clear P.
  cbn [evfit] in Hfit. change (PROT_RW =? PROT_RW) with true in Hfit. change (0 =? 0) with true in Hfit. cbn [andb] in Hfit.
  apply Hfit. clear Hfit.
  destruct (is_err z) eqn:Ez; [exfalso| reflexivity].
  destruct (negb (mmap_answer_ok (live_ranges cs) (n + IB + UNIT) z)).
  - unfold bad_answer in P'. cbn [sbind] in P'. inversion P' as [|L1 e1 k1 z1 L1' r1 c1 n1 Hans1 _ _]; subst. cbn in Hans1. discriminate.
  - unfold ret in P'. cbn [sbind] in P'. inversion P'.
Qed.

Lemma apw_cpathw {R} (w : ev -> Z) : forall (t : M R) L L' r c n, cpathw w L t L' r c n ->
  forall c0 n0 Q, apw w t c0 n0 Q -> Q (c0 + c) (n0 + n)%nat r.
Proof.
  intros t L L' r c n P. induction P as [L r|L e k z L' r c n Hz P IH]; intros c0 n0 Q H.
  - cbn in H. replace (c0 + 0) with c0 by lia. replace (n0 + 0)%nat with n0 by lia. exact H.
  - destruct e; try (cbn in Hz; discriminate);
      (cbn in H; specialize (IH _ _ _ (H z));
       rewrite Z.add_assoc, Nat.add_succ_r; exact IH).
Qed.

Lemma cpathw_cpath {R} (w : ev -> Z) : forall (t : M R) L L' r, cpath L t L' r -> exists c n, cpathw w L t L' r c n.
Proof.
  intros t L L' r P. induction P as [L r|L e k z L' r Hz P IH].
  - exists 0, 0%nat. constructor.
  - destruct IH as (c & n & IH). exists (w e + c), (S n). econstructor; eauto.
Qed.

Lemma cpathw_any {R} (w1 w2 : ev -> Z) : forall (t : M R) L L' r c n, cpathw w1 L t L' r c n -> exists c', cpathw w2 L t L' r c' n.
Proof.
  intros t L L' r c n P. induction P as [L r|L e k z L' r c n Hz P IH].
  - exists 0. constructor.
  - destruct IH as (c' & IH). exists (w2 e + c'). econstructor; eauto.
Qed.

Lemma cpathw_cpath_inv {R} (w : ev -> Z) : forall (t : M R) L L' r c n, cpathw w L t L' r c n -> cpath L t L' r.
Proof. intros t L L' r c n P. induction P; econstructor; eauto. Qed.

Lemma apw_mono {R} (w : ev -> Z) (Q Q' : Z -> nat -> R -> Prop) :
  (forall c n r, Q c n r -> Q' c n r) -> forall t c n, apw w t c n Q -> apw w t c n Q'.
Proof.
  intros HQ. induction t as [r|e k IH]; intros c n H; cbn in *; [auto|].
  destruct e; try exact I; intros z; apply IH; apply H.
Qed.

Lemma apw_ret {R} (w : ev -> Z) (r : R) c n Q : Q c n r -> apw w (SRet r) c n Q.
Proof. intros H. exact H. Qed.

Lemma apw_undef {R} (w : ev -> Z) why (k : Z -> M R) c n Q : apw w (SVis (EUndef why) k) c n Q.
Proof. exact I. Qed.

Lemma apw_bad {R} (w : ev -> Z) (b : M R) c n Q : apw w (bad_answer b) c n Q.
Proof. exact I. Qed.

Lemma apw_vis {R} (w : ev -> Z) e (k : Z -> M R) c n Q :
  (forall z, apw w (k z) (c + w e) (S n) Q) -> apw w (SVis e k) c n Q.
Proof. intros H. destruct e; cbn; auto. Qed.

Lemma apw_guard {R} (w : ev -> Z) tag (b : bool) (k bail : M R) c n Q :
  (b = true -> apw w k c n Q) -> apw w (guard tag b k bail) c n Q.
Proof. intros H. unfold guard. destruct b; [apply H; reflexivity| exact I]. Qed.

Lemma apw_bind {R S} (w : ev -> Z) : forall (t : M R) (f : R -> M S) c n (P : Z -> nat -> R -> Prop) Q,
  apw w t c n P -> (forall c' n' r, P c' n' r -> apw w (f r) c' n' Q) -> apw w (sbind t f) c n Q.
Proof.
  induction t as [r|e k IH]; intros f c n P Q H Hf; cbn [sbind apw] in *.
  - apply Hf. exact H.
  - destruct e; try exact I; intros z; (eapply IH; [apply H| exact Hf]).
Qed.

Definition unmap_len (e : ev) : Z := match e with EMunmap _ len => len | _ => 0 end.
Definition wzero (e : ev) : Z := 0.

End HMTREE.

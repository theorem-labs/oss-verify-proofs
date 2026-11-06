(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad MSafe MSafeN STree Malloc MallocCtrl Prog ModelInv ModelInvN
  ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Fixpoint twpN {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => forall rsp mo' evs, nstepN n mo rsp mo' evs -> twpN (k rsp) mo' P
  | Cho k => forall z, twpN (k z) mo P
  end.

Lemma twpN_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twpN t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twpN t mo P'.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo P P' H HP; cbn in *; [apply HP; exact H| |intros z; eapply IHc; eauto].
  intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twpN_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twpN t mo (fun a mo1 => twpN (f a) mo1 P) -> twpN (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH|kc IHc]; intros f mo P H; cbn in *; [exact H| |intros z; apply IHc; apply H].
  intros rsp mo' evs Hst. apply IH. eapply H; eauto.
Qed.

Lemma twfN_and_p : forall {R} (t : itree node R) mo (P1 P2 : R -> Model -> Prop),
  twfN t mo P1 -> twpN t mo P2 -> twfN t mo (fun r mo1 => P1 r mo1 /\ P2 r mo1).
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo P1 P2 H1 H2; cbn in *; [split; assumption| |intros z; apply IHc; auto].
  destruct H1 as [Hs H1]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; eauto.
Qed.

Section MSpecP.
Context {St : Type}.

Definition mspecP {A} (m : Monad.M St A) (Q : A -> Prop) : Prop :=
  forall s mo, twpN (m s) mo (fun r _ => match r with Unr => True | Ok p => Q (fst p) end).

Lemma mspecP_ret {A} (a : A) (Q : A -> Prop) : Q a -> mspecP (mret a) Q.
Proof. intros H s mo. cbn. exact H. Qed.

Lemma mspecP_munr {A} (Q : A -> Prop) : mspecP munr Q.
Proof. intros s mo. exact I. Qed.

Lemma mspecP_true {A} (m : Monad.M St A) : (forall s mo, twpN (m s) mo (fun _ _ => True)) -> mspecP m (fun _ => True).
Proof. intros H s mo. eapply twpN_mono; [apply H|]. intros [|p] _ _; exact I. Qed.

Lemma mspecP_bind {A B} (m : Monad.M St A) (f : A -> Monad.M St B) (Q1 : A -> Prop) (Q : B -> Prop) :
  mspecP m Q1 -> (forall a, Q1 a -> mspecP (f a) Q) -> mspecP (mbind m f) Q.
Proof.
  intros Hm Hf s mo. unfold mbind, ebind. apply twpN_bind.
  eapply twpN_mono; [apply (Hm s mo)|]. intros [|[a s1]] mo1 H1; cbn in *; [exact I|]. apply (Hf a H1).
Qed.

Lemma mspecP_post {A} (m : Monad.M St A) (Q Q' : A -> Prop) : mspecP m Q -> (forall a, Q a -> Q' a) -> mspecP m Q'.
Proof. intros H HQ s mo. eapply twpN_mono; [apply (H s mo)|]. intros [|p] _; cbn; auto. Qed.

Lemma mspecP_get : mspecP mget (fun _ => True).
Proof. intros s mo. exact I. Qed.

Lemma mspecP_upd (f : St -> St) : mspecP (mupd f) (fun _ => True).
Proof. intros s mo. exact I. Qed.

Lemma mspecP_sys {A} (n : node) (dec : resp -> option A) (Q : A -> Prop) :
  (forall rsp a, noerr_ans n rsp -> dec rsp = Some a -> Q a) -> mspecP (msys n dec) Q.
Proof.
  intros H s mo. unfold msys, enode. cbn. intros rsp mo' evs [_ Hok].
  destruct (dec rsp) as [a|] eqn:E; cbn; [exact (H rsp a Hok E)| exact I].
Qed.

End MSpecP.

Section Embed.
Context {CE__ : Ceiling}.

Lemma ev_step_P : forall e, mspecP (ev_step e) (okans e).
Proof.
  intros e. destruct e as [req|addr len prot flags|addr len|addr len prot|p c h|w]; cbn [ev_step].
  - eapply mspecP_post with (Q := fun _ => True); [| intros; exact I].
    destruct (req =? 0).
    + eapply mspecP_bind; [apply mspecP_sys; intros; exact I|]. intros r _.
      eapply mspecP_bind; [apply mspecP_upd|]. intros _ _. apply mspecP_ret. exact I.
    + eapply mspecP_bind; [apply mspecP_get|]. intros s0 _.
      eapply mspecP_bind; [apply mspecP_sys; intros; exact I|]. intros [|] _.
      * eapply mspecP_bind; [apply mspecP_upd|]. intros _ _. apply mspecP_ret. exact I.
      * apply mspecP_ret. exact I.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)) eqn:Ef.
    + eapply mspecP_bind; [apply mspecP_sys with (Q := fun _ => True); intros; exact I|]. intros a _.
      apply mspecP_ret. cbn [okans]. change MAP_FIXED with MAP_FIXED_Z.
      rewrite <- (negb_involutive (Z.land flags MAP_FIXED_Z =? 0)), Ef. discriminate.
    + apply negb_false_iff in Ef. destruct (prot =? 0).
      * eapply mspecP_bind.
        { apply mspecP_sys with (Q := fun a => exists x, a = MmOk x /\ is_err x = false).
          intros rsp a Hok Hd. cbn [noerr_ans] in Hok. apply Z.eqb_eq in Ef. specialize (Hok Ef).
          destruct a as [e|x]; [exfalso; exact (dec_mmap_none_MmErr _ _ _ _ Hd Hok)|].
          exists x. split; [reflexivity|]. rewrite (dec_mmap_none_MmOk _ _ _ _ Hd). apply is_err_errno_none. exact Hok. }
        intros a (x & -> & Hx). apply mspecP_ret. intros _. exact Hx.
      * eapply mspecP_bind.
        { apply mspecP_sys with (Q := fun a => exists x, a = MmOk x /\ is_err x = false).
          intros rsp a Hok Hd. cbn [noerr_ans] in Hok. apply Z.eqb_eq in Ef. specialize (Hok Ef).
          destruct a as [e|x]; [exfalso; exact (dec_mmap_MmErr _ _ _ _ Hd Hok)|].
          exists x. split; [reflexivity|]. rewrite (dec_mmap_MmOk _ _ _ _ Hd). apply is_err_errno_none. exact Hok. }
        intros a (x & -> & Hx). apply mspecP_ret. intros _. exact Hx.
  - eapply mspecP_bind; [apply mspecP_sys with (Q := fun _ => True); intros; exact I|]. intros a _.
    apply mspecP_ret. exact I.
  - eapply mspecP_bind.
    { apply mspecP_sys with (Q := fun a => exists b, a = RgDone b).
      intros rsp a Hok Hd. cbn [noerr_ans] in Hok.
      destruct a as [e|b]; [exfalso; exact (dec_mprotect_rw_RgErr _ _ _ _ Hd Hok)| eauto]. }
    intros a (b & ->). apply mspecP_ret. reflexivity.
  - apply mspecP_munr.
  - apply mspecP_munr.
Qed.

Lemma membed_P : forall {R} (t : stree ev Z R) (P : R -> Prop), oktree t P -> mspecP (membed t) P.
Proof.
  intros R t. induction t as [r|e k IH]; intros P Ht; cbn [membed].
  - apply mspecP_ret. exact Ht.
  - assert (Hpk : match e with EPeek _ _ _ | EUndef _ => True | _ => False end \/ forall z, okans e z -> oktree (k z) P).
    { cbn [oktree] in Ht. destruct e as [a|a len prot flags|a len|a len prot|p c h|w]; cbn [okans]; [right..|left; exact I|left; exact I].
      - intros z _. exact (Ht z).
      - destruct (Z.land flags MAP_FIXED =? 0) eqn:E; intros z Hz; [exact (Ht z (Hz eq_refl))| exact (Ht z)].
      - intros z _. exact (Ht z).
      - intros z ->. exact Ht. }
    destruct Hpk as [Hpk|Hpk].
    + destruct e; try contradiction; intros s mo; exact I.
    + eapply mspecP_bind; [apply ev_step_P|]. intros z Hz. apply IH. exact (Hpk z Hz).
Qed.

Lemma raw_malloc_P : forall n, size_overflows n = false -> mspecP (raw_malloc n) (fun r => r <> None).
Proof.
  intros n Hn. unfold raw_malloc.
  eapply mspecP_bind; [apply mspecP_get|]. intros s0 _.
  eapply mspecP_bind; [apply membed_P; apply cmalloc_ok; exact Hn|].
  intros [st' p] Hp. cbn [snd] in Hp.
  eapply mspecP_bind; [apply mspecP_upd|]. intros _ _.
  apply mspecP_ret. destruct p; [discriminate| contradiction].
Qed.

Theorem raw_malloc_some : raw_malloc_some_stmt.
Proof.
  intros X n Hn s mo HGI.
  assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; change (2^62) with 4611686018427387904 in Hn; lia).
  pose proof (mspec_N _ _ _ (raw_malloc_GI X n (proj1 Hn)) s mo HGI) as H1.
  pose proof (raw_malloc_P n Hov s mo) as H2.
  unfold etwfN in *. eapply twfN_mono; [exact (twfN_and_p _ _ _ _ H1 H2)|].
  intros [|[r s']] mo1 [HA HB]; cbn in *; [exact HA|].
  destruct r as [p|]; [| exfalso; apply HB; reflexivity].
  exists p. split; [reflexivity| exact (proj1 HA)].
Qed.

End Embed.

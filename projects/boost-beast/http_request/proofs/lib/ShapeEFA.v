(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg ShapeEF.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)

Definition is_kill (e : event) : bool :=
  match e with KillEv _ _ => true | _ => false end.

Definition kill_free (T : TSet) : Prop :=
  forall tr, T tr -> forall e, In e tr -> is_kill e = false.

Lemma kill_free_nil : kill_free t_nil.
Proof. intros tr Htr e Hin. unfold t_nil in Htr. subst tr. destruct Hin. Qed.

Lemma kill_free_eq : forall T T', t_eq T T' -> kill_free T -> kill_free T'.
Proof. intros T T' Heq HK tr Htr e Hin. apply (HK tr); [apply Heq; exact Htr | exact Hin]. Qed.

Lemma is_prefix_In : forall (l1 l2 : list event) e, is_prefix l1 l2 -> In e l1 -> In e l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 e Hp Hin; [destruct Hin|].
  destruct l2 as [|y l2]; [destruct Hp|]. cbn in Hp. destruct Hp as [<- Hp].
  destruct Hin as [<- | Hin]; [now left | right; eapply IH; eauto].
Qed.

Lemma kill_free_emit : forall evs T,
  forallb (fun e => negb (is_kill e)) evs = true ->
  kill_free T -> kill_free (t_emit evs T).
Proof.
  intros evs T Hevs HK tr Htr e Hin.
  assert (Hblk : forall e', In e' evs -> is_kill e' = false).
  { intros e' He'. pose proof (proj1 (forallb_forall _ _) Hevs e' He') as Hb.
    cbn in Hb. destruct (is_kill e'); [cbn in Hb; congruence | reflexivity]. }
  destruct Htr as [Hp | (tr' & -> & Htr')].
  - apply Hblk. eapply is_prefix_In; eauto.
  - apply in_app_iff in Hin as [Hin | Hin].
    + apply Hblk; exact Hin.
    + exact (HK tr' Htr' e Hin).
Qed.

Lemma kill_free_alt : forall (I : Type) (f : I -> TSet),
  (forall i, kill_free (f i)) -> kill_free (t_alt f).
Proof. intros I f HK tr [i Htr] e Hin. exact (HK i tr Htr e Hin). Qed.

Lemma kill_free_alt2 : forall A B, kill_free A -> kill_free B -> kill_free (t_alt2 A B).
Proof. intros A B HA HB tr [Htr | Htr] e Hin; [exact (HA tr Htr e Hin) | exact (HB tr Htr e Hin)]. Qed.

Lemma kill_free_exit : forall code fs, kill_free (t_exit code fs).
Proof. intros code fs. unfold t_exit. apply kill_free_emit; [reflexivity | apply kill_free_nil]. Qed.

(* [comment removed for export] *)
Lemma forallb_not_kill_map_write : forall ch (s : list byte),
  forallb (fun e => negb (is_kill e)) (map (WriteEv ch) s) = true.
Proof. intros ch s. induction s as [|b s IH]; [reflexivity | cbn; exact IH]. Qed.

(* [comment removed for export] *)

Section WithCfg.
Context {SC : StepCfg}.

Lemma realizes_not_dies : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg the_scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T Hrz HK (tr & sig & fs & Htr & Hin).
  cbn in Htr. apply (realizes_obs_iff segs _ T Hrz tr) in Htr.
  pose proof (HK tr Htr _ Hin) as Hk. discriminate Hk.
Qed.

Theorem shape_strong_equiv_ef_abort :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  kill_free T ->
  strong_equiv_error_free_budgets_scfg_abort the_scfg rlim alim
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget HK.
  pose proof (shape_strong_equiv_ef source_segs rpc rph rsp rbrk rmb rrnd rlim
                target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget) as (Hs & Ht & Htr).
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
  repeat split.
  - exact Hs.
  - eapply realizes_not_dies; eassumption.
  - exact Ht.
  - eapply realizes_not_dies; eassumption.
  - apply Htr.
  - apply Htr.
Qed.

(* [comment removed for export] *)
Corollary shape_strong_equiv_ef_abort_eq :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  kill_free T ->
  strong_equiv_error_free_budgets_scfg_abort the_scfg rlim alim
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros until T'. intros inp Hs Ht Heq HK.
  eapply shape_strong_equiv_ef_abort; [| exact Ht | eapply kill_free_eq; eauto].
  eapply rz_conseq; [exact Hs | exact Heq].
Qed.

End WithCfg.

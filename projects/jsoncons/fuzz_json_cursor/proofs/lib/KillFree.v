(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ev_not_kill (e : event) : Prop :=
  match e with KillEv _ _ => False | _ => True end.

Definition kill_free (T : TSet) : Prop := forall tr, T tr -> Forall ev_not_kill tr.

Lemma Forall_prefix {A} (P : A -> Prop) : forall (l1 l2 : list A),
  is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
  induction l1 as [|x l1 IH]; intros l2 Hp Hl2; [constructor|].
  destruct l2 as [|y l2]; cbn in Hp; [contradiction|].
  destruct Hp as [-> Hp]. inversion Hl2; subst. constructor; [assumption | eapply IH; eassumption].
Qed.

Lemma kill_free_nil : kill_free t_nil.
Proof. intros tr ->. constructor. Qed.

Lemma kill_free_emit : forall evs T,
  Forall ev_not_kill evs -> kill_free T -> kill_free (t_emit evs T).
Proof.
  intros evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
  - eapply Forall_prefix; eassumption.
  - apply Forall_app. split; [exact Hevs | exact (HT _ Htr')].
Qed.

Lemma kill_free_alt2 : forall A B, kill_free A -> kill_free B -> kill_free (t_alt2 A B).
Proof. intros A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Lemma kill_free_exit : forall code fs, kill_free (t_exit code fs).
Proof.
  intros code fs. unfold t_exit. apply kill_free_emit; [| apply kill_free_nil].
  constructor; [exact I | constructor].
Qed.

Lemma Forall_not_kill_writes : forall ch (s : list byte), Forall ev_not_kill (map (WriteEv ch) s).
Proof. intros ch s. induction s as [|b s IH]; cbn; constructor; [exact I | exact IH]. Qed.

Section FPX_1.
Context {fx : PropExec.FPState}.

Lemma kill_free_W_emit : forall ch s T, kill_free T -> kill_free (t_emit (W ch s) T).
Proof. intros ch s T HT. apply kill_free_emit; [apply Forall_not_kill_writes | exact HT]. Qed.

Lemma kill_free_die : forall msg fs, kill_free (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply kill_free_W_emit. apply kill_free_exit. Qed.

Lemma kill_free_t_body : forall data fs, kill_free (BigintSpec.t_body data fs).
Proof.
  intros data fs. unfold BigintSpec.t_body.
  repeat first [ apply kill_free_die
               | apply kill_free_W_emit
               | apply kill_free_exit
               | match goal with |- kill_free (if ?c then _ else _) => destruct c end
               | match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.

Lemma kill_free_spec : forall argv fs, kill_free (BigintSpec.spec argv fs).
Proof.
  intros argv fs. unfold BigintSpec.spec.
  repeat first [ apply kill_free_die
               | apply kill_free_t_body
               | apply kill_free_alt2
               | apply kill_free_exit
               | match goal with |- kill_free (if ?c then _ else _) => destruct c end
               | match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.

Lemma srealizes_not_dies_by_signal : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  VmLimitFrame.Safe segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  kill_free T ->
  ~ dies_by_signal (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros scfg segs pc ph sp brk0 mb rnd lim inp T Hs Hsafe HK (tr & sig & fs & Htr & Hin).
  apply (srealizes_traces_iff scfg segs pc ph sp brk0 mb rnd lim inp T tr Hs Hsafe) in Htr.
  pose proof (HK _ Htr) as HF.
  apply Forall_forall with (x := KillEv sig fs) in HF; [exact HF | exact Hin].
Qed.

Lemma srealizes_error_free_unkilled : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  VmLimitFrame.Safe segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  kill_free T ->
  error_free_unkilled (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros. split; [eapply srealizes_error_free; eassumption | eapply srealizes_not_dies_by_signal; eassumption].
Qed.

Lemma srealizes_error_free_unkilled_big : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  (VmLimitFrame.nbr_limit <= lim)%Z ->
  kill_free T ->
  error_free_unkilled (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros. eapply srealizes_error_free_unkilled; [eassumption | apply VmLimitFrame.Safe_init_big; assumption | assumption].
Qed.

Lemma srealizes_error_free_unkilled_wb : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  ~ run_scfg_budget_refused scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  kill_free T ->
  error_free_unkilled (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros. eapply srealizes_error_free_unkilled; [eassumption | apply VmLimitFrame.Safe_init_within_budget; assumption | assumption].
Qed.

End FPX_1.

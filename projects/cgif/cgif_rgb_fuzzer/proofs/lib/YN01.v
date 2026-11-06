(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit HaltsAllowed.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Definition ev_ok (S : list word) (e : event) : Prop :=
match e with
| KillEv _ _ => False
| ExitEv c _ => In c S
| _ => True
end.
Definition tsafe (S : list word) (T : TSet) : Prop :=
forall tr, T tr -> Forall (ev_ok S) tr.
Lemma Forall_prefix {A} (P : A -> Prop) : forall l1 l2,
is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
induction l1 as [| x xs IH]; intros l2 Hp H; [constructor |].
destruct l2 as [| y ys]; [cbn in Hp; contradiction |].
cbn in Hp. destruct Hp as [<- Hp]. inversion H; subst. constructor; [assumption | eapply IH; eauto].
Qed.
Lemma tsafe_nil : forall S, tsafe S t_nil.
Proof. intros S tr ->. constructor. Qed.
Lemma tsafe_bot : forall S, tsafe S t_bot.
Proof. intros S tr []. Qed.
Lemma tsafe_emit : forall S evs T,
Forall (ev_ok S) evs -> tsafe S T -> tsafe S (t_emit evs T).
Proof.
intros S evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
- eapply Forall_prefix; eauto.
- apply Forall_app. split; [exact Hevs | exact (HT _ Htr')].
Qed.
Lemma tsafe_exit : forall S code fs, In code S -> tsafe S (t_exit code fs).
Proof.
intros S code fs Hin. unfold t_exit. apply tsafe_emit; [| apply tsafe_nil].
constructor; [exact Hin | constructor].
Qed.
Lemma tsafe_alt2 : forall S A B, tsafe S A -> tsafe S B -> tsafe S (t_alt2 A B).
Proof. intros S A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Lemma tsafe_eq : forall S T T', t_eq T T' -> tsafe S T -> tsafe S T'.
Proof. intros S T T' Heq HT tr H. apply HT. apply (Heq tr). exact H. Qed.
Lemma tsafe_writes : forall S ch bs T,
tsafe S T -> tsafe S (t_emit (map (WriteEv ch) bs) T).
Proof.
intros S ch bs T HT. apply tsafe_emit; [| exact HT].
apply Forall_forall. intros e Hin. apply in_map_iff in Hin. destruct Hin as (b & <- & _). exact I.
Qed.
Section d.
Context {fx : YK11.FPState}.
Lemma tsafe_tset {St A : Type} : forall S (t : itree St A) (K : A -> TSet),
(forall a, tsafe S (K a)) -> tsafe S (tset t K).
Proof.
intros S t; induction t as [a | q s k IH | f]; intros K HK; cbn.
- apply HK.
- destruct (fallible q); [apply tsafe_alt2; apply IH; exact HK | apply IH; exact HK].
- apply tsafe_bot.
Qed.
End d.
Lemma tsafe_bytes_exit : forall z fs, (0 <= z < 256)%Z -> tsafe byte_codes (t_exit (Z_to_bv 64 z) fs).
Proof. intros z fs Hz. apply tsafe_exit. apply in_byte_codes. exact Hz. Qed.
Section g.
Variable segs : list Segment.
Lemma sstep_next_status : forall S c evs c',
sstep segs c evs (SNext c') ->
Forall (ev_ok S) evs ->
m_killed (cfg_model c') = None
/\ (forall code, m_halted (cfg_model c') = Some code -> In code S).
Proof.
intros S c evs c' Hstep Hok.
inversion Hstep; subst; cbn [cfg_model].
-
match goal with
| [ H : mi_account_step _ _ _ = MachineOk (_, _) |- _ ] =>
destruct (mi_account_step_model_frame _ _ _ _ _ H) as (_&_&_&_&_&Hp&_)
end.
assert (Hh : m_halted model' = None) by (unfold m_halted in *; rewrite Hp; assumption).
split; [apply m_killed_of_m_halted_none; exact Hh | intros code Hc; congruence].
-
match goal with
| [ Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ ] =>
destruct (materialize_model_accesses_frame _ _ _ Hm) as (_&_&_&_&_&Hp&_)
end.
assert (Hh : m_halted model'' = None) by (unfold m_halted in *; rewrite Hp; assumption).
split; [apply m_killed_of_m_halted_none; exact Hh | intros code Hc; congruence].
-
split; [assumption |].
intros code' Hc'. apply Forall_app in Hok. destruct Hok as [_ Hok].
inversion Hok as [| e l He _]; subst. cbn in He. congruence.
-
apply Forall_app in Hok. destruct Hok as [_ Hok].
inversion Hok as [| e l He _]; subst. cbn in He. destruct He.
Qed.
Theorem must_exit_of_realizes : forall S c T,
realizes segs c T ->
tsafe S T ->
m_killed (cfg_model c) = None ->
(forall code, m_halted (cfg_model c) = Some code -> In code S) ->
must_exit_in_at_cfg may_fail_cfg segs S c.
Proof.
intros S c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros Hsafe Hk Hcode.
- destruct Hnode as [Hcomp Hsound].
assert (HsafeI : forall i, tsafe S (T i)).
{ intros i tr Htr.
assert (Hall : Forall (ev_ok S) (evs i ++ tr)).
{ apply Hsafe. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
apply Forall_app in Hall. tauto. }
assert (HevI : forall i, Forall (ev_ok S) (evs i)).
{ intros i.
assert (Hall : Forall (ev_ok S) (evs i ++ [])).
{ apply Hsafe. exists i. right. exists []. split; [reflexivity | eapply realizes_nonempty; exact (Hcont i)]. }
rewrite app_nil_r in Hall. exact Hall. }
apply must_exit_in_at_cfg_running.
+ eapply sstep_halted_none. exact (Hcomp i0).
+ exists (evs i0), (SNext (nx i0)). apply (proj1 (sstep_cfg_may_fail segs _ _ _)). exact (Hcomp i0).
+ intros e Herr. apply (proj2 (sstep_cfg_may_fail segs _ _ _)) in Herr.
destruct (Hsound _ _ Herr) as (i & _ & Habs). discriminate.
+ intros e c' Hstep. apply (proj2 (sstep_cfg_may_fail segs _ _ _)) in Hstep.
destruct (Hsound _ _ Hstep) as (i & -> & Heqc). inversion Heqc; subst c'.
destruct (sstep_next_status S _ _ _ Hstep (HevI i)) as [Hk' Hcode'].
exact (IH i (HsafeI i) Hk' Hcode').
- destruct (m_halted (cfg_model c)) as [code |] eqn:Hh'; [| congruence].
eapply must_exit_in_at_cfg_halted; [exact Hh' | exact (Hcode _ eq_refl) | exact Hk].
- apply IH; [eapply tsafe_eq; [apply t_eq_sym; exact Heq | exact Hsafe] | exact Hk | exact Hcode].
Qed.
Theorem halts_of_realizes : forall S pc ph sp brk0 mbase rnd lim inp T,
realizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) T ->
tsafe S T ->
must_exit_in_at_cfg may_fail_cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof.
intros S pc ph sp brk0 mbase rnd lim inp T Hr Hs.
assert (Hh : m_halted (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)) = None).
{ unfold init_config. cbn [cfg_model]. apply m_halted_init_model. }
eapply must_exit_of_realizes; [exact Hr | exact Hs | apply m_killed_of_m_halted_none; exact Hh |].
intros code Hc. congruence.
Qed.
End g.

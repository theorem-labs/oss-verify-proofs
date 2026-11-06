(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/HaltsKitB.v, with its module paths changed; the walk lemma and the halting corollary take srealizes (YK18.v) where cgif's take realizes, because fuzz_knock's realizes (YK15.v) has a cut at a budget refusal. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/HaltsKitB.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_pin. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs Monad State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK15 YK18 YO0i YO0f YM02 YJ00 YQ05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ev_ok (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv k _ => In k S
  | KillEv _ _ => False
  | _ => True
  end.
Definition trace_ok (S : list word) (tr : list event) : Prop := Forall (ev_ok S) tr.
Definition shape_ok (S : list word) (T : TSet) : Prop := forall tr, T tr -> trace_ok S tr.

Lemma trace_ok_app : forall S a b, trace_ok S (a ++ b) <-> trace_ok S a /\ trace_ok S b.
Proof. intros S a b. unfold trace_ok. apply Forall_app. Qed.
Lemma trace_ok_prefix : forall S tr tr', is_prefix tr tr' -> trace_ok S tr' -> trace_ok S tr.
Proof.
  intros S tr; induction tr as [|e tr IH]; intros tr' Hp Hok.
  - constructor.
  - destruct tr' as [|e' tr']; cbn in Hp; [destruct Hp|]. destruct Hp as [<- Hp].
    inversion Hok; subst. constructor; [assumption|]. eapply IH; eauto.
Qed.
Lemma shape_ok_eq : forall S T T', t_eq T T' -> shape_ok S T' -> shape_ok S T.
Proof. intros S T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.
Lemma shape_ok_nil : forall S, shape_ok S t_nil.
Proof. intros S tr Htr. unfold t_nil in Htr. subst tr. constructor. Qed.
Lemma shape_ok_bot : forall S, shape_ok S t_bot.
Proof. intros S tr Htr. destruct Htr. Qed.
Lemma shape_ok_emit : forall S evs T, trace_ok S evs -> shape_ok S T -> shape_ok S (t_emit evs T).
Proof.
  intros S evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
  - eapply trace_ok_prefix; eauto.
  - apply trace_ok_app. split; [exact Hevs | apply HT; exact Htr'].
Qed.
Lemma shape_ok_emit_inv : forall S evs T, T [] -> shape_ok S (t_emit evs T) -> trace_ok S evs /\ shape_ok S T.
Proof.
  intros S evs T H0 H. split.
  - apply (H evs). right. exists []. rewrite app_nil_r. split; [reflexivity | exact H0].
  - intros tr Htr. assert (Hc : trace_ok S (evs ++ tr)).
    { apply H. right. exists tr. split; [reflexivity | exact Htr]. }
    apply trace_ok_app in Hc. tauto.
Qed.
Lemma shape_ok_alt : forall S (I : Type) (f : I -> TSet), (forall i, shape_ok S (f i)) -> shape_ok S (t_alt f).
Proof. intros S I f H tr [i Hi]. exact (H i tr Hi). Qed.
Lemma shape_ok_alt_inv : forall S (I : Type) (f : I -> TSet) i, shape_ok S (t_alt f) -> shape_ok S (f i).
Proof. intros S I f i H tr Htr. apply H. exists i. exact Htr. Qed.
Lemma shape_ok_alt2 : forall S A B, shape_ok S A -> shape_ok S B -> shape_ok S (t_alt2 A B).
Proof. intros S A B HA HB tr [H|H]; [apply HA | apply HB]; exact H. Qed.
Lemma shape_ok_exit : forall S code fs, In code S -> shape_ok S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply shape_ok_emit; [|apply shape_ok_nil].
  constructor; [exact Hin | constructor].
Qed.
Lemma trace_ok_writes : forall S ch bs, trace_ok S (map (WriteEv ch) bs).
Proof. intros S ch bs. unfold trace_ok. apply Forall_forall. intros e He. apply in_map_iff in He as (b & <- & _). exact I. Qed.
Lemma shape_ok_tset {St A} : forall S (t : itree St A) (K : A -> TSet),
  (forall a, shape_ok S (K a)) -> shape_ok S (tset t K).
Proof.
  intros S t; induction t as [a | q s k IH | f]; intros K HK; cbn.
  - apply HK.
  - destruct (fallible q); [destruct (spurious q)|].
    + apply shape_ok_alt2; apply IH; exact HK.
    + apply IH; exact HK.
    + apply IH; exact HK.
  - apply shape_ok_bot.
Qed.

Section a.
Variable segs : list Segment.

Theorem srealizes_must_exit_in : forall c T,
  srealizes segs c T ->
  forall S,
  m_halted (cfg_model c) = None ->
  shape_ok S T ->
  must_exit_in_at_cfg ACFG segs S c.
Proof using segs.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq];
    intros S Hnone Hx.
  - destruct Hnode as [Hsound Hinv].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + eexists _, _. exact (Hsound i0).
    + intros e Herr. destruct (Hinv e SError Herr) as (i & _ & Habs). discriminate Habs.
    + intros e c' Hs.
      destruct (Hinv e (SNext c') Hs) as (i & -> & Hc'). injection Hc' as ->.
      pose proof (shape_ok_alt_inv S I _ i Hx) as Hxi.
      destruct (shape_ok_emit_inv S (evs i) (T i) (srealizes_nonempty segs _ _ (Hcont i)) Hxi) as [Hevs HTi].
      destruct (sstep_cfg_next_halts_by_exit segs ACFG c (evs i) (nx i) Hs)
        as [Hn | [(evs0 & code & Hevs' & Hh & Hk) | (evs0 & sig & Hevs' & Hk)]].
      * apply IH; assumption.
      * apply (must_exit_in_at_cfg_halted ACFG segs S (nx i) code Hh); [|exact Hk].
        rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. inversion Hev; subst. exact H1.
      * exfalso. rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. inversion Hev; subst. exact H1.
  - exfalso. apply Hh. exact Hnone.
  - destruct Hspin as [[] _].
  - apply IH; [exact Hnone|]. eapply shape_ok_eq; eauto.
Qed.
End a.

Lemma init_config_not_halted : forall segs pc ph sp brk mb rnd lim inp,
  m_halted (cfg_model (init_config segs pc ph sp brk mb rnd lim inp)) = None.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Theorem halts_budgets_of_srealizes : forall cfg S segs pc ph (Lbig Lsmall : Z),
  (Lsmall <= Lbig)%Z ->
  cfg_le cfg ACFG ->
  (forall sp brk mb rnd inp,
      valid_entry (mkImage segs pc ph) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
      exists T, srealizes segs (init_config segs pc ph sp brk mb rnd Lbig inp) T /\ shape_ok S T) ->
  halts_allowed_T_scfg_budgets cfg Lsmall S (mkImage segs pc ph).
Proof.
  intros cfg S segs pc ph Lbig Lsmall HLE Hle H [sp brk mb rnd] inp Hen Hinp SWB.
  apply (must_exit_in_scfg_relim_closed cfg S (mkImage segs pc ph) Lbig Lsmall (mkEntry sp brk mb rnd) inp HLE SWB).
  apply (must_exit_in_scfg_mono cfg ACFG); [exact Hle | apply run_decided_classic |].
  cbn [must_exit_in_scfg].
  destruct (H sp brk mb rnd inp Hen Hinp) as (T & HR & HS).
  exact (srealizes_must_exit_in segs _ _ HR S (init_config_not_halted _ _ _ _ _ _ _ _ _) HS).
Qed.

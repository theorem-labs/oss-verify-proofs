(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib.Logic Require Import Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg Spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ev_ok (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv code _ => In code S
  | KillEv _ _ => False
  | _ => True
  end.

Definition exits_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> Forall (ev_ok S) tr.

Lemma exits_in_t_eq : forall S T T', t_eq T T' -> exits_in S T -> exits_in S T'.
Proof. intros S T T' Heq H tr Htr. apply H. apply (proj2 (Heq tr)). exact Htr. Qed.

Lemma Forall_is_prefix : forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
  is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
  intros A P l1; induction l1 as [| x xs IH]; intros l2 Hp H; [constructor |].
  destruct l2 as [| y ys]; [destruct Hp |]. destruct Hp as [-> Hp].
  inversion H; subst. constructor; [assumption | exact (IH ys Hp ltac:(assumption))].
Qed.

Lemma exits_in_emit : forall S evs T,
  Forall (ev_ok S) evs -> exits_in S T -> exits_in S (t_emit evs T).
Proof.
  intros S evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
  - exact (Forall_is_prefix _ _ _ _ Hp Hevs).
  - apply Forall_app. split; [exact Hevs | exact (HT _ Htr')].
Qed.

Lemma exits_in_nil : forall S, exits_in S t_nil.
Proof. intros S tr ->. constructor. Qed.

Lemma exits_in_exit : forall S code fs, In code S -> exits_in S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply exits_in_emit; [| apply exits_in_nil].
  constructor; [exact Hin | constructor].
Qed.

Lemma exits_in_alt2 : forall S A B, exits_in S A -> exits_in S B -> exits_in S (t_alt2 A B).
Proof. intros S A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Lemma exits_in_alt : forall S (I : Type) (f : I -> TSet),
  (forall i, exits_in S (f i)) -> exits_in S (t_alt f).
Proof. intros S I f Hf tr [i Hi]. exact (Hf i _ Hi). Qed.

Lemma exits_in_alt_inv : forall S (I : Type) (f : I -> TSet) i,
  exits_in S (t_alt f) -> exits_in S (f i).
Proof. intros S I f i H tr Htr. apply H. exists i. exact Htr. Qed.

Lemma exits_in_emit_inv : forall S evs T,
  exits_in S (t_emit evs T) -> T [] -> Forall (ev_ok S) evs /\ exits_in S T.
Proof.
  intros S evs T H Hnil. split.
  - pose proof (H (evs ++ []) ltac:(right; exists []; split; [reflexivity | exact Hnil])) as H1.
    rewrite app_nil_r in H1. exact H1.
  - intros tr Htr. pose proof (H (evs ++ tr) ltac:(right; exists tr; split; [reflexivity | exact Htr])) as H1.
    apply Forall_app in H1. exact (proj2 H1).
Qed.

Lemma Forall_ev_ok_writes : forall S ch bs, Forall (ev_ok S) (map (WriteEv ch) bs).
Proof. intros S ch bs. induction bs as [| b bs IH]; [constructor | constructor; [exact I | exact IH]]. Qed.

Lemma exits_in_W_exit : forall S ch msg code fs,
  In code S -> exits_in S (t_emit (W ch msg) (t_exit code fs)).
Proof.
  intros S ch msg code fs Hin. apply exits_in_emit.
  - unfold W. apply Forall_ev_ok_writes.
  - apply exits_in_exit. exact Hin.
Qed.

(* [comment removed for export] *)
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in_codes02_0 : In (exit_code 0) codes02.  Proof. left. reflexivity. Qed.
Lemma in_codes02_2 : In (exit_code 2) codes02.  Proof. right. left. reflexivity. Qed.

Lemma exits_in_t_die : forall msg fs, exits_in codes02 (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply exits_in_W_exit. exact in_codes02_2. Qed.

Lemma exits_in_t_body : forall data fs, exits_in codes02 (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply exits_in_t_die|].
  destruct (length data <? 6)%nat; [apply exits_in_t_die|].
  cbv zeta.
  destruct (length data <? _)%nat; [apply exits_in_t_die|].
  apply exits_in_W_exit. exact in_codes02_0.
Qed.

Lemma exits_in_spec02 : forall argv fs, exits_in codes02 (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply exits_in_t_die.
  destruct (4096 <=? length path)%nat; [apply exits_in_t_die|].
  destruct (list_byte_eqb path []); [apply exits_in_t_die|].
  destruct (list_byte_eqb path dot_path).
  - apply exits_in_alt2; [apply exits_in_t_die|]. unfold t_opened_dir. apply exits_in_t_die.
  - destruct (fs_lookup fs path) as [data|]; [|apply exits_in_t_die].
    apply exits_in_alt2; [apply exits_in_t_die|]. unfold t_opened. apply exits_in_t_body.
Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Lemma Forall_ev_ok_exit_last : forall S evs0 code fs,
  Forall (ev_ok S) (evs0 ++ [ExitEv code fs]) -> In code S.
Proof.
  intros S evs0 code fs H. apply Forall_app in H. destruct H as [_ H].
  inversion H as [| x l Hx Hl]; subst. exact Hx.
Qed.

Lemma Forall_ev_ok_kill_last : forall S evs0 sig fs,
  Forall (ev_ok S) (evs0 ++ [KillEv sig fs]) -> False.
Proof.
  intros S evs0 sig fs H. apply Forall_app in H. destruct H as [_ H].
  inversion H as [| x l Hx Hl]; subst. exact Hx.
Qed.

Theorem realizes_must_exit : forall S c T,
  realizes segs c T -> exits_in S T -> m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg the_scfg segs S c.
Proof.
  intros S c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros HS Hnone.
  - destruct Hnode as [Hfwd Hbwd].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). exact (Hfwd i0).
    + intros e Herr. destruct (Hbwd e SError Herr) as (i & _ & Hst). discriminate Hst.
    + intros e c' Hss. destruct (Hbwd e (SNext c') Hss) as (i & -> & Hst).
      injection Hst as ->.
      pose proof (exits_in_alt_inv S I (fun i => t_emit (evs i) (T i)) i HS) as HSi. cbn beta in HSi.
      destruct (exits_in_emit_inv S (evs i) (T i) HSi (realizes_nonempty segs _ _ (Hcont i))) as [Hevs HTi].
      destruct (sstep_cfg_next_halts_by_exit segs the_scfg c (evs i) (nx i) Hss)
        as [Hnone' | [(evs0 & code & Hevs' & Hh' & Hk') | (evs0 & sig & Hevs' & Hk')]].
      * exact (IH i HTi Hnone').
      * apply (must_exit_in_at_cfg_halted the_scfg segs S (nx i) code Hh'); [| exact Hk'].
        rewrite Hevs' in Hevs. exact (Forall_ev_ok_exit_last _ _ _ _ Hevs).
      * exfalso. rewrite Hevs' in Hevs. exact (Forall_ev_ok_kill_last _ _ _ _ Hevs).
  - exfalso. exact (Hh Hnone).
  - exact (IH (exits_in_t_eq S T' T (t_eq_sym _ _ Heq) HS) Hnone).
Qed.

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs',
              Specs.syscall_spec i m (Monad.Ok eff' m' evs') /\ refusal_b i m (State.eff_ret eff') = false))
    as [Hyes | Hno]; [left; exact Hyes | right].
  intros eff' m' evs' Hsp.
  destruct (refusal_b i m (State.eff_ret eff')) eqn:Hr; [reflexivity | exfalso].
  apply Hno. exists eff', m', evs'. split; [exact Hsp | exact Hr].
Qed.

Lemma decided_from_classic : forall cfg c, decided_from cfg segs c.
Proof. intros cfg c tr c' x8 _ _. apply refusal_decided_classic. Qed.

(* [comment removed for export] *)
Lemma must_exit_forced_only : forall S c,
  must_exit_in_at_cfg the_scfg segs S c ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros S c H.
  exact (must_exit_in_at_cfg_mono forced_only_cfg the_scfg segs S c (forced_only_cfg_least the_scfg)
           (decided_from_classic _ _) H).
Qed.

End WithSegs.

(* [comment removed for export] *)
Section Halts.
Context {SC : StepCfg}.

Definition full_stmt (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    realizes segs (init_config segs pc ph sp brk mbase rnd lim inp) (spec (in_argv inp) (in_fs inp)).

Lemma init_config_not_halted : forall segs pc ph sp brk mbase rnd lim inp,
  m_halted (cfg_model (init_config segs pc ph sp brk mbase rnd lim inp)) = None.
Proof. intros. reflexivity. Qed.

Theorem halts_of_realizes_spec : forall segs pc ph lim,
  full_stmt segs pc ph lim ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim codes02 (mkImage segs pc ph).
Proof.
  intros segs pc ph lim Hfull [sp brk mbase rnd] inp Hen Hvalid _.
  cbn [must_exit_in_scfg].
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  destruct Hvalid as (Hargv & Henvp & Hfs & _).
  apply (@must_exit_forced_only segs SC).
  apply (realizes_must_exit segs codes02 _ (spec (in_argv inp) (in_fs inp))).
  - exact (Hfull sp brk mbase rnd inp Hsp Hbrk Hfit Hargv Henvp Hfs).
  - apply exits_in_spec02.
  - apply init_config_not_halted.
Qed.

End Halts.

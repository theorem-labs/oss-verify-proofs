(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kf (T : TSet) : Prop := forall tr sig fs, T tr -> ~ In (KillEv sig fs) tr.

(* [comment removed for export] *)
Definition exit_codes_in (S : list word) (T : TSet) : Prop :=
  forall tr code fs, T tr -> In (ExitEv code fs) tr -> In code S.

(* [comment removed for export] *)
Definition evs_ok (S : list word) (evs : list event) : Prop :=
  (forall sig fs, ~ In (KillEv sig fs) evs)
  /\ (forall code fs, In (ExitEv code fs) evs -> In code S).

Lemma is_prefix_In' {A} : forall (l m : list A) x, is_prefix l m -> In x l -> In x m.
Proof.
  induction l as [|a l IH]; intros m x Hp Hin; [destruct Hin|].
  destruct m as [|b m]; [destruct Hp|]. destruct Hp as [-> Hp].
  destruct Hin as [-> | Hin]; [left; reflexivity | right; eapply IH; eauto].
Qed.

Lemma kf_eq : forall T T', t_eq T T' -> kf T' -> kf T.
Proof. intros T T' Heq H tr sig fs Htr. apply H. apply Heq. exact Htr. Qed.

Lemma exit_codes_in_eq : forall S T T', t_eq T T' -> exit_codes_in S T' -> exit_codes_in S T.
Proof. intros S T T' Heq H tr code fs Htr. apply H. apply Heq. exact Htr. Qed.


(* [comment removed for export] *)
Lemma kf_node_evs : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  kf (t_alt (fun i => t_emit (evs i) (T i))) -> T i [] ->
  forall sig fs, ~ In (KillEv sig fs) (evs i).
Proof.
  intros I evs T i H Hnil sig fs Hin.
  apply (H (evs i) sig fs); [| exact Hin].
  exists i. right. exists []. rewrite app_nil_r. split; [reflexivity | exact Hnil].
Qed.

Lemma exit_codes_in_node_evs : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exit_codes_in S (t_alt (fun i => t_emit (evs i) (T i))) -> T i [] ->
  forall code fs, In (ExitEv code fs) (evs i) -> In code S.
Proof.
  intros S I evs T i H Hnil code fs Hin.
  apply (H (evs i) code fs); [| exact Hin].
  exists i. right. exists []. rewrite app_nil_r. split; [reflexivity | exact Hnil].
Qed.

Lemma kf_node_cont : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  kf (t_alt (fun i => t_emit (evs i) (T i))) -> kf (T i).
Proof.
  intros I evs T i H tr sig fs Htr Hin.
  apply (H (evs i ++ tr) sig fs).
  - exists i. right. exists tr. split; [reflexivity | exact Htr].
  - apply in_or_app. right. exact Hin.
Qed.

Lemma exit_codes_in_node_cont : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exit_codes_in S (t_alt (fun i => t_emit (evs i) (T i))) -> exit_codes_in S (T i).
Proof.
  intros S I evs T i H tr code fs Htr Hin.
  apply (H (evs i ++ tr) code fs).
  - exists i. right. exists tr. split; [reflexivity | exact Htr].
  - apply in_or_app. right. exact Hin.
Qed.






Lemma exit_codes_in_t_nil : forall S, exit_codes_in S t_nil.
Proof. intros S tr code fs H. unfold t_nil in H. subst tr. intros []. Qed.

Lemma exit_codes_in_t_emit : forall S evs T,
  (forall code fs, In (ExitEv code fs) evs -> In code S) ->
  exit_codes_in S T -> exit_codes_in S (t_emit evs T).
Proof.
  intros S evs T Hevs HT tr code fs [Hp | (tr' & -> & Htr')] Hin.
  - exact (Hevs code fs (is_prefix_In' _ _ _ Hp Hin)).
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact (Hevs code fs Hin) | exact (HT _ _ _ Htr' Hin)].
Qed.


Lemma exit_codes_in_t_alt2 : forall S A B,
  exit_codes_in S A -> exit_codes_in S B -> exit_codes_in S (t_alt2 A B).
Proof. intros S A B HA HB tr code fs [H|H]; [eapply HA | eapply HB]; eauto. Qed.

Lemma exit_codes_in_t_exit : forall S code fs, In code S -> exit_codes_in S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply exit_codes_in_t_emit; [| apply exit_codes_in_t_nil].
  intros code' fs' [H | []]. injection H as <- <-. exact Hin.
Qed.


Lemma writes_no_exit : forall ch (s : list byte) code fs, ~ In (ExitEv code fs) (map (WriteEv ch) s).
Proof. intros ch s code fs Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & _). discriminate Hb. Qed.

(* [comment removed for export] *)
Lemma in_any_exit_small : forall z, (0 <= z < 256)%Z -> In (Z_to_bv 64 z) AnyExit.codes.
Proof. intros z Hz. unfold AnyExit.codes. apply in_byte_codes. exact Hz. Qed.

(* [comment removed for export] *)

Definition halt_inv (S : list word) (c : config) : Prop :=
  forall code, m_halted (cfg_model c) = Some code ->
    In code S /\ m_killed (cfg_model c) = None.

Lemma halt_inv_of_running : forall S c, m_halted (cfg_model c) = None -> halt_inv S c.
Proof. intros S c H code Hc. rewrite H in Hc. discriminate Hc. Qed.

Lemma m_halted_proc : forall m1 m2, m_proc m1 = m_proc m2 -> m_halted m1 = m_halted m2.
Proof. intros m1 m2 H. unfold m_halted. now rewrite H. Qed.

Section WithSegs.
Variable segs : list Segment.






(* [comment removed for export] *)
Lemma halt_inv_sstep : forall S c evs c',
  sstep segs c evs (SNext c') ->
  evs_ok S evs ->
  halt_inv S c'.
Proof.
  intros S c evs c' Hstep [Hnk Hex].
  inversion Hstep; subst.
  - (* [comment removed for export] *)
    match goal with
    | [ H : mi_account_step _ _ _ = MachineOk (_, _) |- _ ] =>
        destruct (mi_account_step_model_frame _ _ _ _ _ H) as (_&_&_&_&_&Hp&_)
    end.
    apply halt_inv_of_running. cbn [cfg_model].
    rewrite (m_halted_proc _ _ Hp). assumption.
  - (* [comment removed for export] *)
    match goal with
    | [ Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ ] =>
        destruct (materialize_model_accesses_frame _ _ _ Hm) as (_&_&_&_&_&Hp&_)
    end.
    apply halt_inv_of_running. cbn [cfg_model].
    rewrite (m_halted_proc _ _ Hp). assumption.
  - (* [comment removed for export] *)
    intros code' Hc'. cbn [cfg_model] in Hc' |- *.
    match goal with
    | [ Hh : m_halted ?m = Some ?code, Hk : m_killed ?m = None |- _ ] =>
        rewrite Hh in Hc'; injection Hc' as <-; split; [| exact Hk];
        apply (Hex code (m_fs m)); apply in_or_app; right; left; reflexivity
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | [ Hk : m_killed ?m = Some ?sig |- _ ] =>
        apply (Hnk sig (m_fs m)); apply in_or_app; right; left; reflexivity
    end.
Qed.

(* [comment removed for export] *)

Theorem realizes_must_exit : forall S c T,
  realizes segs c T ->
  kf T ->
  exit_codes_in S T ->
  halt_inv S c ->
  must_exit_in_at_cfg CfgStep.kit_cfg segs S c.
Proof.
  intros S c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hkf Hex Hinv.
  - (* [comment removed for export] *)
    destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_halted_none segs _ _ _ (Hcomp i0)).
    + exists (evs i0), (SNext (nx i0)). exact (Hcomp i0).
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Habs). discriminate Habs.
    + intros e c' Hs. destruct (Hsound e (SNext c') Hs) as (i & -> & Heqc).
      injection Heqc as ->.
      pose proof (realizes_nonempty segs _ _ (Hcont i)) as Hnil.
      apply (IH i).
      * exact (kf_node_cont I evs T i Hkf).
      * exact (exit_codes_in_node_cont S I evs T i Hex).
      * apply (halt_inv_sstep S c (evs i) (nx i) (sstep_cfg_sub segs CfgStep.kit_cfg _ _ _ (Hcomp i))). split.
        -- exact (kf_node_evs I evs T i Hkf Hnil).
        -- exact (exit_codes_in_node_evs S I evs T i Hex Hnil).
  - (* [comment removed for export] *)
    destruct (m_halted (cfg_model c)) as [code|] eqn:Hc; [| exfalso; exact (Hh eq_refl)].
    destruct (Hinv code Hc) as [Hin Hk].
    exact (must_exit_in_at_cfg_halted _ _ _ _ _ Hc Hin Hk).
  - (* [comment removed for export] *)
    apply IH; [exact (kf_eq _ _ Heq Hkf) | exact (exit_codes_in_eq _ _ _ Heq Hex) | exact Hinv].
Qed.



(* [comment removed for export] *)
Corollary realizes_must_exit_running : forall S c T,
  realizes segs c T -> kf T -> exit_codes_in S T ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg CfgStep.kit_cfg segs S c.
Proof.
  intros S c T H Hkf Hex Hrun.
  exact (realizes_must_exit S c T H Hkf Hex (halt_inv_of_running S c Hrun)).
Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition root_obligation_core_f (img : Image) (lim : Z) (S : ProcInput -> TSet) : Prop :=
  forall sp brk0 mb rnd inp,
    valid_entry img (mkEntry sp brk0 mb rnd) inp ->
    valid_input_core inp ->
    realizes (img_segments img)
      (init_config (img_segments img) (img_init_pc img) (img_phdrs img) sp brk0 mb rnd lim inp)
      (S inp).

(* [comment removed for export] *)
Lemma root_obligation_core_of_f : forall img lim S,
  root_obligation_core_f img lim S -> root_obligation_core img lim S.
Proof. intros img lim S H. apply root_obligation_core_of_realizes. exact H. Qed.

(* [comment removed for export] *)
Definition exit_codes_allowed (Codes : list word) (S : ProcInput -> TSet) : Prop :=
  forall inp tr code fs, valid_input_core inp -> S inp tr -> In (ExitEv code fs) tr -> In code Codes.

(* [comment removed for export] *)
Lemma init_config_running : forall segs pc ph sp brk0 mb rnd lim inp,
  m_halted (cfg_model (init_config segs pc ph sp brk0 mb rnd lim inp)) = None.
Proof. intros. reflexivity. Qed.


(* [comment removed for export] *)
Theorem must_exit_in_of_root_f : forall (Codes : list word) img lim S en inp,
  root_obligation_core_f img lim S ->
  kill_free S ->
  exit_codes_allowed Codes S ->
  valid_entry img en inp ->
  valid_input inp ->
  must_exit_in_scfg CfgStep.kit_cfg Codes img lim en inp.
Proof.
  intros Codes [segs pc ph] lim S [sp brk0 mb rnd] inp Hroot Hkf Hex He Hv.
  pose proof (valid_input_core_of_valid_input _ Hv) as Hc.
  cbn [must_exit_in_scfg].
  apply (realizes_must_exit_running segs Codes _ (S inp)).
  - exact (Hroot sp brk0 mb rnd inp He Hc).
  - intros tr sig fs Htr. exact (Hkf inp tr sig fs Hc Htr).
  - intros tr code fs Htr. exact (Hex inp tr code fs Hc Htr).
  - apply init_config_running.
Qed.

(* [comment removed for export] *)
Theorem halts_of_root_f : forall (Codes : list word) img S,
  root_obligation_core_f img source_alloc_limit S ->
  kill_free S ->
  exit_codes_allowed Codes S ->
  halts_allowed_T_scfg CfgStep.kit_cfg Codes img.
Proof.
  intros Codes img S Hroot Hkf Hex.
  intros en inp He Hv.
  exact (must_exit_in_of_root_f Codes img source_alloc_limit S en inp Hroot Hkf Hex He Hv).
Qed.




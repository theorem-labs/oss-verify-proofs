(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg BWorld Spec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Good.
Variable S : list word.

Definition ev_good (e : event) : Prop :=
  match e with
  | KillEv _ _ => False
  | ExitEv code _ => In code S
  | _ => True
  end.

(* [comment removed for export] *)
Definition tgood (T : TSet) : Prop := forall tr, T tr -> Forall ev_good tr.

Lemma Forall_is_prefix {A} (P : A -> Prop) : forall l1 l2,
  is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
  induction l1 as [|x xs IH]; intros [|y ys] Hp Hl; cbn in Hp.
  - constructor.
  - constructor.
  - destruct Hp.
  - destruct Hp as [-> Hp]. inversion Hl; subst. constructor; [assumption | eapply IH; eauto].
Qed.

Lemma tgood_eq : forall T T', t_eq T T' -> tgood T' -> tgood T.
Proof. intros T T' Heq Hg tr Htr. apply Hg. apply Heq. exact Htr. Qed.

Lemma tgood_nil : tgood t_nil.
Proof. intros tr ->. constructor. Qed.

Lemma tgood_emit : forall evs T, Forall ev_good evs -> tgood T -> tgood (t_emit evs T).
Proof.
  intros evs T He HT tr [Hp | (tr' & -> & Htr')].
  - eapply Forall_is_prefix; eauto.
  - apply Forall_app. split; [exact He | exact (HT _ Htr')].
Qed.

Lemma tgood_emit_inv : forall evs T, tgood (t_emit evs T) -> T [] -> Forall ev_good evs /\ tgood T.
Proof.
  intros evs T Hg H0. split.
  - rewrite <- (app_nil_r evs). apply Hg. right. exists []. split; [reflexivity | exact H0].
  - intros tr Htr.
    assert (Ha : Forall ev_good (evs ++ tr)).
    { apply Hg. right. exists tr. split; [reflexivity | exact Htr]. }
    apply Forall_app in Ha. exact (proj2 Ha).
Qed.

Lemma tgood_alt : forall (I : Type) (f : I -> TSet), (forall i, tgood (f i)) -> tgood (t_alt f).
Proof. intros I f H tr [i Hi]. exact (H i tr Hi). Qed.

Lemma tgood_alt_inv : forall (I : Type) (f : I -> TSet) i, tgood (t_alt f) -> tgood (f i).
Proof. intros I f i H tr Htr. apply H. exists i. exact Htr. Qed.

Lemma tgood_alt2 : forall A B, tgood A -> tgood B -> tgood (t_alt2 A B).
Proof. intros A B HA HB tr [H|H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Lemma tgood_exit : forall code fs, In code S -> tgood (t_exit code fs).
Proof.
  intros code fs Hin. unfold t_exit. apply tgood_emit; [| apply tgood_nil].
  constructor; [exact Hin | constructor].
Qed.

Lemma Forall_ev_good_writes : forall ch s, Forall ev_good (W ch s).
Proof. intros ch s. unfold W. apply Forall_map. apply Forall_forall. intros x _. exact I. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition me_inv (c : config) : Prop :=
  m_halted (cfg_model c) = None
  \/ exists code, m_halted (cfg_model c) = Some code /\ In code S /\ m_killed (cfg_model c) = None.

Lemma m_halted_proc : forall m1 m2, m_proc m1 = m_proc m2 -> m_halted m1 = m_halted m2.
Proof. intros m1 m2 H. unfold m_halted. now rewrite H. Qed.

(* [comment removed for export] *)
Lemma sstep_me_inv : forall c evs c',
  m_halted (cfg_model c) = None ->
  sstep segs c evs (SNext c') ->
  Forall ev_good evs ->
  me_inv c'.
Proof.
  intros c evs c' Hh Hs Hg.
  inversion Hs; subst; unfold me_inv; cbn [cfg_model] in *.
  - (* [comment removed for export] *)
    left.
    match goal with
    | [ H : mi_account_step _ _ _ = MachineOk (_, _) |- _ ] =>
        destruct (mi_account_step_model_frame _ _ _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _);
        rewrite (m_halted_proc _ _ Hp); assumption
    end.
  - (* [comment removed for export] *)
    left.
    match goal with
    | [ H : materialize_model_accesses _ _ = Some _ |- _ ] =>
        destruct (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _);
        rewrite (m_halted_proc _ _ Hp); assumption
    end.
  - (* [comment removed for export] *)
    right.
    match goal with
    | [ H : m_halted ?m = Some ?code, K : m_killed ?m = None |- _ ] =>
        exists code; split; [exact H | split; [| exact K]]
    end.
    apply Forall_app in Hg. destruct Hg as [_ Hg]. inversion Hg; subst. assumption.
  - (* [comment removed for export] *)
    exfalso. apply Forall_app in Hg. destruct Hg as [_ Hg]. inversion Hg; subst. assumption.
Qed.

Theorem realizes0_must_exit : forall c T,
  realizes0 segs c T -> tgood T -> me_inv c -> must_exit_in_at_cfg ACFG segs S c.
Proof.
  intros c T Hr.
  induction Hr as [c I evs nx T i0 Hnode Hnx IH | c Hh | c T T' Hr IH Heq]; intros Hg Hinv.
  - destruct Hnode as [Hsnd Hcmp].
    destruct Hinv as [Hnone | (code & Hh & Hin & Hk)].
    + apply must_exit_in_at_cfg_running.
      * exact Hnone.
      * exists (evs i0), (SNext (nx i0)). exact (Hsnd i0).
      * intros e Herr. destruct (Hcmp e SError Herr) as (i & _ & Hst). discriminate Hst.
      * intros e c' Hs. destruct (Hcmp e (SNext c') Hs) as (i & He & Hst).
        assert (Ec : c' = nx i) by congruence. subst c' e.
        assert (H0 : T i []) by (eapply realizes0_nonempty; exact (Hnx i)).
        destruct (tgood_emit_inv (evs i) (T i) (tgood_alt_inv I (fun j => t_emit (evs j) (T j)) i Hg) H0)
          as [Hevs HTi].
        apply (IH i HTi).
        exact (sstep_me_inv c (evs i) (nx i) Hnone (sstep_cfg_sub segs ACFG _ _ _ (Hsnd i)) Hevs).
    + apply (must_exit_in_at_cfg_halted ACFG segs S c code Hh Hin Hk).
  - destruct Hinv as [Hnone | (code & Hh' & Hin & Hk)]; [congruence |].
    apply (must_exit_in_at_cfg_halted ACFG segs S c code Hh' Hin Hk).
  - apply IH; [| exact Hinv]. exact (tgood_eq T T' Heq Hg).
Qed.

(* [comment removed for export] *)
Theorem realizes_pinned_must_exit : forall c T,
  realizes segs (BW:=bw_pinned) c T -> tgood T ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg ACFG segs S c.
Proof.
  intros c T Hr Hg Hh.
  apply (realizes0_must_exit c T).
  - exact (rz_unwrap segs (BW:=bw_pinned) c T Hr (never_excused_pinned segs c)).
  - exact Hg.
  - left. exact Hh.
Qed.

End WithSegs.
End Good.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma exit_code_any : forall z, (0 <= z < 256)%Z -> In (exit_code z) AnyExit.codes.
Proof. intros z Hz. unfold exit_code, AnyExit.codes. apply in_byte_codes. exact Hz. Qed.

Lemma tgood_die : forall msg fs, tgood AnyExit.codes (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply tgood_emit; [apply Forall_ev_good_writes |].
  apply tgood_exit. apply exit_code_any. lia.
Qed.

Lemma tgood_body : forall data fs, tgood AnyExit.codes (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  repeat (first [ apply tgood_die
                | match goal with |- tgood _ (if ?b then _ else _) => destruct b end
                | cbv zeta ]).
  apply tgood_emit; [apply Forall_ev_good_writes |].
  apply tgood_exit. apply exit_code_any. lia.
Qed.

Theorem tgood_spec : forall argv fs, tgood AnyExit.codes (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [| a0 [| path [| x l]]]; try apply tgood_die.
  repeat match goal with
         | |- tgood _ (if ?b then _ else _) => destruct b
         | |- tgood _ (match ?o with Some _ => _ | None => _ end) => destruct o
         end;
    try apply tgood_die.
  - apply tgood_alt2; [apply tgood_die | unfold t_opened_dir; apply tgood_die].
  - apply tgood_alt2; [apply tgood_die | unfold t_opened; apply tgood_body].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem halts_of_realizes : forall segs pc ph (T : ProcInput -> TSet),
  (forall inp, tgood AnyExit.codes (T inp)) ->
  (forall sp brk mbase rdraw inp,
     valid_entry (mkImage segs pc ph) (mkEntry sp brk mbase rdraw) inp -> valid_input inp ->
     realizes segs (BW:=bw_pinned) (init_config segs pc ph sp brk mbase rdraw source_alloc_limit inp) (T inp)) ->
  halts_allowed_T_scfg ACFG AnyExit.codes (mkImage segs pc ph).
Proof.
  intros segs pc ph T HT HR [sp brk mbase rdraw] inp Hen Hinp.
  cbn [must_exit_in_scfg].
  apply (realizes_pinned_must_exit AnyExit.codes segs _ (T inp) (HR sp brk mbase rdraw inp Hen Hinp) (HT inp)).
  unfold init_config. cbn [cfg_model]. apply m_halted_init_model.
Qed.

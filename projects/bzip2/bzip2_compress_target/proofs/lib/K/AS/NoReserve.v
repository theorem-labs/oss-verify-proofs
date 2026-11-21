(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap's cut-only node and RomBase.sys_rob at the nodes). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import
  SimInv ExitSim PropExec CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac SpinAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require Import CfgStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common.Cfg Require RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
  materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
  = Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_munmap_inv_lazy : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite materialize_model_accesses_nil in Hmat; inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + right.
      match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite materialize_munmap_eff_nil in Hmat; inversion Hmat; subst
      end.
      reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite materialize_model_accesses_nil in Hmat
      | rewrite materialize_munmap_eff_nil in Hmat ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6 | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6
      | rewrite m_killed_of_m_halted_none in H6;
        [| rewrite munmap_model_halted; exact Hh] ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* munmap is an alloc-family injected call at the revision, so the node
   lives over the config-filtered step: the ENOMEM child is a refusal and
   is dropped there, while the cut returns 0 and is not one. *)
Lemma sstep_cfg_munmap_inv_lazy : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep_cfg segs kit_cfg (mkCfg ms model) evs st ->
  evs = [] /\
  st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
  destruct (sstep_munmap_inv_lazy ms model x8 evs st Hh Hsvc Hno Hargs
              (sstep_cfg_sub segs kit_cfg _ _ _ Hss))
    as [-> [(e & He & ->) | ->]].
  - exfalso.
    apply sstep_cfg_next_iff in Hss as [_ Hns]. apply Hns.
    split; [| split].
    + exact (kit_pending_off_sysno segs ms model x8 215 Hsvc Hno eq_refl).
    + rewrite (child_refusal_b_set_gpr0 segs ms model x8 (errno_ret e) model Hsvc Hh).
      exact (refusal_b_munmap_errno (sys_input segs ms x8) model e Hno He).
    + exists x8, (munmap_eff ms),
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model), [].
      cbn [cfg_ms cfg_model]. split; [exact Hsvc | split].
      * exact (munmap_ok segs ms x8 model Hno Hargs).
      * unfold munmap_eff. cbn [eff_ret].
        apply refusal_b_munmap_below; [exact Hno|].
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
  - split; reflexivity.
Qed.

Lemma node_munmap_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                  model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs.
  split.
  - intros []. apply (sstep_cfg_syscall segs kit_cfg ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + apply spurious_refusal_not_refusal. unfold munmap_eff. cbn [eff_ret].
      apply refusal_b_munmap_below; [exact Hno|].
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_munmap_eff_nil.
  - intros e st Hss.
    destruct (sstep_cfg_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

Lemma srz_munmap_lazy : forall ms model x8 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hsvc Hno Hargs Hc.
  eapply srz_silent1; [apply (node_munmap_lazy ms model x8); assumption
                     | eapply RomBase.sys_rob_memfree; [exact Hsvc | rewrite Hno; exact RomBase.memfree_215] | exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive msteps_acc
    : machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step_accesses segs ms
      = MachineOk (@mkAccessReport machine_state ms1 ranges) ->
    msteps_acc ms1 ms2 accs ->
    msteps_acc ms ms2 (ranges ++ accs).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End WithFP1.
(* [comment removed for export] *)
Section WithFP2.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.

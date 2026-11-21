(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied, namespace aside, from simdjson/fuzz_utf8's lib/Common/SegLift.v: the lift of a walk over a binary's own segments to the run's segment list, without its spin leaf (this tree's walks have none), each node carrying RomBase.sys_rob; taken in part from projects/simdjson/fuzz_utf8/proofs/lib/TopLevel.v, lines 6-7, 286-287, 305-308, 327-328, 337-338, 498-499. *)
(* THE SEGMENT-LIST LIFT FOR [srealizes].
   The symbolic start-up realizes over the BARE image segments; [Run.run_scfg] -- and so
   [LibA.TopLevelGen.side_ok_of_srealizes] -- runs over [Run.run_segments segs inp sp mbase],
   which is [segs ++ vdso_segments (in_kernel inp) sp mbase].  This file carries a realization
   from the shorter list to the longer one AT THE SAME CONFIGURATION.

   WHY THE CONFIGURATION DOES NOT MOVE.  [RiscvSemantics.ms_rom] is read by [ms_read_byte] and
   so by [Run.sys_input]'s read view; a lift that rewrote the ROM inside the induction would
   change what every syscall along the way may read, and [node_ok]'s soundness half -- proved
   against the SHORT list -- could not cover the extra outcomes.  So the ROM change is a
   separate step: [RomStable.srealizes_wrom], which needs each node's [RomBase.sys_rob] (the
   premise [SpinAlg.srz_node] now carries), and [RomStable.srun_init] composes the two.

   THE THREE SIDE CONDITIONS.  [tail] is non-executable (so every fetch path is unchanged:
   [TopLevel.code_read_app]) and non-writable (so [RiscvSemantics.wview] -- the only part of
   [sys_input] that reads the segment list -- is unchanged).  [segs] carries no kernel mapping
   of its own, i.e. it is the loader's list: that is what makes [Run.vdso_entry_fn segs] and
   [RiscvSemantics.range_meets_vvar segs] constantly answer "none", which is what lets
   [node_ok]'s "no SError" close the two arms where the longer list can diverge.  All three
   discharge by computation at the instantiation below. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem DecodeC.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import ShapeAlg DivergeSim SpinAlg RomBase.
Import ListNotations.
Open Scope bv_scope.

(* A list of loader segments carries no vDSO text, so [Run.vdso_entry_fn] has nothing to find. *)
Lemma find_vdso_text_none : forall l,
  Forall (fun s => seg_kernel_map s = false) l -> find seg_vdso_text l = None.
Proof.
  induction l as [|s l IH]; intro H; [reflexivity|].
  inversion H as [|s0 l0 Hs Hl]; subst. cbn [find].
  unfold seg_vdso_text. unfold seg_kernel_map in Hs.
  destruct (seg_kind s); [apply IH; exact Hl | discriminate Hs | discriminate Hs].
Qed.

Section SegLift.

Variables segs tail : list Segment.
Hypothesis NX : Forall (fun s => seg_executable s = false) tail.
Hypothesis NW : Forall (fun s => seg_writable   s = false) tail.
Hypothesis NL : Forall (fun s => seg_kernel_map s = false) segs.

(* ---------- what the SHORT list cannot say ---------- *)

Lemma vvar_byte_at_segs : forall a, vvar_byte_at segs a = false.
Proof.
  intros a. unfold vvar_byte_at.
  destruct (find_segment segs (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
  apply fs_in in E. rewrite Forall_forall in NL. specialize (NL s E).
  unfold seg_vdso_vvar. unfold seg_kernel_map in NL.
  destruct (seg_kind s); [reflexivity | discriminate NL | discriminate NL].
Qed.

Lemma range_meets_vvar_segs : forall n a, range_meets_vvar segs a n = false.
Proof.
  induction n as [|n IH]; intros a; cbn [range_meets_vvar]; [reflexivity|].
  rewrite vvar_byte_at_segs, IH. reflexivity.
Qed.

Lemma vdso_entry_fn_segs : forall pc, vdso_entry_fn segs pc = None.
Proof.
  intros pc. unfold vdso_entry_fn, vdso_image, vdso_text_seg.
  rewrite (find_vdso_text_none segs NL). reflexivity.
Qed.

(* ---------- the writable view, the only segment-list dependence of [sys_input] ---------- *)

Lemma wview_eq : forall m a, wview (segs ++ tail) m a = wview segs m a.
Proof.
  intros m a. unfold wview. destruct (m a); [reflexivity|].
  destruct (find_segment segs (bv_unsigned a) 1) as [s|] eqn:E.
  - rewrite (fs_app_some segs tail _ _ _ E). reflexivity.
  - rewrite (fs_app_none segs tail _ _ E).
    destruct (find_segment tail (bv_unsigned a) 1) as [s|] eqn:E2; [|reflexivity].
    apply fs_in in E2. rewrite Forall_forall in NW. rewrite (NW s E2). reflexivity.
Qed.

Lemma sys_input_eq : forall ms x8, sys_input (segs ++ tail) ms x8 = sys_input segs ms x8.
Proof.
  intros ms x8. unfold sys_input. f_equal.
  unfold ms_writable_byte. apply FunctionalExtensionality.functional_extensionality.
  intro a. apply wview_eq.
Qed.

(* [RomBase.sys_rob] at a node: [sys_input] is the same over both lists, so the node's
   robustness to a larger backing carries over unchanged. *)
Lemma sys_rob_app : forall c, sys_rob segs c -> sys_rob (segs ++ tail) c.
Proof.
  intros c H r x8 Hr Hs o. rewrite !sys_input_eq. exact (H r x8 Hr Hs o).
Qed.

(* ---------- one accounted machine step ---------- *)

Lemma step_accesses_app : forall ms rep,
  RiscvSemantics.step_accesses segs ms = MachineOk rep ->
  RiscvSemantics.step_accesses (segs ++ tail) ms = MachineOk rep.
Proof.
  intros ms rep. unfold RiscvSemantics.step_accesses.
  rewrite (fetch_word_app segs tail NX (ms_pc ms)),
          (fetch_word_ov_app segs tail NX (ms_mem ms) (ms_pc ms)),
          (fetch_tail_any_app segs tail NX (ms_mem ms) (ms_pc ms)).
  destruct (fetch_word segs (ms_pc ms)) as [w|];
    [intro H; exact (decode_app segs tail _ _ _ H)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|];
    [intro H; exact (decode_app segs tail _ _ _ H)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|];
    [intro H; exact (decode_app segs tail _ _ _ H)|].
  destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:FF;
    [|intro H; discriminate H|intro H; discriminate H].
  intros _. exfalso. exact (fetch_failure_not_ok segs (ms_mem ms) (ms_pc ms) _ FF).
Qed.

Lemma mi_account_step_app : forall ms model r,
  mi_account_step segs ms model = MachineOk r ->
  mi_account_step (segs ++ tail) ms model = MachineOk r.
Proof.
  intros ms model r. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |] eqn:E;
    [|intro H; discriminate H|intro H; discriminate H].
  rewrite (step_accesses_app ms rep E). intro H; exact H.
Qed.

(* A step the SHORT list declines for the MODEL's reason is not a step the LONGER list
   completes.  Only [interp_eff_accesses]'s vvar arm and the fetch classifier can answer
   [MachineUnmodeled], and [range_meets_vvar segs] is constantly false here, so the former
   needs the read to have SUCCEEDED -- which [ov_read_app] carries -- and the latter answers
   through [fetch_failure], which is never [MachineOk] on either list. *)
Lemma interp_unmodeled_app : forall t m,
  interp_eff_accesses segs t m = MachineUnmodeled ->
  interp_eff_accesses (segs ++ tail) t m = MachineUnmodeled.
Proof.
  intros t; induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m H;
    cbn [interp_eff_accesses] in H |- *; try exact H.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:E.
    + rewrite (ov_read_app segs tail _ _ _ _ E).
      lazymatch type of H with context [interp_eff_accesses segs ?t0 ?m0] =>
        destruct (interp_eff_accesses segs t0 m0) as [rep| |] eqn:E2 end;
        [discriminate H|discriminate H|].
      rewrite (IH _ _ E2). reflexivity.
    + rewrite range_meets_vvar_segs in H. discriminate H.
  - destruct (store_ok segs m a (width_bytes n)) eqn:E; [|discriminate H].
    rewrite (store_ok_app segs tail _ _ _ E).
    lazymatch type of H with context [interp_eff_accesses segs ?t0 ?m0] =>
      destruct (interp_eff_accesses segs t0 m0) as [rep| |] eqn:E2 end;
      [discriminate H|discriminate H|].
    rewrite (IH _ E2). reflexivity.
Qed.

Lemma decode_unmodeled_app : forall ms w,
  decode_exec_accesses segs ms w = MachineUnmodeled ->
  decode_exec_accesses (segs ++ tail) ms w = MachineUnmodeled.
Proof.
  intros ms w. unfold decode_exec_accesses.
  destruct (is_ecall w); [auto|].
  destruct (decode_any w) as [[i isz]|]; [|auto].
  lazymatch goal with |- context [interp_eff_accesses segs ?t0 ?m0] =>
    destruct (interp_eff_accesses segs t0 m0) as [rep| |] eqn:E end;
    [ destruct (@access_value _ rep) as [cc mm]; intro H; discriminate H
    | intro H; discriminate H
    | ].
  rewrite (interp_unmodeled_app _ _ E). auto.
Qed.

Lemma step_accesses_unmodeled_not_ok : forall ms rep,
  RiscvSemantics.step_accesses segs ms = MachineUnmodeled ->
  RiscvSemantics.step_accesses (segs ++ tail) ms <> MachineOk rep.
Proof.
  intros ms rep. unfold RiscvSemantics.step_accesses.
  rewrite (fetch_word_app segs tail NX (ms_pc ms)),
          (fetch_word_ov_app segs tail NX (ms_mem ms) (ms_pc ms)),
          (fetch_tail_any_app segs tail NX (ms_mem ms) (ms_pc ms)).
  destruct (fetch_word segs (ms_pc ms)) as [w|];
    [intros H HW; rewrite (decode_unmodeled_app ms w H) in HW; discriminate HW|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|];
    [intros H HW; rewrite (decode_unmodeled_app ms w H) in HW; discriminate HW|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|];
    [intros H HW; rewrite (decode_unmodeled_app ms w H) in HW; discriminate HW|].
  intros _ HW.
  destruct (fetch_failure (segs ++ tail) (ms_mem ms) (ms_pc ms)) eqn:FF;
    [|discriminate HW|discriminate HW].
  exact (fetch_failure_not_ok (segs ++ tail) (ms_mem ms) (ms_pc ms) _ FF).
Qed.

Lemma mi_account_step_unmodeled_not_ok : forall ms model r,
  mi_account_step segs ms model = MachineUnmodeled ->
  mi_account_step (segs ++ tail) ms model <> MachineOk r.
Proof.
  intros ms model r. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |] eqn:EN.
  - destruct (materialize_model_accesses model (@accessed_ranges _ rep));
      intro H; discriminate H.
  - intro H; discriminate H.
  - intros _.
    destruct (RiscvSemantics.step_accesses (segs ++ tail) ms) as [rep'| |] eqn:EW;
      [|intro H; discriminate H|intro H; discriminate H].
    exfalso. exact (step_accesses_unmodeled_not_ok ms rep' EN EW).
Qed.

(* ---------- the shape algebra ---------- *)

(* If the SHORT list does not complete the instruction at [mkCfg ms model], then it has an
   SError step there: the fault arm, or -- since [vdso_entry_fn segs] is constantly [None]
   under [NL] -- the unmodeled arm.  This is the "entire SError family" the lift leans on. *)
Lemma narrow_instr_serror : forall ms model,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  (forall r, mi_account_step segs ms model <> MachineOk r) ->
  sstep_cfg segs ACFG (mkCfg ms model) [] SError.
Proof.
  intros ms model Hh Hsvc Hno.
  destruct (mi_account_step segs ms model) as [r| |] eqn:EN.
  - exfalso. exact (Hno r eq_refl).
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled;
      [eassumption|eassumption|eassumption|apply vdso_entry_fn_segs].
Qed.

Lemma narrow_not_ok : forall ms model,
  (forall r, mi_account_step (segs ++ tail) ms model <> MachineOk r) ->
  (forall r, mi_account_step segs ms model <> MachineOk r).
Proof. intros ms model HW r EN. exact (HW r (mi_account_step_app _ _ _ EN)). Qed.

(* FORWARD: a completed step of the short list is a completed step of the longer one. *)
Lemma sstep_cfg_app_fwd : forall c e c',
  sstep_cfg segs ACFG c e (SNext c') -> sstep_cfg (segs ++ tail) ACFG c e (SNext c').
Proof.
  intros c e c' H. remember (SNext c') as st eqn:Hst. revert c' Hst.
  destruct H; intros cc Hst; try discriminate Hst; injection Hst as <-.
  - eapply sstep_cfg_instr; [eassumption|eassumption|apply mi_account_step_app; eassumption].
  - (* the vDSO arm cannot fire on the loader's own list *)
    exfalso. match goal with Hfn : vdso_entry_fn segs _ = Some _ |- _ =>
      rewrite vdso_entry_fn_segs in Hfn; discriminate Hfn end.
  - eapply sstep_cfg_syscall; rewrite ?sys_input_eq; eassumption.
  - eapply sstep_cfg_exit; rewrite ?sys_input_eq; eassumption.
  - eapply sstep_cfg_killed; rewrite ?sys_input_eq; eassumption.
Qed.

(* REVERSE: where the short list has no SError step, every step of the longer list is one
   the short list already has. *)
Lemma sstep_cfg_app_rev : forall c e st,
  sstep_cfg (segs ++ tail) ACFG c e st ->
  (forall e0, ~ sstep_cfg segs ACFG c e0 SError) ->
  sstep_cfg segs ACFG c e st.
Proof.
  intros c e st H. destruct H; intro NoErr.
  - (* instr: the longer list completed it, so the short list did too, identically *)
    destruct (mi_account_step segs ms model) as [[ms1 model1]| |] eqn:EN.
    + match goal with HW : mi_account_step (segs ++ tail) _ _ = _ |- _ =>
        rewrite (mi_account_step_app _ _ _ EN) in HW; injection HW; intros; subst end.
      eapply sstep_cfg_instr; eassumption.
    + exfalso. eapply NoErr. eapply sstep_cfg_instr_fault; eassumption.
    + exfalso. eapply NoErr. eapply sstep_cfg_instr_unmodeled;
        [eassumption|eassumption|eassumption|apply vdso_entry_fn_segs].
  - (* instr_fault *)
    apply narrow_instr_serror; [eassumption|eassumption|].
    apply narrow_not_ok. intros r Hr. match goal with
      HW : mi_account_step (segs ++ tail) _ _ = MachineFault |- _ =>
        rewrite Hr in HW; discriminate HW end.
  - (* instr_unmodeled *)
    apply narrow_instr_serror; [eassumption|eassumption|].
    apply narrow_not_ok. intros r Hr. match goal with
      HW : mi_account_step (segs ++ tail) _ _ = MachineUnmodeled |- _ =>
        rewrite Hr in HW; discriminate HW end.
  - (* vdso_call: the longer list declined the instruction, so the short list has an SError *)
    exfalso. eapply NoErr. apply narrow_instr_serror; [eassumption|eassumption|].
    apply narrow_not_ok. intros r Hr. match goal with
      HW : mi_account_step (segs ++ tail) _ _ = MachineUnmodeled |- _ =>
        rewrite Hr in HW; discriminate HW end.
  - (* vdso_materialization_fault *)
    apply narrow_instr_serror; [eassumption|eassumption|].
    apply narrow_not_ok. intros r Hr. match goal with
      HW : mi_account_step (segs ++ tail) _ _ = MachineUnmodeled |- _ =>
        rewrite Hr in HW; discriminate HW end.
  - (* vdso_unmodeled *)
    apply narrow_instr_serror; [eassumption|eassumption|].
    apply narrow_not_ok. intros r Hr. match goal with
      HW : mi_account_step (segs ++ tail) _ _ = MachineUnmodeled |- _ =>
        rewrite Hr in HW; discriminate HW end.
  - eapply sstep_cfg_syscall; rewrite <- ?sys_input_eq; eassumption.
  - eapply sstep_cfg_syscall_materialization_fault; rewrite <- ?sys_input_eq; eassumption.
  - eapply sstep_cfg_exit; rewrite <- ?sys_input_eq; eassumption.
  - eapply sstep_cfg_killed; rewrite <- ?sys_input_eq; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; rewrite <- ?sys_input_eq; eassumption.
Qed.

Lemma node_ok_app : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  node_ok segs c I evs nx -> node_ok (segs ++ tail) c I evs nx.
Proof.
  intros c I evs nx [Hcomp Hsound].
  assert (NoErr : forall e, ~ sstep_cfg segs ACFG c e SError).
  { intros e0 He0. destruct (Hsound e0 SError He0) as (i & _ & Hbad). discriminate Hbad. }
  split.
  - intro i. exact (sstep_cfg_app_fwd c (evs i) (nx i) (Hcomp i)).
  - intros e st Hss. exact (Hsound e st (sstep_cfg_app_rev c e st Hss NoErr)).
Qed.

(* THE LIFT.  The configuration is the same on both sides; the segment list is the only thing
   that moves, and it moves through exactly [node_ok] and [sys_rob]. *)
Lemma srealizes_app : forall c T, srealizes segs c T -> srealizes (segs ++ tail) c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c T T' H IH Heq].
  - exact (srz_node (segs ++ tail) c I evs nx T i0 (node_ok_app c I evs nx Hnode)
             (sys_rob_app c Hrob) IH).
  - exact (srz_halt (segs ++ tail) c Hh).
  - exact (srz_conseq (segs ++ tail) c T T' IH Heq).
Qed.

End SegLift.

(* ---------- the instantiation: [tail := vdso_segments (in_kernel inp) sp mbase] ---------- *)

Local Transparent vdso_segments.

(* The sibling of [TopLevel.vdso_nonexec]: BOTH records of [Run.vdso_segments] are
   [seg_perms := "r--"], so neither is writable either. *)
Lemma vdso_nonwritable : forall kb (sp mbase : word),
  Forall (fun s => seg_writable s = false) (vdso_segments kb sp mbase).
Proof.
  intros kb sp mbase. unfold vdso_segments. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; repeat constructor.
Qed.

Global Opaque vdso_segments.

(* The conclusion is SYNTACTICALLY over [Run.run_segments segs inp sp mbase] -- the very list
   [Run.run_scfg] runs over and [LibA.TopLevelGen.side_ok_of_srealizes] asks for -- because
   [run_segments segs inp sp mb] IS [segs ++ vdso_segments (in_kernel inp) sp mb] by
   definition (Run.v at this port's model revision). *)
Lemma srealizes_run_segments : forall (segs : list Segment) (inp : ProcInput) (sp mbase : word) c T,
  Forall (fun s => seg_kernel_map s = false) segs ->
  srealizes segs c T ->
  srealizes (run_segments segs inp sp mbase) c T.
Proof.
  intros segs inp sp mbase c T NL H. unfold run_segments.
  exact (srealizes_app segs (vdso_segments (in_kernel inp) sp mbase)
           (vdso_nonexec _ _ _) (vdso_nonwritable _ _ _) NL c T H).
Qed.

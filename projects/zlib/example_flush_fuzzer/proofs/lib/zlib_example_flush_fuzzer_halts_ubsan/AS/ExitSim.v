(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Reusable/YK0n.v at , lines 6-9, 12-15, 59-85, 136-157, 237-248, 314-317, 334-335, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.AS Require Import SimInv.
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.


Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.







Section WithSegs.
Variable segs : list Segment.
Variable code : word.


Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.


Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.







Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  -
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  -
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  -
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_call: its first premise is the same [MachineUnmodeled] () *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_materialization_fault () *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_unmodeled () *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
Qed.


Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.


Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.






Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.





End WithSegs.


















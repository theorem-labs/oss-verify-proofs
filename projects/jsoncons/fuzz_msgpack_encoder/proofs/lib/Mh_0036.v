(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed A_pages_in, A_pages_length, H_off_segments_above and 292 more; added fz_vdso_post, fz_vdso_write_regs, rz_silent_all and 1 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanAcct.v, 515 lines within its lines 78-1379. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite.
Module ErrEscape.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_lbu_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, isz) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = None ->
  range_meets_vvar segs (v_addi (getr regs rs) (bv_signed imm)) 1%nat = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
  intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread Hvv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hread, Hvv; rewrite ?bv_eqb0_is_x0 in Hread, Hvv.
  rewrite ov_rdn, b_addsext, Hread, Hvv.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_ld_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, isz) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = None ->
  range_meets_vvar segs (v_addi (getr regs rs) (bv_signed imm)) 8%nat = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
  intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread Hvv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hread, Hvv; rewrite ?bv_eqb0_is_x0 in Hread, Hvv.
  rewrite ov_rdn, b_addsext, Hread, Hvv.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma msteps_star_nil : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  star segs (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms ms' model Hh Hlazy H.
  induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
  - apply star_refl.
  - change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [| exact IH].
    apply (sstep_instr segs ms model ms1 model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma msteps_illegal_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  reaches_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  exists [], (mkCfg ms' model), [].
  split; [apply msteps_star_nil; assumption |].
  apply sstep_instr_fault; [assumption | assumption |].
  rewrite (mi_account_step_no_lazy segs ms' model Hlazy), Hill. reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section OmniWithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma illegal_exec : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] /\ o = OError (mkCfg ms model)).
Proof.
  intros ms model Hh Hlazy Hsvc Hill.
  apply exec_step; [exact Hh | | |].
  - exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
  - intros evs Hss. inversion Hss; subst; split; reflexivity.
  - intros evs c' Hnext. exfalso. inversion Hnext; subst; try congruence;
    (* the vDSO arms carry [MachineUnmodeled] where this state is
       [MachineFault], so they close the same way the ordinary
       instruction arm does *)
    match goal with H : mi_account_step segs ms model = _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
      discriminate
    end.
Qed.

(* [comment removed for export] *)
Lemma instr_exec : forall ms ms' model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  OmniRun.exec segs (mkCfg ms' model) Q ->
  OmniRun.exec segs (mkCfg ms model) Q.
Proof.
  intros ms ms' model Q Hh Hlazy Hsvc Hstep Hex.
  apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
  - apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros evs st Hss.
    exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
  - eapply exec_conseq; [exact Hex |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma msteps_exec : forall ms ms' model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  OmniRun.exec segs (mkCfg ms' model) Q ->
  OmniRun.exec segs (mkCfg ms model) Q.
Proof.
  intros ms ms' model Q Hh Hlazy Hm Hex.
  induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH]; [exact Hex |].
  eapply instr_exec; eauto.
Qed.

(* [comment removed for export] *)
Lemma msteps_illegal_exec : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] /\ o = OError (mkCfg ms' model)).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  eapply msteps_exec; [exact Hh | exact Hlazy | exact Hm |].
  apply illegal_exec; assumption.
Qed.

(* [comment removed for export] *)
Lemma fault_covered_at : forall ms model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  ~ unmodeled_at segs (mkCfg ms model).
Proof.
  intros ms model Hlazy Hsvc Hfault
    (_ & [(_ & Hum & _) | [(_ & Hum & _) | (x8 & Hsvc' & _)]]); cbn in *.
  - rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - (* the vDSO shape: same [MachineUnmodeled] against this fault *)
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - congruence.
Qed.

(* [comment removed for export] *)
Lemma msteps_illegal_errors : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  OmniRun.exec segs (mkCfg ms model) errors.
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
  intros tr o (_ & ->). exact I.
Qed.

(* [comment removed for export] *)
Lemma msteps_illegal_covered : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  OmniRun.coexec segs (mkCfg ms model) (covered segs).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  apply exec_coexec.
  eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
  intros tr o (_ & ->). unfold covered. apply fault_covered_at; assumption.
Qed.

(* [comment removed for export] *)
Lemma msteps_illegal_no_exit : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  forall code, ~ OmniRun.exec segs (mkCfg ms model) (exits_with code).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill code Hex.
  destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
    as (tr & o & Hm' & _ & ->).
  exact (exec_sound _ _ _ Hex _ _ Hm').
Qed.

Lemma msteps_illegal_not_never_errors : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  ~ OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill Hco.
  destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
    as (tr & o & Hm' & _ & ->).
  exact (coexec_sound _ _ _ _ Hm' _ Hco I).
Qed.

End OmniWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AllErrorWithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma illegal_all_traces_error : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms model Hh Hlazy Hsvc Hill.
  constructor.
  - exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
  - intros evs c' Hnext. inversion Hnext; subst; try congruence;
    match goal with H : mi_account_step segs ms model = _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
      discriminate
    end.
Qed.

(* [comment removed for export] *)
Lemma instr_all_traces_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  all_traces_error segs (mkCfg ms' model) ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hsvc Hstep Hall.
  constructor.
  - exists [], (SNext (mkCfg ms' model)).
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros evs c' Hnext.
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c')
                Hlazy Hsvc Hstep Hnext) as [_ Hto].
    inversion Hto; subst. exact Hall.
Qed.

(* [comment removed for export] *)
Lemma msteps_all_traces_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  all_traces_error segs (mkCfg ms' model) ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hm Hall.
  induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH].
  - exact Hall.
  - eapply instr_all_traces_error; eauto.
Qed.

(* [comment removed for export] *)
Lemma msteps_illegal_all_traces_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hm Hfinal_svc Hillegal.
  apply all_traces_error_iff. eapply msteps_illegal_errors; eassumption.
Qed.

End AllErrorWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section NoUnmodeledWithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma star_stuck_refl : forall c tr c',
  (forall evs c2, ~ sstep segs c evs (SNext c2)) ->
  star segs c tr c' -> c' = c.
Proof.
  intros c tr c' Hno Hstar. inversion Hstar; subst; [reflexivity|].
  exfalso. eapply Hno; eassumption.
Qed.

(* [comment removed for export] *)
Lemma fault_no_unmodeled : forall ms model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms model Hlazy Hsvc Hfault (tr & c & Hstar & Hun).
  assert (Hno : forall evs c2, ~ sstep segs (mkCfg ms model) evs (SNext c2)).
  { intros evs c2 Hss. inversion Hss; subst; try congruence;
    match goal with H : mi_account_step segs ms model = _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in H;
      discriminate
    end. }
  rewrite (star_stuck_refl _ tr c Hno Hstar) in Hun.
  destruct Hun as (_ & [(_ & Hum & _) | [(_ & Hum & _) | (x8 & Hsvc' & _)]]);
    cbn in *.
  - rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - congruence.
Qed.

(* [comment removed for export] *)
Lemma instr_no_unmodeled : forall ms ms' model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  ~ reaches_unmodeled segs (mkCfg ms' model) ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms ms' model Hlazy Hsvc Hstep Hnext (tr & c & Hstar & Hun).
  inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hrest]; subst.
  - destruct Hun as (_ & [(_ & Hum & _) | [(_ & Hum & _) | (x8 & Hsvc' & _)]]);
      cbn in *.
    + rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in Hum.
      discriminate.
    + rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in Hum.
      discriminate.
    + congruence.
  - destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                Hlazy Hsvc Hstep Hss)
      as [_ Hc2].
    inversion Hc2; subst. apply Hnext. exists tr2, c. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma msteps_fault_no_unmodeled : forall ms ms' model,
  msteps segs ms ms' ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms ms' model Hm Hlazy Hsvc Hfault.
  destruct (m_halted model) as [code |] eqn:Hh.
  - (* [comment removed for export] *)
    intros (tr & c & Hstar & Hun).
    inversion Hstar as [| c1 evs c2 tr2 c3 Hss]; subst.
    + destruct Hun as (Hun & _). cbn in Hun. congruence.
    + pose proof (sstep_from_running segs _ _ _ Hss) as Hrun. cbn in Hrun. congruence.
  - apply coexec_covered. eapply msteps_illegal_covered; eassumption.
Qed.

End NoUnmodeledWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma err_escape_omni_run :
  forall segs pc ph sp brk0 mb rnd lim inp ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp errors.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  cbn [omni_run]. unfold init_config.
  eapply msteps_illegal_errors; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

(* [comment removed for export] *)
Lemma err_escape_omni_covered :
  forall segs pc ph sp brk0 mb rnd lim inp ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (covered (run_segments segs inp sp mb)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  cbn [omni_corun]. unfold init_config.
  eapply msteps_illegal_covered; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

(* [comment removed for export] *)
Lemma err_escape_omni_equiv :
  forall segs pc ph sp brk0 mb rnd lim inp T limT et ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_equiv (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) T limT et inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T limT et ms' Hm Hsvc Hill.
  left. eapply err_escape_omni_run; eassumption.
Qed.

(* [comment removed for export] *)
Lemma err_escape_omni_strong_equiv :
  forall segs pc ph sp brk0 mb rnd inp T et ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_strong_equiv (mkImage segs pc ph) T (mkEntry sp brk0 mb rnd) et inp.
Proof.
  intros segs pc ph sp brk0 mb rnd inp T et ms' Hm Hsvc Hill.
  split.
  - cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
  - eapply err_escape_omni_equiv; eassumption.
Qed.

(* [comment removed for export] *)
Lemma err_escape_equiv :
  forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
  left. apply bh_all_errors_iff. eapply err_escape_omni_run; eassumption.
Qed.

(* [comment removed for export] *)
Lemma err_escape_modeled :
  forall segs pc ph sp brk0 mb rnd lim inp ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  apply modeled_iff. cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
Qed.

(* [comment removed for export] *)
Lemma err_escape_strong_equiv :
  forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
  /\ Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
       target.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
  split; [eapply err_escape_modeled | eapply err_escape_equiv]; eassumption.
Qed.
End WithFP1.

End ErrEscape.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Mm.Mmap. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module ShapeAlg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WallSim.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ShapeAlg () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib7Classes;EquivalenceEpointwise_equivalenceC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01c59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_app_rC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00c59OSSVerify5KrLib7Mh_00368ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_nil_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic3iffC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib7Mh_00368ShapeAlg=t_writes_pickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg:t_write_chC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics?LinuxProcessSem5State5event02c59OSSVerify5KrLib7Mh_00368ShapeAlg8t_writesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;t_writes_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03c59OSSVerify5KrLib7Mh_00368ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib7Mh_00306CatSim:wevents_chC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_00368ShapeAlg@t_writes_ch_consC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses;reflexivityC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib7Mh_00306CatSim7weventsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgDt_writes_ch_exit_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WallSim>wevents_ch_fd1C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List7map_appC46Stdlib5Lists4List<firstn_skipnK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes6lengthK47Corelib4Init6Specif3sig01C47Corelib5Lists7ListDef5skipnC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryc59OSSVerify5KrLib7Mh_00368ShapeAlg7wr_fullC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allC56Stdlib5Arith8PeanoNat3Nat7le_reflC46Stdlib5Lists4List9skipn_allC47Corelib4Init6Specif9proj1_sigI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init6Specif3sig00C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveI59OSSVerify5KrLib7Mh_00306CatSim5wpick00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim5wpick01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim=wpick_weventsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim5wpick02C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indc59OSSVerify5KrLib7Mh_00368ShapeAlgIt_writes_ch_pick_exit_iffC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop?or_iff_morphismc59OSSVerify5KrLib7Mh_00368ShapeAlgAt_writes_exit_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:two_tracesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8pnode_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib7Mh_00264Scfg6fam_onC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C59OSSVerify5KrLib7Mh_00264ScfgCsstep_cfg_of_sstep'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=sstep_cfg_subI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00c59OSSVerify5KrLib7Mh_00368ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib7Mh_00264Scfg<fam_on_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_instrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem3Run<injected_armK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00264Scfg<fam_on_sysnoC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem3Run;InjectedArm00c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00368ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_of_iffC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00368ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC47Corelib4Init5Logic3notc59OSSVerify5KrLib7Mh_00368ShapeAlg<realizes_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg00C59OSSVerify5KrLib7Mh_00264ScfgCstar_cfg_halted_nilC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgC59OSSVerify5KrLib7Mh_00264Scfg<star_cfg_oneC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg02C59OSSVerify5KrLib7Mh_00264ScfgAobs_trace_cfg_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgBrealizes_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg@realizes_pclosedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg?realizes_admitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264ScfgEsstep_cfg_halted_noneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgAsstep_halted_noneC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02c59OSSVerify5KrLib7Mh_00368ShapeAlg7rz_pathC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg=realizes_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_indC4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgc59OSSVerify5KrLib7Mh_00368ShapeAlg<rz_path_starC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgCrealizes_no_sserrorC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib7Mh_00368ShapeAlg:t_alt_unitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgArealizes_nonemptyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg:t_eq_transC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00368ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3sum01K47Corelib4Init9Datatypes3sum02C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib7Mh_00368ShapeAlg7rz_alt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg9rz_cases1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputc59OSSVerify5KrLib7Mh_00368ShapeAlg7halt_evC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgK4ELinuxProcessSemantics?LinuxProcessSem5State5event04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_noneK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04c59OSSVerify5KrLib7Mh_00368ShapeAlgCsstep_cfg_svc_casesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8node_svcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offC59OSSVerify5KrLib7Mh_00264Scfg?not_spurious_onC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_svc_onC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;pnode_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg:node_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg:rz_silent1C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7rz_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim7fd1chanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC59OSSVerify5KrLib7Mh_00306CatSim;buf_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC59OSSVerify5KrLib7Mh_00306CatSim;write1_ok_nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib7Mh_00306CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim?sstep_write_invC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00c59OSSVerify5KrLib7Mh_00368ShapeAlg<pnode_write1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264Scfg?injected_arm_64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_write1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib7Mh_00307ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg06C59OSSVerify5KrLib7Mh_00307ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andK47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib7Mh_00368ShapeAlg9node_exitC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00368ShapeAlg8realizes02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8rz_emit1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:munmap_effC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim9munmap_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSimCmunmap_model_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSimDmunmap_model_no_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim@sstep_munmap_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim=page_round_upC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264Scfg@injected_arm_215C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_munmapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib7Mh_00387MmapSim8grant_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFpage_round_up_Z_nonnegC59OSSVerify5KrLib7Mh_00387MmapSim?grant_not_errnoC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC59OSSVerify5KrLib7Mh_00264Scfg>refusal_b_mmapC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_00387MmapSim<mmap_args_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocc59OSSVerify5KrLib7Mh_00368ShapeAlg>mmap_grant_effC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim<mmap_succ_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFmmap_grant_not_refusalC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC59OSSVerify5KrLib7Mh_00264ScfgGnot_spurious_nonrefusalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim;mmap_ok_invC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib7Mh_00264ScfgIinjected_family_off_allocC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude;bv_eqb_reflC59OSSVerify5KrLib7Mh_00264Scfg>spurious_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSimAmmap_no_unmodeledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSimAmmap_model_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim?mmap_model_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg9node_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim<mmap_fail_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264ScfgCnot_spurious_forcedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSimEENOMEM_in_mmap_errnosC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgAnode_mmap_nograntC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim8to_wexit00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgAt_writes_pick_nilC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib7Mh_00368ShapeAlg9rz_write1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgBt_writes_pick_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<to_wexit_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib7Mh_00368ShapeAlgEexitline_realizes_auxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00387WallSim7to_wall10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg:t_alt_wallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00387WallSim7to_wall00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WallSim>to_wall_mutindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WallSim;to_wallexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgAexitline_realizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg<rz_wall1_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgHt_writes_ch_exit_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg=t_writes_consC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00387MmapSim3twm10C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00387MmapSim3twm00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSimDmunmap_model_fd1chanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim?munmap_model_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg9rz_munmapC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00387MmapSim3twm20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:twm_mutindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg@twm_realizes_mutC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismc59OSSVerify5KrLib7Mh_00368ShapeAlg>t_alt_emit_nilC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib7Mh_00389AllocSim2<two_outcomesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg:t_outcomesC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?iff_equivalencec59OSSVerify5KrLib7Mh_00368ShapeAlg@t_writes_ch_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim6fdchanC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C59OSSVerify5KrLib7Mh_00306CatSim=write_ch_ok_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimBsstep_write_ch_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg=node_write_chC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim;to_wexit_ch00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;rz_write_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgEt_writes_ch_pick_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim?to_wexit_ch_indC1?~~~~~~~~~~~~~~~".

From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
  induction l as [|x l IH]; intros m a H.
  - destruct a; [apply is_prefix_nil | cbn in H; contradiction].
  - destruct a as [|y a]; cbn in *; [exact I|].
    destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
  induction l as [|x l IH]; intros a b H.
  - right. exists b. split; [reflexivity | exact H].
  - destruct b as [|y b]; cbn in H; [left; exact I|].
    destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
    + left. cbn. split; [reflexivity | exact Hp].
    + right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Hh11Th22trp;1p;4p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p9P0p1004mp4p710p8P0p1005Dp4p710p8P0p1005eR8p4p710p8P0P8p4p7210p8P0p1006Bp4p710p8p1006^p4p70R0p1007Np4p710R8p8P0p1007hp4p710R9p8P0p1008Dp4p710R:p8P0p1008bp4p7210R;p8P0P5p8p1009?p4p710R0P9p8P0P5p8p1009\p4p70R<P8p8P<P1p8P<P2p8P<p100:Jp4p7210p8P<P9p8P<p100:fp4p710R=p8P<p100;\p4p7210p8P<P0p8P<P:p8P<p100<Kp4p710p8P<P;p8P<p100=Fp4p710R0p8P<p100>@p4p710p8P<P4p8P<P3p4p710R3p8P<P5p8P<p100?<p4p7210p8P<P6p8P<p100@0p4p710R4p8P<p100JAp4p710R>p8P<p100MHp4p710R?p8P<p100OJp4p710R@p8P<p100@Mp4p710p8P<p100ASp4p7210RAp8P<p100B0p4p7210p8P<P7p8p100BOp4p7210R7P8p8P7P1p8P7P2p8P7P9p8P7P:p8P7P;p8P7p100C;p4p7210p8P7P3p8P7P5p8P7P6p8P7p100CXp4p710p8P>P=p8P>P0p8P>P5p8P>p100D_p4p710R0p8P>P4p8P?P=p8P?P5p8P?P0p8P?P4p8P@P=p8p100EAp4p70R=P8p8P=P9p8P=P:p8P=P;p8P=P5p8PAP9p8PAP5p8p100F7p4p710P5p8g00FVj12Tg00IJj41Tg00POj20Tg00QIg00RC#2f1R5f0RAO1R9f2P5O1[R5P5PAX09R9P9C1W210AAeW1o"). Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h02H1h12H2h22H0h31Hh41Th52T'h62trp;2p;1p;5p;4p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p9P0p1004mp4p710p8P0p1005Dp4p710p8P0p1005eR8p4p710p8P0P8p4p7210p8P0p1006Bp4p710p8p1006^p4p70R0p1007Np4p710R8p8P0p1007hp4p710R9p8P0p1008Dp4p710R:p8P0p1008bp4p7210R;p8P0P5p8p1009?p4p710R0P9p8P0P5p8p1009\p4p70R<P8p8P<P1p8P<P2p8P<p100:Jp4p7210p8P<P9p8P<p100:fp4p710R=p8P<p100;\p4p7210p8P<P0p8P<P:p8P<p100<Kp4p710p8P<P;p8P<p100=Fp4p710R0p8P<p100>@p4p710p8P<P4p8P<P3p4p710R3p8P<P5p8P<p100?<p4p7210p8P<P6p8P<p100@0p4p710R4p8P<p100JAp4p710R>p8P<p100MHp4p710R?p8P<p100OJp4p710R@p8P<p100@Mp4p710p8P<p100ASp4p7210RAp8P<p100B0p4p7210p8P<P7p8p100BOp4p7210R7P8p8P7P1p8P7P2p8P7P9p8P7P:p8P7P;p8P7p100C;p4p7210p8P7P3p8P7P5p8P7P6p8P7p100CXp4p710p8P>P=p8P>P0p8P>P5p8P>p100D_p4p710R0p8P>P4p8P?P=p8P?P5p8P?P0p8P?P4p8P@P=p8p100EAp4p70R=P8p8P=P9p8P=P:p8P=P;p8P=P5p8PAP9p8PAP5p8p100F7p4p710P5p8g00POj21Tg00FVj14Tg00S9j22Tg00SRj50Tg00IJj43Tg00QIR5f1RAf0R9'1g00RC#4f2R=P9O1R;f4R:PAO1R8[f3R@P9O1R4P@PAO1R?[128?R?f5R8P=O1R0P8P@O1R8[R>P:P=O1R7f6R6P@O1[R3P0f7P:O1R0\8R8P9X10P9P@O1O1W1X0>P9D0W0P=PAO1R0O1X2;P>P3P7P6P:O1P9W0PAP@O1O1X18X0>P9D0X0?P0O1X24C3W611A=eW3X55W4o"). Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

(* [comment removed for export] *)
Definition t_nil : TSet := fun tr => tr = [].

(* [comment removed for export] *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

(* [comment removed for export] *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(* [comment removed for export] *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(* [comment removed for export] *)
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

(* [comment removed for export] *)
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

(* [comment removed for export] *)
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Tp;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p9P0p1004mp4p710p8P0p1005Dp4p710p8P0p1005eR8p4p710p8P0P8p4p7210p8P0p1006Bp4p710p8p1006^p4p70R0g00I0R8p4p710R9p8P0p1007hp4p710R:p8P0p1008Dp4p710R;p8P0p1008bp4p7210R<p8P0P5p8p1009?p4p710R0P:p8P0P5p8p1009\p4p70R=P9p8P=P1p8P=P2p8P=p100:Jp4p7210p8P=P:p8P=p100:fp4p710R>p8P=p100;\p4p7210p8P=P0p8P=P;p8P=p100<Kp4p710p8P=P<p8P=p100=Fp4p710R0p8P=p100>@p4p710p8P=P4p8P=P3p4p710R3p8P=P5p8P=p100?<p4p7210p8P=P6p8P=p100@0p4p710R4p8P=p100JAp4p710R?p8P=p100MHp4p710R@p8P=p100OJp4p710RAp8P=p100@Mp4p710p8P=p100ASp4p7210RBp8P=p100B0p4p7210p8P=P7p8p100BOp4p7210R7P9p8P7P1p8P7P2p8P7P:p8P7P;p8P7P<p8P7p100C;p4p7210p8P7P3p8P7P5p8P7P6p8P7p100CXp4p710p8P?P>p8P?P0p8P?P5p8P?p100D_p4p710R0p8P?P4p8P@P>p8P@P5p8P@P0p8P@P4p8PAP>p8p100Sop4p711p100Tmp4p710p8p100EAp4p70R>P9p8P>P:p8P>P;p8P>P<p8P>P5p8PBP:p8PBP5p8p100F7p4p710P5p8P8j20Tg00QIR8f0,08W0o"). Qed.
Lemma t_writes_pick_cons : forall buf bufs T,
  t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T).
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
  t_writes_ch (Z_to_bv 64 1) bufs T.

Lemma t_writes_nil : forall T, t_writes [] T = T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Tp;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p9P0p1004mp4p710p8P0p1005Dp4p710p8P0p1005eR8p4p710p8P0P8p4p7210p8P0p1006Bp4p710p8p1006^p4p70R0g00I0R8p4p710R9p8P0p1007hp4p710R:p8P0p1008Dp4p710R;p8P0p1008bp4p7210R<p8P0P5p8p1009?p4p710R0P:p8P0P5p8p1009\p4p70R=P9p8P=P1p8P=P2p8P=p100:Jp4p7210p8P=P:p8P=p100:fp4p710R>p8P=p100;\p4p7210p8P=P0p8P=P;p8P=p100<Kp4p710p8P=P<p8P=p100=Fp4p710R0p8P=p100>@p4p710p8P=P4p8P=P3p4p710R3p8P=P5p8P=p100?<p4p7210p8P=P6p8P=p100@0p4p710R4p8P=p100JAp4p710R?p8P=p100MHp4p710R@p8P=p100OJp4p710RAp8P=p100@Mp4p710p8P=p100ASp4p7210RBp8P=p100B0p4p7210p8P=P7p8p100BOp4p7210R7P9p8P7P1p8P7P2p8P7P:p8P7P;p8P7P<p8P7p100C;p4p7210p8P7P3p8P7P5p8P7P6p8P7p100CXp4p710p8P?P>p8P?P0p8P?P5p8P?p100D_p4p710R0p8P?P4p8P@P>p8P@P5p8P@P0p8P@P4p8PAP>p8p100Sop4p711p100Tmp4p710p8p100EAp4p70R>P9p8P>P:p8P>P;p8P>P<p8P>P5p8PBP:p8PBP5p8p100F7p4p710P5p8P8j20Tg00QIR8f0,08W0o"). Qed.
Lemma t_writes_cons : forall buf bufs T,
  t_writes (buf :: bufs) T
  = t_emit (map (WriteEv (Z_to_bv 64 1)) buf) (t_writes bufs T).
Proof. reflexivity. Qed.
Lemma t_writes_ch_cons : forall ch buf bufs T,
  t_writes_ch ch (buf :: bufs) T
  = t_emit (map (WriteEv ch) buf) (t_writes_ch ch bufs T).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
  t_writes_ch ch bufs (t_exit code fs) [].
Proof.
  intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
    apply t_emit_has_nil.
Qed.

(* [comment removed for export] *)
Lemma t_writes_ch_exit_iff : forall ch bufs code fs tr,
  t_writes_ch ch bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code fs]).
Proof.
  intros ch bufs; induction bufs as [|buf bufs IH]; intros code fs tr.
  - cbn [wevents_ch app]. unfold t_writes_ch, fold_right, t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)]; [exact H | rewrite app_nil_r; apply is_prefix_refl].
    + intro H. left. exact H.
  - rewrite t_writes_ch_cons. cbn [wevents_ch]. rewrite <- app_assoc.
    unfold t_emit at 1. split.
    + intros [H | (tr' & -> & Hc)].
      * apply is_prefix_app_r; exact H.
      * apply is_prefix_app_mono. apply IH. exact Hc.
    + intro H. apply is_prefix_app_split in H as [H | (tr' & -> & H)].
      * left; exact H.
      * right. exists tr'. split; [reflexivity | apply IH; exact H].
Qed.

Lemma t_writes_exit_iff : forall bufs code fs tr,
  t_writes bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents bufs ++ [ExitEv code fs]).
Proof.
  intros bufs code fs tr. unfold t_writes.
  rewrite t_writes_ch_exit_iff, wevents_ch_fd1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
  T [] -> (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
  intros ch rest T HT Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma t_writes_ch_pick_exit_iff : forall ch bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (fold_right (t_write_ch ch) (t_exit code fs) bufs tr
   <-> exists full, wpick ch bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof.
  intros ch bufs code fs tr Hall; revert tr;
    induction Hall as [|buf bufs Hnb Hall IH]; intros tr.
  - cbn [fold_right]. unfold t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)].
      * exists []. split; [apply wp_nil | exact H].
      * exists []. split; [apply wp_nil|].
        rewrite app_nil_r. cbn [app]. apply is_prefix_refl.
    + intros (full & Hw & Hp). inversion Hw; subst full.
      left. exact Hp.
  - cbn [fold_right]. unfold t_write_ch at 1, t_alt at 1.
    split.
    + intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
      destruct Hi as [H | (tr' & -> & Hc)].
      * exists (map (WriteEv ch) (firstn n buf) ++ wevents_ch ch bufs).
        split; [apply wp_cons; [exact Hn1 | exact Hn2 | apply wpick_wevents; exact Hall]|].
        rewrite <- app_assoc.
        eapply is_prefix_trans; [exact H | apply is_prefix_app_r; apply is_prefix_refl].
      * apply IH in Hc. destruct Hc as (full & Hw & Hp).
        exists (map (WriteEv ch) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption|].
        rewrite <- app_assoc. apply is_prefix_app_mono. exact Hp.
    + intros (full & Hw & Hp).
      inversion Hw as [|buf' bufs' n tr0 Hn1 Hn2 Hw0]; subst.
      rewrite <- app_assoc in Hp.
      apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. left. exact Hp.
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. right.
        exists tr'. split; [reflexivity|].
        apply IH. exists tr0. split; assumption.
Qed.

Lemma t_writes_pick_exit_iff : forall bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (t_writes_pick bufs (t_exit code fs) tr
   <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof. intros. apply t_writes_ch_pick_exit_iff. assumption. Qed.

(* [comment removed for export] *)
Lemma two_traces_t_alt2 : forall bf cf bs cs fs tr,
  t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs)) tr
  <-> MmapSim.two_traces bf cf bs cs fs tr.
Proof.
  intros. unfold t_alt2, MmapSim.two_traces.
  rewrite !t_writes_exit_iff. reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs scfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Definition pnode_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Lemma node_ok_of_pnode : forall c I evs nx,
  pnode_ok c I evs nx ->
  fam_on segs scfg (cfg_ms c) ->
  node_ok c I evs nx.
Proof.
  intros c I evs nx [Hcomp Hsound] Hon. split.
  - intros i. apply sstep_cfg_of_sstep'; [apply Hcomp | exact Hon].
  - intros e st Hss. apply Hsound. eapply sstep_cfg_sub. exact Hss.
Qed.

Lemma node_ok_of_pnode_instr : forall c I evs nx,
  ms_svc_pending (cfg_ms c) = None ->
  pnode_ok c I evs nx ->
  node_ok c I evs nx.
Proof.
  intros c I evs nx Hsvc Hp. apply node_ok_of_pnode; [exact Hp|].
  apply fam_on_instr. exact Hsvc.
Qed.

Lemma node_ok_of_pnode_sysno : forall ms model x8 n I evs nx,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = n ->
  injected_arm n = None ->
  pnode_ok (mkCfg ms model) I evs nx ->
  node_ok (mkCfg ms model) I evs nx.
Proof.
  intros ms model x8 n I evs nx Hsvc Hn Harm Hp.
  apply node_ok_of_pnode; [exact Hp|]. eapply fam_on_sysno; eassumption.
Qed.

(* [comment removed for export] *)
Lemma node_of_iff : forall c (I J : Type) (evs : I -> list event) (nx : I -> config)
    (f : J -> I),
  (forall i, exists j, f j = i) ->
  node_ok c I evs nx ->
  node_ok c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros c I J evs nx f Hsurj [Hc Hs]. split.
  - intros j. apply Hc.
  - intros e st Hss. destruct (Hs e st Hss) as (i & -> & ->).
    destruct (Hsurj i) as (j & <-). exists j. split; reflexivity.
Qed.

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    RomBase.sys_rob segs c ->   (* [comment removed for export] *)
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* [comment removed for export] *)

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_pclosed : forall c T, realizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star_cfg segs scfg c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs scfg c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace_cfg segs scfg c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs scfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma sstep_halted_none : forall c e st,
  sstep_cfg segs scfg c e st -> m_halted (cfg_model c) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) ["WithSegs"] "p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p9P0p1004mp4p710p8P0p1005Dp4p710p8P0p1005eR8p4p710p8P0P8p4p7210p8P0p1006Bp4p710p8p1006^p4p70R0p1007Np4p710R8p8P0p1007hp4p710R9p8P0p1008Dp4p710R:p8P0p1008bp4p7210R;p8P0P5p8p1009?p4p710R0P9p8P0P5p8p1009\p4p70R<P8p8P<P1p8P<P2p8P<p100:Jp4p7210p8P<P9p8P<p100:fp4p710R=p8P<p100;\p4p7210p8P<P0p8P<P:p8P<p100<Kp4p710p8P<P;p8P<p100=Fp4p710R0p8P<p100>@p4p710p8P<P4p8P<P3p4p710R3p8P<P5p8P<p100?<p4p7210p8P<P6p8P<p100@0p4p710R4p8P<p100JAp6051000R>p8P<p100MHp6051000R?p8P<p100OJp6051000R@p8P<p100@Mp4p710p8P<p100ASp4p7210RAp8P<p100B0p4p7210p8P<P7p8p100BOp4p7210R7P8p8P7P1p8P7P2p8P7P9p8P7P:p8P7P;p8P7p100C;p4p7210p8P7P3p8P7P5p8P7P6p8P7p100CXp4p710p8P>P=p8P>P0p8P>P5p8P>p100D_p4p710R0p8P>P4p8P?P=p8P?P5p8P?P0p8P?P4p8P@P=p8p100Sop6051100R=p100Tmp6051000R@p8P=p101Gip6054111001R4p8P=p101Hfp605311001R?p8P=p101^Bp6057111111000R0p8P=p101_Np6054111000R=p8p101Q[p6054111000R>P4p8P>P?p8p101Uip6054111000R7P4p8P7P?p8P7P>p8P0P4p8P0P?p8P0P>p8p101`NR>p6054111001R0P9p8P0P4p8P>p60551111000P4p8P=P@p8P=P4p8p100EAp4p70R4P8p8P4P9p8P4P:p8P4P;p8P4P5p8PAP9p8PAP5p8p100F7p4p710P5p8g01nXj20Tp,4segsp,4scfg'0o"). Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep_cfg segs scfg c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep_cfg segs scfg c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

Lemma rz_path_star : forall c tr c',
  rz_path c -> star_cfg segs scfg c tr c' -> rz_path c'.
Proof.
  intros c tr c' Hp Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH].
  - exact Hp.
  - apply IH. destruct Hp as [T HT].
    destruct (realizes_step c1 T evs c2 HT Hss) as [T' HT']. exists T'. exact HT'.
Qed.

Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs scfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  assert (Hp : rz_path c') by (eapply rz_path_star; [exists T; exact H | exact Hstar]).
  destruct Hp as [T' HT']. exact (realizes_no_sserror c' T' evs HT' Herr).
Qed.

(* [comment removed for export] *)

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(* [comment removed for export] *)
Lemma rz_silent1 : forall c c' T,
  node_ok c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma rz_emit1 : forall c c' e T,
  node_ok c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  node_ok c (IA + IB) (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, realizes (nx (inl i)) A) ->
  (forall i, realizes (nx (inr i)) B) ->
  realizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hrob HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode Hrob).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
Lemma rz_cases1 : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, realizes (nx i) T) ->
  realizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob Hc.
  assert (HT0 : T []) by (eapply realizes_nonempty; apply (Hc i0)).
  apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob). exact Hc.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Ht).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_cfg_svc_cases : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs scfg (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff
           /\ m_halted model' = None
           /\ ((exists model'', e = evs
                   /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
                   /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
               \/ (e = [] /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
                   /\ st = SError)))
          \/ (exists code, m_halted model' = Some code
                 /\ e = evs ++ [halt_ev model' code]
                 /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; injection H as -> end.
  -
    left. eexists _, _, _. split; [eassumption|]. left.
    split; [assumption|]. split; [assumption|]. left. eexists. repeat split; eauto.
  -
    left. eexists _, _, _. split; [eassumption|]. left.
    split; [assumption|]. split; [assumption|]. right. repeat split; auto.
  -
    left. eexists _, _, _. split; [eassumption|]. right.
    eexists. split; [eassumption|]. split; [|reflexivity].
    unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  -
    left. eexists _, _, _. split; [eassumption|]. right.
    match goal with Hk : m_killed ?mm = Some _ |- _ =>
      destruct (m_halted mm) as [code|] eqn:Hhc;
        [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
      exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
    end.
  -
    right. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma node_svc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
       (exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
    \/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy. split.
  - intros i.
    apply (sstep_cfg_syscall segs scfg ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc
             (Hok i) (Hns i) (Hh' i)).
    apply materialize_model_accesses_no_lazy. exact (Hlazy i).
  - intros e st Hss.
    destruct (sstep_cfg_svc_cases ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hspec &
           [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (Hum & -> & ->)].
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [_ Hh3]];
        [rewrite Hh' in Hh2; discriminate | rewrite Hh3 in Hh2; discriminate].
    + exfalso. exact (Hnu Hum).
Qed.

(* [comment removed for export] *)
Lemma node_svc_on : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off scfg (sys_input segs ms x8) = false ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
       exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hon Hok Hinv Hnu Hh' Hlazy.
  apply (node_svc ms model x8 I effs ms' evs Hh Hsvc Hok); try assumption.
  - intros i. apply not_spurious_on. exact Hon.
  - intros eff m' ev Hs. left. exact (Hinv eff m' ev Hs).
Qed.

(* [comment removed for export] *)

Lemma pnode_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  pnode_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep. split.
  - intros []. apply (sstep_instr segs ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_of_pnode_instr; [exact Hsvc | apply pnode_instr; assumption].
Qed.

Lemma rz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_instr; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma pnode_write1 : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  pnode_ok (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb. split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_inv segs ms model x8 buf e st
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma node_write1 : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb.
  assert (Hin : bv_unsigned (in_sysno (sys_input segs ms x8)) = 64%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_cfg_syscall segs scfg ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + apply not_spurious_nonrefusal. rewrite (refusal_b_write _ model _ Hin).
      change (eff_ret (with_copyins [(ms_gpr ms 1, n)]
                         (mkEffect (len_word (firstn n buf)) [] [])))
        with (len_word (firstn n buf)).
      apply write_ret_not_ENOMEM. exact Hbm.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_inv segs ms model x8 buf e st
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb
                (sstep_cfg_sub segs scfg _ _ _ Hss))
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 ms model x8 buf); assumption.
  - eapply RomWrite.write1_rob; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
Lemma node_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  node_ok (mkCfg ms model) unit
          (fun _ => [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)])
          (fun _ => mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  split.
  - intros []. cbn.
    replace [ExitEv code (m_fs model)]
      with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
    apply (sstep_cfg_exit segs scfg ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted code model) [] code);
      [exact Hh | exact Hsvc
       | apply (exit_dispatch_ok (sys_input segs ms x8) model);
         rewrite in_sysno_sys_input; exact Hx8
       | reflexivity
       | apply m_killed_with_halted ].
  - intros e st Hss.
    destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 (sstep_cfg_sub _ _ _ _ _ Hss))
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model)
            (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
  - apply (node_exit ms model x8); assumption.
  - eapply RomBase.sys_rob_memfree; [exact Hsvc|].
    destruct Hx8 as [E | E]; rewrite E; [exact RomBase.memfree_93 | exact RomBase.memfree_94].
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)
Lemma node_munmap : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sc_alloc scfg = false ->
  node_ok (mkCfg ms model) unit (fun _ => [])
          (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc.
  assert (Hin : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  apply (node_svc ms model x8 unit (fun _ => munmap_eff ms)
           (fun _ => munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
           (fun _ => []) Hh Hsvc).
  - intros []. apply munmap_ok; assumption.
  - intros []. apply not_spurious_nonrefusal. rewrite (refusal_b_munmap _ model _ Hin).
    apply munmap_eff_ret_not_ENOMEM.
  - intros eff m' ev Hspec.
    destruct (munmap_ok_inv segs ms x8 model eff m' ev Hno Hargs Hspec)
      as [-> [(e & He & -> & ->) | (-> & ->)]].
    + right. split; [| exact Hh].
      apply (spurious_intro scfg (sys_input segs ms x8) model _ (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      * rewrite (injected_family_off_some scfg _ (mkInjectedArm 215 FamAlloc [ENOMEM]));
          [cbn [ia_family family_may_fail]; rewrite Halloc; reflexivity
          | rewrite Hin; exact injected_arm_215].
      * cbn [eff_ret]. rewrite (refusal_b_munmap _ model _ Hin).
        unfold munmap_errnos in He. destruct He as [<- | []]. apply bv_eqb_refl.
      * apply munmap_ok; assumption.
      * rewrite (refusal_b_munmap _ model _ Hin). apply munmap_eff_ret_not_ENOMEM.
    + left. exists tt. repeat split; reflexivity.
  - apply munmap_no_unmodeled; assumption.
  - intros []. rewrite munmap_model_halted; exact Hh.
  - intros []. exact (munmap_model_no_lazy _ _ _ Hlazy).
Qed.

Lemma rz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, realizes (nx i) T) ->
  realizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob HT.
  assert (HT0 : T []) by (eapply realizes_nonempty; apply (HT i0)).
  apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

Lemma rz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sc_alloc scfg = false ->
  realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Halloc Hc.
  eapply rz_silent1; [apply (node_munmap ms model x8); assumption | exact (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_215)) | exact Hc].
Qed.

(* [comment removed for export] *)
Definition mmap_grant_eff (ms : machine_state) (a : word) : SyscallEffect :=
  mkEffect a [] [(a, page_round_up (ms_gpr ms 1))].

Lemma mmap_grant_not_refusal : forall ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  refusal_b (sys_input segs ms x8) model a = false.
Proof.
  intros ms x8 model a Hno Hg.
  rewrite (refusal_b_mmap (sys_input segs ms x8) model a) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (grant_not_errno (ms_gpr ms 0) model a _
                (page_round_up_Z_nonneg _ (proj1 (bv_unsigned_in_range 64 (ms_gpr ms 1)))) Hg) as Hne.
  unfold errno_ret_in, mmap_errnos in Hne. cbn [existsb] in Hne.
  rewrite orb_false_r in Hne. exact Hne.
Qed.

Lemma node_mmap : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sc_alloc scfg = false ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  node_ok (mkCfg ms model)
          {a : word | grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
          (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (mmap_grant_eff ms (proj1_sig i))))
                          (mmap_model (proj1_sig i) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Halloc [a0 Ha0].
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in *.
  set (n := page_round_up (ms_gpr ms 1)) in *.
  apply (node_svc ms model x8 {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}
           (fun i => mmap_grant_eff ms (proj1_sig i))
           (fun i => mmap_model (proj1_sig i) n model)
           (fun _ => []) Hh Hsvc).
  - intros [a Ha]. cbn [proj1_sig]. unfold mmap_grant_eff. apply mmap_succ_ok; assumption.
  - intros [a Ha]. cbn [proj1_sig]. apply not_spurious_nonrefusal.
    unfold mmap_grant_eff. cbn [eff_ret]. eapply mmap_grant_not_refusal; eassumption.
  - intros eff m' ev Hspec.
    destruct (mmap_ok_inv segs ms x8 model eff m' ev Hno Hargs Hspec)
      as [-> [(e & He & -> & ->) | (a & Ha & -> & ->)]].
    + right. split; [| exact Hh].
      apply (spurious_intro scfg (sys_input segs ms x8) model _ (mmap_grant_eff ms a0)
               (mmap_model a0 n model) []).
      * rewrite (injected_family_off_alloc scfg _ 222%Z); [rewrite Halloc; reflexivity | | auto].
        rewrite in_sysno_sys_input. exact Hno.
      * cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8))
          by (rewrite in_sysno_sys_input; exact Hno).
        unfold mmap_errnos in He. destruct He as [<- | []]. apply bv_eqb_refl.
      * unfold mmap_grant_eff. apply mmap_succ_ok; assumption.
      * cbn [eff_ret]. eapply mmap_grant_not_refusal; eassumption.
    + left. exists (exist _ a Ha). cbn [proj1_sig]. repeat split; reflexivity.
  - apply mmap_no_unmodeled; assumption.
  - intros [a Ha]. cbn [proj1_sig]. rewrite mmap_model_halted. exact Hh.
  - intros [a Ha]. cbn [proj1_sig]. exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
Qed.

Lemma rz_mmap : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sc_alloc scfg = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     realizes (mkCfg (advance_past_svc
                       (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                     (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  realizes (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hdecl Halloc HB Hex.
  destruct Hex as [a0 Ha0].
  apply (rz_cases1 (mkCfg ms model) _ _ B (exist _ a0 Ha0)
           (node_mmap ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Halloc (ex_intro _ a0 Ha0))
           (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))).
  intros [a Ha]. cbn [proj1_sig]. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma node_mmap_nogrant : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  node_ok (mkCfg ms model) unit (fun _ => [])
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Hnone.
  rewrite <- (apply_effect_no_write ms (errno_ret ENOMEM)).
  apply (node_svc ms model x8 unit (fun _ => mkEffect (errno_ret ENOMEM) [] [])
           (fun _ => model) (fun _ => []) Hh Hsvc).
  - intros []. apply mmap_fail_ok; [assumption | assumption | apply ENOMEM_in_mmap_errnos | assumption].
  - intros []. apply not_spurious_forced. intros eff' m' evs' Hspec.
    destruct (mmap_ok_inv segs ms x8 model eff' m' evs' Hno Hargs Hspec)
      as [-> [(e & He & -> & ->) | (a & Ha & -> & ->)]].
    + cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8))
        by (rewrite in_sysno_sys_input; exact Hno).
      unfold mmap_errnos in He. destruct He as [<- | []]. apply bv_eqb_refl.
    + rewrite Hnone in Ha. discriminate Ha.
  - intros eff m' ev Hspec. left.
    destruct (mmap_ok_inv segs ms x8 model eff m' ev Hno Hargs Hspec)
      as [-> [(e & He & -> & ->) | (a & Ha & -> & ->)]].
    + exists tt. unfold mmap_errnos in He. destruct He as [<- | []]. repeat split; reflexivity.
    + rewrite Hnone in Ha. discriminate Ha.
  - apply mmap_no_unmodeled; assumption.
  - intros []. exact Hh.
  - intros []. exact Hlazy.
Qed.

Lemma rz_mmap_nogrant : forall ms model x8 A,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  realizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model) A ->
  realizes (mkCfg ms model) A.
Proof.
  intros ms model x8 A Hh Hlazy Hsvc Hno Hargs Hdecl Hnone HA.
  eapply rz_silent1; [apply (node_mmap_nogrant ms model x8); assumption | exact (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222)) | exact HA].
Qed.

End WithSegs.

(* [comment removed for export] *)

Section Bridges.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cat_realizes : forall segs ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
to_wexit segs ms bufs code ->
bufs_modeled bufs ->
realizes segs scfg (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))).
Proof.
intros segs ms model bufs code Hh Hlazy Hfd Hte. revert model Hh Hlazy Hfd.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfd Hbm.
- rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
- apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
intros n Hn1 Hn2. apply IH; assumption.
- eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma exitline_realizes_aux : forall segs ms bufs code model,
to_wexit segs ms bufs code -> bufs = [] ->
m_halted model = None ->
m_vm_lazy model = [] ->
realizes segs scfg (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
intros segs ms bufs code model Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
[| discriminate Hbufs |]; intro Hlazy.
- eapply rz_exit; eassumption.
- eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.

Lemma exitline_realizes : forall segs ms code model,
  to_wexit segs ms [] code ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs scfg (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros segs ms code model Hte Hh Hlazy.
  exact (exitline_realizes_aux segs ms [] code model Hte eq_refl Hh Hlazy).
Qed.

Lemma rz_wall1_mut : forall segs model,
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  (forall ms rest k, to_wall segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs scfg (mkCfg ms' model) T) ->
     realizes segs scfg (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
  /\ (forall ms rest k, to_wall_tail segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs scfg (mkCfg ms' model) T) ->
     realizes segs scfg (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T)).
Proof.
  intros segs model Hh Hlazy Hfd.
  apply (to_wall_mutind segs (Z_to_bv 64 1)
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs scfg (mkCfg ms' model) T) ->
       realizes segs scfg (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs scfg (mkCfg ms' model) T) ->
       realizes segs scfg (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))).
  -
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm T HT Hk.
    eapply rz_conseq.
    { apply (rz_node segs scfg (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest)) T)
        (wr_full rest Hnb)).
      - apply (node_write1 segs scfg ms model x8 rest); assumption.
      - eapply RomWrite.write1_rob; eassumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
    apply t_alt_wall; [exact HT | exact Hnb].
  -
    intros ms k Hk Hbm T HT Hcont.
    eapply rz_conseq; [apply Hcont; exact Hk|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
  -
    intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
  -
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | exact (IH Hbm T HT Hk)].
Qed.

(* [comment removed for export] *)
Lemma wall_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
  bufs_modeled bufs ->
  realizes segs scfg (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hw Hbm. revert ms Hw Hbm.
  induction bufs as [|buf rest IH]; intros ms Hw Hbm.
  - exact (exitline_realizes segs ms code model Hw Hh Hlazy).
  - destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons.
    eapply (proj2 (rz_wall1_mut segs model Hh Hlazy Hfd)).
    + exact Ht.
    + exact Hb.
    + unfold t_writes. apply t_writes_ch_exit_has_nil.
    + intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.

(* [comment removed for export] *)
Lemma twm_realizes_mut : forall segs,
  sc_alloc scfg = false ->
  (forall ms model bufs code, MmapSim.twm segs ms model bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
     realizes segs scfg (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
  /\ (forall ms model rest bufs code, MmapSim.twm_pend segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs scfg (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model)))))
  /\ (forall ms model rest bufs code, MmapSim.twm_tail segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs scfg (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model))))).
Proof.
  intros segs Halloc.
  apply (MmapSim.twm_mutind segs
    (fun ms model bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
       realizes segs scfg (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs scfg (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs scfg (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))).
  -
    intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
  -
    intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
  -
    intros ms model x8 bufs code Hsvc Hno Hargs Hfail IHfail Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_munmap; try eassumption.
    rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
    apply IH; [rewrite munmap_model_halted; exact Hh
              | exact (munmap_model_no_lazy _ _ _ Hlazy)
              | apply munmap_model_fd1chan; exact Hfd | exact Hbm].
  -
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_step; try eassumption. apply IH; assumption.
  -
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq.
    { apply (rz_node segs scfg (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest))
                         (t_writes bufs (t_exit code (m_fs model))))
        (wr_full rest Hnb)).
      - apply (node_write1 segs scfg ms model x8 rest); assumption.
      - eapply RomWrite.write1_rob; eassumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
    apply t_alt_wall;
      [unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
  -
    intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq; [apply IH; assumption|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
    unfold t_writes. apply t_writes_ch_exit_has_nil.
  -
    intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
    exact (IH Hh Hlazy Hfd Hbr Hbm).
  -
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_step; try eassumption. exact (IH Hh Hlazy Hfd Hbr Hbm).
Qed.

Lemma twm_realizes : forall segs ms model bufs code,
  sc_alloc scfg = false ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  MmapSim.twm segs ms model bufs code ->
  bufs_modeled bufs ->
  realizes segs scfg (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Halloc Hh Hlazy Hfd Hte.
  exact (proj1 (twm_realizes_mut segs Halloc) ms model bufs code Hte Hh Hlazy Hfd).
Qed.

(* [comment removed for export] *)

Definition t_outcomes (fs : Fs.Fs)
    (U : (list (list byte) * word) -> Prop) : TSet :=
  fun tr => exists o, U o /\ is_prefix tr (AllocSim.outcome_trace fs o).

Lemma t_alt_emit_nil : forall (I : Type) (f : I -> TSet),
  (forall i, f i []) -> t_eq (t_alt (fun i => t_emit [] (f i))) (t_alt f).
Proof.
  intros I f H tr. split.
  - intros [i Hi]. exists i. exact (proj1 (t_emit_nil_eq (f i) (H i) tr) Hi).
  - intros [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (f i) (H i) tr) Hi).
Qed.

Lemma t_outcomes_two_alt2 : forall fs bf cf bs cs,
  t_eq (t_outcomes fs (AllocSim2.two_outcomes bf cf bs cs))
       (t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs))).
Proof.
  intros fs bf cf bs cs tr.
  unfold t_outcomes, AllocSim2.two_outcomes, AllocSim.outcome_trace, t_alt2.
  rewrite !t_writes_exit_iff. split.
  - intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
  - intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)]; cbn [fst snd]; auto.
Qed.

(* [comment removed for export] *)

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.

Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
  t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof. reflexivity. Qed.

Lemma node_write_ch : forall segs ms model fd ch x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok segs scfg (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb.
  assert (Hin : bv_unsigned (in_sysno (sys_input segs ms x8)) = 64%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_cfg_syscall segs scfg ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv ch) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + eapply write_ch_ok_n; eassumption.
    + apply not_spurious_nonrefusal. rewrite (refusal_b_write _ model _ Hin).
      change (eff_ret (with_copyins [(ms_gpr ms 1, n)]
                         (mkEffect (len_word (firstn n buf)) [] [])))
        with (len_word (firstn n buf)).
      apply write_ret_not_ENOMEM. exact Hbm.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb
                (sstep_cfg_sub segs scfg _ _ _ Hss))
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write_ch : forall segs ms model fd ch x8 buf T,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model -> fd32 fd = fd ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
buf_modeled buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
realizes segs scfg
(mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
realizes segs scfg (mkCfg ms model) (t_write_ch ch buf T).
Proof.
intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
unfold t_write_ch.
apply (rz_node segs scfg (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- eapply node_write_ch; eassumption.
- eapply RomWrite.write_ch_rob; eassumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma cat_realizes_ch : forall segs fd ch ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model -> fd32 fd = fd ->
to_wexit_ch segs fd ms bufs code ->
bufs_modeled bufs ->
realizes segs scfg (mkCfg ms model) (t_writes_ch_pick ch bufs (t_exit code (m_fs model))).
Proof.
intros segs fd ch ms model bufs code Hh Hlazy Hfdc H32 Hte.
revert model Hh Hlazy Hfdc.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfdc Hbm.
- eapply rz_exit; eassumption.
- apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
intros n Hn1 Hn2. apply IH; assumption.
- eapply rz_step; try eassumption. apply IH; assumption.
Qed.

End Bridges.

End ShapeAlg.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.
Module SymExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.Footprint.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_SymExec () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib7Classes;EquivalenceEpointwise_equivalenceC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_app_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_nil_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8pnode_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00368ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_of_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7rz_alt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg9rz_cases1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8node_svcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_svc_onC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00368ShapeAlg>t_alt_emit_nilC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01C46Stdlib6ZArith4ZdivBZminus_mod_idemp_rC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lc59OSSVerify5KrLib7Mh_00367SymExec@Z_to_bv64_wrap_lC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec:v_addi_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec@Z_to_bv64_wrap_rC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4landC49OSSVerify5KrLib8PropExec8jalr_tgtC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2ex01C46Stdlib6ZArith:Znumtheory<Zmod_div_modC49OSSVerify5KrLib8PropExec=bv_wrap32_modC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib7Mh_00367SymExec=bv_wrap_32_64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC4ELinuxProcessSemantics5Riscv3Sem5low32K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv7Prelude4sextc59OSSVerify5KrLib7Mh_00367SymExec9low32_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExecBZ_to_bv64_wrap_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib7Mh_00367SymExecDZ_to_bv64_wrap_sub_rC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib7Mh_00367SymExec9v_add_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib7Mh_00367SymExecDZ_to_bv64_wrap_sub_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec9v_sub_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec5mkAluC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec6edenotC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec4expr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec=alu64_add_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symk59OSSVerify5KrLib7Mh_00367SymExec4expr02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec4expr03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExecAalu64_add_add_litC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec4expr04C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec4expr05C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec4expr06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec=alu64_sub_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExecAalu64_add_sub_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec3envC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00i59OSSVerify5KrLib7Mh_00367SymExec4expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5mulop00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c59OSSVerify5KrLib7Mh_00367SymExec4ridxC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8u5_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib7Mh_00367SymExec6sr_updC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib7Mh_00367SymExec9sbase_eqbC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec5sbase02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib5Arith8PeanoNat3Nat6eqb_eqK47Corelib4Init5Logic4True01i59OSSVerify5KrLib7Mh_00367SymExec5sbase00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec5sbase01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_00367SymExec5a_offC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec5saddr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec6a_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec:v_add_commC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec6adenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_00367SymExec8to_saddrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec6bdenotC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00367SymExec5saddr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec=u_Z_to_bv64_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec6sentry01C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00367SymExec6sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec7regs_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics5Riscv3Sem7reg_getc59OSSVerify5KrLib7Mh_00367SymExec8ridx_injC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8eqb_reflc59OSSVerify5KrLib7Mh_00367SymExec6sr_getC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec:nth_sr_updC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega5Tauto4kind02C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib7Mh_00367SymExec2E0C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib7Mh_00367SymExec>ridx_roundtripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec:ridx_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib7Mh_00367SymExec5sr_idC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib7Mh_00367SymExec5EplusC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3subc59OSSVerify5KrLib7Mh_00367SymExec7sc_flatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_00079Footprint5rg_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079Footprint5rg_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079Footprint5rg_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00K47Corelib4Init5Logic3and01C56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib7Mh_00079Footprint6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079Footprint7rg_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079Footprint6coversC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079Footprint=covers_nowrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079Footprint;covers_disjC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec8sidecond03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec8sc_denotC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions=bv_swrap_wrapC45stdpp9bitvector;definitions>bv_sign_extendC45stdpp9bitvector;definitionsGbv_sign_extend_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec8b_lw_valC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9le_word_vC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions?bv_add_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu32c59OSSVerify5KrLib7Mh_00367SymExec;alu32_add_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec8mkSext32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_0_lC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib7Mh_00367SymExec<mod_pow2_lowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec@shiftr8_mod_pow2C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_00367SymExecAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib7Mh_00367SymExec>low32_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec9scs_denotC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00367SymExec8sidecond00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec8log_flatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec6flat_uC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib7Mh_00367SymExec9sm_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec<sbase_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec@rdn_wbytes_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCrdn_wbytes_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec>scs_denot_consC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismc59OSSVerify5KrLib7Mh_00367SymExec5st_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec4s_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec5s_logC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01c59OSSVerify5KrLib7Mh_00367SymExec6s_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec6s_nextC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec9sym_state01C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec4ssetC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_luiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec;regs_ok_updC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C49OSSVerify5KrLib8PropExec:step_auipcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec;v_auipc_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec8btgt_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec9step_jalrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9jalr_tgtZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec<jalr_tgt_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05c59OSSVerify5KrLib7Mh_00367SymExec;msize_bytesC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec8sidecond02C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>eq_equivalencec59OSSVerify5KrLib7Mh_00367SymExec>to_saddr_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec?sm_lookup_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec8sidecond05C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec?bytes_le_to_Z_1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_lbuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC49OSSVerify5KrLib8PropExec8step_lhuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec7step_lwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec>mkSext32_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_lwuC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec8sidecond04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec?mem_denot_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec7step_sbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec;step_sw_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec;step_sd_valC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C49OSSVerify5KrLib8PropExec>step_opimm_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec:sext64_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec;mkAlu_denotC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C49OSSVerify5KrLib8PropExecAstep_shiftimm_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec:zext64_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec;step_op_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C49OSSVerify5KrLib8PropExec@step_opimm32_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec<sext32_low32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0<C49OSSVerify5KrLib8PropExecCstep_shiftimm32_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec<zext32_low32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C49OSSVerify5KrLib8PropExec=step_op32_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?K4ELinuxProcessSemantics5Riscv5Instr5instr0BC4ELinuxProcessSemantics5Riscv3Sem7mul_divC49OSSVerify5KrLib8PropExec<step_mul_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0CC49OSSVerify5KrLib8PropExec>step_mul32_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics5Riscv5Instr5instr0GK4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JK4ELinuxProcessSemantics5Riscv5Instr5instr0KK4ELinuxProcessSemantics5Riscv5Instr5instr0LK4ELinuxProcessSemantics5Riscv5Instr5instr0MK4ELinuxProcessSemantics5Riscv5Instr5instr0NK4ELinuxProcessSemantics5Riscv5Instr5instr0OK4ELinuxProcessSemantics5Riscv5Instr5instr0PK4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr0Sc59OSSVerify5KrLib7Mh_00367SymExec8sym_stepC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00i59OSSVerify5KrLib7Mh_00367SymExec9sym_state00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr6awidth00I4ELinuxProcessSemantics5Riscv5Instr5amoop00I4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv5Instr4ffmt00I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00C47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List9app_assocC47Corelib4Init9Datatypes4negbc59OSSVerify5KrLib7Mh_00367SymExec8sym_execC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec5sjumpC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SymExec8sidecond01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List9in_or_appC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationI46Stdlib5Lists4List6Exists00C47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms<PER_morphismI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec<sym_exec_accC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec=scs_denot_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SymExec>sym_step_soundC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC4ELinuxProcessSemantics5Riscv3Sem<branch_takenC49OSSVerify5KrLib8PropExecBstep_branch_tk_genC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecBstep_branch_ft_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC47Corelib7Program6Basics4implc59OSSVerify5KrLib7Mh_00367SymExec>sym_exec_soundC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive expr : Type :=
| ELit  (z : Z)
| EVar  (n : nat)
| EAlu  (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)   (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr).  (* [comment removed for export] *)

Definition env := nat -> word.

Fixpoint edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv64_wrap_l : forall a b, Z_to_bv 64 (bv_wrap 64 a + b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_l.
Qed.

Lemma Z_to_bv64_wrap_r : forall a b, Z_to_bv 64 (a + bv_wrap 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_r.
Qed.

Lemma Z_to_bv64_wrap_sub : forall a b,
  Z_to_bv 64 (bv_wrap 64 a - bv_wrap 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addi_lit : forall p i, v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros p i. unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_l. Qed.

Lemma btgt_lit : forall p i, btgt (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros. apply v_addi_lit. Qed.

Lemma v_auipc_lit : forall p i, v_auipc (Z_to_bv 64 p) i = Z_to_bv 64 (i + p).
Proof.
  intros p i. unfold v_auipc. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.

Lemma jalr_tgt_lit : forall z i,
  jalr_tgt (Z_to_bv 64 z) i = Z_to_bv 64 (Z.land (bv_wrap 64 z + i) (-2)).
Proof. intros z i. unfold jalr_tgt, jalr_tgtZ. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof. reflexivity. Qed.

Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof. reflexivity. Qed.

Lemma bv_wrap_32_64 : forall z, bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z.
Proof.
  intro z. rewrite bv_wrap32_mod, !bv_wrap64_mod, bv_wrap32_mod.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia |].
  exists (2^32)%Z. reflexivity.
Qed.

Lemma low32_lit : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof.
  intro z. unfold low32. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
  apply bv_wrap_32_64.
Qed.

Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.

Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkAlu (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x + y)
          | EAlu ALU_ADD a' (ELit x) => EAlu ALU_ADD a' (ELit (x + y))
          | _ => EAlu ALU_ADD a b
          end
      | _ => EAlu ALU_ADD a b
      end
  | ALU_SUB =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x - y)
          | EAlu ALU_ADD a' (ELit x) => EAlu ALU_ADD a' (ELit (x - y))
          | _ => EAlu ALU_SUB a b
          end
      | _ => EAlu ALU_SUB a b
      end
  | _ => EAlu op a b
  end.

Lemma alu64_add_lit : forall x y,
  alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. rewrite alu_add. unfold v_add. rewrite !Z_to_bv_unsigned.
  rewrite Z_to_bv64_wrap_l, Z_to_bv64_wrap_r. reflexivity.
Qed.

Lemma alu64_sub_lit : forall x y,
  alu64 ALU_SUB (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
  intros x y. rewrite alu_sub. unfold v_sub. rewrite !Z_to_bv_unsigned.
  apply Z_to_bv64_wrap_sub.
Qed.

(* [comment removed for export] *)
Lemma Z_to_bv64_wrap_sub_l : forall a b,
  Z_to_bv 64 (bv_wrap 64 a - b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_l.
Qed.

Lemma Z_to_bv64_wrap_sub_r : forall a b,
  Z_to_bv 64 (a - bv_wrap 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

(* [comment removed for export] *)
Lemma v_add_lit : forall (u : word) x,
  v_add u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u + x).
Proof.
  intros u x. unfold v_add. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.

Lemma v_add_comm : forall x y : word, v_add x y = v_add y x.
Proof. intros x y. unfold v_add. f_equal. lia. Qed.

Lemma v_sub_lit : forall (u : word) x,
  v_sub u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u - x).
Proof.
  intros u x. unfold v_sub. rewrite Z_to_bv_unsigned.
  apply Z_to_bv64_wrap_sub_r.
Qed.

Lemma alu64_add_add_lit : forall (u : word) x y,
  alu64 ALU_ADD (alu64 ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
  = alu64 ALU_ADD u (Z_to_bv 64 (x + y)).
Proof.
  intros u x y. rewrite !alu_add, !v_add_lit, Z_to_bv_unsigned,
    Z_to_bv64_wrap_l. f_equal. lia.
Qed.

Lemma alu64_add_sub_lit : forall (u : word) x y,
  alu64 ALU_SUB (alu64 ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
  = alu64 ALU_ADD u (Z_to_bv 64 (x - y)).
Proof.
  intros u x y. rewrite alu_sub, !alu_add, !v_add_lit, !v_sub_lit,
    !Z_to_bv_unsigned, !Z_to_bv64_wrap_sub_l. f_equal. lia.
Qed.

Lemma mkAlu_denot : forall E op a b,
  edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b).
Proof.
  intros E op a b. destruct op; try reflexivity;
    (destruct b as [y| | | | | ]; [|reflexivity..]);
    (destruct a as [x| |op' a1 a2| | | ]; [| |  |reflexivity..]);
    try reflexivity;
    try (cbn [edenot]; auto using alu64_add_lit, alu64_sub_lit; fail);
    destruct op'; try reflexivity;
    (destruct a2 as [z| | | | | ]; [|reflexivity..]);
    cbn [edenot]; auto using alu64_add_add_lit, alu64_add_sub_lit.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof.
  intros r r' H. apply bv_eq. unfold ridx in H.
  pose proof (u5_range r). pose proof (u5_range r').
  lia.
Qed.

(* [comment removed for export] *)
Definition sr_get (sr : list expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0).

(* [comment removed for export] *)
Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

Lemma nth_sr_upd : forall n sr e i,
  nth i (sr_upd sr n e) (ELit 0) =
    if Nat.eqb i n then e else nth i sr (ELit 0).
Proof.
  induction n as [|n IH]; intros sr e i.
  - destruct sr; destruct i; cbn; try reflexivity;
      destruct i; reflexivity.
  - destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
    + rewrite IH. destruct (Nat.eqb i n); [reflexivity|].
      destruct i; reflexivity.
    + apply IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sbase : Type :=
| SBLit
| SBVar (n : nat).

Definition sbase_eqb (b1 b2 : sbase) : bool :=
  match b1, b2 with
  | SBLit, SBLit => true
  | SBVar n, SBVar m => Nat.eqb n m
  | _, _ => false
  end.

Lemma sbase_eqb_eq : forall b1 b2, sbase_eqb b1 b2 = true -> b1 = b2.
Proof.
  intros [|n] [|m] H; try discriminate; [reflexivity|].
  cbn in H. apply Nat.eqb_eq in H. subst. reflexivity.
Qed.

Record saddr : Type := SA { a_base : sbase; a_off : Z }.

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

Definition bdenot (E : env) (b : sbase) : word :=
  match b with SBLit => Z_to_bv 64 0 | SBVar n => E n end.

(* [comment removed for export] *)
Definition adenot (E : env) (a : saddr) : word :=
  v_addi (bdenot E (a_base a)) (a_off a).

(* [comment removed for export] *)
Definition to_saddr (e : expr) (i : Z) : option saddr :=
  match e with
  | ELit z => Some (SA SBLit (z + i))
  | EVar n => Some (SA (SBVar n) i)
  | EAlu ALU_ADD (EVar n) (ELit z) => Some (SA (SBVar n) (z + i))
  | EAlu ALU_ADD (ELit z) (EVar n) => Some (SA (SBVar n) (z + i))
  | _ => None
  end.

Lemma u_Z_to_bv64_0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma to_saddr_denot : forall E e i a,
  to_saddr e i = Some a -> adenot E a = v_addi (edenot E e) i.
Proof.
  intros E e i a H. unfold adenot.
  destruct e as [z|n|op e1 e2| | | ]; cbn in H;
    try discriminate.
  - injection H as <-. cbn [a_base a_off bdenot edenot].
    unfold v_addi. rewrite u_Z_to_bv64_0, Z_to_bv_unsigned,
      Z_to_bv64_wrap_l. f_equal; lia.
  - injection H as <-. reflexivity.
  - destruct op; cbn in H; try discriminate.
    destruct e1; destruct e2; cbn in H; try discriminate;
      injection H as <-; cbn [a_base a_off bdenot edenot]; rewrite alu_add.
    + (* [ELit z + EVar n]: commute the literal to the right first *)
      rewrite v_add_comm, v_add_lit. unfold v_addi.
      rewrite Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal; lia.
    + (* [EVar n + ELit z] *)
      rewrite v_add_lit. unfold v_addi.
      rewrite Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sym_state : Type := SS {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;
  s_next : nat
}.

(* [comment removed for export] *)
Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_next ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (s_log ss) (s_next ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_ok (E : env) (sr : list expr) (regs : bvmap 5 word) : Prop :=
  forall r : reg, getr regs r = edenot E (sr_get sr r).

(* [comment removed for export] *)
Fixpoint mem_denot (E : env) (base : word -> option byte)
                   (log : list sentry) : word -> option byte :=
  match log with
  | [] => base
  | SE a w v :: rest =>
      wbytes (mem_denot E base rest) (adenot E a)
             (word_to_le_bytes w (edenot E v))
  end.

(* [comment removed for export] *)
Lemma mem_denot_grows : forall E base log, mem_grows base (mem_denot E base log).
Proof.
  intros E base log. induction log as [|[a w v] rest IH]; cbn [mem_denot].
  - apply mem_grows_refl.
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

(* [comment removed for export] *)
Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
      /\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
      /\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat w <= 2^64)%Z
      /\ log_flat E rest
  end.

(* [comment removed for export] *)
Definition st_ok (E : env) (base rom : word -> option byte)
                 (ss : sym_state) (ms : machine_state) : Prop :=
  exists regs, ms = mkst regs (Z_to_bv 64 (s_pc ss))
                          (mem_denot E base (s_log ss)) rom
            /\ regs_ok E (s_regs ss) regs
            /\ log_flat E (s_log ss).

Lemma regs_ok_upd : forall E sr regs rd v e,
  regs_ok E sr regs ->
  edenot E e = v ->
  regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
            (if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
  intros E sr regs rd v e Hr Hv.
  destruct (bv_eqb rd 0) eqn:Hrd; [exact Hr|].
  assert (Hne : rd <> 0).
  { intro Hc. subst rd. rewrite bv_eqb_refl in Hrd. discriminate. }
  intro r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd.
    destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r.
      rewrite getr_same by exact Hne. exact (eq_sym Hv).
    + assert (Hrr : r <> rd).
      { intro Hc. subst r. rewrite Nat.eqb_refl in Hi. discriminate. }
      rewrite getr_other by exact Hrr.
      specialize (Hr r). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_pin : forall E sr regs (r : reg) e,
  regs_ok E sr regs ->
  getr regs r = edenot E e ->
  regs_ok E (sr_upd sr (ridx r) e) regs.
Proof.
  intros E sr regs r e Hr Hv r'. unfold sr_get.
  destruct (bv_eqb r' 0) eqn:Hr0.
  - assert (r' = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r'. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
    + specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Definition sr_id : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7;
   EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

Definition E0 (regs : bvmap 5 word) : env :=
  fun n => getr regs (Z_to_bv 5 (Z.of_nat n)).

Lemma ridx_range : forall r : reg, (ridx r < 32)%nat.
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.

Lemma ridx_roundtrip : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
  intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
  pose proof (u5_range r). rewrite Z2Nat.id by lia.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma regs_ok_id : forall regs, regs_ok (E0 regs) sr_id regs.
Proof.
  intros regs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - unfold E0. rewrite <- (ridx_roundtrip r) at 1.
    pose proof (ridx_range r) as Hlt.
    set (n := ridx r) in *. clearbody n.
    cbn [edenot].
    do 32 (destruct n as [|n]; [reflexivity|]).
    exfalso. lia.
Qed.

(* [comment removed for export] *)
Definition Eplus (regs : bvmap 5 word) (vals : list word) : env :=
  fun n => if Nat.ltb n 32
           then getr regs (Z_to_bv 5 (Z.of_nat n))
           else nth (n - 32) vals (Z_to_bv 64 0).

Lemma regs_ok_Eplus : forall regs vals, regs_ok (Eplus regs vals) sr_id regs.
Proof.
  intros regs vals r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - unfold Eplus. rewrite <- (ridx_roundtrip r) at 1.
    pose proof (ridx_range r) as Hlt.
    set (n := ridx r) in *. clearbody n.
    cbn [edenot].
    do 32 (destruct n as [|n]; [reflexivity|]).
    exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : nat)
| SCDisjoint (a1 : saddr) (n1 : nat) (a2 : saddr) (n2 : nat)
| SCStoreOk  (a : saddr) (n : nat)
| SCReadBase (a : saddr) (n : nat) (e : expr).

(* [comment removed for export] *)
Definition sc_flat (E : env) (a : saddr) (n : nat) : Prop :=
  (0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
  /\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
  /\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat n <= 2^64)%Z.

Lemma flat_u : forall E a n, sc_flat E a n ->
  bv_unsigned (adenot E a) = (bv_unsigned (bdenot E (a_base a)) + a_off a)%Z.
Proof.
  intros E a n (H1 & H2 & H3). unfold adenot, v_addi.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia.
Qed.

Definition sc_denot (segs : list Segment) (base : word -> option byte)
                    (E : env) (s : sidecond) : Prop :=
  match s with
  | SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
  | SCFlat a n => sc_flat E a n
  | SCDisjoint a1 n1 a2 n2 =>
      (bv_unsigned (adenot E a1) + Z.of_nat n1 <= 2^64)%Z
      /\ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= 2^64)%Z
      /\ ((bv_unsigned (adenot E a1) + Z.of_nat n1 <= bv_unsigned (adenot E a2))%Z
          \/ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= bv_unsigned (adenot E a1))%Z)
  | SCStoreOk a n => RiscvSemantics.store_ok segs base (adenot E a) n = true
  | SCReadBase a n e =>
      exists bs, rdn segs base (adenot E a) n = Some bs
                 /\ bytes_le_to_Z bs = bv_unsigned (edenot E e)
  end.

Definition scs_denot (segs : list Segment) (base : word -> option byte)
                     (E : env) (l : list sidecond) : Prop :=
  Forall (sc_denot segs base E) l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sc_flat_of_region : forall E a n r,
  rg_wf r -> (1 <= n)%nat ->
  (rg_lo r <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z ->
  (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat n <= rg_hi r)%Z ->
  sc_flat E a n.
Proof.
  intros E a n r (H0 & H1 & H2) Hn Hl Hh. unfold sc_flat.
  assert (1 <= Z.of_nat n)%Z by lia. repeat split; lia.
Qed.

Lemma sc_disjoint_of_regions : forall segs base E a1 n1 a2 n2 r1 r2,
  rg_wf r1 -> rg_wf r2 -> rg_disj r1 r2 ->
  covers r1 (adenot E a1) n1 -> covers r2 (adenot E a2) n2 ->
  sc_denot segs base E (SCDisjoint a1 n1 a2 n2).
Proof.
  intros segs base E a1 n1 a2 n2 r1 r2 Hw1 Hw2 Hd Hc1 Hc2.
  cbn [sc_denot]. repeat split.
  - exact (covers_nowrap r1 _ _ Hw1 Hc1).
  - exact (covers_nowrap r2 _ _ Hw2 Hc2).
  - exact (covers_disj r1 r2 _ _ _ _ Hd Hc1 Hc2).
Qed.

(* [comment removed for export] *)
Lemma sc_disjoint_same_region : forall segs base E a1 n1 a2 n2 r,
  rg_wf r ->
  covers r (adenot E a1) n1 -> covers r (adenot E a2) n2 ->
  (bv_unsigned (adenot E a1) + Z.of_nat n1 <= bv_unsigned (adenot E a2))%Z
  \/ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= bv_unsigned (adenot E a1))%Z ->
  sc_denot segs base E (SCDisjoint a1 n1 a2 n2).
Proof.
  intros segs base E a1 n1 a2 n2 r Hw Hc1 Hc2 Hd.
  cbn [sc_denot]. repeat split;
    [ exact (covers_nowrap r _ _ Hw Hc1)
    | exact (covers_nowrap r _ _ Hw Hc2)
    | exact Hd ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sm_lookup (log : list sentry) (b : sbase) (k : Z) (n : nat)
  : option (option expr * list sidecond) :=
  match log with
  | [] => Some (None, [])
  | SE (SA b' k') w v :: rest =>
      if sbase_eqb b b' then
        (if (Z.eqb k k' && Nat.eqb n 8 && Nat.eqb w 8)%bool
         then Some (Some v, [])
         else if (Z.leb (k + Z.of_nat n) k' || Z.leb (k' + Z.of_nat w) k)%bool
              then sm_lookup rest b k n
              else None)
      else
        match sm_lookup rest b k n with
        | Some (r, scs) =>
            Some (r, SCDisjoint (SA b k) n (SA b' k') w :: scs)
        | None => None
        end
  end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition mkSext32 (e : expr) : expr := EAluw ALU_ADD e (ELit 0).

(* [comment removed for export] *)
Definition sym_step (i : instr) (ss : sym_state) (rds : list expr)
  : option (sym_state * list sidecond * list expr) :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm =>
      Some (sset ss rd (mkAlu op (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | ShiftImm op rd rs sh =>
      Some (sset ss rd (mkAlu op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | Op op rd rs1 rs2 =>
      Some (sset ss rd (mkAlu op (g rs1) (g rs2)) (p + 4), [], rds)
  | OpImm32 rd rs imm =>
      Some (sset ss rd (EAluw ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | ShiftImm32 op rd rs sh =>
      Some (sset ss rd (EAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | Op32 op rd rs1 rs2 =>
      Some (sset ss rd (EAluw op (g rs1) (g rs2)) (p + 4), [], rds)
  | Mul op rd rs1 rs2 =>
      Some (sset ss rd (EMd op (g rs1) (g rs2)) (p + 4), [], rds)
  | Mul32 op rd rs1 rs2 =>
      Some (sset ss rd (EMdw op (g rs1) (g rs2)) (p + 4), [], rds)
  | Lui rd imm =>
      Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12)) (p + 4), [], rds)
  | Auipc rd imm =>
      Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12 + p)) (p + 4), [], rds)
  | Jal rd imm =>
      Some (sset ss rd (ELit (p + 4)) (p + bv_signed imm), [], rds)
  | Jalr rd rs1 imm =>
      (* [comment removed for export] *)
      match g rs1 with
      | ELit z => Some (sset ss rd (ELit (p + 4))
                             (Z.land (bv_wrap 64 z + bv_signed imm) (-2)), [], rds)
      | _ => None
      end
  (* [comment removed for export] *)
  | Load sz sgn rd rs imm =>
      let n := msize_bytes sz in
      match to_saddr (g rs) (bv_signed imm) with
      | None => None
      | Some a =>
          match sm_lookup (s_log ss) (a_base a) (a_off a) n with
          | None => None
          | Some (Some v, scs) =>
              (* [comment removed for export] *)
              match sz, sgn with
              | SZ8, true => Some (sset ss rd v (p + 4), SCFlat a 8 :: scs, rds)
              | _, _ => None
              end
          | Some (None, scs) =>
              let i := s_next ss in
              let rv := match rds with [] => EVar i | e :: _ => e end in
              let rds' := match rds with [] => [] | _ :: t => t end in
              let scs' := SCFlat a n :: SCReadBase a n rv :: scs in
              let mk e := Some (SS (p + 4)
                                   (if bv_eqb rd 0 then s_regs ss
                                    else sr_upd (s_regs ss) (ridx rd) e)
                                   (s_log ss) (S i), scs', rds') in
              match sz, sgn with
              | SZ8, true => mk rv
              | SZ4, false => mk rv
              | SZ2, false => mk rv
              | SZ1, false => mk rv
              | SZ4, true => mk (mkSext32 rv)
              | _, _ => None
              end
          end
      end
  (* [comment removed for export] *)
  | Store sz rs1 rs2 imm =>
      match sz with
      | SZ1 | SZ4 | SZ8 =>
          let n := msize_bytes sz in
          match to_saddr (g rs1) (bv_signed imm) with
          | None => None
          | Some a =>
              Some (SS (p + 4) (s_regs ss)
                       (SE a n (g rs2) :: s_log ss) (s_next ss),
                    [SCFlat a n; SCStoreOk a n], rds)
          end
      | _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma b_lw_val : forall v : word, sext 64 (bv_extract 0 32 v) = v_lw v.
Proof.
  intro v. apply bv_eq. unfold sext, v_lw.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  f_equal. unfold bv_signed.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_swrap_wrap.
Qed.

Lemma step_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma alu32_add_0 : forall x : bv 32, alu32 ALU_ADD x (Z_to_bv 32 0) = x.
Proof.
  intro x. change (alu32 ALU_ADD x (Z_to_bv 32 0)) with (x + Z_to_bv 32 0).
  apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  replace (bv_wrap 32 0) with 0%Z by reflexivity.
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma mkSext32_denot : forall E e, edenot E (mkSext32 e) = v_lw (edenot E e).
Proof.
  intros E e. cbn [edenot mkSext32].
  rewrite low32_lit, alu32_add_0. apply b_lw_val.
Qed.

Lemma bytes_le_to_Z_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof.
  intro b. cbn [bytes_le_to_Z].
  rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shiftr8_mod_pow2 : forall (k z : Z), (0 <= k)%Z ->
  (Z.shiftr (z mod 2 ^ (k + 8)) 8 = (Z.shiftr z 8) mod 2 ^ k)%Z.
Proof.
  intros k z Hk. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia.
  destruct (Z.ltb i k) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma mod_pow2_low : forall (z k m : Z), (0 <= m <= k)%Z ->
  ((z mod 2 ^ k) mod 2 ^ m = z mod 2 ^ m)%Z.
Proof.
  intros z k m Hm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb i m) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_mod : forall (n : nat) (z : Z),
  Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n))%Z = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with (2 ^ 8)%Z.
    apply mod_pow2_low. lia.
  - replace (8 * Z.of_nat (S n))%Z with (8 * Z.of_nat n + 8)%Z by lia.
    rewrite shiftr8_mod_pow2 by lia. apply IH.
Qed.

Lemma low32_le_bytes : forall v : word,
  Z_to_le_bytes 4%nat (bv_unsigned (low32 v)) = word_to_le_bytes 4 v.
Proof.
  intro v. unfold word_to_le_bytes, low32.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  change (bv_wrap 32 (bv_unsigned v)) with (bv_unsigned v mod 2 ^ 32)%Z.
  exact (Z_to_le_bytes_mod 4 (bv_unsigned v)).
Qed.

(* [comment removed for export] *)
Lemma step_sw_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, low32_le_bytes, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Lemma scs_denot_cons : forall base E s l,
  scs_denot segs base E (s :: l) -> sc_denot segs base E s /\ scs_denot segs base E l.
Proof. intros base E s l H. inversion H; auto. Qed.

(* [comment removed for export] *)
Lemma sm_lookup_sound : forall base E log b k n r scs,
  sm_lookup log b k n = Some (r, scs) ->
  scs_denot segs base E scs ->
  log_flat E log ->
  sc_flat E (SA b k) n ->
  match r with
  | None => rdn segs (mem_denot E base log) (adenot E (SA b k)) n
              = rdn segs base (adenot E (SA b k)) n
  | Some v =>
      n = 8%nat /\
      rdn segs (mem_denot E base log) (adenot E (SA b k)) n
        = Some (word_to_le_bytes 8 (edenot E v))
  end.
Proof.
  intros base E log. induction log as [|[[b' k'] w v'] rest IH];
    intros b k n r scs Hl Hsc Hlf Hfl.
  { cbn in Hl. injection Hl as <- <-. reflexivity. }
  cbn [log_flat] in Hlf. destruct Hlf as (Hf1 & Hf2 & Hf3 & Hlf').
  cbn [a_base a_off] in Hf1, Hf2, Hf3.
  pose proof (flat_u E (SA b k) n Hfl) as Hua.
  cbn [a_base a_off] in Hua.
  assert (Hfl2 := Hfl). unfold sc_flat in Hfl2. cbn [a_base a_off] in Hfl2.
  destruct Hfl2 as (Hk1 & Hk2 & Hk3).
  cbn [sm_lookup] in Hl.
  destruct (sbase_eqb b b') eqn:Hb.
  - apply sbase_eqb_eq in Hb. subst b'.
    assert (Hua' : bv_unsigned (adenot E (SA b k')) =
                   (bv_unsigned (bdenot E b) + k')%Z).
    { apply (flat_u E (SA b k') w). unfold sc_flat.
      cbn [a_base a_off]. repeat split; lia. }
    cbn [a_base a_off] in Hua'.
    destruct (Z.eqb k k' && Nat.eqb n 8 && Nat.eqb w 8)%bool eqn:Hhit.
    + injection Hl as <- <-.
      apply andb_prop in Hhit as [Hhit Hw8]. apply andb_prop in Hhit as [Hkk Hn8].
      apply Z.eqb_eq in Hkk. apply Nat.eqb_eq in Hn8. apply Nat.eqb_eq in Hw8.
      subst k' n w. split; [reflexivity|].
      cbn [mem_denot e_addr e_width e_val].
      apply rdn_wbytes_hit8. lia.
    + destruct (Z.leb (k + Z.of_nat n) k' || Z.leb (k' + Z.of_nat w) k)%bool eqn:Hdis;
        [|discriminate].
      assert (Hd : (bv_unsigned (adenot E (SA b k)) + Z.of_nat n
                      <= bv_unsigned (adenot E (SA b k')))%Z
                   \/ (bv_unsigned (adenot E (SA b k')) + Z.of_nat w
                      <= bv_unsigned (adenot E (SA b k)))%Z).
      { apply orb_prop in Hdis as [Hdis|Hdis]; apply Z.leb_le in Hdis;
          [left|right]; lia. }
      specialize (IH b k n r scs Hl Hsc Hlf' Hfl).
      cbn [mem_denot e_addr e_width e_val].
      assert (Hskip : rdn segs (wbytes (mem_denot E base rest)
                                 (adenot E (SA b k'))
                                 (word_to_le_bytes w (edenot E v')))
                          (adenot E (SA b k)) n
                      = rdn segs (mem_denot E base rest) (adenot E (SA b k)) n).
      { destruct Hd as [Hd|Hd].
        - apply rdn_wbytes_below;
            [ lia | rewrite length_N_to_le_bytes; lia ].
        - apply rdn_wbytes_disjoint;
            [ rewrite length_N_to_le_bytes; lia
            | lia ]. }
      destruct r as [v|]; [destruct IH as [Hn8 IH]; split; [exact Hn8|]|];
        rewrite Hskip; exact IH.
  - destruct (sm_lookup rest b k n) as [[r0 scs0]|] eqn:Hrec; [|discriminate].
    injection Hl as <- <-.
    apply scs_denot_cons in Hsc as [Hhd Htl].
    cbn [sc_denot] in Hhd. destruct Hhd as (Hnw1 & Hnw2 & Hd).
    specialize (IH b k n r0 scs0 Hrec Htl Hlf' Hfl).
    cbn [mem_denot e_addr e_width e_val].
    assert (Hskip : rdn segs (wbytes (mem_denot E base rest)
                               (adenot E (SA b' k'))
                               (word_to_le_bytes w (edenot E v')))
                        (adenot E (SA b k)) n
                    = rdn segs (mem_denot E base rest) (adenot E (SA b k)) n).
    { destruct Hd as [Hd|Hd].
      - apply rdn_wbytes_below;
          [ lia | rewrite length_N_to_le_bytes; lia ].
      - apply rdn_wbytes_disjoint;
          [ rewrite length_N_to_le_bytes; lia | lia ]. }
    destruct r0 as [v|]; [destruct IH as [Hn8 IH]; split; [exact Hn8|]|];
      rewrite Hskip; exact IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sym_step_sound : forall E base rom ss ms i ss' scs w rds rds',
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_step i ss rds = Some (ss', scs, rds') ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms'
              /\ st_ok E base rom ss' ms'.
Proof.
  intros E base rom ss ms i ss' scs w rds rds' Hf He Hd Hs Hsc
    (regs & -> & Hregs & Hlf).
  set (mem := mem_denot E base (s_log ss)) in *.
  destruct i; cbn [sym_step] in Hs; try discriminate.
  - (* Lui *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_lui segs regs _ mem rom w rd imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs | reflexivity].
  - (* Auipc *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_auipc segs regs _ mem rom w rd imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. symmetry. apply v_auipc_lit.
  - (* Jal *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_jal_link segs regs _ mem rom w rd imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply btgt_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. symmetry. apply v_addi_lit.
  - (* Jalr *)
    destruct (sr_get (s_regs ss) rs1) as [z| | | | |] eqn:Hg; try discriminate.
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_jalr segs regs _ mem rom w rd rs1 imm Hf He Hd) |].
    eexists; split.
    + f_equal. cbn [s_pc sset]. unfold v_jalr.
      specialize (Hregs rs1) as Hg1. rewrite Hg in Hg1. cbn [edenot] in Hg1.
      rewrite Hg1. exact (jalr_tgt_lit z (bv_signed imm)).
    + cbn [s_regs s_log sset]. split; [| exact Hlf].
      apply regs_ok_upd; [exact Hregs|].
      cbn [edenot]. symmetry. apply v_addi_lit.
  - (* Load *)
    destruct (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm)) as [a|] eqn:Ha;
      [|discriminate].
    assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm))
      by (rewrite (to_saddr_denot E _ _ _ Ha), Hregs; reflexivity).
    destruct a as [ab ak]; cbn [a_base a_off] in *.
    destruct (sm_lookup (s_log ss) ab ak (msize_bytes sz))
      as [[[v|] scs0]|] eqn:Hlk; [| |discriminate].
    + (* hit: only ld *)
      destruct sz; try discriminate; destruct signed; try discriminate.
      injection Hs as <- <- <-.
      apply scs_denot_cons in Hsc as [Hfit Hsc0]. cbn [sc_denot] in Hfit.
      destruct (sm_lookup_sound base E (s_log ss) ab ak 8%nat (Some v) scs0
                  Hlk Hsc0 Hlf Hfit) as [_ Hread].
      rewrite Hadr in Hread.
      eexists; split;
        [ exact (step_ld segs regs _ mem rom w rd rs1 imm _ (edenot E v)
                   Hf He Hd Hread (bytes_le_to_Z_8 _)) |].
      eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
      cbn [s_regs s_log sset]. split; [| exact Hlf].
      apply regs_ok_upd; [exact Hregs | reflexivity].
    + (* miss: read the base memory into a fresh variable *)
      (* unpack the two leading side conditions once *)
      set (rv := match rds with [] => EVar (s_next ss) | e :: _ => e end) in *.
      assert (Hshape :
        scs = SCFlat (SA ab ak) (msize_bytes sz)
                :: SCReadBase (SA ab ak) (msize_bytes sz) rv :: scs0
        /\ ss' = SS (s_pc ss + 4)
                    (if bv_eqb rd 0 then s_regs ss
                     else sr_upd (s_regs ss) (ridx rd)
                            (match sz, signed with
                             | SZ4, true => mkSext32 rv
                             | _, _ => rv
                             end))
                    (s_log ss) (S (s_next ss))).
      { unfold rv; destruct rds; destruct sz; destruct signed; cbn in Hs;
          try discriminate; injection Hs as <- <- <-; split; reflexivity. }
      destruct Hshape as [-> ->].
      apply scs_denot_cons in Hsc as [Hfit Hsc1].
      apply scs_denot_cons in Hsc1 as [Hrb Hsc0].
      cbn [sc_denot] in Hfit, Hrb.
      destruct Hrb as (bs & Hrdn & Hbs).
      pose proof (sm_lookup_sound base E (s_log ss) ab ak (msize_bytes sz)
                    None scs0 Hlk Hsc0 Hlf Hfit) as Hmiss.
      rewrite Hadr in Hmiss, Hrdn.
      assert (Hread : rdn segs mem (v_addi (getr regs rs1) (bv_signed imm))
                        (msize_bytes sz) = Some bs)
        by (unfold mem; rewrite Hmiss; exact Hrdn).
      clear Hmiss Hrdn. rename Hread into Hrdn.
      pose proof (rdn_length segs mem _ _ _ Hrdn) as Hlen.
      (* every supported width, discharged against its step lemma *)
      destruct sz; destruct signed; cbn in Hs; try discriminate; clear Hs.
      * (* lbu *)
        destruct bs as [|b0 [|??]]; cbn in Hlen; try discriminate.
        rewrite bytes_le_to_Z_1 in Hbs.
        eexists; split;
          [ exact (step_lbu segs regs _ mem rom w rd rs1 imm b0 Hf He Hd Hrdn) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs|].
        rewrite Hbs. symmetry. apply Z_to_bv_bv_unsigned.
      * (* lhu *)
        eexists; split;
          [ exact (step_lhu segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs | reflexivity].
      * (* lw *)
        eexists; split;
          [ exact (step_lw segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs|].
        rewrite mkSext32_denot. reflexivity.
      * (* lwu *)
        eexists; split;
          [ exact (step_lwu segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs | reflexivity].
      * (* ld *)
        eexists; split;
          [ exact (step_ld segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs | reflexivity].
  - (* Store *)
    destruct sz; try discriminate;
      destruct (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm)) as [a|] eqn:Ha;
      try discriminate; injection Hs as <- <- <-;
      (assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm))
         by (rewrite (to_saddr_denot E _ _ _ Ha), Hregs; reflexivity));
      apply scs_denot_cons in Hsc as [Hfl Hsc1];
      apply scs_denot_cons in Hsc1 as [Hok _];
      cbn [sc_denot] in Hfl, Hok;
      rewrite Hadr in Hok;
      (assert (Hok' : RiscvSemantics.store_ok segs mem
                        (v_addi (getr regs rs1) (bv_signed imm)) _ = true)
         by (eapply store_ok_mono; [ apply mem_denot_grows | exact Hok ])).
    + (* sb *)
      eexists; split;
        [ exact (step_sb segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok') |].
      eexists; split.
      * f_equal; [ cbn [s_pc]; apply v_addi_lit |].
        cbn [s_log mem_denot e_addr e_width e_val].
        rewrite Hadr, (Hregs rs2). reflexivity.
      * cbn [s_regs s_log]. split; [exact Hregs|].
        cbn [log_flat]. destruct Hfl as (H1 & H2 & H3). repeat split; assumption.
    + (* sw *)
      eexists; split;
        [ exact (step_sw_val segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok') |].
      eexists; split.
      * f_equal; [ cbn [s_pc]; apply v_addi_lit |].
        cbn [s_log mem_denot e_addr e_width e_val].
        rewrite Hadr, (Hregs rs2). reflexivity.
      * cbn [s_regs s_log]. split; [exact Hregs|].
        cbn [log_flat]. destruct Hfl as (H1 & H2 & H3). repeat split; assumption.
    + (* sd *)
      eexists; split;
        [ exact (step_sd_val segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok') |].
      eexists; split.
      * f_equal; [ cbn [s_pc]; apply v_addi_lit |].
        cbn [s_log mem_denot e_addr e_width e_val].
        rewrite Hadr, (Hregs rs2). reflexivity.
      * cbn [s_regs s_log]. split; [exact Hregs|].
        cbn [log_flat]. destruct Hfl as (H1 & H2 & H3). repeat split; assumption.
  - (* OpImm *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_opimm_gen segs regs _ mem rom w op rd rs1 imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    rewrite mkAlu_denot. cbn [edenot]. rewrite <- Hregs, sext64_lit. reflexivity.
  - (* ShiftImm *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_shiftimm_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    rewrite mkAlu_denot. cbn [edenot]. rewrite <- Hregs, zext64_lit. reflexivity.
  - (* Op *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_op_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    rewrite mkAlu_denot. rewrite <- !Hregs. reflexivity.
  - (* OpImm32 *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_opimm32_gen segs regs _ mem rom w rd rs1 imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- Hregs, (sext32_low32 imm). reflexivity.
  - (* ShiftImm32 *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_shiftimm32_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- Hregs, (zext32_low32 shamt). reflexivity.
  - (* Op32 *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_op32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- !Hregs. reflexivity.
  - (* Mul *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_mul_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- !Hregs. reflexivity.
  - (* Mul32 *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_mul32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- !Hregs. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sym_exec (fuel : nat) (dirs : list bool) (rds : list expr)
                  (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond :=
  match fuel with
  | O => (ss, acc)
  | S f =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => (ss, acc)
      | Some w =>
          if is_ecall w then (ss, acc) else
          match decode_any w with
          | None => (ss, acc)
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (ss, acc) else
              match i with
              | Branch c rs1 rs2 imm =>
                  match dirs with
                  | [] => (ss, acc)
                  | t :: dirs' =>
                      sym_exec f dirs' rds
                        (sjump ss (if t then (s_pc ss + bv_signed imm)%Z
                                   else (s_pc ss + 4)%Z))
                        (SCBr t c (sr_get (s_regs ss) rs1)
                                  (sr_get (s_regs ss) rs2) :: acc)
                  end
              | _ =>
                  match sym_step i ss rds with
                  | Some (ss', scs, rds') => sym_exec f dirs rds' ss' (scs ++ acc)
                  | None => (ss, acc)
                  end
              end
          end
      end
  end.

(* [comment removed for export] *)
Lemma sym_exec_acc : forall fuel dirs rds ss acc,
  exists pre, snd (sym_exec fuel dirs rds ss acc) = pre ++ acc.
Proof.
  induction fuel as [|f IH]; intros dirs rds ss acc; [exists []; reflexivity|].
  cbn [sym_exec].
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|exists []; reflexivity].
  destruct (is_ecall w); [exists []; reflexivity|].
  destruct (decode_any w) as [[i sz]|] eqn:Hdec; [|exists []; reflexivity].
  destruct (Z.eqb sz 4); cbn [negb]; [|exists []; reflexivity].
  destruct i;
    try (match goal with
         | |- context [ sym_step ?ii ss rds ] =>
             destruct (sym_step ii ss rds) as [[[ss2 scs2] rds2]|] eqn:Hstep;
               [ destruct (IH dirs rds2 ss2 (scs2 ++ acc)) as [pre Hpre];
                 exists (pre ++ scs2); rewrite <- app_assoc; exact Hpre
               | exists []; reflexivity ]
         end).
  (* Branch *)
  destruct dirs as [|t dirs']; [exists []; reflexivity|].
  destruct (IH dirs' rds (sjump ss (if t then (s_pc ss + bv_signed imm)%Z
                                else (s_pc ss + 4)%Z))
                     (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc))
    as [pre Hpre].
  exists (pre ++ [SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)]).
  rewrite <- app_assoc. exact Hpre.
Qed.

Lemma scs_denot_app : forall base E l1 l2,
  scs_denot segs base E (l1 ++ l2) ->
  scs_denot segs base E l1 /\ scs_denot segs base E l2.
Proof.
  intros base E l1 l2 H. unfold scs_denot in *.
  split; apply Forall_forall; intros x Hx;
    rewrite Forall_forall in H; apply H, in_or_app; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sym_exec_sound : forall fuel dirs rds ss acc ss' scs E base rom ms,
  sym_exec fuel dirs rds ss acc = (ss', scs) ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok E base rom ss' ms'.
Proof.
  induction fuel as [|f IH]; intros dirs rds ss acc ss' scs E base rom ms Hex Hsc Hst.
  { cbn in Hex. injection Hex as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  assert (Hstop : (ss, acc) = (ss', scs) ->
                  exists ms', msteps segs ms ms' /\ st_ok E base rom ss' ms').
  { intro HX. injection HX as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  cbn [sym_exec] in Hex.
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact (Hstop Hex)].
  destruct (is_ecall w) eqn:He; [exact (Hstop Hex)|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hstop Hex)].
  destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in Hex; [|exact (Hstop Hex)].
  apply Z.eqb_eq in Hsz. subst sz.
  destruct i;
    try (match type of Hex with
         | context [ sym_step ?ii ss rds ] =>
             destruct (sym_step ii ss rds) as [[[ss2 scs2] rds2]|] eqn:Hstep;
               [|exact (Hstop Hex)];
             destruct (sym_exec_acc f dirs rds2 ss2 (scs2 ++ acc)) as [pre Hpre];
             rewrite Hex in Hpre; cbn [snd] in Hpre; subst scs;
             assert (Hsc2 : scs_denot segs base E scs2)
               by (apply scs_denot_app in Hsc as [_ Hsc];
                   apply scs_denot_app in Hsc as [Hsc _]; exact Hsc);
             assert (Hsc' : scs_denot segs base E (pre ++ (scs2 ++ acc)))
               by exact Hsc;
             destruct (sym_step_sound E base rom ss ms ii ss2 scs2 w rds rds2
                         Hf He Hd Hstep Hsc2 Hst)
               as (msA & HstepA & HstA);
             destruct (IH dirs rds2 ss2 (scs2 ++ acc) ss' _ E base rom msA
                         Hex Hsc' HstA)
               as (msB & HmsB & HstB);
             exists msB; split; [| exact HstB];
             eapply mst_step;
               [ destruct Hst as (rr & -> & _); reflexivity
               | exact HstepA | exact HmsB ]
         end).
  (* Branch: the executor consumed one caller-supplied direction. *)
  destruct dirs as [|t dirs']; [exact (Hstop Hex)|].
  destruct Hst as (regs & -> & Hregs & Hlf).
  destruct (sym_exec_acc f dirs' rds
              (sjump ss (if t then (s_pc ss + bv_signed imm)%Z else (s_pc ss + 4)%Z))
              (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc))
    as [pre Hpre].
  rewrite Hex in Hpre. cbn [snd] in Hpre. subst scs.
  assert (Hhd : sc_denot segs base E
                  (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2))).
  { apply scs_denot_app in Hsc as [_ Hsc]. inversion Hsc; assumption. }
  cbn [sc_denot] in Hhd.
  rewrite <- !Hregs in Hhd.
  assert (HstA : st_ok E base rom
                   (sjump ss (if t then (s_pc ss + bv_signed imm)%Z else (s_pc ss + 4)%Z))
                   (mkst regs (if t then btgt (Z_to_bv 64 (s_pc ss)) (bv_signed imm)
                               else v_addi (Z_to_bv 64 (s_pc ss)) 4)
                         (mem_denot E base (s_log ss)) rom)).
  { eexists; split; [| split; [exact Hregs | exact Hlf]].
    cbn [s_pc s_log sjump]. destruct t; [rewrite btgt_lit | rewrite v_addi_lit]; reflexivity. }
  destruct (IH dirs' rds _ _ ss' _ E base rom _ Hex Hsc HstA) as (msB & HmsB & HstB).
  exists msB. split; [| exact HstB].
  eapply mst_step; [ reflexivity | | exact HmsB ].
  destruct t.
  - exact (step_branch_tk_gen segs regs _ (mem_denot E base (s_log ss)) rom
             w c rs1 rs2 imm Hf He Hd Hhd).
  - exact (step_branch_ft_gen segs regs _ (mem_denot E base (s_log ss)) rom
             w c rs1 rs2 imm Hf He Hd Hhd).
Qed.

(* [comment removed for export] *)
Lemma sym_exec_msteps : forall fuel dirs rds ss ss' scs E base rom ms,
  sym_exec fuel dirs rds ss [] = (ss', scs) ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok E base rom ss' ms'.
Proof. intros. eapply sym_exec_sound; eauto. Qed.

(* [comment removed for export] *)
Theorem sym_exec_ex : forall fuel dirs rds ss acc ss' scs E base rom ms,
  sym_exec fuel dirs rds ss acc = (ss', scs) ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists R, regs_ok E (s_regs ss') R
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss'))
                                 (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel dirs rds ss acc ss' scs E base rom ms Hex Hsc Hst.
  destruct (sym_exec_sound fuel dirs rds ss acc ss' scs E base rom ms Hex Hsc Hst)
    as (ms' & Hms & (R & Heq & Hregs & _)).
  exists R. split; [exact Hregs|]. rewrite <- Heq. exact Hms.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac sym_val_norm :=
  cbn [edenot sr_get nth ridx bv_eqb s_regs s_pc];
  rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra.

End SymExec.
Module SymTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WallSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.DrainSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.Footprint OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sr_pins (ps : list (reg * expr)) (sr : list expr) : list expr :=
  match ps with
  | [] => sr
  | (r, e) :: rest => sr_pins rest (sr_upd sr (ridx r) e)
  end.

(* [comment removed for export] *)
Definition pins_ok (E : env) (regs : bvmap 5 word) (ps : list (reg * expr))
  : Prop :=
  Forall (fun p => getr regs (fst p) = edenot E (snd p)) ps.

Lemma regs_ok_pins : forall E ps sr regs,
  regs_ok E sr regs -> pins_ok E regs ps -> regs_ok E (sr_pins ps sr) regs.
Proof.
  intros E ps. induction ps as [|[r e] rest IH]; intros sr regs Hr Hp;
    [exact Hr|].
  unfold pins_ok in Hp. inversion Hp as [|p ps' Hh Ht Heq]; subst.
  cbn [fst snd] in Hh. cbn [sr_pins].
  apply IH; [apply regs_ok_pin; [exact Hr | exact Hh] | exact Ht].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alu64_add_0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
  intro x. rewrite alu_add. change (v_add x (Z_to_bv 64 0)) with (v_addi x 0).
  apply v_addi_0.
Qed.

(* [comment removed for export] *)
Lemma aluw_add_0 : forall x : word,
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) = v_lw x.
Proof.
  intro x. rewrite low32_lit.
  change (Z_to_bv 32 0) with (@Z_to_bv 32 0).
  rewrite alu32_add_0. apply b_lw_val.
Qed.

(* [comment removed for export] *)
Lemma aluw_addi_lit : forall (a : word) (k : Z),
  sext 64 (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k))) = v_addiw a k.
Proof.
  intros a k. apply bv_eq. unfold v_addiw.
  rewrite sext32_unsigned, !Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k)))
    with (low32 a + low32 (Z_to_bv 64 k)).
  rewrite bv_add_unsigned, !low32_unsigned, Z_to_bv_unsigned.
  rewrite bv_swrap_wrap', bv_swrap_add_idemp_l.
  rewrite (bv_wrap_bv_wrap 32 64 k) by lia.
  rewrite bv_swrap_add_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bdenot_var : forall E n, bdenot E (SBVar n) = E n.
Proof. reflexivity. Qed.

Lemma bdenot_lit : forall E, bdenot E SBLit = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

Lemma edenot_var : forall E n, edenot E (EVar n) = E n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_addi_Z : forall (x : word) (i : Z),
  v_addi x i = Z_to_bv 64 (bv_unsigned x + i).
Proof. reflexivity. Qed.

Lemma adenot_var : forall E n k,
  adenot E (SA (SBVar n) k) = Z_to_bv 64 (bv_unsigned (E n) + k).
Proof. reflexivity. Qed.

Lemma adenot_lit : forall E k, adenot E (SA SBLit k) = Z_to_bv 64 k.
Proof.
  intros E k. unfold adenot. cbn [a_base a_off bdenot].
  rewrite v_addi_Z, u_Z_to_bv64_0; f_equal; lia.
Qed.

(* [comment removed for export] *)
End WithFP1.
Ltac sym_env_cbn :=
  cbn [Eplus Nat.ltb Nat.leb Nat.sub Nat.add Z.of_nat nth app fst snd
       a_base a_off e_addr e_width e_val].

Ltac sym_env_norm :=
  sym_env_cbn;
  rewrite ?adenot_var, ?adenot_lit, ?bdenot_var, ?bdenot_lit,
          ?edenot_lit, ?edenot_var, ?u_Z_to_bv64_0;
  sym_env_cbn;
  repeat match goal with
  | |- context [getr ?rs (Z_to_bv 5 ?z)] =>
      let u := eval vm_compute in z in
      let l := constr:(@BV 5 u ltac:(vm_compute; exact I)) in
      replace (Z_to_bv 5 z) with l by (apply bv_eq; vm_compute; reflexivity)
  end.

Section WithFP3.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP3.
Ltac sym_z_lit k :=
  lazymatch k with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac sym_z_norm :=
  repeat match goal with
  (* [comment removed for export] *)
  | |- context [Z_to_bv 64 (0 + ?k)] =>
      sym_z_lit k; replace (0 + k)%Z with k by lia
  | |- context [Z_to_bv 64 (?a - ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 - k2)%Z in
      replace (a - k1 + k2)%Z with (a - v)%Z by lia
  | |- context [Z_to_bv 64 (?a + ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 + k2)%Z in
      replace (a + k1 + k2)%Z with (a + v)%Z by lia
  | |- context [Z_to_bv 64 (?a + Zneg ?p)] =>
      replace (a + Zneg p)%Z with (a - Zpos p)%Z by lia
  end.

Ltac sym_addr_norm :=
  imm_norm; rewrite ?v_addi_Z; sym_env_norm; u_norm; sym_z_norm.

Section WithFP6.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP6.
Ltac sym_lit_norm :=
  repeat match goal with
  (* [comment removed for export] *)
  | |- context [wbytes ?m (Z_to_bv 64 ?z) ?bs] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  | |- context [word_to_le_bytes ?n (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  end.

Section WithFP7.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP7.
Ltac sym_norm :=
  cbn [edenot sr_get nth ridx s_regs s_pc s_log s_next branch_taken];
  rewrite ?alu64_add_0, ?aluw_add_0;
  rewrite ?aluw_addi_lit;
  rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra;
  rewrite ?v_add_lit, ?v_sub_lit;
  sym_addr_norm.

Section WithFP8.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP8.
Ltac sym_mem_norm :=
  cbn [mem_denot e_addr e_width e_val];
  sym_norm; sym_lit_norm.

Section WithFP9.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msteps_to_exit : forall segs code ms ms',
  msteps segs ms ms' -> to_exit segs code ms' -> to_exit segs code ms.
Proof.
  intros segs code ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH]; [auto|].
  intro He. eapply te_step; eauto.
Qed.

Lemma msteps_to_wr : forall segs LH bs ms ms',
  msteps segs ms ms' ->
  StreamSim.to_wr segs LH bs ms' -> StreamSim.to_wr segs LH bs ms.
Proof.
  intros segs LH bs ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH];
    [auto|].
  intro Hw. eapply StreamSim.twr_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma msteps_lh_next : forall segs LH ms ms',
  msteps segs ms ms' ->
  StreamSim.lh_next segs LH ms' -> StreamSim.lh_next segs LH ms.
Proof.
  intros segs LH ms ms' H (m & Hm & HL). exists m. split; [|exact HL].
  eapply msteps_trans; eauto.
Qed.

(* [comment removed for export] *)
End WithFP9.
Ltac sym_halted :=
  solve [ reflexivity
        | eassumption
        | (rewrite ?MmapSim.mmap_model_halted, ?MmapSim.munmap_model_halted;
           solve [ reflexivity | eassumption ])
        | (cbn [cfg_model m_halted]; autorewrite with model; solve [ reflexivity | eassumption ]) ].

Ltac sym_no_lazy :=
  cbn [cfg_model];
  repeat first
    [ rewrite MmapSim.mmap_model_lazy
    | apply MmapSim.munmap_model_no_lazy ];
  solve [ reflexivity | eassumption ].

Section WithFP10.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP10.
Ltac chain_mst :=
  first [ eapply CatSim.msteps_to_wexit
        | eapply MmapSim.msteps_twm
        | eapply MmapSim.msteps_twm_tail
        | eapply MmapSim.msteps_tmw
        | eapply StreamSim.msteps_to_rd
        | eapply msteps_to_wr
        | eapply WallSim.msteps_to_wall_tail
        | eapply WallSim.msteps_to_wallexit
        | eapply DrainSim.msteps_to_rd
        | eapply DrainSim.msteps_to_out
        | eapply msteps_to_exit
        | eapply msteps_lh_next
        | (eapply ShapeAlg.rz_msteps; [ sym_halted | sym_no_lazy | | ])
        | eapply msteps_trans ].

Section WithFP11.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma chain_mst_realizes : forall segs scfg ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ShapeAlg.realizes segs scfg (mkCfg ms' model) T ->
  ShapeAlg.realizes segs scfg (mkCfg ms model) T.
Proof.
  intros segs scfg ms ms' model T Hh Hlazy Hms Hr.
  chain_mst; [exact Hms | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma chain_mst_realizes_mmap : forall segs scfg ms ms' model a n T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ShapeAlg.realizes segs scfg (mkCfg ms' (MmapSim.mmap_model a n model)) T ->
  ShapeAlg.realizes segs scfg (mkCfg ms (MmapSim.mmap_model a n model)) T.
Proof.
  intros segs scfg ms ms' model a n T Hh Hlazy Hms Hr.
  chain_mst; [exact Hms | exact Hr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP11.
Ltac sym_close :=
  first [ reflexivity
        | (f_equal; lia)
        | (apply bv_eq; u_norm; lia)
        | bveq ].

Ltac sym_regs H :=
  getr_resolve; regupd_resolve;
  rewrite <- ?getr_nz by reg_neq_tac;
  rewrite ?(H _);
  repeat match goal with
  | |- context [sr_get ?a ?b] =>
      let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
  end;
  sym_norm.

Section WithFP13.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP13.
Ltac sym_reg H R r v tac :=
  assert (getr R r = v) by (sym_regs H; tac).

Section WithFP14.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP14.
Ltac list_len l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | @cons _ _ ?t => let n := list_len t in constr:(S n)
  end.

Section WithFP15.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP15.
Ltac sym_pc_Z :=
  lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] =>
      lazymatch p with
      | Z_to_bv 64 _ => idtac
      | _ => check_closed_term p;
             let u := vm_eval (bv_unsigned p) in
             replace p with (Z_to_bv 64 u) by bveq
      end
  end.

Section WithFP16.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP16.
Ltac sym_pc_lit :=
  try lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] => wlit p
  end.

Section WithFP17.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP17.
Ltac sym_sc_auto :=
  first [ reflexivity | (repeat split; lia) ].

Section WithFP18.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP18.
Ltac sym_pin_auto :=
  first
  [ reflexivity
  | multimatch goal with
    | H : regs_ok _ _ _ |- _ =>
        sym_regs H; first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ]
    end ].

Section WithFP19.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP19.
Ltac sym_block segs fuel dirs rds ps pvals rvals R H :=
  sym_pc_Z;
  lazymatch goal with
  | |- context [ mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom ] =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    let Hms := fresh "Hms" in
    let Heq := fresh "Heq" in
    let Hlf := fresh "Hlf" in
    let msx := fresh "msx" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 (mkst regs (Z_to_bv 64 pc) mem rom));
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_sound segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (msx & Hms & (R & Heq & H & Hlf));
        clear Hsc Hst;
        chain_mst; [ exact Hms | ];
        rewrite Heq; clear Heq Hms msx;
        cbn [s_pc s_log]; try sym_mem_norm;
        norm_pc; sym_pc_lit ] ]
  end.

Section WithFP20.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP20.
Ltac sym_block_ex segs ms fuel dirs rds ps pvals rvals R H Hms :=
  lazymatch ms with
  | mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 ms);
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_ex segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (R & H & Hms);
        clear Hsc Hst;
        cbn [s_pc s_regs s_log mem_denot] in Hms ] ]
  end.

Section WithFP21.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP21.
Ltac sym_chain Hms :=
  sym_pc_Z; chain_mst; [ exact Hms | ]; norm_pc; sym_pc_lit.

End SymTac.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.
Module SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.LazyFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FrmKeepC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Export BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition spin_leaves : Prop := False.

Section WithSegs.
Context {bmK : BMode}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)

Inductive srealizes0 : config -> TSet -> Prop :=
| srz0_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs scfg c I evs nx ->
    RomBase.sys_rob segs c ->   (* [comment removed for export] *)
    (forall i, srealizes0 (nx i) (T i)) ->
    srealizes0 c (t_alt (fun i => t_emit (evs i) (T i)))
| srz0_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes0 c t_nil
| srz0_spin : forall c,
    to_spin segs (cfg_ms c) (cfg_model c) ->
    m_halted (cfg_model c) = None ->
    spin_leaves ->               (* [comment removed for export] *)
    srealizes0 c t_nil
| srz0_conseq : forall c T T',
    srealizes0 c T -> t_eq T T' -> srealizes0 c T'
| srz0_brefused : forall c T,
    bm_on = true -> budget_refused_at segs c ->
    RomBase.sys_rob segs c ->   (* [comment removed for export] *)
    T [] -> srealizes0 c T.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frm_safe : Prop :=
  (forall seg, In seg segs -> seg_executable seg && seg_writable seg = false)
  /\ (forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> FRMC.word_frm_safe w = true).
Definition frm_guard (c : config) : Prop := frm_safe /\ frm_zero (ms_fcsr (cfg_ms c)).
Definition srealizes (c : config) (T : TSet) : Prop := T [] /\ (frm_guard c -> srealizes0 c T).

Lemma fz_set_reg ms r v : ms_fcsr (set_reg ms r v) = ms_fcsr ms.
Proof. unfold set_reg. destruct (bv_eqb r 0); reflexivity. Qed.
(* At LPS 727298f3 [sstep_cfg] has a vDSO-call arm whose successor is [vdso_post]: it writes
   integer registers, the frame and the pc, and leaves the floating-point CSR alone. *)
Lemma fz_vdso_write_regs : forall rs vs ms, ms_fcsr (vdso_write_regs ms rs vs) = ms_fcsr ms.
Proof.
  induction rs as [|r rs IH]; intros [|v vs] ms; cbn [vdso_write_regs]; try reflexivity.
  rewrite IH. apply fz_set_reg.
Qed.
Lemma fz_vdso_post : forall ms model f eff, ms_fcsr (vdso_post segs ms model f eff) = ms_fcsr ms.
Proof.
  intros ms model f eff. unfold vdso_post, vdso_set_pc, vdso_with_mem, apply_effect. cbn [ms_fcsr].
  rewrite fz_set_reg. cbn [ms_fcsr]. apply fz_vdso_write_regs.
Qed.
Lemma sstep_cfg_fz : forall c e c', frm_safe -> sstep_cfg segs scfg c e (SNext c') ->
  frm_zero (ms_fcsr (cfg_ms c)) -> frm_zero (ms_fcsr (cfg_ms c')).
Proof.
  intros c e c' [NWX FS] H. inversion H; subst; cbn [cfg_ms]; intros Z.
  - match goal with A : mi_account_step _ _ _ = MachineOk _ |- _ => apply mi_account_step_projects in A; exact (FRMC.step_fz segs NWX FS _ _ A Z) end.
  - rewrite fz_vdso_post. exact Z.
  - unfold advance_past_svc, apply_effect. cbn [ms_fcsr]. rewrite fz_set_reg. exact Z.
  - exact Z.
  - exact Z.
Qed.

Lemma srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
    node_ok segs scfg c I evs nx -> RomBase.sys_rob segs c -> (forall i, srealizes (nx i) (T i)) -> srealizes c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hnode Hrob Hk. split; [exists i0; left; apply is_prefix_nil|].
  intros [S Z]. apply (srz0_node c I evs nx T i0 Hnode Hrob). intros i. apply (proj2 (Hk i)). split; [exact S|].
  destruct Hnode as [Hc _]. exact (sstep_cfg_fz c (evs i) (nx i) S (Hc i) Z).
Qed.
Lemma srz_halt : forall c, m_halted (cfg_model c) <> None -> srealizes c t_nil.
Proof. intros c H. split; [reflexivity| intros _; exact (srz0_halt c H)]. Qed.
Lemma srz_spin : forall c, to_spin segs (cfg_ms c) (cfg_model c) -> m_halted (cfg_model c) = None -> spin_leaves -> srealizes c t_nil.
Proof. intros c H1 H2 H3. split; [reflexivity| intros _; exact (srz0_spin c H1 H2 H3)]. Qed.
Lemma srz_conseq : forall c T T', srealizes c T -> t_eq T T' -> srealizes c T'.
Proof. intros c T T' [NE H] Heq. split; [apply Heq; exact NE| intros G; exact (srz0_conseq c T T' (H G) Heq)]. Qed.
Lemma srz_brefused : forall c T, bm_on = true -> budget_refused_at segs c -> RomBase.sys_rob segs c -> T [] -> srealizes c T.
Proof. intros c T H1 H2 Hr H3. split; [exact H3| intros _; exact (srz0_brefused c T H1 H2 Hr H3)]. Qed.

Lemma srealizes0_of_realizes : forall c T, realizes segs scfg c T -> srealizes0 c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz0_node c I evs nx T i0 Hnode Hrob IH).
  - exact (srz0_halt c Hh).
  - exact (srz0_conseq c T T' IH Heq).
Qed.
Lemma srz0_spinning : spin_leaves -> forall c, spinning segs c -> srealizes0 c t_nil.
Proof. intros BOFF c [Hspin Hh]. exact (srz0_spin c Hspin Hh BOFF). Qed.
(* [comment removed for export] *)
Lemma srz_fz : forall c T, T [] -> (frm_zero (ms_fcsr (cfg_ms c)) -> srealizes c T) -> srealizes c T.
Proof. intros c T NE H. split; [exact NE|]. intros G. exact (proj2 (H (proj2 G)) G). Qed.
(* [comment removed for export] *)
Lemma srealizes0_of : forall c T, frm_guard c -> srealizes c T -> srealizes0 c T.
Proof. intros c T G [_ H]. exact (H G). Qed.
Lemma srealizes_of0 : forall c T, T [] -> srealizes0 c T -> srealizes c T.
Proof. intros c T NE H. split; [exact NE| intros _; exact H]. Qed.

(* [comment removed for export] *)
Lemma srealizes_of_realizes : forall c T,
  realizes segs scfg c T -> srealizes c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode Hrob IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

(* [comment removed for export] *)
Lemma srz_spinning : spin_leaves -> forall c, spinning segs c -> srealizes c t_nil.
Proof. intros BOFF c [Hspin Hh]. exact (srz_spin c Hspin Hh BOFF). Qed.

(* [comment removed for export] *)

Lemma srealizes0_nonempty : forall c T, srealizes0 c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
  - exact HT0.
Qed.
Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof. intros c T H. exact (proj1 H). Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_silent1 : forall c c' T,
  node_ok segs scfg c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma srz_emit1 : forall c c' e T,
  node_ok segs scfg c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs scfg c (IA + IB) (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hrob HA HB.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) Hnode Hrob).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
Lemma srz_cases1 : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs scfg c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob Hc.
  assert (HT0 : T []) by (eapply srealizes_nonempty; apply (Hc i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob). exact Hc.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Ht).
Qed.

(* [comment removed for export] *)
Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_silent1; [apply node_instr; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma node_instr_disjoint : forall ms model ms' ranges,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' ranges Hh Hsvc Hstep Hout.
  pose proof (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
    as Hacc.
  apply node_ok_of_pnode_instr; [exact Hsvc|].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model); assumption.
  - intros e st Hss.
    inversion Hss; subst; try congruence.
    match goal with
    | H : mi_account_step _ _ _ = MachineOk _ |- _ =>
        rewrite Hacc in H; injection H; intros; subst
    end.
    exists tt. split; reflexivity.
Qed.

Lemma rz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  realizes segs scfg (mkCfg ms' model) T ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply rz_silent1; [eapply node_instr_disjoint; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply srz_silent1; [eapply node_instr_disjoint; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 segs scfg ms model x8 buf); assumption.
  - eapply RomWrite.write1_rob; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
Lemma srz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes_of_realizes. apply (rz_exit segs scfg ms model x8); assumption.
Qed.

(* [comment removed for export] *)
Lemma srz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs scfg c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob HT.
  assert (HT0 : T []) by (eapply srealizes_nonempty; apply (HT i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

Lemma srz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sc_alloc scfg = false ->
  srealizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Halloc Hc.
  eapply srz_silent1; [apply (node_munmap segs scfg ms model x8); assumption | exact (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_215)) | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_mmap : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sc_alloc scfg = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hdecl Halloc HB Hex.
  destruct Hex as [a0 Ha0].
  apply (srz_cases1 (mkCfg ms model) _ _ B (exist _ a0 Ha0)
           (node_mmap segs scfg ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Halloc (ex_intro _ a0 Ha0))
           (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))).
  intros [a Ha]. cbn [proj1_sig]. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_nogrant : forall ms model x8 A,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  srealizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model) A ->
  srealizes (mkCfg ms model) A.
Proof.
  intros ms model x8 A Hh Hlazy Hsvc Hno Hargs Hdecl Hnone HA.
  eapply srz_silent1; [apply (node_mmap_nogrant segs scfg ms model x8); assumption | exact (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222)) | exact HA].
Qed.

End WithSegs.

(* [comment removed for export] *)
Section WithSegsOff.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Local Notation srealizes := (@srealizes0 bm_off_inst segs scfg).

Lemma srealizes_pclosed : forall c T, srealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
  - discriminate Hon.
Qed.

(* [comment removed for export] *)

Lemma srealizes_star_only : forall c T, srealizes c T ->
  forall tr c', star_cfg segs scfg c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs scfg c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_star_nil segs ms model tr c' Hspin Hh (star_cfg_sub _ _ _ _ _ Hstar)).
  - apply Heq. eapply IH; exact Hstar.
  - discriminate Hon.
Qed.

(* [comment removed for export] *)

Lemma srealizes_admits : forall c T, srealizes c T ->
  forall tr, T tr -> obs_trace_cfg segs scfg c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
  - discriminate Hon.
Qed.

(* [comment removed for export] *)
Theorem srealizes_obs_iff : forall c T, srealizes c T ->
  forall tr, obs_trace_cfg segs scfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_pclosed;
      [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply srealizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma srealizes_step : forall c T e c',
  srealizes c T -> sstep_cfg segs scfg c e (SNext c') -> exists T', srealizes c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct (silent_loop_sstep segs (spinning segs) c e (SNext c')
                (spinning_silent_loop segs) (conj Hspin Hh) (sstep_cfg_sub _ _ _ _ _ Hss))
      as (_ & c'' & Heq2 & Hsp').
    injection Heq2 as ->.
    exfalso. exact Hboff.   (* [comment removed for export] *)
  - eapply IH; exact Hss.
  - discriminate Hon.
Qed.

Lemma srealizes_no_sserror : forall c T e,
  srealizes c T -> ~ sstep_cfg segs scfg c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_no_sstep_error segs ms model Hspin Hh e (sstep_cfg_sub _ _ _ _ _ Hss)).
  - eapply IH; exact Hss.
  - discriminate Hon.
Qed.

Definition srz_path (c : config) : Prop := exists T, srealizes c T.

Lemma srz_path_star : forall c tr c',
  srz_path c -> star_cfg segs scfg c tr c' -> srz_path c'.
Proof.
  intros c tr c' Hp Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH].
  - exact Hp.
  - apply IH. destruct Hp as [T HT].
    destruct (srealizes_step c1 T evs c2 HT Hss) as [T' HT']. exists T'. exact HT'.
Qed.

Theorem srealizes_no_error : forall c T,
  srealizes c T -> ~ reaches_error_cfg segs scfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  assert (Hp : srz_path c') by (eapply srz_path_star; [exists T; exact H | exact Hstar]).
  destruct Hp as [T' HT']. exact (srealizes_no_sserror c' T' evs HT' Herr).
Qed.

End WithSegsOff.

(* [comment removed for export] *)
Section BmTransfer.
Context {bmK : BMode}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma srealizes0_bm_transfer : forall c T,
  @srealizes0 bmK segs scfg c T ->
  ~ reaches_budget_refused_cfg segs scfg c ->
  @srealizes0 bm_off_inst segs scfg c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros Hnr.
  - apply (@srz0_node bm_off_inst segs scfg c I evs nx T i0 Hnode Hrob).
    intros i. apply IH. intros (tr & c' & Hstar & Hb). apply Hnr.
    exists (evs i ++ tr), c'. split; [| exact Hb].
    destruct Hnode as [Hcomp _]. eapply star_cfg_step; [apply Hcomp | exact Hstar].
  - exact (@srz0_halt bm_off_inst segs scfg c Hh).
  - exfalso. exact Hboff.   (* [comment removed for export] *)
  - exact (@srz0_conseq bm_off_inst segs scfg c T T' (IH Hnr) Heq).
  - exfalso. apply Hnr. exists [], c. split; [apply star_cfg_refl | exact Hbr].
Qed.

(* [comment removed for export] *)
Lemma srealizes0_of_off : forall c T,
  @srealizes0 bm_off_inst segs scfg c T -> bm_on = false -> @srealizes0 bmK segs scfg c T.
Proof.
  intros c T H BOFF;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0].
  - exact (srz0_node segs scfg c I evs nx T i0 Hnode Hrob IH).
  - exact (srz0_halt segs scfg c Hh).
  - exfalso. exact Hboff.   (* [comment removed for export] *)
  - exact (srz0_conseq segs scfg c T T' IH Heq).
  - discriminate Hon.
Qed.


Lemma srealizes_bm_transfer : forall c T,
  @srealizes bmK segs scfg c T ->
  ~ reaches_budget_refused_cfg segs scfg c ->
  @srealizes bm_off_inst segs scfg c T.
Proof. intros c T [NE H] Hnr. split; [exact NE|]. intros G. exact (srealizes0_bm_transfer c T (H G) Hnr). Qed.
Lemma srealizes_of_off : forall c T,
  @srealizes bm_off_inst segs scfg c T -> bm_on = false -> @srealizes bmK segs scfg c T.
Proof. intros c T [NE H] BOFF. split; [exact NE|]. intros G. exact (srealizes0_of_off c T (H G) BOFF). Qed.

End BmTransfer.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chain_mst_sp :=
  first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
        | chain_mst ].

(* [comment removed for export] *)
Lemma chain_mst_srealizes : forall segs scfg ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes segs scfg (mkCfg ms' model) T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros segs scfg ms ms' model T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.

Lemma chain_mst_srealizes_mmap : forall segs scfg ms ms' model a n T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes segs scfg (mkCfg ms' (MmapSim.mmap_model a n model)) T ->
  srealizes segs scfg (mkCfg ms (MmapSim.mmap_model a n model)) T.
Proof.
  intros segs scfg ms ms' model a n T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.

End SpinAlg.
Module SpinAlgX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section BmKitW. Context {bmK : BMode}.   (* [comment removed for export] *)
Lemma srz_write_ch : forall segs scfg ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes segs scfg
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes segs scfg (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros segs scfg ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node segs scfg (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - eapply node_write_ch; eassumption.
  - eapply RomWrite.write_ch_rob; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
End BmKitW.

End SpinAlgX.
From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
Module AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanAcct () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC59OSSVerify5KrLib7Mh_0037:DivergeSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib7Classes;EquivalenceEpointwise_equivalenceC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_app_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_nil_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8pnode_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00368ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_of_iffC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SpinAlg:srealizes001C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7rz_alt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg9rz_cases1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8node_svcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_svc_onC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00368ShapeAlg>t_alt_emit_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SpinAlg8srz_alt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SpinAlg:srz_cases1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib7Mh_00368AsanAcct4woffC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addK47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib7Mh_00368AsanAcct<range_avoidsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08c59OSSVerify5KrLib7Mh_00368AsanAcct6woff_0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega;ZifyClasses7rew_iffc59OSSVerify5KrLib7Mh_00368AsanAcct9woff_succC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib7Mh_00368AsanAcct<ranges_avoidC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00C46Stdlib5Lists4List9in_app_orI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memc59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc59OSSVerify5KrLib7Mh_00368AsanAcct8restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct:unrestrictC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01c59OSSVerify5KrLib7Mh_00368AsanAcctEmunrestrict_mrestrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrc59OSSVerify5KrLib7Mh_00368AsanAcctEmrestrict_munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib7Mh_00368AsanAcctBhclean_restrict_idC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctCrestrict_unrestrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic3and01c59OSSVerify5KrLib7Mh_00368AsanAcctCmemory_read1_hiddenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_00368AsanAcctArange_avoids_consC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc59OSSVerify5KrLib7Mh_00368AsanAcct>wview_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib7Mh_00368AsanAcct?range_avoids_hdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct?range_avoids_tlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctJov_read_bytes_mrestrict_eqC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctBwview_mrestrict_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC47Corelib4Init5Logic3notC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith4Znat3N2Z9is_nonnegc59OSSVerify5KrLib7Mh_00368AsanAcctFfind_segment_none_specC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsAseg_ov_read_bytesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c59OSSVerify5KrLib7Mh_00368AsanAcctEin_segment_not_hiddenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executablec59OSSVerify5KrLib7Mh_00368AsanAcctFfind_segment_some_specC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Znat7N_nat_Zc59OSSVerify5KrLib7Mh_00368AsanAcctJseg_ov_read_bytes_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<code_read_ovC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le4c59OSSVerify5KrLib7Mh_00368AsanAcctEcode_read_ov_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_half_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_halfc59OSSVerify5KrLib7Mh_00368AsanAcctFfetch_half_ov_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics5Riscv7Prelude4bitsC45stdpp9bitvector;definitions9bv_concatc59OSSVerify5KrLib7Mh_00368AsanAcctGfetch_half_any_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsC47Corelib4Init9Datatypes3orbK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureI47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib7Mh_00368AsanAcct@ranges_avoid_nilC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics5Riscv3Sem3eff02K4ELinuxProcessSemantics5Riscv3Sem3eff03K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05K4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv3Sem3eff07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesc59OSSVerify5KrLib7Mh_00368AsanAcctFov_read_bytes_restrictC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01c59OSSVerify5KrLib7Mh_00368AsanAcctAranges_avoid_consC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem3eff08c59OSSVerify5KrLib7Mh_00368AsanAcctAstore_ok_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBaseDlength_Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc59OSSVerify5KrLib7Mh_00368AsanAcctEwrite_to_mem_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctCwrite_to_mem_hiddenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7eff_indC45stdpp9bitvector;definitions:bv_extractI4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv3Sem3eff00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalK4ELinuxProcessSemantics5Riscv3Sem4core01c59OSSVerify5KrLib7Mh_00368AsanAcct?restrict_hcleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctLinterp_eff_accesses_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4execI4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordc59OSSVerify5KrLib7Mh_00368AsanAcct;restrict_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctFfetch_word_ov_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctGfetch_tail_any_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctFfetch_failure_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctMdecode_exec_accesses_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib7Mh_00368AsanAcctFstep_accesses_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctIrestrict_unrestrict_cleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctCstep_restrict_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC56Stdlib6ZArith6BinInt1Z3mulI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00c59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingI4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct7A_pagesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc59OSSVerify5KrLib7Mh_00368AsanAcct>Zmod0_multipleC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6to_natK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?mul_add_distr_rC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List:length_seqC47Corelib4Init9Datatypes3sndC47Corelib5Lists7ListDef3seqK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib5Lists4List9in_or_appc59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC46Stdlib5Lists4List:in_map_iffI47Corelib4Init5Peano2le00C46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addI46Stdlib5Lists4List5NoDup00K46Stdlib5Lists4List5NoDup01K46Stdlib5Lists4List5NoDup02C46Stdlib5Lists4List9NoDup_indc59OSSVerify5KrLib7Mh_00368AsanAcctENoDup_map_bv_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct:A_pages_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC46Stdlib5Lists4ListANoDup_incl_lengthK46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib7Mh_00368AsanAcct>A_pages_lengthC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC57Corelib7BinNums6PosDef3Pos3mulC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_addC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC46Stdlib;setoid_ring6Ncring>ring_mult_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc59OSSVerify5KrLib7Mh_00368AsanAcct>two64_as_pagesC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib6ZArith4ZdivAZmult_mod_distr_lC4ELinuxProcessSemantics?LinuxProcessSem5State8page_memC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics?LinuxProcessSem5State;page_insertC4ELinuxProcessSemantics?LinuxProcessSem5State@access_pages_accc59OSSVerify5KrLib7Mh_00368AsanAcctApage_insert_nodupC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesc59OSSVerify5KrLib7Mh_00368AsanAcctFaccess_pages_acc_nodupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct>page_insert_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctCaccess_pages_acc_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateHnewly_materialized_pagesC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesc59OSSVerify5KrLib7Mh_00368AsanAcctAaccesses_pages_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctDaccesses_pages_nodupC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<NoDup_filterc59OSSVerify5KrLib7Mh_00368AsanAcctEpage_mem_false_not_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctDpage_base_of_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct>page_base_woffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib7Mh_00368AsanAcctEm_vm_materialized_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct=m_vm_lazy_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct>eager_used_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct<m_vmmaps_wvbC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00368AsanAcct4MInv01C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc59OSSVerify5KrLib7Mh_00368AsanAcct?new_pages_propsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9NoDup_appc59OSSVerify5KrLib7Mh_00368AsanAcctCallowed_pages_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedc59OSSVerify5KrLib7Mh_00368AsanAcct8MInv_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctEvm_backing_used_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctFmaterialize_restrictedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib7Mh_00368AsanAcctJmi_account_step_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctDwith_vm_backing_sameC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01c59OSSVerify5KrLib7Mh_00368AsanAcct?sstep_instr_detC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct;step_hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctEnode_instr_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctJsame_but_materialized_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctCunrestrict_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctDrestrict_svc_pendingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctFunrestrict_munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct>unrestrict_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct=msteps_hcleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctDrz_msteps_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctBwith_vm_backing_idC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00c59OSSVerify5KrLib7Mh_00368AsanAcctAmaterialized_succC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_nonec59OSSVerify5KrLib7Mh_00368AsanAcctGnode_syscall_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct3mkHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctCpage_in_ranges_inclC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc59OSSVerify5KrLib7Mh_00368AsanAcct@wx_segs_nowrap_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct7seg_topC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib7Mh_00368AsanAcct>wx_segs_nowrapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct<segs_below_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctHfind_segment1_none_aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posc59OSSVerify5KrLib7Mh_00368AsanAcct=ranges_from_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct<page_base_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct9mkH_aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcctDH_off_segments_aboveC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Section FPX_1. Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrestrict (H : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if H a then None else m a.

(* [comment removed for export] *)
Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
    : word -> option byte :=
  fun a => if H a then full a else m' a.

Definition restrict (H : word -> bool) (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := mrestrict H (ms_mem ms);
     ms_rom := ms_rom ms |}.

Definition unrestrict (H : word -> bool) (full : word -> option byte)
    (ms' : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
     ms_pc_val := ms_pc_val ms';
     ms_svc_pending := ms_svc_pending ms';
     ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
     ms_mem := munrestrict H full (ms_mem ms');
     ms_rom := ms_rom ms' |}.

(* [comment removed for export] *)
Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
  forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.

(* [comment removed for export] *)
Definition wx_segs_nowrap (segs : list Segment) : Prop :=
  forall seg, In seg segs ->
    seg_executable seg && seg_writable seg = true ->
    (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z.

(* [comment removed for export] *)
Definition woff (a : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> H (woff a k) = false.

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
  forall a n, In (a, n) l -> range_avoids H a n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma woff_0 : forall a, woff a 0 = a.
Proof.
  intros a. unfold woff. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma woff_succ : forall a k, woff (a + 1) k = woff a (S k).
Proof.
  intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma range_avoids_hd : forall H a n,
  range_avoids H a (S n) -> H a = false.
Proof.
  intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.

Lemma range_avoids_tl : forall H a n,
  range_avoids H a (S n) -> range_avoids H (a + 1) n.
Proof.
  intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.

Lemma range_avoids_cons : forall H a n,
  H a = false -> range_avoids H (a + 1) n -> range_avoids H a (S n).
Proof.
  intros H a n H0 Hr k Hk. destruct k as [|k].
  - rewrite woff_0. exact H0.
  - rewrite <- woff_succ. apply Hr. lia.
Qed.

Lemma ranges_avoid_nil : forall H, ranges_avoid H [].
Proof. intros H a n Hin. destruct Hin. Qed.

Lemma ranges_avoid_cons : forall H a n l,
  range_avoids H a n -> ranges_avoid H l -> ranges_avoid H ((a, n) :: l).
Proof.
  intros H a n l Ha Hl a' n' [Heq | Hin].
  - injection Heq as <- <-. exact Ha.
  - exact (Hl a' n' Hin).
Qed.

Lemma ranges_avoid_app : forall H l1 l2,
  ranges_avoid H l1 -> ranges_avoid H l2 -> ranges_avoid H (l1 ++ l2).
Proof.
  intros H l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin];
    [exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.

(* [comment removed for export] *)
Lemma restrict_svc_pending : forall H ms,
  ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma restrict_pc : forall H ms, ms_pc (restrict H ms) = ms_pc ms.
Proof. reflexivity. Qed.
Lemma restrict_regs : forall H ms, ms_regs (restrict H ms) = ms_regs ms.
Proof. reflexivity. Qed.
Lemma restrict_reg : forall H ms r, ms_reg (restrict H ms) r = ms_reg ms r.
Proof. reflexivity. Qed.
Lemma restrict_rom : forall H ms, ms_rom (restrict H ms) = ms_rom ms.
Proof. reflexivity. Qed.
Lemma restrict_mem : forall H ms, ms_mem (restrict H ms) = mrestrict H (ms_mem ms).
Proof. reflexivity. Qed.
Lemma unrestrict_svc_pending : forall H full ms,
  ms_svc_pending (unrestrict H full ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma unrestrict_mem : forall H full ms,
  ms_mem (unrestrict H full ms) = munrestrict H full (ms_mem ms).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma restrict_mkst : forall H regs pc mem rom,
  restrict H (mkst regs pc mem rom) = mkst regs pc (mrestrict H mem) rom.
Proof. reflexivity. Qed.

Lemma mrestrict_idem : forall H m, mrestrict H (mrestrict H m) = mrestrict H m.
Proof.
  intros H m. apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a); reflexivity.
Qed.

Lemma munrestrict_mrestrict : forall H m,
  munrestrict H m (mrestrict H m) = m.
Proof.
  intros H m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma mrestrict_munrestrict : forall H full m,
  mrestrict H (munrestrict H full m) = mrestrict H m.
Proof.
  intros H full m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma unrestrict_restrict : forall H ms,
  unrestrict H (ms_mem ms) (restrict H ms) = ms.
Proof.
  intros H ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite munrestrict_mrestrict. reflexivity.
Qed.

Lemma restrict_unrestrict : forall H full ms,
  restrict H (unrestrict H full ms) = restrict H ms.
Proof.
  intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite mrestrict_munrestrict. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hclean (H : word -> bool) (ms : machine_state) : Prop :=
  forall a, H a = true -> ms_mem ms a = None.

Lemma restrict_hclean : forall H ms, hclean H (restrict H ms).
Proof.
  intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.

Lemma hclean_restrict_id : forall H ms, hclean H ms -> restrict H ms = ms.
Proof.
  intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
  apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma restrict_unrestrict_clean : forall H full ms,
  hclean H ms -> restrict H (unrestrict H full ms) = ms.
Proof.
  intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Lemma memory_read1_hidden : forall a, H a = true -> memory_read segs a 1 = None.
Proof.
  intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.

Lemma ov_read_bytes_restrict : forall n m a bs,
  ov_read_bytes segs (mrestrict H m) a n = Some bs ->
  ov_read_bytes segs m a n = Some bs /\ range_avoids H a n.
Proof.
  induction n as [|n IH]; intros m a bs Hr.
  - cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
  - cbn [ov_read_bytes] in Hr |- *.
    unfold mrestrict in Hr at 1.
    destruct (H a) eqn:Ha.
    + rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
    + destruct (match m a with
                | Some b => Some b
                | None => match memory_read segs a 1 with
                          | Some (b :: _) => Some b | _ => None end
                end) as [b|]; [|discriminate].
      destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
        [|discriminate].
      destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
      rewrite Hfull. split; [exact Hr|].
      apply range_avoids_cons; assumption.
Qed.

Lemma wview_restrict : forall m a,
  wview segs (mrestrict H m) a =
    if H a then None else wview segs m a.
Proof.
  intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
  rewrite (HH a Ha). reflexivity.
Qed.

Lemma store_ok_restrict : forall n m a,
  store_ok segs (mrestrict H m) a n = true ->
  store_ok segs m a n = true /\ range_avoids H a n.
Proof.
  induction n as [|n IH]; intros m a Hs.
  - split; [reflexivity | intros k Hk; lia].
  - cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
    destruct (H a) eqn:Ha; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) Hs) as [Hfull Hav].
    split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

(* [comment removed for export] *)
Lemma write_to_mem_restrict : forall bs m a,
  range_avoids H a (length bs) ->
  write_to_mem (mrestrict H m) a bs = mrestrict H (write_to_mem m a bs).
Proof.
  induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite <- (IH _ (a + 1) Htl). f_equal.
  apply functional_extensionality. intro x. unfold mrestrict.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : forall bs m a x,
  range_avoids H a (length bs) -> H x = true ->
  write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha in Hx. discriminate.
Qed.

(* [comment removed for export] *)
Lemma mrestrict_visible : forall (H0 : word -> bool) m a,
  H0 a = false -> mrestrict H0 m a = m a.
Proof. intros H0 m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

Lemma ov_read_bytes_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  ov_read_bytes segs (mrestrict H0 m) a n = ov_read_bytes segs m a n.
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [ov_read_bytes]. unfold mrestrict at 1. rewrite (range_avoids_hd H0 a n Hav).
  rewrite (IH m (a + 1) (range_avoids_tl H0 a n Hav)). reflexivity.
Qed.

Lemma rdn_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  rdn segs (mrestrict H0 m) a n = rdn segs m a n.
Proof.
  intros H0 n m a Hav. rewrite <- !ov_rdn. apply ov_read_bytes_mrestrict_eq. exact Hav.
Qed.

Lemma wview_mrestrict_eq : forall (H0 : word -> bool) m a,
  H0 a = false -> wview segs (mrestrict H0 m) a = wview segs m a.
Proof. intros H0 m a Ha. unfold wview, mrestrict. rewrite Ha. reflexivity. Qed.

Lemma store_ok_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  store_ok segs (mrestrict H0 m) a n = store_ok segs m a n.
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [store_ok]. rewrite (wview_mrestrict_eq H0 m a (range_avoids_hd H0 a n Hav)).
  destruct (wview segs m a); [|reflexivity].
  exact (IH m (a + 1) (range_avoids_tl H0 a n Hav)).
Qed.

(* [comment removed for export] *)

Lemma find_segment_some_spec : forall l addr n seg,
  find_segment l addr n = Some seg ->
  In seg l /\ (Z.of_N (seg_base seg) <= addr)%Z
  /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - injection Hf as ->. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | split; assumption].
  - destruct (IH addr n seg Hf) as (Hin & H1 & H2).
    split; [right; exact Hin | split; assumption].
Qed.

Lemma find_segment_none_spec : forall l addr n,
  find_segment l addr n = None ->
  forall seg, In seg l ->
    ~ ((Z.of_N (seg_base seg) <= addr)%Z
       /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z).
Proof.
  induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
    [discriminate|].
  destruct Hin as [<- | Hin].
  - intros [H1 H2]. apply andb_false_iff in E as [E | E].
    + apply Z.leb_gt in E. lia.
    + apply Z.leb_gt in E. lia.
  - exact (IH addr n Hf seg Hin).
Qed.

(* [comment removed for export] *)
Lemma in_segment_not_hidden : forall (x : word) seg,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned x)%Z ->
  (bv_unsigned x + 1 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  H x = false.
Proof.
  intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
  exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.

Lemma seg_ov_read_bytes_restrict : forall n m seg a,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z ->
  seg_ov_read_bytes (mrestrict H m) seg a n = seg_ov_read_bytes m seg a n.
Proof.
  induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
  cbn [seg_ov_read_bytes].
  assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
  unfold mrestrict at 1. rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
    { rewrite bv_add_unsigned.
      assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (bv_unsigned_in_range 64 a). lia. }
    rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.

Lemma code_read_ov_restrict : forall m a n,
  code_read_ov segs (mrestrict H m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
  destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
  apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
  rewrite N_nat_Z. exact H2.
Qed.

Lemma fetch_word_ov_restrict : forall m a,
  fetch_word_ov segs (mrestrict H m) a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : forall m a,
  fetch_half_ov segs (mrestrict H m) a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : forall m a,
  fetch_half_any segs (mrestrict H m) a = fetch_half_any segs m a.
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : forall m a,
  fetch_tail_any segs (mrestrict H m) a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : forall m a,
  fetch_failure segs (mrestrict H m) a = fetch_failure segs m a.
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

(* [comment removed for export] *)
Lemma interp_eff_accesses_restrict : forall t m c mr' rs,
  interp_eff_accesses segs t (mrestrict H m)
    = MachineOk (@mkAccessReport _ (c, mr') rs) ->
  exists mf',
    interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs)
    /\ mr' = mrestrict H mf'
    /\ (forall x, H x = true -> mf' x = m x)
    /\ ranges_avoid H rs.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; (* [comment removed for export] *)
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  - (* [comment removed for export] *)
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  - (* [comment removed for export] *)
    destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [|destruct (range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    apply ranges_avoid_cons; assumption.
  - (* [comment removed for export] *)
    destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + apply ranges_avoid_cons; assumption.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_accesses_restrict : forall ms w msr' rs',
  decode_exec_accesses segs (restrict H ms) w
    = MachineOk (@mkAccessReport _ msr' rs') ->
  decode_exec_accesses segs ms w
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-.
    split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict H (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
      as (mf' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split; [|split; [exact Hrs|]].
    + unfold unrestrict. cbn.
      replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Theorem step_accesses_restrict : forall ms msr' rs',
  step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ msr' rs') ->
  step_accesses segs ms
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (vdso_text_at segs (ms_pc ms)); [discriminate|].
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

(* [comment removed for export] *)
Theorem step_restrict_sound : forall ms msr',
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists rep,
    step_accesses segs ms = MachineOk rep
    /\ access_value _ rep = unrestrict H (ms_mem ms) msr'
    /\ ranges_avoid H (accessed_ranges _ rep)
    /\ hclean H msr'
    /\ restrict H (unrestrict H (ms_mem ms) msr') = msr'.
Proof.
  intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
  exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
  split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
  apply restrict_unrestrict_clean. exact Hcl.
Qed.

(* [comment removed for export] *)
Corollary step_restrict_step : forall ms msr',
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  RiscvSemantics.step segs ms = MachineOk (unrestrict H (ms_mem ms) msr').
Proof.
  intros ms msr' Hs.
  destruct (step_restrict_sound ms msr' Hs) as (rep & Hsa & Hv & _).
  unfold RiscvSemantics.step, drop_access_report. rewrite Hsa, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_accesses_ecall_shape : forall ms msr' rs',
  step_accesses segs ms = MachineOk (@mkAccessReport _ msr' rs') ->
  ms_svc_pending msr' <> None ->
  rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
  /\ ms_svc_pending msr' = Some (ms_reg ms 17).
Proof.
  intros ms msr' rs' Hs Hsvc.
  assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ msr' rs') ->
            rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
            /\ ms_svc_pending msr' = Some (ms_reg ms 17)).
  { intros w Hd. unfold decode_exec_accesses in Hd.
    destruct (is_ecall w).
    - injection Hd as <- <-. cbn. repeat split; reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses segs _ _) as [[[c1 m1] rs1]| |]; try discriminate.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn in Hsvc.
      exfalso. apply Hsvc. reflexivity. }
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
  unfold fetch_failure in Hf.
  destruct (vdso_text_at segs (ms_pc ms)); [discriminate|].
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

End ISA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
  existsb (fun iv => (fst iv <=? bv_unsigned p)%Z
                     && (bv_unsigned p + page_size <=? snd iv)%Z) A.

(* [comment removed for export] *)
Definition A_wf (A : list (Z * Z)) : Prop :=
  Forall (fun iv => (fst iv <= snd iv)%Z /\ (fst iv) mod page_size = 0
                    /\ (snd iv) mod page_size = 0)%Z A.

(* [comment removed for export] *)
Fixpoint A_bytes (A : list (Z * Z)) : Z :=
  match A with
  | [] => 0
  | iv :: r => (snd iv - fst iv) + A_bytes r
  end%Z.

(* [comment removed for export] *)
Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
    (A : list (Z * Z)) : Prop :=
  forall w : word,
    page_in_ranges (page_base w) lazy = true -> H w = false ->
    page_allowedb A (page_base w) = true.

(* [comment removed for export] *)
Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m
  = (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
  minv_nodup    : List.NoDup (m_vm_materialized m);
  minv_aligned  : forall p, In p (m_vm_materialized m) ->
                    (bv_unsigned p mod page_size = 0)%Z;
  minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
  minv_lazy     : forall p, In p (m_vm_materialized m) ->
                    page_in_ranges p (m_vm_lazy m) = true;
  minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

(* [comment removed for export] *)
Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : forall m1 m2 m3,
  same_but_materialized m1 m2 -> same_but_materialized m2 m3 ->
  same_but_materialized m1 m3.
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma with_vm_backing_same : forall m mat',
  same_but_materialized m (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_frame : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m  (* [comment removed for export] *)
  /\ m_fds m' = m_fds m /\ m_pipes m' = m_pipes m /\ m_stdin m' = m_stdin m
  /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m
  /\ m_rlimit_core m' = m_rlimit_core m /\ m_clock m' = m_clock m
  /\ eager_used m' = eager_used m.
Proof.
  intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
  repeat split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint A_pages (A : list (Z * Z)) : list Z :=
  match A with
  | [] => []
  | iv :: r =>
      map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
          (seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
      ++ A_pages r
  end.

Lemma Zmod0_multiple : forall a, (a mod page_size = 0)%Z -> exists q, a = (page_size * q)%Z.
Proof.
  intros a Ha. exists (a / page_size)%Z.
  pose proof (Z.div_mod a page_size ltac:(unfold page_size; lia)) as Hdm.
  rewrite Ha, Z.add_0_r in Hdm. exact Hdm.
Qed.

Lemma A_pages_length : forall A,
  A_wf A -> (Z.of_nat (length (A_pages A)) * page_size = A_bytes A)%Z.
Proof.
  induction A as [|[lo hi] A IH]; intros Hwf; [reflexivity|].
  cbn [A_pages A_bytes fst snd]. inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst.
  cbn [fst snd] in *.
  rewrite length_app, length_map, length_seq, Nat2Z.inj_add, Z.mul_add_distr_r.
  rewrite (IH Hwf').
  destruct (Zmod0_multiple lo Hlo) as [qlo ->].
  destruct (Zmod0_multiple hi Hhi) as [qhi ->].
  replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
  rewrite Z.div_mul by (unfold page_size; lia).
  rewrite Z2Nat.id by (unfold page_size in Hle; lia).
  reflexivity.
Qed.

Lemma A_pages_in : forall A p,
  A_wf A ->
  (bv_unsigned p mod page_size = 0)%Z ->
  page_allowedb A p = true ->
  In (bv_unsigned p) (A_pages A).
Proof.
  induction A as [|[lo hi] A IH]; intros p Hwf Hal Hpa; [discriminate|].
  inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst. cbn [fst snd] in *.
  cbn [A_pages fst snd]. apply in_or_app.
  unfold page_allowedb in Hpa. cbn [existsb fst snd] in Hpa.
  apply orb_true_iff in Hpa as [Hpa | Hpa].
  - left. apply andb_true_iff in Hpa as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (Zmod0_multiple lo Hlo) as [qlo Eqlo].
    destruct (Zmod0_multiple hi Hhi) as [qhi Eqhi].
    destruct (Zmod0_multiple (bv_unsigned p) Hal) as [qp Eqp].
    rewrite Eqp in *. rewrite Eqlo, Eqhi in *.
    replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
    rewrite Z.div_mul by (unfold page_size; lia).
    apply in_map_iff. exists (Z.to_nat (qp - qlo)).
    unfold page_size in *.
    split.
    + rewrite Z2Nat.id by lia. lia.
    + apply in_seq. lia.
  - right. apply IH; [exact Hwf' | exact Hal | exact Hpa].
Qed.

Lemma NoDup_map_bv_unsigned : forall (l : list word),
  List.NoDup l -> List.NoDup (map bv_unsigned l).
Proof.
  intros l Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
  apply bv_eq in Hy. subst y. exact (Hx Hiny).
Qed.

Theorem allowed_pages_bound : forall A (pages : list word),
  A_wf A ->
  List.NoDup pages ->
  (forall p, In p pages -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p pages -> page_allowedb A p = true) ->
  (Z.of_nat (length pages) * page_size <= A_bytes A)%Z.
Proof.
  intros A pages Hwf Hnd Hal Hpa.
  rewrite <- (A_pages_length A Hwf).
  assert (Hlen : (length pages <= length (A_pages A))%nat).
  { rewrite <- (length_map bv_unsigned pages).
    apply NoDup_incl_length.
    - apply NoDup_map_bv_unsigned. exact Hnd.
    - intros z Hz. apply in_map_iff in Hz as (p & <- & Hp).
      apply A_pages_in; [exact Hwf | exact (Hal p Hp) | exact (Hpa p Hp)]. }
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_woff : forall a k,
  page_base (woff a k) = page_base_of (bv_unsigned a + Z.of_nat k).
Proof.
  intros a k. unfold page_base, woff, page_base_of.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  assert (Hz : (0 <= z)%Z) by (unfold z; lia).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite !two64_as_pages.
  set (r := (z mod (page_size * 2 ^ 52))%Z).
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  (* z = M*q + r ; both floors differ by M*q *)
  pose proof (Z.div_mod z (page_size * 2 ^ 52) ltac:(lia)) as Hdm.
  fold r in Hdm.
  set (q := (z / (page_size * 2 ^ 52))%Z) in Hdm.
  assert (Hfl : (z / page_size * page_size = page_size * 2 ^ 52 * q + r / page_size * page_size)%Z).
  { rewrite Hdm at 1.
    replace (page_size * 2 ^ 52 * q + r)%Z with (r + (2 ^ 52 * q) * page_size)%Z by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hfl.
  replace (page_size * 2 ^ 52 * q + r / page_size * page_size)%Z
    with (r / page_size * page_size + q * (page_size * 2 ^ 52))%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma page_base_of_aligned : forall z,
  (bv_unsigned (page_base_of z) mod page_size = 0)%Z.
Proof.
  intros z. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite two64_as_pages.
  rewrite (Z.mul_comm (z / page_size) page_size).
  rewrite Zmult_mod_distr_l.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma page_insert_nodup : forall p pages,
  List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages Hnd. unfold page_insert.
  destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
  constructor; [|exact Hnd].
  intros Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma page_mem_false_not_in : forall p pages,
  page_mem p pages = false -> ~ In p pages.
Proof.
  intros p pages Hm Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
  apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
  apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages Hin. unfold page_insert in Hin.
  destruct (page_mem q pages); [right; exact Hin|].
  destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.

Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
  - left; exact Hin.
  - destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin''.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
  - left; exact Hin.
  - destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma new_pages_props : forall H A lazy mat ranges,
  lazy_cover H lazy A ->
  ranges_avoid H ranges ->
  let new := newly_materialized_pages lazy mat ranges in
  List.NoDup new
  /\ (forall p, In p new -> ~ In p mat)
  /\ (forall p, In p new -> (bv_unsigned p mod page_size = 0)%Z)
  /\ (forall p, In p new -> page_in_ranges p lazy = true)
  /\ (forall p, In p new -> page_allowedb A p = true).
Proof.
  intros H A lazy mat ranges Hcov Hav new.
  assert (Hchar : forall p, In p new ->
            page_in_ranges p lazy = true /\ page_mem p mat = false
            /\ exists a n k, In (a, n) ranges /\ (k < n)%nat
                             /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z).
  { intros p Hin. unfold new, newly_materialized_pages in Hin.
    apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
    split; [exact Hl|]. split; [destruct (page_mem p mat); [discriminate | reflexivity]|].
    destruct (accesses_pages_in ranges [] p Hin) as [[] | Hex]. exact Hex. }
  split; [|split; [|split; [|split]]].
  - unfold new, newly_materialized_pages. apply NoDup_filter.
    apply accesses_pages_nodup. constructor.
  - intros p Hp. destruct (Hchar p Hp) as (_ & Hm & _). apply page_mem_false_not_in. exact Hm.
  - intros p Hp. destruct (Hchar p Hp) as (_ & _ & a & n & k & _ & _ & ->).
    apply page_base_of_aligned.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _). exact Hl.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _ & a & n & k & Hin & Hk & Ep).
    pose proof (Hav a n Hin k Hk) as Hw.
    rewrite <- page_base_woff in Ep. rewrite Ep in Hl |- *.
    exact (Hcov (woff a k) Hl Hw).
Qed.

(* [comment removed for export] *)
Lemma m_vm_materialized_wvb : forall l X m,
  m_vm_materialized (with_vm_backing l X m) = X.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_halted_wvb : forall l X m, m_halted (with_vm_backing l X m) = m_halted m.
Proof. reflexivity. Qed.
Lemma eager_used_wvb : forall X m,
  eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m.
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma MInv_wvb : forall A m X,
  List.NoDup X ->
  (forall p, In p X -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p X -> page_allowedb A p = true) ->
  (forall p, In p X -> page_in_ranges p (m_vm_lazy m) = true) ->
  (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z ->
  MInv A (with_vm_backing (m_vm_lazy m) X m).
Proof.
  intros A m X H1 H2 H3 H4 H5. constructor;
    rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb;
    assumption.
Qed.

(* [comment removed for export] *)
Theorem materialize_restricted : forall H A m ranges,
  lazy_cover H (m_vm_lazy m) A ->
  A_wf A ->
  MInv A m ->
  ranges_avoid H ranges ->
  exists mat',
    materialize_model_accesses m ranges
      = Some (with_vm_backing (m_vm_lazy m) mat' m)
    /\ MInv A (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros H A m ranges Hcov Hwf [Hnd Hal Hpa Hlz Hbud] Hav.
  destruct (new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav)
    as (Nnd & Nfresh & Nal & Nlz & Npa).
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
  assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) ->
                      (bv_unsigned p mod page_size = 0)%Z).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
  assert (Happ_pa : forall p, In p (new ++ m_vm_materialized m) -> page_allowedb A p = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Npa p Hp) | exact (Hpa p Hp)]. }
  assert (Happ_lz : forall p, In p (new ++ m_vm_materialized m) ->
                      page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nlz p Hp) | exact (Hlz p Hp)]. }
  pose proof (allowed_pages_bound A (new ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa)
    as Hbound.
  rewrite length_app, Nat2Z.inj_add in Hbound.
  destruct new as [|p0 new'] eqn:Enew.
  - exists (m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
  - rewrite vm_backing_used_split.
    replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
             + Z.of_nat (length (p0 :: new')) * page_size
             <=? vm_limit (m_vmmaps m))%Z with true.
    2:{ symmetry. apply Z.leb_le. unfold page_size in *. lia. }
    exists ((p0 :: new') ++ m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Theorem mi_account_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists mat',
    mi_account_step segs ms model
      = MachineOk (unrestrict H (ms_mem ms) msr',
                   with_vm_backing (m_vm_lazy model) mat' model)
    /\ MInv A (with_vm_backing (m_vm_lazy model) mat' model)
    /\ hclean H msr'.
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hs.
  destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
  destruct (materialize_restricted H A model (accessed_ranges _ rep) Hcov Hwf Hinv Hrs)
    as (mat' & Hmat & Hinv').
  exists mat'. unfold mi_account_step. rewrite Hsa, Hmat, Hv.
  split; [reflexivity | split; [exact Hinv' | exact Hcl]].
Qed.

(* [comment removed for export] *)
Lemma sstep_instr_det : forall ms model ms1 model1 e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms1, model1) ->
  sstep segs (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms1 model1).
Proof.
  intros ms model ms1 model1 e st Hsvc Hacc Hss.
  inversion Hss; subst;
    match goal with
    | Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
    | Ha : mi_account_step segs ms model = _ |- _ =>
        rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
    end.
Qed.

(* [comment removed for export] *)
Theorem node_instr_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists model',
    MInv A model' /\ same_but_materialized model model'
    /\ hclean H msr'
    /\ mi_account_step segs ms model
         = MachineOk (unrestrict H (ms_mem ms) msr', model')
    /\ node_ok (mkCfg ms model) unit (fun _ => [])
               (fun _ => mkCfg (unrestrict H (ms_mem ms) msr') model').
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
  destruct (mi_account_step_restricted A ms msr' model Hcov Hwf Hinv Hs)
    as (mat' & Hacc & Hinv' & Hcl).
  exists (with_vm_backing (m_vm_lazy model) mat' model).
  split; [exact Hinv'|]. split; [apply with_vm_backing_same|]. split; [exact Hcl|].
  split; [exact Hacc|].
  split.
  - intros []. apply sstep_instr; [exact Hh | exact Hsvc | exact Hacc].
  - intros e st Hss. exists tt.
    exact (sstep_instr_det ms model _ _ e st Hsvc Hacc Hss).
Qed.

(* [comment removed for export] *)
Lemma step_hclean : forall ms ms',
  hclean H ms ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  hclean H ms'.
Proof.
  intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
  destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
  exact Hcl.
Qed.

Lemma msteps_hclean : forall ms ms',
  msteps segs ms ms' -> hclean H ms -> hclean H ms'.
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; intros Hc.
  - exact Hc.
  - apply IH. exact (step_hclean ms ms1 Hc Hstep).
Qed.

Lemma unrestrict_munrestrict : forall f g ms',
  unrestrict H (munrestrict H f g) ms' = unrestrict H f ms'.
Proof.
  intros f g ms'. unfold unrestrict. f_equal.
  apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x); reflexivity.
Qed.

(* [comment removed for export] *)
Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
  ms_svc_pending (cfg_ms c) = None ->
  node_ok c unit (fun _ => []) (fun _ => c') -> P c' -> P c.   (* [comment removed for export] *)

Theorem rz_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk.
  destruct (node_instr_restricted A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & _ & _ & Hnode).
  exact (P_silent1 (mkCfg ms model) _ Hsvc Hnode (Hk model' Hinv' Hsame)).
Qed.

Theorem rz_msteps_restricted : forall A msr0 msr',
  msteps segs msr0 msr' ->
  forall ms model,
  msr0 = restrict H ms ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
    intros ms model -> Hcov Hwf Hinv Hh Hk.
  - specialize (Hk model Hinv (same_but_materialized_refl model)).
    rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_restricted A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
      as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
    apply (P_silent1 (mkCfg ms model) _ Hsvc Hnode).
    pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
    apply (IH (unrestrict H (ms_mem ms) msr1) model1).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
    + exact Hwf.
    + exact Hinv1.
    + replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
    + intros model' Hinv' Hsame'.
      rewrite unrestrict_mem, unrestrict_munrestrict.
      apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
(* [comment removed for export] *)
Theorem rz_msteps_restricted' : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
  pose proof (msteps_hclean _ _ Hms (restrict_hclean H ms)) as Hcl.
  apply (rz_msteps_restricted A (restrict H ms) msr' Hms ms model eq_refl Hcov Hwf Hinv Hh).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.

End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses.
  unfold newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
  match materialize_model_accesses m accs with
  | Some m' => m'
  | None => m
  end.

Section SyscallNode.
Variable segs : list Segment.
Variable H : word -> bool.

(* [comment removed for export] *)
Theorem node_syscall_restricted :
  forall A ms model x8 (I : Type)
         (eff : I -> SyscallEffect) (mdl : I -> Model) (evs : I -> list event),
  A_wf A ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (eff i) (mdl i) (evs i))) ->
  (forall r, syscall_spec (sys_input segs ms x8) model r ->
             exists i, r = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, m_halted (mdl i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (mdl i)) A) ->
  (forall i, MInv A (mdl i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (eff i))) ->
  (forall i, MInv A (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))
             /\ same_but_materialized (mdl i)
                  (materialized_succ (mdl i) (syscall_effect_accesses (eff i))))
  /\ node_ok segs (mkCfg ms model) I evs
       (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i)))
                       (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))).
Proof.
  intros A ms model x8 I eff mdl evs Hwf Hh Hsvc Hsound Hcompl Hnh Hcov Hinv Hav.
  assert (Hmat : forall i, exists mat',
            materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
              = Some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
            /\ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))).
  { intros i. exact (materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)). }
  split.
  - intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
    unfold materialized_succ. rewrite Hm. split; [exact Hinv' | apply with_vm_backing_same].
  - split.
    + intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
      unfold materialized_succ. rewrite Hm.
      eapply sstep_syscall; [exact Hh | exact Hsvc | exact (Hsound i) | exact (Hnh i) | exact Hm].
    + intros e st Hss. inversion Hss; subst;
        match goal with
        | Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
        | Hp : ms_svc_pending ms = Some ?x |- _ =>
            rewrite Hsvc in Hp; injection Hp as <-
        end;
        match goal with
        | Hsp : syscall_spec _ _ ?r |- _ =>
            destruct (Hcompl _ Hsp) as [i Ei]; try discriminate Ei;
            injection Ei as -> -> ->
        end.
      * (* sstep_syscall *)
        exists i. split; [reflexivity|].
        unfold materialized_succ.
        match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite Hm end.
        reflexivity.
      * (* materialization fault: impossible *)
        destruct (Hmat i) as (mat' & Hm & _).
        match goal with Hn : materialize_model_accesses _ _ = None |- _ => rewrite Hm in Hn; discriminate end.
      * (* exit: impossible, no outcome halts *)
        match goal with Hc : m_halted (mdl i) = Some _ |- _ => rewrite (Hnh i) in Hc; discriminate end.
      * (* killed: impossible for the same reason *)
        match goal with Hk : m_killed (mdl i) = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh i)) in Hk; discriminate end.
Qed.
End SyscallNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
  fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).

Lemma page_in_ranges_incl : forall p l L,
  incl l L -> page_in_ranges p l = true -> page_in_ranges p L = true.
Proof.
  intros p l L Hincl Hp. unfold page_in_ranges in *.
  apply existsb_exists in Hp as (r & Hin & Hr).
  apply existsb_exists. exists r. split; [exact (Hincl r Hin) | exact Hr].
Qed.

Lemma lazy_cover_mkH : forall L A lazy,
  incl lazy L -> lazy_cover (mkH L A) lazy A.
Proof.
  intros L A lazy Hincl w Hl Hw. unfold mkH in Hw.
  rewrite (page_in_ranges_incl _ _ _ Hincl Hl) in Hw. cbn in Hw.
  destruct (page_allowedb A (page_base w)); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition seg_top (seg : Segment) : Z :=
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition wx_segs_nowrap_b (segs : list Segment) : bool :=
  forallb (fun seg => negb (seg_executable seg && seg_writable seg)
                      || (seg_top seg <=? 2 ^ 64)%Z) segs.

Lemma wx_segs_nowrap_of_b : forall segs,
  wx_segs_nowrap_b segs = true -> wx_segs_nowrap segs.
Proof.
  intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
  rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
  apply Z.leb_le in Hb. exact Hb.
Qed.

Definition segs_below_b (segs : list Segment) (top : Z) : bool :=
  forallb (fun seg => (seg_top seg <=? top)%Z) segs.

Lemma find_segment1_none_above : forall segs top x,
  segs_below_b segs top = true -> (top <= x)%Z -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros top x Hb Hx; [reflexivity|].
  cbn [segs_below_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply Z.leb_le in Hs. unfold seg_top in Hs.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z
    with false.
  - exact (IH top x Hl Hx).
  - symmetry. apply andb_false_iff. right. apply Z.leb_gt. lia.
Qed.

(* [comment removed for export] *)
Lemma H_off_segments_above : forall segs (H : word -> bool) top,
  segs_below_b segs top = true ->
  (forall a, H a = true -> (top <= bv_unsigned a)%Z) ->
  H_off_segments segs H.
Proof.
  intros segs H top Hb Ha a HHa. exact (find_segment1_none_above segs top _ Hb (Ha a HHa)).
Qed.

(* [comment removed for export] *)
Definition ranges_from_b (L : list (word * word)) (top : Z) : bool :=
  forallb (fun r => (top <=? bv_unsigned (fst r))%Z) L.

Lemma page_base_le : forall a, (bv_unsigned (page_base a) <= bv_unsigned a)%Z.
Proof.
  intros a. unfold page_base, page_base_of. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hmb.
  assert (Hq : (0 <= bv_unsigned a / page_size)%Z)
    by (apply Z.div_pos; unfold page_size in *; lia).
  set (q := (bv_unsigned a / page_size)%Z) in *.
  change (bv_modulus 64) with (2 ^ 64)%Z in *. unfold page_size in *.
  rewrite bv_wrap_small; [lia|].
  change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.

Lemma mkH_above : forall L A top a,
  ranges_from_b L top = true -> mkH L A a = true -> (top <= bv_unsigned a)%Z.
Proof.
  intros L A top a Hb Ha. unfold mkH in Ha. apply andb_true_iff in Ha as [Hp _].
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as ([lo sz] & Hin & Hr).
  cbn [fst snd] in Hr. apply andb_true_iff in Hr as [H1 _]. apply Z.leb_le in H1.
  unfold ranges_from_b in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Hin).
  cbn [fst] in Hb. apply Z.leb_le in Hb.
  pose proof (page_base_le a). lia.
Qed.

Corollary H_off_segments_mkH : forall segs L A top,
  segs_below_b segs top = true -> ranges_from_b L top = true ->
  H_off_segments segs (mkH L A).
Proof.
  intros segs L A top Hs HL.
  apply (H_off_segments_above segs (mkH L A) top Hs).
  intros a Ha. exact (mkH_above L A top a HL Ha).
Qed.

(* [comment removed for export] *)
Lemma MInv_intro_empty : forall A m,
  m_vm_materialized m = [] ->
  (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z ->
  MInv A m.
Proof.
  intros A m He Hb. constructor; rewrite ?He;
    [constructor | intros p Hp; destruct Hp | intros p Hp; destruct Hp
    | intros p Hp; destruct Hp | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma MInv_transport : forall A m m',
  MInv A m ->
  m_vm_materialized m' = m_vm_materialized m ->
  m_vm_lazy m' = m_vm_lazy m ->
  (eager_used m' + A_bytes A <= vm_limit (m_vmmaps m'))%Z ->
  MInv A m'.
Proof.
  intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.


End FPX_1.

End AsanAcct.
Module AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg. (* [comment removed for export] *)
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.pnode_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs scfg c T.

Let P_of_silent1 (T : TSet) : forall c c',
    ms_svc_pending (cfg_ms c) = None ->
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hsvc Hn Hr => rz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn)
                          (RomBase.sys_rob_instr segs c Hsvc) Hr.

Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.

Theorem rz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs scfg c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    ms_svc_pending (cfg_ms c) = None ->
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hsvc Hn Hr => srz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn)
                          (RomBase.sys_rob_instr segs c Hsvc) Hr.

Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.

Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.

End FPX_1.

End AsanAcctShape.
Module SymStepR.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_SymStepR () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC59OSSVerify5KrLib7Mh_0037:DivergeSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib7Classes;EquivalenceEpointwise_equivalenceC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_app_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg?is_prefix_nil_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8pnode_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00368ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_of_iffC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00367SpinAlg:srealizes001C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg7rz_alt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg9rz_cases1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg8node_svcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368ShapeAlg;node_svc_onC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00368ShapeAlg>t_alt_emit_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SpinAlg8srz_alt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00367SpinAlg:srz_cases1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_00368AsanAcctGnode_syscall_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368AsanAcct7node_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv3Sem7reg_getC49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib7Mh_00368SymStepR5mkstRC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5instr09C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0BC4ELinuxProcessSemantics5Riscv3Sem7mul_divI4ELinuxProcessSemantics5Riscv5Instr5mulop00K4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr01C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC49OSSVerify5KrLib8PropExec9jalr_tgtZC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8jalr_tgtC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_jalrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?c59OSSVerify5KrLib7Mh_00368SymStepR;load_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff07C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368SymStepR;msize_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractK47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5msize00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6NArith6BinNat1N2leC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions?bv_wrap_bv_wrapC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib7Mh_00368SymStepR<resv_inval_wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK4ELinuxProcessSemantics5Riscv3Sem3eff08C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExecAstore_bytes_low16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExecAstore_bytes_low32C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z6inj_leI47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K4ELinuxProcessSemantics5Riscv5Instr5instr0DC4ELinuxProcessSemantics5Riscv3Sem9amo_bytesC56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib7Mh_00368SymStepR:amo_nbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00368SymStepR9amo_msizeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv3Sem3eff06I4ELinuxProcessSemantics5Riscv5Instr6awidth00K4ELinuxProcessSemantics5Riscv5Instr6awidth01K4ELinuxProcessSemantics5Riscv5Instr6awidth02K4ELinuxProcessSemantics5Riscv5Instr5instr0EC56Stdlib6ZArith6BinInt1Z8eqb_reflK4ELinuxProcessSemantics5Riscv5Instr5instr0Fc59OSSVerify5KrLib7Mh_00368SymStepR?amo_store_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7amo_valI4ELinuxProcessSemantics5Riscv5Instr5amoop00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition mkstR (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (rv : option word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := rv; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkstR_None : forall regs pc mem rom, mkstR regs pc mem rom None = mkst regs pc mem rom.
Proof. reflexivity. Qed.

Lemma mkstR_svc : forall regs pc mem rom rv, ms_svc_pending (mkstR regs pc mem rom rv) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition resv_inval_w (rv : option word) (a : word) : option word :=
  match rv with
  | Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else rv
  | None => None
  end.

(* [comment removed for export] *)
Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
  match sz with
  | SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
  end.

Definition eff_sx (sz : msize) (sx : bool) : bool :=
  match sz with SZ8 => false | _ => sx end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition amo_msize (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition amo_nbytes (wd : awidth) : nat := match wd with AW => 4%nat | AD => 8%nat end.

(* [comment removed for export] *)
Definition amo_store_bytes (op : amoop) (wd : awidth) (bs : list byte) (src : word) : list byte :=
  match wd with
  | AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 src)))
  | AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) src))
  end.
End FPX_1.


Ltac stepR_pipeline Hfetch Hecall Hdecode :=
  unfold mkstR;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_opimm_gen : forall segs regs pc mem rom rv w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_opimm32_gen : forall segs regs pc mem rom rv w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm32_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_lui : forall segs regs pc mem rom rv w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma stepR_auipc : forall segs regs pc mem rom rv w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma stepR_jal_link : forall segs regs pc mem rom rv w rd (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                   (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

Lemma stepR_jalr : forall segs regs pc mem rom rv w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                   (v_jalr (getr regs rs1) (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs1 imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd, v_jalr.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_jalr; reflexivity.
Qed.

Lemma stepR_branch_tk_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma stepR_branch_ft_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fence : forall segs regs pc mem rom rv w a b c d e,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c d e Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma stepR_fencei : forall segs regs pc mem rom rv w a b c,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI a b c, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_load : forall segs regs pc mem rom rv w sz sx rd rs (imm : bv 12) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
    rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
    destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_store : forall segs regs pc mem rom rv w sz (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) (msize_bytes sz) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes (msize_bytes sz) (getr regs rs2))) rom
    (resv_inval_w rv (v_addi (getr regs rs1) (bv_signed imm)))).
Proof.
  intros segs regs pc mem rom rv w sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite !b_addsext.
  destruct sz; cbn [msize_bytes] in Hok |- *; cbv beta iota delta [store_val];
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?Hsb, ?store_bytes_low16, ?store_bytes_low32, b_npc4;
    (destruct rv as [r|]; cbv beta iota; [|reflexivity]);
    unfold resv_inval_w;
    match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepR_lr : forall segs regs pc mem rom rv w wd aq rl rd rs bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc 4) mem rom (Some (getr regs rs))).
Proof.
  intros segs regs pc mem rom rv w wd aq rl rd rs bs Hfetch Hecall Hdecode Hal Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite b_npc4; unfold regupd;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_sc_ok : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom (Some r)) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                   (wbytes mem (getr regs rs1) (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom None).
Proof.
  intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    subst r; rewrite Z.eqb_refl; cbv beta iota;
    cbn [amo_nbytes] in Hok |- *; rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc4;
    unfold regupd, word_to_le_bytes;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_amo : forall segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs1) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc 4)
                   (wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2)))
                   rom (resv_inval_w rv (getr regs rs1))).
Proof.
  intros segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread, Hok |- *; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, b_npc4; unfold regupd, amo_store_bytes;
    (destruct rv as [r|]; cbv beta iota);
    unfold resv_inval_w;
    try match goal with |- context [Z.eqb (bv_unsigned r) ?y] =>
          destruct (Z.eqb (bv_unsigned r) y); cbv beta iota end;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

End FPX_2.

End SymStepR.

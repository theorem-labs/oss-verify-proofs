(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n YK11 YK0i.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section a.
Context {fx : FPState}.
Lemma step_lbu_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, isz) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = None ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread.
reflexivity.
Qed.
Lemma step_ld_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd rs imm, isz) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = None ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread.
reflexivity.
Qed.
Section b.
Variable segs : list Segment.
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
End b.
Section d.
Variable segs : list Segment.
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
- intros evs c' Hnext. exfalso. inversion Hnext; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
discriminate
end.
Qed.
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
Lemma fault_covered_at : forall ms model,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineFault ->
~ unmodeled_at segs (mkCfg ms model).
Proof.
intros ms model Hlazy Hsvc Hfault (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
- rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
discriminate.
- congruence.
Qed.
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
End d.
Section e.
Variable segs : list Segment.
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
- intros evs c' Hnext. inversion Hnext; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
discriminate
end.
Qed.
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
End e.
Section f.
Variable segs : list Segment.
Lemma star_stuck_refl : forall c tr c',
(forall evs c2, ~ sstep segs c evs (SNext c2)) ->
star segs c tr c' -> c' = c.
Proof.
intros c tr c' Hno Hstar. inversion Hstar; subst; [reflexivity|].
exfalso. eapply Hno; eassumption.
Qed.
Lemma fault_no_unmodeled : forall ms model,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineFault ->
~ reaches_unmodeled segs (mkCfg ms model).
Proof.
intros ms model Hlazy Hsvc Hfault (tr & c & Hstar & Hun).
assert (Hno : forall evs c2, ~ sstep segs (mkCfg ms model) evs (SNext c2)).
{ intros evs c2 Hss. inversion Hss; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in H;
discriminate
end. }
rewrite (star_stuck_refl _ tr c Hno Hstar) in Hun.
destruct Hun as (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
- rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
discriminate.
- congruence.
Qed.
Lemma instr_no_unmodeled : forall ms ms' model,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
~ reaches_unmodeled segs (mkCfg ms' model) ->
~ reaches_unmodeled segs (mkCfg ms model).
Proof.
intros ms ms' model Hlazy Hsvc Hstep Hnext (tr & c & Hstar & Hun).
inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hrest]; subst.
- destruct Hun as (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
+ rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in Hum.
discriminate.
+ congruence.
- destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss)
as [_ Hc2].
inversion Hc2; subst. apply Hnext. exists tr2, c. split; assumption.
Qed.
Lemma msteps_fault_no_unmodeled : forall ms ms' model,
msteps segs ms ms' ->
m_vm_lazy model = [] ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
~ reaches_unmodeled segs (mkCfg ms model).
Proof.
intros ms ms' model Hm Hlazy Hsvc Hfault.
destruct (m_halted model) as [code |] eqn:Hh.
-
intros (tr & c & Hstar & Hun).
inversion Hstar as [| c1 evs c2 tr2 c3 Hss]; subst.
+ destruct Hun as (Hun & _). cbn in Hun. congruence.
+ pose proof (sstep_from_running segs _ _ _ Hss) as Hrun. cbn in Hrun. congruence.
- apply coexec_covered. eapply msteps_illegal_covered; eassumption.
Qed.
End f.
Lemma err_escape_omni_run :
forall segs pc ph sp brk0 mb rnd lim inp ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp errors.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
cbn [omni_run]. unfold init_config.
eapply msteps_illegal_errors; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.
Lemma err_escape_omni_covered :
forall segs pc ph sp brk0 mb rnd lim inp ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (covered segs).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
cbn [omni_corun]. unfold init_config.
eapply msteps_illegal_covered; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.
Lemma err_escape_omni_equiv :
forall segs pc ph sp brk0 mb rnd lim inp T limT et ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_equiv (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) T limT et inp.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp T limT et ms' Hm Hsvc Hill.
left. eapply err_escape_omni_run; eassumption.
Qed.
Lemma err_escape_omni_strong_equiv :
forall segs pc ph sp brk0 mb rnd inp T et ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_strong_equiv (mkImage segs pc ph) T (mkEntry sp brk0 mb rnd) et inp.
Proof.
intros segs pc ph sp brk0 mb rnd inp T et ms' Hm Hsvc Hill.
split.
- cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
- eapply err_escape_omni_equiv; eassumption.
Qed.
Lemma err_escape_equiv :
forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
left. apply bh_all_errors_iff. eapply err_escape_omni_run; eassumption.
Qed.
Lemma err_escape_modeled :
forall segs pc ph sp brk0 mb rnd lim inp ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
apply modeled_iff. cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
Qed.
Lemma err_escape_strong_equiv :
forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
/\ Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
target.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
split; [eapply err_escape_modeled | eapply err_escape_equiv]; eassumption.
Qed.
End a.

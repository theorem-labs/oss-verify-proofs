(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ErrEscape () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.Riscv.Instr.Load"; "LinuxProcessSemantics.Riscv.Instr.SZ1"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.bv_signed"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineFault"; "LinuxProcessSemantics.Riscv.Instr.SZ8"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exec"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.outcome"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.OError"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.post"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Run.unmodeled_at"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.errors"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.coexec"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.covered"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exits_with"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.never_errors"; "LinuxProcessSemantics.LinuxProcessSem.Run.all_traces_error"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_unmodeled"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_corun"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Image"; "LinuxProcessSemantics.LinuxProcessSem.Run.ExecEntry"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.LinuxProcessSem.Run.behavior"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"].


Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma step_lbu_fault : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Pregs,(2.&5.(3.&40.))Ppc,(3.&40.)Pmem,P,(3.&40.)(4.(3.&8.))Prom,P,(3.&40.)(4.(3.&8.))Pw,(3.&20.)Prd,(3.&5.)Prs,(3.&5.)Pimm,(3.&<.)Pisz,$5.P,(6.(4.(3.&20.))(7.R:.R8.)(8.(3.&20.)R5.))P,(6.$9.(:.R6.)$;.)P,(6.(4.(<.$=.$5.))(>.R7.)(8.(<.$=.$5.)(?.$=.$5.(10.$11.$;.R6.R5.R4.)R3.)))P,(6.(4.(0.(3.&8.)))(12.R=.R:.(13.(14.R<.R6.)(15.&<.R5.))#1.)(16.(0.(3.&8.))))(6.(17.$18.)(19.R>.(1:.Vfx,R=.R<.R;.R:.))(1;.$18.))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_ld_fault : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Pregs,(2.&5.(3.&40.))Ppc,(3.&40.)Pmem,P,(3.&40.)(4.(3.&8.))Prom,P,(3.&40.)(4.(3.&8.))Pw,(3.&20.)Prd,(3.&5.)Prs,(3.&5.)Pimm,(3.&<.)Pisz,$5.P,(6.(4.(3.&20.))(7.R:.R8.)(8.(3.&20.)R5.))P,(6.$9.(:.R6.)$;.)P,(6.(4.(<.$=.$5.))(>.R7.)(8.(<.$=.$5.)(?.$=.$5.(10.$1<.$1=.R6.R5.R4.)R3.)))P,(6.(4.(0.(3.&8.)))(12.R=.R:.(13.(14.R<.R6.)(15.&<.R5.))#8.)(16.(0.(3.&8.))))(6.(17.$18.)(19.R>.(1:.Vfx,R=.R<.R;.R:.))(1;.$18.))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_star_nil : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)(23.Vsegs,(24.R6.R4.)(21.$25.)(24.R5.R4.))")
(* [comment removed for export] *).
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
#[using="Type"] Lemma msteps_illegal_error : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(1;.$18.))(27.Vsegs,(24.R8.R6.))")
(* [comment removed for export] *).
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
#[using="Type"] Lemma illegal_exec : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R4.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R5.)(1;.$18.))(28.Vsegs,(24.R6.R5.)Ltr,(0.$25.)Lo,$29.(2:.(6.(0.$25.)R2.(21.$25.))(6.$29.R1.(2;.(24.R8.R7.)))))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
#[using="Type"] Lemma instr_exec : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.PQ,$2<.P,(6.(4.(3.&40.))(1?.R2.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R3.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R6.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R7.)(2=.$18.R6.))P,(28.Vsegs,(24.R7.R6.)R5.)(28.Vsegs,(24.R9.R7.)R6.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Q Hh Hlazy Hsvc Hstep Hex.
  apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
  - apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros evs st Hss.
    exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
  - eapply exec_conseq; [exact Hex |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma msteps_exec : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.PQ,$2<.P,(6.(4.(3.&40.))(1?.R2.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R3.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R6.R5.)P,(28.Vsegs,(24.R6.R5.)R4.)(28.Vsegs,(24.R8.R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Q Hh Hlazy Hm Hex.
  induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH]; [exact Hex |].
  eapply instr_exec; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_illegal_exec : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(1;.$18.))(28.Vsegs,(24.R8.R6.)Ltr,(0.$25.)Lo,$29.(2:.(6.(0.$25.)R2.(21.$25.))(6.$29.R1.(2;.(24.R9.R8.)))))")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  eapply msteps_exec; [exact Hh | exact Hlazy | exact Hm |].
  apply illegal_exec; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fault_covered_at : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pmodel,$1>.P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R1.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R3.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R4.)(1;.$18.))(2>.(2?.Vsegs,(24.R5.R4.)))")
(* [comment removed for export] *).
Proof.
  intros ms model Hlazy Hsvc Hfault (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
  - rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_illegal_errors : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(1;.$18.))(28.Vsegs,(24.R8.R6.)$30.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
  intros tr o (_ & ->). exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_illegal_covered : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(1;.$18.))(31.Vsegs,(24.R8.R6.)(32.Vsegs,))")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  apply exec_coexec.
  eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
  intros tr o (_ & ->). unfold covered. apply fault_covered_at; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_illegal_no_exit : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(1;.$18.))Pcode,(3.&40.)(2>.(28.Vsegs,(24.R9.R7.)(33.R1.)))")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill code Hex.
  destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
    as (tr & o & Hm' & _ & ->).
  exact (exec_sound _ _ _ Hex _ _ Hm').
Qed.

#[using="Type"] Lemma msteps_illegal_not_never_errors : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(1;.$18.))(2>.(31.Vsegs,(24.R8.R6.)$34.))")
(* [comment removed for export] *).
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
#[using="Type"] Lemma illegal_all_traces_error : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R4.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R5.)(1;.$18.))(35.Vsegs,(24.R6.R5.))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
#[using="Type"] Lemma instr_all_traces_error : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(2=.$18.R5.))P,(35.Vsegs,(24.R6.R5.))(35.Vsegs,(24.R8.R6.))")
(* [comment removed for export] *).
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
#[using="Type"] Lemma msteps_all_traces_error : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(35.Vsegs,(24.R5.R4.))(35.Vsegs,(24.R7.R5.))")
(* [comment removed for export] *).
Proof.
  intros ms ms' model Hh Hlazy Hm Hall.
  induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH].
  - exact Hall.
  - eapply instr_all_traces_error; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_illegal_all_traces_error : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(4.(3.&40.))(1?.R1.)(16.(3.&40.)))P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(22.Vsegs,R5.R4.)P,(6.(4.(3.&40.))(26.R5.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R6.)(1;.$18.))(35.Vsegs,(24.R8.R6.))")
(* [comment removed for export] *).
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
#[using="Type"] Lemma star_stuck_refl : forall c tr c',
  (forall evs c2, ~ sstep segs c evs (SNext c2)) ->
  star segs c tr c' -> c' = c.
Proof.
  intros c tr c' Hno Hstar. inversion Hstar; subst; [reflexivity|].
  exfalso. eapply Hno; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fault_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pmodel,$1>.P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R1.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R3.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R4.)(1;.$18.))(2>.(36.Vsegs,(24.R5.R4.)))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
#[using="Type"] Lemma instr_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R1.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R4.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R5.)(2=.$18.R4.))P,(2>.(36.Vsegs,(24.R5.R4.)))(2>.(36.Vsegs,(24.R7.R5.)))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_fault_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Pms,$18.Pms',$18.Pmodel,$1>.P,(22.Vsegs,R3.R2.)P,(6.(0.(<.(3.&40.)(3.&40.)))(20.R2.)(21.(<.(3.&40.)(3.&40.))))P,(6.(4.(3.&40.))(26.R4.)(16.(3.&40.)))P,(6.(17.$18.)(19.Vsegs,R5.)(1;.$18.))(2>.(36.Vsegs,(24.R7.R5.)))")
(* [comment removed for export] *).
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
#[using="Type"] Lemma err_escape_omni_run : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Ppc,$37.Pph,$38.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$39.Plim,$5.Pinp,$3:.Pms',$18.P,(22.R:.(3;.R:.R9.R8.R7.R4.(3<.R2.)(3=.R2.)(3>.R2.)(3?.R2.))R1.)P,(6.(4.(3.&40.))(26.R2.)(16.(3.&40.)))P,(6.(17.$18.)(19.R<.R3.)(1;.$18.))(40.(41.R=.R<.R;.)R6.(42.R:.R9.R8.R7.)R5.$30.)")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  cbn [omni_run]. unfold init_config.
  eapply msteps_illegal_errors; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma err_escape_omni_covered : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Ppc,$37.Pph,$38.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$39.Plim,$5.Pinp,$3:.Pms',$18.P,(22.R:.(3;.R:.R9.R8.R7.R4.(3<.R2.)(3=.R2.)(3>.R2.)(3?.R2.))R1.)P,(6.(4.(3.&40.))(26.R2.)(16.(3.&40.)))P,(6.(17.$18.)(19.R<.R3.)(1;.$18.))(43.(41.R=.R<.R;.)R6.(42.R:.R9.R8.R7.)R5.(32.R=.))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  cbn [omni_corun]. unfold init_config.
  eapply msteps_illegal_covered; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma err_escape_omni_equiv : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Ppc,$37.Pph,$38.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$39.Plim,$5.Pinp,$3:.PT,$44.PlimT,$5.Pet,$45.Pms',$18.P,(22.R=.(3;.R=.R<.R;.R:.R7.(3<.R5.)(3=.R5.)(3>.R5.)(3?.R5.))R1.)P,(6.(4.(3.&40.))(26.R2.)(16.(3.&40.)))P,(6.(17.$18.)(19.R?.R3.)(1;.$18.))(46.(41.R10.R?.R>.)R9.(42.R=.R<.R;.R:.)R7.R6.R5.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T limT et ms' Hm Hsvc Hill.
  left. eapply err_escape_omni_run; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma err_escape_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Ppc,$37.Pph,$38.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$39.Pinp,$3:.PT,$44.Pet,$45.Pms',$18.P,(22.R;.(3;.R;.R:.R9.R8.R5.(3<.R4.)(3=.R4.)(3>.R4.)(3?.R4.))R1.)P,(6.(4.(3.&40.))(26.R2.)(16.(3.&40.)))P,(6.(17.$18.)(19.R=.R3.)(1;.$18.))(47.(41.R>.R=.R<.)R6.(42.R;.R:.R9.R8.)R5.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd inp T et ms' Hm Hsvc Hill.
  split.
  - cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
  - eapply err_escape_omni_equiv; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma err_escape_equiv : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Ppc,$37.Pph,$38.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$39.Plim,$5.Pinp,$3:.Ptarget,$48.Pms',$18.P,(22.R;.(3;.R;.R:.R9.R8.R5.(3<.R3.)(3=.R3.)(3>.R3.)(3?.R3.))R1.)P,(6.(4.(3.&40.))(26.R2.)(16.(3.&40.)))P,(6.(17.$18.)(19.R=.R3.)(1;.$18.))(49.(4:.(41.R>.R=.R<.)R7.(42.R;.R:.R9.R8.)R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
  left. apply bh_all_errors_iff. eapply err_escape_omni_run; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma err_escape_modeled : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Ppc,$37.Pph,$38.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$39.Plim,$5.Pinp,$3:.Pms',$18.P,(22.R:.(3;.R:.R9.R8.R7.R4.(3<.R2.)(3=.R2.)(3>.R2.)(3?.R2.))R1.)P,(6.(4.(3.&40.))(26.R2.)(16.(3.&40.)))P,(6.(17.$18.)(19.R<.R3.)(1;.$18.))(4;.(4:.(41.R=.R<.R;.)R6.(42.R:.R9.R8.R7.)R5.))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  apply modeled_iff. cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma err_escape_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_ErrEscape ()) "Psegs,(0.$1.)Ppc,$37.Pph,$38.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$39.Plim,$5.Pinp,$3:.Ptarget,$48.Pms',$18.P,(22.R;.(3;.R;.R:.R9.R8.R5.(3<.R3.)(3=.R3.)(3>.R3.)(3?.R3.))R1.)P,(6.(4.(3.&40.))(26.R2.)(16.(3.&40.)))P,(6.(17.$18.)(19.R=.R3.)(1;.$18.))(2:.(4;.(4:.(41.R>.R=.R<.)R7.(42.R;.R:.R9.R8.)R6.))(49.(4:.(41.R>.R=.R<.)R7.(42.R;.R:.R9.R8.)R6.)R5.))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
  split; [eapply err_escape_modeled | eapply err_escape_equiv]; eassumption.
Qed.
End WithFP1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb RelSpec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeX StoreOk AgentLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes AgentNodes SysNodes NodesDir.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_NodesA () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Shape.node_ok"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Init.Datatypes.unit"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.Lib.Shape.TSet"; "OSSVerify.KrLib.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "OSSVerify.KrLib.Sys.AgentNodes.epend"; "OSSVerify.KrLib.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "LinuxProcessSemantics.LinuxProcessSem.Monad.outcome"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.Lib.Shape.t_emit"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "OSSVerify.KrLib.LibA.ALazy.acc_ok"; "OSSVerify.KrLib.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.with_copyins"; "vm_same"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "OSSVerify.KrLib.Lib.PropExec.regupd"; "OSSVerify.KrLib.Lib.PropExec.v_addi"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.State.with_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_remove"; "OSSVerify.KrLib.BB.RelSpec.fde_not_devnull"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOTTY"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.FdDir"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Stdlib.ZArith.BinInt.Z.to_nat"; "LinuxProcessSemantics.LinuxProcessSem.State.EISDIR"; "LinuxProcessSemantics.LinuxProcessSem.Fs.path"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFile"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.State.MAX_RW_COUNT"; "OSSVerify.KrLib.LibA.ALazy.aok_addr"; "LinuxProcessSemantics.LinuxProcessSem.Fs.file_read"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_insert"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "OSSVerify.KrLib.BB.CatExec.wbytes"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Shape.t_exit"; "stdpp.bitvector.definitions.bv_and"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_same (mo mo' : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "(0.(1.$2.(3.O1.)(3.O2.))(0.(1.(4.(5.(6.&40.)(6.&40.)))(7.O1.)(7.O2.))(0.(1.(4.(6.&40.))(8.O1.)(8.O2.))(1.(9.(6.&40.))(:.O1.)(:.O2.)))))")
(* [comment removed for export] *).

Lemma vm_same_refl : forall mo, vm_same mo mo.
Proof. intros; repeat split; reflexivity. Qed.

Lemma vm_same_with_fds : forall fds mo, vm_same mo (with_fds fds mo).
Proof. intros; repeat split; reflexivity. Qed.

Lemma materialize_nil : forall mo, materialize_model_accesses mo [] = Some mo.
Proof.
  intros mo. apply newly_nil_materialize. unfold newly_materialized_pages. cbn. reflexivity.
Qed.

Lemma syscall_effect_accesses_ret : forall r, syscall_effect_accesses (mkEffect r [] []) = [].
Proof. reflexivity. Qed.

Lemma syscall_effect_accesses_copyins : forall reads r,
  syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads.
Proof. intros. unfold syscall_effect_accesses. cbn. apply app_nil_r. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma node_instr_acc : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmo,$<.Pms',$;.Pmo',$<.P,(1.(9.(6.&40.))(:.R3.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R5.)(=.(6.&40.)))P,(1.(?.(5.$;.$<.))(10.Vsegs,R6.R5.)(11.(5.$;.$<.)(12.$;.$<.R4.R3.)))(13.Vsegs,(14.R7.R6.)$15.L,$15.(16.$17.)L,$15.(14.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros ms mo ms' mo' Hh Hsvc Hacc. split.
  - intros []. apply (sstep_instr segs ms mo ms' mo'); assumption.
  - intros e st Hss. destruct (sstep_acc_inv segs ms mo ms' mo' e st Hsvc Hacc Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_step_acc : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmo,$<.Pms',$;.Pmo',$<.PT,$18.P,(1.(9.(6.&40.))(:.R4.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R6.)(=.(6.&40.)))P,(1.(?.(5.$;.$<.))(10.Vsegs,R7.R6.)(11.(5.$;.$<.)(12.$;.$<.R5.R4.)))P,(19.Vsegs,(14.R6.R5.)R4.)(19.Vsegs,(14.R9.R8.)R5.)")
(* [comment removed for export] *).
Proof.
  intros ms mo ms' mo' T Hh Hsvc Hacc Hc.
  eapply srzJ_silent1; [apply node_instr_acc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_step_noacc : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmo,$<.Pms',$;.PT,$18.P,(1.(9.(6.&40.))(:.R3.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R5.)(=.(6.&40.)))P,(1.(?.(1:.$;.))(1;.Vsegs,R6.)(11.(1:.$;.)(1<.$;.R4.(16.$1=.))))P,(19.Vsegs,(14.R5.R6.)R4.)(19.Vsegs,(14.R8.R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros ms mo ms' T Hh Hsvc Hst Hc.
  eapply rz_step_acc; [exact Hh | exact Hsvc | | exact Hc].
  unfold mi_account_step. rewrite Hst. cbn [accessed_ranges access_value]. rewrite materialize_nil. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_accesses_ecall : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Prom,P,(6.&40.)(9.(6.&8.))Pw,(6.&20.)P,(1.(9.(6.&20.))(1?.Vsegs,R4.)(20.(6.&20.)R1.))P,(1.$21.(22.R2.)$23.)(1.(?.(1:.$;.))(1;.Vsegs,(24.$25.R7.R6.R5.R4.))(11.(1:.$;.)(1<.$;.(26.R7.R6.R5.R4.(27.R7.(28.&5.+11.$29.)))(16.$1=.))))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom w HF HE. unfold step_accesses. cbn [ms_pc mkst ms_pc_val]. unfold ms_pc. cbn [mkst ms_pc_val].
  rewrite HF. unfold decode_exec_accesses. rewrite HE. reflexivity.
Qed.

#[using="Type"] Lemma rz_sysA : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Prom,P,(6.&40.)(9.(6.&8.))Pmo,$<.Pw,(6.&20.)PT,$18.P,(1.(9.(6.&40.))(:.R3.)(=.(6.&40.)))P,(1.(9.(6.&20.))(1?.Vsegs,R7.)(20.(6.&20.)R3.))P,(1.$21.(22.R4.)$23.)P,(19.Vsegs,(14.(26.R:.R9.R8.R7.(27.R:.(28.&5.+11.$29.)))R6.)R4.)(19.Vsegs,(14.(24.$25.R;.R:.R9.R8.)R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom mo w T Hh HF HE Hc.
  eapply rz_step_noacc; [exact Hh | reflexivity | eapply step_accesses_ecall; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_of_spec_mat : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)Peff,$2:.Pm',$<.Pm'',$<.Pevs,(4.$17.)P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R8.)(20.(6.&40.)R6.))P,(2;.(2<.Vsegs,R9.R7.)R8.(2=.$2:.R6.R5.R3.))P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(1.(9.$<.)(2>.R7.(2?.R8.))(20.$<.R6.))(30.Vsegs,(14.R<.R;.)R6.(31.(14.(32.(33.R<.R9.))R7.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff m' m'' evs Hh Hsvc Hc Hh' Hmat.
  apply (sstep_syscall segs ms model x8 eff m' m'' evs Hh Hsvc Hc Hh' Hmat).
Qed.

#[using="Type"] Lemma node_chk_ev_mat : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)PI,StPeffs,P,R1.$2:.Pms',P,R2.$<.Pms'',P,R3.$<.Pevs,P,R4.(4.$17.)P,(1.(9.(6.&40.))(:.R7.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R9.)(20.(6.&40.)R7.))P,Pi,R7.(2;.(2<.Vsegs,R;.R9.)R:.(2=.$2:.A1.R7.R1.A1.R6.R1.A1.R4.R1.))P,Peff,$2:.Pm',$<.Pev,(4.$17.)P,(2;.(2<.Vsegs,R>.R<.)R=.(2=.$2:.R3.R2.R1.))(34.R<.Li,R<.(0.(1.$2:.R5.A1.R<.R1.)(0.(1.$<.R4.A1.R;.R1.)(1.(4.$17.)R3.A1.R9.R1.))))P,(35.(2;.(2<.Vsegs,R<.R:.)R;.(36.$2:.)))P,Pi,R:.(1.(9.(6.&40.))(:.A1.R9.R1.)(=.(6.&40.)))P,Pi,R;.(1.(9.$<.)(2>.A1.R:.R1.(2?.A1.R;.R1.))(20.$<.A1.R9.R1.))(13.Vsegs,(14.R?.R>.)R<.R8.Li,R<.(14.(32.(33.R10.A1.R<.R1.))A1.R:.R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 I effs ms' ms'' evs Hh Hsvc Hok Hinv Hnu Hh' Hmat. split.
  - intros i. apply (sstep_of_spec_mat ms model x8 _ (ms' i)); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m0 & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu Hc).
Qed.

#[using="Type"] Lemma node_family_mat : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)PI,StPeffs,P,R1.$2:.Pms',P,R2.$<.Pms'',P,R3.$<.Pevs,P,R4.(4.$17.)PR,P,(37.$2:.)SpP,(1.(9.(6.&40.))(:.R8.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R:.)(20.(6.&40.)R8.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R<.R:.)R;.R1.)A1.R4.R1.)P,Pi,R9.A1.R5.(2=.$2:.A1.R9.R1.A1.R8.R1.A1.R6.R1.)P,Po,(37.$2:.)P,A1.R6.R1.(34.R<.Li,R<.(1.(37.$2:.)R3.(2=.$2:.A1.R<.R1.A1.R;.R1.A1.R9.R1.)))P,Pi,R;.(1.(9.(6.&40.))(:.A1.R:.R1.)(=.(6.&40.)))P,Pi,R<.(1.(9.$<.)(2>.A1.R;.R1.(2?.A1.R<.R1.))(20.$<.A1.R:.R1.))(13.Vsegs,(14.R10.R?.)R=.R9.Li,R=.(14.(32.(33.R11.A1.R=.R1.))A1.R;.R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hout Hh' Hmat.
  apply (node_chk_ev_mat ms model x8 I effs ms' ms'' evs Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - intros eff m' ev Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi).
    apply Ok_inj in Hi as (-> & -> & ->). exists i. auto.
  - intros Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
  - exact Hh'.
  - exact Hmat.
Qed.

#[using="Type"] Lemma node_det_mat : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)Peff0,$2:.Pm0,$<.Pm1,$<.Pevs0,(4.$17.)P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R8.)(20.(6.&40.)R6.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R:.R8.)R9.R1.)(1.(37.$2:.)R1.(2=.$2:.R7.R6.R4.)))P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(1.(9.$<.)(2>.R7.(2?.R8.))(20.$<.R6.))(13.Vsegs,(14.R<.R;.)$15.L,$15.R7.L,$15.(14.(32.(33.R=.R:.))R8.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 m1 evs0 Hh Hsvc Hchk Hh0 Hmat.
  apply (node_family_mat ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => m1) (fun _ => evs0)
           (fun o => o = Ok eff0 m0 evs0) Hh Hsvc Hchk).
  - intros []. reflexivity.
  - intros o ->. exists tt. reflexivity.
  - intros []; exact Hh0.
  - intros []; exact Hmat.
Qed.

#[using="Type"] Lemma rz_det_mat : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)Peff0,$2:.Pm0,$<.Pm1,$<.Pevs,(4.$17.)PT,$18.P,(1.(9.(6.&40.))(:.R7.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R9.)(20.(6.&40.)R7.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R;.R9.)R:.R1.)(1.(37.$2:.)R1.(2=.$2:.R8.R7.R5.)))P,(1.(9.(6.&40.))(:.R7.)(=.(6.&40.)))P,(1.(9.$<.)(2>.R8.(2?.R9.))(20.$<.R7.))P,(19.Vsegs,(14.(32.(33.R=.R:.))R8.)R6.)(19.Vsegs,(14.R>.R=.)(39.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 m1 evs T Hh Hsvc Hchk Hh0 Hmat Hc.
  eapply srzJ_emit1; [eapply node_det_mat; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_det_mat_silent : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)Peff0,$2:.Pm0,$<.Pm1,$<.PT,$18.P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R8.)(20.(6.&40.)R6.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R:.R8.)R9.R1.)(1.(37.$2:.)R1.(2=.$2:.R7.R6.(16.$17.))))P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(1.(9.$<.)(2>.R7.(2?.R8.))(20.$<.R6.))P,(19.Vsegs,(14.(32.(33.R<.R9.))R7.)R6.)(19.Vsegs,(14.R=.R<.)R7.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 m1 T Hh Hsvc Hchk Hh0 Hmat Hc.
  eapply srzJ_silent1; [eapply node_det_mat; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_ret_only_noacc : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)Pr,(6.&40.)Pm',$<.Pevs,(4.$17.)PT,$18.P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R8.)(20.(6.&40.)R6.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R:.R8.)R9.R1.)(1.(37.$2:.)R1.(2=.$2:.(3:.R7.(16.(5.(6.&40.)(4.(6.&8.))))(16.(5.(6.&40.)(6.&40.)))(16.(5.(6.&40.)(6.&40.)))(16.$3;.)(16.(5.(6.&40.)$3<.)))R6.R5.)))P,(1.(9.(6.&40.))(:.R6.)(=.(6.&40.)))P,(19.Vsegs,(14.(32.(3=.R;.R8.))R7.)R5.)(19.Vsegs,(14.R<.R;.)(39.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hc.
  rewrite <- (apply_effect_no_write ms r) in Hc.
  eapply rz_det_mat; [exact Hh | exact Hsvc | exact Hchk | exact Hh' | | exact Hc].
  rewrite syscall_effect_accesses_ret. apply materialize_nil.
Qed.

#[using="Type"] Lemma rz_ret_only_noacc_silent : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmodel,$<.Px8,(6.&40.)Pr,(6.&40.)Pm',$<.PT,$18.P,(1.(9.(6.&40.))(:.R5.)(=.(6.&40.)))P,(1.(9.(6.&40.))(>.R7.)(20.(6.&40.)R5.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R9.R7.)R8.R1.)(1.(37.$2:.)R1.(2=.$2:.(3:.R6.(16.(5.(6.&40.)(4.(6.&8.))))(16.(5.(6.&40.)(6.&40.)))(16.(5.(6.&40.)(6.&40.)))(16.$3;.)(16.(5.(6.&40.)$3<.)))R5.(16.$17.))))P,(1.(9.(6.&40.))(:.R5.)(=.(6.&40.)))P,(19.Vsegs,(14.(32.(3=.R:.R7.))R6.)R5.)(19.Vsegs,(14.R;.R:.)R6.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hc.
  rewrite <- (apply_effect_no_write ms r) in Hc.
  eapply rz_det_mat_silent; [exact Hh | exact Hsvc | exact Hchk | exact Hh' | | exact Hc].
  rewrite syscall_effect_accesses_ret. apply materialize_nil.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KForm.
Variable AL : asan_layout.
Variable CS : Z -> Prop.
Variable K : Model -> Prop.
Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pmo,$<.Pacc,(4.(5.(6.&40.)$3<.))P,A1.VK,R2.P,(3>.VAL,VCS,R2.)(34.$<.Lmo',$<.(0.(1.(9.$<.)(2>.R5.R4.)(20.$<.R1.))(0.A1.VK,R1.(3?.R5.R1.))))")
(* [comment removed for export] *).
Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pmo,$<.Pmo',$<.P,A1.VK,R2.P,(1.$2.(3.R2.)(3.R3.))P,(1.(4.(5.(6.&40.)(6.&40.)))(7.R3.)(7.R4.))P,(1.(4.(6.&40.))(8.R4.)(8.R5.))P,(1.(9.(6.&40.))(:.R5.)(:.R6.))A1.VK,R6.")
(* [comment removed for export] *).

#[using="K_vmonly"] Lemma K_vm_same : forall mo mo', K mo -> vm_same mo mo' -> K mo'.
Proof. intros mo mo' HK (A & B & C & D). eapply K_vmonly; eauto. Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat K_vmonly"] Lemma rz_ret_only_copyinsK : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmo,$<.Px8,(6.&40.)Preads,(4.(5.(6.&40.)$3<.))Pr,(6.&40.)Pm',$<.Pevs,(4.$17.)PT,$18.P,A1.VK,R7.P,(1.(9.(6.&40.))(>.R9.)(20.(6.&40.)R7.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R;.R9.)R:.R1.)(1.(37.$2:.)R1.(2=.$2:.(40.R8.(3:.R7.(16.(5.(6.&40.)(4.(6.&8.))))(16.(5.(6.&40.)(6.&40.)))(16.(5.(6.&40.)(6.&40.)))(16.$3;.)(16.(5.(6.&40.)$3<.))))R6.R5.)))P,(41.R:.R6.)P,(3>.VAL,VCS,R9.)P,Pmo'',$<.P,A1.VK,R1.P,(3?.R:.R2.)(19.Vsegs,(14.(32.(3=.R10.R<.))R3.)R9.)(19.Vsegs,(14.R>.R=.)(39.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms mo x8 reads r m' evs T HK Hsvc Hchk VS OK Hc.
  pose proof (K_halted mo HK) as Hh.
  pose proof (K_vm_same mo m' HK VS) as HK'.
  destruct (K_mat m' reads HK' OK) as (mo'' & Hm & HK'' & MM).
  rewrite <- (apply_effect_copyins_no_write ms r reads) in Hc.
  eapply (rz_det_mat _ _ _ _ m' mo''); [exact Hh | exact Hsvc | exact Hchk | exact (K_halted _ HK') | | apply Hc; [exact HK''|exact MM]].
  rewrite syscall_effect_accesses_copyins. exact Hm.
Qed.

#[using="K_halted K_mat K_vmonly"] Lemma rz_ret_only_copyinsK_silent : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pms,$;.Pmo,$<.Px8,(6.&40.)Preads,(4.(5.(6.&40.)$3<.))Pr,(6.&40.)Pm',$<.PT,$18.P,A1.VK,R6.P,(1.(9.(6.&40.))(>.R8.)(20.(6.&40.)R6.))P,Po,(37.$2:.)(38.(2;.(2<.Vsegs,R:.R8.)R9.R1.)(1.(37.$2:.)R1.(2=.$2:.(40.R7.(3:.R6.(16.(5.(6.&40.)(4.(6.&8.))))(16.(5.(6.&40.)(6.&40.)))(16.(5.(6.&40.)(6.&40.)))(16.$3;.)(16.(5.(6.&40.)$3<.))))R5.(16.$17.))))P,(41.R9.R5.)P,(3>.VAL,VCS,R8.)P,Pmo'',$<.P,A1.VK,R1.P,(3?.R9.R2.)(19.Vsegs,(14.(32.(3=.R?.R;.))R3.)R9.)(19.Vsegs,(14.R=.R<.)R7.)")
(* [comment removed for export] *).
Proof.
  intros ms mo x8 reads r m' T HK Hsvc Hchk VS OK Hc.
  pose proof (K_halted mo HK) as Hh.
  pose proof (K_vm_same mo m' HK VS) as HK'.
  destruct (K_mat m' reads HK' OK) as (mo'' & Hm & HK'' & MM).
  rewrite <- (apply_effect_copyins_no_write ms r reads) in Hc.
  eapply (rz_det_mat_silent _ _ _ _ m' mo''); [exact Hh | exact Hsvc | exact Hchk | exact (K_halted _ HK') | | apply Hc; [exact HK''|exact MM]].
  rewrite syscall_effect_accesses_copyins. exact Hm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="K_halted"] Lemma rz_closeA : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Pmo,$<.Pw,(6.&20.)Pfd,(6.&40.)Pe,$42.PT,$18.P,(1.(9.(6.&20.))(1?.Vsegs,R7.)(20.(6.&20.)R4.))P,(1.$21.(22.R5.)$23.)P,A1.VK,R7.P,(1.(6.&40.)(27.R;.(28.&5.+11.$29.))(43.&40.+39.))P,(1.(6.&40.)(27.R<.(28.&5.+:.$29.))R7.)P,(44.(45.&40.R8.)(46.+2.+20.))P,(1.(9.$42.)(47.(48.R;.)R9.)(20.$42.R8.))P,(19.Vsegs,(14.(24.$25.(49.R?.(28.&5.+:.$29.)(43.&40.=))(4:.R>.+4.)R=.(4;.Vsegs,))(4<.(4=.(48.R<.)R:.)R<.))R8.)(19.Vsegs,(14.(24.$25.R10.R?.R>.(4;.Vsegs,))R=.)R9.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd e T HF HE HK H17 Hfd Hfd32 Hlk Hc.
  pose proof (K_halted mo HK) as Hh.
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_noacc_silent; [exact Hh | reflexivity | | | rewrite adv_set_epend; exact Hc].
  - intros o. rewrite (syscall_spec_57 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, ms_gpr_epend0, Hfd, (fd32_id fd Hfd32). exact (close_outcome fd _ mo e o Hlk).
  - rewrite with_fds_halted'. exact Hh.
Qed.

#[using="K_vmonly"] Lemma K_with_fds : forall fds mo, K mo -> K (with_fds fds mo).
Proof. intros fds mo HK. eapply K_vm_same; [exact HK | apply vm_same_with_fds]. Qed.

(* [comment removed for export] *)
#[using="K_halted"] Lemma rz_ioctl_winszA : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Pmo,$<.Pw,(6.&20.)Pfd,(6.&40.)Pe,$42.PT,$18.P,(1.(9.(6.&20.))(1?.Vsegs,R7.)(20.(6.&20.)R4.))P,(1.$21.(22.R5.)$23.)P,A1.VK,R7.P,(1.(6.&40.)(27.R;.(28.&5.+11.$29.))(43.&40.+1=.))P,(1.(6.&40.)(27.R<.(28.&5.+:.$29.))R7.)P,(44.(45.&40.R8.)(46.+2.+20.))P,(1.(9.$42.)(47.(48.R;.)R9.)(20.$42.R8.))P,(4>.R9.)P,(1.(6.&40.)(27.R10.(28.&5.+;.$29.))(43.&40.+5413.))P,(19.Vsegs,(14.(24.$25.(49.R11.(28.&5.+:.$29.)(4?.$50.))(4:.R10.+4.)R?.(4;.Vsegs,))R>.)R:.)(19.Vsegs,(14.(24.$25.R12.R11.R10.(4;.Vsegs,))R?.)R;.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd e T HF HE HK H17 Hfd Hfd32 Hlk Hnd H11 Hc.
  pose proof (K_halted mo HK) as Hh.
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_noacc_silent; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros o. rewrite (syscall_spec_29 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
  rewrite in_arg0_si, in_arg1_si, ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), H11.
  apply (ioctl_tty_outcome fd _ _ mo e o Hlk Hnd). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="K_halted"] Lemma rz_read_dir_mappedA : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Pmo,$<.Pw,(6.&20.)Pfd,(6.&40.)Pcnt,$51.PT,$18.P,(1.(9.(6.&20.))(1?.Vsegs,R7.)(20.(6.&20.)R4.))P,(1.$21.(22.R5.)$23.)P,A1.VK,R7.P,(1.(6.&40.)(27.R;.(28.&5.+11.$29.))(43.&40.+3?.))P,(1.(6.&40.)(27.R<.(28.&5.+:.$29.))R7.)P,(44.(45.&40.R8.)(46.+2.+20.))P,(1.(9.$42.)(47.(48.R;.)R9.)(20.$42.$52.))P,(1.(6.&40.)(27.R?.(28.&5.+<.$29.))(43.&40.R9.))P,(53.+1.R:.)P,(53.R;.(46.+2.+18.))P,(53.(54.(45.&40.(27.R12.(28.&5.+;.$29.)))R<.)$55.)P,(1.$21.(56.Vsegs,R11.(27.R13.(28.&5.+;.$29.))(57.R=.))$23.)P,(19.Vsegs,(14.(24.$25.(49.R14.(28.&5.+:.$29.)(4?.$58.))(4:.R13.+4.)R12.(4;.Vsegs,))R11.)R=.)(19.Vsegs,(14.(24.$25.R15.R14.R13.(4;.Vsegs,))R12.)R>.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd cnt T HF HE HK H17 Hfd Hfd32 Hlk H12 Hc1 H64 Hover Hok Hc.
  pose proof (K_halted mo HK) as Hh.
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_noacc_silent; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros o. rewrite (syscall_spec_63 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
  apply (read_dir_outcome fd _ _ _ mo o Hlk).
  rewrite H12. apply access_okb_of_bound.
  rewrite u64_lit by (unfold TASK_SIZE in Hover; pose proof (u64_range (getr regs 11)); lia).
  exact Hover.
Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat K_vmonly"] Lemma rz_read_fileA : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Pmo,$<.Pw,(6.&20.)Pfd,(6.&40.)Pp,$59.Poff,(6.&40.)Pdata,(4.(6.&8.))Pcnt,$51.PT,$18.P,(1.(9.(6.&20.))(1?.Vsegs,R:.)(20.(6.&20.)R7.))P,(1.$21.(22.R8.)$23.)P,A1.VK,R:.P,(1.(6.&40.)(27.R>.(28.&5.+11.$29.))(43.&40.+3?.))P,(1.(6.&40.)(27.R?.(28.&5.+:.$29.))R:.)P,(44.(45.&40.R;.)(46.+2.+20.))P,(1.(9.$42.)(47.(48.R>.)R<.)(20.$42.(5:.R;.R:.)))P,(1.(9.(4.(6.&8.)))(5;.(5<.R?.)R<.)(20.(4.(6.&8.))R:.))P,(1.(6.&40.)(27.R13.(28.&5.+<.$29.))(43.&40.R:.))P,(53.+1.R;.)P,(53.R<.$5=.)P,(44.R=.(46.+2.+40.))P,(53.(54.(45.&40.(27.R17.(28.&5.+;.$29.)))R>.)$55.)P,(1.$21.(56.Vsegs,R16.(27.R18.(28.&5.+;.$29.))(57.R?.))$23.)P,Pz,$51.P,(0.(53.(45.&40.(27.R1:.(28.&5.+;.$29.)))R1.)(44.R1.(54.(45.&40.(27.R1:.(28.&5.+;.$29.)))R11.)))(5>.VAL,VCS,R2.)Zbs,(4.(6.&8.))(5?.R12.R13.(27.R1:.(28.&5.+<.$29.)))Zm',$<.(4<.(60.(48.R18.)R16.(5:.R15.(61.&40.R14.(62.(6.&8.)R1.))))R18.)P,Pmo'',$<.P,A1.VK,R1.P,(3?.R3.R2.)(19.Vsegs,(14.(24.$25.(49.R1?.(28.&5.+:.$29.)(62.(6.&8.)R5.))(4:.R1>.+4.)(63.R1=.(27.R1?.(28.&5.+;.$29.))R5.)(4;.Vsegs,))R3.)R15.)(19.Vsegs,(14.(24.$25.R1=.R1<.R1;.(4;.Vsegs,))R1:.)R13.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem mo w fd p off data cnt T HF HE HK H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hover Hok OK.
  cbv zeta. intros Hc.
  pose proof (K_halted mo HK) as Hh.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  pose proof (read_file_outcome_si segs ms (getr regs 17) mo fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(unfold ms; rewrite ms_gpr_epend1, ms_gpr_epend2, H12; apply access_okb_of_bound; rewrite u64_lit by lia; exact Hover)) as Hchk.
  unfold ms in Hchk. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  (* [comment removed for export] *)
  assert (HL : (Z.of_nat (length (file_read data off (getr regs 12))) <= cnt)%Z).
  { rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat. rewrite H12, u64_lit by lia. lia. }
  revert Hc Hchk HL.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk HL.
  set (m' := with_fds (fd_insert (m_fds mo) fd (FdFile p (off + len_word bs))) mo) in *.
  assert (HK' : K m') by (subst m'; apply K_with_fds; exact HK).
  assert (OKw : acc_ok AL CS (syscall_effect_accesses (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []))).
  { unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    destruct bs as [|b bsr]; cbn [delivered_writes write_accesses].
    - intros z (a & n & [] & _).
    - intros z (a & n & Hin & Hz). destruct Hin as [E|[]]. injection E as <- <-. apply OK. cbn [length] in HL, Hz |- *. lia. }
  destruct (K_mat m' _ HK' OKw) as (mo'' & Hm & HK'' & MM).
  eapply (rz_det_mat_silent _ mo _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []) m' mo'');
    [exact Hh | reflexivity | exact Hchk | exact (K_halted _ HK') | exact Hm | ].
  destruct bs as [|b bsr]; cbn [delivered_writes].
  - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. apply Hc; assumption.
  - unfold ms. rewrite adv_write1_epend. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_exit_atA : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Prom,P,(6.&40.)(9.(6.&8.))Pmo,$<.Pw,(6.&20.)Pcode,(6.&40.)P,(1.(9.(6.&20.))(1?.Vsegs,R6.)(20.(6.&20.)R2.))P,(1.$21.(22.R3.)$23.)P,(1.(9.(6.&40.))(:.R5.)(=.(6.&40.)))P,(64.(1.(6.&40.)(27.R:.(28.&5.+11.$29.))(43.&40.+5>.))(1.(6.&40.)(27.R:.(28.&5.+11.$29.))(43.&40.+5=.)))P,(1.(6.&40.)(27.R;.(28.&5.+:.$29.))R5.)(19.Vsegs,(14.(24.$25.R<.R;.R:.R9.)R8.)(65.(66.&40.R6.(43.&40.+??.))(5<.R8.)))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom mo w code HF HE Hh H17 H10.
  eapply rz_sysA; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srzJ_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

#[using="Type"] Lemma rz_exit_at_litA : ltac2:(CDefT.buildp (gd_tbl_NodesA ()) "Pregs,(1>.&5.(6.&40.))Ppc,(6.&40.)Pmem,P,(6.&40.)(9.(6.&8.))Prom,P,(6.&40.)(9.(6.&8.))Pmo,$<.Pw,(6.&20.)Pcode,$51.P,(1.(9.(6.&20.))(1?.Vsegs,R6.)(20.(6.&20.)R2.))P,(1.$21.(22.R3.)$23.)P,(1.(9.(6.&40.))(:.R5.)(=.(6.&40.)))P,(64.(1.(6.&40.)(27.R:.(28.&5.+11.$29.))(43.&40.+5>.))(1.(6.&40.)(27.R:.(28.&5.+11.$29.))(43.&40.+5=.)))P,(1.(6.&40.)(27.R;.(28.&5.+:.$29.))(43.&40.R5.))P,(0.(53.=R6.)(44.R6.+100.))(19.Vsegs,(14.(24.$25.R=.R<.R;.R:.)R9.)(65.(43.&40.R7.)(5<.R9.)))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom mo w code HF HE Hh H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_atA; eassumption.
Qed.

End KForm.
End WithSegs.

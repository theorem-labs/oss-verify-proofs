(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg SpinAlgB Nodes StoreOk AgentLib AgentNodes RefNodes
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanCeil.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanNodesLibE () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckOk"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckUnmodeled"; "OSSVerify.KrLib.ABoot.AsanAcct.node_ok"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.ShapeAlg.realizes"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "asanreflect_fx"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "OSSVerify.KrLib.ABoot.AgentNodes.epend"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "OSSVerify.KrLib.ABoot.MmapSim.unfill"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_model"; "Corelib.Init.Specif.sig"; "OSSVerify.KrLib.ABoot.AllocSim.brk_resolution_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Specif.proj1_sig"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_zeros"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_unmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "OSSVerify.KrLib.ABoot.AllocSim.brk_model"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok"; "OSSVerify.KrLib.ABoot.MmapSim.zfill"; "LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt2"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.State.m_tid"; "OSSVerify.KrLib.ABoot.RefNodes.tid_I"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE"; "LinuxProcessSemantics.LinuxProcessSem.State.with_tid"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_exit"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_flags_core"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noaccess_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_noaccess_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_b"; "OSSVerify.KrLib.ABoot.RefNodes.three"; "OSSVerify.KrLib.ABoot.RefNodes.T1"; "OSSVerify.KrLib.ABoot.RefNodes.T2"; "OSSVerify.KrLib.ABoot.RefNodes.T3"; "OSSVerify.KrLib.ABoot.RefNodes.t_alt3"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_ecall_at"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.pc"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.two64"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cs_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.refuse"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.ENOMEM_RET"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Noacc.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma sstep_of_check_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Peff,$3.Pm',$1.Pevs,(4.$5.)P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R7.)(;.(2.&40.)R5.))P,(6.$<.(=.(>.Vsegs,R8.R6.)R5.R7.)(?.R4.R3.))P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(4.(10.(2.&40.)$11.))(12.R7.)(13.(10.(2.&40.)$11.)))(14.Vsegs,(15.R;.R:.)R6.(16.(15.(17.(18.R;.R8.))R7.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hacc.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

#[using="Type"] Lemma node_chk_ev_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)PI,StPeffs,P,R1.$3.Pms',P,R2.$1.Pevs,P,R3.(4.$5.)P,(6.(7.(2.&40.))(8.R6.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R8.)(;.(2.&40.)R6.))P,Pi,R6.(6.$<.(=.(>.Vsegs,R:.R8.)A1.R6.R1.R9.)(?.A1.R5.R1.A1.R4.R1.))P,Peff,$3.Pm',$1.Pev,(4.$5.)P,(6.$<.(=.(>.Vsegs,R=.R;.)R3.R<.)(?.R2.R1.))(19.R;.Li,R;.(1:.(6.$3.R5.A1.R;.R1.)(1:.(6.$1.R4.A1.R:.R1.)(6.(4.$5.)R3.A1.R9.R1.))))P,Peff,$3.(1;.(6.$<.(=.(>.Vsegs,R<.R:.)R1.R;.)$1<.))P,Pi,R9.(6.(7.(2.&40.))(8.A1.R8.R1.)(9.(2.&40.)))P,Pi,R:.(6.(4.(10.(2.&40.)$11.))(12.A1.R:.R1.)(13.(10.(2.&40.)$11.)))(1=.Vsegs,(15.R>.R=.)R;.R8.Li,R;.(15.(17.(18.R?.A1.R;.R1.))A1.R:.R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hacc. split.
  - intros i. apply (sstep_of_check_noacc ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

#[using="Type"] Lemma node_chk_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)PI,StPeffs,P,R1.$3.Pms',P,R2.$1.P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R7.)(;.(2.&40.)R5.))P,Pi,R5.(6.$<.(=.(>.Vsegs,R9.R7.)A1.R5.R1.R8.)(?.A1.R4.R1.(13.$5.)))P,Peff,$3.Pm',$1.Pevs,(4.$5.)P,(6.$<.(=.(>.Vsegs,R<.R:.)R3.R;.)(?.R2.R1.))(19.R:.Li,R:.(1:.(6.$3.R5.A1.R:.R1.)(1:.(6.$1.R4.A1.R9.R1.)(6.(4.$5.)R3.(13.$5.)))))P,Peff,$3.(1;.(6.$<.(=.(>.Vsegs,R;.R9.)R1.R:.)$1<.))P,Pi,R8.(6.(7.(2.&40.))(8.A1.R7.R1.)(9.(2.&40.)))P,Pi,R9.(6.(4.(10.(2.&40.)$11.))(12.A1.R9.R1.)(13.(10.(2.&40.)$11.)))(1=.Vsegs,(15.R=.R<.)R:.L,R:.(13.$5.)Li,R:.(15.(17.(18.R>.A1.R:.R1.))A1.R9.R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hacc.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

#[using="Type"] Lemma node_det_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Peff0,$3.Pm0,$1.Pevs0,(4.$5.)P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R7.)(;.(2.&40.)R5.))P,Peff,$3.Pm',$1.Pevs,(4.$5.)(1>.(6.$<.(=.(>.Vsegs,R;.R9.)R3.R:.)(?.R2.R1.))(1:.(6.$3.R3.R8.)(1:.(6.$1.R2.R7.)(6.(4.$5.)R1.R6.))))P,Peff,$3.(1;.(6.$<.(=.(>.Vsegs,R:.R8.)R1.R9.)$1<.))P,(6.(7.(2.&40.))(8.R6.)(9.(2.&40.)))P,(6.(4.(10.(2.&40.)$11.))(12.R8.)(13.(10.(2.&40.)$11.)))(1=.Vsegs,(15.R<.R;.)$1?.L,$1?.R8.L,$1?.(15.(17.(18.R=.R:.))R9.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hacc.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hacc.
Qed.

#[using="Type"] Lemma rz_det_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Peff0,$3.Pm0,$1.PT,$20.P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R7.)(;.(2.&40.)R5.))P,Peff,$3.Pm',$1.Pevs,(4.$5.)(1>.(6.$<.(=.(>.Vsegs,R;.R9.)R3.R:.)(?.R2.R1.))(1:.(6.$3.R3.R8.)(1:.(6.$1.R2.R7.)(6.(4.$5.)R1.(13.$5.)))))P,Peff,$3.(1;.(6.$<.(=.(>.Vsegs,R:.R8.)R1.R9.)$1<.))P,(6.(7.(2.&40.))(8.R6.)(9.(2.&40.)))P,(6.(4.(10.(2.&40.)$11.))(12.R8.)(13.(10.(2.&40.)$11.)))P,(21.Vsegs,(15.(17.(18.R<.R9.))R8.)R7.)(21.Vsegs,(15.R=.R<.)R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply rz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma srz_det_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Peff0,$3.Pm0,$1.PT,$20.P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R7.)(;.(2.&40.)R5.))P,Peff,$3.Pm',$1.Pevs,(4.$5.)(1>.(6.$<.(=.(>.Vsegs,R;.R9.)R3.R:.)(?.R2.R1.))(1:.(6.$3.R3.R8.)(1:.(6.$1.R2.R7.)(6.(4.$5.)R1.(13.$5.)))))P,Peff,$3.(1;.(6.$<.(=.(>.Vsegs,R:.R8.)R1.R9.)$1<.))P,(6.(7.(2.&40.))(8.R6.)(9.(2.&40.)))P,(6.(4.(10.(2.&40.)$11.))(12.R8.)(13.(10.(2.&40.)$11.)))P,(22.Vsegs,(15.(17.(18.R<.R9.))R8.)R7.)(22.Vsegs,(15.R=.R<.)R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_cases : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pc,$23.PI,StPnx,P,R1.$23.PT,P,R2.$20.Pi0,R3.P,(1=.Vsegs,R5.R4.L,R4.(13.$5.)R3.)P,Pi,R5.(22.Vsegs,A1.R5.R1.A1.R4.R1.)(22.Vsegs,R7.(24.R6.R4.))")
(* [comment removed for export] *).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma with_vm_backing_halted : forall l p m, m_halted (with_vm_backing l p m) = m_halted m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma vm_add_lazy_halted : forall a n m, m_halted (vm_add_lazy a n m) = m_halted m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

#[using="Type"] Lemma with_mmap_replacement_halted : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement. rewrite with_mmap_backing_halted.
  apply vm_forget_range_halted.
Qed.

#[using="Type"] Lemma with_mmap_destroyed_halted : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. unfold with_mmap_destroyed. rewrite vm_forget_range_halted. apply with_vmmaps_halted. Qed.

#[using="Type"] Lemma forget_vm_ranges_halted : forall ranges m,
  m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
  induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.

#[using="Type"] Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
  intros. unfold brk_model, with_brk_next. cbv zeta.
  rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma stepacc_ecall_epend : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pw,(2.&20.)P,(6.(7.(2.&20.))(26.Vsegs,R4.)(;.(2.&20.)R1.))P,(6.$27.(28.R2.)$29.)(6.(2:.(2;.$0.))(2<.Vsegs,(2=.$2>.R7.R6.R5.R4.))(2?.(2;.$0.)(30.$0.(31.R7.R6.R5.R4.(32.R7.(33.&5.+11.$34.)))(13.$35.))))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Pms',$0.P,(6.(7.(2.&40.))(8.R2.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R4.)(9.(2.&40.)))P,(6.(2:.(2;.$0.))(2<.Vsegs,R5.)(2?.(2;.$0.)(30.$0.R3.(13.$35.))))(1=.Vsegs,(15.R6.R5.)$1?.L,$1?.(13.$5.)L,$1?.(15.R5.R6.))")
(* [comment removed for export] *).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

#[using="Type"] Lemma rz_sys_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.Pw,(2.&20.)PT,$20.P,(6.(7.(2.&40.))(8.R3.)(9.(2.&40.)))P,(6.(7.(2.&20.))(26.Vsegs,R7.)(;.(2.&20.)R3.))P,(6.$27.(28.R4.)$29.)P,(21.Vsegs,(15.(31.R:.R9.R8.R7.(32.R:.(33.&5.+11.$34.)))R6.)R4.)(21.Vsegs,(15.(2=.$2>.R;.R:.R9.R8.)R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply rz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma epend_len : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Plen,$36.P,(6.(2.&40.)(32.R5.(33.&5.+;.$34.))(37.&40.R1.))P,(1:.(38.=R2.)(38.R2.(39.+2.+40.)))(1:.(6.$36.(3:.&40.(3;.(31.R7.R6.R5.R4.(32.R7.(33.&5.+11.$34.)))#1.))R3.)(1;.(6.(2.&40.)(3;.(31.R7.R6.R5.R4.(32.R7.(33.&5.+11.$34.)))#1.)(37.&40.=))))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srz_sys_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.Pw,(2.&20.)PT,$20.P,(6.(7.(2.&40.))(8.R3.)(9.(2.&40.)))P,(6.(7.(2.&20.))(26.Vsegs,R7.)(;.(2.&20.)R3.))P,(6.$27.(28.R4.)$29.)P,(22.Vsegs,(15.(31.R:.R9.R8.R7.(32.R:.(33.&5.+11.$34.)))R6.)R4.)(22.Vsegs,(15.(2=.$2>.R;.R:.R9.R8.)R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma srz_munmap_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.Pw,(2.&20.)Pa,(2.&40.)Plen,$36.PK,$20.P,(6.(7.(2.&20.))(26.Vsegs,R8.)(;.(2.&20.)R4.))P,(6.$27.(28.R5.)$29.)P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)))P,(6.(2.&40.)(32.R<.(33.&5.+11.$34.))(37.&40.+=7.))P,(6.(2.&40.)(32.R=.(33.&5.+:.$34.))R7.)P,(6.$36.(3<.(3:.&40.R8.)$3=.)=)P,(6.(2.&40.)(32.R?.(33.&5.+;.$34.))(37.&40.R8.))P,(38.=R9.)P,(3>.(3?.(3:.&40.R;.)(40.R:.))$41.)P,(6.$27.(42.(43.(44.R>.))R<.(37.&40.(40.R;.)))$29.)P,(22.Vsegs,(15.(2=.$2>.(45.R13.(33.&5.+:.$34.)(37.&40.=))(46.R12.+4.)(47.R=.(37.&40.(40.R<.))R11.)R10.)(48.R=.(37.&40.(40.R<.))R?.))R;.)(22.Vsegs,(15.(2=.$2>.R14.R13.R12.R11.)R10.)R<.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) model eff Hno) (munmap_check_modeled ms model eff Hargs)) as Hchk.
  rewrite H0, Hpr in Hchk.
  eapply (srz_det_noacc ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
    [exact Hh | reflexivity | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z len))]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
    + intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
  - rewrite munmap_model_halted. exact Hh.
  - unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma node_brk_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)P,(6.(7.(2.&40.))(8.R2.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R4.)(;.(2.&40.)R2.))P,(6.$36.(3:.&40.R3.)+=6.)(1=.Vsegs,(15.R6.R5.)(49.(2.&40.)Lr,(2.&40.)(4:.R6.(3;.R7.#0.)R1.))L,(49.(2.&40.)Lr,(2.&40.)(4:.R6.(3;.R7.#0.)R1.))(13.$5.)Li,(49.(2.&40.)Lr,(2.&40.)(4:.R6.(3;.R7.#0.)R1.))(15.(17.(18.R7.(4;.(4<.(2.&40.)Lr,(2.&40.)(4:.R7.(3;.R8.#0.)R1.)R1.)(13.(10.(2.&40.)(4.(2.&8.))))(4=.(3;.R7.#0.)(4<.(2.&40.)Lr,(2.&40.)(4:.R7.(3;.R8.#0.)R1.)R1.)(4>.(44.R6.)))(4?.(4<.(2.&40.)Lr,(2.&40.)(4:.R7.(3;.R8.#0.)R1.)R1.)(4>.(44.R6.)))(13.$50.)(13.(10.(2.&40.)$11.)))))(51.(3;.R7.#0.)(4<.(2.&40.)Lr,(2.&40.)(4:.R7.(3;.R8.#0.)R1.)R1.)R6.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hsvc Hno.
  apply (node_chk_noacc ms model x8 {r : word | brk_resolution_ok model (ms_gpr ms 0) r}
           (fun i => mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
  - intros [r Hr]. cbn [proj1_sig]. apply check_syscall_ok_iff.
    exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros eff m' evs Hc. apply check_syscall_ok_iff in Hc.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & Hok & ->).
    exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. rewrite <- Heff. repeat split; reflexivity.
  - intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
    exact (proj1 (check_syscall_err_iff _ _ _) Hc).
  - intros [r Hr]. cbn [proj1_sig]. rewrite brk_model_halted. exact Hh.
  - intros [r Hr]. reflexivity.
Qed.

#[using="Type"] Lemma srz_brk_query_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.Pw,(2.&20.)PK,$20.P,(6.(7.(2.&20.))(26.Vsegs,R6.)(;.(2.&20.)R2.))P,(6.$27.(28.R3.)$29.)P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(2.&40.)(32.R:.(33.&5.+11.$34.))(37.&40.+=6.))P,(6.(2.&40.)(32.R;.(33.&5.+:.$34.))(37.&40.=))P,(22.Vsegs,(15.(2=.$2>.(45.R<.(33.&5.+:.$34.)(4>.(44.R8.)))(46.R;.+4.)R:.R9.)R8.)R6.)(22.Vsegs,(15.(2=.$2>.R=.R<.R;.R:.)R9.)R7.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply srz_cases; [exact (exist _ _ Hq) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

#[using="Type"] Lemma srz_brk_grow_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.Pw,(2.&20.)Pd,$36.PKA,$20.PKB,$20.P,(6.(7.(2.&20.))(26.Vsegs,R8.)(;.(2.&20.)R4.))P,(6.$27.(28.R5.)$29.)P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)))P,(6.(2.&40.)(32.R<.(33.&5.+11.$34.))(37.&40.+=6.))Zh,$52.(44.R9.)Zb,(2.&40.)(4>.R1.)P,(6.$36.(3<.(3:.&40.R1.)$3=.)=)P,(6.$36.(3<.R:.$3=.)=)P,(38.=R;.)P,(38.=(3:.&40.R4.))P,(38.(3?.(3:.&40.R5.)R=.)(39.+2.+40.))P,(3>.(3:.&40.(53.R7.))(3?.(3:.&40.R6.)R>.))P,(6.(2.&40.)(32.R15.(33.&5.+:.$34.))(37.&40.(3?.(3:.&40.R7.)R?.)))P,(6.$27.(54.R12.(37.&40.(3?.(3:.&40.R8.)R10.))(37.&40.(3?.(3:.&40.R8.)R10.)))$29.)P,(22.Vsegs,(15.(2=.$2>.(45.R17.(33.&5.+:.$34.)R9.)(46.R16.+4.)R15.R14.)R13.)R10.)P,(22.Vsegs,(15.(2=.$2>.(45.R18.(33.&5.+:.$34.)(37.&40.(3?.(3:.&40.R:.)R12.)))(46.R17.+4.)(55.R:.(37.&40.R12.)R16.)R15.)(56.(57.(58.R;.)(59.(10.(2.&40.)(2.&40.))(5:.(2.&40.)(2.&40.)R:.(37.&40.R12.))(43.R;.))(5;.R;.)(53.R;.)(37.&40.(3?.(3:.&40.R:.)R12.))(5<.R;.)(5=.R;.)(5>.R;.))R14.))R10.)(22.Vsegs,(15.(2=.$2>.R19.R18.R17.R16.)R15.)(5?.R12.R11.))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w d KA KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; left; reflexivity).
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  apply (srz_conseq segs _ (t_alt (fun i : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} =>
                               if bv_eqb (proj1_sig i) b then KA else KB))).
  2:{ intros tr. unfold t_alt2, t_alt. split.
      - intros [[r Hr] Ht]. cbn [proj1_sig] in Ht. destruct (bv_eqb r b); tauto.
      - intros [Ht | Ht].
        + exists (exist _ b Hkeep). cbn [proj1_sig]. rewrite bv_eqb_refl. exact Ht.
        + exists (exist _ req Hgrow). cbn [proj1_sig]. rewrite (bv_eqb_neq _ _ Hneq). exact Ht. }
  eapply srz_cases; [exact (exist _ b Hkeep) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
  - rewrite bv_eqb_refl. fold b. rewrite brk_zeros_keep, brk_unmaps_keep.
    unfold b, h. rewrite brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact HA.
  - rewrite (bv_eqb_neq _ _ Hneq).
    assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    assert (Hreq0 : req <> Z_to_bv 64 0).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

#[using="Type"] Lemma srz_brk_grow_blocked_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.Pw,(2.&20.)Preq,(2.&40.)PKA,$20.P,(6.(7.(2.&20.))(26.Vsegs,R7.)(;.(2.&20.)R3.))P,(6.$27.(28.R4.)$29.)P,(6.(7.(2.&40.))(8.R6.)(9.(2.&40.)))P,(6.(2.&40.)(32.R;.(33.&5.+11.$34.))(37.&40.+=6.))Zh,$52.(44.R8.)Zb,(2.&40.)(4>.R1.)P,(6.(2.&40.)(32.R>.(33.&5.+:.$34.))R8.)P,(38.=(3:.&40.R9.))P,(3>.(3:.&40.(53.R4.))(3:.&40.R:.))P,(3>.(3:.&40.R4.)(3:.&40.R;.))P,(6.$27.(54.R>.R<.R<.)$60.)P,(22.Vsegs,(15.(2=.$2>.(45.R13.(33.&5.+:.$34.)R6.)(46.R12.+4.)R11.R10.)R?.)R<.)(22.Vsegs,(15.(2=.$2>.R14.R13.R12.R11.)R10.)R=.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply srz_cases; [exact (exist _ b Hkeep) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma node_set_tid_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)P,(6.(7.(2.&40.))(8.R2.)(9.(2.&40.)))P,(6.(7.(2.&40.))(:.R4.)(;.(2.&40.)R2.))P,(6.$36.(3:.&40.R3.)+60.)P,(6.(7.(2.&40.))(61.R5.)(9.(2.&40.)))(1=.Vsegs,(15.R7.R6.)$62.L,$62.(13.$5.)Li,$62.(15.(17.(18.R8.(4;.(4<.(2.&40.)Lt,(2.&40.)(1:.(38.=(3:.&40.R1.))(38.(3:.&40.R1.)$63.))R1.)(13.(10.(2.&40.)(4.(2.&8.))))(13.(10.(2.&40.)(2.&40.)))(13.(10.(2.&40.)(2.&40.)))(13.$50.)(13.(10.(2.&40.)$11.)))))(64.(4<.(2.&40.)Lt,(2.&40.)(1:.(38.=(3:.&40.R1.))(38.(3:.&40.R1.)$63.))R1.)R7.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  apply (node_chk_noacc ms model x8 tid_I
           (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
           (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
  - intros [t [Ht1 Ht2]]. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
  - intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
  - intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
  - intros [t Ht]. reflexivity.
Qed.

#[using="Type"] Lemma srz_set_tid_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.PK,$20.Pw,(2.&20.)P,(6.(7.(2.&20.))(26.Vsegs,R6.)(;.(2.&20.)R1.))P,(6.$27.(28.R2.)$29.)P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(6.(2.&40.)(32.R:.(33.&5.+11.$34.))(37.&40.+60.))P,(6.(7.(2.&40.))(61.R7.)(9.(2.&40.)))P,Ptid,(2.&40.)P,(1:.(38.=(3:.&40.R1.))(38.(3:.&40.R1.)$63.))(22.Vsegs,(15.(2=.$2>.(45.R>.(33.&5.+:.$34.)R2.)(46.R=.+4.)R<.R;.)(64.R2.R:.))R9.)(22.Vsegs,(15.(2=.$2>.R=.R<.R;.R:.)R9.)R8.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig].
  change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
  rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_exit_at_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pregs,(25.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pmodel,$1.Pw,(2.&20.)Pcode,(2.&40.)P,(6.(7.(2.&20.))(26.Vsegs,R6.)(;.(2.&20.)R2.))P,(6.$27.(28.R3.)$29.)P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)))P,(65.(6.(2.&40.)(32.R:.(33.&5.+11.$34.))(37.&40.+5>.))(6.(2.&40.)(32.R:.(33.&5.+11.$34.))(37.&40.+5=.)))P,(6.(2.&40.)(32.R;.(33.&5.+:.$34.))R5.)(22.Vsegs,(15.(2=.$2>.R<.R;.R:.R9.)R8.)(66.(67.&40.R6.(37.&40.+??.))(68.R8.)))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma mmap_gates_core50 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pflags,(2.&40.)Pprot,(2.&40.)P,(6.$36.(69.R2.)+32.)(1:.(6.$27.(6:.R2.R3.(37.&40.=))$60.)(1:.(6.$27.(6;.R2.R3.(37.&40.=))$60.)(1:.(6.$27.(6<.(37.&40.=)R3.(37.&40.=))$29.)(1:.(6.$27.(6<.(37.&40.+3.)R3.(37.&40.=))$60.)(6.$27.(6=.(37.&40.+3.)R3.(37.&40.=))$29.)))))")
(* [comment removed for export] *).
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma srz_alt3 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pc,$23.Pnx,P,$6>.$23.PA,$20.PB,$20.PC,$20.P,(1=.Vsegs,R5.$6>.L,$6>.(13.$5.)R4.)P,(22.Vsegs,A1.R5.$6?.R4.)P,(22.Vsegs,A1.R6.$70.R4.)P,(22.Vsegs,A1.R7.$71.R4.)(22.Vsegs,R9.(72.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (srz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (srz_cases c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_alt2b : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pc,$23.Pnx,P,$27.$23.PA,$20.PB,$20.P,(1=.Vsegs,R4.$27.L,$27.(13.$5.)R3.)P,(22.Vsegs,A1.R4.$29.R3.)P,(22.Vsegs,A1.R5.$60.R3.)(22.Vsegs,R7.(5?.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros c nx A B Hnode HA HB.
  apply (srz_conseq segs c (t_alt (fun i : bool => if i then A else B))).
  - apply (srz_cases c bool nx _ true Hnode). intros [|]; assumption.
  - intros tr. unfold t_alt2, t_alt. split.
    + intros [[|] H]; tauto.
    + intros [H | H]; [exists true | exists false]; exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_alt3_sp : forall ms model x8 (nx : three -> config) (A B C : TSet),
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  node_ok segs (mkCfg ms model) three (fun _ => []) nx ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx T1)) 0) = true ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx T2)) 0) = false ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx T3)) 0) = true ->
  srealizes0 segs (nx T1) A -> srealizes segs (nx T2) B -> srealizes0 segs (nx T3) C ->
  srealizes segs (mkCfg ms model) (t_alt3 A B C).
Proof.
  intros ms model x8 nx A B C Hsvc Hoff Hnode Hr1 Hn2 Hr3 HA HB HC.
  assert (HA0 : A []) by (eapply srealizes0_nonempty; exact HA).
  assert (HB0 : B []) by (eapply srealizes_nonempty; exact HB).
  assert (HC0 : C []) by (eapply srealizes0_nonempty; exact HC).
  apply (srz_conseq segs (mkCfg ms model)
           (t_alt (fun i : three => t_emit [] (match i with T1 => A | T2 => B | T3 => C end)))).
  - apply (srz_node_sp_sys segs ms model x8 three nx (fun i => match i with T1 => A | T2 => B | T3 => C end)
             (fun i => match i with T2 => true | _ => false end) T2 Hsvc Hoff Hnode eq_refl Hn2).
    + intros [| |] H; try discriminate H. exact HB.
    + intros [| |] H; try discriminate H; split; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) H)
        | right; left; exact (proj1 (t_emit_nil_eq B HB0 tr) H)
        | right; right; exact (proj1 (t_emit_nil_eq C HC0 tr) H) ].
    + intros [H | [H | H]];
        [ exists T1; exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists T2; exact (proj2 (t_emit_nil_eq B HB0 tr) H)
        | exists T3; exact (proj2 (t_emit_nil_eq C HC0 tr) H) ].
Qed.

(* [comment removed for export] *)
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  if Z.eqb prot 0
  then mkVmMapsFull (vm_reserved h) (vm_maps h)
         ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps := ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "(57.(58.O1.)(73.(43.O1.)(3:.&40.O3.)(3?.(3:.&40.O3.)(3:.&40.O2.)))(73.(5;.O1.)(3:.&40.O3.)(3?.(3:.&40.O3.)(3:.&40.O2.)))(53.O1.)(4>.O1.)(5<.O1.)(5=.O1.)(5>.O1.))")
(* [comment removed for export] *).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

(* [comment removed for export] *)
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

#[using="Type"] Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
#[using="Type"] Lemma with_mmap_destroyed_halted' : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->      (* [comment removed for export] *)
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs us [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs, us with
             | [], [] => CheckOk model []
             | [], _ => if listNN_eqb us [(addr, n)]                 (* [comment removed for export] *)
                        then CheckOk (fixedin_destroyed_model addr n model) []
                        else CheckReject
             | _, _ => CheckReject
             end
        else if (Z.eqb prot 0)
             then match zs with
                  | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
             else match us with
                  | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Hce n Hrf Hmc Hbud.
  assert (Htop64 : (0 < page_round_up_Z len /\ bv_unsigned addr + page_round_up_Z len < 2 ^ 64 - 8388608)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). pose proof Hce as Hce'.
    unfold alloc_top, stack_max_size in Hce'. pose proof (u64_range (vm_init_sp (m_vmmaps model))). unfold page_size in *. lia. }
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). unfold page_size in *. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  - (* [comment removed for export] *)
    rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct zs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
    reflexivity.
  - (* [comment removed for export] *)
    rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    rewrite (Hbud eq_refl).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KA KB KC,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->      (* [comment removed for export] *)
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes0 segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->      (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes0 segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) (unfill addr n mem) rom)
                       (fixedin_destroyed_model addr n model)) KC ->                                               (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt3 KA KB KC).
Proof.
  intros regs pc mem rom model w prot flags addr len KA KB KC HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc Hbud HA HB HC.
  pose proof (u64_range addr) as Har.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof Hce as Hce'.
    unfold alloc_top, stack_max_size in Hce'. pose proof (u64_range (vm_init_sp (m_vmmaps model))). lia. }
  assert (Htop64 : (bv_unsigned addr + page_round_up_Z len < 2 ^ 64 - 8388608)%Z).
  { pose proof Hce as Hce'. unfold alloc_top, stack_max_size in Hce'. pose proof (u64_range (vm_init_sp (m_vmmaps model))). lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Hce Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
    pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  pose (effs := fun i : three => match i with
                           | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | T2 => fixedin_ok_eff prot addr n
                           | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : three => match i with
                          | T1 => model
                          | T2 => fixedin_ok_model prot flags addr n model
                          | T3 => fixedin_destroyed_model addr n model end).
  assert (Herr : forall e, In e mmap_errnos -> e = ENOMEM) by (intros e [<-|[]]; reflexivity).
  assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
  assert (Hrb : forall i, refusal_b (sys_input segs ms (getr regs 17)) model
                            (ms_gpr (cfg_ms (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) 0)
                          = errno_ret_in mmap_errnos (eff_ret (effs i))).
  { intros i. cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect.
    apply (refusal_b_mmap (sys_input segs ms (getr regs 17)) model). cbn [in_sysno sys_input]. exact Hno. }
  apply (srz_alt3_sp ms model (getr regs 17) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  - reflexivity.
  - apply (family_off_alloc (sys_input segs ms (getr regs 17))). cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity.
  - apply (node_chk_noacc ms model (getr regs 17) three effs ms' Hh eq_refl).
    + intros [| |]; cbn [effs ms'].
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk, Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (Herr e He).
        destruct zs; [|discriminate]. destruct us.
        -- injection Hc as <- <-. exists T1. repeat split; reflexivity.
        -- destruct (listNN_eqb (p :: us) [(addr, n)]) eqn:Hl; [|discriminate].
           apply listNN_eqb_eq in Hl. rewrite Hl. injection Hc as <- <-. exists T3. repeat split; reflexivity.
      * destruct (Z.eqb prot 0) eqn:Ep.
        -- destruct zs; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
        -- destruct us; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + intros [| |]; cbn [ms']; [exact Hh | unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh
                              | unfold fixedin_destroyed_model; rewrite with_mmap_destroyed_halted'; cbn; exact Hh].
    + intros [| |]; cbn [effs]; unfold fixedin_ok_eff; [reflexivity | destruct (Z.eqb prot 0); reflexivity | reflexivity].
  - rewrite (Hrb T1). cbn [effs eff_ret]. apply errno_ret_in_intro. exact ENOMEM_in_mmap_errnos.
  - rewrite (Hrb T2). cbn [effs]. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); cbn [eff_ret]; exact Haddr_ne.
  - rewrite (Hrb T3). cbn [effs eff_ret]. apply errno_ret_in_intro. exact ENOMEM_in_mmap_errnos.
  - cbn [effs ms']. unfold ms. rewrite adv_ret_epend. exact HA.
  - cbn [effs ms']. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
  - cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HC.
Qed.

End Noacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Import AX2 AX2S AP APS.

(* [comment removed for export] *)
Lemma is_ecall_at_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "PSEGS,(4.$74.)Pcs,$75.P,(6.$27.(76.R2.R1.)$29.)(1:.(3>.=(77.R2.))(1:.(38.(3?.(77.R2.)+4.)$78.)(19.(2.&20.)Lw,(2.&20.)(1:.(6.(7.(2.&20.))(26.R4.(37.&40.(77.R3.)))(;.(2.&20.)R1.))(6.$27.(28.R1.)$29.)))))")
(* [comment removed for export] *).
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  repeat split; try assumption. exists w. auto.
Qed.

Lemma bv_and_255 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "Pc0,$36.P,(1:.(3>.=R1.)(38.R1.$78.))(6.(2.&40.)(67.&40.(37.&40.R2.)(37.&40.+??.))(37.&40.(79.R2.+??.)))")
(* [comment removed for export] *).
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
  v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
  intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CsOk.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SP0 : Z.   (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SP0 SINV argH FS0).

(* [comment removed for export] *)
#[using="Type"] Lemma cs_ok_refuse : ltac2:(CDefT.buildp (gd_tbl_AsanNodesLibE ()) "PE,$7:.Pcs,$75.PR,(25.&5.(2.&40.))PFULL,P,(2.&40.)(7.(2.&8.))Pmodel,$1.P,(7;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R5.R4.R3.R2.R1.)(7;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R6.(7<.R5.)(45.R4.(33.&5.+:.$34.)(37.&40.$7=.))R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model HC.
  assert (HMr : Mr A SP0 argH E (refuse cs) model FULL = Mr A SP0 argH E cs model FULL) by reflexivity.
  assert (HA : allowA A E (refuse cs) = allowA A E cs) by reflexivity.
  destruct HC; constructor; unfold refuse, set_pc, set_reg, with_ss, mk_ss in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  apply regs_ok_set_n; [exact co_regs0 | lia | rewrite edenot_lit; reflexivity].
Qed.

#[using="Type"] Lemma pc_refuse : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.
#[using="Type"] Lemma nxt_refuse : forall cs, nxt (refuse cs) = nxt cs.
Proof. reflexivity. Qed.
End CsOk.

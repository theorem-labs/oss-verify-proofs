(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import CatSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanAcct SpinAlg.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanAcctShape () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.AsanAcct.lazy_cover"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "OSSVerify.KrLib.ABoot.AsanAcct.A_wf"; "OSSVerify.KrLib.ABoot.AsanAcct.MInv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.AsanAcct.restrict"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.KrLib.ABoot.AsanAcct.same_but_materialized"; "OSSVerify.KrLib.ABoot.ShapeAlg.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.ABoot.AsanAcct.unrestrict"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "OSSVerify.KrLib.ABoot.AsanAcct.hclean"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"].


Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Type"] Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.node_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr.

#[using="HH Hwx P_of P_of_silent1"] Theorem rz_step_restricted_T : ltac2:(CDefT.buildp (gd_tbl_AsanAcctShape ()) "PA,(0.(1.$2.$2.))Pms,$3.Pmsr',$3.Pmodel,$4.PT,$5.P,(6.VH,(7.R2.)R5.)P,(8.R6.)P,(9.R7.R4.)P,(:.(;.(<.&40.))(=.R5.)(>.(<.&40.)))P,(:.(;.(<.&40.))(?.R8.)(>.(<.&40.)))P,(:.(10.$3.)(11.Vsegs,(12.VH,R9.))(13.$3.R8.))P,Pmodel',$4.P,(9.R<.R1.)P,(14.R:.R2.)(15.Vsegs,(16.(17.VH,(18.R=.)R<.)R3.)R:.)(15.Vsegs,(16.R;.R9.)R8.)")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.

#[using="HH Hwx P_of P_of_silent1"] Theorem rz_msteps_restricted_T : ltac2:(CDefT.buildp (gd_tbl_AsanAcctShape ()) "PA,(0.(1.$2.$2.))Pms,$3.Pmsr',$3.Pmodel,$4.PT,$5.P,(6.VH,(7.R2.)R5.)P,(8.R6.)P,(9.R7.R4.)P,(:.(;.(<.&40.))(=.R5.)(>.(<.&40.)))P,(19.Vsegs,(12.VH,R8.)R7.)P,Pmodel',$4.P,(9.R;.R1.)P,(14.R9.R2.)P,(1:.VH,R;.)(15.Vsegs,(16.(17.VH,(18.R=.)R<.)R4.)R:.)(15.Vsegs,(16.R:.R8.)R7.)")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr.

#[using="HH Hwx SP_of SP_of_silent1"] Theorem srz_step_restricted_T : ltac2:(CDefT.buildp (gd_tbl_AsanAcctShape ()) "PA,(0.(1.$2.$2.))Pms,$3.Pmsr',$3.Pmodel,$4.PT,$5.P,(6.VH,(7.R2.)R5.)P,(8.R6.)P,(9.R7.R4.)P,(:.(;.(<.&40.))(=.R5.)(>.(<.&40.)))P,(:.(;.(<.&40.))(?.R8.)(>.(<.&40.)))P,(:.(10.$3.)(11.Vsegs,(12.VH,R9.))(13.$3.R8.))P,Pmodel',$4.P,(9.R<.R1.)P,(14.R:.R2.)(1;.Vsegs,(16.(17.VH,(18.R=.)R<.)R3.)R:.)(1;.Vsegs,(16.R;.R9.)R8.)")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.

#[using="HH Hwx SP_of SP_of_silent1"] Theorem srz_msteps_restricted_T : ltac2:(CDefT.buildp (gd_tbl_AsanAcctShape ()) "PA,(0.(1.$2.$2.))Pms,$3.Pmsr',$3.Pmodel,$4.PT,$5.P,(6.VH,(7.R2.)R5.)P,(8.R6.)P,(9.R7.R4.)P,(:.(;.(<.&40.))(=.R5.)(>.(<.&40.)))P,(19.Vsegs,(12.VH,R8.)R7.)P,Pmodel',$4.P,(9.R;.R1.)P,(14.R9.R2.)P,(1:.VH,R;.)(1;.Vsegs,(16.(17.VH,(18.R=.)R<.)R4.)R:.)(1;.Vsegs,(16.R:.R8.)R7.)")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
(* [comment removed for export] *)
Let SP0_of (T : TSet) : config -> Prop := fun c => srealizes0 segs c T.

Let SP0_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP0_of T c' -> SP0_of T c :=
  fun c c' Hn Hr => srz0_silent1 segs c c' T Hn Hr.

#[using="HH Hwx SP0_of SP0_of_silent1"] Theorem srz0_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes0 segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes0 segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (SP0_of T) (SP0_of_silent1 T) A ms msr' model).
Qed.

#[using="HH Hwx SP0_of SP0_of_silent1"] Theorem srz0_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes0 segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes0 segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP0_of T) (SP0_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.

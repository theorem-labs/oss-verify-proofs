(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanNodesIface () : Init.string Init.list := ["Corelib.Init.Logic.iff"; "Iface.OBL_mmap2"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cs_ok"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_ecall_at"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_mmap2"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.ABoot.AxSymRun3.env_agree"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.nxt"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cfg_of"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.pc"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt2"].


Section Iface.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SP0 : Z.   (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmap2 : Prop := mm2_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Definition OBL_mmapin : Prop := mm3_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 (node_mmapin A LIMIT false).   (* [comment removed for export] *)
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT SP0 SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
#[using="Type"] Lemma OBL_mmap2_unfold :   (* [comment removed for export] *)
  OBL_mmap2 <->
  forall cs csa csb E R FULL model TA TB,
    cs_ok SEGS A LIMIT SP0 SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap2 A nx0 LIMIT cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SP0 SINV argH FS0 E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes0 SEGS (cfg_of SEGS R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SP0 SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB).
Proof. unfold OBL_mmap2, mm2_stmt. tauto. Qed.
End Iface.

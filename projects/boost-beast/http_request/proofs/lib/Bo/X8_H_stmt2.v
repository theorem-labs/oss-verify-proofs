(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import XUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXRep_fields AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8Call X8SRKit XA_leaves AXFuzz_stmt X8_H_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Store.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Win.
Local Ltac stack0_via_aapp ::= stack0_via_aapp_fast.
Local Ltac aconst_via_aapp ::= aconst_via_aapp_fast.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit2.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 Set StepFast.sf_check := true.


Definition P_HZ_SH0     : Z := 0xa5140.   (* [comment removed for export] *)
Definition P_HZ_SH1     : Z := 0xa5164.   (* [comment removed for export] *)
Definition P_HZ_RET_SV1 : Z := 0xa51a8.   (* [comment removed for export] *)
Definition P_HZ_ECD     : Z := 0xa51c0.   (* [comment removed for export] *)
Definition P_HZ_RET_ECD : Z := 0xa51c8.   (* [comment removed for export] *)
Definition P_HZ_RET_DEL : Z := 0xa51ec.   (* [comment removed for export] *)
Definition P_HZ_RET_F5  : Z := 0xa522c.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_HZ_EXEC_CTX_DTOR : Z := 0xa6b34.

(* [comment removed for export] *)
Definition hz_sh3  : list cell := hz_sh 0xf8 0 0 0 0.
Definition hz_sh2a : list cell := hz_sh 0xf8 0 0 0xf8 0xf8.
Definition hz_sh2b : list cell := hz_sh 0xf8 0xf8 0xf8 0xf8 0xf8.

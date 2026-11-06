(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Image ZBridge SysStep Arr SFMisc.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocKit_B.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocModel_B.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocKit_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocModel_B.F_ntf_B. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_syscalls MallocRep F_malloc_free. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocTree. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocKit_B MallocModel_B. From Stdlib Require Lia. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition qa_facts (st : mstate) (sc : Z) (g : aptr) : Prop :=
  forall head, active st sc = Some head -> head <> g ->
    meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Definition qpath_st (st : mstate) (sc : Z) (g : aptr) : mstate :=
  if optr_eqb (active st sc) (Some g) then st else queue_st (LActive sc) g st.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.

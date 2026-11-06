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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_memcpy.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_memcpy.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_memcpy.F_memcpy_A OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_memcpy.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocKit_B MallocModel_B MallocKit_B3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocModel_B.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocKit_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocModel_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocKit_B3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocModel_B.F_ntf_B.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require Import F_am_A F_am_K.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition am_init_st (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.

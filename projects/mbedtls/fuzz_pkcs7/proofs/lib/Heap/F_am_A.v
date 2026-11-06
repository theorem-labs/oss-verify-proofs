(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_am_A () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.upd_meta"; "OSSVerify.KrLib.Heap.MallocModel_B.clr_links"; "OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.set_avail_meta"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.aadd"; "OSSVerify.KrLib.Heap.Malloc.META_SIZE"; "OSSVerify.KrLib.Heap.Malloc.set_avail_meta_count"].



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate := ltac2:(CDefT.buildp (gd_tbl_F_am_A ()) "(0.O2.$1.(2.Lc,$3.(4.(5.$6.(7.O2.$8.))(9.O1.R1.))O3.))")
(* [comment removed for export] *).


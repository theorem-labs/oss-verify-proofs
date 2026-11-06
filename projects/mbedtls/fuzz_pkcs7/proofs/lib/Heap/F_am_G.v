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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_am_A F_am_K F_am_C F_am_F.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_am_G () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.set_meta_alloc_shift"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.c_meta_alloc_shift"; "OSSVerify.KrLib.Heap.Malloc.set_avail_meta_area_count"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.set_avail_meta_areas"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"].



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mm_ok_st (st : mstate) (rid : N) (n : Z) : mstate := ltac2:(CDefT.buildp (gd_tbl_F_am_G ()) "(0.Lc,$1.(2.(3.(4.R1.)+1.)(5.(6.O1.+1.)(7.(8.(9.$:.$;.)(<.$:.$;.O2.+1000.))R1.)))O3.)")
(* [comment removed for export] *).


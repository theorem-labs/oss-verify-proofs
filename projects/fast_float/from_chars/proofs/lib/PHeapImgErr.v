(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from PHeapInst.v (ported there to the binaries of release 2026.10.0 and LPS 2afba80c): its errno-image lemma split out to bound the build's memory. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec StoreOk CatExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout MemSplit RefMemcpyLib FxLin FxMem.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefStartup RefStartupDefs PDrvData PDrvMain PHeapInit PHeapIGlue.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxMalloc MngRepr MngL4 MngL4I.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Open Scope Z_scope.

Local Ltac bvlit := vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).

Lemma errno_img_w : forallb (fun i => match wview PSEGS (fun _ => None) (wa (0x75b2c + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

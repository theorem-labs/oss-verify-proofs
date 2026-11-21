(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from PHeapInst.v (ported there to the binaries of release 2026.10.0 and LPS 2afba80c): its context-image lemmas split out to bound the build's memory. *)
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

(* This window is 928 bytes and the body is a read of the ELF image, so a single
   [vm_compute] over [seq 0 928] has the whole reduction live at once: measured at
   >= 33.96 GiB, monotonic and still climbing at t = 4149.82 s on one core
   (over this exact text, PHeapInst.v blob
   e41167fe216fd63650b715c9ab8694e8b75d4c79).  Two changes cut that peak, and both
   cut the same quantity -- how much of the reduction must be live at one moment:
     (1) the window is proved in two halves, each its own lemma and so its own VM
         heap, recombined below by [seq_app] and [forallb_app];
     (2) [vm_cast_no_check] runs the VM once, at [Qed].  [vm_compute. reflexivity.]
         runs it twice -- once in the tactic and again over the VMcast at [Qed] --
         and holds the tactic-time normal form alive in between.
   [ctx_img_zero]'s statement is unchanged, so [hi_ctx_zero] and every other
   consumer is untouched.  Measured in this shape at 4.22 GiB and 191 s
   (image 2c6b6db8). *)
Lemma ctx_img_zero_c0 : forallb (fun i => match bview PSEGS (fun _ => None) (0x95ed8 + Z.of_nat i) with Some 0 => true | _ => false end) (seq 0 464) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ctx_img_zero_c1 : forallb (fun i => match bview PSEGS (fun _ => None) (0x95ed8 + Z.of_nat i) with Some 0 => true | _ => false end) (seq 464 464) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ctx_img_zero : forallb (fun i => match bview PSEGS (fun _ => None) (0x95ed8 + Z.of_nat i) with Some 0 => true | _ => false end) (seq 0 928) = true.
Proof.
  change 928%nat with (464 + 464)%nat.
  rewrite (seq_app 464 464 0), forallb_app, ctx_img_zero_c0.
  cbn [Nat.add]. rewrite ctx_img_zero_c1. reflexivity.
Qed.

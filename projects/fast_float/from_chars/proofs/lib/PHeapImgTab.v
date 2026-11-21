(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from PHeapInst.v (ported there to the binaries of release 2026.10.0 and LPS 2afba80c): its table-image check split out to bound the build's memory. *)
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

(* [comment removed for export] *)
Definition opt_bytes_eqb (a b : option (list byte)) : bool :=
  match a, b with
  | Some x, Some y => (Nat.eqb (length x) (length y) && forallb (fun '(u, v) => bv_eqb u v) (combine x y))%bool
  | None, None => true
  | _, _ => false
  end.
Lemma opt_bytes_eqb_eq : forall a b, opt_bytes_eqb a b = true -> a = b.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity]. f_equal.
  apply andb_prop in H as [Hl Hc]. apply Nat.eqb_eq in Hl. revert y Hl Hc.
  induction x as [|u x IH]; intros [|v y] Hl Hc; cbn in *; try discriminate; [reflexivity|].
  apply andb_prop in Hc as [Huv Hc]. apply bv_eqb_eq in Huv. subst v. f_equal. apply IH; [lia | exact Hc].
Qed.

(* MEASURED CURE, 2026-11-07.  This file -- not [PHeapInst.v] and not
   [heapI_main] -- is what three builds died in.  The three
   builds each ran
   `dune build -j 1 .../PHeapInst.vo` and each was killed at its 48.00 GiB cap with
   `PHeapImgTab.{glob,vo}` as the LAST launched action; `PHeapInst.v` is named zero
   times in all three logs, so it never started.  Under `-j 1` with `--display short`
   each file's own output falls strictly between its launch line and the next, and in
   those logs PHeapImgCtx and PHeapImgErr both show their output before the next
   launch: they completed, and this file was the live process.
   The pathology is the one PHeapImgCtx.v already measured and cured for
   [ctx_img_zero]: `vm_compute. reflexivity.` runs the VM TWICE -- once in the tactic
   and again over the VMcast at [Qed] -- and holds the tactic-time normal form alive
   in between, while `vm_cast_no_check` runs it ONCE, at [Qed].  A conjunction under
   one `split; vm_compute; reflexivity` additionally keeps BOTH halves' reductions
   live at the same moment.  Each conjunct is therefore its own lemma, so it gets its
   own VM heap, and each runs the VM once.
   [tables_img_ok]'s STATEMENT below is unchanged to the character; the two lemmas
   state its conjuncts verbatim, so [split] leaves exactly these two goals. *)
Lemma tables_img_ok_sc :
  forallb (fun sc => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98984 + 2 * Z.of_nat sc)) 2)
                                   (Some (word_to_le_bytes 2 (wa (znth (Z.of_nat sc) size_classes))))) (seq 0 48) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma tables_img_ok_db :
  forallb (fun j => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (90368 + Z.of_nat j)) 1)
                                  (Some (word_to_le_bytes 1 (wa (znth (Z.of_nat j) debruijn))))) (seq 0 32) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma tables_img_ok :
  forallb (fun sc => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98984 + 2 * Z.of_nat sc)) 2)
                                   (Some (word_to_le_bytes 2 (wa (znth (Z.of_nat sc) size_classes))))) (seq 0 48) = true /\
  forallb (fun j => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (90368 + Z.of_nat j)) 1)
                                  (Some (word_to_le_bytes 1 (wa (znth (Z.of_nat j) debruijn))))) (seq 0 32) = true.
Proof. split; [exact tables_img_ok_sc | exact tables_img_ok_db]. Qed.

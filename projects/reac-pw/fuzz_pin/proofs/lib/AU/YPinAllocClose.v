(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PinAllocClose.v, in the form of reac-pw/fuzz_qdisc's
   lib/AU/YQdiscAllocClose.v (made from proofs/libreac/fuzz_knock/lib/AU/YKnockAllocClose.v at origin/ossv/recipes
   88154566652). The allocator and memcpy parts of reac-pw/fuzz_pin's asan-ubsan driver (fuzz_pin.asan-ubsan, sha256
   d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f), closed at that image's symbol table
   B := YD2l.TfibB: the slots H_ALLOC_MALLOC_U / H_ALLOC_FREE_U / H_RT_MEMCPY_U of lib/A/PinClose.v's Section
   asan_ubsan. Each is image B's core theorem at TfibB: YF0w.tfib_amalloc_realizes, YF0q.afree_realizes_closed and
   YD2m.tfib_AICPY, with TfibB's TfibSyms from YD2l.TfibB_pair and its hash field, which TfibB defines as tfib_dhash.
   As on image A, fuzz_pin's start-up depot holds traces (depot_has_trace = true) and its program allocates (one
   malloc(n + 1) and one free per call), so YF0w discharges the malloc proof's depot premise itself with
   YFem.tfib_depot_ok (no YD3j / kd_inst argument). lib/AU/YD2o.v passes these three lemmas to PinClose's Section
   asan_ubsan. Names pin_* -> pin_*_U, module paths A.Axyz -> AU.Yxyz.
   rule 24: proves no function (kind: assembly). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YF0m YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require YF0w YF0q YD2m.
Lemma pin_amalloc_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0w.tfib_amalloc_realizes fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma pin_afree_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0q.afree_realizes_closed fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma pin_aicpy_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (YD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB (proj2 TfibB_pair)). Qed.

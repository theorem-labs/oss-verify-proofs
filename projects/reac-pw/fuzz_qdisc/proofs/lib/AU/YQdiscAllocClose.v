(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QdiscAllocClose.v, made from proofs/libreac/fuzz_knock/lib/AU/
   YKnockAllocClose.v at origin/ossv/recipes 88154566652. The allocator and memcpy parts of fuzz_qdisc's asan-ubsan
   driver, closed at that image's symbol table B := YD2l.TfibB: the slots H_ALLOC_MALLOC_U / H_ALLOC_FREE_U /
   H_RT_MEMCPY_U of lib/A/QdiscClose.v's Section asan_ubsan. Each is the core's theorem at TfibB:
   YF0w.tfib_amalloc_realizes, YF0q.afree_realizes_closed and YD2m.tfib_AICPY, with TfibB's TfibSyms from
   YD2l.TfibB_pair and its hash field, which TfibB defines as tfib_dhash. fuzz_qdisc's start-up depot holds one trace
   (depot_has_trace = true), so, as on image A, YF0w discharges the malloc proof's depot premise itself with
   YFem.tfib_depot_ok (no YD3j / kd_inst argument). Names knock_* -> qdisc_*, module paths changed.
   rule 24: proves no function (kind: assembly). *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YF0m YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require YF0w YF0q YD2m.
Lemma qdisc_amalloc_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0w.tfib_amalloc_realizes fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma qdisc_afree_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0q.afree_realizes_closed fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma qdisc_aicpy_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (YD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB (proj2 TfibB_pair)). Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, for a Theorem Labs lane): the asan-ubsan twin of lib/A/KnockAllocClose.v.
   The allocator and memcpy parts of fuzz_knock's asan-ubsan driver, closed at that image's symbol table
   B := YD2l.TfibB: the slots H_ALLOC_MALLOC_U / H_ALLOC_FREE_U / H_RT_MEMCPY_U of lib/A/KnockClose.v. Each is the
   relocated core's theorem at TfibB: YF0w.tfib_amalloc_realizes, YF0q.afree_realizes_closed and YD2m.tfib_AICPY, with
   TfibB's TfibSyms from YD2l.TfibB_pair and its hash field, which TfibB defines as tfib_dhash (YD2l.v:35). YF0w
   discharges the malloc proof's StackDepotPut premise itself, with YD3j.tfib_depot_put_any at the kd_inst record.
   rule 24: proves no function (kind: assembly). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YF0m YD2l.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YF0w YF0q YD2m.
Lemma knock_amalloc_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0w.tfib_amalloc_realizes fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma knock_afree_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0q.afree_realizes_closed fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma knock_aicpy_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (YD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB (proj2 TfibB_pair)). Qed.

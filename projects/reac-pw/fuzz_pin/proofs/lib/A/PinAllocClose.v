(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (c-libc-fmt, for h-small-a9): the allocator and memcpy parts of fuzz_knock's ASan driver,
   closed at the image's symbol table B := AD2l.TfibB. They are the three driver assumptions AD1p.v / AD1q.v state as
   Section hypotheses AMALLOC / AFREE / AICPY, and the slots H_ALLOC_MALLOC / H_ALLOC_FREE / H_RT_MEMCPY of
   lib/A/KnockClose.v (h-small-a11's join). Each is the relocated core's theorem at TfibB: AF0w.tfib_amalloc_realizes,
   AF0q.afree_realizes_closed and AD2m.tfib_AICPY, with TfibB's TfibSyms from AD2l.TfibB_pair and its hash field, which
   TfibB defines as tfib_dhash (AD2l.v:34). AF0w discharges the malloc proof's StackDepotPut premise itself, with git-lead's
   AD3j.tfib_depot_put_any at AD3j's instantiation record kd_inst.
   rule 24: proves no function (kind: assembly). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/KnockAllocClose.v at origin/ossv/recipes 6ebe35ba632;
   taken for reac-pw/fuzz_pin image A: fuzz_pin's start-up depot holds traces (depot_has_trace = true) and its program
   allocates (one malloc(n + 1) and one free per call, n up to 64 MiB - 2, so the size-class path and the large mmap path
   of the malloc wrapper are both live). The AF0w / AF0q / AD2m / AD2l it closes over are therefore the depot-true texts
   of fuzz_scene's released tree (proofs/libreac/fuzz_scene/lib/A at 6ebe35ba632, relocated to fuzz_pin.asan): its AF0w
   discharges the malloc proof's depot premise itself with AFem.tfib_depot_ok (no AD3j / kd_inst argument), as
   fuzz_grant's lib/A/Prog/GrantLibXClosed.v:62-65 uses the same two theorems for its allocating program. The three
   lemmas below are the parts that lib/A/PinClose.v's Section asan takes as H_ALLOC_MALLOC / H_ALLOC_FREE / H_RT_MEMCPY
   and that the program walks take at their malloc / free / __asan_memcpy call sites; lib/A/AD2o.v passes them to both.
   Names knock_* -> pin_*, module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 AF0m AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require AF0w AF0q AD2m.
Lemma pin_amalloc_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0w.tfib_amalloc_realizes fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma pin_afree_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0q.afree_realizes_closed fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma pin_aicpy_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (AD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB (proj2 TfibB_pair)). Qed.

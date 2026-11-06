(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, for a Theorem Labs lane): the allocator and memcpy parts of fuzz_knock's ASan driver,
   closed at the image's symbol table B := AD2l.TfibB. They are the three driver assumptions AD1p.v / AD1q.v state as
   Section hypotheses AMALLOC / AFREE / AICPY, and the slots H_ALLOC_MALLOC / H_ALLOC_FREE / H_RT_MEMCPY of
   lib/A/KnockClose.v (a Theorem Labs lane's join). Each is the relocated core's theorem at TfibB: AF0w.tfib_amalloc_realizes,
   AF0q.afree_realizes_closed and AD2m.tfib_AICPY, with TfibB's TfibSyms from AD2l.TfibB_pair and its hash field, which
   TfibB defines as tfib_dhash (AD2l.v:34). AF0w discharges the malloc proof's StackDepotPut premise itself, with a Theorem Labs lane's
   AD3j.tfib_depot_put_any at AD3j's instantiation record kd_inst.
   rule 24: proves no function (kind: assembly). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require AF0w AF0q AD2m.
Lemma knock_amalloc_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0w.tfib_amalloc_realizes fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma knock_afree_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0q.afree_realizes_closed fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma knock_aicpy_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (AD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB (proj2 TfibB_pair)). Qed.

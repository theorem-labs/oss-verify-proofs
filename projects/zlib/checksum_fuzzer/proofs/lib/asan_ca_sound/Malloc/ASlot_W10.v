(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import MallocKit_A3 ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition ag_frame (sc : Z) (j : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (Z_to_bv 64 (sc * 2)); CB 40 j; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section AG1.
Variables (sc lo : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : ATOP <= lo.
End AG1.

Section EPI.
Variables (lo : Z).
Hypothesis CLO : ATOP <= lo.
End EPI.


End CANSEC1.

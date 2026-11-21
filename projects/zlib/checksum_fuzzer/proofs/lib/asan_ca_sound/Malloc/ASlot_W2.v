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
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import MallocKit_A2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Section CANSEC1. Context {rc : runConstT}.
Definition ta_frame (s1v s2v rav : word) (j0 j1 : list byte) : list cell :=
  [CB 64 j0; C8 s2v; C8 s1v; CB 8 j1; C8 rav].

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : ATOP <= lo.
End FIN.



End CANSEC1.

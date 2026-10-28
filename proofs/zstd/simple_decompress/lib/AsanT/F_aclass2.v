(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AModelFacts APrimFacts F_acache3.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma classblock2_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34198) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x340bc) fc None m (seg_rom bsegs)).
Proof.
  intros until size. intros SZ M8 RIMG. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 11 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).            (* [comment removed for export] *)
  do 14 zstep. setreg 11 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).   (* [comment removed for export] *)
  do 12 zstep. setreg 11 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).            (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; revert M8; revert SZ; clear; revert size;
          apply (range_bv_eq8 cb_fin class_id 513 65536); vm_compute; reflexivity).
  apply evtF_done. do 5 eexists. reflexivity.
Qed.
End CANSEC1.

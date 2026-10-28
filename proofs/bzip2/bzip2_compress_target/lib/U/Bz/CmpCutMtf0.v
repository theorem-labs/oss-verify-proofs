(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutMtf CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition S0_genMTF_spec (GMFACTS : est -> Prop) : Prop :=
  forall (Q : machine_state -> Prop) (cx : cctx) (g : eg) (e : est) (m : word -> option byte) (Jy : list byte)
         (ra sp gp tp t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  let E := c_E cx in let A1 := c_A1 cx in let A2 := c_A2 cx in let usp := bv_unsigned sp in
  let e' := gm_e e in
  ememN cx s0segs g e 0 m -> amem cx s0segs e m -> u8arr s0segs m (usp + 16) Jy -> Z.of_nat (length Jy) = 264 ->
  mem_inv s0segs m -> cctx_ok cx -> cctx_sep cx -> CEIL <= usp -> usp + 384 <= 18446744073709551616 ->
  GMFACTS e ->
  (forall m' (Jy' : list byte) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
     emem cx s0segs (g_mtf_on g) e' m' -> amem cx s0segs e' m' -> u8arr s0segs m' (usp + 16) Jy' -> Z.of_nat (length Jy') = 264 ->
     mem_inv s0segs m' -> munch (genMTF_W cx (usp + 16) (usp + 280)) m m' -> wmono s0segs m m' ->
     evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16a4c) fc None m' (seg_rom s0segs))) ->
  evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 256) t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 A1) (Z_to_bv 64 0)
                         (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                         (Z_to_bv 64 (E + 384)) (Z_to_bv 64 (18446744073709551615 - (E + 384)))
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x16640) fc None m (seg_rom s0segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.

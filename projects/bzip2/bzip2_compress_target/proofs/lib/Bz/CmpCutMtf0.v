(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem CmpCut.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCutMtf CmpCut0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition S0_genMTF_spec (GMFACTS : est -> Prop) : Prop :=
  forall (Q : machine_state -> Prop) (cx : cctx) (g : eg) (e : est) (m : word -> option byte) (Jy : list byte)
         (ra sp gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  let E := c_E cx in let A1 := c_A1 cx in let A2 := c_A2 cx in let usp := bv_unsigned sp in
  let e' := gm_e e in
  ememN cx s0segs g e 0 m -> amem cx s0segs e m -> u8arr s0segs m (usp + 616) Jy -> Z.of_nat (length Jy) = 256 ->
  mem_inv s0segs m -> cctx_ok cx -> cctx_sep cx -> CEIL <= usp -> usp + 1008 <= 18446744073709551616 ->
  GMFACTS e ->
  (forall m' (Jy' : list byte) (t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
     emem cx s0segs (g_mtf_on g) e' m' -> amem cx s0segs e' m' -> u8arr s0segs m' (usp + 616) Jy' -> Z.of_nat (length Jy') = 256 ->
     mem_inv s0segs m' -> munch (genMTF_W cx (usp + 616) (usp + 872)) m m' -> wmono s0segs m m' ->
     evt s0segs Q (MS (mkR (Z_to_bv 64 0x15bac) sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 672 + 4 * (e_nInUse e' + 1)))
                            (Z_to_bv 64 0) (Z_to_bv 64 3) a2 (Z_to_bv 64 (e_nMTF e')) a4 a5 a6 a7
                            (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 (E + 384)) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128))
                            s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15d90) fc None m' (seg_rom s0segs))) ->
  evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 0) a0 a1 (Z_to_bv 64 (E + 640)) a3 a4 a5 a6 a7
                         (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 (E + 384)) s5 (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128))
                         s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x15b68) fc None m (seg_rom s0segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.

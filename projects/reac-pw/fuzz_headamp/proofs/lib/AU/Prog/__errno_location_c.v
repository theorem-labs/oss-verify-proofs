(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Prog/__errno_location_c.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 1 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Prog/__errno_location_c.v of this library by derive_y.py b7b132fb12a7: module paths lib.A -> lib.AU, the image module Asan -> AsanUbsan and Img0 -> Img0U, addresses moved from fuzz_headamp's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Prog/__errno_location_c.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
Open Scope Z_scope.

Definition ERRNO_LOCATION : Z := 0x8c6e4.
Definition ERRNO_TP_OFF : Z := -164.

Definition __errno_location_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned tp + ERRNO_TP_OFF))
                                a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ERRNO_LOCATION) fc None m (seg_rom rsegs)).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_both_r0_1 : plan :=
  PRun [0x3f33c]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun [0x7fffc]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1 )))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_both_r1_2 : plan :=
  PRun [0x3f33c]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun [0x7fffc]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2 )))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_both : plan :=
  PBump 453
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030
  (startup2_plan_both_r0_1)
  (startup2_plan_both_r1_2)).

Definition startup2_plan_both_ranges : list (Z * nat) := [(0x31834, 20%nat); (0x31894, 8%nat); (0x3f204, 44%nat); (0x3f2d4, 60%nat); (0x3f434, 52%nat); (0x3f584, 36%nat); (0x3f624, 28%nat); (0x3f774, 4%nat); (0x3f894, 12%nat); (0x3fa54, 28%nat); (0x3fbb4, 32%nat); (0x3fcf4, 36%nat); (0x3fd94, 16%nat); (0x3fde4, 20%nat); (0x405f4, 20%nat); (0x40d44, 40%nat); (0x40e44, 36%nat); (0x40ee4, 16%nat); (0x40f54, 44%nat); (0x41224, 16%nat); (0x42594, 56%nat); (0x537c4, 32%nat); (0x53a04, 8%nat); (0x53a54, 16%nat); (0x53b44, 16%nat); (0x54944, 8%nat); (0x586e4, 8%nat); (0x598f4, 4%nat); (0x5a374, 52%nat); (0x5a4a4, 16%nat); (0x5bdf4, 12%nat); (0x5bfb4, 8%nat); (0x5bff4, 12%nat); (0x5c054, 8%nat); (0x5e1b4, 24%nat); (0x5e284, 12%nat); (0x60054, 12%nat); (0x638f4, 12%nat); (0x64154, 12%nat); (0x65844, 56%nat); (0x659c4, 8%nat); (0x65a14, 8%nat); (0x65d74, 56%nat); (0x66514, 20%nat); (0x66664, 16%nat); (0x6c1d4, 12%nat); (0x6c234, 4%nat); (0x6feb4, 68%nat); (0x6ffe4, 32%nat); (0x700e4, 8%nat); (0x709c4, 40%nat); (0x721d4, 20%nat); (0x724b4, 84%nat); (0x72654, 4%nat); (0x72684, 44%nat); (0x72754, 4%nat); (0x72c44, 28%nat); (0x72cc4, 60%nat); (0x72e34, 28%nat); (0x72ee4, 20%nat); (0x72f44, 12%nat); (0x734a4, 20%nat); (0x73514, 4%nat); (0x73584, 16%nat); (0x7fff4, 4%nat); (0x80834, 12%nat); (0x88c20, 12%nat); (0x88ce0, 8%nat); (0x93004, 64%nat); (0x948a4, 12%nat)]%Z.

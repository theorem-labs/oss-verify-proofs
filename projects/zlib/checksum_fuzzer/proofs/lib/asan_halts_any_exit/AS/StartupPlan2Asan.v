(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_r0_1 : plan :=
  PRun [0x3f3b4]
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
  (PRun []
  (PX XMemset []
  (PRun [0x80074]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1 )))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_r1_2 : plan :=
  PRun [0x3f3b4]
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
  (PRun []
  (PX XMemset []
  (PRun [0x80074]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2 )))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan : plan :=
  PBump 453
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030
  (startup2_plan_r0_1)
  (startup2_plan_r1_2)).

Definition startup2_plan_ranges : list (Z * nat) := [(0x318a8, 24%nat); (0x31918, 4%nat); (0x3f278, 44%nat); (0x3f348, 60%nat); (0x3f4a8, 52%nat); (0x3f5f8, 56%nat); (0x3f6e8, 8%nat); (0x3f7e8, 4%nat); (0x3f918, 8%nat); (0x3fac8, 28%nat); (0x3fc28, 36%nat); (0x3fd68, 36%nat); (0x3fe18, 12%nat); (0x3fe58, 20%nat); (0x40668, 24%nat); (0x40db8, 40%nat); (0x40ec8, 32%nat); (0x40f58, 16%nat); (0x40fc8, 44%nat); (0x41298, 16%nat); (0x42618, 52%nat); (0x53838, 32%nat); (0x53a78, 8%nat); (0x53ad8, 12%nat); (0x53bb8, 16%nat); (0x549b8, 8%nat); (0x58758, 8%nat); (0x59968, 4%nat); (0x5a3f8, 48%nat); (0x5a518, 16%nat); (0x5be68, 12%nat); (0x5c028, 8%nat); (0x5c068, 12%nat); (0x5c0c8, 8%nat); (0x5e228, 24%nat); (0x5e2f8, 12%nat); (0x600c8, 8%nat); (0x600f8, 4%nat); (0x63968, 12%nat); (0x641c8, 12%nat); (0x658b8, 60%nat); (0x65a38, 8%nat); (0x65a88, 8%nat); (0x65de8, 60%nat); (0x66598, 20%nat); (0x666e8, 12%nat); (0x6c248, 12%nat); (0x6c2a8, 4%nat); (0x6ff38, 64%nat); (0x70058, 32%nat); (0x70168, 4%nat); (0x70a38, 44%nat); (0x72248, 20%nat); (0x72528, 84%nat); (0x726c8, 8%nat); (0x726f8, 48%nat); (0x727c8, 4%nat); (0x72cc8, 12%nat); (0x72d08, 8%nat); (0x72d38, 60%nat); (0x72eb8, 28%nat); (0x72f58, 36%nat); (0x73518, 20%nat); (0x73588, 4%nat); (0x735f8, 16%nat); (0x80068, 4%nat); (0x808f8, 12%nat); (0x88ad8, 12%nat); (0x88b88, 8%nat); (0x92ebc, 64%nat); (0x9475c, 8%nat)]%Z.

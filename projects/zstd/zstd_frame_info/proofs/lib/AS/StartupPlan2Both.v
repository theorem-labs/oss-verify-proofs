(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_both_r0_1 : plan :=
  PRun [0x3e3f8] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PSpin (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PSpin (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PSpin (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [0x7f794] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 1 (* [comment removed for export] *))))))))))))))))))))))).

Definition startup2_plan_both_r1_2 : plan :=
  PRun [0x3e3f8] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PSpin (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PSpin (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PSpin (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [0x7f794] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 2 (* [comment removed for export] *))))))))))))))))))))))).

Definition startup2_plan_both : plan :=
  PBump 453 (* [comment removed for export] *)
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030 (* [comment removed for export] *)
  (startup2_plan_both_r0_1)
  (startup2_plan_both_r1_2)).

(* [comment removed for export] *)
Definition startup2_plan_both_ranges : list (Z * nat) := [(0x30028, 24%nat); (0x30098, 4%nat); (0x3e2c8, 40%nat); (0x3e388, 16%nat); (0x3e3d8, 40%nat); (0x3e4e8, 52%nat); (0x3e648, 52%nat); (0x3e728, 12%nat); (0x3e828, 4%nat); (0x3e958, 12%nat); (0x3eb08, 28%nat); (0x3ec98, 24%nat); (0x3edb8, 36%nat); (0x3ee58, 16%nat); (0x3eea8, 20%nat); (0x3f6a8, 24%nat); (0x3fdf8, 40%nat); (0x3ff08, 32%nat); (0x3ff98, 16%nat); (0x40008, 44%nat); (0x402d8, 16%nat); (0x41658, 52%nat); (0x52f58, 32%nat); (0x53198, 8%nat); (0x531f8, 12%nat); (0x532d8, 16%nat); (0x540d8, 8%nat); (0x57e78, 8%nat); (0x59088, 4%nat); (0x59b18, 48%nat); (0x59c38, 16%nat); (0x5b588, 12%nat); (0x5b748, 8%nat); (0x5b788, 12%nat); (0x5b7e8, 8%nat); (0x5d948, 24%nat); (0x5da18, 12%nat); (0x5f7e8, 8%nat); (0x5f818, 4%nat); (0x63088, 12%nat); (0x638e8, 12%nat); (0x64fd8, 60%nat); (0x65158, 8%nat); (0x651a8, 8%nat); (0x65508, 60%nat); (0x65cb8, 20%nat); (0x65e08, 12%nat); (0x6b968, 12%nat); (0x6b9c8, 4%nat); (0x6f658, 64%nat); (0x6f778, 32%nat); (0x6f888, 4%nat); (0x70158, 44%nat); (0x71968, 20%nat); (0x71c48, 84%nat); (0x71de8, 8%nat); (0x71e18, 48%nat); (0x71ee8, 4%nat); (0x723e8, 12%nat); (0x72428, 8%nat); (0x72458, 60%nat); (0x725d8, 28%nat); (0x72678, 36%nat); (0x72c38, 20%nat); (0x72ca8, 4%nat); (0x72d18, 16%nat); (0x7f788, 4%nat); (0x7fec8, 16%nat); (0x88358, 12%nat); (0x88418, 8%nat); (0x9273c, 40%nat); (0x9282c, 4%nat); (0x93fdc, 12%nat)]%Z.

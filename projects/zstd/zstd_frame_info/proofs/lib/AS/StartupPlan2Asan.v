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

Definition startup2_plan_r0_1 : plan :=
  PRun [0x3e3f4] (* [comment removed for export] *)
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
  (PRun [0x7f790] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 1 (* [comment removed for export] *))))))))))))))))))))))).

Definition startup2_plan_r1_2 : plan :=
  PRun [0x3e3f4] (* [comment removed for export] *)
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
  (PRun [0x7f790] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 2 (* [comment removed for export] *))))))))))))))))))))))).

Definition startup2_plan : plan :=
  PBump 453 (* [comment removed for export] *)
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030 (* [comment removed for export] *)
  (startup2_plan_r0_1)
  (startup2_plan_r1_2)).

(* [comment removed for export] *)
Definition startup2_plan_ranges : list (Z * nat) := [(0x30030, 20%nat); (0x30090, 8%nat); (0x3e2c0, 40%nat); (0x3e390, 60%nat); (0x3e4f0, 52%nat); (0x3e640, 36%nat); (0x3e6e0, 12%nat); (0x3e720, 12%nat); (0x3e820, 8%nat); (0x3e950, 12%nat); (0x3eb00, 28%nat); (0x3ec90, 24%nat); (0x3edb0, 36%nat); (0x3ee50, 16%nat); (0x3eea0, 20%nat); (0x3f6a0, 24%nat); (0x3fe00, 40%nat); (0x3ff00, 32%nat); (0x3ffa0, 16%nat); (0x40010, 20%nat); (0x40070, 16%nat); (0x402e0, 16%nat); (0x41650, 56%nat); (0x52f50, 32%nat); (0x531a0, 8%nat); (0x531f0, 12%nat); (0x532d0, 16%nat); (0x540d0, 8%nat); (0x57e70, 12%nat); (0x59080, 4%nat); (0x59b10, 48%nat); (0x59c30, 20%nat); (0x5b580, 12%nat); (0x5b750, 4%nat); (0x5b790, 12%nat); (0x5b7e0, 8%nat); (0x5d940, 28%nat); (0x5da10, 12%nat); (0x5f7e0, 8%nat); (0x5f810, 4%nat); (0x63080, 12%nat); (0x638e0, 16%nat); (0x64fd0, 60%nat); (0x65150, 8%nat); (0x651a0, 8%nat); (0x65510, 56%nat); (0x65cb0, 20%nat); (0x65e00, 12%nat); (0x6b960, 12%nat); (0x6b9c0, 4%nat); (0x6f650, 68%nat); (0x6f770, 16%nat); (0x6f7c0, 12%nat); (0x6f880, 4%nat); (0x70160, 40%nat); (0x71960, 20%nat); (0x71c50, 84%nat); (0x71de0, 8%nat); (0x71e20, 44%nat); (0x71ee0, 8%nat); (0x723e0, 24%nat); (0x72450, 60%nat); (0x725d0, 28%nat); (0x72670, 36%nat); (0x72c30, 20%nat); (0x72cb0, 4%nat); (0x72d10, 16%nat); (0x7f790, 4%nat); (0x7fec0, 16%nat); (0x88180, 12%nat); (0x88240, 4%nat); (0x92564, 40%nat); (0x92654, 4%nat); (0x93e04, 12%nat)]%Z.

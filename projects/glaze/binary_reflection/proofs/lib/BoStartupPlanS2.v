(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3B AzPlanCore AzPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3B AzPlanCore AzPlan.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition s2a_plan_r0_1 : plan :=
  PRun [] (* [comment removed for export] *)
  (PExt 200 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 200 [] (* [comment removed for export] *)
  (PRun [0xc5ca4] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 950 (* [comment removed for export] *))))))).

Definition s2a_plan : plan :=
  PBump 467 (* [comment removed for export] *)
  (s2a_plan_r0_1).

(* [comment removed for export] *)
Definition s2a_plan_ranges : list (Z * nat) := [(0x76388, 16%nat); (0x76588, 32%nat); (0x76908, 16%nat); (0x782c8, 48%nat); (0x7d788, 32%nat); (0x80988, 32%nat); (0x80a48, 64%nat); (0x85908, 48%nat); (0x85b48, 96%nat); (0x85dc8, 32%nat); (0x9cd50, 96%nat); (0xc5c8c, 16%nat)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From LinuxProcessSemantics.Riscv Require Import Instr.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3B AzPlanCore AzPlan.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AX2B.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import APC.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition s2b_plan_r0_1 : plan :=
  PRun [0x8fe98] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 951 (* [comment removed for export] *))).

Definition s2b_plan : plan :=
  PBump 510 (* [comment removed for export] *)
  (s2b_plan_r0_1).

(* [comment removed for export] *)
Definition s2b_plan_ranges : list (Z * nat) := [(0x59a9c, 80%nat); (0x5ae5c, 32%nat); (0x71488, 16%nat); (0x75708, 16%nat); (0x76908, 16%nat); (0x77388, 64%nat); (0x774c8, 16%nat); (0x78e08, 32%nat); (0x78fc8, 64%nat); (0x8fe44, 32%nat); (0x904c4, 80%nat); (0xc5c8c, 16%nat); (0xfdd00, 16%nat)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From LinuxProcessSemantics.Riscv Require Import Instr.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3B AzPlanCore AzPlan.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AX2B.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import APC.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition s2c_plan_r0_1 : plan :=
  PRun [0x59bcc] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PRun [] (* [comment removed for export] *)
  (PExt 202 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PRun [] (* [comment removed for export] *)
  (PExt 202 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 202 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [0x9d030] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 1 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))).

Definition s2c_plan_r1_2 : plan :=
  PRun [0x59bcc] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PRun [] (* [comment removed for export] *)
  (PExt 202 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PRun [] (* [comment removed for export] *)
  (PExt 202 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 202 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [0x9d030] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 2 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))).

Definition s2c_plan : plan :=
  PBump 517 (* [comment removed for export] *)
  (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 4030 (* [comment removed for export] *)
  (s2c_plan_r0_1)
  (s2c_plan_r1_2)).

(* [comment removed for export] *)
Definition s2c_plan_ranges : list (Z * nat) := [(0x4b35c, 48%nat); (0x59b9c, 48%nat); (0x59c9c, 64%nat); (0x59e1c, 80%nat); (0x59fdc, 16%nat); (0x5a11c, 16%nat); (0x5a2dc, 32%nat); (0x5a41c, 48%nat); (0x5a55c, 96%nat); (0x5ae9c, 16%nat); (0x5b59c, 64%nat); (0x5b6dc, 112%nat); (0x5ba9c, 32%nat); (0x5ce1c, 64%nat); (0x70048, 48%nat); (0x70288, 48%nat); (0x703c8, 32%nat); (0x75708, 16%nat); (0x774c8, 32%nat); (0x7b1c8, 32%nat); (0x7b288, 32%nat); (0x7c9c8, 32%nat); (0x7d088, 16%nat); (0x80908, 32%nat); (0x81188, 16%nat); (0x82848, 80%nat); (0x829c8, 48%nat); (0x82d88, 80%nat); (0x83548, 32%nat); (0x83688, 32%nat); (0x89208, 32%nat); (0x8cec4, 128%nat); (0x8d104, 16%nat); (0x8d9c4, 64%nat); (0x8f204, 32%nat); (0x8f4c4, 96%nat); (0x8f684, 80%nat); (0x8fc84, 96%nat); (0x8fe84, 80%nat); (0x9d010, 16%nat); (0xc5c8c, 32%nat); (0xed4cc, 32%nat); (0xed58c, 16%nat); (0xfc380, 80%nat)]%Z.

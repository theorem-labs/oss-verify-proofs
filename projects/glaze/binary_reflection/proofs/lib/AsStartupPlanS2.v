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
  (PRun [0xbeffc] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 950 (* [comment removed for export] *))))))).

Definition s2a_plan : plan :=
  PBump 467 (* [comment removed for export] *)
  (s2a_plan_r0_1).

(* [comment removed for export] *)
Definition s2a_plan_ranges : list (Z * nat) := [(0x75910, 32%nat); (0x75b10, 32%nat); (0x75e90, 16%nat); (0x77850, 48%nat); (0x7cd10, 32%nat); (0x7ff10, 112%nat); (0x84e90, 48%nat); (0x850d0, 96%nat); (0x85350, 32%nat); (0x9c318, 80%nat); (0xbefd4, 16%nat)]%Z.

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
  PRun [0x8f428] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 951 (* [comment removed for export] *))).

Definition s2b_plan : plan :=
  PBump 510 (* [comment removed for export] *)
  (s2b_plan_r0_1).

(* [comment removed for export] *)
Definition s2b_plan_ranges : list (Z * nat) := [(0x59024, 80%nat); (0x5a3e4, 32%nat); (0x70a10, 32%nat); (0x74c90, 16%nat); (0x75e90, 16%nat); (0x76910, 64%nat); (0x76a50, 16%nat); (0x78390, 32%nat); (0x78550, 64%nat); (0x8f3cc, 32%nat); (0x8fa4c, 80%nat); (0xbefd4, 32%nat); (0xf7048, 32%nat)]%Z.

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
  PRun [0x5915c] (* [comment removed for export] *)
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
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [0x9c5c0] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 1 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))))).

Definition s2c_plan_r1_2 : plan :=
  PRun [0x5915c] (* [comment removed for export] *)
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
  (PRun [] (* [comment removed for export] *)
  (PExt 201 [] (* [comment removed for export] *)
  (PRun [0x9c5c0] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PHandoff 2 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))))).

Definition s2c_plan : plan :=
  PBump 517 (* [comment removed for export] *)
  (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 4030 (* [comment removed for export] *)
  (s2c_plan_r0_1)
  (s2c_plan_r1_2)).

(* [comment removed for export] *)
Definition s2c_plan_ranges : list (Z * nat) := [(0x4a924, 32%nat); (0x59124, 48%nat); (0x59224, 64%nat); (0x593a4, 80%nat); (0x59564, 16%nat); (0x596a4, 16%nat); (0x59864, 32%nat); (0x599a4, 48%nat); (0x59ae4, 96%nat); (0x5a424, 16%nat); (0x5ab64, 48%nat); (0x5ac64, 112%nat); (0x5b024, 32%nat); (0x5c3a4, 64%nat); (0x6f5d0, 48%nat); (0x6f810, 48%nat); (0x6f950, 32%nat); (0x74c90, 16%nat); (0x76a50, 32%nat); (0x7a750, 80%nat); (0x7bf50, 32%nat); (0x7c610, 16%nat); (0x7fe90, 32%nat); (0x80710, 16%nat); (0x81dd0, 144%nat); (0x82310, 80%nat); (0x82ad0, 32%nat); (0x82c10, 32%nat); (0x88790, 32%nat); (0x8c44c, 128%nat); (0x8c68c, 16%nat); (0x8cf8c, 48%nat); (0x8e78c, 32%nat); (0x8ea4c, 96%nat); (0x8ec0c, 80%nat); (0x8f20c, 96%nat); (0x8f40c, 80%nat); (0x9c598, 16%nat); (0xbf014, 16%nat); (0xe6854, 16%nat); (0xe68d4, 32%nat); (0xf56c8, 80%nat)]%Z.

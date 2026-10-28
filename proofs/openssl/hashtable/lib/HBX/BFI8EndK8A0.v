(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CxPlan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrRev Br3RespDefs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BFI8DataK8A0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Open Scope Z_scope.
(* [comment removed for export] *)
Definition fresh_vars : list nat := flat_map (fun m : CAP.amap =>
     match CAP.am_base m with
     | AX2.EMd Instr.M_MUL (AX2.ELit 4096) (AX2.EVar v) =>
         if existsb (fun m0 : CAP.amap => AX2.expr_eqb (CAP.am_base m0) (CAP.am_base m)) (CAP.a_maps START0) then [] else [v]
     | _ => [] end) (CAP.a_maps END0).
Definition sh_page_expr0 (v : nat) : AX2.expr :=
  AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit 512) (AX2.EVar v)) (AX2.ELit 2147450880).
Definition row_fresh (b : AX2.expr) : list rrow :=
  flat_map (fun v : nat =>
     if lin_match (AX2.lin_of b) (AX2.lin_of (AX2.EMd Instr.M_MUL (AX2.ELit 512) (AX2.EVar v))) 0
     then [RR b (sh_page_expr0 v) 2147450880 None] else []) fresh_vars.
Definition RTe : list rrow := flat_map (fun b => row_of b ++ row_fresh b) (kbases (CAP.kn END0)).
Definition END : CAP.acs := resp_cs RTe END0.

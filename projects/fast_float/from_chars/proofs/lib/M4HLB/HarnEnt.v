(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanCallTL.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Definition ENT_S : sst := TCL_S.  Definition ENT_M : smodel := TCL_M.  Definition ENT_FS := TCL_FS.
Definition ENT_SH := TCL_SH.  Definition ENT_A : ast := TCL_A.
Definition ent_rg (i : nat) : region := nth i (s_rgs ENT_S) (RG (lconst 0) (lconst 0) RW TEmpty).
Definition V_QU : positive := Eval vm_compute in match l_t (rg_size (ent_rg 1)) with [(x, _)] => x | _ => 1%positive end.
Definition V_TU : positive := Eval vm_compute in
  match List.filter (fun '(x, c) => Z.eqb c 1) (l_t (rget (s_regs ENT_S) (rkey (Z_to_bv 5 11)))) with [(x, _)] => x | _ => 1%positive end.
Definition V_SBU : positive := Eval vm_compute in
  match tget 1%positive (rg_cont (ent_rg 3)) with Some (BV (LIN 0 [(x, 1)]) 0) => x | _ => 1%positive end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IX_FS : nat := 8.  Definition IX_BLK : nat := 9.  Definition IX_CTX : nat := 11.  Definition IX_THR : nat := 12.  Definition IX_PG : nat := 14.

(* [comment removed for export] *)
Definition NB_ENT : positive := 13795.
(* [comment removed for export] *)

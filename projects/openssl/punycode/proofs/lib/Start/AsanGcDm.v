(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Module GCD.

Definition keep_zero (b : expr) (K : kentry) : bool :=
  match K with KZero (SA b' _) _ => negb (expr_eqb b b') | _ => true end.
Definition keep_vals (b : expr) (K : kentry) : bool :=
  match K with
  | KZero (SA b' _) _ => negb (expr_eqb b b')
  | KWord (SA b' o) _ _ => negb (expr_eqb b b' && negb (Z.eqb (o mod 32) 0))
  | _ => true
  end.

Definition node_drop_zero (cs : acs) (args : list expr) : option acs :=
  match args with [b] => Some (set_kn cs (List.filter (keep_zero b) (kn cs))) | _ => None end.
Definition node_drop_vals (cs : acs) (args : list expr) : option acs :=
  match args with [b] => Some (set_kn cs (List.filter (keep_vals b) (kn cs))) | _ => None end.

End GCD.

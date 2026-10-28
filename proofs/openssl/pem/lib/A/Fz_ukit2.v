(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ZBridge Step.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Export Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac ubs_trap :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      first [ ubs_if
            | let K := fresh "KU" in if_cases K; zify_cond K;
              [ exfalso; rewrite ?unsigned_lit, ?ubs_lxor_ones in K by lia; lia | ]
            | let K := fresh "KU" in if_cases K; zify_cond K;
              [ | exfalso; rewrite ?unsigned_lit, ?ubs_lxor_ones in K by lia; lia ] ]
  end.
Ltac ustep := step; try ubs_trap.
Tactic Notation "usteps" constr(n) := do n ustep.

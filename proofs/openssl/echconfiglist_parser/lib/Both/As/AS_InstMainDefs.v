(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainFacts AsMainLazy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocRep AsMainSyms.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cert_st0 (X : pm_syms) (env : list Z) (ts : bool) : astate :=
  init_state (ps_b06 X) (pm_space_beg X) (ps_b08 X) env ts.

Definition cert_s0 (sp0z brk0z : Z) (X : pm_syms) (env : list Z) (ts : bool) (AL0 : Z) : ast :=
  mkAst (cert_st0 X env ts) (ps_b09 X) (ps_b10 X) (ps_b16 X)
        (zz2ww (PM_LAZY sp0z X)) (zz2ww (PM_S sp0z brk0z X)) (zz2ww (PM_ZR sp0z X))
        AL0 (pm_stack_top sp0z) (pm_stack_bottom sp0z).

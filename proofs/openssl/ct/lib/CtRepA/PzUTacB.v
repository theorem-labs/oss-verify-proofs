(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnTacX BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac usw C := match type of C with context [bv_swrap 32 ?e] => rewrite (bk_swrap32_small e) in C by lia end.
Ltac uland C := match type of C with context [Z.land ?x 18446744073709551615] => rewrite (ub_land64_small x) in C by lia end.
Ltac unorm2 C := repeat (first [ progress (ub_norm C) | usw C | uland C ]).

Ltac uchk_solve C ::=
  first [ solve [clear - C; lia]
        | solve [rewrite ?unsigned_lit in C by lia; lia]
        | solve [usmall C; rewrite ?unsigned_lit in C by lia; lia]
        | solve [uchk_open; try usmall C; ub_norm C; first [ ub_solve C | ub_ltb_cases C ]]
        | solve [uchk_open; try usmall C; unorm2 C; first [ ub_solve C | ub_ltb_cases C ]] ].

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.        (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Export ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUbTabB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac uchk_inv :=
  zstep; ub_sw; ub_lts;
  first [ ub_pc_lit | if_true
        | let C := fresh "Cub" in
          if_cases C; [ clear C | exfalso; zify_cond C; first [ uchk_solve C | fail 100 "uchk_inv: cannot refute the UBSan trap condition (inverted pair)" ] ] ].

(* [comment removed for export] *)
Ltac ub1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ApUbTabB.ub_kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ uchk | fail 100 "ub(B): cannot refute the UBSan trap condition at pc" pc ]
      | 3%Z => first [ uchk_inv | fail 100 "ub(B): cannot establish the branch over the UBSan trap jump at pc" pc ]
      end
  end.
Ltac ub := repeat ub1.
Ltac upre := ual; ub; try (udecide; ub).

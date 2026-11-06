(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxState AxSys AxRun.
From OSSVerify.Proofs.openssl.bndiv.lib.AxA Require Import AxExportM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition JUNK : Z := 8589934592.   (* [comment removed for export] *)

Definition fin_model (main_pc top : Z) (B : AST) : bool :=
  w_eqb (a_pc B) (wofZ main_pc) && is_nilb (am_out (a_model B)) && am_shadow (a_model B)
  && match am_fd (a_model B) with FDStd => true | _ => false end
  && match a_resv B with RNone => true | _ => false end       (* [comment removed for export] *)
  && big_top_ok B top && (a_budget B <=? JUNK).

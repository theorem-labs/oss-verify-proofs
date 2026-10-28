(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac TacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac ck_K xt JOIN K :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 xt)) in
  lazymatch goal with |- evt ?sg ?P (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    assert (K : forall tv : word, evt sg P (MS (tset p tv R) F (Z_to_bv 64 JOIN) fc rv m ro))
  end.

(* [comment removed for export] *)
Ltac ck_K2 xt xu JOIN K :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 xt)) in
  let q := eval vm_compute in (bv_key (Z_to_bv 5 xu)) in
  lazymatch goal with |- evt ?sg ?P (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    assert (K : forall tv tu : word, evt sg P (MS (tset q tu (tset p tv R)) F (Z_to_bv 64 JOIN) fc rv m ro))
  end.

Ltac red_tset :=
  lazymatch goal with |- evt ?sg ?P (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    let R' := eval cbv beta iota delta [tset mkR] in R in
    change (evt sg P (MS R F pc fc rv m ro)) with (evt sg P (MS R' F pc fc rv m ro)) end.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: split out of AS/X0lx.v at LPS 727298f3 (the ASan start-up shape and certificate at CONFIG_RSEQ off, compiled beside the one with CONFIG_RSEQ on; the shape read off the one run of the check that collects the hand-off states). *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0li X0lh X0ll X0ly X0lj X0kj X0lv X0n6 PlanRegen X0n2.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
let g := Control.goal () in
let r := constr:(@eq_refl cres $rhs) in
Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(** The start-up's shape with CONFIG_RSEQ off: the answer of AS/X0n2.v's one run of the check
    ([RUN_0]), which the certificate below checks with [check]. *)
Definition startup_shape_0 : shape := Eval vm_compute in coll_shape RUN_0.

Lemma startup_cert0 :
check ASEGS IT0 ASAN_A NX0 X0kj.LIMIT 0 XN0 XE0 XB0 (HS_asan 0) KC0 BFUEL FUEL None (asan_a_init 0) (su_plan 0)
= COk startup_shape_0.
Proof. cert_refl constr:(COk startup_shape_0). Qed.

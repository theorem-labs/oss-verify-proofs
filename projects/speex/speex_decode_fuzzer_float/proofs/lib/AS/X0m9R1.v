(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: split out of AS/X0m9.v at LPS 727298f3 (the ASan+UBSan start-up shape and certificate with CONFIG_RSEQ on, compiled beside the one with CONFIG_RSEQ off; the shape read off the one run of the check that collects the hand-off states). *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0li X0lh X0ll X0lz X0lk X0kj X0lw X0n7 PlanRegen X0n3.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
let g := Control.goal () in
let r := constr:(@eq_refl cres $rhs) in
Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(** The start-up's shape with CONFIG_RSEQ on: the answer of AS/X0n3.v's one run of the check
    ([RUN_1]), which the certificate below checks with [check]. *)
Definition startup_shape_1 : shape := Eval vm_compute in coll_shape RUN_1.

Lemma startup_cert1 :
check ASEGS IT0 ASAN_B NX0 X0kj.LIMIT 1 XN0 XE0 XB0 (HS_both 1) KC0 BFUEL FUEL None (asan_b_init 1) (su_plan 1)
= COk startup_shape_1.
Proof. cert_refl constr:(COk startup_shape_1). Qed.

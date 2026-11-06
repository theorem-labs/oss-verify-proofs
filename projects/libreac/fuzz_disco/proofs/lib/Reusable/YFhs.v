(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sweep5a is proved from its four quarters YFhsA..YFhsD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YFhsA YFhsB YFhsC YFhsD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep5a : forallb (fun i => zev (fun _ => 16648 + 8 * Z.of_nat i) CL_hi =? class_id (16648 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof.
replace (seq 0 1008) with (seq 0 252 ++ seq 252 252 ++ seq 504 252 ++ seq 756 252) by (vm_compute; reflexivity).
rewrite !forallb_app, YFhsA.sweep5a_q0, YFhsB.sweep5a_q1, YFhsC.sweep5a_q2, YFhsD.sweep5a_q3.
reflexivity.
Qed.

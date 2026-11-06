(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sweep6b is proved from its four quarters YFhvA..YFhvD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YFhvA YFhvB YFhvC YFhvD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6b : forallb (fun i => zev (fun _ => 41352 + 8 * Z.of_nat i) CL_hi =? class_id (41352 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof.
replace (seq 0 1008) with (seq 0 252 ++ seq 252 252 ++ seq 504 252 ++ seq 756 252) by (vm_compute; reflexivity).
rewrite !forallb_app, YFhvA.sweep6b_q0, YFhvB.sweep6b_q1, YFhvC.sweep6b_q2, YFhvD.sweep6b_q3.
reflexivity.
Qed.

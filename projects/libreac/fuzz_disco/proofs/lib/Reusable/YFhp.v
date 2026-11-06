(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sweep3 is proved from its four quarters YFhpA..YFhpD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YFhpA YFhpB YFhpC YFhpD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep3 : forallb (fun i => zev (fun _ => 584 + 8 * Z.of_nat i) CL_hi =? class_id (584 + 8 * Z.of_nat i)) (seq 0 440) = true.
Proof.
replace (seq 0 440) with (seq 0 110 ++ seq 110 110 ++ seq 220 110 ++ seq 330 110) by (vm_compute; reflexivity).
rewrite !forallb_app, YFhpA.sweep3_q0, YFhpB.sweep3_q1, YFhpC.sweep3_q2, YFhpD.sweep3_q3.
reflexivity.
Qed.

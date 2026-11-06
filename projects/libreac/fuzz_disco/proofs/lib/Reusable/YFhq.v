(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sweep4a is proved from its four quarters YFhqA..YFhqD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YFhqA YFhqB YFhqC YFhqD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep4a : forallb (fun i => zev (fun _ => 4232 + 8 * Z.of_nat i) CL_hi =? class_id (4232 + 8 * Z.of_nat i)) (seq 0 760) = true.
Proof.
replace (seq 0 760) with (seq 0 190 ++ seq 190 190 ++ seq 380 190 ++ seq 570 190) by (vm_compute; reflexivity).
rewrite !forallb_app, YFhqA.sweep4a_q0, YFhqB.sweep4a_q1, YFhqC.sweep4a_q2, YFhqD.sweep4a_q3.
reflexivity.
Qed.

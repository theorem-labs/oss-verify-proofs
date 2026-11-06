(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhp.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: sweep3 is proved from its four quarters AFhpA..AFhpD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0x AFhy AFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AFhpA AFhpB AFhpC AFhpD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep3 : forallb (fun i => zev (fun _ => 584 + 8 * Z.of_nat i) CL_hi =? class_id (584 + 8 * Z.of_nat i)) (seq 0 440) = true.
Proof.
replace (seq 0 440) with (seq 0 110 ++ seq 110 110 ++ seq 220 110 ++ seq 330 110) by (vm_compute; reflexivity).
rewrite !forallb_app, AFhpA.sweep3_q0, AFhpB.sweep3_q1, AFhpC.sweep3_q2, AFhpD.sweep3_q3.
reflexivity.
Qed.

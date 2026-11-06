(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhr.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: sweep4b is proved from its four quarters AFhrA..AFhrD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0x AFhy AFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AFhrA AFhrB AFhrC AFhrD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep4b : forallb (fun i => zev (fun _ => 10312 + 8 * Z.of_nat i) CL_hi =? class_id (10312 + 8 * Z.of_nat i)) (seq 0 760) = true.
Proof.
replace (seq 0 760) with (seq 0 190 ++ seq 190 190 ++ seq 380 190 ++ seq 570 190) by (vm_compute; reflexivity).
rewrite !forallb_app, AFhrA.sweep4b_q0, AFhrB.sweep4b_q1, AFhrC.sweep4b_q2, AFhrD.sweep4b_q3.
reflexivity.
Qed.

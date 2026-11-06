(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFht.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: sweep5b is proved from its four quarters AFhtA..AFhtD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0x AFhy AFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AFhtA AFhtB AFhtC AFhtD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep5b : forallb (fun i => zev (fun _ => 24712 + 8 * Z.of_nat i) CL_hi =? class_id (24712 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof.
replace (seq 0 1008) with (seq 0 252 ++ seq 252 252 ++ seq 504 252 ++ seq 756 252) by (vm_compute; reflexivity).
rewrite !forallb_app, AFhtA.sweep5b_q0, AFhtB.sweep5b_q1, AFhtC.sweep5b_q2, AFhtD.sweep5b_q3.
reflexivity.
Qed.

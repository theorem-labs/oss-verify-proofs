(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhv.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: sweep6b is proved from its four quarters AFhvA..AFhvD.v, which compile in parallel. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0x AFhy AFhz.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AFhvA AFhvB AFhvC AFhvD.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6b : forallb (fun i => zev (fun _ => 41352 + 8 * Z.of_nat i) CL_hi =? class_id (41352 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof.
replace (seq 0 1008) with (seq 0 252 ++ seq 252 252 ++ seq 504 252 ++ seq 756 252) by (vm_compute; reflexivity).
rewrite !forallb_app, AFhvA.sweep6b_q0, AFhvB.sweep6b_q1, AFhvC.sweep6b_q2, AFhvD.sweep6b_q3.
reflexivity.
Qed.

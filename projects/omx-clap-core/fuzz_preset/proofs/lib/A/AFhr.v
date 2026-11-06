(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhr.v, with its module paths changed; every one of its 6 image numerals names the same object in omx-clap-core/fuzz_preset's ASan build as in cgif_file_fuzzer.asan's (c-asan's checker e55e1b52a8a0, all SAME-* verdicts). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0x AFhy AFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep4b : forallb (fun i => zev (fun _ => 10312 + 8 * Z.of_nat i) CL_hi =? class_id (10312 + 8 * Z.of_nat i)) (seq 0 760) = true.
Proof. vm_compute. reflexivity. Qed.

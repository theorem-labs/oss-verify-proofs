(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGhw.v (cold/c-asan-realloc-primary 95e637d80d2, file sha256 a3b7ddb55561) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhy AGhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6c : forallb (fun i => zev (fun _ => 49416 + 8 * Z.of_nat i) CL_hi =? class_id (49416 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof. vm_compute. reflexivity. Qed.

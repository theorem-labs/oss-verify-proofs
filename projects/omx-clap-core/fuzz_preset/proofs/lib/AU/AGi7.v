(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGi7.v (cold/c-asan-realloc-primary 2810ff79e7b, file sha256 a215cf8eeb80) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGi6.
Import ListNotations. Open Scope Z_scope.
Lemma sweep_lo : sweep clz_okb (Z.to_nat 32750) 18 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

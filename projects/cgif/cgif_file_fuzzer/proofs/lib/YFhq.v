(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep4a : forallb (fun i => zev (fun _ => 4232 + 8 * Z.of_nat i) CL_hi =? class_id (4232 + 8 * Z.of_nat i)) (seq 0 760) = true.
Proof. vm_compute. reflexivity. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AGhr.v at 95e6f1d72b6 (sha256 8730081364c9) into lib/B (libreac/fuzz_decode image B, fuzz_decode.asan-ubsan), with its module paths changed only (it states no image numeral; image B's own copy because its Require closure reaches image modules). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP0m YP0l YG00. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YF0x YFhy AGhy AGhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep4b : forallb (fun i => zev (fun _ => 10312 + 8 * Z.of_nat i) CL_hi =? class_id (10312 + 8 * Z.of_nat i)) (seq 0 760) = true.
Proof. vm_compute. reflexivity. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFht.v (donor image sha256 1c29845fe605), with its module paths changed. *)
(* Relocated from proofs/libreac/fuzz_decode/lib/YFht.v at 88154566652a by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan-ubsan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0m YP0l YG00. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YF0x YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep5b : forallb (fun i => zev (fun _ => 24712 + 8 * Z.of_nat i) CL_hi =? class_id (24712 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof. vm_compute. reflexivity. Qed.

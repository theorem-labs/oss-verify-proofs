(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFhx.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AFhx.v (donor image sha256 61768cf4739b), with its module paths changed. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AF0x AFhy AFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6d : forallb (fun i => zev (fun _ => 57480 + 8 * Z.of_nat i) CL_hi =? class_id (57480 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof. vm_compute. reflexivity. Qed.

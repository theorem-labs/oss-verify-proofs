(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhu.v, with its module paths changed. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/A/AFhu.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AF0x AFhy AFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6a : forallb (fun i => zev (fun _ => 33288 + 8 * Z.of_nat i) CL_hi =? class_id (33288 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof. vm_compute. reflexivity. Qed.

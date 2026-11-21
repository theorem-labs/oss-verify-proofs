(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFhw.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFhw.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFhy_w AFhz_w.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6c : forallb (fun i => zev (fun _ => 49416 + 8 * Z.of_nat i) CL_hi =? class_id (49416 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof. vm_compute. reflexivity. Qed.

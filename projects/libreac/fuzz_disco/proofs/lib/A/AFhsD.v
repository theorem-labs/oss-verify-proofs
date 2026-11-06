(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: new file, quarter 4 of AFhs.v's sweep5a (the indices seq 756 252), split out so the four quarters compile in parallel; checked by the kernel only (vm_cast_no_check), not twice. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0x AFhy AFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep5a_q3 : forallb (fun i => zev (fun _ => 16648 + 8 * Z.of_nat i) CL_hi =? class_id (16648 + 8 * Z.of_nat i)) (seq 756 252) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, quarter 1 of YFht.v's sweep5b (the indices seq 0 252), split out so the four quarters compile in parallel; checked by the kernel only (vm_cast_no_check), not twice. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep5b_q0 : forallb (fun i => zev (fun _ => 24712 + 8 * Z.of_nat i) CL_hi =? class_id (24712 + 8 * Z.of_nat i)) (seq 0 252) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, quarter 3 of YFhv.v's sweep6b (the indices seq 504 252), split out so the four quarters compile in parallel; checked by the kernel only (vm_cast_no_check), not twice. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6b_q2 : forallb (fun i => zev (fun _ => 41352 + 8 * Z.of_nat i) CL_hi =? class_id (41352 + 8 * Z.of_nat i)) (seq 504 252) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

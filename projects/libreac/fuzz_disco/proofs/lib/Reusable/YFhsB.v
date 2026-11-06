(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, quarter 2 of YFhs.v's sweep5a (the indices seq 252 252), split out so the four quarters compile in parallel; checked by the kernel only (vm_cast_no_check), not twice. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YG00 YF0x YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep5a_q1 : forallb (fun i => zev (fun _ => 16648 + 8 * Z.of_nat i) CL_hi =? class_id (16648 + 8 * Z.of_nat i)) (seq 252 252) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

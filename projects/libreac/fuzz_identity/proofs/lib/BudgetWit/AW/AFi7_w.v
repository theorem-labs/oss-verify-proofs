(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFi7.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFi7.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFi6_w.
Import ListNotations. Open Scope Z_scope.
Lemma sweep_lo : sweep clz_okb (Z.to_nat 32750) 18 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

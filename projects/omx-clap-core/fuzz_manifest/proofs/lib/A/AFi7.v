(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: module paths changed to omx-clap-core fuzz_manifest (no address literal changed). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AFi6.
Import ListNotations. Open Scope Z_scope.
Lemma sweep_lo : sweep clz_okb (Z.to_nat 32750) 18 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

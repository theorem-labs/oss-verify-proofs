(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import ParseNumberChkXA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma leaves_30_4 : PNA.leaves_rng 30 4 = true.
Proof. vm_compute. reflexivity. Qed.

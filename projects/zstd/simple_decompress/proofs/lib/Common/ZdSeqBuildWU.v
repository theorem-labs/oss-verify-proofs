(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma neg_maskw : forall (b : bool) fast, 0 <= fast < 2^64 ->
  Z.land (bv_swrap 32 (0 - Z.b2z b) mod 18446744073709551616) fast = if b then fast else 0.
Proof.
  intros b fast Hf. destruct b; cbn [Z.b2z].
  - change (bv_swrap 32 (0 - 1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - reflexivity.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import ModelInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma image_low_bgpsegs : image_low bgpsegs.
Proof. split; vm_compute; [reflexivity| discriminate]. Qed.

Lemma image_low_bgusegs : image_low bgusegs.
Proof. split; vm_compute; [reflexivity| discriminate]. Qed.


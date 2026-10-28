(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ModelInv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma image_low_ctpsegs : image_low ctpsegs.
Proof. split; vm_compute; [reflexivity| discriminate]. Qed.

Lemma image_low_ctusegs : image_low ctusegs.
Proof. split; vm_compute; [reflexivity| discriminate]. Qed.


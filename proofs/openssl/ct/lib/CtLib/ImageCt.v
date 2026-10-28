(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Stage.
From OssFuzzTheorems.openssl.ct.images Require Import Plain.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition ctpsegs : list Segment := Plain.M.loaded_segments.
Definition ctusegs : list Segment := Ubsan.M.loaded_segments.


Definition ctpstage : Z := 0x2dab69.
Definition ctustage : Z := 0x3206a9.

Lemma ctpstage_range : 0x2da000 <= ctpstage /\ ctpstage + RSTAGE_LEN <= 0x30f000.
Proof. unfold ctpstage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.

Lemma ctustage_range : 0x31f000 <= ctustage /\ ctustage + RSTAGE_LEN <= 0x355000.
Proof. unfold ctustage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.

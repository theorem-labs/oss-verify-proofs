(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Stage.
From OssFuzzTheorems.openssl.bignum.images Require Import Plain.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition bgpsegs : list Segment := Plain.M.loaded_segments.
Definition bgusegs : list Segment := Ubsan.M.loaded_segments.

Definition bgpstage : Z := 0x2d8c49.
Definition bgustage : Z := 0x31e419.


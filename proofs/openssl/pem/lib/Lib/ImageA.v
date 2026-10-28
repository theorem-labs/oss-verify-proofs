(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.openssl.pem.images Require Import Asan AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := Asan.M.loaded_segments.
Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.

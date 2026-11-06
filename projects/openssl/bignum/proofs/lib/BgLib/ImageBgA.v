(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.openssl.bignum.images Require Import Asan AsanUbsan.

Definition bgasegs : list Segment := Asan.M.loaded_segments.
Definition bgbsegs : list Segment := AsanUbsan.M.loaded_segments.

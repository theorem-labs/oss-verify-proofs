(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SEGS : list Segment := Ubsan.M.loaded_segments.
Definition PC : N := Ubsan.M.init_pc.
Definition PH : PhdrInfo := Ubsan.M.phdrs.

Definition TEXT_LO : Z := 0x1f234.
Definition TEXT_N : nat := 52732.

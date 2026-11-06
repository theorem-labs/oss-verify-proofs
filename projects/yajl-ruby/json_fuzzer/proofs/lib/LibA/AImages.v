(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Asan AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := Asan.M.loaded_segments.
Definition a_init_pc := Asan.M.init_pc.
Definition a_phdrs := Asan.M.phdrs.
Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition b_init_pc := AsanUbsan.M.init_pc.
Definition b_phdrs := AsanUbsan.M.phdrs.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Plain.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rsegs : list Segment := Plain.M.loaded_segments.
Definition usegs : list Segment := Ubsan.M.loaded_segments.
Definition r_init_pc := Plain.M.init_pc.
Definition u_init_pc := Ubsan.M.init_pc.
Definition r_phdrs := Plain.M.phdrs.
Definition u_phdrs := Ubsan.M.phdrs.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Malloc/F_mm_syscalls.v: module paths and target names for simdjson/fuzz_utf8. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Export SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Export MM_syscalls.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


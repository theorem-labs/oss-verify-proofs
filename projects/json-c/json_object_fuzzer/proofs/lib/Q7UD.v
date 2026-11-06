(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.json_c.json_object_fuzzer.images Require Export Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition asegs := Asan.M.loaded_segments.

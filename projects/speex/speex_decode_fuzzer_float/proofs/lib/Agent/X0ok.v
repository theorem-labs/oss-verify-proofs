(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
Module Agent.
Definition loaded_segments := Plain.M.loaded_segments.
Definition init_pc := Plain.M.init_pc.
Definition phdrs := Plain.M.phdrs.
End Agent.

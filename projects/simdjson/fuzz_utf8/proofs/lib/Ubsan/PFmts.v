(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/PFmts.v: 8 image addresses for simdjson/fuzz_utf8's ubsan binary. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition A_FMT_pct_d : Z := 0x10cb0.
Definition A_FMT_usage : Z := 0x1103c.
Definition A_FMT_too_big : Z := 0x11e3d.
Definition A_FMT_cannot_open : Z := 0x12967.
Definition A_FMT_read_error : Z := 0x1297c.
Definition A_MSG_oom : Z := 0x10c9c.
Definition A_MSG_short_hdr : Z := 0x13040.
Definition A_MSG_cfg_overrun : Z := 0x1104d.

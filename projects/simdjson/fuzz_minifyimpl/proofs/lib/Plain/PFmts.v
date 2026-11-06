(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition A_FMT_pct_d : Z := 0x10d42.
Definition A_FMT_usage : Z := 0x111d6.
Definition A_FMT_too_big : Z := 0x1226b.
Definition A_FMT_cannot_open : Z := 0x130d4.
Definition A_FMT_read_error : Z := 0x130e9.
Definition A_MSG_oom : Z := 0x10d2e.
Definition A_MSG_short_hdr : Z := 0x1390e.
Definition A_MSG_cfg_overrun : Z := 0x111e7.

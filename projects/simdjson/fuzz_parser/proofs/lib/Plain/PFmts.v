(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition A_FMT_pct_d : Z := 0x10bca.
Definition A_FMT_usage : Z := 0x10f39.
Definition A_FMT_too_big : Z := 0x11bc5.
Definition A_FMT_cannot_open : Z := 0x125cb.
Definition A_FMT_read_error : Z := 0x125e0.
Definition A_MSG_oom : Z := 0x10bb6.
Definition A_MSG_short_hdr : Z := 0x12c5f.
Definition A_MSG_cfg_overrun : Z := 0x10f4a.

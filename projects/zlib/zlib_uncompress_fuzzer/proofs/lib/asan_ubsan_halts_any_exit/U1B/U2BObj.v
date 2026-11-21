(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition A_HARNESS : Z := 0x8c948.
Definition A_UNCOMPRESS2 : Z := 0x8cb50.
Definition A_INFLATEINIT : Z := 0x8dae0.
Definition A_INFLATE : Z := 0x8dd9c.
Definition A_UPDATEWINDOW : Z := 0x9458c.
Definition A_INFLATEEND : Z := 0x94ab4.
Definition A_ZCALLOC : Z := 0x94ccc.
Definition A_ZCFREE : Z := 0x94cdc.
Definition A_ADLER32Z : Z := 0x95f24.
Definition A_ADLER32 : Z := 0x96a28.
Definition A_ITABLE : Z := 0x96a34.
Definition A_IFAST : Z := 0x97b28.
Definition A_DISP : Z := 0x8e260.
Definition A_LEAVE : Z := 0x933cc.
Definition A_EPI : Z := 0x93798.
Definition A_JTAB : Z := 0x227b0.
Definition A_OUTBUF : Z := 0x60c1c0.

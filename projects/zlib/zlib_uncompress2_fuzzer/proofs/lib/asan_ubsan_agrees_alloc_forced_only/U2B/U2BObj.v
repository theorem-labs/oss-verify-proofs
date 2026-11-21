(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition A_HARNESS : Z := 0x8cb3c.
Definition A_UNCOMPRESS2 : Z := 0x8cd9c.
Definition A_INFLATEINIT : Z := 0x8dd80.
Definition A_INFLATE : Z := 0x8e03c.
Definition A_UPDATEWINDOW : Z := 0x9482c.
Definition A_INFLATEEND : Z := 0x94d54.
Definition A_ZCALLOC : Z := 0x94f6c.
Definition A_ZCFREE : Z := 0x94f7c.
Definition A_ADLER32Z : Z := 0x961c4.
Definition A_ADLER32 : Z := 0x96cc8.
Definition A_ITABLE : Z := 0x96cd4.
Definition A_IFAST : Z := 0x97dc8.
Definition A_DISP : Z := 0x8e500.
Definition A_LEAVE : Z := 0x9366c.
Definition A_EPI : Z := 0x93a38.
Definition A_JTAB : Z := 0x227c8.
Definition A_OUTBUF : Z := 0x60c440.

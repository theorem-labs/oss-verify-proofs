(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
Open Scope Z_scope.

Definition lh_ns (size : Z) : Z := if size <=? 2^29 then 2 * size else 2147483647.
Definition resize_costB (ns : Z) : Z := (16 * 56 + 512) + (16 * (40 * ns) + 512) + 512 + 512.
Definition ins_costB (size cnt : Z) : Z := if lf_thr size <=? cnt then resize_costB (lh_ns size) else 0.

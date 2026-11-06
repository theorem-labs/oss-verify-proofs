(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition qb_ok (st : astate) (p : AsanCtrl.aptr) : bool :=
match (a_live st) !! p with
| Some ch => (0 <=? a_qloc_bytes st) && (0 <=? a_qglob_bytes st)
&& (a_qloc_bytes st + a_qglob_bytes st + chunk_size ch + Q_BATCH_BYTES <=? Q_MAX)
| None => false
end.

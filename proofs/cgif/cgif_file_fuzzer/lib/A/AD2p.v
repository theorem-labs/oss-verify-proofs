(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AZ03 AD2o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require ACkh ACkg ACke.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Theorem TFIB_T_closed : TFIB_T.
Proof.
exact (TFIB_T_of_partsXF 0x81a18
(fun rc fx => @ACkg.tfib_newgifX_closed fx rc)
(fun rc fx => @ACkh.tfib_addframeX_all rc fx)
(fun rc fx => @ACke.tfib_closeX_closed fx rc)).
Qed.

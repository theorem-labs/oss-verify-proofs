(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YM05.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YZ03 YD2o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YCkh YCkg YCke.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Theorem TFIB_T_closed : TFIB_T.
Proof.
exact (TFIB_T_of_partsXF 0x8131c
(fun rc fx => @YCkg.tfib_newgifX_closed fx rc)
(fun rc fx => @YCkh.tfib_addframeX_all rc fx)
(fun rc fx => @YCke.tfib_closeX_closed fx rc)).
Qed.

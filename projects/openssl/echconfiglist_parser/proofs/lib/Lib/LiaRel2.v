(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaTuning LiaRel.
#[global] Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac n8v_prune_plain2 := ltac2:(Control.enter (fun () => n8v_prune 2 0 0 false 0)).

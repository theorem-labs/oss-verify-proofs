(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog LibProg LibOps ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require HxpInit HxpInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition bndiv_ops : list lop := map HxpInv.dec_op HxpInit.OPS.

#[export] Instance LM_bndiv : LibModel := mkLibModel (lstate bptr) (init_of_ops bndiv_ops ls_init) bn_lib_one.

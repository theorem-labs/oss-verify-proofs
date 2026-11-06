(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import RT_iface RT_rep RT_closed.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import LibaBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXA Require Import HxaIface HxaFinal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem init_cps_RTA : init_cps RTA (LIBA RTA).
Proof. exact (init_cps_A RTA (rc_facts RTA rta_contracts_all) rta_contracts_all rta_live_pos). Qed.

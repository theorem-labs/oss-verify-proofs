(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Sj_num_kitu Sj_num_top Sj_num_closed.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Sj_iface Od_defs Od_fromch Od_arm_dbl Od_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem od_ffu_closed : ffu_stmt_g usegs 0x2a0fc NUMU_GTOP.
Proof. exact (numu_ff numu_memcpy_closed numu_memset_closed). Qed.

Theorem od_fromchu_closed : fromchu_stmt_g usegs OD_FROMCH OD_GTOP.
Proof. exact (fromchu_spec od_ffu_closed). Qed.

Theorem rfuzz_one_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, rfuzz_one_stmt.
Proof. intros CE RN. exact (rfuzz_one_of_dbl (fun E OK OKU => od_arm_dbl E OK OKU od_fromchu_closed)). Qed.

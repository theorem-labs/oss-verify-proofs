(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Sj_iface El_ins_iface El_os_put El_os_ins El_os_insd Dmp_defs Dmp_insb Dmp_pj_iface Dmp_pj Dmp_pj_arr Dmp_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem rfuzz_one_of_cases : (forall d, pj_obj_case d) -> rfuzz_one_stmt.
Proof.
  intros O.
  exact (rfuzz_one_of_pj (pj_root_of_parts os_putX_proof ins_b_proof ins_l_proof ins_ul_proof ins_d_proof pj_arr_proof O)).
Qed.
End WithCeiling0.

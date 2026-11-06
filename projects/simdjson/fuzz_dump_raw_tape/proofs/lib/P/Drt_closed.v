(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_iface El_dump_iface El_ins_iface El_esc_iface El_os_put El_setfill El_os_ins El_dump_top El_esc Drt_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem rfuzz_one_of_ins : ins_ul_stmt -> ins_u_stmt -> ins_l_stmt -> ins_i_stmt -> ins_d_stmt -> setfill_stmt -> rfuzz_one_stmt.
Proof.
  intros IUL IU IL INSI INSD SETF.
  exact (rfuzz_one_of_dump (dump_of_parts os_putX_proof IUL IU IL INSD (esc_of_parts os_putX_proof SETF INSI))).
Qed.

Theorem rfuzz_one_of_insd : ins_d_stmt -> rfuzz_one_stmt.
Proof. intros INSD. exact (rfuzz_one_of_ins ins_ul_proof ins_u_proof ins_l_proof ins_i_proof INSD setfill_proof). Qed.
End WithCeiling0.

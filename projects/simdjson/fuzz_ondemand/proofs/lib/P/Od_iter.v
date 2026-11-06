(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_top Sj_num_closed.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_defs Od_pstr_kit Od_pstr Od_fromch.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_raw Od_arm_cont Od_arm_int Od_arm_lit Od_arm_str Od_arm_dbl_defs Od_arm_dbl_top Od_arm_dbl_fhead Od_arm_nest Od_begin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Theorem od_ff_closed : ff_stmt_g psegs 0x28d4c 0xab000.
Proof. exact (num_ff num_memcpy_closed num_memset_closed). Qed.

Theorem od_fromch_closed : fromch_stmt_g psegs OD_FROMCH OD_GTOP.
Proof. exact (fromch_spec od_ff_closed). Qed.

Theorem od_pstr_closed : pstr_stmt_g psegs OD_PSTR OD_GTOP.
Proof. exact pstr_spec. Qed.

Theorem od_iterate_arms : forall E, od_ok E -> dbl_fhead_stmt E ->
  forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    evt psegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 (Z_to_bv 64 (o_BUF E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (o_len E)) (Z_to_bv 64 (o_act E)) xs4 (Z_to_bv 64 (o_COPY E)) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom psegs)).
Proof.
  intros E OK FH.
  exact (od_iterate E OK (od_arm_string E OK od_pstr_closed) (od_arm_bool E OK) (od_arm_array E OK) (od_arm_int64 E OK)
                    (od_arm_dbl_top2 E OK od_fromch_closed FH) (od_arm_object E OK) (od_arm_uint64 E OK) (od_arm_raw E OK)
                    (od_arm_null E OK) (od_arm_nest E OK)).
Qed.

Theorem od_iterate_closed : forall E, od_ok E ->
  forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    evt psegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 (Z_to_bv 64 (o_BUF E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (o_len E)) (Z_to_bv 64 (o_act E)) xs4 (Z_to_bv 64 (o_COPY E)) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom psegs)).
Proof. intros E OK. exact (od_iterate_arms E OK (dbl_fhead E OK)). Qed.

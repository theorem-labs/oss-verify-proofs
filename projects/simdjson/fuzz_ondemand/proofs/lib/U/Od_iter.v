(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_pstr_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_pstr_defs Od_pstr.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Sj_num_kitu Sj_num_top Sj_num_closed Od_fromch Od_arm_dbl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_arm_raw Od_arm_cont Od_arm_int Od_arm_lit Od_arm_str Od_arm_nest Od_begin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Theorem od_pstr_closed : pstru_stmt_g usegs OD_PSTR OD_GTOP.
Proof. exact pstru_spec. Qed.

Theorem od_iterate_arms : forall E, od_ok E -> od_oku E -> arm_stmt E 0x279b0 ->
  forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 (o_len E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (o_BUF E)) xs3 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 0) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom usegs)).
Proof.
  intros E OK OKU ARM_DBL.
  exact (od_iterate E OK OKU (od_arm_string E OK OKU od_pstr_closed) (od_arm_bool E OK OKU) (od_arm_array E OK OKU) (od_arm_int64 E OK OKU)
                    ARM_DBL (od_arm_object E OK OKU) (od_arm_uint64 E OK OKU) (od_arm_raw E OK OKU)
                    (od_arm_null E OK OKU) (od_arm_nest E OK OKU)).
Qed.

Theorem od_ffu_closed : ffu_stmt_g usegs 0x2a0fc NUMU_GTOP.
Proof. exact (numu_ff numu_memcpy_closed numu_memset_closed). Qed.

Theorem od_fromchu_closed : fromchu_stmt_g usegs OD_FROMCH OD_GTOP.
Proof. exact (fromchu_spec od_ffu_closed). Qed.

Theorem od_iterate_closed : forall E, od_ok E -> od_oku E ->
  forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 (o_len E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (o_BUF E)) xs3 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 0) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom usegs)).
Proof. intros E OK OKU. exact (od_iterate_arms E OK OKU (od_arm_dbl E OK OKU od_fromchu_closed)). Qed.

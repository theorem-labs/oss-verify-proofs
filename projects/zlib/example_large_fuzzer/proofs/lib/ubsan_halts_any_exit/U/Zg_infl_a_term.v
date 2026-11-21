(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma arm_DONE_eq : forall s c r, arm_DONE (mkW s c r) = ALeave (mkW s c (irset_ret r Z_STREAM_END)).
Proof. reflexivity. Qed.
Lemma arm_BAD_eq : forall s c r, arm_BAD (mkW s c r) = ALeave (mkW s c (irset_ret r Z_DATA_ERROR)).
Proof. reflexivity. Qed.
Lemma arm_MEM_eq : forall s c r, arm_MEM (mkW s c r) = ARet Z_MEM_ERROR (mkW s c r).
Proof. reflexivity. Qed.

Lemma arm_DONE_ok : forall flush, arm_stmtg flush DONE PC_DONE arm_DONE.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_DONE_eq.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  unfold PC_DONE. do 2 zs.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
  eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma arm_BAD_ok : forall flush, arm_stmtg flush BAD PC_BAD arm_BAD.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_BAD_eq.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
  eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma arm_MEM_ok : forall flush, arm_stmtg flush MEM PC_MEM arm_MEM.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_MEM_eq.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  unfold PC_MEM. do 2 zs.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply IRET_intro; ired; try ireg.
  - eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
  - intros E; discriminate E.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition PC_LENLENS_E : Z := 0x1d848.
Definition PC_CODELENS_E : Z := 0x1d994.

Definition lenlens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPg X w PC_LENLENS_E q ms ->
  sc12 q = wz (is_ncode (w_s w)) -> sc15 q = wz (is_have (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = LENLENS ->
  evt psegs (fun ms' => IPOST X (arm_LENLENS ivar_ref flush w) ms' /\ PATI X (wof (arm_LENLENS ivar_ref flush w))) ms.

Definition codelens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPg X w PC_CODELENS_E q ms ->
  sc13 q = wz (is_have (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = CODELENS ->
  evt psegs (fun ms' => IPOST X (arm_CODELENS ivar_ref flush w) ms' /\ PATI X (wof (arm_CODELENS ivar_ref flush w))) ms.

Definition len__core_stmt : Prop := forall X w x8 x12 ms,
  ILOOP X w PC_LEN_ x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN_ ->
  evt psegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATI X (wof (arm_LEN_ ivar_ref w))) ms.

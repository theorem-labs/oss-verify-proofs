(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateA_LEN1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition PC_LENLENS_E : Z := 0x1d8c8.
Definition PC_CODELENS_E : Z := 0x1da14.

Definition lenlens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPg X w PC_LENLENS_E q ms ->
  sc12 q = wz (is_ncode (w_s w)) -> sc15 q = wz (is_have (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = LENLENS ->
  evt psegs (fun ms' => IPOST X (arm_LENLENS ivar_ref flush w) ms' /\ PATG X (wof (arm_LENLENS ivar_ref flush w))) ms.

Definition codelens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPg X w PC_CODELENS_E q ms ->
  sc13 q = wz (is_have (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = CODELENS ->
  evt psegs (fun ms' => IPOST X (arm_CODELENS ivar_ref flush w) ms' /\ PATG X (wof (arm_CODELENS ivar_ref flush w))) ms.

Definition len__core_stmt : Prop := forall X w x8 x12 ms,
  ILOOP X w PC_LEN_ x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LEN_ ->
  evt psegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATG X (wof (arm_LEN_ ivar_ref w))) ms.

Definition PC_LENEXT_NB : Z := 0x1d458.
Definition PC_LENEXT_OFF : Z := 0x1e8dc.
Definition PC_DISTEXT_E : Z := 0x1ea88.

Definition len_core_stmt : Prop := forall X w x8 x12 ms,
  ILOOP X w PC_LEN x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LEN ->
  evt psegs (fun ms' => IPOST X (arm_LEN ivar_ref w) ms' /\ PATG X (wof (arm_LEN ivar_ref w))) ms.

Definition lenext_core_on_stmt : Prop := forall X w q ms,
  ILOOPg X w PC_LENEXT_NB q ms -> sc13 q = wz (is_extra (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) <> 0 ->
  evt psegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATG X (wof (arm_LENEXT ivar_ref w))) ms.

Definition lenext_core_off_stmt : Prop := forall X w q ms,
  ILOOPg X w PC_LENEXT_OFF q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) = 0 ->
  evt psegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATG X (wof (arm_LENEXT ivar_ref w))) ms.

Definition dist_core_stmt : Prop := forall X w x8 x12 ms,
  ILOOP X w PC_DIST x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DIST ->
  evt psegs (fun ms' => IPOST X (arm_DIST ivar_ref w) ms' /\ PATG X (wof (arm_DIST ivar_ref w))) ms.

Definition distext_core_stmt : Prop := forall X w q ms,
  ILOOPg X w PC_DISTEXT_E q ms -> sc13 q = wz (is_extra (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DISTEXT ->
  evt psegs (fun ms' => IPOST X (arm_DISTEXT ivar_ref w) ms' /\ PATG X (wof (arm_DISTEXT ivar_ref w))) ms.

Definition match_core_stmt : Prop := forall X w x8 x12 ms,
  ILOOP X w PC_MATCH x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = MATCH ->
  evt psegs (fun ms' => IPOST X (arm_MATCH ivar_ref w) ms' /\ PATG X (wof (arm_MATCH ivar_ref w))) ms.

Definition len_fast_stmt : Prop := forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_LEN x8 x12 ms -> ix_ok X -> WINV (mkW s c r) -> PATG X (mkW s c r) -> is_mode s = LEN ->
  6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  evt psegs (fun ms' => IPOST X (lf_res s c r) ms' /\ PATG X (wof (lf_res s c r))) ms.

Definition copy__core_stmt : Prop := forall X w x8 x12 ms,
  ILOOP X w PC_COPY_ x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = COPY_ ->
  evt psegs (fun ms' => IPOST X (arm_COPY_ w) ms' /\ PATG X (wof (arm_COPY_ w))) ms.

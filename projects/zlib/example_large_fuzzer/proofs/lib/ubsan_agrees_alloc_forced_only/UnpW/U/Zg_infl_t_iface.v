From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Z_infl_t_iface Z_infl_a_dist1 Z_infl_a_distext Z_infl_a_lenext Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateA_LEN1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition lenlens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPh X w PC_LENLENS_E q ms ->
  h17 q = wz (is_have (w_s w)) -> h14 q = wz (il_NI (ix_L X) + ir_next (w_r w)) -> h12 q = wz (ir_have (w_r w)) ->
  h9 q = wz (il_NO (ix_L X) + ir_put (w_r w)) -> h11 q = wz (ix_flush X) -> h13 q = wz (il_S (ix_L X)) ->
  h18 q = wz (ir_bits (w_r w)) -> h22 q = wz (ir_hold (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = LENLENS ->
  evt usegs (fun ms' => IPOST X (arm_LENLENS ivar_ref flush w) ms' /\ PATG X (wof (arm_LENLENS ivar_ref flush w))) ms.
Definition codelens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPh X w PC_CODELENS_E q ms ->
  h9 q = wz (il_NO (ix_L X) + ir_put (w_r w)) -> h10 q = wz (-2) -> h18 q = wz (ir_bits (w_r w)) -> h22 q = wz (ir_hold (w_r w)) ->
  h24 q = wz (ir_have (w_r w)) -> h25 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = CODELENS ->
  evt usegs (fun ms' => IPOST X (arm_CODELENS ivar_ref flush w) ms' /\ PATG X (wof (arm_CODELENS ivar_ref flush w))) ms.
Definition len__core_stmt : Prop := forall X w x26 x12 ms,
  ILOOP X w PC_LEN_ x26 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LEN_ ->
  evt usegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATG X (wof (arm_LEN_ ivar_ref w))) ms.
Definition len_core_stmt : Prop := forall X w q ms,
  ILOOPh X w PC_LEN q ms -> DE X (w_r w) q -> h13 q = wz (il_S (ix_L X)) -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LEN ->
  evt usegs (fun ms' => IPOST X (arm_LEN ivar_ref w) ms' /\ PATG X (wof (arm_LEN ivar_ref w))) ms.
Definition lenext_core_on_stmt : Prop := forall X w q ms,
  ILOOPh X w PC_LENEXT_NB q ms -> LXE X (w_s w) (w_r w) q ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) <> 0 ->
  evt usegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATG X (wof (arm_LENEXT ivar_ref w))) ms.
Definition lenext_core_off_stmt : Prop := forall X w q ms,
  ILOOPh X w PC_LENEXT_OFF q ms -> LXO X (w_r w) q ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) = 0 ->
  evt usegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATG X (wof (arm_LENEXT ivar_ref w))) ms.
Definition dist_core_stmt : Prop := forall X w q ms,
  ILOOPh X w PC_DIST q ms -> DE X (w_r w) q -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DIST ->
  evt usegs (fun ms' => IPOST X (arm_DIST ivar_ref w) ms' /\ PATG X (wof (arm_DIST ivar_ref w))) ms.
Definition distext_core_stmt : Prop := forall X w q ms,
  ILOOPh X w PC_DISTEXT_E q ms -> DXE X (w_s w) (w_r w) q ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DISTEXT ->
  evt usegs (fun ms' => IPOST X (arm_DISTEXT ivar_ref w) ms' /\ PATG X (wof (arm_DISTEXT ivar_ref w))) ms.
Definition match_core_stmt : Prop := forall X w x26 x12 ms,
  ILOOP X w PC_MATCH x26 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = MATCH ->
  evt usegs (fun ms' => IPOST X (arm_MATCH ivar_ref w) ms' /\ PATG X (wof (arm_MATCH ivar_ref w))) ms.
Definition len_fast_stmt : Prop := forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LEN q ms -> DE X r q -> h13 q = wz (il_S (ix_L X)) -> ix_ok X -> WINV (mkW s c r) -> PATG X (mkW s c r) -> is_mode s = LEN ->
  6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  evt usegs (fun ms' => IPOST X (lf_res s c r) ms' /\ PATG X (wof (lf_res s c r))) ms.
Definition copy__core_stmt : Prop := forall X w x26 x12 ms,
  ILOOP X w PC_COPY_ x26 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = COPY_ ->
  evt usegs (fun ms' => IPOST X (arm_COPY_ w) ms' /\ PATG X (wof (arm_COPY_ w))) ms.

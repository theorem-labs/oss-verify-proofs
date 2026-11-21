(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition PC_LENLENS_E : Z := 0x1fab4.
Definition PC_CODELENS_E : Z := 0x1fc4c.

(* [comment removed for export] *)
Definition lenlens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPh X w PC_LENLENS_E q ms ->
  h17 q = wz (is_have (w_s w)) -> h14 q = wz (il_NI (ix_L X) + ir_next (w_r w)) -> h12 q = wz (ir_have (w_r w)) ->
  h9 q = wz (il_NO (ix_L X) + ir_put (w_r w)) -> h11 q = wz (ix_flush X) -> h13 q = wz (il_S (ix_L X)) ->
  h18 q = wz (ir_bits (w_r w)) -> h22 q = wz (ir_hold (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = LENLENS ->
  evt usegs (fun ms' => IPOST X (arm_LENLENS ivar_ref flush w) ms' /\ PATI X (wof (arm_LENLENS ivar_ref flush w))) ms.

(* [comment removed for export] *)
Definition codelens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPh X w PC_CODELENS_E q ms ->
  h9 q = wz (il_NO (ix_L X) + ir_put (w_r w)) -> h10 q = wz (-2) -> h18 q = wz (ir_bits (w_r w)) -> h22 q = wz (ir_hold (w_r w)) ->
  h24 q = wz (ir_have (w_r w)) -> h25 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = CODELENS ->
  evt usegs (fun ms' => IPOST X (arm_CODELENS ivar_ref flush w) ms' /\ PATI X (wof (arm_CODELENS ivar_ref flush w))) ms.

Definition len__core_stmt : Prop := forall X w x26 x12 ms,
  ILOOP X w PC_LEN_ x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN_ ->
  evt usegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATI X (wof (arm_LEN_ ivar_ref w))) ms.

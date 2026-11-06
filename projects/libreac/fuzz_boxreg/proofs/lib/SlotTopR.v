From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_boxreg Require Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YH00 YH02 YI5b YI5c YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import ZTraceSpec ZComplete ZAllocator Img0.
Import ListNotations.
Open Scope Z_scope.
Definition zlib_contract_R (LS : lib_shape) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, @lib_contract_x_R_all rc LS src0_msyms (@zlib_API rc)
    src0_sink_head src0_sink RI G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Theorem plain_halts_from_slot_R : forall (LS : lib_shape) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) G R GI f,
  shape_permitted LS ->
  (forall data, leaves (fun r => match fst r with DL_run _ _ _ => RI (payload data) 0%nat [] (snd r) | _ => True end)
     (driver_tree data)) ->
  (forall a, in_globals G a -> in_globals src0_G a) ->
  (forall a, in_globals R a -> in_globals src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  zlib_contract_R LS RI G R GI f -> Statements.plain_halts.
Proof.
  intros LS RI G R GI f HLSP HDRV HG HRR GIL GI0 H.
  apply (plain_halts_from_runtime_contracts_R LS RI G R GI f HLSP HDRV HG HRR GIL GI0).
  intros rc. exists (@zlib_API rc). split; [apply zlib_allocator_extra | apply H].
Qed.

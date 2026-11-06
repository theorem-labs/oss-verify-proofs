From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
  YK11 YM05 YO0d YO05 YO09 YH00 YH02 YI5b YI5c YL0g YL0i YL0k YL0s DriverSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import ZTraceSpec ZComplete ZAllocator Img0.
Import ListNotations.
Open Scope Z_scope.
Definition zlib_checksum_contract_G (LS : lib_shape) (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, @lib_contract_x_G_all rc LS src0_msyms (@zlib_API rc)
    src0_sink_head src0_sink G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Theorem plain_halts_from_slot_G : forall (LS : lib_shape) G R GI f,
  shape_permitted LS ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD) ->
  (forall a, in_globals G a -> in_globals src0_G a) ->
  (forall a, in_globals R a -> in_globals src0_R a) ->
  G_local src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat mem) ->
  zlib_checksum_contract_G LS G R GI f -> Statements.plain_halts.
Proof.
  intros LS G R GI f HLSP HROOM HG HR GIL GI0 H.
  apply (plain_halts_from_runtime_contracts_G LS G R GI f HLSP HROOM HG HR GIL GI0).
  intros rc. exists (@zlib_API rc). split; [apply zlib_allocator_extra | apply H].
Qed.
Theorem zlib_checksum_contract_G_nil :
  zlib_checksum_contract_G checksum_shape [] [] (fun _ _ => True) (fun _ => []) <-> zlib_checksum_contract.
Proof.
  split; intros H rc.
  - apply (proj1 (lib_contract_x_G_all_nil src0_msyms (@zlib_API rc) LIBPC RA_LIB EMPTY LIB_STACK)). exact (H rc).
  - apply (proj2 (lib_contract_x_G_all_nil src0_msyms (@zlib_API rc) LIBPC RA_LIB EMPTY LIB_STACK)). exact (H rc).
Qed.
Lemma ms_segs_rsegs : ms_segs src0_msyms = rsegs.
Proof. reflexivity. Qed.

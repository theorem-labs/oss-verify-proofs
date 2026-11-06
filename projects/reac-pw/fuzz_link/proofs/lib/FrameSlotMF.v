From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_link Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YH00 YH02 YI5b YI5c YL0g YL0i YL0k YL0s YI14 YI16 YI06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import
  ZTraceSpec ZComplete ZAllocator Img0 Contract FrameAPI FrameProof FrameSlotG SlotTopR SlotTopG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemFileSink MemFile MemFileRI StdioExitMF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MwriteExit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mwrite_c.
Import ListNotations.
Open Scope Z_scope.

Theorem plain_halts_of_frame_slot_mf :
  forall (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  (forall j T m, GI j T m -> mf_gi src0_msyms link_mf T m) ->
  (forall rc : RunCeil, mwrite_exit_contract_all src0_msyms (@zlib_API rc)) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_x_T fx rc mf_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI (fun _ => []) j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.plain_halts.
Proof.
  intros G GI HG GIL GI0 GImf HMW H.
  apply (plain_halts_from_slot_R mf_shape RI_mf G frame_RELRO GI (fun _ => [])
    mf_shape_permitted driver_RI_mf (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0 GIL GI0 GImf HMW).
  intros rc.
  apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) RI_mf G frame_RELRO GI (fun _ => [])
    ENTRY RA_LIB EMPTY SLOT_STACK (RI_mf_step src0_msyms link_mf GI GImf)).
  intros fx j Hj. exact (H rc fx j Hj).
Qed.

Theorem frame_plain_mf_holds : frame_plain_mf.
Proof.
  exists src0_msyms, (@zlib_API), mf_shape, src0_sink_head, src0_sink, RA_LIB, EMPTY.
  split.
  - split; [exact ms_segs_rsegs|].
    split; [vm_compute; reflexivity|].
    do 4 (split; [reflexivity|]).
    split; [exact errno_below_ceiling|].
    do 14 (split; [reflexivity|]).
    do 3 (split; [reflexivity|]).
    split; [reflexivity|].
    split; [split; vm_compute; reflexivity|].
    split; [exact ctx_not_ro|].
    split; [exact frame_G_facts|].
    split; [exact frame_RELRO_facts|].
    exact zlib_frame_allocator.
  - exact plain_halts_of_frame_slot_mf.
Qed.

Theorem plain_halts_of_frame_slot_mf_mwrite :
  forall (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  (forall j T m, GI j T m -> mf_gi src0_msyms link_mf T m) ->
  mwrite_contract ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_x_T fx rc mf_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI (fun _ => []) j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.plain_halts.
Proof.
  intros G GI HG GIL GI0 GImf HMWC H.
  exact (plain_halts_of_frame_slot_mf G GI HG GIL GI0 GImf
    (fun rc => mwrite_exit_of_contract (rc:=rc) (@zlib_API rc) zlib_allocator_extra HMWC) H).
Qed.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements Images.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require RoomShapesDraft.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract SlotKept FrameAPI FrameSlotG SlotPack
  SlotAgree AgreeLim AgreeCanon SlotAgreeP3 AgreeP3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Contract SlotKept FrameAPI SlotPack SlotAgreeP3
  AgreeP3U AgreeRcP3U.
Import ListNotations.
Open Scope Z_scope.

Theorem ubsan_agrees_room_of_slots_p3 : forall (LS : lib_shape) (CS : list byte -> list Z)
    (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_t src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat [] mem) ->
  (forall (rc : RunCeil), limlaw_at SRC_LIM_MIN src0_msyms (@zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgp3 fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       CS frame_MCAP G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.SlotKept.G_local_t U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat [] mem) ->
  (forall (rc : RunCeil), limlaw_at LIM_AG U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgreeP3.lib_contract_cgp3 fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       CS U.FrameAPI.frame_MCAP Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB
       U.Reusable.YL0s.EMPTY U.FrameAPI.SLOT_STACK) ->
  RoomShapesDraft.agrees_in_room Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan.
Proof.
  intros LS CS G GI Gu GIu HCS HG GIL GI0 Hp HGu GILu GI0u Hu.
  assert (HCSu : U.SlotPack.CS_ok CS) by exact HCS.
  apply (agrees_room_of_runs (fun inp => SPECX (LS:=LS) inp)).
  - intros en inp Hv Hi. exact (plain_crealizes_of_cgp3 LS CS G GI HCS HG GIL GI0 Hp en inp
      Budgets.Standard.lim_source Hv Hi ltac:(apply Z.leb_le; vm_compute; reflexivity)).
  - intros en inp Hv Hi. exact (U.AgreeRcP3U.ubsan_crealizes_of_cgp3_rc LS CS Gu GIu HCSu HGu GILu GI0u
      (fun rc Hr => Hu rc (U.AgreeRcP3U.limlaw_of_rclim rc Hr)) en inp Budgets.Standard.lim_target Hv Hi
      ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity)).
Qed.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_rate Require Statements Images.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeLim.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require AgreeZlib.
Import ListNotations.
Open Scope Z_scope.

Theorem ubsan_agrees_of_slots : forall (LS : lib_shape)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_g fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgree.lib_contract_cg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  Statements.ubsan_agrees.
Proof.
  intros LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu.
  assert (HROOMp : forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) by exact HROOM.
  assert (HC : zlib_runtime_contracts_R LS (@RI_G LS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G LS) G frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step LS GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) G frame_RELRO GI (fun _ => []) j LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) G frame_RELRO GI j LIBPC RA_LIB EMPTY LIB_STACK
        (Hp rc fx j Hj))). }
  assert (HUB : forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
    rz_run Images.ubsan Budgets.Standard.lim_target en inp (SPECX (LS:=LS) inp) /\
    cf_run Images.ubsan Budgets.Standard.lim_target en inp).
  { intros en inp Hs Hin.
    exact (U.AgreeZlib.ubsan_crealizes_of_cg LS Gu GIu HROOM HGu GILu GI0u Hu en inp Budgets.Standard.lim_target Hs Hin
      ltac:(apply Z.leb_le; vm_compute; reflexivity)). }
  exact (ubsan_agrees_of_cut_free LS (@RI_G LS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])
    (driver_RI_AG LS HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs G GI GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC
    (fun en inp Hs Hin => proj1 (HUB en inp Hs Hin)) (fun en inp Hs Hin => proj2 (HUB en inp Hs Hin))).
Qed.

Theorem ubsan_agrees_of_slots_lim : forall (LS : lib_shape)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall rc : RunCeil, limlaw_at LIM_AG U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_g fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil), limlaw_at LIM_AG U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgree.lib_contract_cg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  Statements.ubsan_agrees.
Proof.
  intros LS G GI Gu GIu HL HG GIL GI0 Hp HROOM HGu GILu GI0u Hu.
  exact (ubsan_agrees_of_slots LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u (fun rc => Hu rc (HL rc))).
Qed.

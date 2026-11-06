From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots YL0i_cfw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG SlotPack
  SlotAgree SlotAgreeV AgreeLim Agree AgreeTop AgreeZlib AgreeWalkP AgreePack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require SlotPack SlotAgreeV AgreeZlib AgreeWalkP AgreePack Agree.
Import ListNotations.
Open Scope Z_scope.

Definition ubsan_agrees_of_slots_pg_st : Prop :=
  forall (LS : lib_shape) (CS : list byte -> list Z)
         (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
         (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall rc : RunCeil, limlaw_at LIM_AG U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil), limlaw_at SRC_LIM_MIN src0_msyms (@zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgpg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       CS G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil), limlaw_at LIM_AG U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgreeV.lib_contract_cgpg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       CS Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  Statements.ubsan_agrees.

Theorem ubsan_agrees_of_slots_pg : ubsan_agrees_of_slots_pg_st.
Proof.
  intros LS CS G GI Gu GIu HCS HLIM HG GIL GI0 Hp HGu GILu GI0u Hu.
  assert (HCSu : U.SlotPack.CS_ok CS) by exact HCS.
  unfold Statements.ubsan_agrees, agrees_in. intros en_p en_s inp Hp_e Hs_e Hinput _.
  destruct (plain_crealizes_of_cgpg LS CS G GI HCS HG GIL GI0 Hp en_p inp Budgets.Standard.lim_source
    Hp_e Hinput SRC_LIM_MIN_le_source) as [Rp Cp].
  destruct (U.AgreePack.ubsan_crealizes_of_cgpg LIM_AG LS CS Gu GIu HCSu HLIM HGu GILu GI0u Hu en_s inp
    Budgets.Standard.lim_target Hs_e Hinput ltac:(apply Z.leb_le; vm_compute; reflexivity)) as [Ru Cu].
  exact (agree_frame Images.plain Budgets.Standard.lim_source en_p Images.ubsan Budgets.Standard.lim_target en_s inp
    (SPECX (LS:=LS) inp) (SPECX (LS:=LS) inp) Rp Ru (t_eq_refl _) (budget_of_cf_run _ _ _ _ Cp) (U.Agree.budget_of_cf_run _ _ _ _ Cu)).
Qed.

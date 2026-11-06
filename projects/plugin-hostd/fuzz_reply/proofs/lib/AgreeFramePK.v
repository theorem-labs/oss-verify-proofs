From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements Images.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Plain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots YO0d_cf YL0i_cfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract SlotKept FrameAPI FrameSlotG SlotPack
  SlotAgree SlotAgreeV AllocCf AgreeLim Agree AgreeWalk AgreeTop AgreeZlib AgreeWalkP AgreePack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Contract SlotKept FrameAPI SlotPack SlotAgreeV
  AgreeZlib AgreeWalkP AgreePack AgreeFramePKU Agree.
Import ListNotations.
Open Scope Z_scope.

Definition ubsan_agrees_of_slots_p_st : Prop :=
  forall (LS : lib_shape) (CS : list byte -> list Z)
         (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
         (Gu : list (Z * Z)) (GIu : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall rc : RunCeil, limlaw_at LIM_AG U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_t src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat [] mem) ->
  (forall (rc : RunCeil), limlaw_at SRC_LIM_MIN src0_msyms (@zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgp fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       CS G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.SlotKept.G_local_t U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat [] mem) ->
  (forall (rc : RunCeil), limlaw_at LIM_AG U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgreeV.lib_contract_cgp fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       CS Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  Statements.ubsan_agrees.

Theorem plain_crealizes_of_cgp : forall (LS : lib_shape) (CS : list byte -> list Z) (G : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_t src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat [] mem) ->
  (forall (rc : RunCeil), limlaw_at SRC_LIM_MIN src0_msyms (@zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgp fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       CS G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp lim, valid_entry Images.plain en inp -> valid_input inp -> SRC_LIM_MIN <= lim ->
    rz_run Images.plain lim en inp (SPECX (LS:=LS) inp) /\ cf_run Images.plain lim en inp.
Proof.
  intros LS CS G GI HCS HG GIL GI0 H [sp brk0 mbase rnd] inp lim Hentry Hinput Hlim.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp) lim).
  assert (HG' : forall a, in_globals G a -> in_globals src0_G a) by (intros a h; exact (frame_G_src0 a (HG a h))).
  assert (HX : lib_contract_x_Rc_all src0_msyms (@zlib_API rc) (RI_Pc CS) src0_G src0_R
    GI (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK).
  { intros fx j Hj.
    apply (lib_contract_x_Rc_mono src0_msyms (@zlib_API rc) (RI_Pc CS) G src0_G frame_RELRO src0_R
      GI (fun _ => []) j LIBPC RA_LIB EMPTY LIB_STACK HG' frame_RELRO_src0).
    apply (lib_contract_x_Rc_of_cgp src0_msyms (@zlib_API rc) (zlib_tables rc) CS G frame_RELRO GI j
      LIBPC RA_LIB EMPTY LIB_STACK HCS).
    exact (H rc (zlib_limit rc) fx j Hj). }
  change (crealizes src0_msyms (init_config src0segs Plain_init_pc Plain_phdrs sp brk0 mbase rnd lim inp)
    (SPECX (LS:=LS) inp)).
  apply (zlib_pack_walk_crealizes rc LS CS GI (fun _ => []) HCS
    (G_local_T_mono src0segs G src0_G GI HG' GIL)
    (fun mem Hm => GI0 mem (G_img_mono src0segs G src0_G mem HG' Hm))
    HX sp brk0 mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinput Hlim).
  unfold rc. apply ceil_of_top_run.
  unfold rc. reflexivity.
Qed.

Theorem ubsan_agrees_of_slots_p : ubsan_agrees_of_slots_p_st.
Proof.
  intros LS CS G GI Gu GIu HCS HLIM HG GIL GI0 Hp HGu GILu GI0u Hu.
  assert (HCSu : U.SlotPack.CS_ok CS) by exact HCS.
  unfold Statements.ubsan_agrees, agrees_in. intros en_p en_s inp Hp_e Hs_e Hinput _.
  destruct (plain_crealizes_of_cgp LS CS G GI HCS HG GIL GI0 Hp en_p inp Budgets.Standard.lim_source
    Hp_e Hinput SRC_LIM_MIN_le_source) as [Rp Cp].
  destruct (U.AgreeFramePKU.ubsan_crealizes_of_cgp LIM_AG LS CS Gu GIu HCSu HGu GILu GI0u HLIM Hu en_s inp
    Budgets.Standard.lim_target Hs_e Hinput ltac:(apply Z.leb_le; vm_compute; reflexivity)) as [Ru Cu].
  exact (agree_frame Images.plain Budgets.Standard.lim_source en_p Images.ubsan Budgets.Standard.lim_target en_s inp
    (SPECX (LS:=LS) inp) (SPECX (LS:=LS) inp) Rp Ru (t_eq_refl _) (budget_of_cf_run _ _ _ _ Cp)
    (U.Agree.budget_of_cf_run _ _ _ _ Cu)).
Qed.

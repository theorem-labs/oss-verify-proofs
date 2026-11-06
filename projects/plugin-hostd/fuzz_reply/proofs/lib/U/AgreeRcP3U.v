From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements Images.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Ubsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots YO0d_cf YL0i_cfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract SlotKept FrameAPI FrameSlotG SlotPack
  SlotAgree AllocCf Agree AgreeWalk AgreeZlib AgreePack FrameSlotP3 SlotAgreeP3 AgreeWalkP3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AgreeLim.
Import ListNotations.
Open Scope Z_scope.

(* FRAME-NEEDS #39 for fuzz_reply (c-frame-gi's fm AgreeRcU.v, cold/c-frame-gi-rc 73c8bcb3b0): the walk's RunCeil
   carries the run's budget (rc_lim = lim), so the budget law the slot may assume holds at every allocator state
   (MRx_vm_limit), and the ubsan crealizes needs the pack3 slot only at run ceilings with LIM_AG <= rc_lim. *)

Lemma limlaw_of_rclim : forall rc : RunCeil, LIM_AG <= @rc_lim rc ->
  @limlaw_at rc LIM_AG src0_msyms (@zlib_API rc).
Proof. intros rc Hr L A mem md H. rewrite (MRx_vm_limit src0_msyms L A mem md H). exact Hr. Qed.

Lemma rc_lim_RunCeilOf : forall sp0 H lim, @rc_lim (RunCeilOf sp0 H lim) = lim.
Proof. reflexivity. Qed.

Theorem ubsan_crealizes_of_cgp3_rc : forall (LS : lib_shape) (CS : list byte -> list Z) (G : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_t src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat [] mem) ->
  (forall (rc : RunCeil), LIM_AG <= @rc_lim rc -> forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgp3 fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       CS frame_MCAP G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp lim, valid_entry Images.ubsan en inp -> valid_input inp -> SRC_LIM_MIN <= lim -> LIM_AG <= lim ->
    rz_run Images.ubsan lim en inp (SPECX (LS:=LS) inp) /\ cf_run Images.ubsan lim en inp.
Proof.
  intros LS CS G GI HCS HG GIL GI0 H [sp brk0 mbase rnd] inp lim Hentry Hinput Hlim Hag.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp) lim).
  assert (Hr : LIM_AG <= @rc_lim rc) by (unfold rc; rewrite rc_lim_RunCeilOf; exact Hag).
  assert (HG' : forall a, in_globals G a -> in_globals src0_G a) by (intros a h; exact (frame_G_src0 a (HG a h))).
  assert (HX : lib_contract_x_Rc_all src0_msyms (@zlib_API rc) (RI_P3c CS frame_MCAP) src0_G src0_R
    GI (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK).
  { intros fx j Hj.
    apply (lib_contract_x_Rc_mono src0_msyms (@zlib_API rc) (RI_P3c CS frame_MCAP) G src0_G frame_RELRO src0_R
      GI (fun _ => []) j LIBPC RA_LIB EMPTY LIB_STACK HG' frame_RELRO_src0).
    apply (lib_contract_x_Rc_of_cgp3 src0_msyms (@zlib_API rc) (zlib_tables rc) CS frame_MCAP G frame_RELRO GI j
      LIBPC RA_LIB EMPTY LIB_STACK HCS).
    exact (H rc Hr fx j Hj). }
  change (crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk0 mbase rnd lim inp)
    (SPECX (LS:=LS) inp)).
  apply (zlib_pack3_walk_crealizes rc LS CS GI (fun _ => []) HCS
    (G_local_T_mono src0segs G src0_G GI HG' GIL)
    (fun mem Hm => GI0 mem (G_img_mono src0segs G src0_G mem HG' Hm))
    HX sp brk0 mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinput Hlim).
  unfold rc. apply ceil_of_top_run.
  unfold rc. reflexivity.
Qed.

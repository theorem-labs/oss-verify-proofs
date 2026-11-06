From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_link Require Statements Images.
From OSSVerify.reac_pw.fuzz_link.images Require Import Ubsan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots YO0d_cf YL0i_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  SlotAgree AllocCf Agree AgreeWalk AgreeZlib SlotAgreeV.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance YK11.fx0.

Theorem ubsan_crealizes_of_cgo : forall (LS : lib_shape) (f : list byte -> list byte) (G : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop),
  (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgo fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       f G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp lim, valid_entry Images.ubsan en inp -> valid_input inp -> SRC_LIM_MIN <= lim ->
    rz_run Images.ubsan lim en inp (SPECX (LS:=LS) inp) /\ cf_run Images.ubsan lim en inp.
Proof.
  intros LS f G GI HROOM HG GIL GI0 H [sp brk0 mbase rnd] inp lim Hentry Hinput Hlim.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp)).
  assert (HG' : forall a, in_globals G a -> in_globals src0_G a) by (intros a h; exact (frame_G_src0 a (HG a h))).
  change (crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk0 mbase rnd lim inp)
    (SPECX (LS:=LS) inp)).
  apply (zlib_walk_crealizes rc LS (fun j T m => T = [] /\ GI j m) f HROOM
    (G_local_T_mono src0segs G src0_G _ HG' (G_local_T_of_G src0segs G GI GIL))
    (fun mem Hm => conj eq_refl (GI0 mem (G_img_mono src0segs G src0_G mem HG' Hm)))
    (fun fx j Hj => lib_contract_x_Rc_of_cgo src0_msyms (@zlib_API rc) (zlib_tables rc) f G src0_G frame_RELRO src0_R GI
      j LIBPC RA_LIB EMPTY LIB_STACK Hj HG' frame_RELRO_src0 (H rc fx j Hj))
    sp brk0 mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinput Hlim).
  unfold rc. apply ceil_of_top_run.
Qed.

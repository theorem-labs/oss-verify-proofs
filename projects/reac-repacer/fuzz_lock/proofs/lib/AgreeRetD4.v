(* Modified by Theorem Labs: the twin of lib/AgreeTop.v plain_rz_of_contracts_R and of the plain half of lib/AgreeFrame.v ubsan_agrees_of_slots (no licence line) for a return value of the fuzz target of 0 or -1 *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/AgreeTop.v and lib/AgreeFrame.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.AgreeRetD4. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_lock Require Statements Images.
From OSSVerify.reac_repacer.fuzz_lock.images Require Plain.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0d YO05 YO09 YO06 YO04
  YH00 YH02 YI14 YI5b YI5c YL01 YL0g YL0i YL0s YL0j.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import
  YP09 YI06 YI16 YL0k YN03 YN2b YN33 DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import
  ZImage TraceHalting TraceHaltingB ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG Agree
  AgreeZlib.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import FrameRet FrameRetD1 FrameRetD2 FrameRetD3 FrameRetD6.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import AgreeRetD1 AgreeRetD3.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* AgreeTop.v plain_rz_of_contracts_R, with SPECX_q: the plain build realizes the trace for the return function rt *)
Theorem plain_rz_of_contracts_R_q : forall (LS : lib_shape) rt RI G R GI f,
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1 ->
  (forall data, leaves (run_RI RI (payload data)) (driver_tree data)) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  zlib_runtime_contracts_R_r LS rt RI G R GI f ->
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
    rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX_q (LS:=LS) rt inp).
Proof.
  intros LS rt RI G R GI f HR01 ARMS HDRV HG HR GIL GI0 HC [sp brk0 mbase rnd] inp Hentry Hinput.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp)).
  destruct (HC rc) as [API [AX LX]].
  change (realizes zsegs (init_config zsegs Plain.M.init_pc Plain.M.phdrs
    sp brk0 mbase rnd Budgets.Standard.lim_source inp) (SPECX_q (LS:=LS) rt inp)).
  apply (src0_realizes_specX_q (rc:=rc) (LS:=LS) API AX GI RI f rt
    (G_local_T_mono src0segs G YL0k.src0_G GI HG GIL)
    (fun mem H => GI0 mem (G_img_mono src0segs G YL0k.src0_G mem HG H))
    (lib_contract_x_R_all_r_mono src0_msyms API rt RI G YL0k.src0_G R YL0k.src0_R GI f LIBPC RA_LIB EMPTY LIB_STACK HG HR LX)
    HR01 ARMS HDRV sp brk0 mbase rnd
    Budgets.Standard.lim_source inp Hsp Hbrk Hmb Hfits Hinput).
  - apply SRC_LIM_MIN_le_source.
  - unfold rc. apply ceil_of_top_run.
Qed.

(* the plain half of AgreeFrame.v ubsan_agrees_of_slots: from Prog/FrameRet.v lib_contract_gr rt at every call *)
Theorem plain_rz_of_gr : forall (LS : lib_shape) (rt : list byte -> Z)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1 ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_gr fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       rt G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
    rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX_q (LS:=LS) rt inp).
Proof.
  intros LS rt G GI HR01 ARMS HROOM HG GIL GI0 Hp.
  assert (HC : zlib_runtime_contracts_R_r LS rt (@RI_G LS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_r_of_T src0_msyms (@zlib_API rc) rt (@RI_G LS) G frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step LS GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_r_of_G src0_msyms (@zlib_API rc) rt G frame_RELRO GI (fun _ => []) j LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_r_of_gr src0_msyms (@zlib_API rc) (zlib_tables rc) rt G frame_RELRO GI j LIBPC RA_LIB EMPTY LIB_STACK
        (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R_q LS rt (@RI_G LS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])
    HR01 ARMS (driver_RI_AG LS HROOM) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs G GI GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.

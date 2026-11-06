From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition SLOT_FRAME : Z := 2592.

Definition disco_GI (j : nat) (m : word -> option byte) : Prop := True.

Definition LLVMFuzzerTestOneInput_contract : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs ->
    ra mod 2 = 0 ->
    ms_malloc B = 0x17330 ->
    ms_free B = 0x171f0 ->
    ms_realloc B = None ->
    ms_calloc B = None ->
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) ->
    ms_guard B = 0x514d0 ->
    ms_got_guard B = 0x1fee8 ->
    ms_ctx B = 0x51568 ->
    ms_lock B = 0x51560 ->
    ms_libc B = 0x514f0 ->
    ms_size_classes B = 0x10620 ->
    ms_small_cnt B = 0x10680 ->
    ms_med_cnt B = 0x1069b ->
    ms_debruijn B = 0x10600 ->
    ms_tp B = 0x31260 ->
    ms_errno_off B = -164 ->
    ms_replaced B = None ->
    ms_vmlock B = None ->
    ms_debruijn_len B = 32 ->
    @sk_ofl_head SH = 0x51920 ->
    @sk_ofl_lock SK = 0x51918 ->
    @sk_threaded SK = 0x514f0 + 1 ->
    empty = 0x31170 ->
    0 < empty < 2 ^ 62 ->
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) ->
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
    (forall a, in_globals frame_RELRO a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
    (forall n b, @lib_delta LS n b = b) ->
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX) ->
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_g fx rc LS B (API rc) SH SK [] frame_RELRO disco_GI j ENTRY ra empty SLOT_STACK.

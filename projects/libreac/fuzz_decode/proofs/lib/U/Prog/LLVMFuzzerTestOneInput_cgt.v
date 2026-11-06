From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import
memcpy memset bcmp check_braid reac_frame_inspect reac_frame_counter reac_decode reac_decode_plain_le
reac_frame_is_reac reac_frame_clean_len reac_upstream_channels reac_upstream_decode reac_braid_encode_exact
check_round_trip_c check_round_trip LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr fd_segments_c fd_down fd_up
LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0 FrameAPI SlotAgree AgreeLift ZAllocator
  FrameProof AllocCf CallocCf AgreeZlib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import Statement LLVMFuzzerTestOneInput_end
  LLVMFuzzerTestOneInput_cfb fd_segments_ccf check_round_trip_ccf LLVMFuzzerTestOneInput_gcg LLVMFuzzerTestOneInput_cg
  check_round_trip_cg fd_down_cg fd_up_cg.
Import ListNotations.
Local Open Scope Z_scope.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FR : llvm_frame rc B API SH SK.
Hypothesis MCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B API.
Hypothesis FCF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis CCF : forall (fx' : YK11.FPState) (pc : Z), @calloc_contract_cf fx' rc B API pc.
Hypothesis LIM : llvm_limlaw B API.

Theorem LLVMFuzzerTestOneInput_holds_cf : LLVMFuzzerTestOneInput_sr_contract_cf B API.
Proof.
  intros BI. pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof FR as (FA & ERRNO_LOW & CALPC & _).
  pose proof (llvm_sink_env rc B API SH SK BI FR) as SINK.
  assert (MALPC : ms_malloc B = 0x14df4) by exact HMAL.
  assert (FREEPC : ms_free B = 0x14cb4) by exact HFRE.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API)
    by (intros fx'; exact (malloc_ag_of_cf B API LIM (MCF fx'))).
  pose proof FCF as FREE.
  destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & BND & _).
  pose proof reac_braid_encode_exact_holds as ENC. pose proof bcmp_holds as BC.
  assert (CRT : forall fx' : YK11.FPState, @check_round_trip_contract_cf fx' rc B API).
  { intros fx'. destruct (FA fx') as (_ & _ & _ & _ & _ & _ & CT' & _).
    pose proof (calloc_ag_of_cf B API 0x14b7c LIM (CCF fx' 0x14b7c)) as CAL'.
    pose proof (malloc_ag_of_cf B API LIM (MCF fx')) as MAL'.
    eapply (check_round_trip_holds_cf (fx := fx')); eassumption. }
  pose proof reac_frame_inspect_holds as IHI. pose proof reac_frame_counter_holds as IHC.
  pose proof memset_holds as IMS. pose proof (reac_decode_holds IHI) as IDE. pose proof check_braid_holds as ICB.
  pose proof (reac_decode_plain_le_holds IHI) as IPL.
  pose proof reac_upstream_channels_holds as IUC. pose proof reac_upstream_decode_holds as IUD.
  assert (DOWN : forall fx' : YK11.FPState, fd_down_contract_cf (fx := fx') B API).
  { intros fx'. eapply (fd_down_holds_cf (fx := fx')); eassumption. }
  assert (UP : forall fx' : YK11.FPState, fd_up_contract_cf (fx := fx') B API).
  { intros fx'. eapply (fd_up_holds_cf (fx := fx')); eassumption. }
  refine (LLVMFuzzerTestOneInput_holds_of_cf B API MALLOC FREE ERRNO_LOW SINK BND memcpy_holds
    reac_frame_is_reac_holds reac_frame_clean_len_holds DOWN UP BI).
Qed.

Theorem llvm_cg_holds : LLVMFuzzerTestOneInput_contract_cg B API.
Proof. apply llvm_g_of_sr_cf. exact LLVMFuzzerTestOneInput_holds_cf. Qed.

End L.

Theorem decode_slot_cg_frame : forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room_cf b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros LS HK HR HD rc fx j Hj.
  apply (@llvm_cg_holds fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  - unfold llvm_frame. split; [exact (zlib_frame_allocator rc)|]. split; [exact (errno_below_ceiling rc)|].
    repeat split; vm_compute; reflexivity.
  - intros fx'. exact (@zlib_malloc_contract_cf fx' rc).
  - intros fx'. exact (@zlib_free_contract_cf fx' rc).
  - intros fx' pc. exact (@zlib_calloc_contract_cf fx' rc pc).
  - exact (zlib_limit rc).
  - unfold llvm_binds. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc).
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.

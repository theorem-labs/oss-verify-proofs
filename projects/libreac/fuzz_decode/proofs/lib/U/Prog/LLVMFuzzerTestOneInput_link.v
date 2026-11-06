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
Import ListNotations.
Local Open Scope Z_scope.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis CALPC : ms_calloc B = Some 0x14b7c.
Hypothesis SINK : lf_sink_env B.

Theorem LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros BI. pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  assert (MALPC : ms_malloc B = 0x14df4) by exact HMAL.
  assert (FREEPC : ms_free B = 0x14cb4) by exact HFRE.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & BND & _).
  pose proof reac_braid_encode_exact_holds as ENC. pose proof bcmp_holds as BC.
  assert (CRT : forall fx' : YK11.FPState, @check_round_trip_contract fx' rc B API).
  { intros fx'. destruct (FA fx') as (M' & _ & _ & _ & HC' & _ & CT' & _).
    pose proof (HC' 0x14b7c CALPC) as CAL'.
    eapply (check_round_trip_holds (fx := fx')); eassumption. }
  pose proof reac_frame_inspect_holds as IHI. pose proof reac_frame_counter_holds as IHC.
  pose proof memset_holds as IMS. pose proof (reac_decode_holds IHI) as IDE. pose proof check_braid_holds as ICB.
  pose proof (reac_decode_plain_le_holds IHI) as IPL.
  pose proof reac_upstream_channels_holds as IUC. pose proof reac_upstream_decode_holds as IUD.
  assert (DOWN : forall fx' : YK11.FPState, fd_down_contract (fx := fx') B API).
  { intros fx'. eapply (fd_down_holds (fx := fx')); eassumption. }
  assert (UP : forall fx' : YK11.FPState, fd_up_contract (fx := fx') B API).
  { intros fx'. eapply (fd_up_holds (fx := fx')); eassumption. }
  refine (LLVMFuzzerTestOneInput_holds_of B API MALLOC FREE ERRNO_LOW SINK BND memcpy_holds
    reac_frame_is_reac_holds reac_frame_clean_len_holds DOWN UP BI).
Qed.

End L.

(* fuzz_lock.ubsan's LLVMFuzzerTestOneInput meets U/Prog/FrameRet.v's lib_contract_gr for the return lock_ret,
   from the contracts of check_no_overread and check_lookup: libreac/fuzz_decode's released
   lib/U/Prog/LLVMFuzzerTestOneInput_end.v (25e3d17bdb50) at fuzz_lock's addresses. Written by Theorem Labs.
   *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet check_no_overread_c check_lookup_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_g.
Import ListNotations.
Local Open Scope Z_scope.

Lemma llvm_find_img_range : forall B lo n a, ms_segs B = rsegs -> find_segment rsegs lo n <> None ->
  lo <= a < lo + n -> in_img B a.
Proof.
  intros B lo n a HS E Ha. destruct (find_segment rsegs lo n) as [seg|] eqn:F; [|contradiction].
  destruct (lf_find_segment_in rsegs lo n seg F) as (Hin & H1 & H2).
  destruct (lf_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; exact lf_rsegs_nonnil|].
  exists (segment_reservation seg). split; [rewrite HS; unfold segments_reserved; apply in_map; exact Hin | lia].
Qed.

(* the facts of U/FrameAPI.v frame_ubsan that the walk of LLVMFuzzerTestOneInput needs *)
Definition llvm_frame {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms)
    : Prop :=
  (forall fx : FPState, @frame_allocator rc fx B API) /\ errno_addr B + 4 <= @alloc_ceiling rc /\
  ms_ctx B = 0x4e178 /\ ms_lock B = 0x4e170 /\ ms_libc B = 0x4e100 /\ ms_size_classes B = 0x10434 /\
  ms_small_cnt B = 0x10494 /\ ms_med_cnt B = 0x104af /\ ms_debruijn B = 0x10414 /\ ms_tp B = 0x2de70 /\
  ms_errno_off B = -164 /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
  @sk_ofl_head SH = 0x4e530 /\ @sk_ofl_lock SK = 0x4e528 /\ @sk_threaded SK = 0x4e100 + 1.

Lemma llvm_sink_env : forall rc B API SH SK,
  llvm_binds B API -> @llvm_frame rc B API SH SK -> @lf_sink_env B SH SK.
Proof.
  intros rc B API SH SK (HS & _ & _ & HGG & HG & _)
    (_ & _ & Hctx & Hlock & Hlibc & Hsc & Hsmall & Hmed & Hdb & Htp & Heo & Hvml & Hdbl & Hhead & Hlk & Hthr).
  intros a Ha. unfold lf_sink_addr in Ha. rewrite Hhead, Hlk, Hthr in Ha.
  split; [apply (llvm_find_img_range B 0x4e100 0x440 a HS); [vm_compute; discriminate | lia]|].
  split; [unfold static_owned, vml_lo, vml_len; rewrite Hlock, Hlibc, HGG, HG, Hdb, Hsc, Hsmall, Hmed, Hvml, Hdbl;
    unfold LLVM_GUARD_GOT, LLVM_GUARD; lia|].
  split; [rewrite Hctx; unfold CTX_SIZE; lia|].
  unfold errno_addr. rewrite Htp, Heo. lia.
Qed.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FR : @llvm_frame rc B API SH SK.
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API.
Hypothesis CL : forall fx' : YK11.FPState, @check_lookup_contract fx' rc B API.

Theorem llvm_contract : LLVMFuzzerTestOneInput_contract B API.
Proof.
  apply llvm_g_of_sr. intros BI.
  pose proof FR as (HA & Hel & _).
  exact (LLVMFuzzerTestOneInput_holds_of B API Hel (llvm_sink_env rc B API SH SK BI FR) CNO CL BI).
Qed.

End E.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_end.v, with its module paths and addresses changed; 4 of its 51 lines of code are new or changed. *)
(* Modified by Theorem Labs: libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_end.v for
   libdiginet/fuzz_decode, module paths changed and the image values moved: the sink words of this image (ofl_lock
   0x4f378, ofl_head 0x4f380..0x4f388, threaded ms_libc + 1 = 0x4ef51) all lie in [0x4ef50, 0x4ef50 + 0x440), inside
   the last PT_LOAD [0x1e960, 0x4f798) of fuzz_decode.ubsan. The unit links no calloc, so llvm_contract hands the
   link no calloc pc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_g LLVMFuzzerTestOneInput_link Statement.
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

Lemma llvm_sink_env : forall rc B API SH SK,
  llvm_binds B API -> llvm_frame rc B API SH SK -> @lf_sink_env B SH SK.
Proof.
  intros rc B API SH SK (HS & _ & _ & HGG & HG & _)
    (_ & _ & _ & Hctx & Hlock & Hlibc & Hsc & Hsmall & Hmed & Hdb & Htp & Heo & Hvml & Hdbl & Hhead & Hlk & Hthr).
  intros a Ha. unfold lf_sink_addr in Ha. rewrite Hhead, Hlk, Hthr in Ha.
  split; [apply (llvm_find_img_range B 0x4ef50 0x440 a HS); [vm_compute; discriminate | lia]|].
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
Hypothesis FR : llvm_frame rc B API SH SK.

Theorem llvm_contract : LLVMFuzzerTestOneInput_contract B API.
Proof.
  apply llvm_g_of_sr. intros BI.
  pose proof FR as (HA & Hel & _).
  exact (LLVMFuzzerTestOneInput_holds B API HA Hel (llvm_sink_env rc B API SH SK BI FR) BI).
Qed.

End E.

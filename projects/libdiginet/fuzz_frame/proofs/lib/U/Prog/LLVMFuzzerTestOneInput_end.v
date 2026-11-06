(* ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/LLVMFuzzerTestOneInput_end.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; the sink words of fuzz_frame.ubsan (ofl_head 0x4f250, ofl_lock 0x4f248, libc.threaded 0x4ee21) lie in [__libc, __libc + 0x438) = [0x4ee20, 0x4f258), inside the data segment; llvm_contract takes the SR contract of LLVMFuzzerTestOneInput (U/Prog/Statement.v slot_sr_all) as a hypothesis in place of decode's lib/U/Prog/LLVMFuzzerTestOneInput_link.v, the walk of the harness; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_g Statement.
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
  split; [apply (llvm_find_img_range B 0x4ee20 0x438 a HS); [vm_compute; discriminate | lia]|].
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
Hypothesis SRA : slot_sr_all.

Theorem llvm_contract : LLVMFuzzerTestOneInput_contract B API.
Proof.
  apply llvm_g_of_sr. exact (SRA rc fx LS B API SH SK FR).
Qed.

End E.

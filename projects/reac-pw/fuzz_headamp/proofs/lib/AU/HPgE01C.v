(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): segment E01 of the walk of
   LLVMFuzzerTestOneInput (0x80c40), ENTRY 0x80c40 -> C1 0x80fcc, chained from the statements of its four parts
   (lib/AU/HPgE01D.v): the prologue to the frame call's return 0x80cc4, the frame's header and shadow to 0x80f10, the
   two harness bytes to the malloc entry 0x530e0, and the malloc(pp) call to C1. Each part's end facts are the next
   part's start facts, so the chain is three SRr_bind steps. Proves no function (kind: segment lemma, the chaining
   of its parts). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSegM HPgE01D.
Import ListNotations.
Local Open Scope Z_scope.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* E01 at image B's segments from its four parts. *)
Lemma hqu_E01_chain :
e01u_pro_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
e01u_hdr_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
e01u_body_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
e01u_call_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
hqu_S_E01_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros Ppro Phdr Pbody Pcall hx HB.
eapply SRr_bind; [exact (Ppro hx HB)|].
intros W1 c1 _ (pos1 & e1 & ly1 & S1 & regs1 & mem1 & md1 & -> & HF1).
eapply SRr_bind; [exact (Phdr hx pos1 e1 ly1 S1 W1 regs1 mem1 md1 HB HF1)|].
intros W2 c2 _ (pos2 & e2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HF2).
eapply SRr_bind; [exact (Pbody hx pos2 e2 ly2 S2 W2 regs2 mem2 md2 HB HF2)|].
intros W3 c3 _ (pos3 & e3 & rest3 & ly3 & S3 & regs3 & mem3 & md3 & -> & HF3).
exact (Pcall hx pos3 e3 rest3 ly3 S3 W3 regs3 mem3 md3 HB HF3).
Qed.
End p.

Print Assumptions hqu_E01_chain.

(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections other than
   .note.gnu.build-id are byte-equal to the pin's): segment E01 of the walk of LLVMFuzzerTestOneInput (0x80bc0), ENTRY 0x80bc0 -> C1
   0x80e94, lib/A/HPgE01D.v's hq_S_E01_stmt, chained from the four parts lib/A/HPgE01D.v splits it into:
   e01_pro_stmt (ENTRY -> 0x80c40, lib/A/HPgE01P.v e01_pro_ok), e01_hdr_stmt (-> 0x80dfc, lib/A/HPgE01H.v
   e01_hdr_ok), e01_body_stmt (-> the malloc entry 0x53060, lib/A/HPgE01B.v e01_body_ok) and e01_call_stmt (the
   malloc call -> C1, lib/A/HPgE01M.v e01_call_ok), each an SRr to the next part's start, by SRr_bind.

   THE SECTION HYPOTHESES of headamp_E01_ok, the union of the four parts' (each part's file names them too):
   HSTK : 0x1f0 + ASTACK <= LLVMF_STK (the real frame and the callees' stack inside the harness's window);
   errno_low : api_env rsegs B; ML : model_laws (as_universe B);
   ASM4 : astack_malloc_realizes rsegs B 4 and HSM4 : pc_stack_malloc (as_code B) 4 = A_SM4 (the class-4 frame
   request; the port of the side stack's class-4 walk gives both);
   HGOT / HSC / HGU / HUC : the symbol record's two .got words and the runtime cells they hold (0x9c370 ->
   0xa4db8, 0x9c3c8 -> 0xa4dc0);
   HAE : 0 < A_EMPTY < kLowMemEnd (the empty input's address);
   AMALLOC : amalloc_realizes rsegs B and HBmalloc : pc_wrap_malloc (as_code B) = E01_MALLOC (the malloc call);
   HTRACE : e01_trace_stmt B RA_LLVMF (the allocation trace of the call site 0x80e94);
   HEV : 1 <= EV_LIB and HLIVE : Layout.PP_SIZE <= LIVE_LIB (the harness's event and live-byte budgets).
   Proves no function on its own (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSegM HPgCalls HPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgE01P HPgE01H HPgE01B HPgE01M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* The chaining: ENTRY -> 0x80c40 -> 0x80dfc -> 0x53060 -> C1. *)
Lemma e01_of_parts :
e01_pro_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
e01_hdr_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
e01_body_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
e01_call_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
hq_S_E01_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros PRO HDR BODY CALL hx HB.
eapply SRr_bind; [exact (PRO hx HB)|].
intros W1 c1 _ (pos1 & e1 & ly1 & S1 & regs1 & mem1 & md1 & Ec1 & HF). subst c1.
eapply SRr_bind; [exact (HDR hx pos1 e1 ly1 S1 W1 regs1 mem1 md1 HB HF)|].
intros W2 c2 _ (pos2 & e2 & ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HH). subst c2.
eapply SRr_bind; [exact (BODY hx pos2 e2 ly2 S2 W2 regs2 mem2 md2 HB HH)|].
intros W3 c3 _ (pos3 & e3 & rest & ly3 & S3 & regs3 & mem3 & md3 & Ec3 & HC). subst c3.
exact (CALL hx pos3 e3 rest ly3 S3 W3 regs3 mem3 md3 HB HC).
Qed.
End b.

(* ======================================== E01 ======================================== *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x1f0 + ASTACK <= LLVMF_STK.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis HSM4 : pc_stack_malloc (as_code B) 4 = A_SM4.
Hypothesis HGOT : as_got_shadow B = E01_GOT_SH.
Hypothesis HSC : as_shadow_cell B = E01_SHC.
Hypothesis HGU : as_got_uar B = E01_GOT_UAR.
Hypothesis HUC : as_uar_cell B = E01_UAR.
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis HBmalloc : pc_wrap_malloc (as_code B) = E01_MALLOC.
Hypothesis HTRACE : e01_trace_stmt B RA_LLVMF.
Hypothesis HEV : 1 <= EV_LIB.
Hypothesis HLIVE : Layout.PP_SIZE <= LIVE_LIB.

Theorem headamp_E01_ok : hq_S_E01_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
apply e01_of_parts.
- eapply HPgE01P.e01_pro_ok; eassumption.
- eapply HPgE01H.e01_hdr_ok; eassumption.
- eapply HPgE01B.e01_body_ok; eassumption.
- eapply HPgE01M.e01_call_ok; eassumption.
Qed.
End t.

Print Assumptions e01_of_parts.
Print Assumptions headamp_E01_ok.

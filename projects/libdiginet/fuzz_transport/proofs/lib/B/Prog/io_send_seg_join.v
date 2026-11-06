(* io_send_seg_join: the back half of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry
   0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), joined: from the frame-in-flight
   cut (0x832c0 = transportb_text + IOS_FLY, lib/B/Prog/io_send_seg_cut.v ios_tail_at at the world Bx) through
   ios_fly_seg_stmt (the stores into M.fly and __asan_memcpy, to IOS_EPI at the world ios_fly frame Bx) and
   ios_epi_stmt (the epilogue) to the walk's post ios_post. The cut facts at IOS_FLY are the common currency of the
   DATA tail's exit and of the E2 arm's. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section join. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Lemma ios_fly_post_of : @ios_fly_seg_stmt fx rc B MT -> @ios_epi_stmt fx rc B MT ->
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) p frame Bw Bx ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_tail_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 Bx ->
  60 <= Z.of_nat (length frame) -> Z.of_nat (length frame) < 2 ^ 32 ->
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  YK11.getr regs2 8 = w64 (Z.of_nat (length frame)) -> YK11.getr regs2 9 = w64 p ->
  YK11.getr regs2 19 = w64 (TW.g_fail_next Bw) ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_FLY) regs2 mem2 md2)
    (ios_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame (ios_fly frame Bx) (ios_ret Bw)).
Proof.
  intros HFLY HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bx ly2 S2 W2 mem2 md2 regs2
    HL HF HT H60 H32 R2 R3 R4 R8 R9 R19 R24.
  apply (HFLY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bx ly2 S2 W2 mem2 md2 regs2 _
           HL HF HT H60 H32 R2 R3 R4 R8 R9 R19 R24).
  intros mem3 md3 regs3 HC HS Q2 Q3 Q4 Q19 Q24 HTW.
  exact (HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw (ios_fly frame Bx)
           ly2 S2 W2 mem3 md3 regs3 HL HF HC HS Q2 Q3 Q4 Q19 Q24 HTW).
Qed.

End join.

(* io_send_seg_head: the head of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry 0x82ffc =
   TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), from the entry to the return of
   check_sent_frame (0x83064 = transportb_text + IOS_CSF), composed from the two segment statements of
   lib/B/Prog/io_send_seg_cut.v:
     ios_entry_stmt    the prologue, g_fail_next and the call of spec_read_frame, to the cut ios_at_srf;
     ios_csf_seg_stmt  the call of check_sent_frame, to the cut ios_at_csf.
   The model premise gives check_sent_frame's model call at ios_B0 Bw (io_send_seg_cut.v ios_m_arm_B), which both
   take. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section head. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Lemma ios_head_of : @ios_entry_stmt fx rc B MT -> @ios_csf_seg_stmt fx rc B MT ->
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
    p frame Bw Bw' r (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  TC.io_send_m timg_B Bw frame = Some (Bw', r) ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 regs3,
     ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W3 mem3 md3 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_CSF) regs3 mem3 md3) Q) ->
  SRr segs W (@cfg_at fx segs (TI.ti_io_send timg_B) regs memc mdc) Q.
Proof.
  intros HENT HCSF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' r Q HL HF HM K.
  destruct (ios_m_arm_B Bw frame Bw' r HM) as (Hcsf & _ & _).
  apply (HENT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Q HL HF Hcsf).
  intros ly2 S2 W2 mem2 md2 regs2 HAT.
  exact (HCSF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
           HL HF Hcsf HAT K).
Qed.

End head.

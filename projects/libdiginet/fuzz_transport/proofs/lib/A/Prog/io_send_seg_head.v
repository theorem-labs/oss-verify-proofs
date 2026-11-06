(* io_send_seg_head: the head of the image-A walk of io_send, from the statement's entry (0x82d60) to the return of
   check_sent_frame (0x83088 = transport_text + IOS_CSF), composed from three proved segments:
     lib/A/Prog/io_send_seg_entry.v  ios_entry      the prologue and __asan_memset, to the cut ios_at_parse;
     lib/A/Prog/io_send_seg_parse.v  ios_parse_seg  the header parse and the body sum, to 0x83074;
     lib/A/Prog/io_send_seg_csf.v    ios_csf_seg    the store of f.code and the call of check_sent_frame, to the cut
                                                    ios_at_csf.
   The model premise gives check_sent_frame's model call (lib/A/Prog/io_send_segs.v ios_m_arm) and the frame's
   60 bytes (lib/A/Prog/io_send_seg_frm.v ios_len60) that ios_csf_seg takes. The parse ends in the conjuncts of
   io_send_seg_cut.v ios_at_join and one more (the four code bytes are 0), which the join drops. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_segs io_send_seg_frm io_send_seg_cut io_send_seg_entry io_send_seg_parse io_send_seg_csf.
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

Lemma ios_head : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
    p frame Bw Bw' r (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  TC.io_send_m timg_A Bw frame = Some (Bw', r) ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 regs3,
     ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W3 mem3 md3 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_CSF) regs3 mem3 md3) Q) ->
  SRr segs W (@cfg_at fx segs (TI.ti_io_send timg_A) regs memc mdc) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' r Q HL HF HM K.
  destruct (ios_m_arm Bw frame Bw' r HM) as (Hcsf & _ & _).
  pose proof (ios_len60 _ _ _ Hcsf) as H60.
  eapply ios_entry; [exact HL | exact HF |].
  intros ly2 S2 W2 mem2 md2 regs2 HP.
  eapply ios_parse_seg; [exact HL | exact HF | exact HM | exact HP |].
  intros mem3 md3 regs3 (J1 & J2 & J3 & J4 & J5 & J6 & _ & J8 & J9 & J10 & J11).
  eapply ios_csf_seg; [exact HL | exact HF | exact Hcsf | exact H60 | |].
  - exact (conj J1 (conj J2 (conj J3 (conj J4 (conj J5 (conj J6 (conj J8 (conj J9 (conj J10 J11))))))))).
  - exact K.
Qed.

End head.

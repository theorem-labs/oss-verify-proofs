(* io_send_seg_e2w: the E2 / DATA head of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry
   0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), 0x830cc .. 0x83144, composed from
   the four segment statements of lib/B/Prog/io_send_seg_cut.v:
     ios_e2_head_stmt  the load of f.retry and its branch (0x830cc .. 0x830d0);
     ios_rty_arm_stmt  the retry arm (0x830d4 .. 0x83104), to the epilogue;
     ios_e2_test_stmt  a0 = f.cmd against 0xe2 (0x83108 .. 0x8310c): the DATA arm's head or the E2 arm;
     ios_e2_arm_stmt   the E2 arm (0x83110 .. 0x83144), to the frame in flight or the epilogue.
   ios_e2_seg_stmt is the stretch's statement: from the dispatch's E2 / DATA exit (io_send_seg_cut.v ios_at_csf, a0 =
   f.cmd) to the DATA arm's head (ios_at_csf), the frame in flight (ios_e2_at at the world B5 with Bw' = ios_fly frame
   B5) and the epilogue (ios_e2_at at Bw'). *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
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
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section e2w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Definition ios_e2_seg_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame : list byte) (cmd : Z) (Bw Bw' : list byte)
         ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_laws B MT ->
    ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
    YK11.getr regs2 10 = w64 cmd ->
    cmd = DSpec.sf_cmd (TC.rf frame) -> 0 <= cmd < 256 ->
    (cmd = TC.SPEC_CMD_E2 \/ cmd = TC.SPEC_CMD_DATA) ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    ios_arm Bw frame = Some (Bw', tt) ->
    (forall ly3 S3 mem3 md3 regs3,
       cmd = TC.SPEC_CMD_DATA -> TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
       ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W2 mem3 md3 regs3 ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_DATA) regs3 mem3 md3) Q) ->
    (forall ly3 S3 mem3 md3 regs3 B5,
       cmd = TC.SPEC_CMD_E2 -> TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
       TC.truth (TW.g_fail_next Bw) = false -> Bw' = ios_fly frame B5 ->
       ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
         ly3 S3 W2 mem3 md3 regs3 B5 ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_FLY) regs3 mem3 md3) Q) ->
    (forall ly3 S3 (W3 : world segs) mem3 md3 regs3,
       ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
         ly3 S3 W3 mem3 md3 regs3 Bw' ->
       SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_EPI) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_E2DATA) regs2 mem2 md2) Q.

(* f.retry = 0 is the model's truth test false. *)
Lemma ie2w_truth0 : forall frame, ios_e2_rty frame = 0 -> TC.truth (DSpec.sf_retry (TC.rf frame)) = false.
Proof. intros frame H. unfold ios_e2_rty in H. unfold TC.truth. rewrite H. reflexivity. Qed.

Lemma ios_e2_seg_of : @ios_e2_head_stmt fx rc B MT -> @ios_e2_test_stmt fx rc B MT ->
  @ios_rty_arm_stmt fx rc B MT -> @ios_e2_arm_stmt fx rc B MT -> ios_e2_seg_stmt.
Proof.
  intros HHEAD HTEST HRTY HARM.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame cmd Bw Bw' ly2 S2 W2 mem2 md2 regs2 Q
    HL HF HAT Ha0 Hcmd Hcr Hcase Hcsf Harm KDATA KFLY KEPI.
  apply (HHEAD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw (TW.g_fail_next Bw) cmd
           ly2 S2 W2 mem2 md2 regs2 (ios_B0 Bw) Q HL HF HAT Ha0).
  - (* f.retry <> 0: the retry arm *)
    intros mem4 md4 regs4 HAT4 Hr.
    exact (HRTY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' ly2 S2 W2 mem4 md4 regs4
             Q HL HF HAT4 ltac:(rewrite <- Hcmd; exact Hcase) Hr Hcsf Harm KEPI).
  - (* f.retry = 0: f.cmd against 0xe2 *)
    intros mem4 md4 regs4 HAT4 Ha4 Hr.
    pose proof (ie2w_truth0 frame Hr) as Hrt.
    apply (HTEST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw (TW.g_fail_next Bw) cmd
             ly2 S2 W2 mem4 md4 regs4 (ios_B0 Bw) Q HL HF HAT4 Ha4 Hcr).
    + intros mem5 md5 regs5 HAT5 Hne.
      assert (Hd : cmd = TC.SPEC_CMD_DATA) by (destruct Hcase as [He|He]; [exfalso; exact (Hne He) | exact He]).
      exact (KDATA ly2 S2 mem5 md5 regs5 Hd Hrt HAT5).
    + intros mem5 md5 regs5 HAT5 He.
      apply (HARM STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' ly2 S2 W2 mem5 md5 regs5
               Q HL HF HAT5 ltac:(rewrite <- Hcmd; exact He) Hr Hcsf Harm).
      * intros ly6 S6 mem6 md6 regs6 B5 Hf HBw HAT6.
        exact (KFLY ly6 S6 mem6 md6 regs6 B5 He Hrt Hf HBw HAT6).
      * exact KEPI.
Qed.

End e2w.

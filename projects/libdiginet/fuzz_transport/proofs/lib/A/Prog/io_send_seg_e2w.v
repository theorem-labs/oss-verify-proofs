(* io_send_seg_e2w: lib/A/Prog/io_send_seg_e2.v's segment statement ios_e2_seg_stmt (the retry and E2 arms,
   0x830e8 .. 0x8315c), proved by composing the four pieces of the stretch:
     io_send_seg_e2.v   ios_e2_head   the load of f.retry and its branch (0x830e8 .. 0x830ec);
     io_send_seg_rty.v  ios_rty_arm   the retry arm (0x830f0 .. 0x83120), to the epilogue;
     io_send_seg_e2.v   ios_e2_test   s5 against 0xe2 (0x83124 .. 0x83128): the DATA arm's head or the E2 arm;
     io_send_seg_e2a.v  ios_e2_arm    the E2 arm (0x8312c .. 0x8315c), to the frame in flight or the epilogue.
   ios_e2_fix_of reads the stretch's fixed facts off io_send_seg_cut.v ios_fix. *)
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
  io_send_segs io_send_seg_frm io_send_seg_cut io_send_seg_e2 io_send_seg_rty io_send_seg_e2a.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section e2w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* The stretch's fixed facts: the frame against io_send's window and the window itself, from the entry journal. *)
Lemma ios_e2_fix_of : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    regs p frame Bw,
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  60 <= Z.of_nat (length frame) ->
  ios_e2_fix B STK sp0 regs p frame.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HF H60.
  pose proof HF as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & HG8 & HSRC & HOFF & HFAT &
                    Hfail & HROM & HTW & HFLY & HCMD & HEV).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     (Hs16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
  unfold ios_e2_fix.
  split; [exact Hp0|]. split; [lia|]. split; [exact HOFF|]. split; [exact Hsp16|].
  split; [exact Hlo|]. split; [exact Hhi|]. split; [lia|]. split; [lia|].
  split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp | exact Htp].
Qed.

Lemma ios_e2_seg : @ios_e2_seg_stmt fx rc B MT.
Proof.
  unfold ios_e2_seg_stmt.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame cmd Bw Bw' ly2 S2 W2 mem2 md2 regs2 Q
    HL HF HAT R21 Hcmd H256 Hcmd2 Hcsf Harm KDATA KFLY KEPI.
  pose proof HL as (HCELLS & LAWS & MTL & HGX & HGE & HCIR & HCSW & HCLC).
  pose proof (ios_len60 _ _ _ Hcsf) as H60.
  pose proof (ios_e2_fix_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HF H60) as FIX.
  pose proof HF as (HJ & _).
  assert (HARc : @AR rc segs B lyc Sc W memc mdc) by (eapply ajournal_gx_AR; exact HJ).
  pose proof (ios_e2_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw
                ly2 S2 W2 mem2 md2 regs2 HAT) as AT.
  apply (ios_e2_head B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame (TW.g_fail_next Bw) cmd
           ly2 S2 W2 mem2 md2 regs2 (ios_B0 Bw) Q LAWS HGX HARc FIX AT R21).
  - (* f.retry <> 0: the retry arm *)
    intros mem4 md4 regs4 AT4 R214 Hr.
    exact (ios_rty_arm B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame cmd Bw Bw'
             ly2 S2 W2 mem4 md4 regs4 Q HL HF AT4 R214 Hcmd Hcmd2 Hr Hcsf Harm KEPI).
  - (* f.retry = 0: E2 or DATA *)
    intros mem4 md4 regs4 AT4 R214 Hr.
    assert (Hrt : TC.truth (DSpec.sf_retry (TC.rf frame)) = false)
      by (unfold TC.truth; unfold ios_e2_rty in Hr; rewrite Hr; reflexivity).
    apply (ios_e2_test B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame (TW.g_fail_next Bw) cmd
             ly2 S2 W2 mem4 md4 regs4 (ios_B0 Bw) Q LAWS HGX HARc FIX AT4 R214 H256).
    + intros mem5 md5 regs5 AT5 R215 Hne.
      assert (HD : cmd = TC.SPEC_CMD_DATA) by (destruct Hcmd2 as [E|E]; [exfalso; exact (Hne E) | exact E]).
      exact (KDATA ly2 S2 mem5 md5 regs5 HD Hrt AT5 R215).
    + intros mem5 md5 regs5 AT5 R215 Heq.
      exact (ios_e2_arm B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame cmd Bw Bw'
               ly2 S2 W2 mem5 md5 regs5 Q HL HF AT5 R215 Hcmd Heq Hr Hcsf Harm KFLY KEPI).
Qed.

End e2w.

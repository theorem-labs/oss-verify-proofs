(* io_send_seg_top: the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry 0x82ffc = TImgB.v
   ti_io_send timg_B), composed at the level of the segment statements of lib/B/Prog/io_send_seg_cut.v:
   ios_holds_of turns the thirteen segment statements into lib/B/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt. The paths, from the entry:
     io_send_seg_head.v ios_head_of     entry .. IOS_CSF (spec_read_frame, check_sent_frame);
     ios_ack_seg_stmt                   the dispatch on f.cmd: ACK, E3 and any other cmd byte to the epilogue,
                                        E2 / DATA on (a0 = f.cmd);
     io_send_seg_e2w.v ios_e2_seg_of    the retry arm and the E2 arm (to the epilogue or the frame in flight), DATA
                                        on;
     io_send_seg_dpost.v ios_data_post_of  the DATA arm to the post;
     io_send_seg_join.v ios_fly_post_of    the frame in flight and the epilogue, to the post;
     ios_epi_stmt                       the epilogue, to the post.
   The model premise is split once (io_send_seg_cut.v ios_m_arm_B): check_sent_frame's call at ios_B0 Bw, the
   dispatch ios_arm Bw frame = Some (Bw', tt), and r = ios_ret Bw; the frame's length facts are
   io_send_seg_frm.v ios_len60 and io_send_seg_cut.v ios_len_lt32. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  io_send_seg_cut io_send_seg_head io_send_seg_e2w io_send_seg_join io_send_seg_dpost.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Lemma ios_holds_of :
  @ios_entry_stmt fx rc B MT -> @ios_csf_seg_stmt fx rc B MT -> @ios_ack_seg_stmt fx rc B MT ->
  @ios_e2_head_stmt fx rc B MT -> @ios_e2_test_stmt fx rc B MT -> @ios_rty_arm_stmt fx rc B MT ->
  @ios_e2_arm_stmt fx rc B MT -> @iod_head_stmt fx rc B MT -> @ios_loop_stmt fx rc B MT ->
  @iod_mid_stmt fx rc B MT -> @ios_tail_seg_stmt fx rc B MT -> @ios_fly_seg_stmt fx rc B MT ->
  @ios_epi_stmt fx rc B MT ->
  @transport_io_send_cg_holds_stmt fx rc B MT.
Proof.
  intros HENT HCSF HACK HE2H HE2T HRTY HE2A HDH HLOOP HDM HTAIL HFLY HEPI.
  unfold transport_io_send_cg_holds_stmt.
  intros HCELLS HIOC HRU HRE LAWS MTL HGX HGE HSRF HCSFc HCAF HCLC HCIR HCSW HCIN HTOF HCLF HCKD HCLS HCLD HAI1.
  assert (HL : ios_laws B MT)
    by exact (conj HCELLS (conj HIOC (conj HRU (conj HRE (conj LAWS (conj MTL (conj HGX (conj HGE (conj HSRF
               (conj HCSFc (conj HCAF (conj HCLC (conj HCIR (conj HCSW (conj HCIN (conj HTOF (conj HCLF
               (conj HCKD (conj HCLS (conj HCLD HAI1)))))))))))))))))))).
  unfold transport_io_send_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p r frame Bw Bw'
    HJ Hra Hra4 Hgp Htp H11 H12 Hsp16 Hlo Hhi Hp0 HG8 HSRC HOFF HFAT Hfail HROM HTW HM HFLY1 HCMD HEV.
  assert (HF : ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw)
    by exact (conj HJ (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H11 (conj H12 (conj Hsp16 (conj Hlo
               (conj Hhi (conj Hp0 (conj HG8 (conj HSRC (conj HOFF (conj HFAT (conj Hfail (conj HROM (conj HTW
               (conj HFLY1 (conj HCMD HEV)))))))))))))))))))).
  pose proof (ios_m_arm_B Bw frame Bw' r HM) as (Hcsf & Harm & Hr). subst r.
  pose proof (ios_len60 _ _ _ Hcsf) as H60.
  pose proof (ios_len_lt32 _ _ _ Hcsf) as H32.
  pose proof (ios_sf_code _ _ _ Hcsf) as HOK.
  destruct (ios_fields frame HOK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fcmd & _).
  pose proof (DSpec.at8_range frame 28) as Rcmd. change (2 ^ 8) with 256 in Rcmd.
  assert (H256 : 0 <= DSpec.sf_cmd (TC.rf frame) < 256) by (rewrite Fcmd; unfold DSpec.fr_cmd; exact Rcmd).
  apply (ios_head_of B MT HENT HCSF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
           (ios_ret Bw) _ HL HF HM).
  intros ly3 S3 W3 mem3 md3 regs3 HCAT.
  apply (HACK STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' ly3 S3 W3 mem3 md3 regs3 _
           HL HF HCAT Hcsf Harm).
  - (* f.cmd = 0 or 0xe2 *)
    intros rg2 mem4 md4 Hcmd HAT R10 _ _.
    apply (ios_e2_seg_of B MT HE2H HE2T HRTY HE2A STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame
             (DSpec.sf_cmd (TC.rf frame)) Bw Bw' ly3 S3 W3 mem4 md4 rg2 _ HL HF HAT R10 eq_refl H256 Hcmd
             Hcsf Harm).
    + (* DATA *)
      intros ly5 S5 mem5 md5 regs5 Hd Hrt AT5.
      exact (ios_data_post_of B MT HDH HLOOP HDM HTAIL HFLY HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
               regs p frame Bw Bw' ly5 S5 W3 mem5 md5 regs5 HL HF Hcsf Harm Hd Hrt AT5).
    + (* E2 with bit 0 of g_fail_next clear: the frame in flight *)
      intros ly5 S5 mem5 md5 regs5 B5 _ _ _ HBw AT5.
      rewrite HBw.
      destruct AT5 as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW5).
      pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
      exact (ios_fly_post_of B MT HFLY HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw B5
               ly5 S5 W3 mem5 md5 regs5 HL HF
               (conj CUR (conj SAVED (conj SFR (conj GARR (conj SRCF (conj HOFF (conj HFAT HTW5)))))))
               H60 H32 R2 R3 R4 R8 R9 R19 R24).
    + (* the retry arm, or E2 with that bit set: the epilogue *)
      intros ly5 S5 W5 mem5 md5 regs5 AT5.
      destruct AT5 as (CUR & SAVED & RG & R24 & _ & _ & _ & _ & HTW5).
      pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
      exact (HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
               ly5 S5 W5 mem5 md5 regs5 HL HF CUR SAVED R2 R3 R4 R19 R24 HTW5).
  - (* ACK, E3 or another cmd byte: the epilogue *)
    intros rg2 mem4 md4 CUR SAVED RG R24 HTW4.
    pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
    exact (HEPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
             ly3 S3 W3 mem4 md4 rg2 HL HF CUR SAVED R2 R3 R4 R19 R24 HTW4).
Qed.

End top.

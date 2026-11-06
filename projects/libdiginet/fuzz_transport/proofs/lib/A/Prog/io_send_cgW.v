(* io_send_cgW: Theorem transport_io_send_cg_holds : the statement transport_io_send_cg_holds_stmt of
   lib/A/Prog/io_send_cg.v, the machine walk of io_send (fuzz/fuzz_transport.c:823-899) on fuzz_transport.asan
   (e89be137db17) at 0x82d60 = TImgA.v ti_io_send timg_A (1892 bytes, frame 160, twelve calls).

   The walk is a G-form caller-journal walk (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 [] from the entry to the
   return), split at the cuts of lib/A/Prog/io_send_seg_cut.v into segment files, each proved on its own:
     io_send_seg_head.v  ios_head      entry, __asan_memset, the inlined parse (header and body sum), the store of
                                       f.code and the call of check_sent_frame (gx_call_cg), to IOS_CSF;
     io_send_seg_ack.v   ios_ack_seg   the dispatch on f.cmd, the ACK arm (GOT.acks++, check_ack_frame) and the E3
                                       arm (GOT.e3++), both through check_latest_control, to the epilogue; a cmd
                                       byte that is none of the four goes straight there; E2 / DATA go on;
     io_send_seg_e2w.v   ios_e2_seg    the retry arm (check_inflight_retry, gx_call_cg, M.fly.retries / .sent) and
                                       the E2 arm (check_state_wake, check_latest_control, GOT.e2, g_last_counter),
                                       to the epilogue or the frame in flight; DATA goes on;
     io_send_seg_dpost.v ios_data_post the DATA arm (check_inflight_new, the command count loop, check_latest_frame,
                                       M.host_counter, g_last_counter, the keepalive or check_latest_sent and the
                                       display), the frame in flight and the epilogue, to the post;
     io_send_seg_join.v  ios_fly_post  the frame in flight (six stores into M.fly, __asan_memcpy) and the epilogue;
     io_send_seg_epi.v   ios_epi       the epilogue: a0 = ios_ret Bw, the nine reloads, the post.
   The model premise is split once (lib/A/Prog/io_send_segs.v ios_m_arm): check_sent_frame's call at ios_B0 Bw,
   the dispatch ios_arm Bw frame = Some (Bw', tt), and r = ios_ret Bw; the frame's length facts are
   io_send_seg_frm.v ios_len60 and io_send_seg_join.v ios_len_lt32. *)
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
  io_send_segs io_send_seg_frm io_send_seg_cut io_send_seg_head io_send_seg_ack io_send_seg_e2 io_send_seg_e2w
  io_send_seg_tail io_send_seg_join io_send_seg_epi io_send_seg_dpost.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Lemma ios_holds : @transport_io_send_cg_holds_stmt fx rc B MT.
Proof.
  unfold transport_io_send_cg_holds_stmt.
  intros HCELLS HIOC LAWS MTL HGX HGE HAI0 HCSF HCAF HCLC HCIR HCSW HCIN HCLF HCKD HCLS HCLD HAI1.
  assert (HL : ios_laws B MT)
    by exact (conj HCELLS (conj HIOC (conj LAWS (conj MTL (conj HGX (conj HGE (conj HAI0 (conj HCSF (conj HCAF
               (conj HCLC (conj HCIR (conj HCSW (conj HCIN (conj HCLF (conj HCKD (conj HCLS (conj HCLD
               HAI1))))))))))))))))).
  assert (HL2 : ios_e2_laws B MT)
    by exact (conj HCELLS (conj LAWS (conj MTL (conj HGX (conj HGE (conj HCIR (conj HCSW HCLC))))))).
  unfold transport_io_send_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p r frame Bw Bw'
    HJ Hra Hra4 Hgp Htp H11 H12 Hsp16 Hlo Hhi Hp0 HG8 HSRC HOFF HFAT Hfail HROM HTW HM HFLY HCMD HEV.
  assert (HF : ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw)
    by exact (conj HJ (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H11 (conj H12 (conj Hsp16 (conj Hlo
               (conj Hhi (conj Hp0 (conj HG8 (conj HSRC (conj HOFF (conj HFAT (conj Hfail (conj HROM (conj HTW
               (conj HFLY (conj HCMD HEV)))))))))))))))))))).
  destruct (ios_m_arm Bw frame Bw' r HM) as (Hcsf & Harm & Hr). subst r.
  pose proof (ios_len60 _ _ _ Hcsf) as H60.
  pose proof (ios_len_lt32 _ _ _ Hcsf) as H32.
  pose proof (ios_sf_code _ _ _ Hcsf) as HOK.
  destruct (ios_fields frame HOK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fcmd & _).
  pose proof (DSpec.at8_range frame 28) as Rcmd. change (2 ^ 8) with 256 in Rcmd.
  assert (H256 : 0 <= DSpec.sf_cmd (TC.rf frame) < 256) by (rewrite Fcmd; unfold DSpec.fr_cmd; exact Rcmd).
  apply (ios_head B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' (ios_ret Bw) _
           HL HF HM).
  intros ly3 S3 W3 mem3 md3 regs3 HCAT.
  apply (ios_ack_seg B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
           ly3 S3 W3 mem3 md3 regs3 _ HL HF HCAT Hcsf Harm).
  - (* f.cmd = 0 or 0xe2 *)
    intros rg2 mem4 md4 Hcmd HAT R21 _ _.
    apply (ios_e2_seg B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame
             (DSpec.sf_cmd (TC.rf frame)) Bw Bw' ly3 S3 W3 mem4 md4 rg2 _ HL2 HF HAT R21 eq_refl H256 Hcmd
             Hcsf Harm).
    + (* DATA *)
      intros ly5 S5 mem5 md5 regs5 HD Hrt AT5 R215.
      exact (ios_data_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
               (ios_ret Bw) ly5 S5 W3 mem5 md5 regs5 HL HF HM HD Hrt AT5 R215).
    + (* E2 with bit 0 of g_fail_next clear: the frame in flight *)
      intros ly5 S5 mem5 md5 regs5 B5 _ _ _ HBw AT5 R215.
      rewrite HBw.
      destruct AT5 as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW5).
      pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
      exact (ios_fly_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw B5
               ly5 S5 W3 mem5 md5 regs5 HL HF
               (conj CUR (conj SAVED (conj SFR (conj GARR (conj SRCF (conj HOFF (conj HFAT HTW5)))))))
               H60 H32 R2 R3 R4 R8 R9 R19 R215 R24).
    + (* the retry arm, or E2 with that bit set: the epilogue *)
      intros ly5 S5 W5 mem5 md5 regs5 AT5.
      destruct AT5 as (CUR & SAVED & RG & R24 & _ & _ & _ & _ & HTW5).
      pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
      exact (ios_epi B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
               ly5 S5 W5 mem5 md5 regs5 HL HF CUR SAVED R2 R3 R4 R19 R24 HTW5).
  - (* ACK, E3 or another cmd byte: the epilogue *)
    intros rg2 mem4 md4 CUR SAVED RG R24 HTW4.
    pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
    exact (ios_epi B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
             ly3 S3 W3 mem4 md4 rg2 HL HF CUR SAVED R2 R3 R4 R19 R24 HTW4).
Qed.

End top.

(* The statement of lib/A/Prog/io_send_cg.v. *)
Theorem transport_io_send_cg_holds : forall fx rc B MT, @transport_io_send_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ios_holds fx rc B MT). Qed.

Print Assumptions transport_io_send_cg_holds.

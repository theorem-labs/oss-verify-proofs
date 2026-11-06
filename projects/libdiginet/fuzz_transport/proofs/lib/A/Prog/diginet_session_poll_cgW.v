(* diginet_session_poll_cgW: Theorem transport_diginet_session_poll_cg_holds : the statement
   transport_diginet_session_poll_cg_holds_stmt of lib/A/Prog/diginet_session_poll_cg.v, the machine walk of
   diginet_session_poll on fuzz_transport.asan at 0x8ad88 (1000 bytes), a G-form caller-journal walk with a class-5
   side-stack frame of its own.

   The walk is in these files:
   - lib/A/Prog/diginet_session_poll_segs.v: the context, the cuts (now1, recv1, tick, loop, rel), the piece
     statements and their composition pw_walk;
   - lib/A/Prog/diginet_session_poll_seg_kit.v: the model at the code's branches and the facts the pieces share;
   - lib/A/Prog/diginet_session_poll_seg_rt.v, _seg_leaf.v, _seg_grecv.v, _seg_grx.v: the calls (the shadow fills
     and the stack free; io_now and diginet_session_deadline; io_recv; diginet_session_rx and diginet_session_tick);
   - lib/A/Prog/diginet_session_poll_seg_head.v, _seg_now1.v, _seg_recv1.v, _seg_tick.v, _seg_loop.v, _seg_rel.v:
     the six pieces.
   Here they are put together at the statement's values: the five run-invariant premises and their two bounds are
   SrxCut.v srx_inv Bw, and pw_X's invariants are dropped from the post. The model facts pw_keep (the callees' model
   calls keep the run invariants and g_rx) are lib/TModel/TRunInv.v's lemmas (pw_keep_holds; srx_inv is TRunInv.v
   run_inv by unfolding). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg notice_cg io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  diginet_session_poll_seg_head diginet_session_poll_seg_now1 diginet_session_poll_seg_recv1
  diginet_session_poll_seg_tick diginet_session_poll_seg_loop diginet_session_poll_seg_rel.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TRunInv.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section poll_holds. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

(* pw_keep from lib/TModel/TRunInv.v: srx_inv is run_inv (the same seven conjuncts), and each keep lemma concludes
   the length too. *)
Lemma pw_keep_holds : pw_keep.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - intros I F Bx b now B2 r HL HI HM. exact (proj2 (TRI.rx_m_run_inv I F Bx b now B2 r HL HI HM)).
  - intros I F Bx now B2 r HL HI HM. exact (proj2 (TRI.tick_m_run_inv I F Bx now B2 r HL HI HM)).
  - exact TRI.rx_m_g_rx.
  - exact TRI.tick_m_g_rx.
  - intros I F Bx cap B1 r got HL HI HM. exact (proj2 (TRI.iorecv_m_run_inv I F Bx cap B1 r got HL HI HM)).
  - exact TRI.iorecv_m_g_rx.
Qed.

Lemma pw_holds : @transport_diginet_session_poll_cg_holds_stmt fx rc B MT.
Proof.
  intros HPCS HCELLS HPC HGU HGE HRU HRE LAWS MTL MTF SMP FFL ASM AF8 A00 LNOW LDL IORC SRXC TICKC ASF.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs w r TF Bw Bw'
    HJ Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hw Htw Hfn Hm HTF HTFG HROM HAP HRXIN
    I1 I2 Iq I4 In I5a I5b HRXE C5 C1 C4 C0 C2 Hev.
  set (c := mkPW STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs w r TF Bw Bw').
  assert (HRT : pw_rt B MT).
  { exact (conj HPCS (conj HCELLS (conj HPC (conj HGU (conj HGE (conj HRU (conj HRE (conj LAWS (conj MTL
      (conj MTF (conj SMP (conj FFL (conj (G_HARNESS_gx_ok B HGU) (conj (G_HARNESS_gx_noerrno B HGE)
      (conj ASM (conj AF8 (conj A00 (conj LNOW (conj LDL (conj IORC (conj SRXC (conj TICKC ASF)))))))))))))))))))))). }
  pose proof pw_keep_holds as HKEEP.
  assert (HOK : pw_ok B c).
  { exact (conj HJ (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
      (conj Hw (conj Htw (conj Hfn (conj Hm (conj HTF (conj HTFG (conj HROM (conj HAP (conj HRXIN
      (conj (conj I1 (conj I2 (conj I4 (conj I5a (conj I5b (conj In Iq))))))
      (conj HRXE (conj C5 (conj C1 (conj C4 (conj C0 (conj C2 Hev)))))))))))))))))))))))))). }
  eapply SRr_mono.
  { exact (pw_walk B MT (pw_head_piece fx rc B MT) (pw_now1_piece fx rc B MT) (pw_recv1_piece fx rc B MT)
      (pw_tick_piece fx rc B MT) (pw_loop_piece fx rc B MT) (pw_rel_piece fx rc B MT) c HRT HKEEP HOK). }
  intros W2 c2 _ HP. unfold transport_poll_post. unfold pw_post in HP.
  eapply transport_cg_post_X_mono; [|exact HP].
  intros regs2 W3 mem3 (X1 & X2 & X3 & _). exact (conj X1 (conj X2 X3)).
Qed.

End poll_holds.

(* The statement of lib/A/Prog/diginet_session_poll_cg.v. *)
Theorem transport_diginet_session_poll_cg_holds :
  forall fx rc B MT, @transport_diginet_session_poll_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pw_holds fx rc B MT). Qed.

Print Assumptions transport_diginet_session_poll_cg_holds.

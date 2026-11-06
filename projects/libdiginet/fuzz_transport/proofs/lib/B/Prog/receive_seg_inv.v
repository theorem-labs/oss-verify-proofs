(* receive_seg_inv: the model piece of the image-B walk of receive (lib/B/Prog/receive_cg.v; the cut interface
   lib/B/Prog/receive_seg_cut.v): recv_inv_stmt, the run invariants with their two index bounds (lib/TModel/TRunInv.v
   run_inv) at the worlds receive hands its callees and settle. No code and no machine state: only lib/TModel worlds.
   Image B's model steps are image A's (receive_cg.v's recv_w1 .. recv_w2c are image A's definitions word for word),
   so the store lemmas are image A's model piece, lib/A/Prog/receive_seg_inv.v (image-free: each is stated over
   lib/TModel worlds only): rvi_w2 (op_begin, then g_rx_send) and rvi_w2c (then g_rx_send, g_rx, g_rx_len,
   g_rx_times, g_rx_fail) keep the length and run_inv, and so do rvi_set_g_rx / rvi_set_g_rx_fail (the two stores of 0
   after diginet_session_poll). The three callee steps keep them by TRunInv.v mrx_m_run_inv, rx_m_run_inv and
   poll_m_run_inv, at timg_B. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TImgB receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require receive_seg_inv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TRunInv.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module AINV := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_inv.

Lemma recv_inv : recv_inv_stmt.
Proof.
  unfold recv_inv_stmt. split; [|split; [|split; [|split]]].
  - intros Bw bytes HL HI. exact (proj2 (AINV.rvi_w2 Bw bytes (conj HL HI))).
  - intros Bw bytes a pf HL HI. exact (proj2 (AINV.rvi_w2c Bw bytes a pf (conj HL HI))).
  - intros Bw bytes F n Bx t HL HI HM.
    destruct (AINV.rvi_w2 Bw bytes (conj HL HI)) as [L2 I2].
    exact (proj2 (TRunInv.mrx_m_run_inv timg_B F (recv_w2 Bw bytes) n Bx t L2 I2 HM)).
  - intros F Bx b now By r HL HI HM.
    exact (proj2 (TRunInv.rx_m_run_inv timg_B F Bx b now By r HL HI HM)).
  - intros Bw bytes a pf F B2d r HL HI HM.
    destruct (AINV.rvi_w2c Bw bytes a pf (conj HL HI)) as [L2 I2].
    destruct (TRunInv.poll_m_run_inv timg_B F (recv_w2c Bw bytes a pf) 0 B2d r L2 I2 HM) as [L3 I3].
    exact (proj2 (AINV.rvi_set_g_rx_fail (TW.set_g_rx B2d 0) 0 (AINV.rvi_set_g_rx B2d 0 (conj L3 I3)))).
Qed.

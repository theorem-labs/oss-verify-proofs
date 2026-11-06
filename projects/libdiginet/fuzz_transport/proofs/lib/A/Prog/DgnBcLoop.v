(* DgnBcLoop: Lemma bc_loop : bc_rel_stmt -> bc_scan_stmt -> bc_loop_stmt (lib/A/Prog/DgnBcCut.v), the msg_next
   loop of diginet_body_check (fuzz_decode.asan, the loop head +0x16c).
   Strong induction on length bb - cp, the bytes the cursor has not passed. One turn is the call (bl_call_stmt of
   lib/A/Prog/DgnBcLoopCut.v, proved in lib/A/Prog/DgnBcLoopCall.v) and the test after it (bl_test_stmt, proved in
   lib/A/Prog/DgnBcLoopTest.v):
     - a result that is not the end and not a refused sysex goes back to +0x16c with the cursor at
       (mr_pos r, mr_st r) and the message bytes of r: r is not the end, so cp < length bb and msg_step_progress
       gives cp < mr_pos r <= length bb, and the induction hypothesis applies;
     - the end (a0 = 0) goes to the prefix scan, bc_scan_stmt;
     - a refused sysex goes to the release with a0 = -10, bc_rel_stmt: refused_hit gives sys_hit bb cp, so
       system_at bb and body_check bb = -10 (body_check_refused).
   The test writes no memory, so after it only the model differs from the state bl_after describes: the journal
   takes it (ajournal_materialize). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib DgnTransportCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_msg_next_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnBcCut DgnBcLoopCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnBcLoopCall DgnBcLoopTest.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_cg.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PMsg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_msg_next_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The 40 message bytes of a step are 40 bytes again. *)
Lemma bl_msg_len : forall body (mj : list byte) r, length mj = 40%nat ->
  length (LC.cells_bytes (PMsg.msg_cells body mj r)) = 40%nat.
Proof.
  intros body mj r Hmj. unfold PMsg.msg_cells.
  destruct (is_end r).
  - cbn [LC.cells_bytes LC.cbytes]. rewrite app_nil_r. exact Hmj.
  - destruct (writes_len (mr_kind r));
    (rewrite LC.cells_bytes_length; cbn [LC.cells_size LC.csize LC.cells_wf LC.cell_wf];
     [reflexivity | rewrite ?length_firstn, ?length_skipn, Hmj; repeat split]).
Qed.

Section lp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* The facts at a cut hold again for a materialized model. *)
Lemma bl_cur_mat : forall lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 md2 X,
  AR_laws segs B ->
  bc_cur B MT lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 md2 ->
  bc_cur B MT lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 (with_vm_backing (m_vm_lazy md2) X md2).
Proof.
  intros lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 md2 X LAWS [HJ R].
  split; [|exact R].
  eapply ajournal_materialize; first [exact HJ | exact LAWS | exact transport_segs_low].
Qed.

(* The loop, from its two halves and the two cuts after it. *)
Lemma bc_loop_of : @bl_call_stmt fx rc B MT -> @bl_test_stmt fx rc B MT ->
  @bc_rel_stmt fx rc B MT -> @bc_scan_stmt fx rc B MT -> @bc_loop_stmt fx rc B MT.
Proof.
  intros CALL TEST REL SCAN. unfold bc_loop_stmt.
  intros LAWS MN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F
    W2 regs2 mem2 md2 ly2 S2 cp st mj HFIX HCUR HREG Hcp Hst Hcur Hmjl Hmj Hcm.
  pose proof LAWS as (_ & HARL & _).
  remember (length bb - cp)%nat as n eqn:Hn.
  revert W2 regs2 mem2 md2 ly2 S2 cp st mj Hn HCUR HREG Hcp Hst Hcur Hmjl Hmj Hcm.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros W2 regs2 mem2 md2 ly2 S2 cp st mj Hn HCUR HREG Hcp Hst Hcur Hmjl Hmj Hcm.
  apply (CALL LAWS MN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F
    W2 regs2 mem2 md2 ly2 S2 cp st mj _ HFIX HCUR HREG Hcp Hst Hcur Hmjl Hmj Hcm).
  intros W3 regs3 mem3 md3 ly3 S3 HAF.
  pose proof HAF as (HC3 & _ & _ & Hc3 & Hm3 & Hz3).
  apply (TEST LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F cp st mj
    W3 regs3 mem3 md3 ly3 S3 _ HFIX Hcp Hst Hmjl HAF).
  - (* another message: the next turn *)
    intros Hne Hnr regs4 mat HR4.
    assert (Hlt : (cp < length bb)%nat).
    { pose proof (is_end_msg_step bb cp st) as E. rewrite Hne in E.
      symmetry in E. apply Nat.leb_gt in E. exact E. }
    pose proof (msg_step_progress bb cp st Hlt) as Hpr.
    apply (IH (length bb - mr_pos (msg_step bb cp st))%nat ltac:(lia) W3 regs4 mem3 _ ly3 S3
      (mr_pos (msg_step bb cp st)) (mr_st (msg_step bb cp st))
      (LC.cells_bytes (PMsg.msg_cells body mj (msg_step bb cp st))) eq_refl).
    + exact (bl_cur_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat HARL HC3).
    + exact HR4.
    + lia.
    + apply msg_step_st_ok. exact Hst.
    + exact Hc3.
    + apply bl_msg_len. exact Hmjl.
    + exact Hm3.
    + exact Hz3.
  - (* the end: the prefix scan *)
    intros Hend regs4 mat HR4.
    exact (SCAN LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F
      W3 regs4 mem3 _ ly3 S3 HFIX (bl_cur_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat HARL HC3) HR4).
  - (* a refused sysex: the release with -10 *)
    intros Href regs4 mat HR4 H10.
    apply (REL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F
      W3 regs4 mem3 _ ly3 S3 HFIX (bl_cur_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat HARL HC3) HR4).
    rewrite H10. f_equal. symmetry. apply body_check_refused. apply system_at_true.
    exists cp. exact (refused_hit bb cp st Href).
Qed.

(* The loop piece: the cut at +0x16c from the cuts at +0x1ec and +0x298. *)
Lemma bc_loop : @bc_rel_stmt fx rc B MT -> @bc_scan_stmt fx rc B MT -> @bc_loop_stmt fx rc B MT.
Proof. exact (bc_loop_of (@DgnBcLoopCall.bl_call fx rc B MT) (@DgnBcLoopTest.bl_test fx rc B MT)). Qed.
End lp.

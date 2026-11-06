(* Case 6 of the op loop of LLVMFuzzerTestOneInput in the ubsan image (fuzz_transport.c:1200-1205,
   `case 6: op_begin(); m_close(); diginet_session_close(&g_s, g_now); settle(0); break;`), from the case entry
   0x13bcc to the latch 0x14574: llvm_op_stmt 6 of U/Prog/T/LLVMFuzzerTestOneInput_lh.v. The walk is three pieces:
   LLVMFuzzerTestOneInput_op6_head.v (0x13bcc-0x13be8, op_begin's two memsets), _op6_mid.v (0x13bec-0x13c1c,
   op_begin's last two writes and the inlined m_close's test and then arm), _op6_tail.v (0x13c20-0x13c40 and
   0x1456c-0x14570: M.fly.on = 0, m_set, diginet_session_close, settle, the latch); _op6_lib.v holds the model's
   side, the model's op 6 split into its calls (op6_split) among it. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  m_set_c diginet_session_close_c settle_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_op6_lib LLVMFuzzerTestOneInput_op6_head LLVMFuzzerTestOneInput_op6_mid
  LLVMFuzzerTestOneInput_op6_tail.
Import ListNotations.
Open Scope Z_scope.

Theorem llvm_op6_holds :
  memset_contract -> m_set_contract -> diginet_session_close_contract -> settle_contract -> llvm_op_stmt 6.
Proof.
  intros MSC MSE DSC STC. unfold llvm_op_stmt.
  intros data D regs0 m0 Sp lo ops c c1 B F fc ms A k B1 c2 k1 HCASE HOP.
  destruct HCASE as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                     m & j10 & jio & j60 & -> & HOPS & HN & HC & HC1 & H6 & HM).
  destruct (op6_split timg_ubsan B A D c k B1 c2 k1 H6 HOP) as (Bm & B3 & r & HB2 & HB3 & HB4 & Ec2 & _).
  rewrite <- HC1 in Ec2. subst c2.
  pose proof (op6_cursor D c HC HN) as HC2. rewrite <- HC1 in HC2.
  pose proof HM as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WM & _).
  pose proof (wm_len rsegs W_BASE_UBSAN m B WM) as LB. clear WM.
  rewrite (op6_close_eq B LB) in HB2.
  change (LH_CASE 6) with 0x13bcc.
  eapply (op6_head data D regs0 MSC); [exact HM |].
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' HM1.
  eapply (op6_mid data D regs0); [exact LB | exact HM1 |].
  intros a0'' a1'' m'' HM2.
  eapply (op6_tail data D regs0 MSE DSC STC);
    [ exact HOPS | exact HC2 | exact HM2 | exact HB2 | exact HB3 | exact HB4 ].
Qed.

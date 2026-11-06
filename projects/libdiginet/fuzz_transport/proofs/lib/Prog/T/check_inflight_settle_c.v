(* check_inflight_settle (fuzz/fuzz_transport.c:744-771; model TCb.v check_inflight_settle_m), entry 0x15ea4, 43
   instructions. Checks GOT.acked = OW.acked, no overdue frame in flight, and that diginet_session_deadline(&g_s,
   g_now) lies in [g_now, g_now + 1000000] and not after the next retransmission.
   Arguments: none.
   FRAME 32: the prologue `addi sp,sp,-32`; the callee diginet_session_deadline is a leaf with no stack (FRAME 0
   in its contract).
   Callee contracts its walk uses: diginet_session_deadline_contract
   (lib/Prog/T/diginet_session_deadline_c.v).
   The world: not written (the model returns its B on Some); post B' = B and wmem rsegs m' B, no world interval in
   munch. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract.
Import ListNotations.
Open Scope Z_scope.

Definition check_inflight_settle_ENTRY : Z := 0x15ea4.
Definition check_inflight_settle_FRAME : Z := 32.

Definition check_inflight_settle_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte),
    wmem rsegs m B ->
    check_inflight_settle_m B = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + check_inflight_settle_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp check_inflight_settle_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - check_inflight_settle_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         B' = B /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 check_inflight_settle_ENTRY) fc None m (seg_rom rsegs)).

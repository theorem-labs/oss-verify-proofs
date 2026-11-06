(* settle (fuzz/fuzz_transport.c:980-991; model TCb.v settle_m), entry 0x14f10, 21 instructions. Runs
   check_ack_settle, check_state_settle, check_inflight_settle, check_keepalive_settle, then (tagged mode, g_raw =
   0) check_latest_queue and, when ticked != 0, check_latest_drain.
   Arguments: a0 = ticked (int).
   FRAME 96: own prologue 16 + the deepest callee called inside the frame, check_latest_queue (80); the others:
   check_ack_settle 16, check_state_settle 16, check_inflight_settle 32, check_keepalive_settle 16;
   check_latest_drain (16) is tail-called from the entry sp.
   Callee contracts its walk uses: check_ack_settle_contract, check_state_settle_contract,
   check_inflight_settle_contract, check_keepalive_settle_contract, check_latest_queue_contract,
   check_latest_drain_contract.
   The world: not written (the model returns its B on Some); post B' = B and wmem rsegs m' B, no world interval in
   munch. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract.
Import ListNotations.
Open Scope Z_scope.

Definition settle_ENTRY : Z := 0x14f10.
Definition settle_FRAME : Z := 96.

Definition settle_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (ticked : Z),
    a0 = Z_to_bv 64 ticked ->
    -2 ^ 31 <= ticked < 2 ^ 31 ->
    wmem rsegs m B ->
    settle_m B ticked = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + settle_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp settle_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - settle_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         B' = B /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 settle_ENTRY) fc None m (seg_rom rsegs)).

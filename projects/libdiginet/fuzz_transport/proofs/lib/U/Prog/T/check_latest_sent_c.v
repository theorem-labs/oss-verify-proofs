(* check_latest_sent (fuzz/fuzz_transport.c:626-644; model TCb.v check_latest_sent_m), entry 0x1570c, 111
   instructions. Walks the sent body command by command: each must be a tagged, PENDING command whose bytes match;
   marks it SENT, removes its serial from g_q (q_remove), ORs its display flag into *display. Writes g_cmd[].st,
   g_q, g_nq and *display.
   Arguments: a0 = body (the len bytes at bp; below g_cmd in the world, i.e. in g_s.inflight_frame, or above the
   world), a1 = len, a2 = display (an int on the caller's stack, written).
   FRAME 128: the prologue `addi sp,sp,-128`; the callees tagged_of (a leaf with no stack, FRAME 0) and bcmp use no
   stack; q_remove is inlined.
   Callee contracts its walk uses: bcmp_contract (lib/U/Prog/bcmp_c.v), tagged_of_contract
   (lib/U/Prog/T/tagged_of_c.v).
   The world: written; post wmem rsegs m' B', the world interval in munch. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract.
Import ListNotations.
Open Scope Z_scope.

Definition check_latest_sent_ENTRY : Z := 0x1570c.
Definition check_latest_sent_FRAME : Z := 128.

Definition check_latest_sent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (bp len dp : Z) (body junk : list byte) (disp : Z),
    a0 = Z_to_bv 64 bp ->
    a1 = Z_to_bv 64 len ->
    a2 = Z_to_bv 64 dp ->
    0 < bp ->
    bytes_at rsegs m bp body ->
    Z.of_nat (length body) = len ->
    bp + len <= W_BASE_UBSAN + OFF_g_cmd \/ W_BASE_UBSAN + W_LEN <= bp ->
    off_window sp check_latest_sent_FRAME bp len ->
    dp mod 4 = 0 ->
    rw_cells rsegs m dp [CB 4 junk] ->
    off_world dp 4 ->
    off_window sp check_latest_sent_FRAME dp 4 ->
    bp + len <= dp \/ dp + 4 <= bp ->
    wmem rsegs m B ->
    check_latest_sent_m B body len = Some (B', disp) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + check_latest_sent_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp check_latest_sent_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - check_latest_sent_FRAME, bv_unsigned sp); (dp, dp + 4); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' dp [C4 (Z_to_bv 64 disp)] /\
         wmem rsegs m' B')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 check_latest_sent_ENTRY) fc None m (seg_rom rsegs)).

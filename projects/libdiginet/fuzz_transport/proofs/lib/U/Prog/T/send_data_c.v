(* send_data (transport/src/diginet_session.c:388-401) at 0x178c0, 252 bytes. The binary inlines inflight_start and
   send_raw; it calls diginet_frame_build (:393) and, through g_s.io.send, io_send (:400). FRAME 576 = its own 64
   (addi sp,sp,-64 at 0x178c0) + 512, the deepest callee window (io_send; diginet_frame_build 240). Every callee
   window counted is that callee's full transitive stack depth, abort() paths included, so it bounds the window
   any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition send_data_ENTRY : Z := 0x178c0.
Definition send_data_FRAME : Z := 576.

(* a0 = s = &g_s, a1 = body, a2 = body_len = the length of the bytes body at it (tick's body[] after take, or its
   keepalive byte ka, :455, :471), a3 = ncmds (unsigned, sign-extended from bit 31 by the LP64 ABI), a4 = now
   (uint64_t). Result: the int send_data_m gives. *)
Definition send_data_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (bodyp ncmds now r : Z) (body : list byte) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 bodyp ->
    a2 = Z_to_bv 64 (Z.of_nat (length body)) ->
    a3 = Z_to_bv 64 (bv_swrap 32 ncmds) ->
    a4 = Z_to_bv 64 now ->
    0 <= ncmds < 2^32 ->
    0 <= now < 2^64 ->
    bytes_at rsegs m bodyp body ->
    arg_blk sp send_data_FRAME bodyp (Z.of_nat (length body)) ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    send_data_m timg_ubsan TF B body ncmds now = Some (B', r) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + send_data_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp send_data_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - send_data_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 send_data_ENTRY) fc None m (seg_rom rsegs)).

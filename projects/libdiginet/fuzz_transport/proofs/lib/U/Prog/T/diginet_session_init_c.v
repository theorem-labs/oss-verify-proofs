(* diginet_session_init (transport/src/diginet_session.c:56-75) at 0x169d4, 292 bytes. The binary calls memset (:64)
   and memcpy (:65 s->cfg = *cfg, :66 s->io = *io, :71 desk_mac; some as stores). FRAME 48 = its own 48 (addi
   sp,sp,-48 at 0x169d4) + 0, the deepest callee window (memcpy; memset 0). Every callee window counted is that
   callee's full transitive stack depth, abort() paths included, so it bounds the window any callee contract asks
   for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_init_ENTRY : Z := 0x169d4.
Definition diginet_session_init_FRAME : Z := 48.

(* a0 = s = &g_s, a1 = cfg = &g_cfg, a2 = io = the address of the caller's struct diginet_io (32 bytes: ctx, send,
   recv, now_us), a3 = notify, a4 = ctx (fuzz_transport.c:1165). Result: the int diginet_session_init_m gives. *)
Definition diginet_session_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (iop io_ctx io_send io_recv io_now ntf ctx r : Z) (B B' : list byte),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cfg) ->
    a2 = Z_to_bv 64 iop ->
    a3 = Z_to_bv 64 ntf ->
    a4 = Z_to_bv 64 ctx ->
    0 <= io_ctx < 2^64 ->
    0 <= io_send < 2^64 ->
    0 <= io_recv < 2^64 ->
    0 <= io_now < 2^64 ->
    0 <= ntf < 2^64 ->
    0 <= ctx < 2^64 ->
    bytes_at rsegs m iop (put 8 io_ctx ++ put 8 io_send ++ put 8 io_recv ++ put 8 io_now) ->
    arg_blk sp diginet_session_init_FRAME iop 32 ->
    iop mod 8 = 0 ->
    wmem rsegs m B ->
    diginet_session_init_m B io_ctx io_send io_recv io_now ntf ctx = Some (B', r) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + diginet_session_init_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp diginet_session_init_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - diginet_session_init_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 diginet_session_init_ENTRY) fc None m (seg_rom rsegs)).

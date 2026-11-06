(* diginet_session_rx (transport/src/diginet_session.c:263-318) at 0x16e04, 508 bytes. The binary inlines
   session_lost; it calls diginet_frame_parse (:268), bcmp (:273-279), diginet_mac_is_digidesign (:286),
   on_announce, on_ack, on_data, set_state (session_lost's, :311) and diginet_session_tick (:317); the memcpy of
   :290 is stores. FRAME 2256 = its own 112 (addi sp,sp,-112 at 0x16e04) + 2144, the deepest callee window
   (diginet_session_tick; bcmp 0, diginet_frame_parse 48, diginet_mac_is_digidesign 0, on_ack 480, on_announce
   1056, on_data 752, set_state 384). Every callee window counted is that callee's full transitive stack depth,
   abort() paths included, so it bounds the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_rx_ENTRY : Z := 0x16e04.
Definition diginet_session_rx_FRAME : Z := 2256.

(* a0 = s = &g_s, a1 = buf, a2 = len = the length of the bytes b at buf (receive's heap frame,
   fuzz_transport.c:1021, or poll's local buf, :521, :525), a3 = now_us (uint64_t). Result: the int
   diginet_session_rx_m gives. *)
Definition diginet_session_rx_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (bufp now r : Z) (b : list byte) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 bufp ->
    a2 = Z_to_bv 64 (Z.of_nat (length b)) ->
    a3 = Z_to_bv 64 now ->
    0 <= now < 2^64 ->
    bytes_at rsegs m bufp b ->
    arg_blk sp diginet_session_rx_FRAME bufp (Z.of_nat (length b)) ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    diginet_session_rx_m timg_ubsan TF B b now = Some (B', r) ->
    tframe_at m sp diginet_session_rx_FRAME TF ->
    relro_img m ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + diginet_session_rx_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp diginet_session_rx_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - diginet_session_rx_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 diginet_session_rx_ENTRY) fc None m (seg_rom rsegs)).

(* send_control (transport/src/diginet_session.c:97-109) at 0x16bf0, 240 bytes. The binary inlines send_raw; it
   calls diginet_frame_build (:101), memcpy (:105) and, through g_s.io.send, io_send (:90). FRAME 640 = its own
   128 (addi sp,sp,-128 at 0x16bf0) + 512, the deepest callee window (io_send; diginet_frame_build 240, memcpy
   0). Every callee window counted is that callee's full transitive stack depth, abort() paths included, so it
   bounds the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition send_control_ENTRY : Z := 0x16bf0.
Definition send_control_FRAME : Z := 640.

(* a0 = s = &g_s, a1 = cmd (uint8_t), a2 = ack_counter (uint32_t, sign-extended from bit 31 by the LP64 ABI), a3 =
   keep, a4 = keep_len: both NULL (close :154, on_data :242), or wake's e2[60] and its size_t e2_len (:134-136).
   Result: the int r of send_control_m; when keep is not NULL and the build succeeded (the model's f is the 60
   built bytes, else []), keep holds f and *keep_len = 60. *)
Definition send_control_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (cmd ack kp klp r : Z) (K KL f : list byte) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 cmd ->
    a2 = Z_to_bv 64 (bv_swrap 32 ack) ->
    a3 = Z_to_bv 64 kp ->
    a4 = Z_to_bv 64 klp ->
    0 <= cmd < 2^8 ->
    0 <= ack < 2^32 ->
    (kp = 0 \/ (rw_cells rsegs m kp [CB 60 K] /\ arg_blk sp send_control_FRAME kp 60 /\
                 rw_cells rsegs m klp [CB 8 KL] /\ arg_blk sp send_control_FRAME klp 8 /\ klp mod 8 = 0 /\ blk_sep kp 60 klp 8)) ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    send_control_m timg_ubsan TF B cmd ack = Some (B', (r, f)) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + send_control_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp send_control_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(bv_unsigned sp - send_control_FRAME, bv_unsigned sp);
                 (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] ++
               (if kp =? 0 then [] else [(kp, kp + 60); (klp, klp + 8)])) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1 /\
         (kp = 0 \/ (rw_cells rsegs m' kp [CB 60 (match f with nil => K | _ => f end)] /\
                      rw_cells rsegs m' klp [CB 8 (match f with nil => KL | _ => put 8 (Z.of_nat (length f)) end)])))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 send_control_ENTRY) fc None m (seg_rom rsegs)).

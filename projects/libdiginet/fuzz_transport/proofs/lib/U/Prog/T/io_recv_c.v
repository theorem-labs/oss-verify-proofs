(* The machine contract of io_recv (fuzz/fuzz_transport.c:906-929, as the harness fix c47f6290 on 835f336c has it) in
   the ubsan image. *)
(* Numbers from the ubsan image (stripped sha256 af7b86991906e2fd..., unstripped twin c53d4b20cfc1e663...),
   disassembled by symbol:
   io_recv at 0x14b20, 156 bytes. addi sp,sp,-32 at 0x14b20 (ra, s0-s2 saved); s2 = W_BASE_UBSAN + OFF_g_fail_next
   (auipc / addi at 0x14b34); g_rx_fail lw 0x14b3c (sw zero 0x14b44), g_rx ld 0x14b50, g_rx_times lw 0x14b60 /
   sw 0x14b70, g_rx_len ld 0x14b68, n = min (g_rx_len, cap) by bltu at 0x14b74; no UBSan check in the function.
   Callees (all jal): m_rx 0x15908 at 0x14b84 when n <> 0 (a0 = g_rx, a1 = n; window 208, U/Prog/T/m_rx_c.v),
   m_tick 0x14e8c at 0x14b8c when n = 0 (window 0, U/Prog/T/m_tick_c.v), memcpy 0x20440 at 0x14b9c (kit, window 0;
   a0 = buf, a1 = g_rx, loaded again at 0x14b90 after either callee, a2 = n); result sext.w n at 0x14ba0.
   FRAME 240 = its own 32 + 208, the deepest callee window (m_rx). io_recv is called through the world cell
   g_s.io.recv (TSess.v call_recv), by diginet_session_poll (transport/src/diginet_session.c:516, :524) with
   buf = poll's local uint8_t[1514] and cap = 1514. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition io_recv_ENTRY : Z := 0x14b20.
Definition io_recv_FRAME : Z := 240.

(* The buffer [bp, bp + cap) and the block of the current heap frame TF do not overlap (memcpy's source lies in
   that block: g_rx points into it). *)
Definition io_recv_sep (TF : option tframe) (bp cap : Z) : Prop :=
  match TF with
  | None => True
  | Some fr => blk_sep bp cap (tf_addr fr) (Z.of_nat (length (tf_bytes fr)))
  end.

(* a0 = ctx and a3 = timeout_ms (io_recv reads neither, :908-909), a1 = buf, a2 = cap (size_t). TF = the current
   heap frame, which g_rx points into; its block ends below 2^64 (tframe_ok, which m_rx's contract needs). Result:
   the int io_recv_m gives (sign-extended from bit 31 as the LP64 ABI returns a 32-bit value); buf[0 .. length got)
   holds the bytes io_recv_m gives (the bytes copied when the result is > 0, else []); the bytes past them are left
   free. *)
Definition io_recv_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (bp cap r : Z) (J got : list byte) (TF : option tframe) (B B' : list byte),
    a1 = Z_to_bv 64 bp ->
    a2 = Z_to_bv 64 cap ->
    0 <= cap ->
    rw_cells rsegs m bp [CB (Z.to_nat cap) J] ->
    arg_blk sp io_recv_FRAME bp cap ->
    io_recv_sep TF bp cap ->
    tframe_at m sp io_recv_FRAME TF ->
    tframe_ok TF ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    io_recv_m timg_ubsan TF B cap = Some (B', r, got) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + io_recv_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp io_recv_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (X : list byte)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - io_recv_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
                (bp, bp + cap)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1 /\
         rw_cells rsegs m' bp [CB (Z.to_nat cap) X] /\
         firstn (length got) X = got)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 io_recv_ENTRY) fc None m (seg_rom rsegs)).

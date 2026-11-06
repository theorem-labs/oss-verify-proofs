(* The machine contract of io_recv (fuzz/fuzz_transport.c:906-929, as the harness fix c47f6290 on 835f336c has it) in
   the plain image. *)
(* Numbers from the plain image (stripped sha256 bb20ce415827592a..., unstripped twin c2d42d89541589e1...),
   disassembled by symbol:
   io_recv at 0x1492c, 172 bytes. addi sp,sp,-48 at 0x1492c (ra, s0-s3 saved); s3 = W_BASE_PLAIN + OFF_g_fail_next
   (auipc / addi at 0x14944); g_rx_fail lw 0x1494c (sw zero 0x14954), g_rx ld 0x14960, g_rx_times lw 0x1496c /
   sw 0x14980, g_rx_len ld 0x14978, n = min (g_rx_len, cap) by bltu at 0x14984. Callees (all jal): m_rx 0x153e0 at
   0x14998 when n <> 0 (a0 = g_rx, a1 = n; window 144, Prog/T/m_rx_c.v), m_tick 0x14d28 at 0x149a4 when n = 0
   (window 0, Prog/T/m_tick_c.v), memcpy 0x1f910 at 0x149b4 (kit, window 0; a0 = buf, a1 = g_rx, loaded again at
   0x1499c after m_rx, a2 = n); result sext.w n at 0x149b8. FRAME 192 = its own 48 + 144, the deepest callee
   window (m_rx). io_recv is called through the world cell g_s.io.recv (TSess.v call_recv), by diginet_session_poll
   (transport/src/diginet_session.c:516, :524) with buf = poll's local uint8_t[1514] and cap = 1514. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition io_recv_ENTRY : Z := 0x1492c.
Definition io_recv_FRAME : Z := 192.

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
    io_recv_m timg_plain TF B cap = Some (B', r, got) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + io_recv_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp io_recv_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (X : list byte)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - io_recv_FRAME, bv_unsigned sp);
                (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
                (bp, bp + cap)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1 /\
         rw_cells rsegs m' bp [CB (Z.to_nat cap) X] /\
         firstn (length got) X = got)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 io_recv_ENTRY) fc None m (seg_rom rsegs)).

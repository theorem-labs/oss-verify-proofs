(* check_ack_frame_contract: check_ack_frame (fuzz/fuzz_transport.c:422-430; model lib/TModel/TCb.v
   check_ack_frame_m) on fuzz_transport.asan (e89be137db17), a leaf that reads three fields of the struct spec_frame
   at its argument and the int g_rx_send of the harness, and returns nothing. It stores into no harness global, so it
   takes the leaf form.
   Argument: a0 = fp, the address of a struct spec_frame (fuzz/spec.h:188-197; retry at 30 (2 bytes), ack at 36
   (4), body_len at 56 (8)) holding the parse rf frame of a frame buffer (TCb.v:128).
   Premises:
   - the plain contract's struct premise sframe_at m fp fa (rf frame) (lib/Prog/T/TContract.v:73-83), stated over
     image A's memory for the fields the code reads: 0 < fp, fp mod 8 = 0, and the bytes at fp + 36, fp + 56 and
     fp + 30 are the little-endian ack, body_len and retry of rf frame (bytes_at of TWorld.v put);
   - the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between the
     memory m, read through mrd (csw_view, check_state_wake_c.v), and the world Bw; check_ack_frame_m Bw frame =
     Some (Bw', tt), which holds exactly when ack = g_rx_send, body_len = 0 and retry = 0 (TCb.v:365-368);
   - the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull
     [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store does not touch
     the world; both ends of the frame in application memory (app_mem), so the frame is not shadow memory;
   - asan_cells m (lib/A/AsanCells.v: among others the 8 bytes at GOT_CELL_K 0xa4090 hold CELL_K 0xac9f8 and the 8
     bytes at CELL_K hold 0x7fff8000); GOT_CELL_K's 8 bytes, CELL_K's 8 bytes and each field the code loads lie
     outside the frame (off_stk; the plain contract's off_window), and each loaded field is marked usable
     (addressable).
   Result: the run returns to ra with every register but a0-a4 unchanged (they are not specified: the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays
   usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the
   plain contract's post facts (lib/Prog/T/check_ack_frame_c.v: B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 176 code bytes of
   this function are equal in both files): symbol check_ack_frame, value 0x8415c, size 176 (44 words).
     0x8415c          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x84160          the 8-byte store of ra at sp - 8 (own frame); 0x841cc loads it back.
     0x84164-0x8416c  a1 = the 8-byte load at GOT_CELL_K 0xa4090 (it holds CELL_K); a2 = the 8-byte load at CELL_K
                      0xac9f8 (it holds 0x7fff8000).
     0x84170-0x8417c  the instrumented check of the 4-byte load at fp + 36: a1 = fp + 36; a3 = the signed shadow byte
                      k at ((fp + 36) >> 3) + 0x7fff8000. 0x84180: k = 0 goes on to 0x84184; else 0x841e0-0x841e8:
                      a4 = ((fp + 36) & 7) + 3, and a4 < k (signed) goes back to 0x84184; else 0x841ec-0x841f0:
                      a0 = fp + 36 and the call of TS___asan_report_load4 (0x59608), the error path.
     0x84184          a1 = the 4-byte load at fp + 36, sign-extended: f->ack.
     0x84188-0x8418c  a3 = the 4-byte load at 0x5e53e0, sign-extended: g_rx_send (payload 0x5e53e0, 4 bytes, the
                      image's own asan_globals descriptor at 0xa9180). No instrumented check precedes this load.
     0x84190          a1 <> a3 goes to 0x841d8.
     0x84194-0x841a0  the instrumented check of the 8-byte load at fp + 56: a1 = fp + 56; a3 = the unsigned shadow
                      byte at ((fp + 56) >> 3) + 0x7fff8000. 0x841a4: a3 <> 0 goes to 0x84204-0x84208: a0 = fp + 56
                      and the call of TS___asan_report_load8 (0x596a8), the error path.
     0x841a8          a1 = the 8-byte load at fp + 56: f->body_len. 0x841ac: a1 <> 0 goes to 0x841d8.
     0x841b0-0x841bc  the instrumented check of the 2-byte load at fp + 30: a0 = fp + 30; a1 = the signed shadow byte
                      k at ((fp + 30) >> 3) + 0x7fff8000. 0x841c0: k = 0 goes on to 0x841c4; else 0x841f4-0x841fc:
                      a2 = ((fp + 30) & 7) + 1, and a2 < k (signed) goes back to 0x841c4; else 0x84200: the call of
                      TS___asan_report_load2 (0x59568) with a0 = fp + 30, the error path.
     0x841c4          a0 = the 2-byte load at fp + 30, zero-extended: f->retry. 0x841c8: a0 <> 0 goes to 0x841d8.
     0x841cc-0x841d4  ra reloaded, sp = sp + 16, return. This is the one return; on it a0-a4 hold values the code
                      loaded or computed (a4 only after the check at 0x841e0) and every other register is as at entry.
     0x841d8          call of TS___asan_handle_no_return (0x5a4c4), then 0x841dc call of TS_abort (0x93734): the
                      trap path.
   Error paths and the premise that rules each out:
     - TS___asan_report_load4 (0x841f0): addressable m (fp + 36) 4. Each byte x of [fp + 36, fp + 40) has its shadow
       byte k = 0 or x mod 8 < k <= 7. If the 4 bytes lie in one 8-byte granule, the last one gives k = 0 or
       ((fp + 36) & 7) + 3 < k; if they cross a granule boundary, byte 7 of the first granule is in the range and
       gives k = 0. Either way the check passes. asan_cells gives the shadow base 0x7fff8000 the code uses.
     - TS___asan_report_load2 (0x84200): addressable m (fp + 30) 2, the same argument with ((fp + 30) & 7) + 1.
     - TS___asan_report_load8 (0x84208): addressable m (fp + 56) 8. The 8 bytes run to the end of the granule of
       fp + 56, so byte 7 of that granule is in the range and its shadow byte is 0.
     - the trap path (0x841d8 / 0x841dc): reached only when the loaded ack differs from the loaded g_rx_send, or
       body_len <> 0, or retry <> 0. check_ack_frame_m Bw frame = Some _ gives sf_ack (rf frame) = g_rx_send Bw,
       sf_body_len (rf frame) = 0 and sf_retry (rf frame) = 0; g_rx_send Bw is a 4-byte u_at (0 <= it < 2^32), so the
       put bytes at fp + 36 and the world bytes at 0x5e53e0 (by tw_at, sub Bw OFF_g_rx_send 4) load to the same
       sign-extended word (TWorldG.v tw_read_val, tw_lw), and the put bytes of 0 load to 0.
   The shadow bytes lie in shadow memory and the frame in application memory (app_mem of both frame ends), so the ra
   store does not change them; off_stk keeps the store off the three fields and the two cells.
   Callee texts assumed: none (the only callees are the error-path entries and TS___asan_handle_no_return / TS_abort
   on the trap path).
   Caller: io_send (the call at 0x830b4 with a0 = sp + 8, its struct spec_frame f in its own 160-byte machine frame;
   return address 0x830b8). io_send takes no side-stack frame.
   Form: lib/A/Prog/check_state_wake_c.v (image A's leaf exemplar: the world premise, the model premise, the evt rsegs
   run, the munch / wmono / stk post, Bw' = Bw and the world after) with fuzz_frame's image-A
   diginet_frame_is_keepalive_c.v for a pointer argument read under instrumented checks (the argument as a Z value
   in a0, bytes_at of each field read, asan_cells, app_mem of the frame ends, off_stk and addressable of each range
   loaded); TW, TC and TG are check_state_wake_c.v's module names. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_ACK_FRAME : Z := 0x8415c.
Definition CHECK_ACK_FRAME_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-A base (TWorldA.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: g_rx_send (4 bytes). *)
Definition CHECK_ACK_FRAME_RX_SEND : Z := TA_g_rx_send.
Lemma check_ack_frame_rx_send_at : CHECK_ACK_FRAME_RX_SEND = 0x5e53e0.
Proof. reflexivity. Qed.

Definition check_ack_frame_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo : Z) (frame : list byte)
         (Bw Bw' : list byte),
    0 < fp ->
    fp mod 8 = 0 ->
    bytes_at rsegs m (fp + 36) (TW.put 4 (sf_ack (TC.rf frame))) ->
    bytes_at rsegs m (fp + 56) (TW.put 8 (sf_body_len (TC.rf frame))) ->
    bytes_at rsegs m (fp + 30) (TW.put 2 (sf_retry (TC.rf frame))) ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_ack_frame_m Bw frame = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_ACK_FRAME_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_ACK_FRAME_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_ACK_FRAME_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_ACK_FRAME_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_ACK_FRAME_FRAME CELL_K 8 ->
    off_stk sp CHECK_ACK_FRAME_FRAME (fp + 36) 4 -> addressable m (fp + 36) 4 ->
    off_stk sp CHECK_ACK_FRAME_FRAME (fp + 56) 8 -> addressable m (fp + 56) 8 ->
    off_stk sp CHECK_ACK_FRAME_FRAME (fp + 30) 2 -> addressable m (fp + 30) 2 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_ACK_FRAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fp) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ACK_FRAME) fc None m (seg_rom rsegs)).

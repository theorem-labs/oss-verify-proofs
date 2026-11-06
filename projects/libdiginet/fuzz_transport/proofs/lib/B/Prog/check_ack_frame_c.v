(* check_ack_frame_contract: check_ack_frame (fuzz/fuzz_transport.c:422-430; model lib/TModel/TCb.v
   check_ack_frame_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads three fields of the struct
   spec_frame at its argument and the int g_rx_send of the harness, and returns nothing. It stores into no harness
   global, so it takes the leaf form.
   Argument: a0 = fp, the address of a struct spec_frame (fuzz/spec.h:188-197; retry at 30 (2 bytes), ack at 36
   (4), body_len at 56 (8)) holding the parse rf frame of a frame buffer (TCb.v:128).
   Premises:
   - the plain contract's struct premise sframe_at m fp fa (rf frame) (lib/Prog/T/TContract.v:73-83), stated over
     image B's memory for the fields the code reads: 0 < fp, fp mod 8 = 0, and the bytes at fp + 36, fp + 56 and
     fp + 30 are the little-endian ack, body_len and retry of rf frame (bytes_at of TWorld.v put);
   - the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between the
     memory m, read through mrd (csw_view, check_state_wake_c.v), and the world Bw; check_ack_frame_m Bw frame =
     Some (Bw', tt), which holds exactly when ack = g_rx_send, body_len = 0 and retry = 0 (TCb.v:365-368);
   - the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull
     [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame store does not
     touch the world; both ends of the frame in application memory (app_mem), so the frame is not shadow memory;
   - asan_cells m (lib/B/AsanCells.v: among others the 8 bytes at GOT_CELL_K 0xa3cf0 hold CELL_K 0xac678 and the 8
     bytes at CELL_K hold 0x7fff8000); GOT_CELL_K's 8 bytes, CELL_K's 8 bytes and each field the code loads lie
     outside the frame (off_stk; the plain contract's off_window), and each loaded field is marked usable
     (addressable).
   Result: the run returns to ra with every register but a0-a4 unchanged (they are not specified: the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays
   usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the
   plain contract's post facts (lib/Prog/T/check_ack_frame_c.v: B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 188 code bytes of this function are equal in both files):
   symbol check_ack_frame, value 0x843d4, size 188 (47 words).
     0x843d4          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x843d8          the 8-byte store of ra at sp - 8 (own frame); 0x8444c loads it back.
     0x843dc-0x843e0  a1 = fp & 7; a1 <> 0 goes to 0x84460 (the unimp word below): the trap path.
     0x843e4-0x843ec  a1 = the 8-byte load at GOT_CELL_K 0xa3cf0 (it holds CELL_K); a2 = the 8-byte load at CELL_K
                      0xac678 (it holds 0x7fff8000).
     0x843f0-0x843fc  the instrumented check of the 4-byte load at fp + 36: a1 = fp + 36; a3 = the signed shadow byte
                      k at ((fp + 36) >> 3) + 0x7fff8000. 0x84400: k = 0 goes on to 0x84404; else 0x84464-0x8446c:
                      a4 = ((fp + 36) & 7) + 3, and a4 < k (signed) goes back to 0x84404; else 0x84470-0x84474:
                      a0 = fp + 36 and the call of __asan_report_load4 (0x59644), the error path.
     0x84404          a1 = the 4-byte load at fp + 36, sign-extended: f->ack.
     0x84408-0x8440c  a3 = the 4-byte load at 0x5e5060, sign-extended: g_rx_send (payload 0x5e5060 = TB_g_rx_send,
                      4 bytes, the image's own asan_globals descriptor at 0xa8de0). No instrumented check precedes
                      this load.
     0x84410          a1 <> a3 goes to 0x84458.
     0x84414-0x84420  the instrumented check of the 8-byte load at fp + 56: a1 = fp + 56; a3 = the unsigned shadow
                      byte at ((fp + 56) >> 3) + 0x7fff8000. 0x84424: a3 <> 0 goes to 0x84488-0x8448c: a0 = fp + 56
                      and the call of __asan_report_load8 (0x596e4), the error path.
     0x84428          a1 = the 8-byte load at fp + 56: f->body_len. 0x8442c: a1 <> 0 goes to 0x84458.
     0x84430-0x8443c  the instrumented check of the 2-byte load at fp + 30: a0 = fp + 30; a1 = the signed shadow byte
                      k at ((fp + 30) >> 3) + 0x7fff8000. 0x84440: k = 0 goes on to 0x84444; else 0x84478-0x84480:
                      a2 = ((fp + 30) & 7) + 1, and a2 < k (signed) goes back to 0x84444; else 0x84484: the call of
                      __asan_report_load2 (0x595a4) with a0 = fp + 30, the error path.
     0x84444          a0 = the 2-byte load at fp + 30, zero-extended: f->retry. 0x84448: a0 <> 0 goes to 0x84458.
     0x8444c-0x84454  ra reloaded, sp = sp + 16, return. This is the one return; on it a0-a4 hold values the code
                      loaded or computed (a4 only after the check at 0x84464) and every other register is as at entry.
     0x84458          call of __asan_handle_no_return (0x5a500), then 0x8445c call of abort (0x93390), then 0x84460
                      the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps), reached only if abort returns or from the test at 0x843e0: the trap path.
   Against image A's code (lib/A/Prog/check_ack_frame_c.v, 44 words): image B's code has three words image A's code
   does not have: the test of fp & 7 at 0x843dc-0x843e0, and the unimp word at 0x84460. The other 44 words are image
   A's instructions in the same order with image B's auipc / ld / lw / branch / jal immediates, the same registers
   and the same field offsets 36, 56 and 30.
   Error paths and the premise that rules each out:
     - there is no call of an __ubsan_handle_* entry in this function;
     - the branch at 0x843e0 to the unimp word: fp mod 8 = 0. The register a0 is Z_to_bv 64 fp and 8 divides 2^64,
       so its low three bits are fp mod 8 = 0, a1 = 0 and the branch is not taken;
     - __asan_report_load4 (0x84474): addressable m (fp + 36) 4. Each byte x of [fp + 36, fp + 40) has its shadow
       byte k = 0 or x mod 8 < k <= 7. If the 4 bytes lie in one 8-byte granule, the last one gives k = 0 or
       ((fp + 36) & 7) + 3 < k; if they cross a granule boundary, byte 7 of the first granule is in the range and
       gives k = 0. Either way the check passes. asan_cells gives the shadow base 0x7fff8000 the code uses.
     - __asan_report_load2 (0x84484): addressable m (fp + 30) 2, the same argument with ((fp + 30) & 7) + 1.
     - __asan_report_load8 (0x8448c): addressable m (fp + 56) 8. The 8 bytes run to the end of the granule of
       fp + 56, so byte 7 of that granule is in the range and its shadow byte is 0.
     - the trap path (0x84458 / 0x8445c / 0x84460): reached from 0x84410, 0x8442c and 0x84448 only when the loaded
       ack differs from the loaded g_rx_send, or body_len <> 0, or retry <> 0. check_ack_frame_m Bw frame = Some _
       gives sf_ack (rf frame) = g_rx_send Bw, sf_body_len (rf frame) = 0 and sf_retry (rf frame) = 0; g_rx_send Bw
       is a 4-byte u_at (0 <= it < 2^32), so the put bytes at fp + 36 and the world bytes at 0x5e5060 (by tw_at,
       sub Bw OFF_g_rx_send 4) load to the same sign-extended word (TWorldG.v tw_read_val, tw_lw), and the put bytes
       of 0 load to 0. The unimp word at 0x84460 follows the call of abort on this path, so the same premise rules
       it out there.
   The shadow bytes lie in shadow memory and the frame in application memory (app_mem of both frame ends), so the ra
   store does not change them; off_stk keeps the store off the three fields and the two cells.
   Callee texts assumed: none (the only callees are the error-path entries and __asan_handle_no_return / abort on
   the trap path).
   Caller: io_send (the call at 0x83094 with a0 = sp + 8 (0x83090), its struct spec_frame f in its own 160-byte
   machine frame, filled by the call of spec_read_frame at 0x83050 with a2 = sp + 8; return address 0x83098).
   io_send takes no side-stack frame.
   Form: lib/A/Prog/check_ack_frame_c.v (image A's contract of this function), at image B's entry, load address,
   world table TMAP_B, harness hull and runtime cells (lib/B/AsanCells.v); TW, TC and TG are check_state_wake_c.v's
   module names. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_ACK_FRAME : Z := 0x843d4.
Definition CHECK_ACK_FRAME_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-B base (TWorldB.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: g_rx_send (4 bytes). *)
Definition CHECK_ACK_FRAME_RX_SEND : Z := TB_g_rx_send.
Lemma check_ack_frame_rx_send_at : CHECK_ACK_FRAME_RX_SEND = 0x5e5060.
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
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_ack_frame_m Bw frame = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_ACK_FRAME_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_ACK_FRAME_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
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
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fp) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ACK_FRAME) fc None m (seg_rom rsegs)).

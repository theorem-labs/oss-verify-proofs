(* check_latest_control_contract: check_latest_control (fuzz/fuzz_transport.c:599-607; model lib/TModel/TCb.v
   check_latest_control_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that compares the member send of the
   struct spec_frame at its argument with M.host_counter and returns nothing. It stores into no harness global, so it
   takes the leaf form.
   Argument: a0 = fp, the address of a struct spec_frame holding rf frame (TCb.v:128; only send, the 4 bytes at
   fp + 32, is read).
   Premises:
   - as the plain contract (lib/Prog/T/check_latest_control_c.v): a0 = fp; from sframe_at (lib/Prog/T/TContract.v:73,
     stated there over the plain image's segments): 0 < fp, fp mod 8 = 0, and the member the code reads, the 4 bytes
     at fp + 32 holding put 4 (sf_send (rf frame)) (TContract.v:80 u_at SB 32 4 = sf_send f; sf_send is a be32
     value, so put 4 keeps it); the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table
     lib/B/Prog/TWorldB.v TMAP_B) between the memory m, read through csw_view (check_state_wake_c.v), and the world
     Bw; check_latest_control_m Bw frame = Some (Bw', tt), which holds exactly when sf_send (rf frame) =
     M.host_counter (TCb.v:480-481); the caller's stack below sp (stk, with room for the 16-byte frame); the frame
     [sp - 16, sp) outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v),
     so the frame store does not touch the world;
   - for the instrumented check (lib/B/AsanCells.v): asan_cells m (among others, the 8 bytes at GOT_CELL_K = 0xa3cf0
     hold CELL_K = 0xac678 and the 8 bytes at CELL_K hold 0x7fff8000); both ends of the frame are in application
     memory (app_mem), so the frame is not a shadow byte; GOT_CELL_K 8, CELL_K 8 and fp + 32 (4 bytes) are outside
     the frame (off_stk; off_window of the plain contract, for the member); the 4 bytes at fp + 32 are marked usable
     in the shadow map (addressable).
   Result: the run returns to ra with every register but a0, a1 and a2 unchanged (they are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 108 code bytes of this function are equal in both files):
   symbol check_latest_control, value 0x84490, size 108 (27 words).
     0x84490          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x84494          the 8-byte store of ra at sp - 8 (own frame); 0x844d0 loads it back.
     0x84498          a1 = a0 & 7: the alignment check of the pointer fp (struct spec_frame is 8-byte aligned).
     0x8449c          a1 <> 0 goes to 0x844dc, the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an
                      illegal instruction that traps): the alignment trap path.
     0x844a0-0x844a4  a1 = the 8-byte load at GOT_CELL_K = 0xa3cf0 (.got): CELL_K.
     0x844a8          a1 = the 8-byte load at CELL_K = 0xac678: 0x7fff8000.
     0x844ac          a0 = fp + 32.
     0x844b0-0x844b8  the instrumented check of the 4-byte load at a = fp + 32: a2 = a >> 3; a1 = the signed shadow
                      byte k at (a >> 3) + 0x7fff8000.
     0x844bc          k <> 0 goes to 0x844e0: a2 = (a & 7) + 3; a2 < k goes back to 0x844c0, else 0x844ec calls
                      __asan_report_load4 (0x59644, TB___asan_report_load4): the error path.
     0x844c0          a0 = the 4-byte load at fp + 32, sign-extended: send.
     0x844c4-0x844c8  a1 = the 4-byte load at 0x5dee34, sign-extended: M.host_counter (M payload 0x5dede0 = TB_M,
                      1648 bytes; TWorld.v A_M_host_counter = OFF_M + 84). No instrumented check precedes this load.
     0x844cc          a0 <> a1 goes to 0x844f0; else 0x844d0-0x844d8: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it every register but a0, a1, a2 is as at entry.
     0x844f0          call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), then 0x844f4 call of
                      abort (0x93390), then 0x844f8 the word 0xc0001073 (unimp), reached only if abort returns: the
                      trap path.
   Against image A's code (lib/A/Prog/check_latest_control_c.v, 23 words): the words at 0x84490-0x84494,
   0x844a0-0x844d8 and 0x844e0-0x844f4 are image A's twenty-three instructions in the same order with image B's
   auipc / load / branch / jal immediates. Image B's code has four words image A's code does not have: the alignment
   check at 0x84498-0x8449c (UBSan, trapping mode: no __ubsan_handle_* call), its unimp word at 0x844dc, and the
   unimp word at 0x844f8 after the call of abort.
   Error paths and the premise that rules each out:
     - the alignment trap at 0x844dc is reached only when a0 & 7 <> 0 at entry. a0 = Z_to_bv 64 fp and 8 divides
       2^64, so the low three bits of a0 are fp mod 8 = 0: the branch at 0x8449c falls through;
     - the call of __asan_report_load4 at 0x844ec is reached only when k <> 0 and (a & 7) + 3 >= k. addressable m
       (fp + 32) 4 gives, for the byte a + 3 (fp mod 8 = 0, so a mod 8 = 0 and a + 3 is in a's granule), k = 0 or
       3 < k <= 7: the check passes;
     - the trap path (0x844f0 / 0x844f4 / 0x844f8) is reached only when the two sign-extended ints differ. The
       member's bytes are put 4 (sf_send (rf frame)) and, by tw_at, the 4 bytes at 0x5dee34 are
       sub Bw A_M_host_counter 4 (TWorldG.v tw_read_val, tw_lw); both are 32-bit values, equal exactly when
       sf_send (rf frame) = M_host_counter Bw, which check_latest_control_m Bw frame = Some _ gives. The unimp word
       at 0x844f8 follows the call of abort on this path, so the same premise rules it out.
   Callee texts assumed: none (the only callees, __asan_report_load4, __asan_handle_no_return and abort, are on the
   error and trap paths).
   The caller: io_send, the calls at 0x830c4 and 0x83118 (return addresses 0x830c8 and 0x8311c; DgnTransportBList.v
   PCall TB_check_latest_control), each with a0 = io_send's sp + 8 (0x830c0, 0x83114), its struct spec_frame in its
   own machine frame.
   Form: lib/A/Prog/check_latest_control_c.v (image A's contract of this function), at image B's entry, load
   addresses, runtime cells (lib/B/AsanCells.v), world table TMAP_B and harness hull; its premises also refute the
   alignment trap, so the premise list is image A's. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.

Definition CHECK_LATEST_CONTROL : Z := 0x84490.
Definition CHECK_LATEST_CONTROL_FRAME : Z := 16.
(* The int of the world the code loads: M.host_counter, at M's image-B base plus the member's offset in M. *)
Definition CHECK_LATEST_CONTROL_HOST : Z := TB_M + (TW.A_M_host_counter - TW.OFF_M).
Lemma check_latest_control_host_at : CHECK_LATEST_CONTROL_HOST = 0x5dee34.
Proof. reflexivity. Qed.

Definition check_latest_control_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (fp : Z) (frame : list byte),
    a0 = Z_to_bv 64 fp ->
    0 < fp ->
    fp mod 8 = 0 ->
    bytes_at rsegs m (fp + 32) (TW.put 4 (DgnSpec.sf_send (TC.rf frame))) ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_latest_control_m Bw frame = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_CONTROL_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_LATEST_CONTROL_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME CELL_K 8 ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME (fp + 32) 4 ->
    addressable m (fp + 32) 4 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_CONTROL_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_CONTROL) fc None m (seg_rom rsegs)).

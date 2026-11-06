(* check_latest_control_contract: check_latest_control (fuzz/fuzz_transport.c:599-607; model lib/TModel/TCb.v
   check_latest_control_m) on fuzz_transport.asan (e89be137db17), a leaf that compares the member send of the struct
   spec_frame at its argument with M.host_counter and returns nothing. It stores into no harness global, so it takes
   the leaf form.
   Argument: a0 = fp, the address of a struct spec_frame holding rf frame (TCb.v:128; only send, the 4 bytes at
   fp + 32, is read).
   Premises:
   - as the plain contract (lib/Prog/T/check_latest_control_c.v): a0 = fp; from sframe_at (lib/Prog/T/TContract.v:73,
     stated there over the plain image's segments): 0 < fp, fp mod 8 = 0, and the member the code reads, the 4 bytes
     at fp + 32 holding put 4 (sf_send (rf frame)) (TContract.v:80 u_at SB 32 4 = sf_send f; sf_send is a be32
     value, so put 4 keeps it); the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table
     lib/A/Prog/TWorldA.v TMAP_A) between the memory m, read through csw_view (check_state_wake_c.v), and the world
     Bw; check_latest_control_m Bw frame = Some (Bw', tt), which holds exactly when sf_send (rf frame) =
     M.host_counter (TCb.v:480-481); the caller's stack below sp (stk, with room for the 16-byte frame); the frame
     [sp - 16, sp) outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so
     the frame store does not touch the world;
   - for the instrumented check (lib/A/AsanCells.v): asan_cells m (among others, the 8 bytes at GOT_CELL_K = 0xa4090
     hold CELL_K = 0xac9f8 and the 8 bytes at CELL_K hold 0x7fff8000); both ends of the frame are in application
     memory (app_mem), so the frame is not a shadow byte; GOT_CELL_K 8, CELL_K 8 and fp + 32 (4 bytes) are outside
     the frame (off_stk; off_window of the plain contract, for the member); the 4 bytes at fp + 32 are marked usable
     in the shadow map (addressable).
   Result: the run returns to ra with every register but a0, a1 and a2 unchanged (they are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 92 code bytes of
   this function are equal in both files): symbol check_latest_control, value 0x8420c, size 92 (23 words).
     0x8420c          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x84210          the 8-byte store of ra at sp - 8 (own frame); 0x84244 loads it back.
     0x84214-0x84218  a1 = the 8-byte load at GOT_CELL_K = 0xa4090 (.got): CELL_K.
     0x8421c          a1 = the 8-byte load at CELL_K = 0xac9f8: 0x7fff8000.
     0x84220          a0 = fp + 32.
     0x84224-0x8422c  the instrumented check of the 4-byte load at a = fp + 32: a2 = a >> 3; a1 = the signed shadow
                      byte k at (a >> 3) + 0x7fff8000.
     0x84230          k <> 0 goes to 0x84250: a2 = (a & 7) + 3; a2 < k goes back to 0x84234, else 0x8425c calls
                      __asan_report_load4 (0x59608, TS___asan_report_load4): the error path.
     0x84234          a0 = the 4-byte load at fp + 32, sign-extended: send.
     0x84238-0x8423c  a1 = the 4-byte load at 0x5df1b4, sign-extended: M.host_counter (M payload 0x5df160, 1648
                      bytes; TWorld.v A_M_host_counter = OFF_M + 84). No instrumented check precedes this load.
     0x84240          a0 <> a1 goes to 0x84260; else 0x84244-0x8424c: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it every register but a0, a1, a2 is as at entry.
     0x84260          call of __asan_handle_no_return (0x5a4c4, TS___asan_handle_no_return), then 0x84264 call of
                      abort (0x93734): the trap path.
   Error paths and the premise that rules each out:
     - the call of __asan_report_load4 at 0x8425c is reached only when k <> 0 and (a & 7) + 3 >= k. addressable m
       (fp + 32) 4 gives, for the byte a + 3 (fp mod 8 = 0, so a mod 8 = 0 and a + 3 is in a's granule), k = 0 or
       3 < k <= 7: the check passes;
     - the trap path (0x84260 / 0x84264) is reached only when the two sign-extended ints differ. The member's bytes
       are put 4 (sf_send (rf frame)) and, by tw_at, the 4 bytes at 0x5df1b4 are sub Bw A_M_host_counter 4
       (TWorldG.v tw_read_val, tw_lw); both are 32-bit values, equal exactly when sf_send (rf frame) =
       M_host_counter Bw, which check_latest_control_m Bw frame = Some _ gives.
   Callee texts assumed: none (the only callees, __asan_report_load4, __asan_handle_no_return and abort, are on the
   error and trap paths).
   The caller: io_send, the calls at 0x830e0 and 0x83134 (return addresses 0x830e4 and 0x83138; DgnTransportList.v
   PCall TS_check_latest_control), each with a0 = io_send's sp + 8, its struct spec_frame in its own machine frame.
   Form: check_state_wake_c.v (the image-A leaf form of the exemplar) with the instrumented-load premises of fuzz_frame's
   image-A diginet_frame_is_keepalive_c.v (asan_cells, app_mem of the frame ends, off_stk and addressable per loaded
   range), and the plain contract's argument, world and model premises, B' = B and the world after. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.

Definition CHECK_LATEST_CONTROL : Z := 0x8420c.
Definition CHECK_LATEST_CONTROL_FRAME : Z := 16.
(* The int of the world the code loads: M.host_counter, at M's image-A base plus the member's offset in M. *)
Definition CHECK_LATEST_CONTROL_HOST : Z := TA_M + (TW.A_M_host_counter - TW.OFF_M).
Lemma check_latest_control_host_at : CHECK_LATEST_CONTROL_HOST = 0x5df1b4.
Proof. reflexivity. Qed.

Definition check_latest_control_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (fp : Z) (frame : list byte),
    a0 = Z_to_bv 64 fp ->
    0 < fp ->
    fp mod 8 = 0 ->
    bytes_at rsegs m (fp + 32) (TW.put 4 (DgnSpec.sf_send (TC.rf frame))) ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_control_m Bw frame = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_CONTROL_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
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
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_CONTROL) fc None m (seg_rom rsegs)).

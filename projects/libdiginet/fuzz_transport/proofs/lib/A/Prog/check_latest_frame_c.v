(* check_latest_frame_contract: check_latest_frame (fuzz/fuzz_transport.c:582-597; model lib/TModel/TCb.v
   check_latest_frame_m) on fuzz_transport.asan (e89be137db17), a leaf that checks three members of the struct
   spec_frame at its first argument against g_cfg, g_raw, its second argument and M.host_counter, and returns nothing.
   It stores into no harness global, so it takes the leaf form.
   Arguments: a0 = fp, the address of a struct spec_frame holding rf frame (TCb.v:128; only send, the 4 bytes at
   fp + 32, ncmds, the byte at fp + 41, and body_len, the 8 bytes at fp + 56, are read); a1 = cmds, an unsigned int
   (the sign-extended 32-bit value, RV64 psABI).
   Premises:
   - as the plain contract (lib/Prog/T/check_latest_frame_c.v): a0 = fp, a1 = bv_swrap 32 cmds with
     0 <= cmds < 2^32; from sframe_at (lib/Prog/T/TContract.v:73, stated there over the plain image's segments):
     0 < fp, fp mod 8 = 0, and the three members the code reads, the bytes put 4 (sf_send (rf frame)) at fp + 32,
     put 1 (sf_ncmds (rf frame)) at fp + 41 and put 8 (sf_body_len (rf frame)) at fp + 56 (TContract.v:80-82;
     sf_send is a be32 value, sf_ncmds a byte, sf_body_len = numbytes - 16 with 16 <= numbytes < 2^16 or 0, so each
     put keeps its value); the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v
     TMAP_A) between the memory m, read through csw_view (check_state_wake_c.v), and the world Bw;
     check_latest_frame_m Bw frame cmds = Some (Bw', tt), which holds exactly when sf_body_len <= max_body,
     sf_ncmds <= max_cmds, (g_raw <> 0 or sf_ncmds = cmds) and sf_send = u32 (M.host_counter + sf_ncmds)
     (TCb.v:472-477); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp)
     outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store
     does not touch the world;
   - for the instrumented checks (lib/A/AsanCells.v): asan_cells m (among others, the 8 bytes at GOT_CELL_K =
     0xa4090 hold CELL_K = 0xac9f8 and the 8 bytes at CELL_K hold 0x7fff8000); both ends of the frame are in
     application memory (app_mem), so the frame is not a shadow byte; GOT_CELL_K 8, CELL_K 8 and the three members
     are outside the frame (off_stk; off_window of the plain contract, for the members); the bytes of each member are
     marked usable in the shadow map (addressable).
   Result: the run returns to ra with every register but a0 .. a6 unchanged (they are not specified: the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays usable
   (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the plain
   contract's post facts (B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 208 code bytes of
   this function are equal in both files): symbol check_latest_frame, value 0x843e0, size 208 (52 words).
     0x843e0          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x843e4          the 8-byte store of ra at sp - 8 (own frame); 0x84474 loads it back.
     0x843e8-0x843ec  a2 = the 8-byte load at GOT_CELL_K = 0xa4090 (.got): CELL_K.
     0x843f0          a3 = the 8-byte load at CELL_K = 0xac9f8: 0x7fff8000.
     0x843f4-0x84400  the instrumented check of the 8-byte load at fp + 56: a2 = fp + 56; a4 = the unsigned shadow
                      byte k at ((fp + 56) >> 3) + 0x7fff8000.
     0x84404          k <> 0 goes to 0x844a8: a0 = fp + 56, then 0x844ac calls __asan_report_load8 (0x596a8,
                      TS___asan_report_load8): the error path.
     0x84408          a2 = the 8-byte load at fp + 56: body_len.
     0x8440c-0x84410  a4 = 0x5df080: g_cfg (payload 0x5df080, 60 bytes).
     0x84414          a5 = the 4-byte load at 0x5df0b8, zero-extended: g_cfg.max_body (A_Cfg_max_body =
                      OFF_g_cfg + 56). No instrumented check precedes the loads of g_cfg, g_raw and M.
     0x84418          a5 < a2 (unsigned) goes to 0x84480.
     0x8441c-0x84428  the instrumented check of the byte load at fp + 41: a2 = fp + 41; a5 = the signed shadow byte k
                      at ((fp + 41) >> 3) + 0x7fff8000.
     0x8442c          k <> 0 goes to 0x84488: a6 = (fp + 41) & 7; a6 < k goes back to 0x84430, else 0x84490-0x84494:
                      a0 = fp + 41, call of __asan_report_load1 (0x594c8, TS___asan_report_load1): the error path.
     0x84430          a2 = the byte at fp + 41, zero-extended: ncmds.
     0x84434          a4 = the 4-byte load at 0x5df0b4, sign-extended: g_cfg.max_cmds (A_Cfg_max_cmds =
                      OFF_g_cfg + 52).
     0x84438          a4 < a2 (unsigned) goes to 0x84480.
     0x8443c          a1 = a2 (cmds = ncmds) goes to 0x8444c.
     0x84440-0x84444  a1 = the 4-byte load at 0x5df0e0, sign-extended: g_raw (payload 0x5df0e0, 4 bytes).
     0x84448          a1 = 0 goes to 0x84480.
     0x8444c-0x84458  the instrumented check of the 4-byte load at a = fp + 32: a0 = a; a1 = the signed shadow byte k
                      at (a >> 3) + 0x7fff8000.
     0x8445c          k <> 0 goes to 0x84498: a3 = (a & 7) + 3; a3 < k goes back to 0x84460, else 0x844a4 calls
                      __asan_report_load4 (0x59608, TS___asan_report_load4): the error path.
     0x84460-0x84464  a1 = the 4-byte load at 0x5df1b4, sign-extended: M.host_counter (M payload 0x5df160;
                      A_M_host_counter = OFF_M + 84).
     0x84468          a0 = the 4-byte load at fp + 32, sign-extended: send.
     0x8446c          a1 = the sign-extended low 32 bits of a1 + a2.
     0x84470          a0 <> a1 goes to 0x84480; else 0x84474-0x8447c: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it every register but a0 .. a6 is as at entry.
     0x84480          call of __asan_handle_no_return (0x5a4c4, TS___asan_handle_no_return), then 0x84484 call of
                      abort (0x93734): the trap path.
   Error paths and the premise that rules each out:
     - __asan_report_load8 (0x844ac): reached when the shadow byte k of fp + 56 is not 0. fp + 56 is 8-aligned, so
       addressable m (fp + 56) 8 gives, for the byte fp + 63 of the same granule, k = 0;
     - __asan_report_load1 (0x84494): reached when k <> 0 and ((fp + 41) & 7) >= k. addressable m (fp + 41) 1 gives
       k = 0 or (fp + 41) mod 8 < k <= 7: the check passes;
     - __asan_report_load4 (0x844a4): reached when k <> 0 and ((fp + 32) & 7) + 3 >= k. addressable m (fp + 32) 4
       gives, for the byte fp + 35 of fp + 32's granule, k = 0 or 3 < k <= 7: the check passes;
     - the trap path (0x84480 / 0x84484), from four branches. With the members' bytes (the premises) and the world's
       (tw_at: sub Bw A_Cfg_max_body 4, sub Bw A_Cfg_max_cmds 4, sub Bw OFF_g_raw 4, sub Bw A_M_host_counter 4;
       TWorldG.v tw_read_val, tw_lw, tw_lwu) the branches test Cfg_max_body Bw < sf_body_len, Cfg_max_cmds Bw <
       sf_ncmds (a max_cmds of 2^31 or more sign-extends to an unsigned value above any byte, as its unsigned value is
       above it), cmds <> sf_ncmds with g_raw Bw = 0 (bv_swrap 32 cmds equals the byte sf_ncmds exactly when
       cmds = sf_ncmds, as 0 <= cmds < 2^32), and sf_send <> u32 (M_host_counter Bw + sf_ncmds);
       check_latest_frame_m Bw frame cmds = Some _ rules out each.
   Callee texts assumed: none (the only callees, __asan_report_load8, __asan_report_load1, __asan_report_load4,
   __asan_handle_no_return and abort, are on the error and trap paths).
   The caller: io_send, the call at 0x832a0 (return address 0x832a4; DgnTransportList.v PCall TS_check_latest_frame),
   with a0 = io_send's sp + 8, its struct spec_frame in its own machine frame.
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

Definition CHECK_LATEST_FRAME : Z := 0x843e0.
Definition CHECK_LATEST_FRAME_FRAME : Z := 16.
(* The members of the world the code loads, at their global's image-A base plus the member's offset in it. *)
Definition CHECK_LATEST_FRAME_MAXBODY : Z := TA_g_cfg + (TW.A_Cfg_max_body - TW.OFF_g_cfg).
Definition CHECK_LATEST_FRAME_MAXCMDS : Z := TA_g_cfg + (TW.A_Cfg_max_cmds - TW.OFF_g_cfg).
Definition CHECK_LATEST_FRAME_HOST : Z := TA_M + (TW.A_M_host_counter - TW.OFF_M).
Lemma check_latest_frame_maxbody_at : CHECK_LATEST_FRAME_MAXBODY = 0x5df0b8.
Proof. reflexivity. Qed.
Lemma check_latest_frame_maxcmds_at : CHECK_LATEST_FRAME_MAXCMDS = 0x5df0b4.
Proof. reflexivity. Qed.
Lemma check_latest_frame_host_at : CHECK_LATEST_FRAME_HOST = 0x5df1b4.
Proof. reflexivity. Qed.
Lemma check_latest_frame_raw_at : TA_g_raw = 0x5df0e0.
Proof. reflexivity. Qed.

Definition check_latest_frame_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (fp : Z) (frame : list byte) (cmds : Z),
    a0 = Z_to_bv 64 fp ->
    a1 = Z_to_bv 64 (bv_swrap 32 cmds) ->
    0 <= cmds < 2 ^ 32 ->
    0 < fp ->
    fp mod 8 = 0 ->
    bytes_at rsegs m (fp + 32) (TW.put 4 (DgnSpec.sf_send (TC.rf frame))) ->
    bytes_at rsegs m (fp + 41) (TW.put 1 (DgnSpec.sf_ncmds (TC.rf frame))) ->
    bytes_at rsegs m (fp + 56) (TW.put 8 (DgnSpec.sf_body_len (TC.rf frame))) ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_frame_m Bw frame cmds = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_FRAME_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_FRAME_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_LATEST_FRAME_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_LATEST_FRAME_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME CELL_K 8 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME (fp + 56) 8 ->
    addressable m (fp + 56) 8 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME (fp + 41) 1 ->
    addressable m (fp + 41) 1 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME (fp + 32) 4 ->
    addressable m (fp + 32) 4 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_FRAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_FRAME) fc None m (seg_rom rsegs)).

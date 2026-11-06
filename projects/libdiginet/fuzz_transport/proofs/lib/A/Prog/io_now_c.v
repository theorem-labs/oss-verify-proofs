(* io_now_contract: io_now (fuzz/fuzz_transport.c:931-935; model lib/TModel/TCb.v io_now_m) on fuzz_transport.asan
   (e89be137db17), a leaf that returns the 8 bytes of the harness global g_now. It has no frame and stores nothing,
   so it takes the leaf form.
   Arguments: a0 = ctx, not read.
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; the caller's stack below sp (stk; the
   frame is 0 bytes). io_now_m is total, so there is no model premise. The code stores nothing, so there is no
   off_stk premise.
   Result: the run returns to ra with a0 = io_now_m Bw (= g_now Bw, TCb.v:792, TWorld.v:454: the 8 bytes of g_now,
   unsigned little-endian) and every other register unchanged. It writes no byte (munch of the empty frame range),
   every writable byte stays writable (wmono), the stack below sp stays usable (stk), and the world relation still
   holds at the new memory with the same world. These are the plain contract's post facts (lib/Prog/T/io_now_c.v:
   a0 = io_now_m B, wmem rsegs m' B, munch of the empty frame).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 12 code bytes of
   this function are equal in both files): symbol io_now, value 0x8356c, size 12 (3 words).
     0x8356c          a0 = pc + 0x55c000 = 0x5df56c. There is no stack adjustment: the frame is 0 bytes. No
                      side-stack frame.
     0x83570          a0 = the 8-byte load at a0 - 1132 = 0x5df100: g_now (payload 0x5df100, 8 bytes, the image's
                      own asan_globals descriptor; TWorldA.v TA_g_now, TWorld.v OFF_g_now). No instrumented check
                      precedes this load: the code reads no shadow byte and no runtime cell.
     0x83574          return. This is the one return; on it a0 = the 8 bytes of g_now and every other register is
                      as at entry.
   Error paths: none (no call, no instrumented check, no trap word).
   Callee texts assumed: none.
   The image holds io_now's address in the 8-byte word at 0xa3d78 (.data.rel.ro: the third function word of
   __const.LLVMFuzzerTestOneInput.io, DgnTransportCg.v TRANS_IO + 24; TImgA.v ti_io_now timg_A = 0x8356c);
   LLVMFuzzerTestOneInput copies those 32 bytes into its frame (0x813e0) and diginet_session_init copies them into
   g_s.io (0x865d4); diginet_session_poll calls io_now through g_s.io.now_us at 0x8af44, 0x8afe4 and 0x8b064 (return
   addresses 0x8af48, 0x8afe8, 0x8b068).
   Form: lib/Prog/T/io_now_c.v (the plain contract: world premise, a0 = io_now_m B, the world after) in the image-A
   leaf form of check_state_wake_c.v, with the result register of fuzz_frame's diginet_mac_is_digidesign_c.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.

Definition IO_NOW : Z := 0x8356c.
Definition IO_NOW_FRAME : Z := 0.
(* The 8 bytes the code loads: g_now's image-A payload. *)
Definition IO_NOW_G_NOW : Z := TA_g_now.
Lemma io_now_g_now_at : IO_NOW_G_NOW = 0x5df100.
Proof. reflexivity. Qed.

Definition io_now_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + IO_NOW_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (TC.io_now_m Bw)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - IO_NOW_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IO_NOW) fc None m (seg_rom rsegs)).

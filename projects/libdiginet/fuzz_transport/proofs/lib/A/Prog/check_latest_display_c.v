(* check_latest_display_contract: check_latest_display (fuzz/fuzz_transport.c:646-654; model lib/TModel/TCb.v
   check_latest_display_m) on fuzz_transport.asan (e89be137db17), a leaf that reads members of the harness globals M,
   g_now and g_cfg and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_latest_display_m Bw =
   Some (Bw', tt), which holds exactly when M.display_sent is 0 or u64 (g_now - M.last_display) is not below
   g_cfg.display_gap_us (TCb.v:545-547); the caller's stack below sp (stk, with room for the 16-byte frame); the
   frame [sp - 16, sp) outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v),
   so the frame store does not touch the world.
   Result: the run returns to ra with every register but a0, a1 and a2 unchanged (they are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (lib/Prog/T/check_latest_display_c.v: B' = B, wmem rsegs m' B, munch of the
   frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 72 code bytes of
   this function are equal in both files): symbol check_latest_display, value 0x84844, size 72 (18 words).
     0x84844          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x84848          the 8-byte store of ra at sp - 8 (own frame); 0x84878 loads it back.
     0x8484c-0x84850  a0 = 0x5df160: M (payload 0x5df160, 1648 bytes, the image's own asan_globals descriptor).
     0x84854          a1 = the 4-byte load at a0 + 72 = 0x5df1a8, sign-extended: M.display_sent (TWorld.v
                      A_M_display_sent = OFF_M + 72).
     0x84858          a1 = 0 goes to 0x84878 (the return).
     0x84860          a0 = the 8-byte load at 0x5df1a0: M.last_display (A_M_last_display = OFF_M + 64).
     0x8485c, 0x84864 a1 = the 8-byte load at 0x5df100: g_now (payload 0x5df100, 8 bytes).
     0x84868-0x8486c  a2 = the 4-byte load at 0x5df0b0, zero-extended: g_cfg.display_gap_us (g_cfg payload 0x5df080,
                      60 bytes; A_Cfg_display_gap_us = OFF_g_cfg + 48).
     0x84870          a1 = a1 - a0 (mod 2^64).
     0x84874          a1 < a2 (unsigned) goes to 0x84884; else 0x84878-0x84880: ra reloaded, sp = sp + 16, return.
                      This is the one return (also reached from 0x84858); on it every register but a0, a1, a2 is as
                      at entry.
     0x84884          call of __asan_handle_no_return (0x5a4c4, TS___asan_handle_no_return), then 0x84888 call of
                      abort (0x93734): the trap path.
   No instrumented check precedes any load: the code reads no shadow byte and no runtime cell.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* entry in this function;
     - the trap path (0x84884 / 0x84888) is reached only when M.display_sent is not 0 and u64 (g_now -
       M.last_display) < display_gap_us. By tw_at the loaded bytes are sub Bw A_M_display_sent 4,
       sub Bw A_M_last_display 8, sub Bw OFF_g_now 8 and sub Bw A_Cfg_display_gap_us 4, so the loaded values are
       M_display_sent Bw (sign-extended), M_last_display Bw, g_now Bw and Cfg_display_gap_us Bw (TWorldG.v
       tw_read_val, tw_lw, tw_lwu), and check_latest_display_m Bw = Some _ rules the trap condition out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   The caller: io_send, the call at 0x83320 (return address 0x83324; DgnTransportList.v PCall
   TS_check_latest_display).
   Form: check_state_wake_c.v (the image-A leaf form of the exemplar), with the plain contract
   lib/Prog/T/check_latest_display_c.v's world premise, model premise, B' = B and the world after. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.

Definition CHECK_LATEST_DISPLAY : Z := 0x84844.
Definition CHECK_LATEST_DISPLAY_FRAME : Z := 16.
(* The members the code loads, at their global's image-A base plus the member's offset in it. *)
Definition CHECK_LATEST_DISPLAY_SENT : Z := TA_M + (TW.A_M_display_sent - TW.OFF_M).
Definition CHECK_LATEST_DISPLAY_LAST : Z := TA_M + (TW.A_M_last_display - TW.OFF_M).
Definition CHECK_LATEST_DISPLAY_GAP : Z := TA_g_cfg + (TW.A_Cfg_display_gap_us - TW.OFF_g_cfg).
Lemma check_latest_display_sent_at : CHECK_LATEST_DISPLAY_SENT = 0x5df1a8.
Proof. reflexivity. Qed.
Lemma check_latest_display_last_at : CHECK_LATEST_DISPLAY_LAST = 0x5df1a0.
Proof. reflexivity. Qed.
Lemma check_latest_display_gap_at : CHECK_LATEST_DISPLAY_GAP = 0x5df0b0.
Proof. reflexivity. Qed.
Lemma check_latest_display_now_at : TA_g_now = 0x5df100.
Proof. reflexivity. Qed.

Definition check_latest_display_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_display_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_DISPLAY_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_DISPLAY_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_DISPLAY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_DISPLAY) fc None m (seg_rom rsegs)).

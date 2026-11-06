(* check_latest_display_contract: check_latest_display (fuzz/fuzz_transport.c:646-654; model lib/TModel/TCb.v
   check_latest_display_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads members of the harness
   globals M, g_now and g_cfg and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_latest_display_m Bw =
   Some (Bw', tt), which holds exactly when M.display_sent is 0 or u64 (g_now - M.last_display) is not below
   g_cfg.display_gap_us (TCb.v:545-547); the caller's stack below sp (stk, with room for the 16-byte frame); the
   frame [sp - 16, sp) outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals
   (lib/B/TransportGB.v), so the frame store does not touch the world.
   Result: the run returns to ra with every register but a0, a1 and a2 unchanged (they are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (lib/Prog/T/check_latest_display_c.v: B' = B, wmem rsegs m' B, munch of the
   frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 76 code bytes of this function are equal in both files):
   symbol check_latest_display, value 0x84bd0, size 76 (19 words).
     0x84bd0          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x84bd4          the 8-byte store of ra at sp - 8 (own frame); 0x84c04 loads it back.
     0x84bd8-0x84bdc  a0 = 0x5dede0: M (payload 0x5dede0 = TB_M, 1648 bytes, the image's own asan_globals descriptor
                      at 0xa8c60).
     0x84be0          a1 = the 4-byte load at a0 + 72 = 0x5dee28, sign-extended: M.display_sent (TWorld.v
                      A_M_display_sent = OFF_M + 72).
     0x84be4          a1 = 0 goes to 0x84c04 (the return).
     0x84be8          a1 = 0x5debe8.
     0x84bec          a0 = the 8-byte load at a0 + 64 = 0x5dee20: M.last_display (A_M_last_display = OFF_M + 64).
     0x84bf0          a1 = the 8-byte load at a1 + 0x198 = 0x5ded80: g_now (payload 0x5ded80 = TB_g_now, 8 bytes).
     0x84bf4-0x84bf8  a2 = the 4-byte load at 0x5ded30, zero-extended: g_cfg.display_gap_us (g_cfg payload 0x5ded00 =
                      TB_g_cfg, 60 bytes; A_Cfg_display_gap_us = OFF_g_cfg + 48).
     0x84bfc          a1 = a1 - a0 (mod 2^64).
     0x84c00          a1 < a2 (unsigned) goes to 0x84c10; else 0x84c04-0x84c0c: ra reloaded, sp = sp + 16, return.
                      This is the one return (also reached from 0x84be4); on it every register but a0, a1, a2 is as
                      at entry.
     0x84c10          call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), then 0x84c14 call of
                      abort (0x93390), then 0x84c18 the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an
                      illegal instruction that traps), reached only if abort returns: the trap path.
   No instrumented check precedes any load: the code reads no shadow byte and no runtime cell. The subtraction at
   0x84bfc is of unsigned 64-bit values, and the code has no overflow check on it.
   Against image A's code (lib/A/Prog/check_latest_display_c.v, 18 words): the words at 0x84bd0-0x84c14 are the same
   eighteen instructions in the same order with image B's auipc / addi / load / jal immediates; the word at 0x84c18
   is the one instruction image A's code does not have.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* or __ubsan_handle_* entry in this function;
     - the trap path (0x84c10 / 0x84c14 / 0x84c18) is reached only when M.display_sent is not 0 and u64 (g_now -
       M.last_display) < display_gap_us. By tw_at the loaded bytes are sub Bw A_M_display_sent 4,
       sub Bw A_M_last_display 8, sub Bw OFF_g_now 8 and sub Bw A_Cfg_display_gap_us 4, so the loaded values are
       M_display_sent Bw (sign-extended), M_last_display Bw, g_now Bw and Cfg_display_gap_us Bw (TWorldG.v
       tw_read_val, tw_lw, tw_lwu), and check_latest_display_m Bw = Some _ rules the trap condition out. The unimp
       word at 0x84c18 follows the call of abort on this path, so the same premise rules it out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   The caller: io_send, the call at 0x832a8 (return address 0x832ac; DgnTransportBList.v PCall
   TB_check_latest_display).
   Form: lib/A/Prog/check_latest_display_c.v (image A's contract of this function), at image B's entry, load
   addresses, world table TMAP_B and harness hull. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.

Definition CHECK_LATEST_DISPLAY : Z := 0x84bd0.
Definition CHECK_LATEST_DISPLAY_FRAME : Z := 16.
(* The members the code loads, at their global's image-B base plus the member's offset in it. *)
Definition CHECK_LATEST_DISPLAY_SENT : Z := TB_M + (TW.A_M_display_sent - TW.OFF_M).
Definition CHECK_LATEST_DISPLAY_LAST : Z := TB_M + (TW.A_M_last_display - TW.OFF_M).
Definition CHECK_LATEST_DISPLAY_GAP : Z := TB_g_cfg + (TW.A_Cfg_display_gap_us - TW.OFF_g_cfg).
Lemma check_latest_display_sent_at : CHECK_LATEST_DISPLAY_SENT = 0x5dee28.
Proof. reflexivity. Qed.
Lemma check_latest_display_last_at : CHECK_LATEST_DISPLAY_LAST = 0x5dee20.
Proof. reflexivity. Qed.
Lemma check_latest_display_gap_at : CHECK_LATEST_DISPLAY_GAP = 0x5ded30.
Proof. reflexivity. Qed.
Lemma check_latest_display_now_at : TB_g_now = 0x5ded80.
Proof. reflexivity. Qed.

Definition check_latest_display_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_latest_display_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_DISPLAY_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_DISPLAY_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_DISPLAY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_DISPLAY) fc None m (seg_rom rsegs)).

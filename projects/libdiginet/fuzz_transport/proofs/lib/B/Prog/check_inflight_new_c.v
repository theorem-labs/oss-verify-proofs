(* check_inflight_new_contract: check_inflight_new (fuzz/fuzz_transport.c:432-448; model lib/TModel/TCb.v
   check_inflight_new_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads two ints and one 8-byte word
   of the harness global M and the 8-byte harness global g_now, and returns nothing. It stores into no harness
   global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_inflight_new_m Bw =
   Some (Bw', tt), which holds exactly when M.state = S_ONLINE (2), M.fly.on = 0 and M.backoff_until <= g_now
   (TCb.v:371-374); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp)
   outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame
   store does not touch the world.
   Result: the run returns to ra with every register but a0, a1 and a2 unchanged (they are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (lib/Prog/T/check_inflight_new_c.v: B' = B, wmem rsegs m' B, munch of the
   frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 76 code bytes of this function are equal in both files):
   symbol check_inflight_new, value 0x84654, size 76 (19 words).
     0x84654          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x84658          the 8-byte store of ra at sp - 8 (own frame); 0x84688 loads it back.
     0x8465c-0x84660  a0 = 0x5dede0: M (payload 0x5dede0 = TB_M, 1648 bytes, the image's own asan_globals descriptor
                      at 0xa8c60).
     0x84664          a1 = the 4-byte load at a0 + 12 = 0x5dedec, sign-extended: M.state (TWorld.v A_M_state =
                      OFF_M + 12).
     0x84668-0x8466c  a2 = 2; a1 <> a2 goes to 0x84694.
     0x84670          a1 = the 4-byte load at a0 + 96 = 0x5dee40, sign-extended: M.fly.on (A_M_fly_on = OFF_M + 96).
     0x84674          a1 <> 0 goes to 0x84694.
     0x84678-0x8467c  a1 = the 8-byte load at 0x5ded80: g_now (payload 0x5ded80 = TB_g_now, 8 bytes, descriptor at
                      0xa8ba0).
     0x84680          a0 = the 8-byte load at a0 + 56 = 0x5dee18: M.backoff_until (A_M_backoff_until = OFF_M + 56).
     0x84684          a1 < a0 as unsigned 64-bit words goes to 0x84694; else 0x84688-0x84690: ra reloaded,
                      sp = sp + 16, return. This is the one return; on it a0, a1 and a2 hold M.backoff_until, g_now
                      and 2, and every other register is as at entry.
     0x84694          call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), then 0x84698 call of
                      abort (0x93390), then 0x8469c the word 0xc0001073 (unimp: a write of the read-only CSR cycle,
                      an illegal instruction that traps), reached only if abort returns: the trap path.
   No instrumented check precedes any of the four loads: the code reads no shadow byte and no runtime cell.
   Against image A's code (lib/A/Prog/check_inflight_new_c.v, 18 words): the words at 0x84654-0x84698 are the same
   eighteen instructions with image B's auipc / addi / ld / jal immediates; the word at 0x8469c is the one
   instruction image A's code does not have.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* or __ubsan_handle_* entry in this function;
     - the trap path (0x84694 / 0x84698 / 0x8469c) is reached only when M.state <> 2, M.fly.on <> 0, or
       g_now < M.backoff_until as unsigned words. By tw_at the loaded values are M_state Bw and M_fly_on Bw
       sign-extended (s32_at; TWorldG.v tw_read_val, tw_lw), and g_now Bw and M_backoff_until Bw (u_at of 8 bytes: the
       whole word), and check_inflight_new_m Bw = Some _ gives M_state Bw = S_ONLINE, M_fly_on Bw = 0 and
       M_backoff_until Bw <= g_now Bw. The unimp word at 0x8469c follows the call of abort on this path, so the same
       premise rules it out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   Caller: io_send (the call at 0x8317c, return address 0x83180).
   Form: lib/A/Prog/check_inflight_new_c.v (image A's contract of this function), at image B's entry, load
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

Definition CHECK_INFLIGHT_NEW : Z := 0x84654.
Definition CHECK_INFLIGHT_NEW_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-B base (TWorldB.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: M.state (4 bytes); M.fly.on (4
   bytes); g_now (8 bytes); M.backoff_until (8 bytes). *)
Definition CHECK_INFLIGHT_NEW_STATE : Z := TB_M + (TW.A_M_state - TW.OFF_M).
Definition CHECK_INFLIGHT_NEW_FLY_ON : Z := TB_M + (TW.A_M_fly_on - TW.OFF_M).
Definition CHECK_INFLIGHT_NEW_NOW : Z := TB_g_now.
Definition CHECK_INFLIGHT_NEW_BACKOFF : Z := TB_M + (TW.A_M_backoff_until - TW.OFF_M).
Lemma check_inflight_new_state_at : CHECK_INFLIGHT_NEW_STATE = 0x5dedec.
Proof. reflexivity. Qed.
Lemma check_inflight_new_fly_on_at : CHECK_INFLIGHT_NEW_FLY_ON = 0x5dee40.
Proof. reflexivity. Qed.
Lemma check_inflight_new_now_at : CHECK_INFLIGHT_NEW_NOW = 0x5ded80.
Proof. reflexivity. Qed.
Lemma check_inflight_new_backoff_at : CHECK_INFLIGHT_NEW_BACKOFF = 0x5dee18.
Proof. reflexivity. Qed.

Definition check_inflight_new_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_inflight_new_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_INFLIGHT_NEW_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_INFLIGHT_NEW_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_INFLIGHT_NEW_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_INFLIGHT_NEW) fc None m (seg_rom rsegs)).

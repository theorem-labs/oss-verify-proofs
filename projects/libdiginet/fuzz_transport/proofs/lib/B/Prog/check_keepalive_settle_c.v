(* check_keepalive_settle_contract: check_keepalive_settle (fuzz/fuzz_transport.c:773-783; model lib/TModel/TCb.v
   check_keepalive_settle_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads the int g_raw, two ints
   and two 8-byte words of the harness global M and the 8-byte harness global g_now, and returns nothing. It stores
   into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_keepalive_settle_m Bw =
   Some (Bw', tt), which holds exactly when NOT (g_raw = 0, M.state = S_ONLINE (2), M.fly.on = 0,
   M.backoff_until <= g_now and M.next_ka <= g_now) (TCb.v:605-608); the caller's stack below sp (stk, with room for
   the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness
   globals (lib/B/TransportGB.v), so the frame store does not touch the world.
   Result: the run returns to ra with every register but a0, a1 and a2 unchanged (they are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (lib/Prog/T/check_keepalive_settle_c.v: B' = B, wmem rsegs m' B, munch of the
   frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 96 code bytes of this function are equal in both files):
   symbol check_keepalive_settle, value 0x860a4, size 96 (24 words).
     0x860a4          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x860a8          the 8-byte store of ra at sp - 8 (own frame); 0x860ec loads it back.
     0x860ac-0x860b0  a0 = the 4-byte load at 0x5ded60, sign-extended: g_raw (payload 0x5ded60 = TB_g_raw, 4 bytes,
                      the image's own asan_globals descriptor at 0xa8b60).
     0x860b4          a0 <> 0 goes to the return 0x860ec.
     0x860b8-0x860bc  a0 = 0x5dede0: M (payload 0x5dede0 = TB_M, 1648 bytes, descriptor at 0xa8c60).
     0x860c0          a1 = the 4-byte load at a0 + 12 = 0x5dedec, sign-extended: M.state (TWorld.v A_M_state =
                      OFF_M + 12).
     0x860c4-0x860c8  a2 = 2; a1 <> a2 goes to the return 0x860ec.
     0x860cc          a1 = the 4-byte load at a0 + 96 = 0x5dee40, sign-extended: M.fly.on (A_M_fly_on = OFF_M + 96).
     0x860d0          a1 <> 0 goes to the return 0x860ec.
     0x860d4-0x860d8  a1 = the 8-byte load at 0x5ded80: g_now (payload 0x5ded80 = TB_g_now, 8 bytes, descriptor at
                      0xa8ba0).
     0x860dc          a2 = the 8-byte load at a0 + 56 = 0x5dee18: M.backoff_until (A_M_backoff_until = OFF_M + 56).
     0x860e0          a1 < a2 as unsigned 64-bit words goes to the return 0x860ec.
     0x860e4          a0 = the 8-byte load at a0 + 48 = 0x5dee10: M.next_ka (A_M_next_ka = OFF_M + 48).
     0x860e8          a1 >= a0 as unsigned 64-bit words goes to 0x860f8; else on to the return.
     0x860ec-0x860f4  ra reloaded, sp = sp + 16, return: the one return, reached from 0x860b4, 0x860c8, 0x860d0,
                      0x860e0 or 0x860e8. On it a0 holds g_raw (from 0x860b4), 0x5dede0 (from 0x860c8, 0x860d0
                      or 0x860e0) or M.next_ka (through 0x860e8); a1 and a2 are as at entry (from 0x860b4) or hold
                      values the code loaded or set; every other register is as at entry.
     0x860f8          call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), then 0x860fc call of
                      abort (0x93390), then 0x86100 the word 0xc0001073 (unimp: a write of the read-only CSR cycle,
                      an illegal instruction that traps), reached only if abort returns: the trap path.
   No instrumented check precedes any of the six loads: the code reads no shadow byte and no runtime cell.
   Against image A's code (lib/A/Prog/check_keepalive_settle_c.v, 23 words): the words at 0x860a4-0x860fc are the
   same twenty-three instructions with image B's lw / addi / ld / jal immediates (the three auipc words are equal);
   the word at 0x86100 is the one instruction image A's code does not have.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* or __ubsan_handle_* entry in this function;
     - the trap path (0x860f8 / 0x860fc / 0x86100) is reached only when g_raw = 0, M.state = 2, M.fly.on = 0,
       M.backoff_until <= g_now and M.next_ka <= g_now (unsigned words). By tw_at the loaded values are g_raw Bw,
       M_state Bw and M_fly_on Bw sign-extended (s32_at; TWorldG.v tw_read_val, tw_lw), and g_now Bw,
       M_backoff_until Bw and M_next_ka Bw (u_at of 8 bytes: the whole word), so on that path
       check_keepalive_settle_m Bw is None, against its premise Some (Bw', tt). The unimp word at 0x86100 follows
       the call of abort on this path, so the same premise rules it out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   Caller: settle (the call at 0x838dc, return address 0x838e0).
   Form: lib/A/Prog/check_keepalive_settle_c.v (image A's contract of this function), at image B's entry, load
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

Definition CHECK_KEEPALIVE_SETTLE : Z := 0x860a4.
Definition CHECK_KEEPALIVE_SETTLE_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-B base (TWorldB.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: g_raw (4 bytes); M.state (4
   bytes); M.fly.on (4 bytes); g_now (8 bytes); M.backoff_until (8 bytes); M.next_ka (8 bytes). *)
Definition CHECK_KEEPALIVE_SETTLE_RAW : Z := TB_g_raw.
Definition CHECK_KEEPALIVE_SETTLE_STATE : Z := TB_M + (TW.A_M_state - TW.OFF_M).
Definition CHECK_KEEPALIVE_SETTLE_FLY_ON : Z := TB_M + (TW.A_M_fly_on - TW.OFF_M).
Definition CHECK_KEEPALIVE_SETTLE_NOW : Z := TB_g_now.
Definition CHECK_KEEPALIVE_SETTLE_BACKOFF : Z := TB_M + (TW.A_M_backoff_until - TW.OFF_M).
Definition CHECK_KEEPALIVE_SETTLE_NEXT_KA : Z := TB_M + (TW.A_M_next_ka - TW.OFF_M).
Lemma check_keepalive_settle_raw_at : CHECK_KEEPALIVE_SETTLE_RAW = 0x5ded60.
Proof. reflexivity. Qed.
Lemma check_keepalive_settle_state_at : CHECK_KEEPALIVE_SETTLE_STATE = 0x5dedec.
Proof. reflexivity. Qed.
Lemma check_keepalive_settle_fly_on_at : CHECK_KEEPALIVE_SETTLE_FLY_ON = 0x5dee40.
Proof. reflexivity. Qed.
Lemma check_keepalive_settle_now_at : CHECK_KEEPALIVE_SETTLE_NOW = 0x5ded80.
Proof. reflexivity. Qed.
Lemma check_keepalive_settle_backoff_at : CHECK_KEEPALIVE_SETTLE_BACKOFF = 0x5dee18.
Proof. reflexivity. Qed.
Lemma check_keepalive_settle_next_ka_at : CHECK_KEEPALIVE_SETTLE_NEXT_KA = 0x5dee10.
Proof. reflexivity. Qed.

Definition check_keepalive_settle_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_keepalive_settle_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_KEEPALIVE_SETTLE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_KEEPALIVE_SETTLE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_KEEPALIVE_SETTLE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_KEEPALIVE_SETTLE) fc None m (seg_rom rsegs)).

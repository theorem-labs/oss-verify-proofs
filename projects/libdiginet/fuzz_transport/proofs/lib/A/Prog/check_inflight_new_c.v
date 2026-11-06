(* check_inflight_new_contract: check_inflight_new (fuzz/fuzz_transport.c:432-448; model lib/TModel/TCb.v
   check_inflight_new_m) on fuzz_transport.asan (e89be137db17), a leaf that reads two ints and one 8-byte word of the
   harness global M and the 8-byte harness global g_now, and returns nothing. It stores into no harness global, so it
   takes the leaf form.
   Arguments: none.
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through mrd (csw_view, check_state_wake_c.v), and the world Bw; check_inflight_new_m Bw =
   Some (Bw', tt), which holds exactly when M.state = S_ONLINE (2), M.fly.on = 0 and M.backoff_until <= g_now
   (TCb.v:371-374); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp)
   outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store
   does not touch the world.
   Result: the run returns to ra with every register but a0, a1 and a2 unchanged (they are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (lib/Prog/T/check_inflight_new_c.v: B' = B, wmem rsegs m' B, munch of the
   frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 72 code bytes of
   this function are equal in both files): symbol check_inflight_new, value 0x84398, size 72 (18 words).
     0x84398          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x8439c          the 8-byte store of ra at sp - 8 (own frame); 0x843cc loads it back.
     0x843a0-0x843a4  a0 = 0x5df160, the base of M (payload 0x5df160, 1648 bytes, the image's own asan_globals
                      descriptor at 0xa9000).
     0x843a8          a1 = the 4-byte load at a0 + 12 = 0x5df16c, sign-extended: M.state (TWorld.v A_M_state =
                      OFF_M + 12).
     0x843ac-0x843b0  a2 = 2; a1 <> a2 goes to 0x843d8.
     0x843b4          a1 = the 4-byte load at a0 + 96 = 0x5df1c0, sign-extended: M.fly.on (A_M_fly_on = OFF_M + 96).
     0x843b8          a1 <> 0 goes to 0x843d8.
     0x843bc-0x843c0  a1 = the 8-byte load at 0x5df100: g_now (payload 0x5df100, 8 bytes, descriptor at 0xa8f40).
     0x843c4          a0 = the 8-byte load at a0 + 56 = 0x5df198: M.backoff_until (A_M_backoff_until = OFF_M + 56).
     0x843c8          a1 < a0 as unsigned 64-bit words goes to 0x843d8; else 0x843cc-0x843d4: ra reloaded,
                      sp = sp + 16, return. This is the one return; on it a0, a1 and a2 hold M.backoff_until, g_now
                      and 2, and every other register is as at entry.
                      No instrumented check precedes any of the four loads: the code reads no shadow byte and no
                      runtime cell.
     0x843d8          call of TS___asan_handle_no_return (0x5a4c4), then 0x843dc call of TS_abort (0x93734): the
                      trap path.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* entry in this function;
     - the trap path (0x843d8 / 0x843dc) is reached only when M.state <> 2, M.fly.on <> 0, or g_now < M.backoff_until
       as unsigned words. By tw_at the loaded values are M_state Bw and M_fly_on Bw sign-extended (s32_at; TWorldG.v
       tw_read_val, tw_lw), and g_now Bw and M_backoff_until Bw (u_at of 8 bytes: the whole word), and
       check_inflight_new_m Bw = Some _ gives M_state Bw = S_ONLINE, M_fly_on Bw = 0 and
       M_backoff_until Bw <= g_now Bw.
   Callee texts assumed: none (the only callees, TS___asan_handle_no_return and TS_abort, are on the trap path).
   Caller: io_send (the call at 0x8318c, return address 0x83190).
   Form: lib/A/Prog/check_state_wake_c.v (image A's leaf exemplar: the world premise, the model premise, the evt rsegs
   run, the munch / wmono / stk post, Bw' = Bw and the world after, the kept registers in the MS (mkR ...) state);
   TW, TC and TG are that file's module names. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_INFLIGHT_NEW : Z := 0x84398.
Definition CHECK_INFLIGHT_NEW_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-A base (TWorldA.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: M.state (4 bytes); M.fly.on (4
   bytes); g_now (8 bytes); M.backoff_until (8 bytes). *)
Definition CHECK_INFLIGHT_NEW_STATE : Z := TA_M + (TW.A_M_state - TW.OFF_M).
Definition CHECK_INFLIGHT_NEW_FLY_ON : Z := TA_M + (TW.A_M_fly_on - TW.OFF_M).
Definition CHECK_INFLIGHT_NEW_NOW : Z := TA_g_now.
Definition CHECK_INFLIGHT_NEW_BACKOFF : Z := TA_M + (TW.A_M_backoff_until - TW.OFF_M).
Lemma check_inflight_new_state_at : CHECK_INFLIGHT_NEW_STATE = 0x5df16c.
Proof. reflexivity. Qed.
Lemma check_inflight_new_fly_on_at : CHECK_INFLIGHT_NEW_FLY_ON = 0x5df1c0.
Proof. reflexivity. Qed.
Lemma check_inflight_new_now_at : CHECK_INFLIGHT_NEW_NOW = 0x5df100.
Proof. reflexivity. Qed.
Lemma check_inflight_new_backoff_at : CHECK_INFLIGHT_NEW_BACKOFF = 0x5df198.
Proof. reflexivity. Qed.

Definition check_inflight_new_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_inflight_new_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_INFLIGHT_NEW_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_INFLIGHT_NEW_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_INFLIGHT_NEW_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_INFLIGHT_NEW) fc None m (seg_rom rsegs)).

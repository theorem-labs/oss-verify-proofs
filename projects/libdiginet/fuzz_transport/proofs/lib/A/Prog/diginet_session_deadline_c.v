(* diginet_session_deadline_contract: diginet_session_deadline (transport/src/diginet_session.c:476-503; model
   lib/TModel/TSess0.v diginet_session_deadline_m) on fuzz_transport.asan (e89be137db17), a leaf that reads fields of
   the session s = &g_s and returns a uint64_t deadline. It stores into no harness global, so it takes the leaf form.
   The binary inlines ms and min64; it calls no program function.
   Arguments: a0 = s, the address of g_s's image-A payload (DIGINET_SESSION_DEADLINE_S = TWorldA.v TA_g_s, as the
   plain contract's a0 = W_BASE_PLAIN + OFF_g_s); a1 = now (uint64_t).
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; diginet_session_deadline_m Bw now =
   Some r (TSess0.v:259-292; None is the UBSan build's array-bounds trap of s->queue[i].display with i >= 512,
   TSess0.v:243-246); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp)
   outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store
   does not touch the world; both ends of the frame in application memory (app_mem), so the frame store changes no
   shadow byte; the runtime cells (asan_cells: the 8 bytes at GOT_CELL_K 0xa4090 hold CELL_K 0xac9f8 and the 8 bytes
   at CELL_K hold 0x7fff8000) outside the frame (off_stk); g_s's payload [s, s + 18264) addressable (its bytes are
   marked usable in the shadow map).
   Result: the run returns to ra with a0 = r and every register but t0, t1, t2, a1-a7 unchanged. It writes only its
   frame (munch), every writable byte stays writable (wmono), the stack below sp stays usable (stk), and the world
   relation still holds at the new memory with the same world. These are the plain contract's post facts
   (lib/Prog/T/diginet_session_deadline_c.v: a0 = r, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 948 code bytes of
   this function are equal in both files): symbol diginet_session_deadline, value 0x8a9d4, size 948 (237 words).
     0x8a9d4          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x8a9d8          the 8-byte store of ra at sp - 8 (own frame); 0x8ac90 loads it back. This is the only store.
     0x8a9dc-0x8a9e8  a2 = s; a0 = now + 1000000 (the deadline d, mod 2^64).
     0x8a9ec          s = 0 goes to the return 0x8ac90 with a0 = d. Not taken: s = 0x5df9c0.
     0x8a9f4-0x8a9f8  a3 = the 8-byte load at GOT_CELL_K 0xa4090 (= CELL_K), a4 = the 8-byte load at CELL_K (the
                      shadow base 0x7fff8000).
     0x8a9fc-0x8ac8c  the body: loads of the fields of g_s at s + k, each after the instrumented check of its address
                      a (the shadow byte at (a >> 3) + a4):
                        4-byte (signed or unsigned) loads of state (+112, 0x8aa10), cfg.wake_timeout_ms (+44,
                        0x8aa58), cfg.offline_ms (+40, 0x8aab8), inflight (+212, 0x8aae4 and 0x8ab44),
                        cfg.ack_timeout_ms (+28, 0x8ab78), queued (+18144, 0x8abb4), display_sent (+208, 0x8ac3c),
                        cfg.display_gap_us (+48, 0x8ac70); when the shadow byte k <> 0 the code compares (a & 7) + 3
                        with k and goes back to the load when (a & 7) + 3 < k, else to the error path;
                        8-byte loads of wake_sent_us (+152, 0x8aa50), last_rx_us (+176, 0x8aab0), next_keepalive_us
                        (+184, 0x8ab18), backoff_until_us (+192, 0x8ab1c and 0x8abd0), inflight_sent_us (+1752,
                        0x8ab70), last_display_us (+200, 0x8ac68); the shadow byte k <> 0 goes to the error path;
                        the 1-byte loads of queue[i].display (+1785 + 32 i, 0x8abf0) for i = 0, 1, ... while i <
                        queued and the last byte read is not 0; when k <> 0 the code compares a & 7 with k and goes
                        back to the load when (a & 7) < k, else to the error path.
                      (TWorld.v A_S_state = OFF_g_s + 112, A_S_cfg_wake_timeout_ms = OFF_g_s + 44, ...,
                      A_S_queue_display i = OFF_g_s + 1760 + 32 i + 25, A_S_queued = OFF_g_s + 18144.) The state
                      compares (0 and 3 return d, 1 is the waking branch, 2 the online branch), the multiplications by
                      1000 (ms), the unsigned minima and maxima and the final clamp to now are those of the model.
     0x8ac90-0x8ac98  ra reloaded, sp = sp + 16, return. This is the one return; on it a0 is the deadline, t0, t1,
                      t2, a1-a7 may differ from their entry values and every other register is as at entry.
   Error paths and the premise that rules each out:
     - the calls of __asan_report_load4 (0x59608, TS___asan_report_load4) at 0x8acac, 0x8acc0, 0x8acd4, 0x8ace8,
       0x8acfc, 0x8ad10, 0x8ad24, 0x8ad38, 0x8ad4c, of __asan_report_load8 (0x596a8, TS___asan_report_load8) at
       0x8ad54, 0x8ad5c, 0x8ad64, 0x8ad6c, 0x8ad74, 0x8ad7c, 0x8ad84, and of __asan_report_load1 (0x594c8,
       TS___asan_report_load1) at 0x8ac18 are reached only when a checked load at a fails its check. Every checked
       load lies in [s, s + 18264): the queue loop reads queue[i].display only for i < 512 on the runs the model
       premise allows (i = 512 with the loop still running is the model's None), and 1785 + 32 * 511 < 18264. s is
       8-aligned (0x5df9c0), every 8-byte field offset is a multiple of 8 and every 4-byte one is 0 or 4 mod 8, so
       each checked access [a, a + n) lies in one 8-byte granule and its last byte has address mod 8 = (a & 7) + n -
       1; addressable m s 18264 gives for that byte k = 0 or (a & 7) + n - 1 < k <= 7: k = 0 for n = 8, and the
       check passes for n = 4 and n = 1. asan_cells gives a4 = 0x7fff8000, so the loaded byte is the shadow byte
       addressable speaks of.
     - there is no trap path: the code has no unimp word and calls no abort; the model's None (the UBSan build's
       bounds trap at i >= 512) is a run the model premise excludes, on which this code would read queue[512].display
       inside g_s's payload without failing a check.
   By tw_at each loaded value is the model's (TWorldG.v tw_read_val, tw_lw / tw_lwu / tw_lbu;
   an 8-byte load needs no extension lemma): S_state Bw,
   S_cfg_wake_timeout_ms Bw, ..., S_queue_display Bw i.
   Callee texts assumed: none (the only callees, __asan_report_load1/4/8, are on the error path).
   The callers are check_inflight_settle (the call at 0x85db8, return address 0x85dbc) and diginet_session_poll (the
   call at 0x8af54, return address 0x8af58), each with a0 = 0x5df9c0.
   Form: lib/Prog/T/diginet_session_deadline_c.v (the plain contract: a0 = s, a1 = now, world premise, model premise,
   a0 = r and the world after) in the image-A leaf form of check_state_wake_c.v, with the register arguments of
   fuzz_frame's diginet_cursor_init_c.v and the instrumented-load premises of its diginet_frame_is_keepalive_c.v
   (asan_cells, app_mem of both frame ends, off_stk of the two cells, addressable of the checked range). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0.
Import ListNotations.
Open Scope Z_scope.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.

Definition DIGINET_SESSION_DEADLINE : Z := 0x8a9d4.
Definition DIGINET_SESSION_DEADLINE_FRAME : Z := 16.
(* s: g_s's image-A payload, and its size (every field the code reads lies in it). *)
Definition DIGINET_SESSION_DEADLINE_S : Z := TA_g_s.
Definition DIGINET_SESSION_DEADLINE_SN : Z := TW.SZ_g_s.
Lemma diginet_session_deadline_s_at :
  DIGINET_SESSION_DEADLINE_S = 0x5df9c0 /\ DIGINET_SESSION_DEADLINE_SN = 18264.
Proof. split; reflexivity. Qed.

Definition diginet_session_deadline_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo now r : Z) (Bw : list byte),
    a0 = Z_to_bv 64 DIGINET_SESSION_DEADLINE_S ->
    a1 = Z_to_bv 64 now ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_A (csw_view m) Bw ->
    TS0.diginet_session_deadline_m Bw now = Some r ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_SESSION_DEADLINE_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    app_mem (bv_unsigned sp - DIGINET_SESSION_DEADLINE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME CELL_K 8 ->
    addressable m DIGINET_SESSION_DEADLINE_S DIGINET_SESSION_DEADLINE_SN ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_SESSION_DEADLINE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SESSION_DEADLINE) fc None m (seg_rom rsegs)).

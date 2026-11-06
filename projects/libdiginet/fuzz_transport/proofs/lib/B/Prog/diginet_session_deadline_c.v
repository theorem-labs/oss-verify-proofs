(* diginet_session_deadline_contract: diginet_session_deadline (transport/src/diginet_session.c:476-503; model
   lib/TModel/TSess0.v diginet_session_deadline_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads
   fields of the session s = &g_s and returns a uint64_t deadline. It stores into no harness global, so it takes the
   leaf form. The binary inlines ms and min64; it calls no program function.
   Arguments: a0 = s, the address of g_s's image-B payload (DIGINET_SESSION_DEADLINE_S = TWorldB.v TB_g_s, as the
   plain contract's a0 = W_BASE_PLAIN + OFF_g_s); a1 = now (uint64_t).
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; diginet_session_deadline_m Bw now =
   Some r (TSess0.v:259-292; None is the UBSan build's array-bounds trap of s->queue[i].display with i >= 512,
   TSess0.v:243-246, which this image's code has: the branch at 0x8a8f4 below); the caller's stack below sp (stk,
   with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the
   18 harness globals (lib/B/TransportGB.v), so the frame store does not touch the world; both ends of the frame in
   application memory (app_mem), so the frame store changes no shadow byte; the runtime cells (lib/B/AsanCells.v
   asan_cells: the 8 bytes at GOT_CELL_K 0xa3cf0 hold CELL_K 0xac678 and the 8 bytes at CELL_K hold 0x7fff8000)
   outside the frame (off_stk); g_s's payload [s, s + 18264) addressable (its bytes are marked usable in the shadow
   map).
   Result: the run returns to ra with a0 = r and every register but t0, t1, t2, a1-a7, t3, t4, t5 unchanged. It
   writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays usable (stk),
   and the world relation still holds at the new memory with the same world. These are the plain contract's post
   facts (lib/Prog/T/diginet_session_deadline_c.v: a0 = r, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 984 code bytes of this function are equal in both files):
   symbol diginet_session_deadline, value 0x8a6c0, size 984 (246 words).
     0x8a6c0          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x8a6c4          the 8-byte store of ra at sp - 8 (own frame); 0x8a884 loads it back. This is the only store.
     0x8a6c8-0x8a6d4  a2 = s; a0 = now + 1000000 (the deadline d, mod 2^64).
     0x8a6d8          s = 0 goes to the return 0x8a884 with a0 = d. Not taken: s = 0x5df640.
     0x8a6dc-0x8a6e0  s & 7 <> 0 goes to the unimp word at 0x8a9a8 (the UBSan alignment check of s). Not taken.
     0x8a6e4-0x8a6ec  a3 = the 8-byte load at GOT_CELL_K 0xa3cf0 (= CELL_K), a5 = the 8-byte load at CELL_K (the
                      shadow base 0x7fff8000).
     0x8a6f0-0x8a9a4  the body (around the return at 0x8a884-0x8a88c): loads of the fields of g_s at s + k, each after
                      the instrumented check of its address a (the shadow byte at (a >> 3) + a5):
                        4-byte (signed or unsigned) loads of state (+112, 0x8a704), cfg.wake_timeout_ms (+44,
                        0x8a74c), cfg.offline_ms (+40, 0x8a7ac), inflight (+212, 0x8a7d8 and 0x8a838),
                        cfg.ack_timeout_ms (+28, 0x8a86c), queued (+18144, 0x8a8b0), display_sent (+208, 0x8a954),
                        cfg.display_gap_us (+48, 0x8a988); when the shadow byte k <> 0 the code compares (a & 7) + 3
                        with k and goes back to the load when (a & 7) + 3 < k, else to the error path;
                        8-byte loads of wake_sent_us (+152, 0x8a744), last_rx_us (+176, 0x8a7a4), next_keepalive_us
                        (+184, 0x8a80c), backoff_until_us (+192, 0x8a810 and 0x8a8cc), inflight_sent_us (+1752,
                        0x8a864), last_display_us (+200, 0x8a980); the shadow byte k <> 0 goes to the error path;
                        the 1-byte loads of queue[i].display (+1785 + 32 i, 0x8a90c) for i = 0, 1, ... while i <
                        queued and the last byte read is not 0; when k <> 0 the code compares a & 7 with k and goes
                        back to the load when (a & 7) < k, else to the error path. Before the check of queue[i]
                        (t1 = i + 1, a7 = 32 i, t2 = the bitwise not of s + 1760): t1 = 513 (i = 512) goes to the
                        unimp word at 0x8a9a8 (0x8a8f4, the UBSan array-bounds check of s->queue[i]), and a7 above t2
                        (unsigned: s + 1760 + 32 i past 2^64 - 1) goes there too (0x8a8f8, the UBSan pointer-overflow
                        check).
                      (TWorld.v A_S_state = OFF_g_s + 112, A_S_cfg_wake_timeout_ms = OFF_g_s + 44, ...,
                      A_S_queue_display i = OFF_g_s + 1760 + 32 i + 25, A_S_queued = OFF_g_s + 18144.) The state
                      compares (0 and 3 return d, 1 is the waking branch, 2 the online branch), the multiplications by
                      1000 (ms), the unsigned minima and maxima and the final clamp to now are those of the model.
     0x8a884-0x8a88c  ra reloaded, sp = sp + 16, return. This is the one return; on it a0 is the deadline, t0, t1,
                      t2, a1-a7, t3, t4, t5 may differ from their entry values and every other register is as at entry.
     0x8a9a8          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path, from the three branches at 0x8a6e0, 0x8a8f4 and 0x8a8f8.
   Against image A's code (lib/A/Prog/diginet_session_deadline_c.v, 237 words): the same loads, checks, compares and
   error-path calls, with image B's addresses and other scratch registers; image B's code has three UBSan checks
   image A's code does not have (the test of s & 7 at 0x8a6dc-0x8a6e0, and in the queue loop the test of i = 512 at
   0x8a8f4 and of the pointer overflow at 0x8a8f8, with the setup of t1, t2, t3 at 0x8a8d8-0x8a8ec), the unimp word
   at 0x8a9a8 they go to, and it writes t3, t4 and t5, which image A's code keeps: so the result leaves t3, t4, t5
   unspecified, where image A's contract keeps them.
   Error paths and the premise that rules each out:
     - the calls of __asan_report_load4 (0x59644, TB___asan_report_load4) at 0x8a9bc, 0x8a9d0, 0x8a9e4, 0x8a9f8,
       0x8aa0c, 0x8aa20, 0x8aa34, 0x8aa48, 0x8aa5c, of __asan_report_load8 (0x596e4, TB___asan_report_load8) at
       0x8aa64, 0x8aa6c, 0x8aa74, 0x8aa7c, 0x8aa84, 0x8aa8c, 0x8aa94, and of __asan_report_load1 (0x59504,
       TB___asan_report_load1) at 0x8a938 are reached only when a checked load at a fails its check. Every checked
       load lies in [s, s + 18264): the queue loop reads queue[i].display only for i < 512 (at i = 512 the code goes
       to the trap path first), and 1785 + 32 * 511 < 18264. s is 8-aligned (0x5df640), every 8-byte field offset is
       a multiple of 8 and every 4-byte one is 0 or 4 mod 8, so each checked access [a, a + n) lies in one 8-byte
       granule and its last byte has address mod 8 = (a & 7) + n - 1; addressable m s 18264 gives for that byte
       k = 0 or (a & 7) + n - 1 < k <= 7: k = 0 for n = 8, and the check passes for n = 4 and n = 1. asan_cells gives
       a5 = 0x7fff8000, so the loaded byte is the shadow byte addressable speaks of.
     - the trap path (the unimp word at 0x8a9a8), from three branches: 0x8a6e0 is taken when s & 7 <> 0, and
       a0 = Z_to_bv 64 DIGINET_SESSION_DEADLINE_S gives s = 0x5df640, so s & 7 = 0; 0x8a8f4 is taken when the loop
       reaches i = 512 still running (queued > 512 and queue[0..511].display all not 0), which is exactly the run on
       which diginet_session_deadline_m Bw now is None (deadline_display_only_m at S_queue_N <=? i, TSess0.v:255;
       the loaded bytes are the model's by tw_at), so the premise = Some r rules it out; 0x8a8f8 is taken when
       s + 1760 + 32 i >= 2^64, and s = 0x5df640 with i <= 511 gives s + 1760 + 32 i < 2^64.
     - there is no call of abort and no call of an __ubsan_handle_* entry in this function.
   By tw_at each loaded value is the model's (TWorldG.v tw_read_val, tw_lw / tw_lwu / tw_lbu;
   an 8-byte load needs no extension lemma): S_state Bw,
   S_cfg_wake_timeout_ms Bw, ..., S_queue_display Bw i.
   Callee texts assumed: none (the only callees, __asan_report_load1/4/8, are on the error path).
   The callers are check_inflight_settle (the call at 0x86044, return address 0x86048, a0 = 0x5df640) and
   diginet_session_poll (the call at 0x8ac6c, return address 0x8ac70, a0 = its own argument s, 0x5df640)
   (DgnTransportBList.v PCall TB_diginet_session_deadline).
   Form: lib/A/Prog/diginet_session_deadline_c.v (image A's contract of this function), at image B's entry, load
   address of g_s, runtime cells (lib/B/AsanCells.v), world table TMAP_B and harness hull, with t3, t4, t5 in the
   result's unspecified registers (above). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0.
Import ListNotations.
Open Scope Z_scope.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.

Definition DIGINET_SESSION_DEADLINE : Z := 0x8a6c0.
Definition DIGINET_SESSION_DEADLINE_FRAME : Z := 16.
(* s: g_s's image-B payload, and its size (every field the code reads lies in it). *)
Definition DIGINET_SESSION_DEADLINE_S : Z := TB_g_s.
Definition DIGINET_SESSION_DEADLINE_SN : Z := TW.SZ_g_s.
Lemma diginet_session_deadline_s_at :
  DIGINET_SESSION_DEADLINE_S = 0x5df640 /\ DIGINET_SESSION_DEADLINE_SN = 18264.
Proof. split; reflexivity. Qed.

Definition diginet_session_deadline_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo now r : Z) (Bw : list byte),
    a0 = Z_to_bv 64 DIGINET_SESSION_DEADLINE_S ->
    a1 = Z_to_bv 64 now ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_B (csw_view m) Bw ->
    TS0.diginet_session_deadline_m Bw now = Some r ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_SESSION_DEADLINE_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    app_mem (bv_unsigned sp - DIGINET_SESSION_DEADLINE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME CELL_K 8 ->
    addressable m DIGINET_SESSION_DEADLINE_S DIGINET_SESSION_DEADLINE_SN ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_SESSION_DEADLINE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SESSION_DEADLINE) fc None m (seg_rom rsegs)).

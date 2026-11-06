(* check_state_settle_contract: check_state_settle (fuzz/fuzz_transport.c:690-742; model lib/TModel/TCb.v
   check_state_settle_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that compares the harness globals GOT and
   OW (e2, e3, ndata, desk, foreign, n, and the first min(OW.n, 16) transitions' state / old / reason) and g_s.state
   with M.state, and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_state_settle_m Bw = Some (Bw',
   tt) (TCb.v:581-591); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp)
   outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame
   store does not touch the world; both ends of the frame in application memory (app_mem), so the frame store changes
   no shadow byte; the runtime cells (lib/B/AsanCells.v asan_cells: the 8 bytes at GOT_CELL_K 0xa3cf0 hold CELL_K
   0xac678 and the 8 bytes at CELL_K hold 0x7fff8000) outside the frame (off_stk); the two transition arrays
   GOT.t[0..16) and OW.t[0..16) (CHECK_STATE_SETTLE_GOT_T / _OW_T, 192 bytes each) addressable (their bytes are marked
   usable in the shadow map).
   Result: the run returns to ra with every register but t0, t1, t2, a0-a7, t3, t4, t5 unchanged (the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays
   usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the
   plain contract's post facts (lib/Prog/T/check_state_settle_c.v: B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 544 code bytes of this function are equal in both files):
   symbol check_state_settle, value 0x85dbc, size 544 (136 words).
     0x85dbc          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85dc0          the 8-byte store of ra at sp - 8 (own frame); 0x85fa0 loads it back. This is the only store.
     0x85dc4-0x85dd0  a3 = 0x5e4f60 (GOT, TWorldB.v TB_GOT, payload 224 bytes), a4 = 0x5f2ce0 (OW, TB_OW, payload 304).
     0x85dd4-0x85e0c  five pairs of 4-byte loads, GOT + k and OW + k for k = 196 (e2), 200 (e3), 220 (ndata), 208
                      (desk), 212 (foreign) (TWorld.v A_GOT_e2 ... = OFF_GOT + k, A_OW_e2 ... = OFF_OW + k); each pair
                      unequal goes to the trap path 0x85fb0. No instrumented check precedes these loads.
     0x85e10-0x85e20  a0 = the 8-byte load at GOT_CELL_K 0xa3cf0 (= CELL_K), a1 = the 4-byte load at GOT + 0 (n),
                      a6 = the 4-byte load at OW + 0 (n), a5 = the 8-byte load at CELL_K (the shadow base 0x7fff8000).
     0x85e24-0x85e4c  when GOT.n = OW.n: a0 = the 4-byte load at 0x5df6b0 (g_s + 112, TWorld.v A_S_state), a1 = the
                      4-byte load at 0x5dedec (M + 12, A_M_state), no instrumented check; OW.n <= 0 (signed) goes to
                      0x85fac (a0 = a1 returns, else the trap path); else a7 = (a0 = a1). When GOT.n <> OW.n: a7 = 0
                      and OW.n <= 0 goes to the trap path.
     0x85e50-0x85f30  a6 = min(OW.n, 16) (unsigned), t1 = 12 i, t0 = 1; the loop for i < a6 loads the 4-byte state,
                      old and reason of GOT.t[i] at GOT + 4 + 12 i + {0, 4, 8} (0x85e94, 0x85ec8, 0x85f04) and of
                      OW.t[i] at OW + 4 + 12 i + {0, 4, 8} (0x85ea0, 0x85ed0, 0x85f0c) (A_GOT_t_state i = OFF_GOT + 4
                      + 12 i, ...), each after the instrumented check of its address a: the shadow byte k at (a >> 3) +
                      a5 (0x85e74, 0x85eb0, 0x85ef0 for GOT, 0x85e90, 0x85ec4, 0x85f00 for OW); when k <> 0 the code
                      compares (a & 7) + 3 with k (0x85f34-0x85f8c) and goes back to the load when (a & 7) + 3 < k,
                      else to the error path. t3 = (state equal and old equal) and a7 &= t3; t0 &= (reason equal).
                      The olds are checked and loaded only when the states are equal (0x85ea4).
     0x85f98-0x85fa8  a7 = 0 or t0 = 0 goes to the trap path; else ra reloaded, sp = sp + 16, return. These returns
                      (0x85fa8, also reached from 0x85fac) are the only ones; on them t0, t1, t2, a0-a7, t3, t4, t5 may
                      differ from their entry values and every other register is as at entry.
     0x85fb0          call of __asan_handle_no_return (0x5a500, DgnTransportBAddr.v TB___asan_handle_no_return), then
                      0x85fb4 call of abort (0x93390, TB_abort), then 0x85fb8 the word 0xc0001073 (unimp: a write of
                      the read-only CSR cycle, an illegal instruction that traps), reached only if abort returns: the
                      trap path.
   Against image A's code (lib/A/Prog/check_state_settle_c.v, 135 words): the same loads, checks, compares and calls,
   with image B's addresses; inside the loop image B's code orders the checks and loads differently and uses other
   scratch registers (from the same set, t0-t5 and a0-a7). The word at 0x85fb8 is the one instruction image A's code
   does not have.
   Error paths and the premise that rules each out:
     - the six calls of __asan_report_load4 (0x59644, TB___asan_report_load4) at 0x85f94, 0x85fc0, 0x85fc4, 0x85fc8,
       0x85fd0, 0x85fd8 are reached only when a checked 4-byte load at a has its shadow byte k <> 0 and
       (a & 7) + 3 >= k. Every checked load lies in GOT.t[0..16) or OW.t[0..16) (i < 16), and a & 7 is 0 or 4
       (GOT and OW are 8-aligned and 4 + 12 i is 0 or 4 mod 8), so the 4 bytes [a, a + 4) lie in one 8-byte granule
       and the byte a + 3 has (a + 3) mod 8 = (a & 7) + 3; addressable m CHECK_STATE_SETTLE_GOT_T 192 (or _OW_T)
       gives for it k = 0 or (a & 7) + 3 < k <= 7: the check passes. asan_cells gives a5 = 0x7fff8000, so the
       loaded byte is the shadow byte addressable speaks of.
     - there is no call of an __ubsan_handle_* entry and no UBSan check in this function (the loop's index is below
       16 by the min at 0x85e50-0x85e58);
     - the trap path (0x85fb0 / 0x85fb4 / 0x85fb8) is reached only when one of the compares fails. By tw_at each
       loaded value is the model's (TWorldG.v tw_read_val, tw_lw): GOT_e2 Bw, OW_e2 Bw, ..., GOT_n Bw, OW_n Bw,
       S_state Bw, M_state Bw, GOT_t_state Bw i, ...; check_state_settle_m Bw = Some _ gives every compare its
       passing outcome (TCb.v:581-591, the loop state_settle_loop :569-578). The unimp word at 0x85fb8 follows the
       call of abort on this path, so the same premise rules it out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return, abort and __asan_report_load4, are on the
   trap and error paths).
   The caller is settle (the call at 0x838d4, return address 0x838d8; DgnTransportBList.v PCall
   TB_check_state_settle).
   Form: lib/A/Prog/check_state_settle_c.v (image A's contract of this function), at image B's entry, load addresses,
   runtime cells (lib/B/AsanCells.v), world table TMAP_B and harness hull. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_STATE_SETTLE : Z := 0x85dbc.
Definition CHECK_STATE_SETTLE_FRAME : Z := 16.
(* GOT and OW at their image-B bases; the code reads the first 224 bytes of each (n, t[16], e2, e3, desk, foreign,
   ndata: up to A_GOT_ndata + 4 = OFF_GOT + 224, A_OW_ndata + 4 = OFF_OW + 224). *)
Definition CHECK_STATE_SETTLE_GOT : Z := TB_GOT.
Definition CHECK_STATE_SETTLE_OW : Z := TB_OW.
Definition CHECK_STATE_SETTLE_RD : Z := TW.A_GOT_ndata + 4 - TW.OFF_GOT.
(* The two transition arrays (the checked loads): GOT.t[0..16) and OW.t[0..16), 12 bytes an entry. *)
Definition CHECK_STATE_SETTLE_GOT_T : Z := TB_GOT + (TW.A_GOT_t_state 0 - TW.OFF_GOT).
Definition CHECK_STATE_SETTLE_OW_T : Z := TB_OW + (TW.A_OW_t_state 0 - TW.OFF_OW).
Definition CHECK_STATE_SETTLE_T_LEN : Z := TW.GOT_t_ESZ * TW.GOT_t_N.
(* The two ints read when GOT.n = OW.n: g_s.state and M.state. *)
Definition CHECK_STATE_SETTLE_S_STATE : Z := TB_g_s + (TW.A_S_state - TW.OFF_g_s).
Definition CHECK_STATE_SETTLE_M_STATE : Z := TB_M + (TW.A_M_state - TW.OFF_M).
Lemma check_state_settle_addrs :
  CHECK_STATE_SETTLE_GOT = 0x5e4f60 /\ CHECK_STATE_SETTLE_OW = 0x5f2ce0 /\ CHECK_STATE_SETTLE_RD = 224 /\
  TW.A_OW_ndata + 4 - TW.OFF_OW = CHECK_STATE_SETTLE_RD /\
  CHECK_STATE_SETTLE_GOT_T = 0x5e4f64 /\ CHECK_STATE_SETTLE_OW_T = 0x5f2ce4 /\ CHECK_STATE_SETTLE_T_LEN = 192 /\
  TW.OW_t_ESZ * TW.OW_t_N = CHECK_STATE_SETTLE_T_LEN /\
  CHECK_STATE_SETTLE_S_STATE = 0x5df6b0 /\ CHECK_STATE_SETTLE_M_STATE = 0x5dedec.
Proof. repeat split; reflexivity. Qed.

Definition check_state_settle_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_state_settle_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_SETTLE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_SETTLE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    app_mem (bv_unsigned sp - CHECK_STATE_SETTLE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp CHECK_STATE_SETTLE_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_STATE_SETTLE_FRAME CELL_K 8 ->
    addressable m CHECK_STATE_SETTLE_GOT_T CHECK_STATE_SETTLE_T_LEN ->
    addressable m CHECK_STATE_SETTLE_OW_T CHECK_STATE_SETTLE_T_LEN ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STATE_SETTLE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_SETTLE) fc None m (seg_rom rsegs)).

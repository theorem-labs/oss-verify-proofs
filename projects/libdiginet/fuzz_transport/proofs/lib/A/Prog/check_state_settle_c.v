(* check_state_settle_contract: check_state_settle (fuzz/fuzz_transport.c:690-742; model lib/TModel/TCb.v
   check_state_settle_m) on fuzz_transport.asan (e89be137db17), a leaf that compares the harness globals GOT and OW
   (e2, e3, ndata, desk, foreign, n, and the first min(OW.n, 16) transitions' state / old / reason) and g_s.state with
   M.state, and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_state_settle_m Bw = Some (Bw',
   tt) (TCb.v:581-591); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp)
   outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store
   does not touch the world; both ends of the frame in application memory (app_mem), so the frame store changes no
   shadow byte; the runtime cells (asan_cells: the 8 bytes at GOT_CELL_K 0xa4090 hold CELL_K 0xac9f8 and the 8 bytes
   at CELL_K hold 0x7fff8000) outside the frame (off_stk); the two transition arrays GOT.t[0..16) and OW.t[0..16)
   (CHECK_STATE_SETTLE_GOT_T / _OW_T, 192 bytes each) addressable (their bytes are marked usable in the shadow map).
   Result: the run returns to ra with every register but t0, t1, t2, a0-a7, t3, t4, t5 unchanged (the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays
   usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the
   plain contract's post facts (lib/Prog/T/check_state_settle_c.v: B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 540 code bytes of
   this function are equal in both files): symbol check_state_settle, value 0x85b34, size 540 (135 words).
     0x85b34          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85b38          the 8-byte store of ra at sp - 8 (own frame); 0x85d18 loads it back. This is the only store.
     0x85b3c-0x85b48  a3 = 0x5e52e0 (GOT, TWorldA.v TA_GOT, payload 224 bytes), a4 = 0x5f3060 (OW, TA_OW, payload 304).
     0x85b4c-0x85b84  five pairs of 4-byte loads, GOT + k and OW + k for k = 196 (e2), 200 (e3), 220 (ndata), 208
                      (desk), 212 (foreign) (TWorld.v A_GOT_e2 ... = OFF_GOT + k, A_OW_e2 ... = OFF_OW + k); each pair
                      unequal goes to the trap path 0x85d28. No instrumented check precedes these loads.
     0x85b88-0x85b98  a0 = the 8-byte load at GOT_CELL_K 0xa4090 (= CELL_K), a1 = the 4-byte load at GOT + 0 (n),
                      a6 = the 4-byte load at OW + 0 (n), a5 = the 8-byte load at CELL_K (the shadow base 0x7fff8000).
     0x85b9c-0x85bc4  when GOT.n = OW.n: a0 = the 4-byte load at 0x5dfa30 (g_s + 112, TWorld.v A_S_state), a1 = the
                      4-byte load at 0x5df16c (M + 12, A_M_state), no instrumented check; OW.n <= 0 (signed) goes to
                      0x85d24 (a0 = a1 returns, else the trap path); else a7 = (a0 = a1). When GOT.n <> OW.n: a7 = 0
                      and OW.n <= 0 goes to the trap path.
     0x85bc8-0x85ca8  a6 = min(OW.n, 16) (unsigned), t0 = 1, t1 = 12 i; the loop for i < a6 loads the 4-byte state,
                      old and reason of GOT.t[i] at GOT + 4 + 12 i + {0, 4, 8} and of OW.t[i] at OW + 4 + 12 i +
                      {0, 4, 8} (A_GOT_t_state i = OFF_GOT + 4 + 12 i, ...), each after the instrumented check of its
                      address a: the shadow byte k at (a >> 3) + a5 (0x85bec, 0x85c08, 0x85c2c, 0x85c3c, 0x85c64,
                      0x85c78); when k <> 0 the code compares (a & 7) + 3 with k (0x85cac-0x85d04) and goes back to
                      the load when (a & 7) + 3 < k, else to the error path. a7 &= (state and old equal), t0 &=
                      (reason equal).
     0x85d10-0x85d20  a7 = 0 or t0 = 0 goes to the trap path; else ra reloaded, sp = sp + 16, return. These returns
                      (0x85d20, also reached from 0x85d24) are the only ones; on them t0, t1, t2, a0-a7, t3, t4, t5 may
                      differ from their entry values and every other register is as at entry.
     0x85d28          call of __asan_handle_no_return (0x5a4c4, DgnTransportAddr.v TS___asan_handle_no_return), then
                      0x85d2c call of abort (0x93734, TS_abort): the trap path.
   Error paths and the premise that rules each out:
     - the six calls of __asan_report_load4 (0x59608, TS___asan_report_load4) at 0x85d0c, 0x85d30, 0x85d38,
       0x85d3c, 0x85d44, 0x85d4c are reached only when a checked 4-byte load at a has its shadow byte k <> 0 and
       (a & 7) + 3 >= k. Every checked load lies in GOT.t[0..16) or OW.t[0..16) (i < 16), and a & 7 is 0 or 4
       (GOT and OW are 8-aligned and 4 + 12 i is 0 or 4 mod 8), so the 4 bytes [a, a + 4) lie in one 8-byte granule
       and the byte a + 3 has (a + 3) mod 8 = (a & 7) + 3; addressable m CHECK_STATE_SETTLE_GOT_T 192 (or _OW_T)
       gives for it k = 0 or (a & 7) + 3 < k <= 7: the check passes. asan_cells gives a5 = 0x7fff8000, so the
       loaded byte is the shadow byte addressable speaks of.
     - the trap path (0x85d28 / 0x85d2c) is reached only when one of the compares fails. By tw_at each loaded
       value is the model's (TWorldG.v tw_read_val, tw_lw): GOT_e2 Bw, OW_e2 Bw, ..., GOT_n Bw, OW_n Bw, S_state Bw,
       M_state Bw, GOT_t_state Bw i, ...; check_state_settle_m Bw = Some _ gives every compare its passing outcome
       (TCb.v:581-591, the loop state_settle_loop :569-578).
   Callee texts assumed: none (the only callees, __asan_handle_no_return, abort and __asan_report_load4, are on the
   trap and error paths).
   Form: lib/Prog/T/check_state_settle_c.v (the plain contract: world premise, model premise, B' = B and the world
   after) in the image-A leaf form of check_state_wake_c.v, with fuzz_frame's instrumented-load premises
   (diginet_frame_is_keepalive_c.v: asan_cells, app_mem of both frame ends, off_stk of the two cells, addressable of
   each checked range). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_STATE_SETTLE : Z := 0x85b34.
Definition CHECK_STATE_SETTLE_FRAME : Z := 16.
(* GOT and OW at their image-A bases; the code reads the first 224 bytes of each (n, t[16], e2, e3, desk, foreign,
   ndata: up to A_GOT_ndata + 4 = OFF_GOT + 224, A_OW_ndata + 4 = OFF_OW + 224). *)
Definition CHECK_STATE_SETTLE_GOT : Z := TA_GOT.
Definition CHECK_STATE_SETTLE_OW : Z := TA_OW.
Definition CHECK_STATE_SETTLE_RD : Z := TW.A_GOT_ndata + 4 - TW.OFF_GOT.
(* The two transition arrays (the checked loads): GOT.t[0..16) and OW.t[0..16), 12 bytes an entry. *)
Definition CHECK_STATE_SETTLE_GOT_T : Z := TA_GOT + (TW.A_GOT_t_state 0 - TW.OFF_GOT).
Definition CHECK_STATE_SETTLE_OW_T : Z := TA_OW + (TW.A_OW_t_state 0 - TW.OFF_OW).
Definition CHECK_STATE_SETTLE_T_LEN : Z := TW.GOT_t_ESZ * TW.GOT_t_N.
(* The two ints read when GOT.n = OW.n: g_s.state and M.state. *)
Definition CHECK_STATE_SETTLE_S_STATE : Z := TA_g_s + (TW.A_S_state - TW.OFF_g_s).
Definition CHECK_STATE_SETTLE_M_STATE : Z := TA_M + (TW.A_M_state - TW.OFF_M).
Lemma check_state_settle_addrs :
  CHECK_STATE_SETTLE_GOT = 0x5e52e0 /\ CHECK_STATE_SETTLE_OW = 0x5f3060 /\ CHECK_STATE_SETTLE_RD = 224 /\
  TW.A_OW_ndata + 4 - TW.OFF_OW = CHECK_STATE_SETTLE_RD /\
  CHECK_STATE_SETTLE_GOT_T = 0x5e52e4 /\ CHECK_STATE_SETTLE_OW_T = 0x5f3064 /\ CHECK_STATE_SETTLE_T_LEN = 192 /\
  TW.OW_t_ESZ * TW.OW_t_N = CHECK_STATE_SETTLE_T_LEN /\
  CHECK_STATE_SETTLE_S_STATE = 0x5dfa30 /\ CHECK_STATE_SETTLE_M_STATE = 0x5df16c.
Proof. repeat split; reflexivity. Qed.

Definition check_state_settle_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_state_settle_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_SETTLE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_SETTLE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
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
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_SETTLE) fc None m (seg_rom rsegs)).

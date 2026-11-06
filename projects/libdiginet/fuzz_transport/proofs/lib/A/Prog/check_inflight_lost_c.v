(* check_inflight_lost_contract: check_inflight_lost (fuzz/fuzz_transport.c:486-495; model lib/TModel/TCb.v
   check_inflight_lost_m) on fuzz_transport.asan (e89be137db17), a leaf that reads two fields of the struct
   diginet_notice at its argument, three ints of the harness global M and one int of the harness global g_cfg, and
   returns nothing. It stores into no harness global, so it takes the leaf form.
   Argument: a0 = p, the address of a struct diginet_notice (include/diginet/transport/diginet_session.h; counter at
   64 (4 bytes), retry at 68 (2)) holding the model's notice n (lib/TModel/TImg.v ntc).
   Premises:
   - the plain contract's struct premise ntc_at m p n sp FRAME (lib/Prog/T/TContract.v:96-111), stated over image
     A's memory for the fields the code reads: 0 < p, p mod 8 = 0, and the bytes at p + 64 and p + 68 are the
     little-endian counter and retry of n (bytes_at of TWorld.v put). The retry is a uint16_t: 0 <= n_retry n < 2^16,
     as the plain contract's u_at NB 68 2 = n_retry n gives. It is a premise here because put 2 keeps only the low
     16 bits while the model compares n_retry n with the 4-byte world value g_cfg.max_retries; the counter needs
     none, because the model equates it with the 4-byte world value M.fly.counter;
   - the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between the
     memory m, read through mrd (csw_view, check_state_wake_c.v), and the world Bw; check_inflight_lost_m Bw n =
     Some (Bw', tt), which holds exactly when M.fly.on <> 0, n_counter n = M.fly.counter,
     M.fly.retries = g_cfg.max_retries and n_retry n = g_cfg.max_retries (TCb.v:397-400);
   - the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull
     [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store does not touch
     the world; both ends of the frame in application memory (app_mem), so the frame is not shadow memory;
   - asan_cells m (lib/A/AsanCells.v: among others the 8 bytes at GOT_CELL_K 0xa4090 hold CELL_K 0xac9f8 and the 8
     bytes at CELL_K hold 0x7fff8000); GOT_CELL_K's 8 bytes, CELL_K's 8 bytes and each field the code loads lie
     outside the frame (off_stk; the plain contract's off_window), and each loaded field is marked usable
     (addressable).
   Result: the run returns to ra with every register but a0-a5 unchanged (they are not specified: the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays
   usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the
   plain contract's post facts (lib/Prog/T/check_inflight_lost_c.v: B' = B, wmem rsegs m' B, munch of the frame
   only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 168 code bytes of
   this function are equal in both files): symbol check_inflight_lost, value 0x852e4, size 168 (42 words).
     0x852e4          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x852e8          the 8-byte store of ra at sp - 8 (own frame); 0x85354 loads it back.
     0x852ec-0x852f0  a3 = 0x5df160, the base of M (payload 0x5df160, 1648 bytes, the image's own asan_globals
                      descriptor at 0xa9000).
     0x852f4          a1 = the 4-byte load at a3 + 96 = 0x5df1c0, sign-extended: M.fly.on (TWorld.v A_M_fly_on =
                      OFF_M + 96). 0x852f8: a1 = 0 goes to 0x85360.
     0x852fc-0x85304  a1 = the 8-byte load at GOT_CELL_K 0xa4090 (it holds CELL_K); a2 = the 8-byte load at CELL_K
                      0xac9f8 (it holds 0x7fff8000).
     0x85308-0x85314  the instrumented check of the 4-byte load at p + 64: a1 = p + 64; a4 = the signed shadow byte k
                      at ((p + 64) >> 3) + 0x7fff8000. 0x85318: k = 0 goes on to 0x8531c; else 0x85368-0x85370:
                      a5 = ((p + 64) & 7) + 3, and a5 < k (signed) goes back to 0x8531c; else 0x85374-0x85378:
                      a0 = p + 64 and the call of TS___asan_report_load4 (0x59608), the error path.
     0x8531c          a1 = the 4-byte load at p + 64, sign-extended: n->counter.
     0x85320          a4 = the 4-byte load at a3 + 104 = 0x5df1c8, sign-extended: M.fly.counter (A_M_fly_counter =
                      OFF_M + 104). 0x85324: a1 <> a4 goes to 0x85360.
     0x85328          a1 = the 4-byte load at a3 + 108 = 0x5df1cc, sign-extended: M.fly.retries (A_M_fly_retries =
                      OFF_M + 108).
     0x8532c-0x85330  a3 = the 4-byte load at 0x5df0a0, sign-extended: g_cfg (payload 0x5df080, 60 bytes, descriptor
                      at 0xa8ec0) + 32, the member max_retries (A_Cfg_max_retries = OFF_g_cfg + 32). 0x85334:
                      a1 <> a3 goes to 0x85360.
     0x85338-0x85344  the instrumented check of the 2-byte load at p + 68: a0 = p + 68; a3 = (p + 68) >> 3; a2 = the
                      signed shadow byte k at a3 + 0x7fff8000. 0x85348: k = 0 goes on to 0x8534c; else
                      0x8537c-0x85384: a3 = ((p + 68) & 7) + 1, and a3 < k (signed) goes back to 0x8534c; else
                      0x85388: the call of TS___asan_report_load2 (0x59568) with a0 = p + 68, the error path.
     0x8534c          a0 = the 2-byte load at p + 68, zero-extended: n->retry. 0x85350: a1 (M.fly.retries, equal to
                      g_cfg.max_retries here) <> a0 goes to 0x85360.
                      No instrumented check precedes any of the four loads of M and g_cfg.
     0x85354-0x8535c  ra reloaded, sp = sp + 16, return. This is the one return; on it a0-a5 hold values the code
                      loaded or computed (a5 only after the check at 0x85368) and every other register is as at entry.
     0x85360          call of TS___asan_handle_no_return (0x5a4c4), then 0x85364 call of TS_abort (0x93734): the
                      trap path.
   Error paths and the premise that rules each out:
     - TS___asan_report_load4 (0x85378): addressable m (p + 64) 4. Each byte x of [p + 64, p + 68) has its shadow
       byte k = 0 or x mod 8 < k <= 7. If the 4 bytes lie in one 8-byte granule, the last one gives k = 0 or
       ((p + 64) & 7) + 3 < k; if they cross a granule boundary, byte 7 of the first granule is in the range and
       gives k = 0. Either way the check passes. asan_cells gives the shadow base 0x7fff8000 the code uses.
     - TS___asan_report_load2 (0x85388): addressable m (p + 68) 2, the same argument with ((p + 68) & 7) + 1.
     - the trap path (0x85360 / 0x85364): reached only when M.fly.on = 0, or the loaded counter differs from
       M.fly.counter, or M.fly.retries differs from g_cfg.max_retries, or the loaded retry differs from
       M.fly.retries. By tw_at the world loads are M_fly_on Bw (s32_at) and M_fly_counter Bw, M_fly_retries Bw and
       Cfg_max_retries Bw (4-byte u_at) sign-extended (TWorldG.v tw_read_val, tw_lw). check_inflight_lost_m Bw n =
       Some _ gives M_fly_on Bw <> 0, n_counter n = M_fly_counter Bw (so 0 <= n_counter n < 2^32, and the put bytes
       at p + 64 load to the same sign-extended word), M_fly_retries Bw = Cfg_max_retries Bw, and
       n_retry n = Cfg_max_retries Bw = M_fly_retries Bw, which with 0 <= n_retry n < 2^16 makes the zero-extended
       2-byte load equal to the sign-extended 4-byte load of M.fly.retries.
   The shadow bytes lie in shadow memory and the frame in application memory (app_mem of both frame ends), so the ra
   store does not change them; off_stk keeps the store off the two fields and the two cells.
   Callee texts assumed: none (the only callees are the error-path entries and TS___asan_handle_no_return / TS_abort
   on the trap path).
   Caller: notice (the call at 0x835ec; notice moves its second argument n, a struct diginet_notice its caller
   built, from a1 to a0 at 0x835e8; return address 0x835f0).
   Form: lib/A/Prog/check_state_wake_c.v (image A's leaf exemplar: the world premise, the model premise, the evt rsegs
   run, the munch / wmono / stk post, Bw' = Bw and the world after) with fuzz_frame's image-A
   diginet_frame_is_keepalive_c.v for a pointer argument read under instrumented checks (the argument as a Z value
   in a0, bytes_at of each field read, asan_cells, app_mem of the frame ends, off_stk and addressable of each range
   loaded); TW, TC and TG are check_state_wake_c.v's module names, TI is TImg. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.

Definition CHECK_INFLIGHT_LOST : Z := 0x852e4.
Definition CHECK_INFLIGHT_LOST_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-A base (TWorldA.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: M.fly.on (4 bytes);
   M.fly.counter (4 bytes); M.fly.retries (4 bytes); g_cfg.max_retries (4 bytes). *)
Definition CHECK_INFLIGHT_LOST_FLY_ON : Z := TA_M + (TW.A_M_fly_on - TW.OFF_M).
Definition CHECK_INFLIGHT_LOST_FLY_COUNTER : Z := TA_M + (TW.A_M_fly_counter - TW.OFF_M).
Definition CHECK_INFLIGHT_LOST_FLY_RETRIES : Z := TA_M + (TW.A_M_fly_retries - TW.OFF_M).
Definition CHECK_INFLIGHT_LOST_MAX_RETRIES : Z := TA_g_cfg + (TW.A_Cfg_max_retries - TW.OFF_g_cfg).
Lemma check_inflight_lost_fly_on_at : CHECK_INFLIGHT_LOST_FLY_ON = 0x5df1c0.
Proof. reflexivity. Qed.
Lemma check_inflight_lost_fly_counter_at : CHECK_INFLIGHT_LOST_FLY_COUNTER = 0x5df1c8.
Proof. reflexivity. Qed.
Lemma check_inflight_lost_fly_retries_at : CHECK_INFLIGHT_LOST_FLY_RETRIES = 0x5df1cc.
Proof. reflexivity. Qed.
Lemma check_inflight_lost_max_retries_at : CHECK_INFLIGHT_LOST_MAX_RETRIES = 0x5df0a0.
Proof. reflexivity. Qed.

Definition check_inflight_lost_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (n : TI.ntc) (Bw Bw' : list byte),
    0 < p ->
    p mod 8 = 0 ->
    0 <= TI.n_retry n < 2 ^ 16 ->
    bytes_at rsegs m (p + 64) (TW.put 4 (TI.n_counter n)) ->
    bytes_at rsegs m (p + 68) (TW.put 2 (TI.n_retry n)) ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_inflight_lost_m Bw n = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_INFLIGHT_LOST_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_INFLIGHT_LOST_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_INFLIGHT_LOST_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_INFLIGHT_LOST_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_INFLIGHT_LOST_FRAME CELL_K 8 ->
    off_stk sp CHECK_INFLIGHT_LOST_FRAME (p + 64) 4 -> addressable m (p + 64) 4 ->
    off_stk sp CHECK_INFLIGHT_LOST_FRAME (p + 68) 2 -> addressable m (p + 68) 2 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_INFLIGHT_LOST_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_INFLIGHT_LOST) fc None m (seg_rom rsegs)).

(* Footprint form of check_inflight_lost_contract (check_inflight_lost_c.v; image A, entry 0x852e4): the same
   premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under
   the footprint RNG (every data access of every step lies in RNG). The code touches every range below on its one
   return path, so no rng premise has a condition; in the order the code touches them:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x852e8) and its load (0x85354);
     - [CHECK_INFLIGHT_LOST_FLY_ON, + 4) = [0x5df1c0, 0x5df1c4): the 4-byte load of M.fly.on (0x852f4);
     - GOT_CELL_K 0xa4090: one 8-byte load (0x85300); CELL_K 0xac9f8: one 8-byte load (0x85304);
     - the shadow byte of p + 64, shadow_addr (p + 64) = ((p + 64) >> 3) + 0x7fff8000 (0x85314), and [p + 64, + 4):
       the 4-byte load of n->counter (0x8531c);
     - [CHECK_INFLIGHT_LOST_FLY_COUNTER, + 4) = [0x5df1c8, 0x5df1cc): the 4-byte load of M.fly.counter (0x85320);
     - [CHECK_INFLIGHT_LOST_FLY_RETRIES, + 4) = [0x5df1cc, 0x5df1d0): the 4-byte load of M.fly.retries (0x85328);
     - [CHECK_INFLIGHT_LOST_MAX_RETRIES, + 4) = [0x5df0a0, 0x5df0a4): the 4-byte load of g_cfg.max_retries
       (0x85330);
     - the shadow byte of p + 68 (0x85344) and [p + 68, + 2): the 2-byte load of n->retry (0x8534c).
   Each check loads the one shadow byte of the first address of its access, so every shadow range is one byte. The
   error-path calls (0x85378, 0x85388) are not reached under the addressable premises, and the compares at
   0x85368-0x85370 and 0x8537c-0x85384 touch only registers, so they add no range. There is no shadow_rw premise:
   the shadow bytes the checks load are given by the addressable premises.
   Form: lib/A/Prog/check_state_wake_F_c.v with fuzz_frame's image-A diginet_frame_is_keepalive_F_c.v (one-byte
   shadow ranges, the cell ranges). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_lost_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_inflight_lost_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    ExecF.rng RNG (bv_unsigned sp - CHECK_INFLIGHT_LOST_FRAME) CHECK_INFLIGHT_LOST_FRAME ->
    ExecF.rng RNG CHECK_INFLIGHT_LOST_FLY_ON 4 ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (shadow_addr (p + 64)) 1 ->
    ExecF.rng RNG (p + 64) 4 ->
    ExecF.rng RNG CHECK_INFLIGHT_LOST_FLY_COUNTER 4 ->
    ExecF.rng RNG CHECK_INFLIGHT_LOST_FLY_RETRIES 4 ->
    ExecF.rng RNG CHECK_INFLIGHT_LOST_MAX_RETRIES 4 ->
    ExecF.rng RNG (shadow_addr (p + 68)) 1 ->
    ExecF.rng RNG (p + 68) 2 ->
    ExecF.evtF rsegs RNG
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

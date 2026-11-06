(* Footprint form of check_latest_drain_contract (check_latest_drain_c.v; image A, entry 0x85fdc): the same premises,
   then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the
   footprint RNG (every data access of every step lies in RNG). The ranges, in the code's order:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x85fe0) and its load (0x860f8);
     - [CHECK_LATEST_DRAIN_SENT, + 4) = [0x5df1a8, 0x5df1ac): M.display_sent (0x85fec);
     - [CHECK_LATEST_DRAIN_LAST, + 8) = [0x5df1a0, 0x5df1a8): M.last_display (0x85ff8), when display_sent <> 0;
     - [TA_g_now, + 8) = [0x5df100, 0x5df108): g_now (0x85ffc when display_sent <> 0, and 0x860e0);
     - [CHECK_LATEST_DRAIN_GAP, + 4) = [0x5df0b0, 0x5df0b4): g_cfg.display_gap_us (0x86004), when display_sent <> 0;
     - [TA_g_nq, + 4) = [0x5df960, 0x5df964): g_nq (0x8601c);
     - GOT_CELL_K 8 (0x86028) and CELL_K 8 (0x86034), when g_nq <> 0: the runtime cells that give 0x7fff8000;
     - the shadow bytes of g_q's payload [shadow_addr TA_g_q, + 4096 / 8) and the payload [TA_g_q, + 4096): the
       loop's checks (0x86054) and loads (0x8605c) of g_q[i];
     - the shadow bytes of g_cmd's payload [shadow_addr TA_g_cmd, + 40960 / 8) and the payload [TA_g_cmd, + 40960):
       the loop's checks (0x86074) and loads (0x8607c) of g_cmd[q].display;
     - [CHECK_LATEST_DRAIN_STATE, + 4) = [0x5df16c, 0x5df170): M.state (0x860c8);
     - [CHECK_LATEST_DRAIN_FLY, + 4) = [0x5df1c0, 0x5df1c4): M.fly.on (0x860d4), when M.state = 2;
     - [CHECK_LATEST_DRAIN_BACKOFF, + 8) = [0x5df198, 0x5df1a0): M.backoff_until (0x860e4), when also M.fly.on = 0.
   Both payloads start on an 8-byte boundary and have a length divisible by 8 (0x5f1c00, 4096; 0x5e5400, 40960), so
   their shadow bytes are exactly the given ranges, and each loaded g_q[i] (i < 1024) and g_cmd[q].display (q < 1024)
   and its one checked shadow byte lie inside them. No rng premise has a condition: every range is a part of a harness
   global's payload, its shadow bytes, or a runtime cell, which the call site's footprint RNG_W W always holds, so a
   condition (on display_sent, g_nq, M.state, M.fly.on, or the loop's index) would only add a case to the walk. The
   compares at 0x860a0-0x860a8 and 0x860b0-0x860b8 touch only registers.
   Form: check_state_wake_F_c.v (the rng premises after the contract's premises, the same post), with fuzz_frame's
   image-A diginet_frame_is_keepalive_F_c.v's rng premises for the runtime cells and the shadow bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_latest_drain_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_latest_drain_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_drain_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_DRAIN_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_LATEST_DRAIN_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_LATEST_DRAIN_FRAME CELL_K 8 ->
    addressable m TA_g_q TW.SZ_g_q ->
    addressable m TA_g_cmd TW.SZ_g_cmd ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_LATEST_DRAIN_FRAME) CHECK_LATEST_DRAIN_FRAME ->
    ExecF.rng RNG CHECK_LATEST_DRAIN_SENT 4 ->
    ExecF.rng RNG CHECK_LATEST_DRAIN_LAST 8 ->
    ExecF.rng RNG TA_g_now 8 ->
    ExecF.rng RNG CHECK_LATEST_DRAIN_GAP 4 ->
    ExecF.rng RNG TA_g_nq 4 ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (shadow_addr TA_g_q) (TW.SZ_g_q / 8) ->
    ExecF.rng RNG TA_g_q TW.SZ_g_q ->
    ExecF.rng RNG (shadow_addr TA_g_cmd) (TW.SZ_g_cmd / 8) ->
    ExecF.rng RNG TA_g_cmd TW.SZ_g_cmd ->
    ExecF.rng RNG CHECK_LATEST_DRAIN_STATE 4 ->
    ExecF.rng RNG CHECK_LATEST_DRAIN_FLY 4 ->
    ExecF.rng RNG CHECK_LATEST_DRAIN_BACKOFF 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_DRAIN_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_DRAIN) fc None m (seg_rom rsegs)).

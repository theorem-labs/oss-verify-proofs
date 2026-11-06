(* Footprint form of check_state_settle_contract (check_state_settle_c.v; image A, entry 0x85b34, frame 16 bytes):
   the same premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF
   run under the footprint RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x85b38) and its load (0x85d18);
     - GOT_CELL_K 0xa4090 and CELL_K 0xac9f8: one 8-byte load each (0x85b8c, 0x85b98);
     - [CHECK_STATE_SETTLE_GOT, + 224) = [0x5e52e0, 0x5e53c0) and [CHECK_STATE_SETTLE_OW, + 224) = [0x5f3060,
       0x5f3140): the 4-byte loads of n, e2, e3, desk, foreign, ndata (0x85b4c-0x85b84, 0x85b90, 0x85b94) and of the
       transitions' state, old and reason (0x85c0c, 0x85c18, 0x85c40, 0x85c48, 0x85c7c, 0x85c84). The range is the
       hull of these loads; the two ints it holds that the code does not read (acks at + 204, acked at + 216) add
       nothing the caller cannot give;
     - [CHECK_STATE_SETTLE_S_STATE, + 4) = [0x5dfa30, 0x5dfa34) and [CHECK_STATE_SETTLE_M_STATE, + 4) = [0x5df16c,
       0x5df170): the 4-byte loads of g_s.state and M.state (0x85ba8, 0x85bac);
     - the shadow bytes of the two transition arrays, [shadow_addr GOT_T, shadow_addr (GOT_T + 191)] and the same
       for OW_T: the 1-byte loads of the instrumented checks (0x85bec, 0x85c08, 0x85c2c, 0x85c3c, 0x85c64, 0x85c78).
   The code reads g_s.state and M.state only when GOT.n = OW.n, and the transitions only for i < min(OW.n, 16); the
   rng premises are stated with no condition, as fuzz_frame's diginet_mac_is_digidesign_F_c.v states its 3 bytes:
   every range is in a harness global's payload or its shadow, which the caller has in its footprint whatever the
   values. The error-path calls (__asan_report_load4 at 0x85d0c, 0x85d30, 0x85d38, 0x85d3c, 0x85d44, 0x85d4c) and the
   trap path (0x85d28) are not reached (check_state_settle_c.v), so no range is given for them, and the compares at
   0x85cac-0x85d04 touch only registers. There is no shadow_rw premise.
   Form: check_state_wake_F_c.v (the rng premises after the contract's premises, the same post), with fuzz_frame's
   diginet_frame_is_keepalive_F_c.v ranges of the two cells and of the shadow bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_settle_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_state_settle_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    ExecF.rng RNG (bv_unsigned sp - CHECK_STATE_SETTLE_FRAME) CHECK_STATE_SETTLE_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG CHECK_STATE_SETTLE_GOT CHECK_STATE_SETTLE_RD ->
    ExecF.rng RNG CHECK_STATE_SETTLE_OW CHECK_STATE_SETTLE_RD ->
    ExecF.rng RNG CHECK_STATE_SETTLE_S_STATE 4 ->
    ExecF.rng RNG CHECK_STATE_SETTLE_M_STATE 4 ->
    ExecF.rng RNG (shadow_addr CHECK_STATE_SETTLE_GOT_T)
      (shadow_addr (CHECK_STATE_SETTLE_GOT_T + CHECK_STATE_SETTLE_T_LEN - 1) - shadow_addr CHECK_STATE_SETTLE_GOT_T + 1) ->
    ExecF.rng RNG (shadow_addr CHECK_STATE_SETTLE_OW_T)
      (shadow_addr (CHECK_STATE_SETTLE_OW_T + CHECK_STATE_SETTLE_T_LEN - 1) - shadow_addr CHECK_STATE_SETTLE_OW_T + 1) ->
    ExecF.evtF rsegs RNG
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

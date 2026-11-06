(* Footprint form of check_state_settle_contract (check_state_settle_c.v; image B, entry 0x85dbc, frame 16 bytes):
   the same premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF
   run under the footprint RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x85dc0) and its load (0x85fa0);
     - GOT_CELL_K 0xa3cf0 and CELL_K 0xac678: one 8-byte load each (0x85e14, 0x85e20);
     - [CHECK_STATE_SETTLE_GOT, + 224) = [0x5e4f60, 0x5e5040) and [CHECK_STATE_SETTLE_OW, + 224) = [0x5f2ce0,
       0x5f2dc0): the 4-byte loads of e2, e3, ndata, desk, foreign, n (0x85dd4-0x85e08, 0x85e18, 0x85e1c) and of the
       transitions' state, old and reason (0x85e94, 0x85ea0, 0x85ec8, 0x85ed0, 0x85f04, 0x85f0c). The range is the
       hull of these loads; the two ints it holds that the code does not read (acks at + 204, acked at + 216) add
       nothing the caller cannot give;
     - [CHECK_STATE_SETTLE_S_STATE, + 4) = [0x5df6b0, 0x5df6b4) and [CHECK_STATE_SETTLE_M_STATE, + 4) = [0x5dedec,
       0x5dedf0): the 4-byte loads of g_s.state and M.state (0x85e30, 0x85e34);
     - the shadow bytes of the two transition arrays, [shadow_addr GOT_T, shadow_addr (GOT_T + 191)] and the same
       for OW_T: the 1-byte loads of the instrumented checks (0x85e74, 0x85e90, 0x85eb0, 0x85ec4, 0x85ef0, 0x85f00).
   The code reads g_s.state and M.state only when GOT.n = OW.n, and the transitions only for i < min(OW.n, 16); the
   rng premises are stated with no condition, as fuzz_frame's diginet_mac_is_digidesign_F_c.v states its 3 bytes:
   every range is in a harness global's payload or its shadow, which the caller has in its footprint whatever the
   values. The error-path calls (__asan_report_load4 at 0x85f94, 0x85fc0, 0x85fc4, 0x85fc8, 0x85fd0, 0x85fd8) and the
   trap path (0x85fb0 - 0x85fb8) are not reached (check_state_settle_c.v), so no range is given for them, and the
   compares at 0x85f34-0x85f8c touch only registers. There is no shadow_rw premise.
   Form: lib/A/Prog/check_state_settle_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_settle_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_state_settle_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_SETTLE) fc None m (seg_rom rsegs)).

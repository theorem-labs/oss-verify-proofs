(* Footprint form of diginet_session_deadline_contract (diginet_session_deadline_c.v; image A, entry 0x8a9d4, frame
   16 bytes): the same premises, then one rng premise per memory range the code reads or writes, and the run as an
   ExecF.evtF run under the footprint RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x8a9d8) and its load (0x8ac90);
     - GOT_CELL_K 0xa4090 and CELL_K 0xac9f8: one 8-byte load each (0x8a9f4, 0x8a9f8);
     - [DIGINET_SESSION_DEADLINE_S, + 18264) = [0x5df9c0, 0x5e4118), g_s's payload: the 4-, 8- and 1-byte loads of
       its fields (diginet_session_deadline_c.v lists them with their pcs). The range is the hull of these loads
       and of every queue[i].display the loop can read (i < 512), widened to the payload's end;
     - the shadow bytes of that payload, [shadow_addr S, shadow_addr (S + 18264 - 1)]: the 1-byte loads of the
       instrumented checks.
   The code reads the cells and the shadow bytes only when s <> 0, which holds (s = 0x5df9c0), and each field only on
   the branch that needs it; the rng premises are stated with no condition, as fuzz_frame's
   diginet_mac_is_digidesign_F_c.v states its 3 bytes: every range is in g_s's payload or its shadow, which the caller
   has in its footprint whatever the values. The error-path calls (__asan_report_load1/4/8) are not reached
   (diginet_session_deadline_c.v), so no range is given for them, and the compares before them touch only registers.
   There is no shadow_rw premise.
   Form: check_state_wake_F_c.v (the rng premises after the contract's premises, the same post), with fuzz_frame's
   diginet_mac_is_digidesign_F_c.v ranges of the two cells, of the bytes and of their shadow bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_deadline_c.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_deadline_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    ExecF.rng RNG (bv_unsigned sp - DIGINET_SESSION_DEADLINE_FRAME) DIGINET_SESSION_DEADLINE_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG DIGINET_SESSION_DEADLINE_S DIGINET_SESSION_DEADLINE_SN ->
    ExecF.rng RNG (shadow_addr DIGINET_SESSION_DEADLINE_S)
      (shadow_addr (DIGINET_SESSION_DEADLINE_S + DIGINET_SESSION_DEADLINE_SN - 1) -
       shadow_addr DIGINET_SESSION_DEADLINE_S + 1) ->
    ExecF.evtF rsegs RNG
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

(* Footprint form of check_keepalive_settle_contract (check_keepalive_settle_c.v; image A, entry 0x85e14): the same
   premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under
   the footprint RNG (every data access of every step lies in RNG):
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x85e18) and its load (0x85e5c);
     - [CHECK_KEEPALIVE_SETTLE_RAW, + 4) = [0x5df0e0, 0x5df0e4): the 4-byte load of g_raw (0x85e20);
     - [CHECK_KEEPALIVE_SETTLE_STATE, + 4) = [0x5df16c, 0x5df170): the 4-byte load of M.state (0x85e30);
     - [CHECK_KEEPALIVE_SETTLE_FLY_ON, + 4) = [0x5df1c0, 0x5df1c4): the 4-byte load of M.fly.on (0x85e3c);
     - [CHECK_KEEPALIVE_SETTLE_NOW, + 8) = [0x5df100, 0x5df108): the 8-byte load of g_now (0x85e48);
     - [CHECK_KEEPALIVE_SETTLE_BACKOFF, + 8) = [0x5df198, 0x5df1a0): the 8-byte load of M.backoff_until (0x85e4c);
     - [CHECK_KEEPALIVE_SETTLE_NEXT_KA, + 8) = [0x5df190, 0x5df198): the 8-byte load of M.next_ka (0x85e54).
   The frame and g_raw are touched on every path; each later range only on the paths past the test before it
   (0x85e24, 0x85e38, 0x85e40, 0x85e50 return early). The rng premises carry no condition all the same: every range
   is a constant range of a harness global's payload, which the caller's footprint always holds (image bytes, never
   hidden), and ExecF.evtF asks only that each access the run makes lies in RNG, so a premise for a range a path does
   not touch costs that path nothing.
   There is no range of runtime cells and no shadow range: the code reads neither (no instrumented check), so there
   is no asan_cells, addressable or shadow_rw premise.
   Form: lib/A/Prog/check_state_wake_F_c.v (the rng premises after the contract's premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_keepalive_settle_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_keepalive_settle_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_keepalive_settle_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_KEEPALIVE_SETTLE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_KEEPALIVE_SETTLE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_KEEPALIVE_SETTLE_FRAME) CHECK_KEEPALIVE_SETTLE_FRAME ->
    ExecF.rng RNG CHECK_KEEPALIVE_SETTLE_RAW 4 ->
    ExecF.rng RNG CHECK_KEEPALIVE_SETTLE_STATE 4 ->
    ExecF.rng RNG CHECK_KEEPALIVE_SETTLE_FLY_ON 4 ->
    ExecF.rng RNG CHECK_KEEPALIVE_SETTLE_NOW 8 ->
    ExecF.rng RNG CHECK_KEEPALIVE_SETTLE_BACKOFF 8 ->
    ExecF.rng RNG CHECK_KEEPALIVE_SETTLE_NEXT_KA 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_KEEPALIVE_SETTLE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_KEEPALIVE_SETTLE) fc None m (seg_rom rsegs)).

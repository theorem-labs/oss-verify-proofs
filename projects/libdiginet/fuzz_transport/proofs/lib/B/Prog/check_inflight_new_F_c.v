(* Footprint form of check_inflight_new_contract (check_inflight_new_c.v; image B, entry 0x84654): the same premises,
   then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the
   footprint RNG (every data access of every step lies in RNG). The code touches every range on its one return path
   (check_inflight_new_m Bw = Some _ rules out the early branches to the trap at 0x8466c and 0x84674), so no rng
   premise has a condition:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x84658) and its load (0x84688);
     - [CHECK_INFLIGHT_NEW_STATE, + 4) = [0x5dedec, 0x5dedf0): the 4-byte load of M.state (0x84664);
     - [CHECK_INFLIGHT_NEW_FLY_ON, + 4) = [0x5dee40, 0x5dee44): the 4-byte load of M.fly.on (0x84670);
     - [CHECK_INFLIGHT_NEW_NOW, + 8) = [0x5ded80, 0x5ded88): the 8-byte load of g_now (0x8467c);
     - [CHECK_INFLIGHT_NEW_BACKOFF, + 8) = [0x5dee18, 0x5dee20): the 8-byte load of M.backoff_until (0x84680).
   There is no range of runtime cells and no shadow range: the code reads neither (no instrumented check), so there
   is no asan_cells, addressable or shadow_rw premise. The trap path (0x84694 - 0x8469c) makes no data access of
   this function's own.
   Form: lib/A/Prog/check_inflight_new_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_inflight_new_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_inflight_new_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_inflight_new_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_INFLIGHT_NEW_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_INFLIGHT_NEW_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_INFLIGHT_NEW_FRAME) CHECK_INFLIGHT_NEW_FRAME ->
    ExecF.rng RNG CHECK_INFLIGHT_NEW_STATE 4 ->
    ExecF.rng RNG CHECK_INFLIGHT_NEW_FLY_ON 4 ->
    ExecF.rng RNG CHECK_INFLIGHT_NEW_NOW 8 ->
    ExecF.rng RNG CHECK_INFLIGHT_NEW_BACKOFF 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_INFLIGHT_NEW_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_INFLIGHT_NEW) fc None m (seg_rom rsegs)).

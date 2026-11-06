(* Footprint form of check_state_online_contract (check_state_online_c.v; image B, entry 0x85320): the same premises,
   then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the
   footprint RNG (every data access of every step lies in RNG). The code touches all three ranges on its one return
   path (check_state_online_m Bw = Some _ rules out the early branch to the trap at 0x85334), so no rng premise has a
   condition:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x85324) and its load (0x85340);
     - [CHECK_STATE_ONLINE_E2, + 4) = [0x5dedf0, 0x5dedf4): the 4-byte load of M.e2_acked (0x85330);
     - [CHECK_STATE_ONLINE_E1, + 4) = [0x5dedf4, 0x5dedf8): the 4-byte load of M.e1_us (0x85338).
   There is no range of runtime cells and no shadow range: the code reads neither (no instrumented check), so there
   is no asan_cells, addressable or shadow_rw premise. The trap path (0x8534c - 0x85354) makes no data access of
   this function's own.
   Form: lib/A/Prog/check_state_online_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_online_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_state_online_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_state_online_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_ONLINE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_ONLINE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_STATE_ONLINE_FRAME) CHECK_STATE_ONLINE_FRAME ->
    ExecF.rng RNG CHECK_STATE_ONLINE_E2 4 ->
    ExecF.rng RNG CHECK_STATE_ONLINE_E1 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STATE_ONLINE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_ONLINE) fc None m (seg_rom rsegs)).

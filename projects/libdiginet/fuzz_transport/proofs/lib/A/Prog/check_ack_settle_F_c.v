(* Footprint form of check_ack_settle_contract (check_ack_settle_c.v; image A, entry 0x85b04): the same premises,
   then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the
   footprint RNG (every data access of every step lies in RNG). The code touches every range on its one return path,
   so no rng premise has a condition:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x85b08) and its load (0x85b20);
     - [CHECK_ACK_SETTLE_GOT_ACKS, + 4) = [0x5e53ac, 0x5e53b0): the 4-byte load of GOT.acks (0x85b14);
     - [CHECK_ACK_SETTLE_OW_ACKS, + 4) = [0x5f312c, 0x5f3130): the 4-byte load of OW.acks (0x85b18).
   There is no range of runtime cells and no shadow range: the code reads neither (no instrumented check), so there
   is no asan_cells, addressable or shadow_rw premise.
   Form: lib/A/Prog/check_state_wake_F_c.v (the rng premises after the contract's premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_ack_settle_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_ack_settle_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_ack_settle_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_ACK_SETTLE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_ACK_SETTLE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_ACK_SETTLE_FRAME) CHECK_ACK_SETTLE_FRAME ->
    ExecF.rng RNG CHECK_ACK_SETTLE_GOT_ACKS 4 ->
    ExecF.rng RNG CHECK_ACK_SETTLE_OW_ACKS 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_ACK_SETTLE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ACK_SETTLE) fc None m (seg_rom rsegs)).

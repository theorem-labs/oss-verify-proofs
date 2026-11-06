(* Footprint form of io_now_contract (io_now_c.v; image A, entry 0x8356c): the same premises, then one rng premise
   per memory range the code reads or writes, and the run as an ExecF.evtF run under the footprint RNG (every data
   access of every step lies in RNG). The code touches one range, on its one path, so the rng premise has no
   condition:
     - [IO_NOW_G_NOW, + 8) = [0x5df100, 0x5df108): the 8-byte load of g_now (0x83570).
   The frame is 0 bytes (no stack access), so there is no frame range. There is no range of runtime cells and no
   shadow range: the code reads neither (no instrumented check), so there is no asan_cells, addressable or shadow_rw
   premise.
   Form: check_state_wake_F_c.v (the rng premises after the contract's premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_now_c.
Import ListNotations.
Open Scope Z_scope.

Definition io_now_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + IO_NOW_FRAME <= bv_unsigned sp ->
    ExecF.rng RNG IO_NOW_G_NOW 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (TC.io_now_m Bw)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - IO_NOW_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IO_NOW) fc None m (seg_rom rsegs)).

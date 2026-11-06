(* Footprint form of check_latest_submit_contract (check_latest_submit_c.v; image B, entry 0x86568): the same
   premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under
   the footprint RNG (every data access of every step lies in RNG). The code touches one range, on its one return
   path, so the rng premise has no condition:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x8656c) and its load (0x86574).
   It reads no world byte, no runtime cell and no shadow byte (no instrumented check), so there is no other rng
   premise and no asan_cells, addressable or shadow_rw premise. The trap path (0x86580 - 0x86588) makes no data access
   of this function's own.
   Form: lib/A/Prog/check_latest_submit_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_submit_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_latest_submit_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte) (rc want : Z),
    a0 = Z_to_bv 64 rc ->
    a1 = Z_to_bv 64 want ->
    -2 ^ 31 <= rc < 2 ^ 31 ->
    -2 ^ 31 <= want < 2 ^ 31 ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_latest_submit_m Bw rc want = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_SUBMIT_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_SUBMIT_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_LATEST_SUBMIT_FRAME) CHECK_LATEST_SUBMIT_FRAME ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_SUBMIT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_SUBMIT) fc None m (seg_rom rsegs)).

(* Relocated from libreac/fuzz_decode lib/B/Prog/reac_frame_clean_len_F_c.v (origin/ossv/recipes 98c99a85e4) to reac-repacer/fuzz_wire
   image B: entry 0x8158c -> 0x818e8, constants 0x10310 -> 0x10300 and 0x103c8 -> 0x103b0, module paths changed. A byte compare
   gives the two functions equal modulo pc-relative offsets and both 8-byte constants byte-equal. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import reac_frame_clean_len_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
Open Scope Z_scope.

(* Footprint twin of reac_frame_clean_len_contract (reac_frame_clean_len_c.v): the same premises and postcondition,
   with the run an ExecF.evtF run whose data accesses lie in RNG. RNG holds the ranges the run reads or writes:
     - A_M 8: the 8-byte load of KM (when a0 >= 54);
     - A_T 8: the 8-byte load of KT (when a0 >= 54).
   The run uses no stack frame, stores nothing, and does no instrumented check. *)
Definition reac_frame_clean_len_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    ExecF.rng RNG A_M 8 ->
    ExecF.rng RNG A_T 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (reac_frame_clean_len_model (bv_unsigned a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_CLEAN_LEN) fc None m (seg_rom rsegs)).

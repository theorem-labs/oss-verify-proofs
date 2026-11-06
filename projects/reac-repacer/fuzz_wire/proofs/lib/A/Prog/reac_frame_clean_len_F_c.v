(* Relocated from libreac/fuzz_decode lib/A/Prog/reac_frame_clean_len_F_c.v (origin/ossv/recipes 98c99a85e4) to reac-repacer/fuzz_wire
   image A: entry 0x8126c -> 0x81854, constants 0x10310 -> 0x10300 and 0x103c0 -> 0x103b0, module paths changed. A byte compare
   gives the two functions equal modulo pc-relative offsets and both 8-byte constants byte-equal. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import reac_frame_clean_len_c.
Open Scope Z_scope.

(* Footprint form of reac_frame_clean_len_contract: the same premises, then one rng premise per memory range the
   code reads or writes, and the run as an ExecF.evtF run under RNG. The code reads memory only with two 8-byte
   loads, at A_M and at A_T, and writes no memory. *)
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

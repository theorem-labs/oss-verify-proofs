From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_upstream_channels_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
Open Scope Z_scope.

(* Footprint form of reac_upstream_channels_contract (A image, entry 0x81ad0). The run is an ExecF.evtF run under
   a footprint RNG: every data access of every step lies in RNG. The code has no stack frame and writes no memory;
   its only data access is one 8-byte load at UPSTREAM_DIV36_AT (an image constant; the load has no shadow check).
   So RNG holds [UPSTREAM_DIV36_AT, UPSTREAM_DIV36_AT + 8). *)

Definition reac_upstream_channels_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m UPSTREAM_DIV36_AT (le8 (Z_to_bv 64 UPSTREAM_DIV36)) ->
    ExecF.rng RNG UPSTREAM_DIV36_AT 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (upstream_result (bv_unsigned a0))) a1' a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_UPSTREAM_CHANNELS) fc None m (seg_rom rsegs)).

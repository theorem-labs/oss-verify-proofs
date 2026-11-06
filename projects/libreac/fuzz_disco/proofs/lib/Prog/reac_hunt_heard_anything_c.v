From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HUNT_HEARD_ANYTHING : Z := 0x1624c.

Definition reac_hunt_heard_anything_model (n : Z) : Z := if 0 <? n then 1 else 0.

Definition reac_hunt_heard_anything_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (h n : Z),
    a0 = Z_to_bv 64 h -> 0 < h < 2^64 -> h mod 8 = 0 ->
    -2^31 <= n < 2^31 -> bytes_at rsegs m (h + 384) (le4 (Z_to_bv 64 n)) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (reac_hunt_heard_anything_model n)) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HUNT_HEARD_ANYTHING) fc None m (seg_rom rsegs)).

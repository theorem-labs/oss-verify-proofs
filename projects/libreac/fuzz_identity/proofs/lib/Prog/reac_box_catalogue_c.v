From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_CATALOGUE : Z := 0x145d0.
Definition BOX_CATALOGUE : Z := 0x1dec0.

Definition reac_box_catalogue_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z),
    a0 = Z_to_bv 64 c ->
    c = 0 \/ (c mod 8 = 0 /\ wr_at rsegs m c 8) ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BOX_CATALOGUE) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         if c =? 0 then m' = m
         else bytes_at rsegs m' c (le8 (Z_to_bv 64 11)) /\ munch [(c, c + 8)] m m' /\ wmono rsegs m m' /\
              (mem_inv rsegs m -> mem_inv rsegs m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE) fc None m (seg_rom rsegs)).

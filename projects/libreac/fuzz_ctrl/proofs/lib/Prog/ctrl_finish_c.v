From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcFin.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_FINISH : Z := 0x14dc4.

Definition ctrl_finish_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f c o n : Z) (row B : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    ubat row 20 = c -> ubat row 18 = o -> ubat row 19 = n ->
    c <= 2 -> (c = 2 -> 2 <= n /\ o + n <= 31) ->
    0 < p -> p + 50 <= 2^64 ->
    (c = 1 \/ c = 2 -> rw_cells rsegs m (p + 18) [CB 32 B]) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (fin_w c o n p) m m' /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ (c = 1 \/ c = 2 ->
               rw_cells rsegs m' (p + 18) [CB 32 (fin c o n B)]
               /\ closes c o n (fin c o n B) /\ (closes c o n B -> fin c o n B = B)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_FINISH) fc None m (seg_rom rsegs)).
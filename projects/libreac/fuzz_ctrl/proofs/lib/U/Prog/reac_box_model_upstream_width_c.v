From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_MODEL_UPSTREAM_WIDTH : Z := 0x15ea8.

Definition reac_box_model_upstream_width_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    (mp <> 0 -> mp mod 8 = 0) ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' a4' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bm_uw mp bs))
                       a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_UPSTREAM_WIDTH) fc None m (seg_rom rsegs)).

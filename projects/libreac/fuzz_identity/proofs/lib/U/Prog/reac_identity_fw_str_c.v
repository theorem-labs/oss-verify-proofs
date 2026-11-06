From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_fw_str_c(FW, L).
Import ListNotations.
Open Scope Z_scope.

Definition REAC_IDENTITY_FW_STR : Z := 0x14bb4.

Definition reac_identity_fw_str_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v o c : Z),
    a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 o -> a2 = Z_to_bv 64 c ->
    0 <= v < 65536 -> 0 <= o < 2^64 -> 0 <= c < 2^64 ->
    (o <> 0 -> 8 <= c -> wr_at rsegs m o 8) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\
         (o = 0 \/ c < 8 -> r = Z_to_bv 64 (-1) /\ m' = m) /\
         (o <> 0 -> 8 <= c ->
            r = Z_to_bv 64 (L v) /\ bytes_at rsegs m' o (FW v ++ [Z_to_bv 8 0]) /\
            munch [(o, o + L v + 1)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_FW_STR) fc None m (seg_rom rsegs)).

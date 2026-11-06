From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_reac_ver_str_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_reac_ver_str_c(
  reac_ver_str_VER, reac_ver_str_LV).
Import ListNotations.
Open Scope Z_scope.

Definition REAC_IDENTITY_REAC_VER_STR : Z := 0x14d0c.

Definition reac_identity_reac_ver_str_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ma mi pa o c lo : Z),
    a0 = Z_to_bv 64 ma -> a1 = Z_to_bv 64 mi -> a2 = Z_to_bv 64 pa -> a3 = Z_to_bv 64 o -> a4 = Z_to_bv 64 c ->
    0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
    (o <> 0 -> 20 <= c -> wr_at rsegs m o 20 /\ (o + 20 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= o)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if (o =? 0) || (c <? 20)
          then r = Z_to_bv 64 (-1) /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m'
          else r = Z_to_bv 64 (reac_ver_str_LV ma mi pa) /\
               munch [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + reac_ver_str_LV ma mi pa + 1)] m m' /\
               bytes_at rsegs m' o (reac_ver_str_VER ma mi pa ++ [Z_to_bv 8 0])))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_REAC_VER_STR) fc None m (seg_rom rsegs)).

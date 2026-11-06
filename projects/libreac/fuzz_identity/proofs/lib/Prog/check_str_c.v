From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_STR : Z := 0x13dc0.
Definition CHECK_STR_FRAME : Z := 16.

Definition check_str_ok (m : word -> option byte) (sp : word) (r o c : Z) (str slack : list byte) : Prop :=
  r < c /\ Z.of_nat (length str) = r /\
  bytes_at rsegs m o (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str /\
  (- (o + r + 1)) mod 8 <= Z.of_nat (length slack) /\
  (o + r + 1 + Z.of_nat (length slack) <= bv_unsigned sp - CHECK_STR_FRAME \/ bv_unsigned sp <= o).

Definition check_str_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r o c lo : Z) (str slack : list byte),
    -2^31 <= r < 2^31 -> a0 = Z_to_bv 64 r ->
    0 <= o < 2^64 -> a1 = Z_to_bv 64 o ->
    0 <= c < 2^64 -> a2 = Z_to_bv 64 c ->
    (0 <= r -> check_str_ok m sp r o c str slack) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_STR_FRAME <= bv_unsigned sp ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STR_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STR) fc None m (seg_rom rsegs)).

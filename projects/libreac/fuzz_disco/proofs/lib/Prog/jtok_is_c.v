From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition JTOK_IS : Z := 0x14740.
Definition JTOK_IS_K : Z := 32.

Definition jtok_match (vk kind : Z) (vn : word) (P T : list byte) : Prop :=
  vk = kind /\ bv_unsigned vn = Z.of_nat (length T) /\ P = T.

Definition jtok_is_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo kind vk : Z) (vp vn : word)
         (T slack P : list byte),
    -2^31 <= kind < 2^31 -> a1 = Z_to_bv 64 kind ->
    -2^31 <= vk < 2^31 ->
    bytes_at rsegs m (bv_unsigned a0) (le8 vp ++ le8 vn ++ le4 (Z_to_bv 64 vk)) ->
    bytes_at rsegs m (bv_unsigned a2) (T ++ Z_to_bv 8 0 :: slack) ->
    ~ In (Z_to_bv 8 0) T ->
    (- (bv_unsigned a2 + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) ->
    (vk = kind -> bv_unsigned vn = Z.of_nat (length T) ->
       bytes_at rsegs m (bv_unsigned vp) P /\ length P = length T /\
       (bv_unsigned vp + Z.of_nat (length T) <= bv_unsigned sp - JTOK_IS_K \/ bv_unsigned sp <= bv_unsigned vp)) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + JTOK_IS_K <= bv_unsigned sp ->
    (bv_unsigned a0 + 20 <= bv_unsigned sp - JTOK_IS_K \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a2 + Z.of_nat (length T + 1 + length slack) <= bv_unsigned sp - JTOK_IS_K \/
     bv_unsigned sp <= bv_unsigned a2) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - JTOK_IS_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         ((jtok_match vk kind vn P T /\ a0' = Z_to_bv 64 1) \/
          (~ jtok_match vk kind vn P T /\ a0' = Z_to_bv 64 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 JTOK_IS) fc None m (seg_rom rsegs)).

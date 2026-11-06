From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition HAS_PREFIX : Z := 0x15428.
Definition HAS_PREFIX_K : Z := 32.

Definition prefix_of (P S : list byte) : Prop := (length P <= length S)%nat /\ firstn (length P) S = P.

Definition has_prefix_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (S P slack : list byte),
    bytes_at rsegs m (bv_unsigned a0) S ->
    bv_unsigned a1 = Z.of_nat (length S) ->
    bytes_at rsegs m (bv_unsigned a2) (P ++ Z_to_bv 8 0 :: slack) ->
    ~ In (Z_to_bv 8 0) P ->
    (- (bv_unsigned a2 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + HAS_PREFIX_K <= bv_unsigned sp ->
    (bv_unsigned a0 + Z.of_nat (length S) <= bv_unsigned sp - HAS_PREFIX_K \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a2 + Z.of_nat (length P + 1 + length slack) <= bv_unsigned sp - HAS_PREFIX_K \/
     bv_unsigned sp <= bv_unsigned a2) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - HAS_PREFIX_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         ((prefix_of P S /\ a0' = Z_to_bv 64 1) \/ (~ prefix_of P S /\ a0' = Z_to_bv 64 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HAS_PREFIX) fc None m (seg_rom rsegs)).

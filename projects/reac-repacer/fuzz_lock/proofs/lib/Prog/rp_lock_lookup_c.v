(* Contract of reac-repacer's rp_lock_lookup (src/repace_conf.c:114-145 at 3ac1cf10) in fuzz_lock.plain.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import LockSpec.
Import ListNotations.
Open Scope Z_scope.

Definition RP_LOCK_LOOKUP : Z := 0x13118.
Definition RP_FRAME : Z := 176.

(* rp_lock_lookup(text, n, port, rate): text holds the n bytes T, port the string P (no NUL; strlen reads up to
   the next 8-byte boundary after its NUL, so SL covers that many bytes). The callees use no stack. *)
Definition rp_lock_lookup_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tx pa rate lo : Z) (T P SL : list byte),
    0 < tx -> tx + Z.of_nat (length T) < 2^64 -> bytes_at rsegs m tx T ->
    0 < pa -> bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) -> ~ In (Z_to_bv 8 0) P ->
    (- (pa + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length SL) ->
    0 <= rate < 2^64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + RP_FRAME <= bv_unsigned sp ->
    tx + Z.of_nat (length T) <= bv_unsigned sp - RP_FRAME \/ bv_unsigned sp <= tx ->
    pa + Z.of_nat (length P + 1 + length SL) <= bv_unsigned sp - RP_FRAME \/ bv_unsigned sp <= pa ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lock_lookup T P rate)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 tx) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 pa)
               (Z_to_bv 64 rate) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_LOCK_LOOKUP) fc None m (seg_rom rsegs)).

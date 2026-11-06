From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition LIST_FIND : Z := 0x1525c.
Definition LIST_FIND_FRAME : Z := 80.

Definition list_rec (m : word -> option byte) (V : Z) (j : nat) (r : word * list byte) : Prop :=
  bytes_at rsegs m (V + 16 * Z.of_nat j) (le8 (fst r) ++ le8 (Z_to_bv 64 (Z.of_nat (length (snd r))))) /\
  bytes_at rsegs m (bv_unsigned (fst r)) (snd r ++ [Z_to_bv 8 0]).

Definition list_find_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo N : Z)
         (v : word) (recs : list (word * list byte)) (src : list byte),
    let L := bv_unsigned a0 in
    let V := bv_unsigned v in
    let SP := bv_unsigned sp in
    stk rsegs m lo SP -> lo + LIST_FIND_FRAME <= SP ->
    mem_inv rsegs m ->
    bytes_at rsegs m L (le8 v) -> bytes_at rsegs m (L + 8) (le4 (Z_to_bv 64 N)) -> L mod 8 = 0 ->
    0 <= N < 2^31 -> Z.of_nat (length recs) = N ->
    (0 < N -> 0 < V /\ V mod 8 = 0) ->
    (forall j r, nth_error recs j = Some r -> list_rec m V j r) ->
    bytes_at rsegs m (bv_unsigned a1) src -> bv_unsigned a2 = Z.of_nat (length src) ->
    (L + 12 <= SP - LIST_FIND_FRAME \/ SP <= L) ->
    (0 < N -> V + 16 * N <= SP - LIST_FIND_FRAME \/ SP <= V) ->
    (forall j r, nth_error recs j = Some r ->
       bv_unsigned (fst r) + Z.of_nat (length (snd r)) + 1 <= SP - LIST_FIND_FRAME \/ SP <= bv_unsigned (fst r)) ->
    (bv_unsigned a1 + Z.of_nat (length src) <= SP - LIST_FIND_FRAME \/ SP <= bv_unsigned a1) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(SP - LIST_FIND_FRAME, SP)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SP /\
         ((exists j r, nth_error recs j = Some r /\ snd r = src /\
             (forall k r', (k < j)%nat -> nth_error recs k = Some r' -> snd r' <> src) /\
             a0' = Z_to_bv 64 (Z.of_nat j)) \/
          ((forall k r', nth_error recs k = Some r' -> snd r' <> src) /\ a0' = Z_to_bv 64 (-1))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LIST_FIND) fc None m (seg_rom rsegs)).

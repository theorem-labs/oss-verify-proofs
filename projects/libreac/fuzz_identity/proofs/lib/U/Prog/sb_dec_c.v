From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import sb_ch_c.
Import ListNotations.
Open Scope Z_scope.

Definition SB_DEC : Z := 0x14778.
Definition SB_DEC_K : Z := 64.

Fixpoint sb_dec_lsd (v : Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => (48 + v mod 10) :: (if v <? 10 then [] else sb_dec_lsd (v / 10) k')
  end.

Definition sb_dec_D (v md : Z) : list Z :=
  let ds := sb_dec_lsd v 3 in rev (if Z.of_nat (length ds) <? md then ds ++ [48] else ds).

Definition sb_dec_room (cap n : Z) : Z := if n + 1 <=? cap then cap - 1 - n else 0.

Definition sb_dec_acc (v md cap n : Z) : Z := Z.min (Z.of_nat (length (sb_dec_D v md))) (sb_dec_room cap n).

Definition sb_dec_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo v md : Z) (p cap n over : word),
    0 <= v < 2^31 -> a1 = Z_to_bv 64 v ->
    (md = 1 \/ md = 2) -> a2 = Z_to_bv 64 md ->
    bytes_at rsegs m (bv_unsigned a0) (sb_rec p cap n over) ->
    wr_at rsegs m (bv_unsigned a0) 28 ->
    bv_unsigned a0 mod 8 = 0 ->
    bv_unsigned n + 1 < 2^64 - 3 ->
    (0 < sb_dec_room (bv_unsigned cap) (bv_unsigned n) ->
       bv_unsigned p <> 0 /\
       bv_unsigned p + bv_unsigned cap <= 2^64 /\
       wr_at rsegs m (bv_unsigned p + bv_unsigned n) (sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n)) /\
       (bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n) <= bv_unsigned a0 \/
        bv_unsigned a0 + 28 <= bv_unsigned p + bv_unsigned n) /\
       (bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n) <= bv_unsigned sp - SB_DEC_K \/
        bv_unsigned sp <= bv_unsigned p + bv_unsigned n)) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + SB_DEC_K <= bv_unsigned sp ->
    (bv_unsigned a0 + 28 <= bv_unsigned sp - SB_DEC_K \/ bv_unsigned sp <= bv_unsigned a0) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - SB_DEC_K, bv_unsigned sp); (bv_unsigned a0 + 16, bv_unsigned a0 + 28);
                (bv_unsigned p + bv_unsigned n,
                 bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n))] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned a0)
           (sb_rec p cap (Z_to_bv 64 (bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n)))
              (if sb_dec_room (bv_unsigned cap) (bv_unsigned n) <? Z.of_nat (length (sb_dec_D v md))
               then Z_to_bv 64 1 else over)) /\
         (0 < sb_dec_room (bv_unsigned cap) (bv_unsigned n) ->
          bytes_at rsegs m' (bv_unsigned p + bv_unsigned n)
            (map (Z_to_bv 8) (firstn (Z.to_nat (sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n))) (sb_dec_D v md)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SB_DEC) fc None m (seg_rom rsegs)).

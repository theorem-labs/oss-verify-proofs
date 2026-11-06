From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition EX_WORD : Z := 0x15158.
Definition EX_WORD_K : Z := 64.
Definition LIT_TRUE : Z := 0x10349.
Definition LIT_FALSE : Z := 0x10298.
Definition LIT_NULL : Z := 0x102ed.

Definition ex_word_lit (w : Z) (W : list byte) : Prop :=
  (w = LIT_TRUE /\ W = map (Z_to_bv 8) [116; 114; 117; 101]) \/
  (w = LIT_FALSE /\ W = map (Z_to_bv 8) [102; 97; 108; 115; 101]) \/
  (w = LIT_NULL /\ W = map (Z_to_bv 8) [110; 117; 108; 108]).

Definition ex_word_match (x : list byte) (i0 : Z) (W : list byte) : Prop :=
  Z.of_nat (length W) <= Z.of_nat (length x) - i0 /\ firstn (length W) (skipn (Z.to_nat i0) x) = W.

Definition ex_word_off (sp : word) (a n : Z) : Prop :=
  a + n <= bv_unsigned sp - EX_WORD_K \/ bv_unsigned sp <= a.

Definition ex_word_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo q x0 i0 w ty v t : Z) (x W : list byte),
    a0 = Z_to_bv 64 q -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 ty -> a3 = Z_to_bv 64 v ->
    ex_word_lit w W -> 0 <= ty <= 2 ->
    q mod 8 = 0 ->
    bytes_at rsegs m q (le8 (Z_to_bv 64 (x0 + i0)) ++ le8 (Z_to_bv 64 (x0 + Z.of_nat (length x)))) ->
    wr_at rsegs m q 8 -> wr_at rsegs m (q + 32) 4 ->
    bytes_at rsegs m x0 x -> 0 < x0 -> x0 + Z.of_nat (length x) < 2^64 -> 0 <= i0 <= Z.of_nat (length x) ->
    (v <> 0 -> v mod 8 = 0 /\ bytes_at rsegs m v (le4 (Z_to_bv 64 t)) /\ 0 <= t < 2^32 /\ ex_word_off sp v 4) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + EX_WORD_K <= bv_unsigned sp ->
    ex_word_off sp q 36 -> ex_word_off sp x0 (Z.of_nat (length x)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         ((ex_word_match x i0 W /\ r = Z_to_bv 64 0 /\
           bytes_at rsegs m' q (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat (length W)))) /\
           ((v <> 0 /\ t <> ty /\ bytes_at rsegs m' (q + 32) (le4 (Z_to_bv 64 1)) /\
             munch [(bv_unsigned sp - EX_WORD_K, bv_unsigned sp); (q, q + 8); (q + 32, q + 36)] m m') \/
            ((v = 0 \/ t = ty) /\
             munch [(bv_unsigned sp - EX_WORD_K, bv_unsigned sp); (q, q + 8)] m m'))) \/
          (~ ex_word_match x i0 W /\ r = Z_to_bv 64 (-1) /\
           munch [(bv_unsigned sp - EX_WORD_K, bv_unsigned sp)] m m')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EX_WORD) fc None m (seg_rom rsegs)).

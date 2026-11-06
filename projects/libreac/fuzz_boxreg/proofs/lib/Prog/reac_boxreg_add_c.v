From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg lowest_free_base_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOXREG_ADD : Z := 0x13a1c.
Definition ADD_K : Z := 112.

Definition add_width_ok (k fabric : Z) : Prop :=
  Z.even k = true /\ 2 <= k <= 40 /\ k <= fabric.

Definition add_held (bs M : list byte) (i : Z) : Prop :=
  0 <= i < bx_n bs /\ bx_mac bs i = M /\ forall j, 0 <= j < i -> bx_mac bs j <> M.

Definition add_unbound (bs : list byte) (k i : Z) : Prop :=
  0 <= i < bx_n bs /\ bx_mac bs i = zero6 /\ bx_nch bs i = k /\
  forall j, 0 <= j < i -> ~ (bx_mac bs j = zero6 /\ bx_nch bs j = k).

Definition add_none_held (bs M : list byte) : Prop :=
  forall i, 0 <= i < bx_n bs -> bx_mac bs i <> M.

Definition add_none_unbound (bs : list byte) (k : Z) : Prop :=
  forall i, 0 <= i < bx_n bs -> ~ (bx_mac bs i = zero6 /\ bx_nch bs i = k).

Definition add_row (M : list byte) (b k : Z) : list byte :=
  M ++ repeat (Z_to_bv 8 0) 2 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
    ++ le4 (Z_to_bv 64 0) ++ repeat (Z_to_bv 8 0) 32.

Definition add_bytes (bs M : list byte) (b k : Z) : list byte :=
  upd_bytes (upd_bytes bs (Z.to_nat (56 * bx_n bs)) (add_row M b k)) 280
    (le4 (Z_to_bv 64 (bx_n bs + 1))).

Definition add_out (bs M : list byte) (k z : Z) (bs' : list byte) : Prop :=
  ((~ add_width_ok k (bx_fabric bs) \/ M = zero6) /\ z = -1 /\ bs' = bs) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_held bs M z /\ bs' = bs) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_unbound bs k z /\
   bs' = upd_bytes bs (Z.to_nat (56 * z)) M) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_none_unbound bs k /\
   (5 <= bx_n bs \/ lowest_free bs k (-1)) /\ z = -1 /\ bs' = bs) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_none_unbound bs k /\
   bx_n bs < 5 /\ z = bx_n bs /\ exists b, 0 <= b /\ lowest_free bs k b /\ bs' = add_bytes bs M b k).

Definition reac_boxreg_add_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (r p k lo : Z) (bs M : list byte),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 k ->
    -2^31 <= k < 2^31 ->
    r mod 8 = 0 ->
    bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> boxreg_inv bs ->
    bytes_at rsegs m p M -> length M = 6%nat -> (p + 6 <= r \/ r + 288 <= p) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ADD_K <= bv_unsigned sp ->
    (bv_unsigned sp <= r \/ r + 288 <= lo) -> (bv_unsigned sp <= p \/ p + 6 <= lo) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (z : Z) (bs' : list byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         a0' = Z_to_bv 64 z /\ add_out bs M k z bs' /\ bytes_at rsegs m' r bs' /\
         munch [(lo, bv_unsigned sp); (r, r + 288)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOXREG_ADD) fc None m (seg_rom rsegs)).

Definition reac_boxreg_add_keeps_inv : Prop :=
  forall (bs M bs' : list byte) (k z : Z),
    boxreg_inv bs -> length M = 6%nat -> add_out bs M k z bs' -> boxreg_inv bs'.

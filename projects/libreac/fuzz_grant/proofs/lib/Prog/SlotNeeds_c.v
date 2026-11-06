From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_GRANT_BUILD_SWEEP : Z := 0x149b8.
Definition BUILD_SWEEP_STACK : Z := 2096.
Definition CHECK_GROUPA : Z := 0x13a74.
Definition CHECK_GROUPA_STACK : Z := 224.

Definition u32at (T : list byte) (k : Z) : Z :=
  tb T k + 256 * tb T (k + 1) + 65536 * tb T (k + 2) + 16777216 * tb T (k + 3).
Definition s32at (T : list byte) (k : Z) : Z :=
  let u := u32at T k in if u <? 2147483648 then u else u - 4294967296.
Definition put1 (T : list byte) (k v : Z) : list byte := upd_bytes T (Z.to_nat k) (le1 (Z_to_bv 64 v)).
Definition put4 (T : list byte) (k v : Z) : list byte := upd_bytes T (Z.to_nat k) (le4 (Z_to_bv 64 v)).

Definition I1 (T : list byte) : Prop :=
  (forall i, 0 <= i < 144 -> tb T (144 + i) <= 1 /\ tb T (288 + i) <= 1) /\
  (forall c q, 0 <= c < 48 -> 0 <= q < 3 -> tb T (144 + 3 * c + q) = 1 -> legal q (tb T (3 * c + q))) /\
  (forall i, 0 <= i < 144 -> tb T (288 + i) = 1 -> tb T (144 + i) = 1) /\
  (u32at T 432 <= 1 /\ ((exists i, 0 <= i < 144 /\ tb T (288 + i) = 1) -> u32at T 432 = 1)) /\
  (tb T 437 = 0 \/ (tb T 436 < 48 /\ tb T 436 + tb T 437 <= 48)) /\
  (tb T 450 = 0 \/ (tb T 449 < 48 /\ tb T 449 + tb T 450 <= 48)) /\
  (0 <= s32at T 440 /\ (tb T 437 <> 0 -> s32at T 440 <= 3 * tb T 437) /\ 0 <= s32at T 444 <= 11 /\ tb T 448 <= 1) /\
  (u32at T 452 <> 0 -> u32at T 456 <= u32at T 452).

Definition sweep_vals (T : list byte) (t base : Z) (w : nat) : list byte :=
  map (fun j => Z_to_bv 8 (eff T t (base + Z.of_nat (j / 3)) (Z.of_nat (j mod 3)))) (seq 0 (3 * w)).

Definition bs_res (s al mx base w : Z) : Z :=
  if (s =? 0) || (al =? 0) || negb (fits base w) then -1
  else if mx <? 8 + 3 * w then -1 else 8 + 3 * w.

Definition bs_win (s al mx base w : Z) : list (Z * Z) :=
  if bs_res s al mx base w =? -1 then [] else [(s, s + 34 * (8 + 3 * w))].

Definition reac_grant_build_sweep_need : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (s mx al t lo base w : Z) (T junk : list byte),
    a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 mx -> a2 = Z_to_bv 64 al -> a3 = Z_to_bv 64 t ->
    0 <= s < 2 ^ 64 -> 0 <= al < 2 ^ 64 -> -2 ^ 31 <= mx < 2 ^ 31 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BUILD_SWEEP_STACK <= bv_unsigned sp -> mem_inv rsegs m ->
    0 <= w ->
    (al <> 0 -> 0 <= base < 256 /\ 0 <= w < 256 /\
       bytes_at rsegs m al [Z_to_bv 8 base; Z_to_bv 8 w] /\ (al + 2 <= lo \/ bv_unsigned sp <= al)) ->
    0 < t -> length T = 460%nat -> bytes_at rsegs m t T -> I1 T ->
    (t + 460 <= lo \/ bv_unsigned sp <= t) ->
    bytes_at rsegs m CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES ->
    (CTRL_HEADAMP_ROW + 24 <= lo \/ bv_unsigned sp <= CTRL_HEADAMP_ROW) ->
    (bs_res s al mx base w = 8 + 3 * w ->
       rw_cells rsegs m s [CB (Z.to_nat (34 * (8 + 3 * w))) junk] /\
       (s + 34 * (8 + 3 * w) <= lo \/ bv_unsigned sp <= s) /\
       (s + 34 * (8 + 3 * w) <= t \/ t + 460 <= s) /\
       (s + 34 * (8 + 3 * w) <= al \/ al + 2 <= s) /\
       (s + 34 * (8 + 3 * w) <= CTRL_HEADAMP_ROW \/ CTRL_HEADAMP_ROW + 24 <= s)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         r = Z_to_bv 64 (bs_res s al mx base w) /\
         munch ((lo, bv_unsigned sp) :: bs_win s al mx base w) m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES /\
         (bs_res s al mx base w = 8 + 3 * w ->
            rw_cells rsegs m' s [CB (Z.to_nat (34 * (8 + 3 * w)))
                                    (SWEEP base (Z.to_nat w) (sweep_vals T t base (Z.to_nat w)))]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_GRANT_BUILD_SWEEP) fc None m (seg_rom rsegs)).

Definition check_groupa_need : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (row ch p t lo : Z) (T : list byte),
    a0 = Z_to_bv 64 row -> a1 = Z_to_bv 64 ch -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 t ->
    a4 = Z_to_bv 64 (eff T t ch p) ->
    0 <= ch < 48 -> 0 <= p < 3 ->
    0 < t -> length T = 460%nat -> bytes_at rsegs m t T -> I1 T ->
    bytes_at rsegs m row (GA ch p (eff T t ch p)) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_GROUPA_STACK <= bv_unsigned sp -> mem_inv rsegs m ->
    (row + 34 <= lo \/ bv_unsigned sp <= row) -> (t + 460 <= lo \/ bv_unsigned sp <= t) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_GROUPA) fc None m (seg_rom rsegs)).

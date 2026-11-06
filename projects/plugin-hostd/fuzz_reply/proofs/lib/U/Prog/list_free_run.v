From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma lfu_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lfu_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma lfu_addiw : forall z c, -2^31 <= z < 2^31 -> -2^31 <= z + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c)) = Z_to_bv 64 (z + c).
Proof.
  intros z c Hz Hzc. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz, Hzc.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lfu_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma lfu_entry : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo LA : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> mem_inv rsegs m ->
  a0 = Z_to_bv 64 LA -> 0 <= LA < 2 ^ 64 -> LA mod 8 = 0 ->
  evt rsegs (fun ms' => exists a0' m',
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 LA) s1 a0' a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x154a0) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra] /\
      stk rsegs m' lo (bv_unsigned sp + -16))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15488) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo LA
    ST LO MI -> HLA HAl.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 4 step.
  step. rewrite unsigned_lit by lia. rewrite (lfu_land7 LA HAl).
  step. if_false.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma lfu_head_drop : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (LA n : Z) (v c : word),
  s0 = Z_to_bv 64 LA -> 0 <= LA -> LA + 16 <= 2 ^ 64 -> 0 < n < 2 ^ 31 ->
  rw_cells rsegs m LA [C8 v; C4 (Z_to_bv 64 n); C4 c] ->
  evt rsegs (fun ms' => exists a2' a3' a4' a5' a6' a7',
      ms' = MS (mkR (Z_to_bv 64 0x154b8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LA) (Z_to_bv 64 (n - 1))
                    a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14d58) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LA n v c
    -> HL0 HL1 Hn RC.
  step. rewrite (lfu_sx32 n) by lia.
  step. if_cases K0; [exfalso; zify_cond K0; lia|].
  step. rewrite (lfu_addiw n (-1)) by lia. replace (n + -1) with (n - 1) by lia.
  step. if_cases K1; [exfalso; unfold bv_lts, bv_leu in K1; try rewrite (lfu_signed (n - 1)), (lfu_signed n) in K1 by lia;
    zify_cond K1; lia|].
  step. step.
  apply evt_done. do 6 eexists. f_equal.
Qed.

Lemma lfu_head_free : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (LA : Z) (v c : word),
  s0 = Z_to_bv 64 LA -> 0 <= LA -> LA + 16 <= 2 ^ 64 ->
  rw_cells rsegs m LA [C8 v; C4 (Z_to_bv 64 0); C4 c] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x154c4) sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15f4c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LA v c
    -> HL0 HL1 RC.
  step. rewrite (lfu_sx32 0) by lia.
  step. if_true.
  step. step.
  apply evt_done. reflexivity.
Qed.

Lemma lfu_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (LA B : Z) (v n c s0v rav : word),
  s0 = Z_to_bv 64 LA -> 0 <= LA -> LA + 16 <= 2 ^ 64 -> sp = Z_to_bv 64 B -> 0 <= B -> B + 16 <= 2 ^ 64 ->
  (LA + 16 <= B \/ B + 16 <= LA) -> mem_inv rsegs m ->
  rw_cells rsegs m LA [C8 v; C4 n; C4 c] ->
  rw_cells rsegs m B [C8 s0v; C8 rav] ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR rav (Z_to_bv 64 (B + 16)) gp tp t0 t1 t2 s0v s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom rsegs) /\
      munch [(LA, LA + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' LA [C8 (Z_to_bv 64 0); C4 n; C4 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' B [C8 s0v; C8 rav])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154c4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LA B
    v n c s0v rav -> HL0 HL1 -> HB0 HB1 DJ MI RC FR.
  pose proof (munch_refl [(LA, LA + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  step. step. step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

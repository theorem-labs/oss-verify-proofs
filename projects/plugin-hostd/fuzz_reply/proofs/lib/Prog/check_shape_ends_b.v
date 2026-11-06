From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import has_prefix_c next_line_c list_find_c memmove_c
  RelayModel HarnessRep CheckRep check_shape_ends_a.
Import ListNotations.
Open Scope Z_scope.

Lemma ce_wrap : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof. intros x c. apply bv_eq. rewrite !unsigned_lit_wrap. Z.div_mod_to_equations. lia. Qed.

Lemma ce_addw : forall x y, - 2 ^ 31 <= x + y < 2 ^ 31 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + bv_unsigned (Z_to_bv 64 y)) = x + y.
Proof.
  intros x y Hxy. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 31) with 2147483648 in Hxy.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ce_g2 : memmove_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V N CAP i : Z) (us : list byte),
  rw_cells rsegs m (bv_unsigned s0 + 80) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  u8arr rsegs m V us -> Z.of_nat (length us) = 16 * CAP ->
  0 <= i < N -> N <= CAP < 2 ^ 30 -> N < 2 ^ 26 -> 8 <= V -> V + 16 * CAP < 2 ^ 63 ->
  (bv_unsigned s0 + 96 <= V \/ V + 16 * CAP <= bv_unsigned s0 + 80) ->
  s4 = Z_to_bv 64 (- (i + 1)) -> s5 = Z_to_bv 64 (16 * i) -> s6 = Z_to_bv 64 (-16) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      munch [(V + 16 * i, V + 16 * (N - 1)); (bv_unsigned s0 + 88, bv_unsigned s0 + 92)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned s0 + 80) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 CAP)] /\
      u8arr rsegs m' V (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1)))) /\
      ((0 < i /\ ms' = MS (mkR (Z_to_bv 64 0x144a8) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 (Z_to_bv 64 (- i)) (Z_to_bv 64 (16 * (i - 1))) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                         F (Z_to_bv 64 0x14464) fc None m' (seg_rom rsegs)) \/
       (i = 0 /\ ms' = MS (mkR (Z_to_bv 64 0x144a8) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 (Z_to_bv 64 0) (Z_to_bv 64 (-16)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                         F (Z_to_bv 64 0x145a4) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1448c) fc None m (seg_rom rsegs)).
Proof.
  intros MM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    V N CAP i us HC HU HUL Hi HN HN2 HV0 HV1 HD -> -> -> MI.
  pose proof (zr_word s0) as R0. unfold inr64 in R0.
  pose proof (munch_refl [(V + 16 * i, V + 16 * (N - 1)); (bv_unsigned s0 + 88, bv_unsigned s0 + 92)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. rewrite (ce_sx32 N) by lia. step. step. step. step. step.
  rewrite ce_addw by lia. rewrite ce_shl4 by lia.
  assert (Ua0 : bv_unsigned (Z_to_bv 64 (V + 16 * i)) = V + 16 * i) by (apply unsigned_lit; lia).
  assert (Ua1 : bv_unsigned (Z_to_bv 64 (V + 16 * i + 16)) = V + 16 * i + 16) by (apply unsigned_lit; lia).
  assert (Ua2 : bv_unsigned (Z_to_bv 64 (16 * (- (i + 1) + N))) = 16 * (N - i - 1)) by (rewrite unsigned_lit; lia).
  eapply evt_cut.
  { eapply MM with (U := V) (us := us); rewrite ?Ua0, ?Ua1, ?Ua2; [exact HU | lia | lia | lia | lia | exact MI]. }
  intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU1 & WM1 & MI1 & U1).
  rewrite Ua0, Ua1, Ua2 in *.
  replace (V + 16 * i + 16 - V) with (16 * i + 16) in U1 by lia.
  replace (V + 16 * i - V) with (16 * i) in U1 by lia.
  replace (ret_pc (Z_to_bv 64 83112)) with (Z_to_bv 64 83112) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (rw_cells_transport rsegs _ m m1 _ _ HC MU1 WM1 ltac:(cbn [disjoint_from cells_size csize]; lia)) as HC1.
  assert (MU2 : munch [(V + 16 * i, V + 16 * (N - 1)); (bv_unsigned s0 + 88, bv_unsigned s0 + 92)] m m1).
  { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM WM1) as WM2.
  clear MU WM HC MU1 WM1 MI.
  rename MU2 into MU. rename WM2 into WM.
  assert (ULn : Z.of_nat (length (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1)))))
                = 16 * CAP).
  { unfold mm_result, slice. rewrite upd_bytes_length; [exact HUL|].
    rewrite length_firstn, length_skipn. lia. }
  step. rewrite (ce_sx32 N) by lia. step. step. step. step. step.
  if_cases Q.
  - zify_cond Q. assert (Hi0 : 0 < i) by (try rewrite !unsigned_lit_wrap in Q; Z.div_mod_to_equations; lia).
    apply evt_done. do 16 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
    split; [replace (N - 1) with (N + -1) by lia; exact HC1|]. split; [exact U1|].
    left. split; [exact Hi0|].
    replace (- (i + 1) + 1) with (- i) by lia. replace (16 * i + -16) with (16 * (i - 1)) by lia. reflexivity.
  - zify_cond Q. assert (Hi0 : i = 0) by (try rewrite !unsigned_lit_wrap in Q; Z.div_mod_to_equations; lia).
    subst i. step.
    apply evt_done. do 16 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
    split; [replace (N - 1) with (N + -1) by lia; exact HC1|]. split; [exact U1|].
    right. split; [reflexivity|]. reflexivity.
Qed.

Lemma ce_not : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (D : Z.ldiff x (Z.ones 64) = 0).
  { rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x D).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
  pose proof (f_equal (fun z => Z.testbit z n) D) as Dn. cbv beta in Dn. rewrite Z.ldiff_spec, Z.bits_0 in Dn.
  destruct (Z.testbit (Z.ones 64) n), (Z.testbit x n); cbn in *; congruence.
Qed.

Lemma ce_swrap64 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 (z + 18446744073709551616) = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2 ^ 31) with 2147483648 in Hz. Z.div_mod_to_equations. lia.
Qed.

Lemma ce_e2 : memmove_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V N CAP i w : Z) (us : list byte),
  rw_cells rsegs m (bv_unsigned s0 + 80) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  u8arr rsegs m V us -> Z.of_nat (length us) = 16 * CAP ->
  0 <= i < N -> N <= CAP < 2 ^ 30 -> N < 2 ^ 26 -> 8 <= V -> V + 16 * CAP < 2 ^ 63 ->
  (bv_unsigned s0 + 96 <= V \/ V + 16 * CAP <= bv_unsigned s0 + 80) ->
  s4 = Z_to_bv 64 (16 * i) -> s6 = Z_to_bv 64 i -> s8 = Z_to_bv 64 (w + 1) -> s10 = Z_to_bv 64 1 ->
  1 <= w < 2 ^ 26 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      munch [(V + 16 * i, V + 16 * (N - 1)); (bv_unsigned s0 + 88, bv_unsigned s0 + 92)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned s0 + 80) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 CAP)] /\
      u8arr rsegs m' V (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1)))) /\
      ((1 < w /\ ms' = MS (mkR (Z_to_bv 64 0x14590) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 (Z_to_bv 64 (16 * i)) s5 (Z_to_bv 64 i) s7 (Z_to_bv 64 w) s9 (Z_to_bv 64 1) s11
                              t3' t4' t5' t6')
                         F (Z_to_bv 64 0x144e0) fc None m' (seg_rom rsegs)) \/
       (w = 1 /\ ms' = MS (mkR (Z_to_bv 64 0x14590) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 (Z_to_bv 64 (16 * i)) s5 (Z_to_bv 64 i) s7 (Z_to_bv 64 w) s9 (Z_to_bv 64 1) s11
                              t3' t4' t5' t6')
                         F (Z_to_bv 64 0x145a4) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14570) fc None m (seg_rom rsegs)).
Proof.
  intros MM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    V N CAP i w us HC HU HUL Hi HN HN2 HV0 HV1 HD -> -> -> -> Hw MI.
  pose proof (zr_word s0) as R0. unfold inr64 in R0.
  pose proof (munch_refl [(V + 16 * i, V + 16 * (N - 1)); (bv_unsigned s0 + 88, bv_unsigned s0 + 92)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. rewrite (ce_sx32 N) by lia. step. step. step.
  rewrite (unsigned_lit i) by lia. rewrite ce_not by lia. rewrite !unsigned_lit by lia.
  replace (N + (18446744073709551615 - i)) with ((N - i - 1) + 18446744073709551616) by lia.
  rewrite ce_swrap64 by lia.
  step. step. rewrite ce_shl4 by lia. step.
  assert (Ua0 : bv_unsigned (Z_to_bv 64 (V + 16 * i)) = V + 16 * i) by (apply unsigned_lit; lia).
  assert (Ua1 : bv_unsigned (Z_to_bv 64 (V + 16 * i + 16)) = V + 16 * i + 16) by (apply unsigned_lit; lia).
  assert (Ua2 : bv_unsigned (Z_to_bv 64 (16 * (N - i - 1))) = 16 * (N - i - 1)) by (rewrite unsigned_lit; lia).
  eapply evt_cut.
  { eapply MM with (U := V) (us := us); rewrite ?Ua0, ?Ua1, ?Ua2; [exact HU | lia | lia | lia | lia | exact MI]. }
  intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU1 & WM1 & MI1 & U1).
  rewrite Ua0, Ua1, Ua2 in *.
  replace (V + 16 * i + 16 - V) with (16 * i + 16) in U1 by lia.
  replace (V + 16 * i - V) with (16 * i) in U1 by lia.
  replace (ret_pc (Z_to_bv 64 83344)) with (Z_to_bv 64 83344) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (rw_cells_transport rsegs _ m m1 _ _ HC MU1 WM1 ltac:(cbn [disjoint_from cells_size csize]; lia)) as HC1.
  assert (MU2 : munch [(V + 16 * i, V + 16 * (N - 1)); (bv_unsigned s0 + 88, bv_unsigned s0 + 92)] m m1).
  { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM WM1) as WM2.
  clear MU WM HC MU1 WM1 MI.
  rename MU2 into MU. rename WM2 into WM.
  assert (ULn : Z.of_nat (length (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1)))))
                = 16 * CAP).
  { unfold mm_result, slice. rewrite upd_bytes_length; [exact HUL|].
    rewrite length_firstn, length_skipn. lia. }
  step. rewrite (ce_sx32 N) by lia. step. step. step.
  rewrite (unsigned_lit (w + 1)), ce_swrap by lia. replace (w + 1 + -1) with w by lia.
  step. if_cases Q.
  - zify_cond Q. assert (Hw1 : 1 < w) by (try rewrite !unsigned_lit in Q by lia; lia).
    apply evt_done. do 16 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
    split; [replace (N - 1) with (N + -1) by lia; exact HC1|]. split; [exact U1|].
    left. split; [exact Hw1 | reflexivity].
  - zify_cond Q. assert (Hw1 : w = 1) by (try rewrite !unsigned_lit in Q by lia; lia).
    apply evt_done. do 16 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
    split; [replace (N - 1) with (N + -1) by lia; exact HC1|]. split; [exact U1|].
    right. split; [exact Hw1 | reflexivity].
Qed.

Lemma ce_g1 : has_prefix_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N CAP i q : Z) (S P slack : list byte),
  rw_cells rsegs m (bv_unsigned s2) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  ro_cells rsegs m (V + 16 * i) [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 (Z.of_nat (length S)))] ->
  bytes_at rsegs m q S -> 0 <= q -> q + Z.of_nat (length S) < 2 ^ 64 ->
  0 <= i < 2 ^ 26 -> 0 <= V -> V + 16 * i + 16 <= 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned s1) (P ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) P ->
  (- (bv_unsigned s1 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  (q + Z.of_nat (length S) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= q) ->
  (bv_unsigned s1 + Z.of_nat (length P + 1 + length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s1) ->
  s4 = Z_to_bv 64 (- (i + 1)) -> s5 = Z_to_bv 64 (16 * i) -> s6 = Z_to_bv 64 (-16) ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp) /\
      ((prefix_of P S /\
        ms' = MS (mkR (Z_to_bv 64 0x1448c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' a7'
                      s2 (Z_to_bv 64 q) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x15664) fc None m' (seg_rom rsegs)) \/
       (~ prefix_of P S /\ 0 < i /\
        ms' = MS (mkR (Z_to_bv 64 0x14480) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                      s2 (Z_to_bv 64 q) (Z_to_bv 64 (- i)) (Z_to_bv 64 (16 * (i - 1))) s6 s7 s8 s9 s10 s11
                      t3' t4' t5' t6')
                 F (Z_to_bv 64 0x14464) fc None m' (seg_rom rsegs)) \/
       (~ prefix_of P S /\ i = 0 /\
        ms' = MS (mkR (Z_to_bv 64 0x14480) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                      s2 (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 (-16)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x145a4) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14464) fc None m (seg_rom rsegs)).
Proof.
  intros HP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo V N CAP i q S P slack HC RC HS Hq0 Hq1 Hi HV0 HV1 HPB NZ SL MI ST LO D1 D2 -> -> ->.
  pose proof (zr_word s1) as R1. unfold inr64 in R1.
  step. step. remember (V + 16 * i) as R eqn:ER. step. step. step. step. step.
  assert (Uq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 (Z.of_nat (length S))) = Z.of_nat (length S)) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply HP with (lo := lo) (S := S) (P := P) (slack := slack); rewrite ?Uq, ?UL;
      [exact HS | reflexivity | exact HPB | exact NZ | exact SL | exact MI | exact ST | unfold HAS_PREFIX_K; lia
      | unfold HAS_PREFIX_K; exact D1 | unfold HAS_PREFIX_K; exact D2]. }
  intros ms1 (u0 & u1 & u2 & b0 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 &
    -> & MU1 & WM1 & MI1 & ST1 & PR).
  unfold HAS_PREFIX_K in MU1.
  replace (ret_pc (Z_to_bv 64 83072)) with (Z_to_bv 64 83072) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct PR as [(PO & ->)|(PO & ->)].
  - step. if_cases Q; [vm_compute in Q; discriminate|]. step. step.
    apply evt_done. do 15 eexists. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
    split; [exact ST1|]. left. split; [exact PO | reflexivity].
  - step. if_cases Q; [|vm_compute in Q; discriminate]. step. step. step. if_cases Q2.
    + zify_cond Q2. assert (Hi0 : 0 < i) by (try rewrite !unsigned_lit_wrap in Q2; Z.div_mod_to_equations; lia).
      apply evt_done. do 15 eexists. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      split; [exact ST1|]. right. left. split; [exact PO|]. split; [exact Hi0|].
      replace (- (i + 1) + 1) with (- i) by lia. replace (16 * i + -16) with (16 * (i - 1)) by lia. reflexivity.
    + zify_cond Q2. assert (Hi0 : i = 0) by (try rewrite !unsigned_lit_wrap in Q2; Z.div_mod_to_equations; lia).
      subst i. step.
      apply evt_done. do 15 eexists. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      split; [exact ST1|]. right. right. split; [exact PO|]. split; reflexivity.
Qed.

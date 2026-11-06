From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregInit reac_boxreg_init_c memset_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rbi_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (W0 & W1 & W2)].
  apply cells_wf_app in Hwf. destruct Hwf as [Hw1 Hw2].
  rewrite cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact Hw1.
  rewrite cells_size_app in W1, W2.
  split.
  - split; [ split; assumption | ]. split; [ lia | ]. split; [ lia | ].
    intros i Hi. apply W2. lia.
  - split; [ split; assumption | ]. split; [ lia | ]. split; [ lia | ].
    intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply W2. lia.
Qed.

Lemma rbi_stk_fill : forall m m' lo hi A n bs,
  stk rsegs m lo hi -> munch [(A, A + n)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' A bs -> n <= Z.of_nat (length bs) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi A n bs (H1 & H2 & H) Hm Hw (B0 & B1 & B) Hn.
  split; [ lia | ]. split; [ lia | ].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [ apply Hw; exact Hwa | ].
  destruct (Z_lt_le_dec a A) as [L | L]; [ | destruct (Z_lt_le_dec a (A + n)) as [L2 | L2] ].
  - exists b. unfold mrd in Hb |- *. rewrite Hm; [ exact Hb | ].
    cbn [outside]. rewrite wa_unsigned by lia. split; [ lia | exact I ].
  - assert (Hi : (Z.to_nat (a - A) < length bs)%nat) by lia.
    pose proof (B _ Hi) as E.
    replace (A + Z.of_nat (Z.to_nat (a - A))) with a in E by lia.
    rewrite E. destruct (nth_error bs (Z.to_nat (a - A))) eqn:N; [ eexists; reflexivity | ].
    apply nth_error_None in N. lia.
  - exists b. unfold mrd in Hb |- *. rewrite Hm; [ exact Hb | ].
    cbn [outside]. rewrite wa_unsigned by lia. split; [ lia | exact I ].
Qed.

Lemma rbi_cond : forall a : word,
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned a + -1))) (Z_to_bv 64 40) =
  ((1 <=? bv_swrap 32 (bv_unsigned a)) && (bv_swrap 32 (bv_unsigned a) <=? 40)).
Proof.
  intros a. rewrite bv_ltu_Z, (unsigned_lit 40), unsigned_lit_wrap by lia.
  pose proof (bv_unsigned_in_range 64 a) as R.
  revert R. generalize (bv_unsigned a). intros u R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
  unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616.
  apply eq_true_iff_eq. rewrite andb_true_iff, Z.ltb_lt, !Z.leb_le.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rbi_le4 : forall a : word, 1 <= bv_swrap 32 (bv_unsigned a) <= 40 ->
  le4 a = le4 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned a))).
Proof.
  intros a H. unfold le4. rewrite (unsigned_lit (bv_swrap 32 (bv_unsigned a))) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (bv_unsigned a)) 32) by lia.
  f_equal. clear H. generalize (bv_unsigned a). intros u.
  unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Theorem reac_boxreg_init_holds : memset_contract -> reac_boxreg_init_contract.
Proof.
  intros MEMS. unfold reac_boxreg_init_contract, REAC_BOXREG_INIT, REAC_BOXREG_INIT_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo r junk E0 HK Hr0 Hr4 ST LO DJ HMI.
  pose proof (rw_cells_bound rsegs m r _ HK) as HBr.
  change (Z.of_nat (cells_size [CB 288 junk])) with 288 in HBr.
  assert (Er : r = bv_unsigned a0) by (rewrite E0; symmetry; apply unsigned_lit; lia).
  subst r. clear E0.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 288); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (U284 : bv_unsigned (Z_to_bv 64 284) = 284) by reflexivity.
  apply (rw_cells_cb_split rsegs m (bv_unsigned a0) [CB 288 junk]
           [CB 284 (firstn 284 junk); CB 4 (skipn 284 junk)] 0 284) in HK; [ | reflexivity | reflexivity ].
  destruct (rbi_split m (bv_unsigned a0) [CB 284 (firstn 284 junk)] [CB 4 (skipn 284 junk)] HK) as [HK1 HK2].
  clear HK.
  change (Z.of_nat (cells_size [CB 284 (firstn 284 junk)])) with 284 in HK2.
  carve_frame 32%nat ST.
  step. step. step. step.
  step. step. step. step. step.
  eapply evt_cut; [ eapply MEMS; [ exact HK1 | exact HMI ] | ].
  intros ms' PO.
  destruct PO as (c5 & c6 & c7 & c11 & c12 & c13 & c14 & c15 & c16 & c17 & c28 & c29 & c30 & c31 & mc
                  & E & MUc & WMc & MI2 & HZ).
  subst ms'.
  assert (HZ' : rw_cells rsegs mc (bv_unsigned a0) [CB 284 (repeat (Z_to_bv 8 0) 284)]) by exact HZ.
  clear HZ. rename HZ' into HZ.
  rewrite U284 in MUc.
  pose proof HZ as [[_ HZb] _]. cbn [cells_bytes cbytes] in HZb. rewrite app_nil_r in HZb.
  assert (HN : 284 <= Z.of_nat (length (repeat (Z_to_bv 8 0) 284))) by (rewrite repeat_length; lia).
  pose proof (rbi_stk_fill _ _ _ _ _ _ _ ST MUc WMc HZb HN) as ST2.
  clear ST HZb HN. rename ST2 into ST.
  lazymatch type of MUc with
  | munch _ ?mm ?mm' => transport_after_call rsegs mm mm' MUc WMc
  end.
  clear MUc WMc HMI.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  step. step. step.
  pose proof (init_bytes_inv (bv_swrap 32 (bv_unsigned a1))) as (I1 & I2 & I3).
  if_cases HC.
  - assert (HB1 : ((1 <=? bv_swrap 32 (bv_unsigned a1)) && (bv_swrap 32 (bv_unsigned a1) <=? 40)) = true)
      by (rewrite <- rbi_cond; exact HC).
    assert (HCL : clamp40 (bv_swrap 32 (bv_unsigned a1)) = bv_swrap 32 (bv_unsigned a1))
      by (unfold clamp40; rewrite HB1; reflexivity).
    pose proof (clamp40_range (bv_swrap 32 (bv_unsigned a1))) as HF. rewrite HCL in HF.
    assert (HV : le4 a1 = le4 (Z_to_bv 64 (clamp40 (bv_swrap 32 (bv_unsigned a1)))))
      by (rewrite HCL; apply rbi_le4; exact HF).
    clear HC HB1 HCL HF.
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HBY : bytes_at rsegs mm (bv_unsigned a0) (init_bytes (clamp40 (bv_swrap 32 (bv_unsigned a1)))))
    end.
    { unfold init_bytes. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split.
      - destruct HZ as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
      - rewrite repeat_length. change (Z.of_nat 284) with 284. rewrite <- HV.
        destruct HK2 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    finish.
  - assert (HB1 : ((1 <=? bv_swrap 32 (bv_unsigned a1)) && (bv_swrap 32 (bv_unsigned a1) <=? 40)) = false)
      by (rewrite <- rbi_cond; exact HC).
    assert (HV : le4 (Z_to_bv 64 40) = le4 (Z_to_bv 64 (clamp40 (bv_swrap 32 (bv_unsigned a1)))))
      by (unfold clamp40; rewrite HB1; reflexivity).
    clear HC HB1.
    step.
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HBY : bytes_at rsegs mm (bv_unsigned a0) (init_bytes (clamp40 (bv_swrap 32 (bv_unsigned a1)))))
    end.
    { unfold init_bytes. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split.
      - destruct HZ as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
      - rewrite repeat_length. change (Z.of_nat 284) with 284. rewrite <- HV.
        destruct HK2 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    finish.
Qed.

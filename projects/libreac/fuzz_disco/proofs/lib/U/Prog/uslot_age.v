From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib disco_table_c disco_table
  reac_disco_table_age_c reac_disco_table_age check_table_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ua_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.b2z (a <? b)).
Proof. intros a b Ha Hb. rewrite v_sltu_b2z, !unsigned_lit by lia. reflexivity. Qed.

Lemma ua_count : forall f j, 0 <= j -> age_count f (Z.to_nat (j + 1)) = age_count f (Z.to_nat j) + Z.b2z (f j).
Proof.
  intros f j Hj. rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r.
  cbn [age_count]. rewrite Z2Nat.id by lia. destruct (f j); reflexivity.
Qed.

Lemma ua_count_range : forall f k, 0 <= age_count f k <= Z.of_nat k.
Proof. intros f k. induction k as [|k IH]; cbn [age_count]; [lia|]. destruct (f (Z.of_nat k)); lia. Qed.

Lemma ua_seq : forall s (b : bool), 0 <= s < 2 ^ 32 ->
  Z_to_bv 64 (bv_swrap 32 (if b then (s + 1) mod 2 ^ 32 else s)) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 s)) + bv_unsigned (Z_to_bv 64 (Z.b2z b)))).
Proof.
  intros s b Hs. f_equal. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  replace (2 ^ 64) with 18446744073709551616 by reflexivity.
  destruct b; cbn [Z.b2z]; Z.div_mod_to_equations; lia.
Qed.

Lemma ua_eqb_refl : forall w : word, bv_eqb w w = true.
Proof. intros w. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma ua_wadd : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  intros x c. rewrite unsigned_lit_wrap.
  rewrite <- (Z_to_bv_mod64 (x mod 2 ^ 64 + c)), <- (Z_to_bv_mod64 (x + c)).
  f_equal. apply Zplus_mod_idemp_l.
Qed.

Lemma ua_chk8 : forall j, 0 <= j < 8 -> bv_eqb (Z_to_bv 64 (48 * j - 384)) (Z_to_bv 64 0) = false.
Proof. intros j Hj. unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq. Z.div_mod_to_equations. lia. Qed.

Lemma ua_stale_ge : forall T j now, now <= last_of T j -> disco_stale T j now = false.
Proof. intros T j now H. unfold disco_stale. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. Qed.

Lemma ua_stale_lt : forall T j now, last_of T j < now -> now - last_of T j < STALE1 -> disco_stale T j now = false.
Proof.
  intros T j now H1 H2. unfold disco_stale, REAC_DISCO_STALE_NS, STALE1 in *.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma ua_stale_t : forall T j now, last_of T j < now -> STALE1 <= now - last_of T j -> disco_stale T j now = true.
Proof.
  intros T j now H1 H2. unfold disco_stale, REAC_DISCO_STALE_NS, STALE1 in *.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Ltac ua_weq := first [ reflexivity | (f_equal; lia) | (rewrite ?unsigned_lit by lia; f_equal; lia)
                     | (rewrite ?ua_wadd; f_equal; lia)
                     | (apply bv_eq; rewrite !unsigned_lit_wrap; Z.div_mod_to_equations; lia) ].

Ltac ua_ret n := rewrite (ret_pc_even n) by (first [lia | reflexivity]).

Lemma uslot_R5_R7 : reac_disco_table_age_contract -> check_table_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo now : Z) (T : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 now ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 ->
  rw_cells rsegs m (X + 120) [C8 (Z_to_bv 64 STALE1)] ->
  rw_cells rsegs m (X + 544) [CB 400 T] ->
  tbl_T1 T -> tbl_T2 T -> tbl_T3 T -> tbl_T4 T ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + CHECK_TABLE_K <= X ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (T' : list byte) (removed : Z),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3' s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x136ec) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 544, X + 944)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 120) [C8 (Z_to_bv 64 STALE1)] /\
       rw_cells rsegs m' (X + 544) [CB 400 T'] /\
       age_model T now = (T', removed) /\ age_post T now T' removed /\
       tbl_T1 T' /\ tbl_T2 T' /\ tbl_T3 T' /\ tbl_T4 T')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135ac) fc None m (seg_rom rsegs)).
Proof.
  intros AGE CHK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo now T Esp Es1 HX0 HX16 HX1 Hnow R120 RT T1 T2 T3 T4 MI ST HLO.
  subst sp s1. unfold CHECK_TABLE_K in HLO.
  pose proof (munch_refl [(lo, X); (X + 544, X + 944)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply rw_cb in RT. destruct RT as (LT & HT & HW). change (Z.of_nat 400) with 400 in HW.
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (MID : forall (w1 w5 w6 w7 w8 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w28 w29 w30 w31 : word) (c : Z),
    c = age_count (fun j => disco_stale T j now) (Z.to_nat (n_of T)) ->
    w8 = Z_to_bv 64 (bv_swrap 32 (seq_of T)) -> w20 = Z_to_bv 64 c -> w21 = Z_to_bv 64 (n_of T) ->
    evt rsegs QQ (MS (mkR w1 (Z_to_bv 64 X) gp tp w5 w6 w7 w8 (Z_to_bv 64 now) w10 w11 w12 w13 w14 w15 w16 w17
                          s2 w19 w20 w21 s6 s7 s8 s9 s10 s11 w28 w29 w30 w31)
                     F (Z_to_bv 64 0x13604) fc None m (seg_rom rsegs))).
  { intros w1 w5 w6 w7 w8 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w28 w29 w30 w31 c Hc E8 E20 E21.
    subst w8 w20 w21.
    pose proof (ua_count_range (fun j => disco_stale T j now) (Z.to_nat (n_of T))) as Hcr.
    rewrite <- Hc in Hcr. rewrite Z2Nat.id in Hcr by lia.
    step. step. step.
    eapply evt_cut.
    { eapply AGE with (lo := lo) (t := X + 544) (now := now) (T := T).
      - ua_weq.
      - ua_weq.
      - lia.
      - lia.
      - Z.div_mod_to_equations. lia.
      - apply rw_cb. split; [exact LT|]. split; [exact HT|exact HW].
      - exact LT.
      - exact (conj T1 (conj T2 (conj T3 T4))).
      - exact MI.
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. unfold REAC_DISCO_TABLE_AGE_K. lia.
      - unfold off_window. rewrite unsigned_lit by lia. lia. }
    intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & T' & r &
                E2 & MU2 & WM2 & MI2 & ST2 & RT2 & AM & AP).
    subst ms'.
    rewrite unsigned_lit in MU2, ST2 by lia. unfold REAC_DISCO_TABLE_AGE_K in MU2.
    clear MI.
    transport_after_call rsegs m m2 MU2 WM2. clear MU2 WM2.
    ua_ret 0x13610.
    pose proof AP as (LT2 & Hrm & Hrr & Hn2 & Hns & Hsq & (U1 & U2 & U3 & U4) & _ & _).
    assert (Hrc : r = c) by (rewrite Hrm, Hc; reflexivity).
    clear Hrm. subst r.
    pose proof U1 as U1'. unfold tbl_T1 in U1'.
    step. step. step.
    eapply evt_cut.
    { eapply CHK with (lo := lo) (t := X + 544) (T := T').
      - ua_weq.
      - Z.div_mod_to_equations. lia.
      - apply rw_cb in RT2. destruct RT2 as (_ & B & _). exact B.
      - exact LT2.
      - exact U1.
      - exact U2.
      - exact U3.
      - exact MI2.
      - rewrite unsigned_lit by lia. exact ST2.
      - rewrite unsigned_lit by lia. unfold CHECK_TABLE_K. lia.
      - unfold off_window. rewrite unsigned_lit by lia. lia. }
    intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
                E3 & MU3 & WM3 & MI3 & ST3).
    subst ms'.
    rewrite unsigned_lit in MU3, ST3 by lia. unfold CHECK_TABLE_K in MU3.
    clear MI2.
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3.
    ua_ret 0x1361c.
    apply rw_cb in RT2. destruct RT2 as (_ & HT2 & HW2).
    assert (FIN : forall (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v28 v29 v30 v31 : word),
      v1 = Z_to_bv 64 0x1361c -> v10 = Z_to_bv 64 (n_of T') -> v11 = Z_to_bv 64 0 ->
      v19 = Z_to_bv 64 c -> v20 = Z_to_bv 64 c ->
      evt rsegs QQ (MS (mkR v1 (Z_to_bv 64 X) gp tp v5 v6 v7
                            (Z_to_bv 64 (bv_swrap 32 (seq_of T))) (Z_to_bv 64 now)
                            v10 v11 v12 v13 v14 v15 v16 v17
                            s2 v19 v20 (Z_to_bv 64 (n_of T)) s6 s7 s8 s9 s10 s11 v28 v29 v30 v31)
                       F (Z_to_bv 64 0x136b8) fc None m3 (seg_rom rsegs))).
    { intros v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v28 v29 v30 v31 E1 E10 E11 E19 E20.
      subst v1 v10 v11 v19 v20.
      replace (n_of T') with (n_of T - c) by lia.
      step. step.
      rewrite ?(unsigned_lit (n_of T)), ?(unsigned_lit c) by lia.
      rewrite (swrap32_small (n_of T - c)) by lia.
      step.
      rewrite ua_eqb_refl. cbn [negb].
      step.
      rewrite (unsigned_lit (n_of T - c)) by lia. rewrite Z.add_0_r, (swrap32_small (n_of T - c)) by lia.
      step.
      rewrite Z.lxor_nilpotent.
      step.
      rewrite ?w0_lit. rewrite ua_sltu by lia.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ (if ?cc then _ else _) _ _ _ _) =>
        replace cc with false by (vm_compute; reflexivity) end.
      cbv iota.
      pose proof (rd_sub _ (X + 544) T' 392 4 HT2 ltac:(lia) ltac:(rewrite LT2; lia)) as RS2.
      step.
      rewrite lw_val by (apply length_sub; lia).
      change (bytes_le_to_Z (sub T' 392 4)) with (seq_of T').
      step.
      rewrite ?w0_lit. rewrite ua_sltu by lia.
      step.
      rewrite Hsq.
      rewrite (ua_seq (seq_of T) (0 <? c) (seq_range T)).
      step.
      rewrite ua_eqb_refl. cbn [negb].
      apply evt_done. unfold QQ.
      do 20 eexists. exists m3, T', c.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
      split; [exact R120|].
      split; [apply rw_cb; split; [exact LT2|]; split; [exact HT2|exact HW2]|].
      split; [exact AM|]. split; [exact AP|].
      exact (conj U1 (conj U2 (conj U3 U4))). }
    assert (L4 : forall (k : nat) (j : Z)
                        (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v28 v29 v30 v31 : word),
      Z.of_nat k = n_of T' - j -> 0 <= j < n_of T' ->
      v1 = Z_to_bv 64 0x1361c -> v10 = Z_to_bv 64 (n_of T') -> v11 = Z_to_bv 64 0 ->
      v12 = Z_to_bv 64 (48 * j - 384) -> v13 = Z_to_bv 64 (n_of T' - j) -> v14 = Z_to_bv 64 (X + 584 + 48 * j) ->
      v16 = Z_to_bv 64 STALE1 -> v19 = Z_to_bv 64 c -> v20 = Z_to_bv 64 c ->
      evt rsegs QQ (MS (mkR v1 (Z_to_bv 64 X) gp tp v5 v6 v7
                            (Z_to_bv 64 (bv_swrap 32 (seq_of T))) (Z_to_bv 64 now)
                            v10 v11 v12 v13 v14 v15 v16 v17
                            s2 v19 v20 (Z_to_bv 64 (n_of T)) s6 s7 s8 s9 s10 s11 v28 v29 v30 v31)
                       F (Z_to_bv 64 0x13638) fc None m3 (seg_rom rsegs))).
    { induction k as [|k IH];
        intros j v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v28 v29 v30 v31
          Hk Hj E1 E10 E11 E12 E13 E14 E16 E19 E20; [lia|].
      subst v1 v10 v11 v12 v13 v14 v16 v19 v20.
      step.
      rewrite ua_chk8 by lia. cbn [negb].
      pose proof (rd_sub _ (X + 544) T' (48 * j + 40) 8 HT2 ltac:(lia) ltac:(rewrite LT2; lia)) as RL.
      step.
      rewrite ld_val by (apply length_sub; lia).
      change (bytes_le_to_Z (sub T' (48 * j + 40) 8)) with (last_of T' j).
      clear RL.
      pose proof (last_range T' j LT2 ltac:(lia)) as LR.
      pose proof (Hns j ltac:(lia)) as NS.
      assert (TAIL : forall v15' : word,
        evt rsegs QQ (MS (mkR (Z_to_bv 64 0x1361c) (Z_to_bv 64 X) gp tp v5 v6 v7
                              (Z_to_bv 64 (bv_swrap 32 (seq_of T))) (Z_to_bv 64 now)
                              (Z_to_bv 64 (n_of T')) (Z_to_bv 64 0) (Z_to_bv 64 (48 * j - 384))
                              (Z_to_bv 64 (n_of T' - j)) (Z_to_bv 64 (X + 584 + 48 * j)) v15'
                              (Z_to_bv 64 STALE1) v17
                              s2 (Z_to_bv 64 c) (Z_to_bv 64 c) (Z_to_bv 64 (n_of T)) s6 s7 s8 s9 s10 s11
                              v28 v29 v30 v31)
                         F (Z_to_bv 64 0x13660) fc None m3 (seg_rom rsegs))).
      { intros v15'.
        step. step. step. step.
        rewrite ?ua_wadd. rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (n_of T' - j + -1) 0) as [Ee|Ee]; cbn [negb].
        - step.
          rewrite ?w0_lit. rewrite ua_sltu by lia.
          step.
          rewrite ua_eqb_refl. cbn [negb].
          step.
          eapply FIN; ua_weq.
        - eapply (IH (j + 1)); try ua_weq; lia. }
      step.
      rewrite ltu_lit by lia.
      destruct (Z.ltb_spec (last_of T' j) now) as [Hl|Hl]; cbn [negb].
      - step.
        rewrite (unsigned_lit now), (unsigned_lit (last_of T' j)) by lia.
        step.
        rewrite ltu_lit by (unfold STALE1; lia).
        destruct (Z.ltb_spec (now - last_of T' j) STALE1) as [Hs|Hs]; cbn [negb].
        + apply TAIL.
        + exfalso. rewrite (ua_stale_t T' j now Hl Hs) in NS. discriminate.
      - apply TAIL. }
    pose proof (rd_sub _ (X + 544) T' 384 4 HT2 ltac:(lia) ltac:(rewrite LT2; lia)) as RN2.
    step.
    rewrite lw_val by (apply length_sub; lia).
    change (bv_swrap 32 (bytes_le_to_Z (sub T' 384 4))) with (n_of T') in *.
    clear RN2.
    step.
    rewrite lts_lit by lia.
    destruct (Z.ltb_spec 0 (n_of T')) as [Hn'|Hn']; cbn [negb].
    - step. step. step. step. step.
      eapply (L4 (Z.to_nat (n_of T')) 0); try ua_weq; lia.
    - step. step.
      rewrite ua_eqb_refl. cbn [negb].
      eapply FIN; ua_weq. }
  assert (L3 : forall (k : nat) (j c : Z)
                      (w1 w5 w6 w7 w8 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w28 w29 w30 w31 : word),
    Z.of_nat k = n_of T - j -> 0 <= j < n_of T -> c = age_count (fun j => disco_stale T j now) (Z.to_nat j) ->
    w8 = Z_to_bv 64 (bv_swrap 32 (seq_of T)) ->
    w10 = Z_to_bv 64 (48 * j - 384) -> w11 = Z_to_bv 64 (n_of T - j) -> w12 = Z_to_bv 64 (X + 584 + 48 * j) ->
    w14 = Z_to_bv 64 STALE1 -> w20 = Z_to_bv 64 c -> w21 = Z_to_bv 64 (n_of T) ->
    evt rsegs QQ (MS (mkR w1 (Z_to_bv 64 X) gp tp w5 w6 w7 w8 (Z_to_bv 64 now) w10 w11 w12 w13 w14 w15 w16 w17
                          s2 w19 w20 w21 s6 s7 s8 s9 s10 s11 w28 w29 w30 w31)
                     F (Z_to_bv 64 0x135cc) fc None m (seg_rom rsegs))).
  { induction k as [|k IH];
      intros j c w1 w5 w6 w7 w8 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w28 w29 w30 w31
        Hk Hj Hc E8 E10 E11 E12 E14 E20 E21; [lia|].
    subst w8 w10 w11 w12 w14 w20 w21.
    pose proof (ua_count_range (fun j => disco_stale T j now) (Z.to_nat j)) as Hcr.
    rewrite <- Hc in Hcr. rewrite Z2Nat.id in Hcr by lia.
    step.
    rewrite ua_chk8 by lia. cbn [negb].
    pose proof (rd_sub _ (X + 544) T (48 * j + 40) 8 HT ltac:(lia) ltac:(rewrite LT; lia)) as RL.
    step.
    rewrite ld_val by (apply length_sub; lia).
    change (bytes_le_to_Z (sub T (48 * j + 40) 8)) with (last_of T j).
    clear RL.
    pose proof (last_range T j LT ltac:(lia)) as LR.
    assert (TAIL : forall (c' : Z) (w13' : word),
      c' = age_count (fun j => disco_stale T j now) (Z.to_nat (j + 1)) ->
      evt rsegs QQ (MS (mkR w1 (Z_to_bv 64 X) gp tp w5 w6 w7 (Z_to_bv 64 (bv_swrap 32 (seq_of T))) (Z_to_bv 64 now)
                            (Z_to_bv 64 (48 * j - 384)) (Z_to_bv 64 (n_of T - j)) (Z_to_bv 64 (X + 584 + 48 * j))
                            w13' (Z_to_bv 64 STALE1) w15 w16 w17
                            s2 w19 (Z_to_bv 64 c') (Z_to_bv 64 (n_of T)) s6 s7 s8 s9 s10 s11 w28 w29 w30 w31)
                       F (Z_to_bv 64 0x135f4) fc None m (seg_rom rsegs))).
    { intros c' w13' Hc'.
      pose proof (ua_count_range (fun j => disco_stale T j now) (Z.to_nat (j + 1))) as Hcr'.
      rewrite <- Hc' in Hcr'. rewrite Z2Nat.id in Hcr' by lia.
      step. step. step. step.
      rewrite ?ua_wadd. rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (n_of T - j + -1) 0) as [Ee|Ee]; cbn [negb].
      - eapply (MID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c'); try ua_weq.
        rewrite Hc'. replace (n_of T) with (j + 1) by lia. reflexivity.
      - eapply (IH (j + 1) c'); try ua_weq; lia. }
    step.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (last_of T j) now) as [Hl|Hl]; cbn [negb].
    - step.
      rewrite (unsigned_lit now), (unsigned_lit (last_of T j)) by lia.
      step.
      rewrite ltu_lit by (unfold STALE1; lia).
      destruct (Z.ltb_spec (now - last_of T j) STALE1) as [Hs|Hs]; cbn [negb].
      + apply (TAIL c).
        rewrite ua_count, <- Hc, (ua_stale_lt T j now Hl Hs) by lia. cbn [Z.b2z]. lia.
      + step.
        rewrite (unsigned_lit c) by lia. rewrite (swrap32_small (c + 1)) by lia.
        step.
        rewrite lts_lit by lia.
        replace (c + 1 <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
        step.
        apply (TAIL (c + 1)).
        rewrite ua_count, <- Hc, (ua_stale_t T j now Hl Hs) by lia. cbn [Z.b2z]. reflexivity.
    - apply (TAIL c).
      rewrite ua_count, <- Hc, (ua_stale_ge T j now) by lia. cbn [Z.b2z]. lia. }
  pose proof (rd_sub _ (X + 544) T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  clear RN.
  pose proof (rd_sub _ (X + 544) T 392 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RS.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bytes_le_to_Z (sub T 392 4)) with (seq_of T).
  clear RS.
  step.
  step.
  rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 (n_of T)) as [Hn|Hn]; cbn [negb].
  - step. step. step. step.
    eapply (L3 (Z.to_nat (n_of T)) 0 0); try ua_weq; lia.
  - eapply (MID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0); try ua_weq.
    replace (Z.to_nat (n_of T)) with O by lia. reflexivity.
Qed.

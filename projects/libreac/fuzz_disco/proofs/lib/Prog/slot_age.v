From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib disco_table_c disco_table
  reac_disco_table_age_c reac_disco_table_age check_table_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sa_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.b2z (a <? b)).
Proof. intros a b Ha Hb. rewrite v_sltu_b2z, !unsigned_lit by lia. reflexivity. Qed.

Lemma sa_sltu_wrap : forall a d, 0 <= a < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 d) = Z_to_bv 64 (Z.b2z (a <? d mod 2 ^ 64)).
Proof. intros a d Ha. rewrite v_sltu_b2z, (unsigned_lit a), unsigned_lit_wrap by lia. reflexivity. Qed.

Lemma sa_land : forall b1 b2 : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.b2z b1))) (bv_unsigned (Z_to_bv 64 (Z.b2z b2)))) =
  Z_to_bv 64 (Z.b2z (b1 && b2)).
Proof.
  intros b1 b2. rewrite !unsigned_lit by (destruct b1, b2; cbn; lia). destruct b1, b2; reflexivity.
Qed.

Lemma sa_stale : forall T j now, 0 <= last_of T j < 2 ^ 64 -> 0 <= now < 2 ^ 64 ->
  (last_of T j <? now) && (STALE_NS <? (now - last_of T j) mod 2 ^ 64) = disco_stale T j now.
Proof.
  intros T j now HL Hn. unfold disco_stale, STALE_NS, REAC_DISCO_STALE_NS.
  destruct (Z.ltb_spec (last_of T j) now); [|reflexivity].
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma sa_addw : forall c (b : bool), 0 <= c < 2 ^ 31 - 1 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 c) + bv_unsigned (Z_to_bv 64 (Z.b2z b)))) =
  Z_to_bv 64 (c + Z.b2z b).
Proof.
  intros c b Hc. assert (Hb : 0 <= Z.b2z b <= 1) by (destruct b; cbn; lia).
  rewrite !unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma sa_count : forall f j, 0 <= j -> age_count f (Z.to_nat (j + 1)) = age_count f (Z.to_nat j) + Z.b2z (f j).
Proof.
  intros f j Hj. rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r.
  cbn [age_count]. rewrite Z2Nat.id by lia. destruct (f j); reflexivity.
Qed.

Lemma sa_count_range : forall f k, 0 <= age_count f k <= Z.of_nat k.
Proof. intros f k. induction k as [|k IH]; cbn [age_count]; [lia|]. destruct (f (Z.of_nat k)); lia. Qed.

Lemma sa_seq : forall s (b : bool), 0 <= s < 2 ^ 32 ->
  Z_to_bv 64 (bv_swrap 32 (if b then (s + 1) mod 2 ^ 32 else s)) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 s)) + bv_unsigned (Z_to_bv 64 (Z.b2z b)))).
Proof.
  intros s b Hs. f_equal. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  replace (2 ^ 64) with 18446744073709551616 by reflexivity.
  destruct b; cbn [Z.b2z]; Z.div_mod_to_equations; lia.
Qed.

Lemma sa_eqb_refl : forall w : word, bv_eqb w w = true.
Proof. intros w. unfold bv_eqb. apply Z.eqb_refl. Qed.

Ltac sa_weq := first [ reflexivity | (f_equal; lia) | (rewrite ?unsigned_lit by lia; f_equal; lia) ].

Ltac sa_ret n := rewrite (ret_pc_even n) by (first [lia | reflexivity]).

Lemma slot_R5_R7 : reac_disco_table_age_contract -> check_table_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo n p now : Z) (T : list byte) (junk : word),
  sp = Z_to_bv 64 X -> s3 = Z_to_bv 64 n -> s6 = Z_to_bv 64 p -> s11 = Z_to_bv 64 now -> a4 = Z_to_bv 64 STALE_NS ->
  0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 -> 0 <= now < 2 ^ 64 ->
  rw_cells rsegs m (X + 152) [C8 junk] ->
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 STALE_NS)] ->
  rw_cells rsegs m (X + 512) [CB 400 T] ->
  tbl_T1 T -> tbl_T2 T -> tbl_T3 T -> tbl_T4 T ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + CHECK_TABLE_K <= X ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (T' : list byte) (removed : Z),
       ms' = MS (mkR (Z_to_bv 64 0x13528) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3' s4' s5' s6' (Z_to_bv 64 p) s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x135b8) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 152, X + 160); (X + 512, X + 912)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 152) [C8 (Z_to_bv 64 n)] /\
       rw_cells rsegs m' (X + 176) [C8 (Z_to_bv 64 STALE_NS)] /\
       rw_cells rsegs m' (X + 512) [CB 400 T'] /\
       age_model T now = (T', removed) /\ age_post T now T' removed /\
       tbl_T1 T' /\ tbl_T2 T' /\ tbl_T3 T' /\ tbl_T4 T')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13498) fc None m (seg_rom rsegs)).
Proof.
  intros AGE CHK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo n p now T junk Esp Es3 Es6 Es11 Ea4 HX0 HX16 HX1 Hnow R152 R176 RT T1 T2 T3 T4 MI ST HLO.
  subst sp s3 s6 s11 a4. unfold CHECK_TABLE_K in HLO.
  pose proof (munch_refl [(lo, X); (X + 152, X + 160); (X + 512, X + 912)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply rw_cb in RT. destruct RT as (LT & HT & HW). change (Z.of_nat 400) with 400 in HW.
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (rd_sub _ (X + 512) T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  clear RN.
  assert (MID : forall (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w22 w23 w28 w29 w30 w31 : word)
                       (c : Z),
    c = age_count (fun j => disco_stale T j now) (Z.to_nat (n_of T)) ->
    w20 = Z_to_bv 64 c -> w21 = Z_to_bv 64 (n_of T) -> w23 = Z_to_bv 64 p ->
    evt rsegs QQ (MS (mkR w1 (Z_to_bv 64 X) gp tp w5 w6 w7 s0 s1 w10 w11 w12 w13 w14 w15 w16 w17
                          s2 w19 w20 w21 w22 w23 s8 s9 s10 (Z_to_bv 64 now) w28 w29 w30 w31)
                     F (Z_to_bv 64 0x1350c) fc None m1 (seg_rom rsegs))).
  { intros w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w22 w23 w28 w29 w30 w31 c Hc E20 E21 E23.
    subst w20 w21 w23.
    pose proof (sa_count_range (fun j => disco_stale T j now) (Z.to_nat (n_of T))) as Hcr.
    rewrite <- Hc in Hcr. rewrite Z2Nat.id in Hcr by lia.
    pose proof (rd_sub _ (X + 512) T 392 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RS.
    step.
    rewrite lw_val by (apply length_sub; lia).
    change (bytes_le_to_Z (sub T 392 4)) with (seq_of T).
    clear RS.
    step. step. step.
    eapply evt_cut.
    { eapply AGE with (lo := lo) (t := X + 512) (now := now) (T := T).
      - sa_weq.
      - sa_weq.
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
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    sa_ret 0x1351c.
    pose proof AP as (LT2 & Hrm & Hrr & Hn2 & Hns & Hsq & (U1 & U2 & U3 & U4) & _ & _).
    assert (Hrc : r = c) by (rewrite Hrm, Hc; reflexivity).
    pose proof U1 as U1'. unfold tbl_T1 in U1'.
    step. step. step.
    eapply evt_cut.
    { eapply CHK with (lo := lo) (t := X + 512) (T := T').
      - sa_weq.
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
    sa_ret 0x13528.
    apply rw_cb in RT2. destruct RT2 as (_ & HT2 & HW2).
    assert (FIN : forall (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v21 v22 v23 v28 v29 v30 v31 : word),
      v1 = Z_to_bv 64 0x13528 -> v10 = Z_to_bv 64 (n_of T') -> v11 = Z_to_bv 64 0 ->
      v20 = Z_to_bv 64 c -> v21 = Z_to_bv 64 (n_of T) -> v22 = Z_to_bv 64 (bv_swrap 32 (seq_of T)) ->
      v23 = Z_to_bv 64 p ->
      evt rsegs QQ (MS (mkR v1 (Z_to_bv 64 X) gp tp v5 v6 v7 s0 s1 v10 v11 v12 v13 v14 v15 v16 v17
                            s2 v19 v20 v21 v22 v23 s8 s9 s10 (Z_to_bv 64 now) v28 v29 v30 v31)
                       F (Z_to_bv 64 0x13590) fc None m3 (seg_rom rsegs))).
    { intros v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v21 v22 v23 v28 v29 v30 v31
        E1 E10 E11 E20 E21 E22 E23.
      subst v1 v10 v11 v20 v21 v22 v23.
      replace (n_of T') with (n_of T - c) by lia.
      step.
      rewrite (unsigned_lit (n_of T)), (unsigned_lit c) by lia. rewrite (swrap32_small (n_of T - c)) by lia.
      step.
      rewrite Z.lxor_nilpotent.
      step.
      rewrite ?w0_lit. rewrite sa_sltu by lia.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ (if ?cc then _ else _) _ _ _ _) =>
        replace cc with false by (vm_compute; reflexivity) end.
      cbv iota.
      pose proof (rd_sub _ (X + 512) T' 392 4 HT2 ltac:(lia) ltac:(rewrite LT2; lia)) as RS2.
      step.
      rewrite lw_val by (apply length_sub; lia).
      change (bytes_le_to_Z (sub T' 392 4)) with (seq_of T').
      step.
      rewrite ?w0_lit. rewrite sa_sltu by lia.
      step.
      rewrite Hsq, Hrc.
      rewrite (sa_seq (seq_of T) (0 <? c) (seq_range T)).
      step.
      rewrite sa_eqb_refl. cbn [negb].
      apply evt_done. unfold QQ.
      do 19 eexists. exists m3, T', r.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
      split; [exact R152|]. split; [exact R176|].
      split; [apply rw_cb; split; [exact LT2|]; split; [exact HT2|exact HW2]|].
      split; [exact AM|]. split; [exact AP|].
      exact (conj U1 (conj U2 (conj U3 U4))). }
    assert (L4 : forall (k : nat) (j : Z)
                        (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v21 v22 v23 v28 v29 v30 v31 : word),
      Z.of_nat k = n_of T' - j -> 0 <= j < n_of T' ->
      v1 = Z_to_bv 64 0x13528 -> v10 = Z_to_bv 64 (n_of T') -> v11 = Z_to_bv 64 0 ->
      v12 = Z_to_bv 64 (X + 552 + 48 * n_of T') -> v13 = Z_to_bv 64 (X + 552 + 48 * j) ->
      v16 = Z_to_bv 64 STALE_NS -> v19 = Z_to_bv 64 c ->
      v20 = Z_to_bv 64 c -> v21 = Z_to_bv 64 (n_of T) -> v22 = Z_to_bv 64 (bv_swrap 32 (seq_of T)) ->
      v23 = Z_to_bv 64 p ->
      evt rsegs QQ (MS (mkR v1 (Z_to_bv 64 X) gp tp v5 v6 v7 s0 s1 v10 v11 v12 v13 v14 v15 v16 v17
                            s2 v19 v20 v21 v22 v23 s8 s9 s10 (Z_to_bv 64 now) v28 v29 v30 v31)
                       F (Z_to_bv 64 0x1354c) fc None m3 (seg_rom rsegs))).
    { induction k as [|k IH];
        intros j v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v21 v22 v23 v28 v29 v30 v31
          Hk Hj E1 E10 E11 E12 E13 E16 E19 E20 E21 E22 E23; [lia|].
      subst v1 v10 v11 v12 v13 v16 v19 v20 v21 v22 v23.
      pose proof (rd_sub _ (X + 512) T' (48 * j + 40) 8 HT2 ltac:(lia) ltac:(rewrite LT2; lia)) as RL.
      step.
      rewrite ld_val by (apply length_sub; lia).
      change (bytes_le_to_Z (sub T' (48 * j + 40) 8)) with (last_of T' j).
      clear RL.
      pose proof (last_range T' j LT2 ltac:(lia)) as LR.
      step. step.
      rewrite (sa_sltu (last_of T' j) now) by lia.
      step.
      rewrite (unsigned_lit now), (unsigned_lit (last_of T' j)) by lia.
      step.
      rewrite (sa_sltu_wrap STALE_NS (now - last_of T' j)) by (unfold STALE_NS; lia).
      step.
      rewrite sa_land, (sa_stale T' j now LR Hnow), (Hns j ltac:(lia)).
      step.
      step.
      rewrite eqb_lit by lia.
      match goal with |- context [?u =? ?v] => destruct (Z.eqb_spec u v) as [Ee|Ee] end; cbn [negb].
      - step. step.
        rewrite sa_eqb_refl. cbn [negb].
        step.
        eapply FIN; sa_weq.
      - eapply (IH (j + 1)); try sa_weq; lia. }
    pose proof (rd_sub _ (X + 512) T' 384 4 HT2 ltac:(lia) ltac:(rewrite LT2; lia)) as RN2.
    step.
    rewrite lw_val by (apply length_sub; lia).
    change (bv_swrap 32 (bytes_le_to_Z (sub T' 384 4))) with (n_of T') in *.
    clear RN2.
    step.
    rewrite lts_lit by lia.
    destruct (Z.ltb_spec 0 (n_of T')) as [Hn'|Hn']; cbn [negb].
    - step. step. step. step.
      rewrite mul48_lit by lia.
      step. step. step.
      eapply (L4 (Z.to_nat (n_of T')) 0); sa_weq.
    - step. step.
      rewrite eqb_lit by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia. cbn [negb].
      eapply FIN; sa_weq. }
  assert (L3 : forall (k : nat) (j c : Z)
                      (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w22 w23 w28 w29 w30 w31 : word),
    Z.of_nat k = n_of T - j -> 0 <= j < n_of T -> c = age_count (fun j => disco_stale T j now) (Z.to_nat j) ->
    w10 = Z_to_bv 64 (X + 552 + 48 * n_of T) -> w11 = Z_to_bv 64 (X + 552 + 48 * j) ->
    w14 = Z_to_bv 64 STALE_NS -> w20 = Z_to_bv 64 c -> w21 = Z_to_bv 64 (n_of T) -> w23 = Z_to_bv 64 p ->
    evt rsegs QQ (MS (mkR w1 (Z_to_bv 64 X) gp tp w5 w6 w7 s0 s1 w10 w11 w12 w13 w14 w15 w16 w17
                          s2 w19 w20 w21 w22 w23 s8 s9 s10 (Z_to_bv 64 now) w28 w29 w30 w31)
                     F (Z_to_bv 64 0x134c0) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH];
      intros j c w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w20 w21 w22 w23 w28 w29 w30 w31
        Hk Hj Hc E10 E11 E14 E20 E21 E23; [lia|].
    subst w10 w11 w14 w20 w21 w23.
    pose proof (sa_count_range (fun j => disco_stale T j now) (Z.to_nat j)) as Hcr.
    rewrite <- Hc in Hcr. rewrite Z2Nat.id in Hcr by lia.
    pose proof (rd_sub _ (X + 512) T (48 * j + 40) 8 HT ltac:(lia) ltac:(rewrite LT; lia)) as RL.
    step.
    rewrite ld_val by (apply length_sub; lia).
    change (bytes_le_to_Z (sub T (48 * j + 40) 8)) with (last_of T j).
    clear RL.
    pose proof (last_range T j LT ltac:(lia)) as LR.
    step. step.
    rewrite (sa_sltu (last_of T j) now) by lia.
    step.
    rewrite (unsigned_lit now), (unsigned_lit (last_of T j)) by lia.
    step.
    rewrite (sa_sltu_wrap STALE_NS (now - last_of T j)) by (unfold STALE_NS; lia).
    step.
    rewrite sa_land, (sa_stale T j now LR Hnow).
    step.
    rewrite (sa_addw c) by lia.
    step.
    rewrite eqb_lit by lia.
    match goal with |- context [?u =? ?v] => destruct (Z.eqb_spec u v) as [Ee|Ee] end; cbn [negb].
    - step.
      eapply (MID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c + Z.b2z (disco_stale T j now))); try sa_weq.
      rewrite Hc. replace (n_of T) with (j + 1) by lia. rewrite sa_count by lia. reflexivity.
    - eapply (IH (j + 1) (c + Z.b2z (disco_stale T j now))); try sa_weq; try lia.
      rewrite Hc. rewrite sa_count by lia. reflexivity. }
  step.
  rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 (n_of T)) as [Hn|Hn]; cbn [negb].
  - step. step. step. step. step.
    rewrite mul48_lit by lia.
    step. step.
    eapply (L3 (Z.to_nat (n_of T)) 0 0); try sa_weq; lia.
  - step. step.
    eapply (MID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0); try sa_weq.
    replace (Z.to_nat (n_of T)) with O by lia. reflexivity.
Qed.

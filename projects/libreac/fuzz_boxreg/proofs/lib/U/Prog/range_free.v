From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg range_free_c.
Import ListNotations.
Open Scope Z_scope.

Lemma slt_t : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> a < b ->
  v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros a b Ha Hb H. unfold v_slt, c_lts. rewrite lts_lit by lia.
  replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma slt_f : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
  v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb H. unfold v_slt, c_lts. rewrite lts_lit by lia.
  replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma land_m1 : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma land3 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Section RF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t base nch fabric : Z) (bs : list byte).
  Hypothesis Hbase : -2^31 <= base < 2^31.
  Hypothesis Hnch : 1 <= nch <= 40.
  Hypothesis Hfab : 1 <= fabric <= 40.
  Hypothesis HB : bytes_at rsegs m t bs.
  Hypothesis HL : length bs = 288%nat.
  Hypothesis H1 : boxreg_B1 bs.
  Hypothesis H2 : boxreg_B2 bs.
  Hypothesis H3 : boxreg_B3 bs.
  Hypothesis HA : t mod 4 = 0.

  Notation POST := (fun ms' : machine_state => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         ((r = Z_to_bv 64 1 /\ range_free_ok bs base nch fabric) \/
          (r = Z_to_bv 64 0 /\ ~ range_free_ok bs base nch fabric))).
  Notation ST pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma Tb : 0 <= t /\ t + 288 <= 2^64.
  Proof. pose proof (bytes_at_bound rsegs m t bs HB) as R. rewrite HL in R. exact R. Qed.

  Lemma ret0 : forall x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28, ~ range_free_ok bs base nch fabric ->
    evt rsegs POST (ST 0x138e4 x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 0) x15 x16 x17 x28).
  Proof.
    intros x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28 N. step. step.
    apply evt_done. do 15 eexists. split; [reflexivity|]. right. split; [reflexivity|exact N].
  Qed.

  Lemma ret1 : forall x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28, range_free_ok bs base nch fabric ->
    evt rsegs POST (ST 0x138e4 x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 1) x15 x16 x17 x28).
  Proof.
    intros x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28 OK. step. step.
    apply evt_done. do 15 eexists. split; [reflexivity|]. left. split; [reflexivity|exact OK].
  Qed.

  Lemma exit : forall i x5 x6 x7 x10 x11 x12 x15 x16 x17 x28, 0 <= i <= bx_n bs ->
    (i < bx_n bs -> ~ range_free_ok bs base nch fabric) -> (i = bx_n bs -> range_free_ok bs base nch fabric) ->
    evt rsegs POST (ST 0x138dc x5 x6 x7 x10 x11 x12 (Z_to_bv 64 (bx_n bs)) (Z_to_bv 64 i) x15 x16 x17 x28).
  Proof.
    unfold boxreg_B1 in H1.
    intros i x5 x6 x7 x10 x11 x12 x15 x16 x17 x28 Hi N OK. step.
    destruct (Z_lt_le_dec i (bx_n bs)) as [Lt|Ge].
    - rewrite slt_t by lia. step. apply ret0. exact (N Lt).
    - rewrite slt_f by lia. step. apply ret1. apply OK. lia.
  Qed.

  Lemma loop : forall k i x6 x7 x28,
    Z.of_nat k = bx_n bs - i -> 0 <= i < bx_n bs -> 0 <= base <= fabric - nch ->
    (forall j, 0 <= j < i -> ~ meets base nch (bx_base bs j) (bx_nch bs j)) ->
    evt rsegs POST (ST 0x1389c (Z_to_bv 64 5) x6 x7 (Z_to_bv 64 (t + 12 + 56 * i)) (Z_to_bv 64 base)
                       (Z_to_bv 64 (nch + base)) (Z_to_bv 64 (bx_n bs)) (Z_to_bv 64 i) (Z_to_bv 64 (56 * i))
                       (Z_to_bv 64 (18446744073709551615 - t)) (Z_to_bv 64 (bx_n bs)) x28).
  Proof.
    pose proof Tb as TB. unfold boxreg_B1 in H1.
    induction k as [|k IH]; intros i x6 x7 x28 Hk Hi Hr P; [lia|].
    destruct (B3_bounds bs i H2 H3 Hi) as (Bb & Bn & Be).
    pose proof (rd4_read m t bs (56 * i + 8) HB ltac:(lia) ltac:(rewrite HL; lia)) as RB.
    pose proof (rd4_read m t bs (56 * i + 12) HB ltac:(lia) ltac:(rewrite HL; lia)) as RN.
    step.
    rewrite eqb_lit by lia.
    destruct (Z.eqb_spec i 5) as [E5|N5]; [lia|].
    step.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (18446744073709551615 - t) (56 * i)) as [Ov|Nov]; [lia|].
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_base bs i).
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_nch bs i).
    step.
    step.
    rewrite swrap_add by lia.
    step.
    rewrite eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb].
    step.
    rewrite swrap_addi by lia.
    replace (bx_base bs i + bx_nch bs i + 0) with (bx_base bs i + bx_nch bs i) by lia.
    step.
    rewrite lts_lit by lia.
    assert (NEXT : forall y6 y7 y28, ~ meets base nch (bx_base bs i) (bx_nch bs i) ->
      evt rsegs POST (ST 0x138c4 (Z_to_bv 64 5) y6 y7 (Z_to_bv 64 (t + 12 + 56 * i)) (Z_to_bv 64 base)
                         (Z_to_bv 64 (nch + base)) (Z_to_bv 64 (bx_n bs)) (Z_to_bv 64 i) (Z_to_bv 64 (56 * i))
                         (Z_to_bv 64 (18446744073709551615 - t)) (Z_to_bv 64 (bx_n bs)) y28)).
    { intros y6 y7 y28 NM. step. step. step.
      step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (bx_n bs) (i + 1)) as [Z0|Z1].
      - cbn [negb]. step. apply (exit (i + 1)); [lia| |].
        + intros L. lia.
        + intros _. split; [exact Hr|]. intros j Hj.
          destruct (Z.eq_dec j i) as [->|NE]; [exact NM|]. apply P. lia.
      - cbn [negb].
        replace (t + 12 + 56 * i + 56) with (t + 12 + 56 * (i + 1)) by lia.
        replace (56 * i + 56) with (56 * (i + 1)) by lia.
        apply (IH (i + 1)); try lia.
        intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [exact NM|]. apply P. lia. }
    destruct (Z.ltb_spec base (bx_base bs i + bx_nch bs i)) as [Lt|Ge].
    - cbn [negb]. step. rewrite lts_lit by lia.
      destruct (Z.ltb_spec (bx_base bs i) (nch + base)) as [Lt2|Ge2].
      + apply (exit i); [lia| |].
        * intros _ [_ OK]. apply (OK i Hi). unfold meets. lia.
        * intros E. lia.
      + apply NEXT. unfold meets. lia.
    - cbn [negb]. apply NEXT. unfold meets. lia.
  Qed.

  Lemma entry : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3, a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 base ->
    a2 = Z_to_bv 64 nch -> a3 = Z_to_bv 64 fabric ->
    evt rsegs POST (ST 0x13858 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3).
  Proof.
    intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 -> -> -> ->.
    pose proof Tb as TB. unfold boxreg_B1 in H1.
    step. step.
    rewrite lts_lit by lia.
    destruct (Z.ltb_spec base 0) as [Hn|Hp].
    - apply ret0. intros [Hr _]. lia.
    - step.
      rewrite swrap_sub by lia.
      step.
      rewrite lts_lit by lia.
      destruct (Z.ltb_spec (fabric - nch) base) as [Hg|Hl].
      + apply ret0. intros [Hr _]. lia.
      + step.
        rewrite (unsigned_lit t) by lia. rewrite (land3 t HA).
        step. if_false.
        pose proof (rd4_read m t bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as RN.
        step.
        rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_n bs).
        step.
        rewrite lts_lit by lia.
        destruct (Z.ltb_spec 0 (bx_n bs)) as [Pos|Npos].
        * cbn [negb]. step. step. step.
          rewrite (unsigned_lit t) by lia. rewrite zb_lxor_ones by lia.
          step.
          rewrite swrap_add by lia.
          step.
          rewrite slt_t by lia.
          step. step. step.
          rewrite (unsigned_lit (bx_n bs)) by lia. rewrite land_m1 by lia.
          step.
          replace (t + 12) with (t + 12 + 56 * 0) by lia.
          apply (loop (Z.to_nat (bx_n bs - 0)) 0); try lia.
        * cbn [negb]. step.
          apply (exit 0); [lia| |].
          -- intros L. lia.
          -- intros _. split; [lia|]. intros j Hj. lia.
  Qed.
End RF.

Theorem range_free_holds : range_free_contract.
Proof.
  unfold range_free_contract, RANGE_FREE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         t base nch fabric bs E0 E1 E2 E3 Hb Hn Hf HB HL B1 B2 B3 HA.
  eapply entry; eassumption.
Qed.

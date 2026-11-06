From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcLeaf RcLeafLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT reac_ports_parse_c.
Import ListNotations.
Open Scope Z_scope.

Lemma reac_ports_parse_m8 : forall x i, x mod 4 = 0 -> i mod 4 = 0 -> (x + i) mod 8 + 4 <= 8.
Proof. intros x i Hx Hi. Z.div_mod_to_equations. lia. Qed.

Section Body.
  Variables (ra sp1 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q off : Z) (bs : list byte) (W : list ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hp : 0 < p < 2^64.
  Hypothesis Hq : 0 < q < 2^64.
  Hypothesis Hlen : length bs = 20%nat.
  Hypothesis HB : bytes_at rsegs m p bs.
  Hypothesis Hq4 : q mod 4 = 0.
  Hypothesis HW : wr_at rsegs m q 12.
  Hypothesis Hd : q + 12 <= p \/ p + 20 <= q.
  Hypothesis HWq : sub_fp [(q, q + 12)] W.
  Hypothesis HRT : asan_rt rsegs m GOT_CELL_K CELL_K off W.
  Hypothesis HSRp : asan_shadow_rd rsegs m off p 20 W.
  Hypothesis HSRq : asan_shadow_rd rsegs m off q 12 W.
  Hypothesis HADp : asan_addressable rsegs m off p 20.
  Hypothesis HADq : asan_addressable rsegs m off q 12.

  Abbreviation ST pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 mm :=
    (MS (mkR ra sp1 gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Hypothesis FIN_FAIL : ports_ok p q bs = false -> forall x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29,
    evt rsegs Q (ST 0x885a0 x5 x6 x7 x10 x11 (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 x28 x29 m).
  Hypothesis FIN_OK : ports_ok p q bs = true -> forall x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 mm,
    munch [(q, q + 12)] m mm -> wmono rsegs m mm -> (mem_inv rsegs m -> mem_inv rsegs mm) ->
    (forall lo hi, stk rsegs m lo hi -> stk rsegs mm lo hi) ->
    bytes_at rsegs mm q (le4 (Z_to_bv 64 (4 * n_in bs))) ->
    bytes_at rsegs mm (q + 4) (le4 (Z_to_bv 64 (4 * n_out bs))) ->
    bytes_at rsegs mm (q + 8) (le4 (Z_to_bv 64 (16 * bt bs 7))) ->
    evt rsegs Q (ST 0x885a0 x5 x6 x7 x10 x11 (Z_to_bv 64 0) x13 x14 x15 x16 x17 x28 x29 mm).

  Lemma reac_ports_parse_tail : ports_ok p q bs = true -> forall x5 x6 x7 x12 x16 x17 x28 x29,
    evt rsegs Q (ST 0x88504 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q) x12 (Z_to_bv 64 (n_out bs)) (Z_to_bv 64 off)
                    (Z_to_bv 64 (n_in bs)) x16 x17 x28 x29 m).
  Proof using Hp Hq Hlen HB Hq4 HW Hd HWq HSRp HSRq HADp HADq FIN_OK.
    intros Hok x5 x6 x7 x12 x16 x17 x28 x29.
    pose proof (rcl_cnt_range is_in bs 12) as RI. pose proof (rcl_cnt_range is_out bs 12) as RO.
    change (cnt is_in bs 12) with (n_in bs) in RI. change (cnt is_out bs 12) with (n_out bs) in RO.
    change (Z.of_nat 12) with 12 in RI, RO.
    pose proof HW as (HWl & HWh & _). pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
    step. step. step. step. rc_small (n_in bs).
    step. step. rewrite (unsigned_lit q) by lia. rewrite rcl_land3, Hq4. rc_false.
    destruct (asan_shadow_read_at rsegs m off q 12 W 0 (q / 8 + off) HSRq ltac:(lia)
                ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k1 & RK1 & BK1).
    pose proof (asan_check_lt rsegs m off q 12 0 4 k1 HADq ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(apply reac_ports_parse_m8; [exact Hq4 | reflexivity]) BK1) as OK1.
    rewrite Z.add_0_r in OK1.
    pose proof (rc_byte_signed k1) as KR1. clear BK1.
    step.
    rewrite (unsigned_lit q) by lia. rewrite rc_shr3.
    step. step. clear RK1. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k1)) by lia.
    enough (K1 : forall y12 y16, evt rsegs Q (ST 0x8852c x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q) y12
                   (Z_to_bv 64 (n_out bs)) (Z_to_bv 64 off) (Z_to_bv 64 (n_in bs)) y16 x17 x28 x29 m)).
    { destruct (Z.eqb_spec (bv_signed k1) 0) as [E|E]; cbn [negb]; [apply K1|].
      step. rewrite (unsigned_lit q) by lia. rewrite rc_land7.
      step. step.
      rewrite (rc_lts_signed (q mod 8 + 3) (bv_signed k1))
        by (pose proof (Z.mod_pos_bound q 8 ltac:(lia)); lia).
      replace (q mod 8 + 3 <? bv_signed k1) with true by (symmetry; apply Z.ltb_lt; lia).
      apply K1. }
    intros y12 y16.
    pose proof (rcl_store_ok rsegs m q 12 4 HW ltac:(lia)) as ST0.
    step.
    rewrite (unsigned_lit (n_in bs)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (n_in bs * 2^2) with (4 * n_in bs) by lia.
    step. step. step. step. step.
    rc_small (n_out bs).
    remember (write_to_mem m (Z_to_bv 64 q) (le4 (Z_to_bv 64 (4 * n_in bs)))) as m2 eqn:E2.
    assert (MU2 : munch [(q, q + 12)] m m2)
      by (rewrite E2; apply munch_write; [apply munch_refl | lia | rewrite ?length_le4; lia
                                           | cbn [inside]; rewrite ?length_le4; lia]).
    assert (WM2 : wmono rsegs m m2) by (rewrite E2; apply wmono_write, wmono_refl).
    assert (MI2 : mem_inv rsegs m -> mem_inv rsegs m2)
      by (intros HI; rewrite E2; apply mem_inv_store; [exact HI | rewrite length_le4; exact ST0]).
    assert (SK2 : forall lo hi, stk rsegs m lo hi -> stk rsegs m2 lo hi)
      by (intros lo hi H; rewrite E2; apply stk_write; [exact H | lia | rewrite ?length_le4; lia]).
    assert (HW2 : wr_at rsegs m2 q 12) by (rewrite E2; apply wr_at_write; exact HW).
    assert (HB2 : bytes_at rsegs m2 p bs)
      by (rewrite E2; apply bytes_at_write_other;
          [exact HB | lia | rewrite ?length_le4; lia | rewrite ?length_le4, Hlen; lia]).
    assert (BQ0 : bytes_at rsegs m2 q (le4 (Z_to_bv 64 (4 * n_in bs))))
      by (rewrite E2; apply bytes_at_write_same; rewrite ?length_le4; lia).
    clear E2 ST0.
    step. step.
    rewrite (unsigned_lit (q + 4)) by lia. rewrite rc_shr3.
    step.
    pose proof (asan_shadow_rd_munch rsegs m m2 off q 12 W _ HSRq MU2 HWq) as HSRq2.
    pose proof (asan_addressable_munch rsegs m m2 off q 12 W _ HADq HSRq MU2 HWq) as HADq2.
    destruct (asan_shadow_read_at rsegs m2 off q 12 W 4 ((q + 4) / 8 + off) HSRq2 ltac:(lia) eq_refl)
      as (k2 & RK2 & BK2).
    pose proof (asan_check_lt rsegs m2 off q 12 4 4 k2 HADq2 ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(apply reac_ports_parse_m8; [exact Hq4 | reflexivity]) BK2) as OK2.
    pose proof (rc_byte_signed k2) as KR2. clear BK2 HSRq2 HADq2.
    step. clear RK2. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k2)) by lia.
    enough (K2 : forall z15 z16, evt rsegs Q (ST 0x88558 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q)
                   (Z_to_bv 64 (q + 4)) (Z_to_bv 64 (n_out bs)) (Z_to_bv 64 off) z15 z16 x17 x28 x29 m2)).
    { destruct (Z.eqb_spec (bv_signed k2) 0) as [E|E]; cbn [negb]; [apply K2|].
      step. rewrite (unsigned_lit (q + 4)) by lia. rewrite rc_land7.
      step. step.
      rewrite (rc_lts_signed ((q + 4) mod 8 + 3) (bv_signed k2))
        by (pose proof (Z.mod_pos_bound (q + 4) 8 ltac:(lia)); lia).
      replace ((q + 4) mod 8 + 3 <? bv_signed k2) with true by (symmetry; apply Z.ltb_lt; lia).
      apply K2. }
    intros z15 z16.
    pose proof (wr_at_store_ok rsegs m2 q 12 4 4 HW2 ltac:(lia) ltac:(lia)) as ST1.
    step.
    rewrite (unsigned_lit (n_out bs)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (n_out bs * 2^2) with (4 * n_out bs) by lia.
    step. step. step.
    rc_false.
    remember (write_to_mem m2 (Z_to_bv 64 (q + 4)) (le4 (Z_to_bv 64 (4 * n_out bs)))) as m3 eqn:E3.
    assert (MU3 : munch [(q, q + 12)] m m3)
      by (rewrite E3; apply munch_write; [exact MU2 | lia | rewrite ?length_le4; lia
                                           | cbn [inside]; rewrite ?length_le4; lia]).
    assert (WM3 : wmono rsegs m m3) by (rewrite E3; apply wmono_write; exact WM2).
    assert (MI3 : mem_inv rsegs m -> mem_inv rsegs m3)
      by (intros HI; rewrite E3; apply mem_inv_store; [exact (MI2 HI) | rewrite length_le4; exact ST1]).
    assert (SK3 : forall lo hi, stk rsegs m lo hi -> stk rsegs m3 lo hi)
      by (intros lo hi H; rewrite E3; apply stk_write; [exact (SK2 lo hi H) | lia | rewrite ?length_le4; lia]).
    assert (HW3 : wr_at rsegs m3 q 12) by (rewrite E3; apply wr_at_write; exact HW2).
    assert (HB3 : bytes_at rsegs m3 p bs)
      by (rewrite E3; apply bytes_at_write_other;
          [exact HB2 | lia | rewrite ?length_le4; lia | rewrite ?length_le4, Hlen; lia]).
    assert (BQ0' : bytes_at rsegs m3 q (le4 (Z_to_bv 64 (4 * n_in bs))))
      by (rewrite E3; apply bytes_at_write_other;
          [exact BQ0 | lia | rewrite ?length_le4; lia | rewrite ?length_le4; lia]).
    assert (BQ4 : bytes_at rsegs m3 (q + 4) (le4 (Z_to_bv 64 (4 * n_out bs))))
      by (rewrite E3; apply bytes_at_write_same; rewrite ?length_le4; lia).
    clear E3 ST1 MU2 WM2 MI2 SK2 HW2 HB2 BQ0.
    step. step.
    rewrite (unsigned_lit (p + 7)) by lia. rewrite rc_shr3.
    step.
    pose proof (asan_shadow_rd_munch rsegs m m3 off p 20 W _ HSRp MU3 HWq) as HSRp3.
    pose proof (asan_addressable_munch rsegs m m3 off p 20 W _ HADp HSRp MU3 HWq) as HADp3.
    destruct (asan_shadow_read_at rsegs m3 off p 20 W 7 ((p + 7) / 8 + off) HSRp3 ltac:(lia) eq_refl)
      as (k3 & RK3 & BK3).
    pose proof (HADp3 7 k3 ltac:(lia) BK3) as OK3. unfold asan_ok in OK3.
    pose proof (rc_byte_signed k3) as KR3. clear BK3 HSRp3 HADp3.
    step. clear RK3. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k3)) by lia.
    enough (K3 : forall v12 v13 v15, evt rsegs Q (ST 0x8857c x5 x6 x7 (Z_to_bv 64 (p + 7)) (Z_to_bv 64 q) v12 v13
                   (Z_to_bv 64 off) v15 z16 x17 x28 x29 m3)).
    { destruct (Z.eqb_spec (bv_signed k3) 0) as [E|E]; cbn [negb]; [apply K3|].
      step. rewrite (unsigned_lit (p + 7)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 7) mod 8) (bv_signed k3))
        by (pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)); lia).
      replace ((p + 7) mod 8 <? bv_signed k3) with true by (symmetry; apply Z.ltb_lt; lia).
      apply K3. }
    intros v12 v13 v15.
    pose proof (rd_byte rsegs m3 p bs 7 HB3 ltac:(lia)) as R7.
    pose proof (byte_range (nth 7 bs (Z_to_bv 8 0))) as B7.
    step. step.
    rewrite (unsigned_lit (q + 8)) by lia. rewrite rc_shr3.
    step.
    pose proof (asan_shadow_rd_munch rsegs m m3 off q 12 W _ HSRq MU3 HWq) as HSRq3.
    pose proof (asan_addressable_munch rsegs m m3 off q 12 W _ HADq HSRq MU3 HWq) as HADq3.
    destruct (asan_shadow_read_at rsegs m3 off q 12 W 8 ((q + 8) / 8 + off) HSRq3 ltac:(lia) eq_refl)
      as (k4 & RK4 & BK4).
    pose proof (asan_check_lt rsegs m3 off q 12 8 4 k4 HADq3 ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(apply reac_ports_parse_m8; [exact Hq4 | reflexivity]) BK4) as OK4.
    pose proof (rc_byte_signed k4) as KR4. clear BK4 HSRq3 HADq3.
    step. clear RK4. step. clear R7. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k4)) by lia.
    enough (K4 : forall w12 w13, evt rsegs Q (ST 0x88594 x5 x6 x7 (zxb (nth 7 bs (Z_to_bv 8 0)))
                   (Z_to_bv 64 (q + 8)) w12 w13 (Z_to_bv 64 off) v15 z16 x17 x28 x29 m3)).
    { destruct (Z.eqb_spec (bv_signed k4) 0) as [E|E]; cbn [negb]; [apply K4|].
      step. rewrite (unsigned_lit (q + 8)) by lia. rewrite rc_land7.
      step. step.
      rewrite (rc_lts_signed ((q + 8) mod 8 + 3) (bv_signed k4))
        by (pose proof (Z.mod_pos_bound (q + 8) 8 ltac:(lia)); lia).
      replace ((q + 8) mod 8 + 3 <? bv_signed k4) with true by (symmetry; apply Z.ltb_lt; lia).
      apply K4. }
    intros w12 w13.
    pose proof (wr_at_store_ok rsegs m3 q 12 8 4 HW3 ltac:(lia) ltac:(lia)) as ST2.
    step. step.
    unfold zxb. rewrite (unsigned_lit (bv_unsigned (nth 7 bs (Z_to_bv 8 0)))) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    change (bv_unsigned (nth 7 bs (Z_to_bv 8 0))) with (bt bs 7) in *.
    replace (bt bs 7 * 2^4) with (16 * bt bs 7) by lia.
    step.
    change (Z_to_bv 64 (q + 8)) with (wa (q + 8)).
    eapply (FIN_OK Hok).
    - apply munch_write; [exact MU3 | lia | rewrite ?length_le4; lia | cbn [inside]; rewrite ?length_le4; lia].
    - apply wmono_write; exact WM3.
    - intros HI. apply mem_inv_store; [exact (MI3 HI) | rewrite length_le4; exact ST2].
    - intros lo hi H. apply stk_write; [exact (SK3 lo hi H) | lia | rewrite ?length_le4; lia].
    - apply bytes_at_write_other; [exact BQ0' | lia | rewrite ?length_le4; lia | rewrite ?length_le4; lia].
    - apply bytes_at_write_other; [exact BQ4 | lia | rewrite ?length_le4; lia | rewrite ?length_le4; lia].
    - apply bytes_at_write_same; rewrite ?length_le4; lia.
  Qed.

  Lemma reac_ports_parse_loop : ports_ok p q bs = true -> forall n i x28 x29,
    (i + n = 12)%nat -> (0 < n)%nat ->
    evt rsegs Q (ST 0x8849c (Z_to_bv 64 2) (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 p)
                    (Z_to_bv 64 q) (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 (cnt is_out bs i))
                    (Z_to_bv 64 off) (Z_to_bv 64 (cnt is_in bs i)) (Z_to_bv 64 (p + 8 + Z.of_nat i))
                    (Z_to_bv 64 (12 - Z.of_nat i)) x28 x29 m).
  Proof using Hp Hq Hlen HB Hq4 HW Hd HWq HSRp HSRq HADp HADq FIN_OK.
    intros Hok. pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
    induction n as [|n IH]; intros i x28 x29 Hin Hn; [lia|].
    pose proof (rcl_cnt_range is_in bs i) as RI. pose proof (rcl_cnt_range is_out bs i) as RO.
    assert (K : forall y28 y29, evt rsegs Q
      (ST 0x884dc (Z_to_bv 64 2) (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 p) (Z_to_bv 64 q)
          (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 (cnt is_out bs (S i))) (Z_to_bv 64 off)
          (Z_to_bv 64 (cnt is_in bs (S i))) (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 (12 - Z.of_nat i))
          y28 y29 m)).
    { intros y28 y29. step. step. step. step. step.
      rewrite (rcl_eqb (12 - Z.of_nat i + -1) 0) by lia.
      destruct n as [|n].
      - replace (12 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. step.
        replace i with 11%nat in * by lia.
        exact (reac_ports_parse_tail Hok _ _ _ _ _ _ _ _).
      - replace (12 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (12 - Z.of_nat i + -1) with (12 - Z.of_nat (S i)) by lia.
        replace (p + 8 + Z.of_nat i + 1) with (p + 8 + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    assert (BODY : forall y28 y29, evt rsegs Q
      (ST 0x884b0 (Z_to_bv 64 2) (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 p) (Z_to_bv 64 q)
          (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 (cnt is_out bs i)) (Z_to_bv 64 off)
          (Z_to_bv 64 (cnt is_in bs i)) (Z_to_bv 64 (p + 8 + Z.of_nat i)) (Z_to_bv 64 (12 - Z.of_nat i))
          y28 y29 m)).
    { intros y28 y29.
      pose proof (rd_byte rsegs m p bs (8 + i) HB ltac:(lia)) as RD.
      pose proof (byte_range (nth (8 + i) bs (Z_to_bv 8 0))) as BC.
      step. step.
      rewrite (rcl_zxb_eqb _ 2) by lia.
      change (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) with (bt bs (8 + i)) in *.
      destruct (Z.eqb_spec (bt bs (8 + i)) 2) as [C2|C2]; cbn [negb].
      - assert (IN : is_in (bt bs (8 + i)) = true) by (unfold is_in; rewrite C2; reflexivity).
        assert (OUT : is_out (bt bs (8 + i)) = false) by (unfold is_out; rewrite C2; reflexivity).
        step. step.
        rewrite (rcl_addiw (cnt is_in bs i)) by lia. rewrite (rcl_blt1 (cnt is_in bs i)) by lia. cbn [negb].
        step. step.
        replace (cnt is_in bs i + 1) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; reflexivity).
        replace (cnt is_out bs i) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; lia).
        apply K.
      - step.
        rewrite (rcl_zxb_eqb _ 1) by lia.
        change (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) with (bt bs (8 + i)).
        destruct (Z.eqb_spec (bt bs (8 + i)) 1) as [C1|C1]; cbn [negb].
        + assert (IN : is_in (bt bs (8 + i)) = false) by (unfold is_in; rewrite C1; reflexivity).
          assert (OUT : is_out (bt bs (8 + i)) = true) by (unfold is_out; rewrite C1; reflexivity).
          step. step.
          rewrite (rcl_addiw (cnt is_out bs i)) by lia. rewrite (rcl_blt1 (cnt is_out bs i)) by lia. cbn [negb].
          step.
          replace (cnt is_out bs i + 1) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; reflexivity).
          replace (cnt is_in bs i) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; lia).
          apply K.
        + step.
          rewrite (rcl_zxb_eqb _ 0) by lia.
          change (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) with (bt bs (8 + i)).
          destruct (Z.eqb_spec (bt bs (8 + i)) 0) as [C0|C0]; cbn [negb].
          * assert (IN : is_in (bt bs (8 + i)) = true) by (unfold is_in; rewrite C0; reflexivity).
            assert (OUT : is_out (bt bs (8 + i)) = false) by (unfold is_out; rewrite C0; reflexivity).
            step. step.
            rewrite (rcl_addiw (cnt is_in bs i)) by lia. rewrite (rcl_blt1 (cnt is_in bs i)) by lia. cbn [negb].
            step. step.
            replace (cnt is_in bs i + 1) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; reflexivity).
            replace (cnt is_out bs i) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; lia).
            apply K.
          * assert (IN : is_in (bt bs (8 + i)) = false)
              by (unfold is_in; rewrite (proj2 (Z.eqb_neq _ _) C0), (proj2 (Z.eqb_neq _ _) C2); reflexivity).
            assert (OUT : is_out (bt bs (8 + i)) = false) by (unfold is_out; apply Z.eqb_neq; exact C1).
            replace (cnt is_in bs i) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; lia).
            replace (cnt is_out bs i) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; lia).
            apply K. }
    step. rc_false.
    destruct (asan_shadow_read_at rsegs m off p 20 W (8 + Z.of_nat i) ((p + 8 + Z.of_nat i) / 8 + off) HSRp
                ltac:(lia) ltac:(unfold asan_shadow; replace (p + (8 + Z.of_nat i)) with (p + 8 + Z.of_nat i) by lia;
                                 reflexivity)) as (k & RK & BK).
    pose proof (HADp (8 + Z.of_nat i) k ltac:(lia) BK) as OK. unfold asan_ok in OK.
    replace (p + (8 + Z.of_nat i)) with (p + 8 + Z.of_nat i) in OK by lia.
    pose proof (rc_byte_signed k) as KR. clear BK.
    step. rewrite (unsigned_lit (p + 8 + Z.of_nat i)) by lia. rewrite rc_shr3.
    step. step. clear RK. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [E|E]; cbn [negb]; [apply BODY|].
    step. rewrite (unsigned_lit (p + 8 + Z.of_nat i)) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed ((p + 8 + Z.of_nat i) mod 8) (bv_signed k))
      by (pose proof (Z.mod_pos_bound (p + 8 + Z.of_nat i) 8 ltac:(lia)); lia).
    replace ((p + 8 + Z.of_nat i) mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; lia).
    apply BODY.
  Qed.

  Lemma reac_ports_parse_accept : ports_ok p q bs = true -> forall x5 x6 x7 x12 x13 x15 x16 x17 x28 x29,
    evt rsegs Q (ST 0x88474 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q) x12 x13 (Z_to_bv 64 off) x15 x16 x17 x28 x29 m).
  Proof using Hp Hq Hlen HB Hq4 HW Hd HWq HSRp HSRq HADp HADq FIN_OK.
    intros Hok x5 x6 x7 x12 x13 x15 x16 x17 x28 x29.
    pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
    step. step. step. step. step. step. step. step. step. step.
    rewrite (rcl_a7 p) by lia.
    replace (p + 8) with (p + 8 + Z.of_nat 0) by lia.
    exact (reac_ports_parse_loop Hok 12 0 _ _ eq_refl ltac:(lia)).
  Qed.

  Lemma reac_ports_parse_entry : forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29,
    evt rsegs Q (ST 0x883e4 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 x28 x29 m).
  Proof using Hp Hq Hlen HB Hq4 HW Hd HWq HRT HSRp HSRq HADp HADq FIN_FAIL FIN_OK.
    intros x5 x6 x7 x13 x14 x15 x16 x17 x28 x29.
    pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
    assert (Pf : (p =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (Qf : (q =? 0) = false) by (apply Z.eqb_neq; lia).
    pose proof (asan_rt_got_read rsegs m _ _ off _ HRT) as RG.
    pose proof (asan_rt_cell_read rsegs m _ _ off _ HRT) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    step. step. step. clear RG RC.
    step. rewrite (unsigned_lit p) by lia. rewrite rc_shr3.
    step.
    destruct (asan_shadow_read_at rsegs m off p 20 W 0 (p / 8 + off) HSRp ltac:(lia)
                ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k0 & RK0 & BK0).
    pose proof (HADp 0 k0 ltac:(lia) BK0) as OK0. unfold asan_ok in OK0. rewrite Z.add_0_r in OK0.
    pose proof (rc_byte_signed k0) as KR0. clear BK0.
    step. clear RK0. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k0)) by lia.
    enough (M1 : forall y13 y15, evt rsegs Q (ST 0x88400 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (-1))
                   y13 (Z_to_bv 64 off) y15 x16 x17 x28 x29 m)).
    { destruct (Z.eqb_spec (bv_signed k0) 0) as [E|E]; cbn [negb]; [apply M1|].
      step. rewrite (unsigned_lit p) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed (p mod 8) (bv_signed k0)) by (pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
      replace (p mod 8 <? bv_signed k0) with true by (symmetry; apply Z.ltb_lt; lia).
      apply M1. }
    intros y13 y15.
    pose proof (rd_byte rsegs m p bs 0 HB ltac:(lia)) as R0.
    pose proof (byte_range (nth 0 bs (Z_to_bv 8 0))) as B0.
    step. clear R0. step. step.
    rewrite (rcl_zxb_eqb _ 1) by lia.
    change (bv_unsigned (nth 0 bs (Z_to_bv 8 0))) with (bt bs 0) in *.
    destruct (Z.eqb_spec (bt bs 0) 1) as [E0|E0]; cbn [negb].
    2: { apply FIN_FAIL. unfold ports_ok, decl. rewrite Pf, Qf, (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
    step. step. rc_false.
    step. step. rewrite (unsigned_lit (p + 1)) by lia. rewrite rc_shr3. step.
    destruct (asan_shadow_read_at rsegs m off p 20 W 1 ((p + 1) / 8 + off) HSRp ltac:(lia) eq_refl)
      as (k1 & RK1 & BK1).
    pose proof (HADp 1 k1 ltac:(lia) BK1) as OK1. unfold asan_ok in OK1.
    pose proof (rc_byte_signed k1) as KR1. clear BK1.
    step. clear RK1. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k1)) by lia.
    enough (M2 : forall y13 y15, evt rsegs Q (ST 0x88428 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q)
                   (Z_to_bv 64 (p + 1)) y13 (Z_to_bv 64 off) y15 x16 x17 x28 x29 m)).
    { destruct (Z.eqb_spec (bv_signed k1) 0) as [E|E]; cbn [negb]; [apply M2|].
      step. rewrite (unsigned_lit (p + 1)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 1) mod 8) (bv_signed k1))
        by (pose proof (Z.mod_pos_bound (p + 1) 8 ltac:(lia)); lia).
      replace ((p + 1) mod 8 <? bv_signed k1) with true by (symmetry; apply Z.ltb_lt; lia).
      apply M2. }
    intros z13 z15.
    pose proof (rd_byte rsegs m p bs 1 HB ltac:(lia)) as R1.
    pose proof (byte_range (nth 1 bs (Z_to_bv 8 0))) as B1.
    step. clear R1. step. step. step.
    rewrite (rcl_zxb_eqb _ 3) by lia.
    change (bv_unsigned (nth 1 bs (Z_to_bv 8 0))) with (bt bs 1) in *.
    destruct (Z.eqb_spec (bt bs 1) 3) as [E1|E1]; cbn [negb].
    2: { apply FIN_FAIL. unfold ports_ok, decl. rewrite Pf, Qf, E0, (proj2 (Z.eqb_neq _ _) E1). reflexivity. }
    step. step. rc_false.
    step. step. rewrite (unsigned_lit (p + 4)) by lia. rewrite rc_shr3. step.
    destruct (asan_shadow_read_at rsegs m off p 20 W 4 ((p + 4) / 8 + off) HSRp ltac:(lia) eq_refl)
      as (k4 & RK4 & BK4).
    pose proof (HADp 4 k4 ltac:(lia) BK4) as OK4. unfold asan_ok in OK4.
    pose proof (rc_byte_signed k4) as KR4. clear BK4.
    step. clear RK4. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k4)) by lia.
    enough (M3 : forall y15 y16, evt rsegs Q (ST 0x88454 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (-1))
                   (Z_to_bv 64 (p + 4)) (Z_to_bv 64 off) y15 y16 x17 x28 x29 m)).
    { destruct (Z.eqb_spec (bv_signed k4) 0) as [E|E]; cbn [negb]; [apply M3|].
      step. rewrite (unsigned_lit (p + 4)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 4) mod 8) (bv_signed k4))
        by (pose proof (Z.mod_pos_bound (p + 4) 8 ltac:(lia)); lia).
      replace ((p + 4) mod 8 <? bv_signed k4) with true by (symmetry; apply Z.ltb_lt; lia).
      apply M3. }
    intros w15 w16.
    pose proof (rd_byte rsegs m p bs 4 HB ltac:(lia)) as R4.
    pose proof (byte_range (nth 4 bs (Z_to_bv 8 0))) as B4.
    step. clear R4. step. step.
    rewrite (rcl_zxb_eqb _ 130) by lia.
    change (bv_unsigned (nth 4 bs (Z_to_bv 8 0))) with (bt bs 4) in *.
    destruct (Z.eqb_spec (bt bs 4) 130) as [X|X]; cbn [negb].
    - assert (Hok : ports_ok p q bs = true) by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1, X; reflexivity).
      exact (reac_ports_parse_accept Hok _ _ _ _ _ _ _ _ _ _).
    - step. step. rc_false.
      step. step. step.
      unfold zxb. change (bv_unsigned (nth 4 bs (Z_to_bv 8 0))) with (bt bs 4).
      rewrite (unsigned_lit (bt bs 4)) by lia.
      rewrite (rcl_ori_eqb (bt bs 4)) by lia.
      destruct ((bt bs 4 =? 128) || (bt bs 4 =? 132)) eqn:O; cbn [negb].
      + assert (Hok : ports_ok p q bs = true)
          by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1; apply orb_true_iff in O;
              destruct O as [O|O]; apply Z.eqb_eq in O; rewrite O; reflexivity).
        exact (reac_ports_parse_accept Hok _ _ _ _ _ _ _ _ _ _).
      + apply FIN_FAIL. unfold ports_ok, decl. rewrite Pf, Qf, E0, E1.
        rewrite (proj2 (Z.eqb_neq (bt bs 4) 130) X). apply orb_false_iff in O. destruct O as [O1 O2].
        rewrite O1, O2. reflexivity.
  Qed.
End Body.

Theorem reac_ports_parse_holds : reac_ports_parse_contract.
Proof.
  unfold reac_ports_parse_contract, REAC_PORTS_PARSE, REAC_PORTS_PARSE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p q lo bs -> -> Hp Hq ST HLO HR HWR HAS HWS.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  destruct (Z.eqb_spec p 0) as [P0|P0]; [|destruct (Z.eqb_spec q 0) as [Q0|Q0]].
  - subst p. clear HR HWR HAS HWS.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    step. step. rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb].
    step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold reac_ports_parse_post.
    replace (ports_ok 0 q bs) with false by reflexivity.
    do 13 eexists. split; [reflexivity|].
    split; [exact WM|]. split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV)|].
    split; [exact ST | exact MU].
  - subst q. clear HR HWR HAS HWS.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    step. step. rewrite (rcl_eqb p 0) by lia.
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact P0). cbn [negb].
    step. rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb].
    step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold reac_ports_parse_post.
    replace (ports_ok p 0 bs) with false by (unfold ports_ok; rewrite (proj2 (Z.eqb_neq _ _) P0); reflexivity).
    do 13 eexists. split; [reflexivity|].
    split; [exact WM|]. split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV)|].
    split; [exact ST | exact MU].
  - destruct (HR P0 Q0) as [Hlen HB]. destruct (HWR P0 Q0) as (Hq4 & HWr & Hd & HDp & HDq).
    destruct (HAS P0 Q0) as (HCE & HSW & HADRp & HADRq). pose proof (HWS P0 Q0) as HWX.
    clear HR HWR HAS HWS.
    pose proof (rt_asan_rt m _ HCE HWX) as HRT.
    pose proof (rt_shadow_rd m p 20 _ HADRp (fun x Hx => HWX x (or_intror (or_intror Hx)))) as HSRp.
    pose proof (rt_shadow_rd m q 12 _ HADRq (fun x Hx => HWX x (or_intror (or_intror Hx)))) as HSRq.
    pose proof (rt_addressable m p 20 HADRp) as HADp.
    pose proof (rt_addressable m q 12 HADRq) as HADq.
    set (off := ASAN_K) in HRT, HSRp, HSRq, HADp, HADq. clearbody off.
    clear HCE HSW HADRp HADRq HWX.
    pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
    pose proof HWr as (HWl & HWh & _).
    assert (SF : sub_fp [(bv_unsigned sp - 16, bv_unsigned sp)]
                   [(bv_unsigned sp - 16, bv_unsigned sp); (q, q + 12)])
      by (intros x Hx; cbn [outside] in *; tauto).
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU SF) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 off p 20 _ _ HSRp MU SF) as HSRp1.
    pose proof (asan_shadow_rd_munch rsegs m m1 off q 12 _ _ HSRq MU SF) as HSRq1.
    pose proof (asan_addressable_munch rsegs m m1 off p 20 _ _ HADp HSRp MU SF) as HADp1.
    pose proof (asan_addressable_munch rsegs m m1 off q 12 _ _ HADq HSRq MU SF) as HADq1.
    clear HRT HSRp HSRq HADp HADq.
    step. step. rewrite (rcl_eqb p 0) by lia.
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact P0). cbn [negb].
    step. rewrite (rcl_eqb q 0) by lia.
    replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; exact Q0). cbn [negb].
    refine (reac_ports_parse_entry ra _ gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m1 p q off bs
              [(bv_unsigned sp - 16, bv_unsigned sp); (q, q + 12)] _
              ltac:(lia) ltac:(lia) Hlen HB Hq4 HWr Hd (fun x Hx => proj2 Hx) HRT1 HSRp1 HSRq1 HADp1 HADq1 _ _
              t0 t1 t2 a3 a4 a5 a6 a7 t3 t4).
    + intros HF x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29.
      step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold reac_ports_parse_post. rewrite HF.
      do 13 eexists. split; [reflexivity|].
      split; [exact WM|]. split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV)|].
      split; [exact ST | exact MU].
    + intros HO x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 mm MUq WMq MIq SKq BQ0 BQ4 BQ8.
      eapply rw_cells_transport in FR; [ | exact MUq | exact WMq | simpl; lia ].
      apply SKq in ST.
      step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold reac_ports_parse_post. rewrite HO.
      do 13 eexists. split; [reflexivity|].
      split; [exact (wmono_trans rsegs m m1 mm WM WMq)|].
      split; [intros HI; exact (MIq (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV))|].
      split; [exact ST|].
      split; [exact BQ0|]. split; [exact BQ4|]. split; [exact BQ8|].
      eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MUq]];
        intros x Hx; cbn [outside] in *; tauto.
Qed.

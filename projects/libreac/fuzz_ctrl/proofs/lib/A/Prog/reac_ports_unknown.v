From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT reac_ports_unknown_c.
Import ListNotations.
Open Scope Z_scope.

Lemma reac_ports_unknown_sub_frame : forall a b L, sub_fp [(a, b)] ((a, b) :: L).
Proof. intros a b L x [H1 _]. split; [exact H1 | exact I]. Qed.

Lemma reac_ports_unknown_sub_tail : forall a L, sub_fp L (a :: L).
Proof. intros [lo hi] L x [_ H2]. exact H2. Qed.

Lemma reac_ports_unknown_munch : forall a b L m m1 mc,
  munch [(a, b)] m m1 -> munch L m1 mc -> munch ((a, b) :: L) m mc.
Proof.
  intros a b L m m1 mc H1 H2 x [Hx1 Hx2]. rewrite (H2 x Hx2). apply H1. split; [exact Hx1 | exact I].
Qed.

Section P.
  Variables (ra sp1 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (p c off : Z) (W : list ivl) (bs : list byte)
    (Q : machine_state -> Prop).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rc : 0 <= c < 2^64.
  Hypothesis HWs : sub_fp (if c =? 0 then [] else [(c, c + 1)]) W.
  Hypothesis HP : p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs m1 p bs.
  Hypothesis HD : c <> 0 -> p <> 0 -> c + 1 <= p \/ p + 20 <= c.
  Hypothesis HSC : c <> 0 -> asan_shadow_rd rsegs m1 off c 1 W /\ asan_addressable rsegs m1 off c 1.
  Hypothesis HSP : p <> 0 -> asan_shadow_rd rsegs m1 off p 20 W /\ asan_addressable rsegs m1 off p 20.
  Hypothesis HWc : c <> 0 -> wr_at rsegs m1 c 1.

  Abbreviation ST pc mc x5 x6 x7 x10 x12 x13 x15 x16 x17 :=
    (MS (mkR ra sp1 gp tp x5 x6 x7 s0 s1 x10 (Z_to_bv 64 c) x12 x13 (Z_to_bv 64 off) x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs)).

  Hypothesis EXIT : forall mc x5 x6 x7 x10 x13 x15 x16 x17,
    rc_inv rsegs c m1 mc (if pu_ok p bs then pu_first bs 12 else 0) ->
    evt rsegs Q (ST 0x8796c mc x5 x6 x7 x10 (Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1))
                    x13 x15 x16 x17).

  Lemma reac_ports_unknown_mc : forall mc v, rc_inv rsegs c m1 mc v ->
    (p <> 0 -> bytes_at rsegs mc p bs) /\
    (c <> 0 -> asan_shadow_rd rsegs mc off c 1 W /\ asan_addressable rsegs mc off c 1) /\
    (p <> 0 -> asan_shadow_rd rsegs mc off p 20 W /\ asan_addressable rsegs mc off p 20).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros mc v HI. destruct (rc_inv_post rsegs c m1 mc v HI) as (MU & _).
    split; [|split].
    - intros P0. destruct (HP P0) as (H20 & Hlen & HB).
      apply (bytes_at_transport rsegs _ m1 mc p bs HB MU). rewrite Hlen. change (Z.of_nat 20) with 20.
      destruct (Z.eqb_spec c 0) as [C0|C0]; cbn [disjoint_from]; [exact I|].
      split; [|exact I]. destruct (HD C0 P0); lia.
    - intros C0. destruct (HSC C0) as [HR HA]. split.
      + exact (asan_shadow_rd_munch rsegs m1 mc off c 1 W _ HR MU HWs).
      + exact (asan_addressable_munch rsegs m1 mc off c 1 W _ HA HR MU HWs).
    - intros P0. destruct (HSP P0) as [HR HA]. split.
      + exact (asan_shadow_rd_munch rsegs m1 mc off p 20 W _ HR MU HWs).
      + exact (asan_addressable_munch rsegs m1 mc off p 20 W _ HA HR MU HWs).
  Qed.

  Lemma reac_ports_unknown_fin : forall mc v r x5 x6 x7 x10 x13 x15 x16 x17,
    rc_inv rsegs c m1 mc v -> r = Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1) ->
    v = (if pu_ok p bs then pu_first bs 12 else 0) ->
    evt rsegs Q (ST 0x8796c mc x5 x6 x7 x10 r x13 x15 x16 x17).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros mc v r x5 x6 x7 x10 x13 x15 x16 x17 HI -> ->. apply EXIT. exact HI.
  Qed.

  Ltac rpu_bad HI :=
    let Hok := fresh "Hok" in
    assert (Hok : pu_ok p bs = false) by (unfold pu_ok, pu_decl; decide_tests; reflexivity);
    eapply reac_ports_unknown_fin; [exact HI | rewrite Hok; reflexivity | rewrite Hok; reflexivity].

  Lemma reac_ports_unknown_tail : forall j mc x6 x7,
    (j < 12)%nat -> pu_ok p bs = true ->
    rc_inv rsegs c m1 mc (pu_first bs (S j)) ->
    ((S j < 12)%nat ->
      evt rsegs Q (ST 0x8790c mc (Z_to_bv 64 (c mod 8)) x6 x7 (Z_to_bv 64 (p + 8 + Z.of_nat (S j)))
                      (Z_to_bv 64 (pu_nunk bs (S j))) (Z_to_bv 64 (p + 8 + Z.of_nat (S j)))
                      (Z_to_bv 64 (12 - Z.of_nat (S j))) (Z_to_bv 64 4) (Z_to_bv 64 (c / 8 + off)))) ->
    evt rsegs Q (ST 0x8793c mc (Z_to_bv 64 (c mod 8)) x6 x7 (Z_to_bv 64 (p + 8 + Z.of_nat j))
                    (Z_to_bv 64 (pu_nunk bs (S j))) (Z_to_bv 64 (p + 8 + Z.of_nat j))
                    (Z_to_bv 64 (12 - Z.of_nat j)) (Z_to_bv 64 4) (Z_to_bv 64 (c / 8 + off))).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros j mc x6 x7 Hj Hok HI K. pose proof (pu_nunk_range bs (S j)) as NR.
    step. step. step. step.
    rewrite (rc_eqb (12 - Z.of_nat j + -1) 0) by lia.
    destruct (Nat.eq_dec j 11) as [J|J].
    - subst j. replace (12 - Z.of_nat 11 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. step. step. rewrite (rc_slliw2 (pu_nunk bs 12)) by lia.
      eapply reac_ports_unknown_fin; [exact HI | rewrite Hok; reflexivity | rewrite Hok; reflexivity].
    - replace (12 - Z.of_nat j + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. replace (p + 8 + Z.of_nat j + 1) with (p + 8 + Z.of_nat (S j)) by lia.
      replace (12 - Z.of_nat j + -1) with (12 - Z.of_nat (S j)) by lia.
      apply K. lia.
  Qed.

  Lemma reac_ports_unknown_loop : forall n j mc x6 x7,
    (j + n = 12)%nat -> (0 < n)%nat -> p <> 0 -> pu_ok p bs = true ->
    rc_inv rsegs c m1 mc (pu_first bs j) ->
    evt rsegs Q (ST 0x8790c mc (Z_to_bv 64 (c mod 8)) x6 x7 (Z_to_bv 64 (p + 8 + Z.of_nat j))
                    (Z_to_bv 64 (pu_nunk bs j)) (Z_to_bv 64 (p + 8 + Z.of_nat j))
                    (Z_to_bv 64 (12 - Z.of_nat j)) (Z_to_bv 64 4) (Z_to_bv 64 (c / 8 + off))).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    induction n as [|n IH]; intros j mc x6 x7 Hjn Hn P0 Hok HI; [lia|].
    destruct (HP P0) as (H20 & Hlen & _).
    destruct (reac_ports_unknown_mc mc _ HI) as (HBm & HSCm & HSPm).
    pose proof (HBm P0) as HB. destruct (HSPm P0) as [HSR HAD]. clear HBm HSPm.
    pose proof (pu_nunk_range bs j) as NR.
    assert (NEXT : forall mc' y6 y7, rc_inv rsegs c m1 mc' (pu_first bs (S j)) ->
      evt rsegs Q (ST 0x8793c mc' (Z_to_bv 64 (c mod 8)) y6 y7 (Z_to_bv 64 (p + 8 + Z.of_nat j))
                      (Z_to_bv 64 (pu_nunk bs (S j))) (Z_to_bv 64 (p + 8 + Z.of_nat j))
                      (Z_to_bv 64 (12 - Z.of_nat j)) (Z_to_bv 64 4) (Z_to_bv 64 (c / 8 + off)))).
    { intros mc' y6 y7 HI'. apply (reac_ports_unknown_tail j); [lia | exact Hok | exact HI' |].
      intros HS. apply (IH (S j)); [lia | lia | exact P0 | exact Hok | exact HI']. }
    assert (NEXT1 : 4 <= rc_u8 bs (8 + j) -> forall mc' y6 y7, rc_inv rsegs c m1 mc' (pu_first bs (S j)) ->
      evt rsegs Q (ST 0x87938 mc' (Z_to_bv 64 (c mod 8)) y6 y7 (Z_to_bv 64 (p + 8 + Z.of_nat j))
                      (Z_to_bv 64 (pu_nunk bs j)) (Z_to_bv 64 (p + 8 + Z.of_nat j))
                      (Z_to_bv 64 (12 - Z.of_nat j)) (Z_to_bv 64 4) (Z_to_bv 64 (c / 8 + off)))).
    { intros K mc' y6 y7 HI'. step. rewrite (rc_addiw (pu_nunk bs j) 1) by lia.
      rewrite <- (pu_nunk_unk bs j K). apply NEXT. exact HI'. }
    assert (BODY : forall y6 y7,
      evt rsegs Q (ST 0x8791c mc (Z_to_bv 64 (c mod 8)) y6 y7 (Z_to_bv 64 (p + 8 + Z.of_nat j))
                      (Z_to_bv 64 (pu_nunk bs j)) (Z_to_bv 64 (p + 8 + Z.of_nat j))
                      (Z_to_bv 64 (12 - Z.of_nat j)) (Z_to_bv 64 4) (Z_to_bv 64 (c / 8 + off)))).
    { intros y6 y7.
      pose proof (rd_byte rsegs mc p bs (8 + j) HB ltac:(lia)) as RD.
      pose proof (rc_u8_range bs (8 + j)) as UR.
      step. step. rewrite (rc_u8_ltu bs (8 + j) 4) by lia.
      destruct (Z.ltb_spec (rc_u8 bs (8 + j)) 4) as [K|K]; cbv iota.
      - rewrite <- (pu_nunk_known bs j K). apply NEXT.
        apply (rc_inv_same rsegs c m1 mc (pu_first bs j)); [right; symmetry; apply pu_first_keep; lia | exact HI].
      - step. rewrite (rc_eqb c 0) by lia.
        destruct (Z.eqb_spec c 0) as [C0|C0]; cbv iota.
        + apply (NEXT1 K). apply (rc_inv_same rsegs c m1 mc (pu_first bs j)); [left; exact C0 | exact HI].
        + step. rewrite (rc_eqb (pu_nunk bs j) 0) by lia.
          destruct (Z.eqb_spec (pu_nunk bs j) 0) as [N0|N0]; cbn [negb].
          * pose proof (rc_inv_store_ok rsegs c m1 mc _ C0 HI) as SO.
            destruct (HSCm C0) as [HSRc HADc].
            destruct (asan_shadow_read_at rsegs mc off c 1 W 0 (c / 8 + off) HSRc ltac:(lia)
                        ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (kc & RKc & BKc).
            pose proof (HADc 0 kc ltac:(lia) BKc) as OKc. rewrite Z.add_0_r in OKc.
            pose proof (rc_byte_signed kc) as KRc. clear BKc.
            assert (STORE : forall y7',
              evt rsegs Q (ST 0x87934 mc (Z_to_bv 64 (c mod 8)) (zxb (nth (8 + j) bs (Z_to_bv 8 0))) y7'
                              (Z_to_bv 64 (p + 8 + Z.of_nat j)) (Z_to_bv 64 (pu_nunk bs j))
                              (Z_to_bv 64 (p + 8 + Z.of_nat j)) (Z_to_bv 64 (12 - Z.of_nat j)) (Z_to_bv 64 4)
                              (Z_to_bv 64 (c / 8 + off)))).
            { intros y7'. step. rewrite le1_zxb.
              apply (NEXT1 K).
              rewrite (pu_first_new bs j N0 K). exact (rc_inv_store rsegs c m1 mc _ _ C0 Rc HI). }
            step. clear RKc.
            step. unfold sxb. rewrite (rc_eqb0_signed (bv_signed kc)) by lia.
            destruct (Z.eqb_spec (bv_signed kc) 0) as [K0|K0]; cbn [negb].
            -- apply STORE.
            -- step.
               rewrite (rc_lts_signed (c mod 8) (bv_signed kc))
                 by (pose proof (Z.mod_pos_bound c 8 ltac:(lia)); lia).
               replace (c mod 8 <? bv_signed kc) with true by (symmetry; apply Z.ltb_lt; destruct OKc; lia).
               apply STORE.
          * apply (NEXT1 K).
            apply (rc_inv_same rsegs c m1 mc (pu_first bs j)); [right; symmetry; apply pu_first_keep; lia | exact HI]. }
    destruct (asan_shadow_read_at rsegs mc off p 20 W (8 + Z.of_nat j) ((p + 8 + Z.of_nat j) / 8 + off) HSR
                ltac:(lia)
                ltac:(unfold asan_shadow; replace (p + (8 + Z.of_nat j)) with (p + 8 + Z.of_nat j) by lia;
                      reflexivity)) as (k & RK & BK).
    pose proof (HAD (8 + Z.of_nat j) k ltac:(lia) BK) as OK.
    replace (p + (8 + Z.of_nat j)) with (p + 8 + Z.of_nat j) in OK by lia.
    pose proof (rc_byte_signed k) as KR. clear BK.
    step. rewrite (unsigned_lit (p + 8 + Z.of_nat j)) by lia. rewrite rc_shr3.
    step. step. clear RK.
    step. unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step. rewrite (unsigned_lit (p + 8 + Z.of_nat j)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 8 + Z.of_nat j) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 8 + Z.of_nat j) 8 ltac:(lia)); lia).
      replace ((p + 8 + Z.of_nat j) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      cbn [negb].
      step. apply BODY.
  Qed.

  Lemma reac_ports_unknown_decl : forall mc x5 x6 x7 x15 x16 x17,
    p <> 0 -> rc_inv rsegs c m1 mc 0 -> rc_u8 bs 0 = 1 -> rc_u8 bs 1 = 3 ->
    evt rsegs Q (ST 0x878cc mc x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 (-1)) (Z_to_bv 64 (p + 4)) x15 x16 x17).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros mc x5 x6 x7 x15 x16 x17 P0 HI B0 B1.
    destruct (HP P0) as (H20 & Hlen & _).
    destruct (reac_ports_unknown_mc mc _ HI) as (HBm & _ & _).
    pose proof (HBm P0) as HB. clear HBm.
    pose proof (rd_byte rsegs mc p bs 4 HB ltac:(lia)) as RD4.
    step. step. step. step.
    rewrite rc_zxb_u. change (bv_unsigned (nth 4 bs (Z_to_bv 8 0))) with (rc_u8 bs 4).
    rewrite (rc_decl_ltu (rc_u8 bs 4)) by (apply rc_u8_range).
    destruct (Z.leb_spec 128 (rc_u8 bs 4)) as [D1|D1]; destruct (Z.leb_spec (rc_u8 bs 4) 132) as [D2|D2];
      cbn [andb negb]; [| rpu_bad HI | rpu_bad HI | rpu_bad HI].
    assert (U4 : rc_u8 bs 4 = 128 \/ rc_u8 bs 4 = 129 \/ rc_u8 bs 4 = 130 \/ rc_u8 bs 4 = 131 \/ rc_u8 bs 4 = 132)
      by lia.
    destruct U4 as [U4|[U4|[U4|[U4|U4]]]]; rewrite U4; step; step; step; step;
      [ if_false | if_true; rpu_bad HI | if_false | if_true; rpu_bad HI | if_false ].
    all: assert (Hok : pu_ok p bs = true) by (unfold pu_ok, pu_decl; decide_tests; reflexivity).
    all: step; step; step; step; step.
    all: rewrite (unsigned_lit c) by lia; rewrite rc_shr3.
    all: step; step.
    all: rewrite (unsigned_lit c) by lia; rewrite rc_land7.
    all: step.
    all: replace (p + 8) with (p + 8 + Z.of_nat 0) by lia.
    all: change (Z_to_bv 64 0) with (Z_to_bv 64 (pu_nunk bs 0)).
    all: change (Z_to_bv 64 12) with (Z_to_bv 64 (12 - Z.of_nat 0)).
    all: apply (reac_ports_unknown_loop 12 0 mc); [lia | lia | exact P0 | exact Hok | exact HI].
  Qed.

  Lemma reac_ports_unknown_b4 : forall mc x5 x6 x7 x13 x15 x16 x17,
    p <> 0 -> rc_inv rsegs c m1 mc 0 -> rc_u8 bs 0 = 1 -> rc_u8 bs 1 = 3 ->
    evt rsegs Q (ST 0x878b8 mc x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x13 x15 x16 x17).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros mc x5 x6 x7 x13 x15 x16 x17 P0 HI B0 B1.
    destruct (HP P0) as (H20 & Hlen & _).
    destruct (reac_ports_unknown_mc mc _ HI) as (_ & _ & HSPm).
    destruct (HSPm P0) as [HSR HAD]. clear HSPm.
    destruct (asan_shadow_read rsegs mc off p 20 W 4 HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD 4 k ltac:(lia) BK) as OK. pose proof (rc_byte_signed k) as KR. clear BK.
    step. step. rewrite (unsigned_lit (p + 4)) by lia. rewrite rc_shr3.
    step. step. clear RK.
    step. unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply reac_ports_unknown_decl; assumption.
    - step. rewrite (unsigned_lit (p + 4)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 4) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 4) 8 ltac:(lia)); lia).
      replace ((p + 4) mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply reac_ports_unknown_decl; assumption.
  Qed.

  Lemma reac_ports_unknown_b1 : forall mc x5 x6 x7 x13 x15 x16 x17,
    p <> 0 -> rc_inv rsegs c m1 mc 0 -> rc_u8 bs 0 = 1 ->
    evt rsegs Q (ST 0x87898 mc x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x13 x15 x16 x17).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros mc x5 x6 x7 x13 x15 x16 x17 P0 HI B0.
    destruct (HP P0) as (H20 & Hlen & _).
    destruct (reac_ports_unknown_mc mc _ HI) as (HBm & _ & HSPm).
    pose proof (HBm P0) as HB. destruct (HSPm P0) as [HSR HAD]. clear HBm HSPm.
    assert (BODY : forall y15 y16,
      evt rsegs Q (ST 0x878ac mc x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 (-1)) (Z_to_bv 64 (p + 1)) y15 y16 x17)).
    { intros y15 y16.
      pose proof (rd_byte rsegs mc p bs 1 HB ltac:(lia)) as RD1.
      step. step. step. rewrite (rc_u8_eqb bs 1 3) by lia.
      destruct (Z.eqb_spec (rc_u8 bs 1) 3) as [B1|B1]; cbn [negb]; [|rpu_bad HI].
      apply reac_ports_unknown_b4; assumption. }
    destruct (asan_shadow_read rsegs mc off p 20 W 1 HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD 1 k ltac:(lia) BK) as OK. pose proof (rc_byte_signed k) as KR. clear BK.
    step. step. rewrite (unsigned_lit (p + 1)) by lia. rewrite rc_shr3.
    step. step. clear RK.
    step. unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step. rewrite (unsigned_lit (p + 1)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 1) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 1) 8 ltac:(lia)); lia).
      replace ((p + 1) mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.

  Lemma reac_ports_unknown_body : forall mc x5 x6 x7 x12 x13 x15 x16 x17,
    rc_inv rsegs c m1 mc 0 ->
    evt rsegs Q (ST 0x87874 mc x5 x6 x7 (Z_to_bv 64 p) x12 x13 x15 x16 x17).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros mc x5 x6 x7 x12 x13 x15 x16 x17 HI.
    step. step. rewrite (rc_eqb p 0) by lia.
    destruct (Z.eqb_spec p 0) as [P0|P0]; cbv iota.
    - rpu_bad HI.
    - destruct (HP P0) as (H20 & Hlen & _).
      destruct (reac_ports_unknown_mc mc _ HI) as (HBm & _ & HSPm).
      pose proof (HBm P0) as HB. destruct (HSPm P0) as [HSR HAD]. clear HBm HSPm.
      assert (BODY : forall y13 y15,
        evt rsegs Q (ST 0x8788c mc x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 (-1)) y13 y15 x16 x17)).
      { intros y13 y15.
        pose proof (rd_byte rsegs mc p bs 0 HB ltac:(lia)) as RD0.
        step. step. step. rewrite (rc_u8_eqb bs 0 1) by lia.
        destruct (Z.eqb_spec (rc_u8 bs 0) 1) as [B0|B0]; cbn [negb]; [|rpu_bad HI].
        apply reac_ports_unknown_b1; assumption. }
      destruct (asan_shadow_read_at rsegs mc off p 20 W 0 (p / 8 + off) HSR ltac:(lia)
                  ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k & RK & BK).
      pose proof (HAD 0 k ltac:(lia) BK) as OK. rewrite Z.add_0_r in OK.
      pose proof (rc_byte_signed k) as KR. clear BK.
      step. rewrite (unsigned_lit p) by lia. rewrite rc_shr3.
      step. step. clear RK.
      step. unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
      + apply BODY.
      + step. rewrite (unsigned_lit p) by lia. rewrite rc_land7.
        step.
        rewrite (rc_lts_signed (p mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
        replace (p mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia).
        apply BODY.
  Qed.

  Lemma reac_ports_unknown_start : forall x5 x6 x7 x12 x13 x15 x16 x17,
    evt rsegs Q (ST 0x8785c m1 x5 x6 x7 (Z_to_bv 64 p) x12 x13 x15 x16 x17).
  Proof using Rp Rc HWs HP HD HSC HSP HWc EXIT.
    intros x5 x6 x7 x12 x13 x15 x16 x17.
    step. rewrite (rc_eqb c 0) by lia.
    destruct (Z.eq_dec c 0) as [C0|C0].
    - replace (c =? 0) with true by (symmetry; apply Z.eqb_eq; exact C0). cbv iota.
      apply reac_ports_unknown_body. left. split; [exact C0 | reflexivity].
    - replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact C0). cbv iota.
      destruct (HSC C0) as [HSRc HADc].
      destruct (asan_shadow_read_at rsegs m1 off c 1 W 0 (c / 8 + off) HSRc ltac:(lia)
                  ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k & RK & BK).
      pose proof (HADc 0 k ltac:(lia) BK) as OK. rewrite Z.add_0_r in OK.
      pose proof (rc_byte_signed k) as KR. clear BK.
      pose proof (rc_store_ok rsegs m1 c (HWc C0)) as SO.
      assert (STORE : forall y12 y13,
        evt rsegs Q (ST 0x87870 m1 x5 x6 x7 (Z_to_bv 64 p) y12 y13 x15 x16 x17)).
      { intros y12 y13. step.
        match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 c) ?l) _) =>
          replace l with [Z_to_bv 8 0] by reflexivity end.
        apply reac_ports_unknown_body. exact (rc_inv_first rsegs c m1 (Z_to_bv 8 0) C0 Rc (HWc C0)). }
      step. rewrite (unsigned_lit c) by lia. rewrite rc_shr3.
      step. step. clear RK.
      step. unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
      + apply STORE.
      + step. rewrite (unsigned_lit c) by lia. rewrite rc_land7.
        step.
        rewrite (rc_lts_signed (c mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound c 8 ltac:(lia)); lia).
        replace (c mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia).
        apply STORE.
  Qed.
End P.

Theorem reac_ports_unknown_holds : reac_ports_unknown_contract.
Proof.
  unfold reac_ports_unknown_contract, REAC_PORTS_UNKNOWN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p c lo bs Ha0 Ha1 ST HLO HP HC HCE HSW HAC HAP HW.
  pose proof (rc_word_range a0 p Ha0) as Rp. pose proof (rc_word_range a1 c Ha1) as Rc.
  apply rc_word in Ha0. apply rc_word in Ha1. subst a0 a1.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  assert (HWS : forall x, in_shadow x -> outside (reac_ports_unknown_W (bv_unsigned sp) c) x)
    by (intros x Hx; apply HW; right; right; exact Hx).
  assert (HSC : c <> 0 -> asan_shadow_rd rsegs m ASAN_K c 1 (reac_ports_unknown_W (bv_unsigned sp) c) /\
                          asan_addressable rsegs m ASAN_K c 1)
    by (intros C0; split; [exact (rt_shadow_rd m c 1 _ (HAC C0) HWS) | exact (rt_addressable m c 1 (HAC C0))]).
  assert (HSP : p <> 0 -> asan_shadow_rd rsegs m ASAN_K p 20 (reac_ports_unknown_W (bv_unsigned sp) c) /\
                          asan_addressable rsegs m ASAN_K p 20)
    by (intros P0; split; [exact (rt_shadow_rd m p 20 _ (HAP P0) HWS) | exact (rt_addressable m p 20 (HAP P0))]).
  clear HCE HSW HAC HAP HW HWS.
  set (off := ASAN_K) in HRT, HSC, HSP. clearbody off.
  unfold reac_ports_unknown_W, REAC_PORTS_UNKNOWN_FRAME in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (HP1 : p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs m1 p bs).
  { intros P0. destruct (HP P0) as (H20 & Hlen & HB & HF). split; [exact H20|]. split; [exact Hlen|].
    apply (bytes_at_transport rsegs _ m m1 p bs HB MU). rewrite Hlen. change (Z.of_nat 20) with 20.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HD : c <> 0 -> p <> 0 -> c + 1 <= p \/ p + 20 <= c) by (intros C0; exact (proj1 (proj2 (HC C0)))).
  assert (HWc : c <> 0 -> wr_at rsegs m1 c 1)
    by (intros C0; exact (wr_at_transport rsegs m m1 c 1 (proj1 (HC C0)) WM)).
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (reac_ports_unknown_sub_frame _ _ _)) as HRT1.
  pose proof (fun C0 : c <> 0 =>
    conj (asan_shadow_rd_munch rsegs m m1 off c 1 _ _ (proj1 (HSC C0)) MU (reac_ports_unknown_sub_frame _ _ _))
         (asan_addressable_munch rsegs m m1 off c 1 _ _ (proj2 (HSC C0)) (proj1 (HSC C0)) MU
            (reac_ports_unknown_sub_frame _ _ _))) as HSC1.
  pose proof (fun P0 : p <> 0 =>
    conj (asan_shadow_rd_munch rsegs m m1 off p 20 _ _ (proj1 (HSP P0)) MU (reac_ports_unknown_sub_frame _ _ _))
         (asan_addressable_munch rsegs m m1 off p 20 _ _ (proj2 (HSP P0)) (proj1 (HSP P0)) MU
            (reac_ports_unknown_sub_frame _ _ _))) as HSP1.
  pose proof (reac_ports_unknown_sub_tail (bv_unsigned sp + -16, bv_unsigned sp) (if c =? 0 then [] else [(c, c + 1)]))
    as HWs.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step.
  clear RG RC.
  eapply reac_ports_unknown_start; try eassumption.
  intros mc x5 x6 x7 x10 x13 x15 x16 x17 HI.
  destruct (rc_inv_post rsegs c m1 mc _ HI) as (MUc & WMc & STc & MIc & HBc).
  assert (DJ : disjoint_from (if c =? 0 then [] else [(c, c + 1)]) (bv_unsigned sp + -16) 16).
  { destruct (Z.eqb_spec c 0) as [C0|C0]; cbn [disjoint_from]; [exact I|].
    split; [|exact I]. destruct (HC C0) as (_ & _ & HF). lia. }
  pose proof (rw_cells_transport rsegs _ m1 mc _ _ FR MUc WMc DJ) as FRc.
  apply STc in ST. clear FR.
  step. step. step. step.
  release_frame FRc ST (bv_unsigned sp).
  apply evt_done. cbv beta. do 10 eexists. split; [reflexivity|].
  split; [exact (reac_ports_unknown_munch _ _ _ m m1 mc MU MUc)|].
  split; [exact (wmono_trans rsegs m m1 mc WM WMc)|].
  split; [exact ST|].
  split; [intros HI0; apply MIc; exact (rc_mem_inv_frame rsegs m m1 _ _ HI0 MU WV)|].
  exact HBc.
Qed.

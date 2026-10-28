(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2 FseRdKit3.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base.
Import ListNotations.
Open Scope Z_scope.

Section Zero.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.
  Variable POST : machine_state -> Prop.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Lemma tab_rd : forall m1 i, mem_inv usegs m1 -> 0 <= i < 32 ->
    ov_read_bytes usegs m1 (Z_to_bv 64 (70168 + i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) DB_TABLE 0)].
  Proof.
    intros m1 i MI Hi.
    assert (RO : ro_cells usegs m1 70168 [CB 32 (map (Z_to_bv 8) DB_TABLE)]).
    { apply (ro_cells_image usegs m1 70168 (map (Z_to_bv 8) DB_TABLE) MI); [vm_compute; reflexivity| lia| cbn; lia]. }
    destruct RO as [_ BA]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
    eapply (u8ro_read usegs m1 70168 _ i); [exact BA| | lia| unfold wa; f_equal; lia].
    rewrite nth_error_map. rewrite (nth_error_nth' DB_TABLE 0) by (cbn; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma zero_ctz1 : forall bs m1 (x1 x6 x11 x14 x16 x24 x25 x26 x27 x28 x29 : word),
    0 <= bs < 2^32 -> mem_inv usegs m1 ->
    evt usegs POST (rd_lst C 0x29eac m1 (Z_to_bv 64 70168) x6 x11 (Z_to_bv 64 (bv_swrap 32 bs)) (Z_to_bv 64 (ctzv bs)) (Z_to_bv 64 24)
                      x24 x25 x26 x27 x28 x29) ->
    evt usegs POST (rd_lst C 0x29e80 m1 x1 x6 x11 (Z_to_bv 64 (bv_swrap 32 bs)) x14 x16 x24 x25 x26 x27 x28 x29).
  Proof.
    intros bs m1 x1 x6 x11 x14 x16 x24 x25 x26 x27 x28 x29 Hbs MI K.
    pose proof (ctzv_range bs Hbs) as Rk. destruct (db_table_ok (ctzv bs) ltac:(lia)) as [Ri Et].
    pose proof (tab_rd m1 (db_idx (ctzv bs)) MI Ri) as RD. rewrite Et in RD.
    unfold rd_lst in *.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (ctz_index_form bs Hbs).
    zstep. cbv beta. rewrite byte_lit by lia.
    zstep.
    exact K.
  Qed.
  (* [comment removed for export] *)
  Lemma zero_load1 : forall m1 msvw tlw nc ip' bc' cn (x6 x13 x14 x16 x24 x25 x28 x29 : word),
    rd_inv C m1 nc msvw tlw -> 0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= bc' < 32 -> 0 <= cn < 2^31 ->
    (forall y16 y28, evt usegs POST (rd_lst C 0x29f10 m1 (Z_to_bv 64 70168) x6 (Z_to_bv 64 (cn + 36))
                                      (Z_to_bv 64 (bv_swrap 32 (le32 buf ip' / 2 ^ bc'))) (Z_to_bv 64 (ctzv (le32 buf ip' / 2 ^ bc')))
                                      y16 x24 x25 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip')) y28 x29)) ->
    evt usegs POST (rd_lst C 0x29ec0 m1 (Z_to_bv 64 70168) x6 (Z_to_bv 64 cn) x13 x14 x16 x24 x25 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip'))
                      x28 x29).
  Proof.
    intros m1 msvw tlw nc ip' bc' cn x6 x13 x14 x16 x24 x25 x28 x29 INV Hip0 Hip4 Hbc Hcn K.
    destruct INV as (_ & _ & HBUF & _ & _ & _ & _ & _ & _ & MI).
    destruct (buf_rd C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
    destruct (buf_rd C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
    destruct (buf_rd C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
    destruct (buf_rd C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
    rewrite !Z.add_assoc in RD1, RD2, RD3.
    set (bs' := le32 buf ip' / 2 ^ bc') in *.
    assert (Rbs : 0 <= bs' < 2^32) by (subst bs'; apply shr_range; [apply le32_range; apply (buf_all_bytes C OK)| lia]).
    pose proof (ctzv_range bs' Rbs) as Rk. destruct (db_table_ok (ctzv bs') ltac:(lia)) as [Ri Et].
    pose proof (tab_rd m1 (db_idx (ctzv bs')) MI Ri) as RDT. rewrite Et in RDT.
    unfold rd_lst in *.
    zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc' 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
    fold (le32 buf ip'). fold bs'.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (ctz_index_form bs' Rbs).
    zstep. cbv beta. rewrite byte_lit by lia.
    zstep.
    apply K.
  Qed.
  (* [comment removed for export] *)
  Lemma zero_rep : forall f s rep s1 rep1 m1 msvw tlw pc (x6 x16 x24 x25 x28 x29 : word),
    rep_loop buf f s rep = Ok (s1, rep1) ->
    rd_inv C m1 (r_nc s) msvw tlw ->
    0 <= r_bitStream s < 2^32 -> 0 <= r_ip s -> r_ip s + 4 <= zlen buf -> 0 <= r_bitCount s < 32 ->
    0 <= r_charnum s -> r_charnum s + 36 * Z.of_nat f <= 2^30 ->
    rep = ctzv (r_bitStream s) / 2 ->
    ((pc = 0x29eac /\ x16 = Z_to_bv 64 24) \/ pc = 0x29f10) ->
    (forall y16 y28,
        0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
        0 <= r_charnum s1 <= 2^30 -> rep1 = ctzv (r_bitStream s1) / 2 -> rep1 < 12 ->
        r_nc s1 = r_nc s /\ r_remaining s1 = r_remaining s /\ r_threshold s1 = r_threshold s /\ r_nbBits s1 = r_nbBits s /\ r_previous0 s1 = r_previous0 s ->
        evt usegs POST (rd_lst C 0x29f4c m1 (Z_to_bv 64 70168) x6 (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s1)))
                          (Z_to_bv 64 (ctzv (r_bitStream s1))) y16 x24 x25 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (BUF + r_ip s1)) y28 x29)) ->
    evt usegs POST (rd_lst C pc m1 (Z_to_bv 64 70168) x6 (Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s)))
                      (Z_to_bv 64 (ctzv (r_bitStream s))) x16 x24 x25 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (BUF + r_ip s)) x28 x29).
  Proof.
    induction f as [|f IH]; intros s rep s1 rep1 m1 msvw tlw pc x6 x16 x24 x25 x28 x29 RL INV Hbs Hip0 Hip4 Hbc Hcn0 Hcn Erep Hpc K.
    { cbn in RL. discriminate RL. }
    pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & (HB0 & HB1) & _).
    destruct (rd_aln C OK) as (_ & _ & _ & _ & _ & _ & HBP).
    pose proof (ctzv_range _ Hbs) as Rk.
    cbn [rep_loop] in RL.
    destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
    change (2^30) with 1073741824 in *. rewrite Nat2Z.inj_succ in Hcn.
    destruct (Z.leb_spec 12 rep) as [GE|LT].
    - (* [comment removed for export] *)
      assert (K24 : 24 <= ctzv bs) by (subst rep; Z.div_mod_to_equations; lia).
      unfold FseNCount.Zlength in RL.
      (* [comment removed for export] *)
      assert (LOAD : forall ip' bc' (y13 y14 y16 y26 y27 y28 : word),
                (let! w := readLE32 buf ip' in let! bs0 := shr32 w bc' in let! repeats' := repeats_of bs0 in
                 rep_loop buf f (FseNCount.mkR nc ip' bs0 bc' (cn + 3 * 12) rem thr nb p0) repeats') = Ok (s1, rep1) ->
                y27 = Z_to_bv 64 (BUF + ip') -> y26 = Z_to_bv 64 bc' ->
                evt usegs POST (rd_lst C 0x29ec0 m1 (Z_to_bv 64 70168) x6 (Z_to_bv 64 cn) y13 y14 y16 x24 x25 y26 y27 y28 x29)).
      { intros ip' bc' y13 y14 y16 y26 y27 y28 RL' -> ->.
        destruct (readLE32 buf ip') as [w| | |] eqn:ER; cbn [bind] in RL'; try discriminate RL'.
        destruct (shr32 w bc') as [bs'| | |] eqn:ES; cbn [bind] in RL'; try discriminate RL'.
        destruct (repeats_of bs') as [rep'| | |] eqn:EP; cbn [bind] in RL'; try discriminate RL'.
        destruct (readLE32_inv _ _ _ ER) as (I1 & I2 & ->). destruct (shr32_inv _ _ _ ES) as (I3 & ->).
        assert (Rbs' : 0 <= le32 buf ip' / 2 ^ bc' < 2^32) by (apply shr_range; [apply le32_range; apply (buf_all_bytes C OK)| lia]).
        rewrite (repeats_of_ctzv _ Rbs') in EP. injection EP as <-.
        eapply (zero_load1 m1 msvw tlw nc ip' bc' cn); try eassumption; try lia.
        intros z16 z28.
        eapply (IH (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' (cn + 3 * 12) rem thr nb p0) _ s1 rep1 m1 msvw tlw 0x29f10);
          cbnR; try eassumption; try reflexivity; try lia; try (right; reflexivity). }
      clear IH K. pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (junk0 & junk16 & FR) & _).
      unfold rd_lst in LOAD |- *.
      assert (T0 : forall y13 y14 y16 y28 : word, evt usegs POST
                (MS (mkR (Z_to_bv 64 70168) (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C)
                      (Z_to_bv 64 18446744071562067968) x6 (Z_to_bv 64 23)
                      (Z_to_bv 64 BUF) (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 32) (Z_to_bv 64 cn) (Z_to_bv 64 (BUF + zlen buf + -7)) y13 y14
                      (Z_to_bv 64 4) y16 (Z_to_bv 64 8)
                      (Z_to_bv 64 NC) (Z_to_bv 64 252645135) (Z_to_bv 64 msv1) (Z_to_bv 64 (BUF + zlen buf))
                      (Z_to_bv 64 16843009) (Z_to_bv 64 125613361) x24 x25 (Z_to_bv 64 bc) (Z_to_bv 64 (BUF + ip)) y28 x29
                      (Z_to_bv 64 1431655765) (Z_to_bv 64 858993459))
                    (c_F C) (Z_to_bv 64 0x29eb4) (c_fc C) None m1 (seg_rom usegs))).
      { intros y13 y14 y16 y28. zstep.
        if_cases B; zify_cond B.
        - (* [comment removed for export] *)
          replace (ip <=? zlen buf - 7) with false in RL by (symmetry; apply Z.leb_gt; lia).
          zstep. replace (BUF + zlen buf + -7 - (BUF + ip)) with (zlen buf - 7 - ip) by lia.
          set (d := zlen buf - 7 - ip) in *. assert (Rd : -3 <= d <= -1) by (subst d; lia).
          zstep. zstep. zstep. zstep.
          match goal with |- context [Z_to_bv 64 (?x ≫ 61)] =>
            replace (x ≫ 61) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; change (2^61) with 2305843009213693952; lia) end.
          zstep. if_false.
          zstep. rewrite (slliw3_neg d) by lia.
          zstep. zstep. rewrite (subw_mod64 bc (8 * d)) by lia. rewrite (sub_mod64_word bc (8 * d)).
          zstep. if_false.
          zstep. zstep. zstep.
          eapply (LOAD _ _ _ _ _ _ _ _ RL); first [reflexivity | f_equal; lia | f_equal; rewrite ?land31_word, ?land_31; lia].
        - replace (ip <=? zlen buf - 7) with true in RL by (symmetry; apply Z.leb_le; lia).
          zstep. zstep. if_cases B2; zify_cond B2; [exfalso; lia|].
          eapply (LOAD _ _ _ _ _ _ _ _ RL); [f_equal; lia| reflexivity]. }
      destruct Hpc as [[-> ->] | ->].
      + zstep. if_cases B; zify_cond B; [exfalso; lia|]. zstep. if_cases B2; zify_cond B2; [exfalso; lia|]. apply T0.
      + zstep. if_cases B; zify_cond B; [| exfalso; lia]. apply T0.
    - (* [comment removed for export] *)
      injection RL as <- <-. cbnR.
      assert (K24 : ctzv bs < 24) by (subst rep; Z.div_mod_to_equations; lia).
      specialize (fun y16 y28 => K y16 y28 Hbs Hip0 Hip4 Hbc ltac:(lia) Erep LT ltac:(repeat split; reflexivity)).
      unfold rd_lst in K |- *.
      destruct Hpc as [[-> ->] | ->].
      + zstep. if_cases B; zify_cond B; [| exfalso; lia]. apply K.
      + zstep. if_cases B; zify_cond B; [exfalso; lia|]. zstep. apply K.
  Qed.
  (* [comment removed for export] *)
  Lemma zero_load2 : forall s3 m1 msvw tlw ip' (x6 x13 x14 x16 x27 x28 : word),
    rd_inv C m1 (r_nc s3) msvw tlw ->
    0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s3 < 32 ->
    r_ip s3 = ip' -> r_bitStream s3 = le32 buf ip' / 2 ^ r_bitCount s3 ->
    2 <= r_threshold s3 <= 32768 -> 0 <= r_remaining s3 <= 32769 ->
    (forall y6 y27, evt usegs POST (rd_cnt C s3 m1 y6 y27)) ->
    evt usegs POST (rd_lst C 0x29f94 m1 (Z_to_bv 64 (BUF + ip')) x6 (Z_to_bv 64 (r_charnum s3)) x13 x14 x16
                      (Z_to_bv 64 (r_remaining s3)) (Z_to_bv 64 (r_threshold s3)) (Z_to_bv 64 (r_bitCount s3)) x27 x28
                      (Z_to_bv 64 (r_nbBits s3))).
  Proof.
    intros s3 m1 msvw tlw ip' x6 x13 x14 x16 x27 x28 INV Hip0 Hip4 Hbc Eip Ebs Hthr Hrem K.
    destruct INV as (_ & _ & HBUF & _).
    destruct (buf_rd C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
    destruct (buf_rd C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
    destruct (buf_rd C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
    destruct (buf_rd C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
    rewrite !Z.add_assoc in RD1, RD2, RD3.
    pose proof K as K'. unfold rd_cnt, rd_lst in K'.
    destruct s3 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip.
    unfold rd_lst.
    zstep. zstep. rewrite (swrap32_small (thr + 1073741824)) by lia.
    zstep. if_cases B; zify_cond B; [exfalso; lia|].
    zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
    fold (le32 buf ip'). rewrite <- Ebs.
    zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite ?(Z.mod_small (thr * 2)) by lia.
    zstep. rewrite (swrap32_small (thr * 2 + -1)) by lia.
    zstep. rewrite ?(Z.mod_small (thr * 2 + -1)) by lia.
    zstep. rewrite (swrap32_small (thr * 2 + -1 - rem)) by lia.
    zstep. if_false.
    apply K'.
  Qed.

  (* [comment removed for export] *)
  Lemma zero_reload : forall s2 s3 m1 msvw tlw (x1 x6 x13 x14 x16 x28 : word),
    rd_inv C m1 (r_nc s2) msvw tlw -> reload buf s2 = Ok s3 ->
    0 <= r_ip s2 -> r_ip s2 + 4 <= zlen buf -> 0 <= r_bitCount s2 < 64 ->
    2 <= r_threshold s2 <= 32768 -> 0 <= r_remaining s2 <= 32769 ->
    (forall y6 y27, evt usegs POST (rd_cnt C s3 m1 y6 y27)) ->
    evt usegs POST (rd_lst C 0x29f78 m1 x1 x6 (Z_to_bv 64 (r_charnum s2)) x13 x14 x16 (Z_to_bv 64 (r_remaining s2))
                      (Z_to_bv 64 (r_threshold s2)) (Z_to_bv 64 (r_bitCount s2)) (Z_to_bv 64 (BUF + r_ip s2)) x28
                      (Z_to_bv 64 (r_nbBits s2))).
  Proof.
    intros s2 s3 m1 msvw tlw x1 x6 x13 x14 x16 x28 INV RL Hip0 Hip4 Hbc Hthr Hrem K.
    pose proof (reload_inv buf s2 s3 (buf_all_bytes C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
    destruct RI as (I1 & I2 & I3 & ->).
    pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & (HB0 & HB1) & _).
    destruct (rd_aln C OK) as (_ & _ & _ & _ & _ & _ & HBP).
    pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (junk0 & junk16 & FR) & _).
    destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR.
    unfold reload_pos in *. unfold FseNCount.Zlength in *.
    rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
    assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (LOAD : forall ip' bc' (y1 y13 y14 y16 y26 y27 : word),
       fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
       snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
       y1 = Z_to_bv 64 (BUF + ip') -> y26 = Z_to_bv 64 bc' ->
       evt usegs POST (rd_lst C 0x29f94 m1 y1 x6 (Z_to_bv 64 cn) y13 y14 y16 (Z_to_bv 64 rem) (Z_to_bv 64 thr) y26 y27 x28 (Z_to_bv 64 nb))).
    { intros ip' bc' y1 y13 y14 y16 y26 y27 E1 E2 -> ->. rewrite E1, E2 in *.
      eapply (zero_load2 (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb p0) m1 msvw tlw ip'); try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
    clear K. unfold rd_lst in LOAD |- *.
    assert (FAST : (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) = true -> forall y1 y13 y14 : word,
              y1 = Z_to_bv 64 (BUF + (ip + bc / 8)) ->
              evt usegs POST (MS (mkR y1 (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C)
                      (Z_to_bv 64 18446744071562067968) x6 (Z_to_bv 64 23)
                      (Z_to_bv 64 BUF) (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 32) (Z_to_bv 64 cn) (Z_to_bv 64 (BUF + zlen buf + -7)) y13 y14
                      (Z_to_bv 64 4) x16 (Z_to_bv 64 8)
                      (Z_to_bv 64 NC) (Z_to_bv 64 252645135) (Z_to_bv 64 msv1) (Z_to_bv 64 (BUF + zlen buf))
                      (Z_to_bv 64 16843009) (Z_to_bv 64 125613361) (Z_to_bv 64 rem) (Z_to_bv 64 thr) (Z_to_bv 64 bc) (Z_to_bv 64 (BUF + ip))
                      x28 (Z_to_bv 64 nb) (Z_to_bv 64 1431655765) (Z_to_bv 64 858993459))
                    (c_F C) (Z_to_bv 64 0x29f88) (c_fc C) None m1 (seg_rom usegs))).
    { intros EC y1 y13 y14 ->. rewrite EC in LOAD, I1, I2, I3. cbn [fst snd] in LOAD, I1, I2, I3.
      zstep. if_cases B; zify_cond B; [exfalso; lia|].
      zstep. zstep. if_cases B2; zify_cond B2; [exfalso; lia|].
      eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia | rewrite land_7; reflexivity]. }
    zstep. if_cases B0; zify_cond B0; [exfalso; lia|].
    zstep. rewrite (wrap32_small bc) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    rewrite (swrap32_small (bc / 8)) by lia.
    zstep.
    zstep. if_cases B1; zify_cond B1.
    - zstep. if_cases B2; zify_cond B2; [exfalso; lia|].
      zstep. zstep.
      zstep. if_cases B3; zify_cond B3.
      + eapply FAST; [apply orb_true_iff; right; apply Z.leb_le; lia | f_equal; lia].
      + replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with false in LOAD
          by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
        zstep. zstep. replace (BUF + zlen buf + -4 - (BUF + ip)) with (zlen buf - 4 - ip) by lia.
        set (d := zlen buf - 4 - ip) in *. assert (Rd : 0 <= d <= 2) by (subst d; lia).
        zstep. zstep. zstep. zstep.
        match goal with |- context [Z_to_bv 64 (?x ≫ 61)] =>
          replace (x ≫ 61) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; change (2^61) with 2305843009213693952; lia) end.
        zstep. if_false.
        zstep. rewrite ?(Z.mod_small d) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
        rewrite (swrap32_small (d * 8)) by lia.
        zstep. rewrite ?(Z.mod_small (d * 8)) by lia.
        zstep. rewrite ?(swrap32_small (bc - d * 8)) by lia.
        zstep. if_false.
        zstep. rewrite land_31. zstep. zstep.
        if_cases G4; zify_cond G4; [| exfalso; lia].
        replace (BUF + zlen buf + -4) with (BUF + (zlen buf - 4)) by lia. replace (bc - d * 8) with (bc - 8 * d) by lia.
        eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); first [reflexivity | f_equal; lia | f_equal; f_equal; lia].
    - eapply FAST; [apply orb_true_iff; left; apply Z.leb_le; lia | f_equal; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma zero_tail : forall s1 m1 msvw tlw fl (x6 x16 x28 : word),
    rd_inv C m1 (r_nc s1) msvw tlw ->
    0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
    0 <= r_charnum s1 <= 2^30 -> ctzv (r_bitStream s1) / 2 < 12 -> 0 <= r_remaining s1 < 2^31 ->
    2 <= r_threshold s1 <= 32768 -> r_remaining s1 <= 32769 ->
    (let rep1 := ctzv (r_bitStream s1) / 2 in
     let! bs := shr32 (r_bitStream s1) (2 * rep1) in
     let s2 := FseNCount.mkR (r_nc s1) (r_ip s1) bs (r_bitCount s1 + 2 * rep1 + 2) (r_charnum s1 + 3 * rep1 + Z.land bs 3)
                             (r_remaining s1) (r_threshold s1) (r_nbBits s1) (r_previous0 s1) in
     if msv1 <=? r_charnum s1 + 3 * rep1 + Z.land bs 3 then Ok (Brk s2) else let! s3 := reload buf s2 in Ok (Cont s3)) = Ok fl ->
    (forall s' y1 y6 y13 y14 y16 y25 y28 y29, fl = Brk s' -> r_nc s' = r_nc s1 -> rd_brk_ok C s' ->
        evt usegs POST (rd_exit C s' m1 y1 y6 y13 y14 y16 y25 y28 y29)) ->
    (forall s' y6 y27, fl = Cont s' -> r_nc s' = r_nc s1 -> evt usegs POST (rd_cnt C s' m1 y6 y27)) ->
    evt usegs POST (rd_lst C 0x29f4c m1 (Z_to_bv 64 70168) x6 (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s1)))
                      (Z_to_bv 64 (ctzv (r_bitStream s1))) x16 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1))
                      (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (BUF + r_ip s1)) x28 (Z_to_bv 64 (r_nbBits s1))).
  Proof.
    intros s1 m1 msvw tlw fl x6 x16 x28 INV Hbs Hip0 Hip4 Hbc Hcn Hrep Hrem Hthr Hrem2 RR KB KC.
    pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
    pose proof (ctzv_range _ Hbs) as Rk.
    destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. cbv zeta in RR.
    set (k := ctzv bs) in *. set (rep := k / 2) in *.
    assert (Rrep : 0 <= rep <= 11 /\ 2 * rep <= k <= 2 * rep + 1) by (subst rep; Z.div_mod_to_equations; lia).
    rewrite shr32_ok in RR by lia. cbn [bind] in RR.
    set (bs2 := bs / 2 ^ (2 * rep)) in *.
    assert (Rbs2 : 0 <= bs2 < 2^32) by (subst bs2; apply shr_range; lia).
    assert (L3 : 0 <= Z.land bs2 3 <= 3) by (rewrite land_3; pose proof (Z.mod_pos_bound bs2 4 ltac:(lia)); lia).
    change (2^30) with 1073741824 in *. change (2^31) with 2147483648 in *.
    unfold rd_lst.
    destruct (ctz_masks k ltac:(lia)) as (M1 & M2 & M3). fold rep in M1, M2, M3.
    zstep. rewrite M3. zstep. rewrite M1. zstep. rewrite M2.
    zstep. rewrite (wrap32_swrap32_u32 bs Hbs). rewrite (Z.mod_small (2 * rep) 32) by lia.
    rewrite Z.shiftr_div_pow2 by lia. fold bs2.
    zstep. zstep. zstep. zstep. rewrite (land_swrap32 bs2 3) by lia.
    zstep. rewrite (swrap32_small (2 * rep + rep + cn + Z.land bs2 3)) by lia.
    replace (2 * rep + rep + cn + Z.land bs2 3) with (cn + 3 * rep + Z.land bs2 3) by lia.
    zstep. rewrite (swrap32_small (bc + 2 * rep + 2)) by lia.
    zstep.
    if_cases B; zify_cond B.
    - (* [comment removed for export] *)
      replace (msv1 <=? cn + 3 * rep + Z.land bs2 3) with true in RR by (symmetry; apply Z.leb_le; lia).
      injection RR as <-.
      pose proof (KB (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)) as KB'.
      unfold rd_exit, rd_lst in KB'. cbnR.
      eapply KB'; [reflexivity| reflexivity|]. unfold rd_brk_ok. cbnR. change (2^31) with 2147483648. lia.
    - replace (msv1 <=? cn + 3 * rep + Z.land bs2 3) with false in RR by (symmetry; apply Z.leb_gt; lia).
      destruct (reload buf (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)) as [s3| | |] eqn:RL;
        cbn [bind] in RR; try discriminate RR. injection RR as <-.
      pose proof (fun y1 y6 y13 y14 y16 y28 => zero_reload (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)
                                  s3 m1 msvw tlw y1 y6 y13 y14 y16 y28 INV RL) as ZR. cbnR. unfold rd_lst in ZR.
      eapply ZR; try lia.
      intros y6 y27. apply KC; [reflexivity|].
      pose proof (reload_inv buf _ s3 (buf_all_bytes C OK) RL) as RI. cbnR. cbv zeta in RI.
      destruct (RI ltac:(lia) ltac:(unfold FseNCount.Zlength; lia) ltac:(lia)) as (_ & _ & _ & ->). reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma zero_run : forall tl s m1 msvw tlw fl (x1 x6 x14 x16 x28 : word),
    5 <= tl <= 15 ->
    rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    rzero_block buf msv1 s = Ok fl ->
    (forall s' y1 y6 y13 y14 y16 y25 y28 y29, fl = Brk s' -> r_nc s' = r_nc s -> rd_brk_ok C s' ->
        evt usegs POST (rd_exit C s' m1 y1 y6 y13 y14 y16 y25 y28 y29)) ->
    (forall s' y6 y27, fl = Cont s' -> r_nc s' = r_nc s -> evt usegs POST (rd_cnt C s' m1 y6 y27)) ->
    evt usegs POST (rd_lst C 0x29e80 m1 x1 x6 (Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s)))
                      x14 x16 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (r_bitCount s))
                      (Z_to_bv 64 (BUF + r_ip s)) x28 (Z_to_bv 64 (r_nbBits s))).
  Proof.
    intros tl s m1 msvw tlw fl x1 x6 x14 x16 x28 Htl INV HC HP HB32 RR KB KC.
    destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
    pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
    unfold rzero_block in RR. rewrite (repeats_of_ctzv _ Rbs) in RR. cbn [bind] in RR.
    destruct (rep_loop buf (S (Z.to_nat (FseNCount.Zlength buf))) s (ctzv (r_bitStream s) / 2)) as [[s1 rep1]| | |] eqn:RLP;
      cbn [bind] in RR; try discriminate RR.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))))) as MI.
    eapply zero_ctz1; [exact Rbs| exact MI|].
    eapply (zero_rep _ s _ s1 rep1 m1 msvw tlw 0x29eac); try exact RLP; try exact INV; try lia; try reflexivity;
      try (left; split; reflexivity).
    { unfold FseNCount.Zlength. change (2^30) with 1073741824. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
    intros z16 z28 Hbs1 Hip0 Hip4 Hbc1 Hcn1 Erep1 Hrep1 (E1 & E2 & E3 & E4 & E5).
    rewrite <- E2, <- E3, <- E4.
    eapply (zero_tail s1 m1 msvw tlw fl); try eassumption; try lia.
    - rewrite E1. exact INV.
    - cbv zeta. rewrite <- Erep1. exact RR.
    - intros s' y1 y6 y13 y14 y16 y25 y28 y29 EF EN BK. apply KB; [exact EF| rewrite EN; exact E1| exact BK].
    - intros s' y6 y27 EF EN. apply KC; [exact EF| rewrite EN; exact E1].
  Qed.
End Zero.

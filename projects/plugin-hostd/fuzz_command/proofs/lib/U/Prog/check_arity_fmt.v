From Stdlib Require Import ZArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandTac check_reply_c strcmp_c strcspn_c strncmp_c bcmp_c check_arity_c check_arity_lib.
Import ListNotations.
Open Scope Z_scope.

Section Fmt.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (A : Z) (SS : list byte) (m0 : word -> option byte)
    (lo : Z) (saved : list cell) (xs2 : word).
  Hypothesis HSn : ~ In NUL SS.
  Hypothesis LSS : Z.of_nat (length SS) <= 128.
  Hypothesis AP : 0 < A.
  Hypothesis AL : A + Z.of_nat (length SS) + 1 <= lo.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis LOS : lo + 144 <= bv_unsigned sp.
  Hypothesis BC : bcmp_contract.

  Lemma fa_top : A + Z.of_nat (length SS) + 145 <= 2^64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2^64) in R. lia. Qed.

  Abbreviation SG pc xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 m :=
    (SGU sp gp tp F fc pc xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         xt3 xt4 xt5 xt6 m).

  Lemma fskipA : forall n k m xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7
                        xt3 xt4 xt5 xt6,
    (length SS - k < n)%nat -> (k <= length SS)%nat -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists k', (k <= k' <= length SS)%nat /\ skipn k' SS = skip_sp (skipn k SS) /\
                 bz (hd NUL (skipn k' SS)) <> 32 /\
                 ms' = SG 0x14794 xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (zxb (hd NUL (skipn k' SS))) xt1 xt2
                          (Z_to_bv 64 (A + Z.of_nat k')) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) xa3 xa4 xa5 xa6 xa7
                          xt3 xt4 xt5 xt6 m)
      (SG 0x14780 xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
          (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k m xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 HN HK HB; [lia|].
    pose proof fa_top as TOP.
    pose proof (ca_rd_hd m A SS k HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn k SS))) as BR.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists k. split; [lia|]. split.
      + rewrite (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact C | reflexivity].
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS k ltac:(lia)) as LT.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep.
      replace (A + Z.of_nat k + 1) with (A + Z.of_nat (S k)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact HB] |].
      intros ms' (k' & Hk' & Hs & Hb & E). exists k'. split; [lia|]. split.
      + rewrite Hs, (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma fscanB : forall n q d m xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt1 xt2 xt3 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists yt0 ya0 ya2,
                 ms' = SG 0x14a4c xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10
                          (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS)))) yt0 xt1 xt2 ya0 (Z_to_bv 64 91) ya2
                          (Z_to_bv 64 (-1)) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) (Z_to_bv 64 32)
                          xt3 xt4 xt5 xt6 m)
      (SG 0x147b4 xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (zxb (hd NUL (skipn q SS))) xt1 xt2
          (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 91) (Z_to_bv 64 d) (Z_to_bv 64 (-1)) (Z_to_bv 64 62) (Z_to_bv 64 60)
          (Z_to_bv 64 93) (Z_to_bv 64 32) xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt1 xt2 xt3 xt4 xt5 xt6
      HN HQ HD NZ HB; [lia|].
    pose proof fa_top as TOP.
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d' yt0, 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SG 0x147ec xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt0 xt1 xt2
          (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 91) (Z_to_bv 64 d') (Z_to_bv 64 (-1)) (Z_to_bv 64 62) (Z_to_bv 64 60)
          (Z_to_bv 64 93) (Z_to_bv 64 32) xt3 xt4 xt5 xt6 m)).
    { intros d' yt0 HD' Ed' NS.
      assert (IL : ilen d (skipn q SS) = S (ilen d' (skipn (S q) SS))).
      { rewrite (ca_hd_skipn_S SS q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (ca_rd_hd m A SS (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) SS))) as BR1.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (yt0' & ya0 & ya2 & E). subst ms'. unfold POSTQ. exists yt0', ya0, ya2.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        reflexivity.
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia. reflexivity. }
    assert (INC : bv_unsigned (hd NUL (skipn q SS)) = 60 \/ bv_unsigned (hd NUL (skipn q SS)) = 91 ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SG 0x147c8 xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (zxb (hd NUL (skipn q SS))) xt1 xt2
          (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 91) (Z_to_bv 64 d) (Z_to_bv 64 (-1)) (Z_to_bv 64 62) (Z_to_bv 64 60)
          (Z_to_bv 64 93) (Z_to_bv 64 32) xt3 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. rewrite ca_swrap32_id by lia.
      zstep. if_cases Ho.
      { exfalso. zify_cond Ho. try rewrite !ca_signed_small in Ho by lia. lia. }
      zstep. zstep.
      apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SG 0x147bc xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (zxb (hd NUL (skipn q SS))) xt1 xt2
          (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 91) (Z_to_bv 64 d) (Z_to_bv 64 (-1)) (Z_to_bv 64 62) (Z_to_bv 64 60)
          (Z_to_bv 64 93) (Z_to_bv 64 32) xt3 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. apply INC; [lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. zstep. if_cases Hc4.
          * zify_cond Hc4. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc4. pos_false_tac. zstep.
            apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. apply INC; [lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. zstep. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Abbreviation LS pc xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xt3 xt4 xt5 xt6 m :=
    (SG pc xra (Z_to_bv 64 67124) xs1 xs3 (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 91) (Z_to_bv 64 62)
        (Z_to_bv 64 60) xs9 (Z_to_bv 64 2147483647) xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 93) xa6 xa7
        xt3 xt4 xt5 xt6 m).

  Lemma fskipC : forall n k m xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa2 xa3 xa4 xa6 xa7 xt3 xt4 xt5 xt6,
    (length SS - k < n)%nat -> (k <= length SS)%nat -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists k', (k <= k' <= length SS)%nat /\ skipn k' SS = skip_sp (skipn k SS) /\
                 bz (hd NUL (skipn k' SS)) <> 32 /\
                 ms' = LS 0x14aac xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat k'))
                          (Z_to_bv 64 (A + Z.of_nat k' + 3)) xa2 xa3 (zxb (hd NUL (skipn k' SS))) xa6 xa7
                          xt3 xt4 xt5 xt6 m)
      (LS 0x14a94 xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 (A + Z.of_nat k + 3))
          xa2 xa3 xa4 xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k m xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa2 xa3 xa4 xa6 xa7 xt3 xt4 xt5 xt6 HN HK HB; [lia|].
    pose proof fa_top as TOP.
    pose proof (ca_rd_hd m A SS k HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn k SS))) as BR.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists k. split; [lia|]. split.
      + rewrite (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact C | reflexivity].
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS k ltac:(lia)) as LT.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep. zstep.
      replace (A + Z.of_nat k + 4) with (A + Z.of_nat (S k) + 3) by lia.
      replace (A + Z.of_nat k + 1) with (A + Z.of_nat (S k)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact HB] |].
      intros ms' (k' & Hk' & Hs & Hb & E). exists k'. split; [lia|]. split.
      + rewrite Hs, (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma fscanD : forall n q d m xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa0 xa1 xa6 xa7 xt3 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya2 ya3 ya4,
                 ms' = LS 0x14b0c xra xs1 xs3 xs9 (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS)))) xt0 xt1 xt2
                          xa0 xa1 ya2 ya3 ya4 xa6 xa7 xt3 xt4 xt5 xt6 m)
      (LS 0x14ab8 xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
          (zxb (hd NUL (skipn q SS))) xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa0 xa1 xa6 xa7 xt3 xt4 xt5 xt6
      HN HQ HD NZ HB; [lia|].
    pose proof fa_top as TOP.
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d' ya4, 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14af0 xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d')
          ya4 xa6 xa7 xt3 xt4 xt5 xt6 m)).
    { intros d' ya4 HD' Ed' NS.
      assert (IL : ilen d (skipn q SS) = S (ilen d' (skipn (S q) SS))).
      { rewrite (ca_hd_skipn_S SS q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (ca_rd_hd m A SS (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) SS))) as BR1.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (ya2 & ya3 & ya4' & E). subst ms'. unfold POSTQ. exists ya2, ya3, ya4'.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        reflexivity.
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia. reflexivity. }
    assert (INC : bv_unsigned (hd NUL (skipn q SS)) = 60 \/ bv_unsigned (hd NUL (skipn q SS)) = 91 ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14acc xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
          (zxb (hd NUL (skipn q SS))) xa6 xa7 xt3 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. rewrite ca_swrap32_id by lia.
      zstep. if_cases Ho.
      { exfalso. zify_cond Ho. try rewrite !ca_signed_small in Ho by lia. lia. }
      zstep. zstep.
      apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14ac0 xra xs1 xs3 xs9 xs11 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
          (zxb (hd NUL (skipn q SS))) xa6 xa7 xt3 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. apply INC; [lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. zstep. if_cases Hc4.
          * zify_cond Hc4. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc4. pos_false_tac. zstep.
            apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. apply INC; [lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. zstep. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Ltac uinv_tac := unfold uinv; repeat (lazymatch goal with |- _ /\ _ => split | |- ex _ => eexists end); eassumption.

  Lemma fmtloop : forall f k mn mx rmn rmx m xra xs1 xs3 xt0 xt1 xt2 xa0 xa3 xa4 xa6 xa7 xt3 xt4 xt5 xt6,
    (length SS - k <= f)%nat -> (k <= length SS)%nat -> 0 <= mn -> mn + Z.of_nat (length SS - k) <= 2^20 ->
    (mx = UNB \/ 0 <= mx /\ mx + Z.of_nat (length SS - k) <= 2^20) ->
    format_arity_items (items_f f (skipn k SS)) mn mx = (rmn, rmx) -> uinv sp m0 lo saved A SS m ->
    evt rsegs (upost sp gp tp F fc m0 lo saved A SS rmn rmx xs2)
      (LS 0x14a84 xra xs1 xs3 (Z_to_bv 64 mn) (Z_to_bv 64 (A + Z.of_nat k)) xt0 xt1 xt2 xa0 (Z_to_bv 64 mx)
          (Z_to_bv 64 mx) xa3 xa4 xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    pose proof BC as BC'. unfold bcmp_contract in BC'.
    pose proof fa_top as TOP.
    intros f. induction f as [f IH] using (well_founded_induction lt_wf).
    intros k mn mx rmn rmx m xra xs1 xs3 xt0 xt1 xt2 xa0 xa3 xa4 xa6 xa7 xt3 xt4 xt5 xt6 Hf Hk Hmn0 Hmn Hmx Hres INV.
    pose proof INV as (MI & (j & FR) & ST & MU & WM & HB).
    assert (Rmx : 0 <= mx <= 2147483647) by (unfold UNB in Hmx; lia).
    zstep. zstep. zstep. zstep.
    eapply evt_cut; [eapply (fskipC (S (length SS - k)) k m); [lia | lia | exact HB] |].
    intros ms1 (k1 & Hk1 & Hsk & Hsp & ->).
    zstep. if_cases Z1.
    - zify_cond Z1.
      pose proof (ca_hd_z_end SS k1 HSn ltac:(lia) Z1) as E1.
      rewrite (items_f_nil f (skipn k SS)) in Hres by (rewrite <- Hsk, E1, skipn_all; reflexivity).
      cbn [format_arity_items] in Hres. injection Hres as <- <-.
      zstep. apply evt_done. unfold upost. do 26 eexists. split; [exact INV | reflexivity].
    - zify_cond Z1.
      assert (LT1 : (k1 < length SS)%nat) by (apply (ca_hd_nz_lt SS k1); lia).
      destruct f as [|f']; [lia|].
      rewrite (items_f_step f' SS k k1 Hsk LT1) in Hres.
      zstep. zstep.
      eapply evt_cut; [eapply (fscanD (S (length SS - k1)) k1 0 m); [lia | lia | lia | exact Z1 | exact HB] |].
      intros ms2 (ya2 & ya3 & ya4 & ->).
      assert (NE1 : skipn k1 SS <> []).
      { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
      pose proof (ilen_pos (skipn k1 SS) Hsp NE1) as HL1.
      pose proof (ilen_le 0 (skipn k1 SS)) as HL2. rewrite length_skipn in HL2.
      set (L := ilen 0 (skipn k1 SS)) in *.
      cbn [format_arity_items] in Hres.
      assert (CNT : forall m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa6' xa7' xt3' xt4' xt5' xt6',
        uinv sp m0 lo saved A SS m' ->
        format_arity_items (items_f f' (skipn (k1 + L) SS)) (mn + 1) (bump mx) = (rmn, rmx) ->
        evt rsegs (upost sp gp tp F fc m0 lo saved A SS rmn rmx xs2)
          (LS 0x14b2c xra' (Z_to_bv 64 mx) (Z_to_bv 64 mx) (Z_to_bv 64 mn) (Z_to_bv 64 (A + Z.of_nat (k1 + L)))
              xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa6' xa7' xt3' xt4' xt5' xt6' m')).
      { intros m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa6' xa7' xt3' xt4' xt5' xt6' INV' HR.
        zstep. rewrite ca_swrap32_id by lia.
        zstep. if_cases O1.
        { exfalso. zify_cond O1. try rewrite !ca_signed_small in O1 by lia. lia. }
        zstep. zstep. if_cases C3.
        + zify_cond C3.
          zstep. if_cases N4.
          { exfalso. zify_cond N4. lia. }
          zstep. zstep. zstep. zstep.
          assert (MXU : mx = UNB) by (unfold UNB; lia). subst mx.
          change (bump UNB) with UNB in HR.
          eapply (IH f' ltac:(lia) (k1 + L)%nat (mn + 1) UNB rmn rmx m');
            [lia | lia | lia | lia | left; reflexivity | exact HR | exact INV'].
        + zify_cond C3. rewrite ca_swrap32_id by lia.
          zstep. zstep. if_cases N4.
          2:{ exfalso. zify_cond N4. lia. }
          zstep. zstep. zstep.
          unfold bump in HR. rewrite (proj2 (Z.eqb_neq mx UNB)) in HR by (unfold UNB; lia).
          eapply (IH f' ltac:(lia) (k1 + L)%nat (mn + 1) (mx + 1) rmn rmx m');
            [lia | lia | lia | lia | right; unfold UNB in Hmx; lia | exact HR | exact INV']. }
      zstep. if_cases Y1.
      + zify_cond Y1.
        rewrite (ca_bytes_eqb_len (firstn L (skipn k1 SS)) (str [46; 46; 46])) in Hres
          by (rewrite length_firstn, length_skipn; unfold str; cbn [length map]; lia).
        eapply CNT; [exact INV | exact Hres].
      + zify_cond Y1.
        assert (L3 : L = 3%nat) by lia.
        zstep. zstep. zstep.
        pose proof (lit_at m 67124 (str [46; 46; 46] ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(lia)
                      ltac:(cbn; lia)) as HD.
        destruct (ca_memcmp_eq 3 (skipn k1 (SS ++ [NUL])) (str [46; 46; 46] ++ [NUL])) as (vv & Hv & Hv0);
          [rewrite length_skipn, length_app; cbn [length]; lia | cbn; lia |].
        pose proof (ca_memcmp_range _ _ _ _ Hv) as VR.
        assert (FW : firstn 3 (skipn k1 (SS ++ [NUL])) = firstn L (skipn k1 SS)).
        { rewrite L3, skipn_app. replace (k1 - length SS)%nat with 0%nat by lia. cbn [skipn].
          rewrite firstn_app, length_skipn. replace (3 - (length SS - k1))%nat with 0%nat by lia.
          rewrite firstn_O, app_nil_r. reflexivity. }
        eapply evt_cut.
        { eapply BC' with (ls := skipn k1 (SS ++ [NUL])) (rs := str [46; 46; 46] ++ [NUL]) (v := vv).
          - rewrite unsigned_lit by lia. apply bytes_at_skipn; [exact HB | rewrite length_app; cbn [length]; lia].
          - rewrite unsigned_lit by lia. exact HD.
          - exact Hv.
          - exact MI. }
        intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MU1 & WM1 & MI1 & HB1 & HB2).
        subst ms'. clear HB1 HB2 HD INV.
        transport_after_call rsegs m m1 MU1 WM1.
        clear MU1 WM1 MI.
        fix_ret.
        zstep. zstep. zstep. zstep. if_cases Z2.
        * zify_cond Z2.
          assert (V0 : vv = 0) by (Z.div_mod_to_equations; lia).
          apply Hv0 in V0. rewrite FW in V0.
          assert (EB : bytes_eqb (firstn L (skipn k1 SS)) (str [46; 46; 46]) = true) by (apply bytes_eqb_iff; exact V0).
          rewrite EB in Hres.
          eapply (IH f' ltac:(lia) (k1 + L)%nat mn UNB rmn rmx m1);
            [lia | lia | lia | lia | left; reflexivity | exact Hres | uinv_tac].
        * zify_cond Z2.
          assert (VN : vv <> 0) by (intros ->; apply Z2; reflexivity).
          assert (EB : bytes_eqb (firstn L (skipn k1 SS)) (str [46; 46; 46]) = false).
          { destruct (bytes_eqb (firstn L (skipn k1 SS)) (str [46; 46; 46])) eqn:EB; [|reflexivity].
            exfalso. apply VN, Hv0. rewrite FW. apply bytes_eqb_iff in EB. rewrite EB. reflexivity. }
          rewrite EB in Hres.
          eapply CNT; [uinv_tac | exact Hres].
  Qed.

  Lemma fmt_path : forall m rmn rmx xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6
                          xa7 xt3 xt4 xt5 xt6,
    uinv sp m0 lo saved A SS m -> row_arity SS 1 = (rmn, rmx) ->
    evt rsegs (upost sp gp tp F fc m0 lo saved A SS rmn rmx xs2)
      (SG 0x14770 xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 A) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
          xt3 xt4 xt5 xt6 m).
  Proof.
    intros m rmn rmx xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 INV HR.
    pose proof INV as (MI & FR & ST & MU & WM & HB).
    pose proof fa_top as TOP.
    unfold row_arity in HR. cbn [Z.eqb] in HR.
    zstep. if_cases NA.
    { exfalso. zify_cond NA. lia. }
    zstep. zstep. zstep.
    replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + Z.of_nat 0)) by (f_equal; lia).
    eapply evt_cut; [eapply (fskipA (S (length SS)) 0 m); [lia | lia | exact HB] |].
    intros ms1 (k1 & Hk1 & Hsk & Hsp & ->).
    zstep. if_cases Z1.
    - zify_cond Z1.
      pose proof (ca_hd_z_end SS k1 HSn ltac:(lia) Z1) as E1.
      assert (NIL : shape_items SS = []).
      { unfold shape_items. apply items_f_nil. change SS with (skipn 0 SS) at 1. rewrite <- Hsk, E1, skipn_all. reflexivity. }
      rewrite NIL in HR. injection HR as <- <-.
      do 14 zstep.
      eapply (fmtloop (length SS) 0 0 0 0 0 m); [lia | lia | lia | lia | right; lia | | exact INV].
      change (items_f (length SS) (skipn 0 SS)) with (shape_items SS). rewrite NIL. reflexivity.
    - zify_cond Z1.
      assert (LT1 : (k1 < length SS)%nat) by (apply (ca_hd_nz_lt SS k1); lia).
      pose proof (items_f_step (length SS - 1) SS 0 k1 Hsk LT1) as IS.
      change (skipn 0 SS) with SS in IS. replace (S (length SS - 1)) with (length SS) in IS by lia.
      unfold shape_items in HR. rewrite IS in HR. cbv iota in HR.
      do 7 zstep.
      eapply evt_cut; [eapply (fscanB (S (length SS - k1)) k1 0 m); [lia | lia | lia | exact Z1 | exact HB] |].
      intros ms2 (yt0 & ya0 & ya2 & ->).
      assert (NE1 : skipn k1 SS <> []).
      { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
      pose proof (ilen_pos (skipn k1 SS) Hsp NE1) as HL1.
      pose proof (ilen_le 0 (skipn k1 SS)) as HL2. rewrite length_skipn in HL2.
      set (L := ilen 0 (skipn k1 SS)) in *.
      do 14 zstep.
      eapply (fmtloop (length SS - 1) (k1 + L) 0 0 rmn rmx m);
        [lia | lia | lia | lia | right; lia | exact HR | exact INV].
  Qed.

End Fmt.

Theorem fmt_path_holds : bcmp_contract -> fmt_path_spec.
Proof.
  intros BC. unfold fmt_path_spec, path_spec.
  intros sp gp tp F fc A SS m0 lo saved HSn LSS AP AL LO0 LOS m rmn rmx xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10
    xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 INV HR.
  eapply fmt_path; eassumption.
Qed.

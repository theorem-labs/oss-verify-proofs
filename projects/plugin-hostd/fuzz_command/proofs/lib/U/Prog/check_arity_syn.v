From Stdlib Require Import ZArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandTac check_reply_c strcmp_c strcspn_c strncmp_c bcmp_c check_arity_c check_arity_lib.
Import ListNotations.
Open Scope Z_scope.

Definition item_upd (it : list byte) (mn mx : Z) : Z * Z :=
  if bracketed it then (if has_dots it then (mn, UNB) else (mn, bump mx)) else (mn + 1, bump mx).

Lemma arity_items_nb : forall it rest mn mx, bytes_eqb it (str [124]) = false ->
  arity_items (it :: rest) mn mx = arity_items rest (fst (item_upd it mn mx)) (snd (item_upd it mn mx)).
Proof.
  intros it rest mn mx H. cbn [arity_items]. rewrite H. unfold item_upd.
  destruct (bracketed it); [destruct (has_dots it)|]; reflexivity.
Qed.

Lemma item_upd_cases : forall it mn mx mn' mx', (mn', mx') = item_upd it mn mx ->
  (mn' = mn \/ mn' = mn + 1) /\ (mx' = UNB \/ mx' = bump mx).
Proof.
  intros it mn mx mn' mx' E. unfold item_upd in E.
  destruct (bracketed it); [destruct (has_dots it)|]; injection E as -> ->; tauto.
Qed.

Lemma bump_cases : forall mx, (mx = UNB /\ bump mx = UNB) \/ (mx <> UNB /\ bump mx = mx + 1).
Proof.
  intros mx. unfold bump. destruct (Z.eqb_spec mx UNB) as [E|E]; [left; split; [exact E | exact E] | right; tauto].
Qed.

Section USyn.
  Variables (sp gp tp r2 : word) (F : bvmap 5 word) (fc : bv 32) (A : Z) (SS : list byte)
            (m0 : word -> option byte) (lo : Z) (saved : list cell).
  Hypothesis HSn : ~ In NUL SS.
  Hypothesis LSS : Z.of_nat (length SS) <= 128.
  Hypothesis A0 : 0 < A.
  Hypothesis AL : A + Z.of_nat (length SS) + 1 <= lo.
  Hypothesis LO : 0 <= lo.
  Hypothesis LSP : lo + 144 <= bv_unsigned sp.
  Hypothesis RSP : bv_unsigned sp < 2^64.

  Abbreviation LB pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 xs11 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             r2 xs3 (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93)
             xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Abbreviation LS pc xra xs0 mn mx xa0 xa1 xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m :=
    (LB pc xra (Z_to_bv 64 3) (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 2147483647) xs0 (Z_to_bv 64 mx)
        xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 mn) (Z_to_bv 64 124) xs3 xs10 xs11 (Z_to_bv 64 mx) xt4 xt5 xt6 m).

  Lemma skipA : forall n i k p m xra mn mx xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6,
    (length SS - p < n)%nat -> p = (k + i)%nat -> (p <= length SS)%nat -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists p', (p <= p' <= length SS)%nat /\ skipn p' SS = skip_sp (skipn p SS) /\
                 bz (hd NUL (skipn p' SS)) <> 32 /\
                 ms' = LS 0x14864 xra (Z_to_bv 64 (A + Z.of_nat p')) mn mx (Z_to_bv 64 (A + Z.of_nat k))
                          (Z_to_bv 64 (Z.of_nat (p' - k))) (zxb (hd NUL (skipn p' SS))) (Z_to_bv 64 (A + Z.of_nat p'))
                          xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m)
      (LS 0x14848 xra (Z_to_bv 64 (A + Z.of_nat p)) mn mx (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 (Z.of_nat i))
          xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros i k p m xra mn mx xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 HN HP HK HB; [lia|].
    pose proof (ca_rd_hd m A SS p HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn p SS))) as BR.
    zstep.
    replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat p) by lia.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists p. split; [lia|]. split.
      + rewrite (ca_skip_sp_at SS p HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn p SS))) 32) C). reflexivity.
      + split; [exact C|]. replace (p - k)%nat with i by lia.
        reflexivity.
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS p ltac:(lia)) as LT.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep. zstep.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      replace (A + Z.of_nat p + 1) with (A + Z.of_nat (S p)) by lia.
      eapply evt_mono; [eapply (IH (S i) k (S p)); [lia | lia | lia | exact HB] |].
      intros ms' (p' & Hp' & Hs & Hb & E). exists p'. split; [lia|]. split.
      + rewrite Hs, (ca_skip_sp_at SS p HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn p SS))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma scanB : forall n q d m xra xs0 mn mx xa0 xa1 xa2 xs3 xs10 xs11 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya3 ya4 ya5,
                 ms' = LS 0x148c4 xra xs0 mn mx xa0 xa1 xa2 ya3 ya4 ya5 xs3 xs10
                          (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS)))) xt4 xt5 xt6 m)
      (LS 0x14870 xra xs0 mn mx xa0 xa1 xa2 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d) (zxb (hd NUL (skipn q SS)))
          xs3 xs10 xs11 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xs0 mn mx xa0 xa1 xa2 xs3 xs10 xs11 xt4 xt5 xt6 HN HQ HD NZ HB; [lia|].
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d' ya5, 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x148a8 xra xs0 mn mx xa0 xa1 xa2 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d') ya5
                          xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros d' ya5 HD' Ed' NS.
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
        intros ms' (ya3 & ya4 & ya5' & E). subst ms'. unfold POSTQ. exists ya3, ya4, ya5'.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        reflexivity.
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia. reflexivity. }
    assert (INC : bv_unsigned (hd NUL (skipn q SS)) = 60 \/ bv_unsigned (hd NUL (skipn q SS)) = 91 ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14884 xra xs0 mn mx xa0 xa1 xa2 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q SS))) xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. rewrite ca_swrap32_id by lia.
      zstep. if_cases Ho.
      { exfalso. zify_cond Ho. try rewrite !ca_signed_small in Ho by lia. lia. }
      zstep. zstep.
      apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    assert (CLS : bv_unsigned (hd NUL (skipn q SS)) = 62 ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14894 xra xs0 mn mx xa0 xa1 xa2 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q SS))) xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. if_cases Hb.
      - zify_cond Hb. zstep. rewrite ca_swrap32_id by lia.
        apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
      - zify_cond Hb. try pos_false_tac. zstep.
        apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS]. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14878 xra xs0 mn mx xa0 xa1 xa2 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q SS))) xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. apply INC; [lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. apply CLS; [lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. try pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. apply INC; [lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. try pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. zstep. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Lemma skipC : forall n p m xra xs0 mn mx xa0 xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6,
    (length SS - p < n)%nat -> (p <= length SS)%nat -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists p', (p <= p' <= length SS)%nat /\ skipn p' SS = skip_sp (skipn p SS) /\
                 bz (hd NUL (skipn p' SS)) <> 32 /\
                 ms' = LS 0x148ec xra xs0 mn mx xa0 (Z_to_bv 64 (A + Z.of_nat p')) xa2 (zxb (hd NUL (skipn p' SS)))
                          xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m)
      (LS 0x148d8 xra xs0 mn mx xa0 (Z_to_bv 64 (A + Z.of_nat p)) xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros p m xra xs0 mn mx xa0 xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 HN HK HB; [lia|].
    pose proof (ca_rd_hd m A SS p HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn p SS))) as BR.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists p. split; [lia|]. split.
      + rewrite (ca_skip_sp_at SS p HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn p SS))) 32) C). reflexivity.
      + split; [exact C | reflexivity].
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS p ltac:(lia)) as LT.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep.
      replace (A + Z.of_nat p + 1) with (A + Z.of_nat (S p)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact HB] |].
      intros ms' (p' & Hp' & Hs & Hb & E). exists p'. split; [lia|]. split.
      + rewrite Hs, (ca_skip_sp_at SS p HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn p SS))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma scanD : forall n q d m xra xs0 mn mx xa0 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya1 ya2 ya3,
                 ms' = LS 0x14840 xra xs0 mn mx (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS)))) ya1 ya2 ya3
                          xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m)
      (LS 0x148f8 xra xs0 mn mx xa0 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d) (zxb (hd NUL (skipn q SS)))
          xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xs0 mn mx xa0 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 HN HQ HD NZ HB; [lia|].
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d' ya0, 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14930 xra xs0 mn mx ya0 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d')
                          (zxb (hd NUL (skipn q SS))) xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros d' ya0 HD' Ed' NS.
      assert (IL : ilen d (skipn q SS) = S (ilen d' (skipn (S q) SS))).
      { rewrite (ca_hd_skipn_S SS q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (ca_rd_hd m A SS (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) SS))) as BR1.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia. reflexivity.
      - zify_cond C. zstep.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (ya1 & ya2 & ya3 & E). subst ms'. unfold POSTQ. exists ya1, ya2, ya3.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        reflexivity. }
    assert (INC : bv_unsigned (hd NUL (skipn q SS)) = 60 \/ bv_unsigned (hd NUL (skipn q SS)) = 91 ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x1490c xra xs0 mn mx xa0 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q SS))) xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. rewrite ca_swrap32_id by lia.
      zstep. if_cases Ho.
      { exfalso. zify_cond Ho. try rewrite !ca_signed_small in Ho by lia. lia. }
      zstep. zstep.
      apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    assert (CLS : bv_unsigned (hd NUL (skipn q SS)) = 62 ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x1491c xra xs0 mn mx xa0 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q SS))) xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. if_cases Hb.
      - zify_cond Hb. zstep. rewrite ca_swrap32_id by lia.
        apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
      - zify_cond Hb. try pos_false_tac. zstep.
        apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS]. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x14900 xra xs0 mn mx xa0 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q SS))) xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. apply INC; [lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. apply CLS; [lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. try pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. apply INC; [lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. try pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. zstep. zstep. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Hypothesis BC : bcmp_contract.

  Ltac pre_of cs tl :=
    lazymatch cs with
    | tl => constr:(@nil cell)
    | ?c :: ?r => let p := pre_of r tl in constr:(c :: p)
    end.

  Ltac uinv_tac :=
    match goal with FR : rw_cells rsegs ?mm (bv_unsigned sp + -144) ?cs |- _ =>
      let mid := pre_of cs saved in
      let M := fresh "M" in
      pose proof (rw_cells_merge rsegs mm (bv_unsigned sp + -144) [] mid saved FR) as M;
      cbn [app cells_size csize Nat.add] in M;
      unfold uinv; refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); first [eassumption | eexists; exact M]
    end.

  Ltac inv6 := refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
    first [eassumption | eexists; eassumption | do 2 eexists; eassumption].

  Definition dinv (mn mx L : Z) (m : word -> option byte) : Prop :=
    mem_inv rsegs m /\
    (exists j0, rw_cells rsegs m (bv_unsigned sp + -144)
       (CB 8 j0 :: C8 (Z_to_bv 64 mx) :: C8 (Z_to_bv 64 mn) :: C8 (Z_to_bv 64 2147483647) :: C8 (Z_to_bv 64 L) :: saved)) /\
    stk rsegs m lo (bv_unsigned sp + -144) /\ munch [(lo, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\
    bytes_at rsegs m A (SS ++ [NUL]).

  Definition ninv (m : word -> option byte) : Prop :=
    mem_inv rsegs m /\
    (exists j1 j2, rw_cells rsegs m (bv_unsigned sp + -144) (CB 24 j1 :: C8 (Z_to_bv 64 2147483647) :: CB 8 j2 :: saved)) /\
    stk rsegs m lo (bv_unsigned sp + -144) /\ munch [(lo, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\
    bytes_at rsegs m A (SS ++ [NUL]).

  Definition dpost (hb : bool) (mn mx L : Z) (xs11 : word) (ms' : machine_state) : Prop :=
    exists m' xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 xt3 xt4 xt5 xt6,
      dinv mn mx L m' /\
      ((hb = true /\ ms' = LB 0x149f8 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 mx) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 xs11
                                xt3 xt4 xt5 xt6 m') \/
       (hb = false /\ ms' = LB 0x149c4 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 mx) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 xs11
                                xt3 xt4 xt5 xt6 m')).

  Lemma dots_loop : forall n i p q L hb mn mx m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs11 xt3 xt4 xt5 xt6,
    (L - i < n)%nat -> q = (p + i)%nat -> (i + 3 <= L)%nat -> (p + L <= length SS)%nat ->
    bv_unsigned xs3 = 2^64 - 1 - (A + Z.of_nat p) ->
    has_dots (skipn i (firstn L (skipn p SS))) = hb -> dinv mn mx (Z.of_nat L) m ->
    evt rsegs (dpost hb mn mx (Z.of_nat L) xs11)
      (LB 0x14994 xra xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 mx) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3
          (Z_to_bv 64 (Z.of_nat i)) xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    pose proof BC as BC'. unfold bcmp_contract in BC'.
    induction n as [|n IH]; intros i p q L hb mn mx m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs11 xt3 xt4 xt5 xt6
      HN HQ HI HP HS3 HH INV; [lia|].
    destruct INV as (MI & [j0 FR] & ST & MU & WM & HB).
    destruct (win3 SS p i L HI HP) as [W3 L3].
    rewrite (has_dots_window _ L3), <- skipn_S_tl, W3 in HH.
    pose proof (lit_at m 67124 (str [46; 46; 46] ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HD.
    destruct (ca_memcmp_eq 3 (skipn (p + i) (SS ++ [NUL])) (str [46; 46; 46] ++ [NUL])) as (vv & Hv & Hv0);
      [rewrite length_skipn, length_app; cbn [length]; lia | cbn; lia |].
    pose proof (ca_memcmp_range _ _ _ _ Hv) as VR.
    zstep. if_cases T.
    { exfalso. zify_cond T. lia. }
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply BC' with (ls := skipn (p + i) (SS ++ [NUL])) (rs := str [46; 46; 46] ++ [NUL]) (v := vv).
      - match goal with |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 ?e)) _ =>
          rewrite (unsigned_lit e) by lia; replace e with (A + Z.of_nat (p + i)) by lia end.
        apply bytes_at_skipn; [exact HB | rewrite length_app; cbn [length]; lia].
      - rewrite unsigned_lit by lia. exact HD.
      - exact Hv.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                E & MU1 & WM1 & MI1 & HB1 & HB2).
    subst ms'. clear HB1 HB2 HD.
    transport_after_call rsegs m m1 MU1 WM1.
    clear MU1 WM1 MI.
    fix_ret.
    zstep. if_cases Z1.
    - zify_cond Z1.
      assert (V0 : vv = 0) by (Z.div_mod_to_equations; lia).
      apply evt_done. unfold dpost. do 20 eexists. split; [unfold dinv; inv6|]. left. split; [|reflexivity].
      rewrite <- HH. apply Hv0 in V0. rewrite V0. reflexivity.
    - zify_cond Z1.
      assert (VN : vv <> 0) by (intros ->; apply Z1; reflexivity).
      assert (HH' : has_dots (skipn (S i) (firstn L (skipn p SS))) = hb).
      { rewrite <- HH. destruct (bytes_eqb (firstn 3 (skipn (p + i) (SS ++ [NUL]))) (str [46; 46; 46])) eqn:EB; [|reflexivity].
        exfalso. apply VN, Hv0. apply bytes_eqb_iff in EB. rewrite EB. reflexivity. }
      zstep. zstep. zstep. zstep. zstep. if_cases Z2.
      + zify_cond Z2.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
        apply (IH (S i) p (S q)); [lia | lia | lia | lia | exact HS3 | exact HH' | unfold dinv; inv6].
      + zify_cond Z2. apply evt_done. unfold dpost. do 20 eexists. split; [unfold dinv; inv6|]. right. split; [|reflexivity].
        rewrite <- HH'. apply has_dots_short. rewrite length_skipn, length_firstn, length_skipn. lia.
  Qed.

  Lemma seg_found : forall (Q : machine_state -> Prop) e mn mx L m xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                           xs3 xs10 xt3 xt4 xt5 xt6,
    dinv mn mx L m ->
    (forall m', uinv sp m0 lo saved A SS m' ->
       evt rsegs Q (LS 0x14840 xra xs0 mn 2147483647 (Z_to_bv 64 e) xa1 xa2 xa3 xa4 xa5 xs3 xs10 (Z_to_bv 64 e)
                       xt4 xt5 xt6 m')) ->
    evt rsegs Q (LB 0x149f8 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 mx) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 (Z_to_bv 64 e)
                    xt3 xt4 xt5 xt6 m).
  Proof.
    intros Q e mn mx L m xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 xt3 xt4 xt5 xt6
      (MI & [j0 FR] & ST & MU & WM & HB) K.
    do 9 zstep.
    eapply K. uinv_tac.
  Qed.

  Lemma seg_nodots : forall (Q : machine_state -> Prop) e mn mx L m xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            xs3 xs10 xt3 xt4 xt5 xt6,
    0 <= mx <= 2147483647 -> dinv mn mx L m ->
    (forall m' mx' ya1, uinv sp m0 lo saved A SS m' -> mx' = bump mx ->
       evt rsegs Q (LS 0x14840 xra xs0 mn mx' (Z_to_bv 64 e) ya1 xa2 xa3 xa4 xa5 xs3 xs10 (Z_to_bv 64 e) xt4 xt5 xt6 m')) ->
    evt rsegs Q (LB 0x149c4 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 mx) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 (Z_to_bv 64 e)
                    xt3 xt4 xt5 xt6 m).
  Proof.
    intros Q e mn mx L m xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs10 xt3 xt4 xt5 xt6 Hmx
      (MI & [j0 FR] & ST & MU & WM & HB) K.
    zstep. zstep. zstep. zstep.
    zstep. if_cases C.
    - zify_cond C. assert (EU : mx = 2147483647) by lia.
      zstep. zstep. zstep. if_cases D2.
      { exfalso. zify_cond D2. lia. }
      zstep. zstep. zstep. zstep. zstep.
      subst mx. eapply K; [uinv_tac | reflexivity].
    - zify_cond C. rewrite (ca_swrap32_id (mx + 1)) by lia.
      zstep. zstep. zstep. zstep. if_cases D2.
      + zify_cond D2. zstep. zstep. zstep. zstep.
        eapply K; [uinv_tac |]. unfold bump. rewrite (proj2 (Z.eqb_neq mx UNB)) by (unfold UNB; lia). reflexivity.
      + exfalso. zify_cond D2. lia.
  Qed.

  Lemma seg_norm : forall (Q : machine_state -> Prop) e mn mx m xra xs0 xa0 xa1 xa2 xa3 xa4 xa5 xs3 xs10 xt4 xt5 xt6,
    0 <= mn <= 2^20 -> 0 <= mx <= 2147483647 -> ninv m ->
    (forall m' mx' ya1 ya2, uinv sp m0 lo saved A SS m' -> mx' = bump mx ->
       evt rsegs Q (LS 0x14840 xra xs0 (mn + 1) mx' (Z_to_bv 64 e) ya1 ya2 xa3 xa4 xa5 xs3 xs10 (Z_to_bv 64 e)
                       xt4 xt5 xt6 m')) ->
    evt rsegs Q (LS 0x14a18 xra xs0 mn mx xa0 xa1 xa2 xa3 xa4 xa5 xs3 xs10 (Z_to_bv 64 e) xt4 xt5 xt6 m).
  Proof.
    intros Q e mn mx m xra xs0 xa0 xa1 xa2 xa3 xa4 xa5 xs3 xs10 xt4 xt5 xt6 Hmn Hmx
      (MI & (j1 & j2 & FR) & ST & MU & WM & HB) K.
    zstep. rewrite (ca_swrap32_id (mn + 1)) by lia.
    zstep. if_cases T.
    { exfalso. zify_cond T. try rewrite !ca_signed_small in T by lia. lia. }
    zstep. zstep. zstep.
    zstep. if_cases C.
    - zify_cond C. assert (EU : mx = 2147483647) by lia.
      zstep. if_cases D2.
      { exfalso. zify_cond D2. lia. }
      zstep. zstep. zstep. zstep. zstep.
      subst mx. eapply K; [uinv_tac | reflexivity].
    - zify_cond C. rewrite (ca_swrap32_id (mx + 1)) by lia.
      zstep. zstep. if_cases D2.
      + zify_cond D2. zstep. zstep. zstep. zstep.
        eapply K; [uinv_tac |]. unfold bump. rewrite (proj2 (Z.eqb_neq mx UNB)) by (unfold UNB; lia). reflexivity.
      + exfalso. zify_cond D2. lia.
  Qed.

  Lemma seg_item : forall (Q : machine_state -> Prop) k k1 L mn mx m xra xa3 xa4 xa5 xs3 xs10 xt4 xt5 xt6,
    (k <= k1)%nat -> (1 <= L)%nat -> (k1 + L <= length SS)%nat -> 0 <= mn <= 2^20 -> 0 <= mx <= 2147483647 ->
    uinv sp m0 lo saved A SS m ->
    (forall m' mn' mx' yra ys0 ya1 ya2 ya3 ya4 ya5 ys3 ys10 yt4 yt5 yt6,
       uinv sp m0 lo saved A SS m' -> (mn', mx') = item_upd (firstn L (skipn k1 SS)) mn mx ->
       evt rsegs Q (LS 0x14840 yra ys0 mn' mx' (Z_to_bv 64 (A + Z.of_nat (k1 + L))) ya1 ya2 ya3 ya4 ya5 ys3 ys10
                       (Z_to_bv 64 (A + Z.of_nat (k1 + L))) yt4 yt5 yt6 m')) ->
    evt rsegs Q (LS 0x14950 xra (Z_to_bv 64 (A + Z.of_nat k1)) mn mx (Z_to_bv 64 (A + Z.of_nat k))
                    (Z_to_bv 64 (Z.of_nat (k1 - k))) (zxb (hd NUL (skipn k1 SS))) xa3 xa4 xa5 xs3 xs10
                    (Z_to_bv 64 (A + Z.of_nat (k1 + L))) xt4 xt5 xt6 m).
  Proof.
    intros Q k k1 L mn mx m xra xa3 xa4 xa5 xs3 xs10 xt4 xt5 xt6 HK HL HKL Hmn Hmx (MI & [j FR] & ST & MU & WM & HB) K.
    assert (BI : bracketed (firstn L (skipn k1 SS)) =
                 (bz (hd NUL (skipn k1 SS)) =? 91) && (bz (hd NUL (skipn (k1 + L - 1) SS)) =? 93)).
    { rewrite bracketed_iff by (rewrite length_skipn; lia). rewrite skipn_skipn.
      replace (L - 1 + k1)%nat with (k1 + L - 1)%nat by lia. reflexivity. }
    pose proof (byte_range (hd NUL (skipn k1 SS))) as BR.
    pose proof (byte_range (hd NUL (skipn (k1 + L - 1) SS))) as BRl.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ca_rd_hd mm A SS (k1 + L - 1) HB ltac:(lia)) as RDl end.
    zstep. if_cases Y2.
    - zify_cond Y2.
      eapply seg_norm; [lia | lia | unfold ninv; inv6 |].
      intros m' mx' ya1 ya2 U E. apply K; [exact U |].
      unfold item_upd. rewrite BI, (proj2 (Z.eqb_neq (bz (hd NUL (skipn k1 SS))) 91) Y2). cbn [andb]. rewrite E. reflexivity.
    - zify_cond Y2.
      zstep. zstep. zstep. zstep.
      rewrite !zb_lxor_ones by lia.
      zstep. if_cases T.
      { exfalso. zify_cond T. Z.div_mod_to_equations. lia. }
      zstep. zstep.
      zstep.
      zstep. if_cases Y4.
      + zify_cond Y4. eapply seg_norm; [lia | lia | unfold ninv; inv6 |].
        intros m' mx' ya1 ya2 U E. apply K; [exact U |].
        unfold item_upd. rewrite BI, (proj2 (Z.eqb_eq (bz (hd NUL (skipn k1 SS))) 91) Y2).
        rewrite (proj2 (Z.eqb_neq (bz (hd NUL (skipn (k1 + L - 1) SS))) 93) Y4). cbn [andb]. rewrite E. reflexivity.
      + zify_cond Y4.
        assert (BT : bracketed (firstn L (skipn k1 SS)) = true).
        { rewrite BI, (proj2 (Z.eqb_eq (bz (hd NUL (skipn k1 SS))) 91) Y2).
          rewrite (proj2 (Z.eqb_eq (bz (hd NUL (skipn (k1 + L - 1) SS))) 93) Y4). reflexivity. }
        zstep. zstep. zstep.
        replace (A + Z.of_nat (k1 + L) - (A + Z.of_nat k) - Z.of_nat (k1 - k)) with (Z.of_nat L) by lia.
        zstep.
        zstep. if_cases C5.
        * zify_cond C5.
          eapply seg_nodots; [lia | unfold dinv; inv6 |].
          intros m' mx' ya1 U E. apply K; [exact U |].
          unfold item_upd. rewrite BT, has_dots_short by (rewrite length_firstn, length_skipn; lia). rewrite E. reflexivity.
        * zify_cond C5. zstep.
          eapply evt_cut.
          { eapply (dots_loop (S L) 0 k1 k1 L (has_dots (firstn L (skipn k1 SS))) mn mx);
              [lia | lia | lia | lia | | reflexivity | unfold dinv; inv6].
            rewrite unsigned_lit_wrap, ?zb_lxor_ones by lia. Z.div_mod_to_equations. lia. }
          intros ms5 (m5 & xra5 & xt05 & xt15 & xt25 & xs05 & xa05 & xa15 & xa25 & xa35 & xa45 & xa55 & xa65 & xa75 &
                      xs35 & xs105 & xt35 & xt45 & xt55 & xt65 & INV5 & [[HT E5] | [HF E5]]); subst ms5.
          -- eapply seg_found; [exact INV5 |]. intros m' U. apply K; [exact U |].
             unfold item_upd. rewrite BT, HT. reflexivity.
          -- eapply seg_nodots; [lia | exact INV5 |]. intros m' mx' ya1 U E. apply K; [exact U |].
             unfold item_upd. rewrite BT, HF, E. reflexivity.
  Qed.

  Lemma synloop : forall f k mn mx rmn rmx m xra xs0 xa1 xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6,
    (length SS - k <= f)%nat -> (k <= length SS)%nat -> 0 <= mn -> mn + Z.of_nat (length SS - k) <= 2^20 ->
    (mx = UNB \/ 0 <= mx /\ mx + Z.of_nat (length SS - k) <= 2^20) ->
    arity_items (items_f f (skipn k SS)) mn mx = (rmn, rmx) -> uinv sp m0 lo saved A SS m ->
    evt rsegs (upost sp gp tp F fc m0 lo saved A SS rmn rmx r2)
      (LS 0x14840 xra xs0 mn mx (Z_to_bv 64 (A + Z.of_nat k)) xa1 xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 m).
  Proof.
    intros f. induction f as [f IH] using (well_founded_induction lt_wf).
    intros k mn mx rmn rmx m xra xs0 xa1 xa2 xa3 xa4 xa5 xs3 xs10 xs11 xt4 xt5 xt6 Hf Hk Hmn0 Hmn Hmx Hres INV.
    pose proof INV as (MI & [j FR] & ST & MU & WM & HB).
    assert (Rmx : 0 <= mx <= 2147483647) by (unfold UNB in Hmx; lia).
    zstep. zstep.
    eapply evt_cut; [eapply (skipA (S (length SS - k)) 0 k k m); [lia | lia | lia | exact HB] |].
    intros ms1 (k1 & Hk1 & Hsk & Hsp & ->).
    zstep. if_cases Z1.
    - zify_cond Z1.
      pose proof (ca_hd_z_end SS k1 HSn ltac:(lia) Z1) as E1.
      rewrite (items_f_nil f (skipn k SS)) in Hres by (rewrite <- Hsk, E1, skipn_all; reflexivity).
      cbn [arity_items] in Hres. injection Hres as <- <-.
      apply evt_done. unfold upost. do 26 eexists. split; [exact INV | reflexivity].
    - zify_cond Z1.
      assert (LT1 : (k1 < length SS)%nat) by (apply (ca_hd_nz_lt SS k1); lia).
      destruct f as [|f']; [lia|].
      rewrite (items_f_step f' SS k k1 Hsk LT1) in Hres.
      zstep. zstep.
      eapply evt_cut; [eapply (scanB (S (length SS - k1)) k1 0 m); [lia | lia | lia | exact Z1 | exact HB] |].
      intros ms2 (ya3 & ya4 & ya5 & ->).
      assert (NE1 : skipn k1 SS <> []).
      { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
      pose proof (ilen_pos (skipn k1 SS) Hsp NE1) as HL1.
      pose proof (ilen_le 0 (skipn k1 SS)) as HL2. rewrite length_skipn in HL2.
      set (L := ilen 0 (skipn k1 SS)) in *.
      pose proof (byte_range (hd NUL (skipn k1 SS))) as BR.
      assert (ITEM : Nat.eqb L 1 && (bz (hd NUL (skipn k1 SS)) =? 124) = false -> forall ya3',
        evt rsegs (upost sp gp tp F fc m0 lo saved A SS rmn rmx r2)
          (LS 0x14950 xra (Z_to_bv 64 (A + Z.of_nat k1)) mn mx (Z_to_bv 64 (A + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (k1 - k))) (zxb (hd NUL (skipn k1 SS))) ya3' ya4 ya5 xs3 xs10
              (Z_to_bv 64 (A + Z.of_nat (k1 + L))) xt4 xt5 xt6 m)).
      { intros NB ya3'.
        rewrite arity_items_nb in Hres by (rewrite bar_iff by (rewrite length_skipn; lia); exact NB).
        eapply seg_item; [lia | lia | lia | lia | lia | exact INV |].
        intros m' mn' mx' yra ys0 ya1 ya2 ya3'' ya4' ya5' ys3 ys10 yt4 yt5 yt6 U IU.
        rewrite <- IU in Hres. cbn [fst snd] in Hres.
        destruct (item_upd_cases _ _ _ _ _ IU) as [Hn Hx].
        destruct (bump_cases mx) as [[Bx Bb] | [Bx Bb]];
          (eapply (IH f' ltac:(lia) (k1 + L)%nat mn' mx' rmn rmx m'); [lia | lia | lia | lia | | exact Hres | exact U]);
          unfold UNB in *; lia. }
      zstep. if_cases Y1.
      + zify_cond Y1. apply ITEM. unfold bz. rewrite (proj2 (Z.eqb_neq _ 124) Y1), andb_false_r. reflexivity.
      + zify_cond Y1.
        zstep. zstep. rewrite !zb_lxor_ones by lia.
        zstep. if_cases C6.
        * zify_cond C6. apply ITEM. rewrite (proj2 (Nat.eqb_neq L 1)); [reflexivity|].
          intros HL. rewrite ?unsigned_lit_wrap in C6. apply C6. Z.div_mod_to_equations. lia.
        * zify_cond C6.
          assert (L1 : L = 1%nat) by (rewrite ?unsigned_lit_wrap in C6; Z.div_mod_to_equations; lia).
          cbn [arity_items] in Hres.
          rewrite (bar_iff (skipn k1 SS) L) in Hres by (rewrite length_skipn; lia).
          rewrite (proj2 (Nat.eqb_eq L 1) L1), (proj2 (Z.eqb_eq (bz (hd NUL (skipn k1 SS))) 124) Y1) in Hres.
          cbn [andb] in Hres.
          zstep.
          eapply evt_cut; [eapply (skipC (S (length SS - (k1 + L))) (k1 + L) m); [lia | lia | exact HB] |].
          intros ms3 (k2 & Hk2 & Hsk2 & Hsp2 & ->).
          zstep. zstep. if_cases C9.
          -- zify_cond C9.
             pose proof (ca_hd_z_end SS k2 HSn ltac:(lia) C9) as E2.
             assert (NIL : items_f f' (skipn (k1 + L) SS) = []).
             { apply items_f_nil. rewrite <- Hsk2, E2, skipn_all. reflexivity. }
             rewrite NIL in Hres. cbv iota in Hres.
             eapply (IH f' ltac:(lia) (k1 + L)%nat mn mx rmn rmx m); [lia | lia | lia | lia | | | exact INV].
             ++ destruct Hmx as [Hmx'|Hmx']; [left; exact Hmx' | right; lia].
             ++ rewrite NIL. exact Hres.
          -- zify_cond C9.
             assert (LT3 : (k2 < length SS)%nat) by (apply (ca_hd_nz_lt SS k2); lia).
             zstep.
             eapply evt_cut; [eapply (scanD (S (length SS - k2)) k2 0 m); [lia | lia | lia | exact C9 | exact HB] |].
             intros ms4 (ya1 & ya2 & ya3'' & ->).
             assert (NE2 : skipn k2 SS <> []).
             { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
             pose proof (ilen_pos (skipn k2 SS) Hsp2 NE2) as HL21.
             pose proof (ilen_le 0 (skipn k2 SS)) as HL22. rewrite length_skipn in HL22.
             set (L2 := ilen 0 (skipn k2 SS)) in *.
             destruct f' as [|f'']; [lia|].
             rewrite (items_f_step f'' SS (k1 + L) k2 Hsk2 LT3) in Hres. fold L2 in Hres. cbv iota in Hres.
             eapply (IH f'' ltac:(lia) (k2 + L2)%nat mn mx rmn rmx m); [lia | lia | lia | lia | | exact Hres | exact INV].
             destruct Hmx as [Hmx'|Hmx']; [left; exact Hmx' | right; lia].
  Qed.

  Lemma syn_path : forall m rmn rmx xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          xt3 xt4 xt5 xt6,
    uinv sp m0 lo saved A SS m -> row_arity SS 0 = (rmn, rmx) ->
    evt rsegs (upost sp gp tp F fc m0 lo saved A SS rmn rmx r2)
      (SGU sp gp tp F fc 0x14804 xra xs0 xs1 r2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 A) xt0 xt1 xt2
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    intros m rmn rmx xra xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 INV HR.
    unfold row_arity in HR. cbn [Z.eqb] in HR.
    zstep. if_cases T.
    { exfalso. zify_cond T. lia. }
    do 14 zstep.
    replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + Z.of_nat 0)) by (f_equal; lia).
    eapply (synloop (length SS) 0 0 0 rmn rmx m); [lia | lia | lia | lia | right; lia | exact HR | exact INV].
  Qed.
End USyn.

Theorem syn_path_holds : bcmp_contract -> syn_path_spec.
Proof.
  intros BC. unfold syn_path_spec, path_spec.
  intros sp gp tp F fc A SS m0 lo saved HSn LSS A0 AL LO LSP m rmn rmx xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10
    xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 INV HR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  eapply syn_path; solve [eassumption | lia].
Qed.

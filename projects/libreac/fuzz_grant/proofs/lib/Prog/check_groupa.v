From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel GroupaModel RcModel
  RcLeaf memcpy_c reac_headamp_tx_effective_c reac_ctrl_checksum_verify_c reac_ctrl_headamp_record_verify_c
  GroupaNeeds_c check_groupa_c.
Import ListNotations.
Open Scope Z_scope.

Lemma T0_split : T0 = le8 (Z_to_bv 64 4611967493404098559) ++ le8 (Z_to_bv 64 28071923024043).
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.

Lemma rw_cells_bytes_at : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Lemma rd_at : forall segs m A bs (k : Z) b,
  bytes_at segs m A bs -> 0 <= k -> (Z.to_nat k < length bs)%nat -> nth (Z.to_nat k) bs (Z_to_bv 8 0) = b ->
  ov_read_bytes segs m (wa (A + k)) 1 = Some [b].
Proof.
  intros segs m A bs k b HB Hk Hl Hn. rewrite (bytes_at_read segs m A bs k 1 HB Hk) by lia.
  rewrite <- Hn. f_equal. clear HB Hn. revert bs Hl. induction (Z.to_nat k) as [|j IH]; intros bs Hl.
  - destruct bs; cbn in *; [lia | reflexivity].
  - destruct bs; cbn in *; [lia|]. apply IH. lia.
Qed.

Lemma ga_blocksum : forall ch p v, 0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
  blocksum (skipn 2 (GA ch p v)) = 0.
Proof.
  intros ch p v Hc Hp Hv. pose proof (ga_r_range ch p v). pose proof (ga_c_range ch p v).
  pose proof (GA_sum_block ch p v) as S.
  unfold sum_from, GAz in S. cbn [skipn fold_right] in S.
  unfold blocksum, GA, bl, GAz. cbn [skipn map psum nth].
  rewrite !u8_lit by lia.
  rewrite <- S. f_equal. lia.
Qed.

Ltac u8s := cbv beta; repeat match goal with |- context [bv_unsigned (Z_to_bv 8 ?x)] => rewrite (u8_lit x) by lia end.
Lemma bytes_at_sub : forall segs m A bs k n, bytes_at segs m A bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros segs m A bs k n H Hl. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma ga_hv : forall ch p v, 0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
  hv (Z_to_bv 8 4) (Z_to_bv 8 3) (firstn 6 (skipn 18 (GA ch p v))) = true.
Proof.
  intros ch p v Hc Hp Hv. pose proof (ga_r_range ch p v). pose proof (GA_record_sum ch p v) as S.
  unfold hv, rsum, GA, bl, GAz. cbn [skipn firstn map psum nth].
  rewrite !u8_lit by lia.
  match goal with |- context [?x mod 128] => replace x with (1 + 1 + ch + p + v + ga_r ch p v) by lia end.
  rewrite S. reflexivity.
Qed.

Ltac br_not := let HC := fresh "HC" in if_cases HC; zify_cond HC; [exfalso; lia | ].
Ltac br_taken := let HC := fresh "HC" in if_cases HC; zify_cond HC; [ | exfalso; lia ].

Theorem check_groupa_holds :
  memcpy_contract -> reac_ctrl_parse_need -> reac_headamp_tx_effective_contract ->
  reac_ctrl_headamp_record_verify_contract -> reac_ctrl_checksum_verify_contract -> check_groupa_contract.
Proof.
  intros MEMC PARSE EFF RVC CKS.
  unfold reac_ctrl_parse_need, REAC_CTRL_PARSE, REAC_CTRL_PARSE_FRAME in PARSE.
  unfold reac_ctrl_headamp_record_verify_contract, REAC_CTRL_HEADAMP_RECORD_VERIFY in RVC.
  unfold reac_headamp_tx_effective_contract, REAC_HEADAMP_TX_EFFECTIVE in EFF.
  unfold reac_ctrl_checksum_verify_contract, REAC_CTRL_CHECKSUM_VERIFY in CKS.
  unfold check_groupa_contract, CHECK_GROUPA, CHECK_GROUPA_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m row ch p t lo T -> -> -> -> -> SP16 HCH HP HLT HT DT HR DR HMI ST LO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (bytes_at_bound rsegs m row _ HR) as Brow. rewrite length_GA in Brow.
  pose proof (bytes_at_bound rsegs m t _ HT) as Bt. rewrite HLT in Bt.
  change (Z.of_nat 34) with 34 in Brow. change (Z.of_nat 460) with 460 in Bt.
  change (2 ^ 64) with 18446744073709551616 in Brow, Bt.
  pose proof (eff_range T t ch p) as RGV.
  remember (eff T t ch p) as v eqn:Hv.
  remember (GA ch p v) as G eqn:HG.
  assert (HLG : length G = 34%nat) by (subst G; reflexivity).
  assert (U144 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144)
    by (apply unsigned_lit; lia).
  assert (U88 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -88)) = bv_unsigned sp + -88)
    by (apply unsigned_lit; lia).
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  assert (UR : bv_unsigned (Z_to_bv 64 row) = row) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST. rename FR into RS.
  carve_frame 6%nat ST. rename FR into RPAD.
  carve_frame 34%nat ST. rename FR into RFH.
  carve_frame 16%nat ST. rename FR into RFL.
  carve_frame 36%nat ST. rename FR into RP.
  carve_frame 4%nat ST. rename FR into R0.
  do 7 zstep.
  do 5 zstep.
  do 6 zstep.
  do 2 zstep.
  do 4 zstep.
  call MEMC.
  { rewrite UR. exact HR. }
  { rewrite HLG, U34. reflexivity. }
  { rewrite U88, U34. exact RFH. }
  { rewrite UR, U88, U34. lia. }
  { exact HMI. }
  rewrite U88, U34 in PC. change (Z.to_nat 34) with 34%nat in PC. clear POST. rename PC into RFH.
  pose proof (length_F50 ch p v) as HL50.
  assert (HF50 : bytes_at rsegs x13 (bv_unsigned sp + -104) (F50 ch p v)).
  { unfold F50. rewrite T0_split. apply bytes_at_app. split.
    - pose proof (rw_cells_bytes_at _ _ _ _ RFL) as H. cbn [cells_bytes cbytes] in H.
      rewrite app_nil_r in H. exact H.
    - rewrite length_app, !length_le8. replace (bv_unsigned sp + -104 + Z.of_nat (8 + 8)) with (bv_unsigned sp + -88) by lia.
      pose proof (rw_cells_bytes_at _ _ _ _ RFH) as H. cbn [cells_bytes cbytes] in H.
      rewrite app_nil_r in H. subst G. exact H. }
  do 4 zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply PARSE with (f := bv_unsigned sp + -104) (o := bv_unsigned sp + -140)
                       (ch := ch) (p := p) (v := v) (lo := lo) | post_call segs mm] end.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { rewrite U144. Z.div_mod_to_equations. lia. }
  { lia. }
  { lia. }
  { lia. }
  { Z.div_mod_to_equations. lia. }
  { lia. }
  { exact HCH. }
  { exact HP. }
  { exact RGV. }
  { exact HF50. }
  { exact RP. }
  { lia. }
  { rewrite U144. lia. }
  { rewrite U144. lia. }
  { rewrite U144. exact ST. }
  { rewrite U144. lia. }
  { exact MI. }
  rewrite U144 in PC. rename PC into ST. rename POST into RP. rename MI0 into HMI.
  zstep. zstep. try br_not.
  zstep. u8s. zstep. try br_not.
  zstep. u8s. zstep. try br_not.
  zstep. u8s.
  do 4 zstep.
  eapply evt_cut.
  { eapply EFF with (t := t) (ch := ch) (p := p) (T := T);
      [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HLT | exact HT]]. }
  intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & ->).
  replace (ret_pc (Z_to_bv 64 0x13b10)) with (Z_to_bv 64 0x13b10) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite <- Hv.
  zstep. try br_not.
  do 2 zstep.
  pose proof (rw_cells_bytes_at _ _ _ _ RFH) as HB. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  assert (HB01 : bytes_at rsegs x28 (bv_unsigned sp + -104 + 18) [Z_to_bv 8 4; Z_to_bv 8 3]).
  { replace (bv_unsigned sp + -104 + 18) with (bv_unsigned sp + -88 + Z.of_nat 2) by lia.
    replace [Z_to_bv 8 4; Z_to_bv 8 3] with (firstn 2 (skipn 2 G)) by (subst G; reflexivity).
    apply bytes_at_sub; [exact HB | rewrite HLG; lia]. }
  assert (HREC : bytes_at rsegs x28 (bv_unsigned sp + -104 + 34) (firstn 6 (skipn 18 G))).
  { replace (bv_unsigned sp + -104 + 34) with (bv_unsigned sp + -88 + Z.of_nat 18) by lia.
    apply bytes_at_sub; [exact HB | rewrite HLG; lia]. }
  eapply evt_cut.
  { eapply RVC with (p := bv_unsigned sp + -104) (b0 := Z_to_bv 8 4) (b1 := Z_to_bv 8 3)
                    (rec := firstn 6 (skipn 18 G));
      [reflexivity | lia | lia | exact HB01 | rewrite length_firstn, length_skipn, HLG; reflexivity | exact HREC]. }
  intros ms' (y1' & y2' & y3' & ->).
  replace (ret_pc (Z_to_bv 64 0x13b1c)) with (Z_to_bv 64 0x13b1c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (hv (Z_to_bv 8 4) (Z_to_bv 8 3) (firstn 6 (skipn 18 G))) with true by (subst G; symmetry; apply ga_hv; lia).
  zstep. try br_not.
  assert (HCK : bytes_at rsegs x28 (bv_unsigned sp + -104 + 18) (skipn 2 G)).
  { pose proof HB as H. rewrite <- (firstn_skipn 2 G) in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite length_firstn, HLG in H. replace (bv_unsigned sp + -104 + 18) with (bv_unsigned sp + -88 + Z.of_nat (Nat.min 2 34))
      by (cbn; lia). exact H. }
  do 2 zstep.
  eapply evt_cut.
  { eapply CKS with (p := bv_unsigned sp + -104) (bs := skipn 2 G);
      [lia | lia | reflexivity | rewrite length_skipn, HLG; reflexivity | exact HCK]. }
  intros ms' (z1 & z2 & z3 & ->).
  replace (ret_pc (Z_to_bv 64 0x13b28)) with (Z_to_bv 64 0x13b28) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (blocksum (skipn 2 G)) with 0 by (subst G; symmetry; apply ga_blocksum; lia).
  rewrite Z.eqb_refl.
  zstep. try br_not.
  assert (RD0 : ov_read_bytes rsegs x28 (wa (bv_unsigned sp + -70)) 1 = Some [Z_to_bv 8 1]).
  { replace (bv_unsigned sp + -70) with (bv_unsigned sp + -88 + 18) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD1 : ov_read_bytes rsegs x28 (wa (bv_unsigned sp + -69)) 1 = Some [Z_to_bv 8 1]).
  { replace (bv_unsigned sp + -69) with (bv_unsigned sp + -88 + 19) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD2 : ov_read_bytes rsegs x28 (wa (bv_unsigned sp + -68)) 1 = Some [Z_to_bv 8 ch]).
  { replace (bv_unsigned sp + -68) with (bv_unsigned sp + -88 + 20) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD3 : ov_read_bytes rsegs x28 (wa (bv_unsigned sp + -67)) 1 = Some [Z_to_bv 8 p]).
  { replace (bv_unsigned sp + -67) with (bv_unsigned sp + -88 + 21) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD4 : ov_read_bytes rsegs x28 (wa (bv_unsigned sp + -66)) 1 = Some [Z_to_bv 8 v]).
  { replace (bv_unsigned sp + -66) with (bv_unsigned sp + -88 + 22) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD5 : ov_read_bytes rsegs x28 (wa (bv_unsigned sp + -65)) 1 = Some [Z_to_bv 8 (ga_r ch p v)]).
  { replace (bv_unsigned sp + -65) with (bv_unsigned sp + -88 + 23) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  pose proof (ga_r_range ch p v) as RGR.
  destruct RFH as [RFHc RFHw].
  do 2 zstep.
  zstep. u8s. zstep. zstep. zstep. br_taken.
  zstep. u8s. zstep. zstep. zstep. br_taken.
  zstep. u8s. zstep. zstep. zstep. br_taken.
  zstep. u8s. zstep. zstep. zstep. br_taken.
  zstep. u8s. zstep. zstep. zstep. br_taken.
  zstep. u8s. zstep. zstep. zstep. br_not.
  zstep.
  replace (Z.land (2 + ch + p + v + ga_r ch p v) 127) with 0
    by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; change (2 ^ 7) with 128;
        replace (2 + ch + p + v + ga_r ch p v) with (1 + 1 + ch + p + v + ga_r ch p v) by lia;
        symmetry; apply GA_record_sum).
  zstep. try br_not.
  zstep. u8s. zstep. try br_not.
  assert (RFH : rw_cells rsegs x28 (bv_unsigned sp + -88) [CB 34 G]) by (split; assumption).
  clear RFHc RFHw.
  do 8 zstep.
  release_frame R0 ST (bv_unsigned sp + -140).
  release_frame RP ST (bv_unsigned sp + -104).
  release_frame RFL ST (bv_unsigned sp + -88).
  release_frame RFH ST (bv_unsigned sp + -54).
  release_frame RPAD ST (bv_unsigned sp + -48).
  release_frame RS ST (bv_unsigned sp).
  finish.
Qed.

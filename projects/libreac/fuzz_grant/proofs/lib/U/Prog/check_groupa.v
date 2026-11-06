From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantSweepModel GroupaModel
  memcpy_c reac_headamp_tx_effective_c reac_ctrl_checksum_verify_c reac_ctrl_headamp_record_verify_c
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

Definition Z50 : list byte := T0 ++ repeat (Z_to_bv 8 0) 34.

Lemma length_Z50 : length Z50 = 50%nat.
Proof. reflexivity. Qed.

Lemma img_Z50 : ro_bytes rsegs 0x1044e Z50.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma wr_ro_disj : forall m d n s bs,
  mem_inv rsegs m -> wr_at rsegs m d n -> ro_bytes rsegs s bs -> 0 < n -> 0 <= s -> (0 < length bs)%nat ->
  d + n <= s \/ s + Z.of_nat (length bs) <= d.
Proof.
  intros m d n s bs HI (Hd & Hdn & HW) HR Hn Hs Hl.
  destruct (Z_le_gt_dec (d + n) s) as [?|H1]; [left; lia|].
  destruct (Z_le_gt_dec (s + Z.of_nat (length bs)) d) as [?|H2]; [right; lia|].
  exfalso.
  destruct (nth_error bs (Z.to_nat (Z.max d s - s))) as [b|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  pose proof (ro_bytes_nth rsegs bs s _ b HR E) as [_ Hro].
  replace (s + Z.of_nat (Z.to_nat (Z.max d s - s))) with (Z.max d s) in Hro by lia.
  specialize (HW (Z.max d s - d) ltac:(lia)). replace (d + (Z.max d s - d)) with (Z.max d s) in HW by lia.
  destruct (m (wa (Z.max d s))) eqn:Em.
  - pose proof (HI _ _ Em). congruence.
  - pose proof (wview_not_ro rsegs m (wa (Z.max d s)) HW Em). congruence.
Qed.

Lemma rw_cells_cut : forall segs m A n1 n2 bs1 bs2, length bs1 = n1 -> length bs2 = n2 ->
  rw_cells segs m A [CB (n1 + n2) (bs1 ++ bs2)] ->
  rw_cells segs m A [CB n1 bs1] /\ rw_cells segs m (A + Z.of_nat n1) [CB n2 bs2].
Proof.
  intros segs m A n1 n2 bs1 bs2 L1 L2 H.
  unfold rw_cells, cells_at, wr_at in *. destruct H as [[_ Hb] (Ha & Hn & Hw)].
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hn, Hw. rewrite app_nil_r in Hb.
  apply bytes_at_app in Hb. destruct Hb as [B1 B2]. rewrite L1 in B2.
  cbn [cells_bytes cbytes cells_size csize cells_wf cell_wf]. rewrite !app_nil_r.
  split; split; [split; [split; [exact L1 | exact I] | exact B1] | | split; [split; [exact L2 | exact I] | exact B2] |].
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat n1 + i) with (A + (Z.of_nat n1 + i)) by lia. apply Hw. lia.
Qed.

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
    F fc m row ch p t lo T -> -> -> -> -> SP16 HCH HP HLT HT HT4 DT HR DR HMI ST LO.
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
  assert (U106 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -106)) = bv_unsigned sp + -106)
    by (apply unsigned_lit; lia).
  assert (U90 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -90)) = bv_unsigned sp + -90)
    by (apply unsigned_lit; lia).
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  assert (U50 : bv_unsigned (Z_to_bv 64 50) = 50) by reflexivity.
  assert (UI : bv_unsigned (Z_to_bv 64 0x1044e) = 0x1044e) by reflexivity.
  assert (UR : bv_unsigned (Z_to_bv 64 row) = row) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 56%nat ST. rename FR into RS.
  carve_frame 50%nat ST. rename FR into RF.
  carve_frame 2%nat ST. rename FR into RPAD.
  carve_frame 36%nat ST. rename FR into RP.
  do 19 zstep.
  pose proof (ro_bytes_at rsegs m0 0x1044e Z50 HMI ltac:(lia) ltac:(rewrite length_Z50; lia) img_Z50) as HIMG.
  pose proof (wr_ro_disj _ _ _ _ _ HMI (proj2 RF) img_Z50 ltac:(cbn; lia) ltac:(lia)
                ltac:(rewrite length_Z50; lia)) as HDJ.
  rewrite length_Z50 in HDJ. cbn [cells_size csize] in HDJ.
  call MEMC.
  { rewrite UI. exact HIMG. }
  { rewrite U50. reflexivity. }
  { rewrite U106, U50. exact RF. }
  { rewrite UI, U106, U50. lia. }
  { exact HMI. }
  rewrite U106, U50 in PC. change (Z.to_nat 50) with (16 + 34)%nat in PC. clear POST.
  unfold Z50 in PC.
  destruct (rw_cells_cut _ _ _ 16 34 T0 (repeat (Z_to_bv 8 0) 34) eq_refl eq_refl PC) as [RFL RFH0].
  clear PC. change (Z.of_nat 16) with 16 in RFH0.
  replace (bv_unsigned sp + -106 + 16) with (bv_unsigned sp + -90) in RFH0 by lia.
  zstep. zstep. try br_not.
  do 4 zstep.
  call MEMC.
  { rewrite UR. exact HR. }
  { rewrite HLG, U34. reflexivity. }
  { rewrite U90, U34. exact RFH0. }
  { rewrite UR, U90, U34. lia. }
  { exact MI. }
  rewrite U90, U34 in PC. change (Z.to_nat 34) with 34%nat in PC. clear POST. rename PC into RFH. rename MI0 into HMI.
  pose proof (length_F50 ch p v) as HL50.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  assert (HF50 : bytes_at rsegs m2 (bv_unsigned sp + -106) (F50 ch p v)).
  { unfold F50. apply bytes_at_app. split.
    - pose proof (rw_cells_bytes_at _ _ _ _ RFL) as H. cbn [cells_bytes cbytes] in H.
      rewrite app_nil_r in H. exact H.
    - replace (bv_unsigned sp + -106 + Z.of_nat (length T0)) with (bv_unsigned sp + -90) by (cbn; lia).
      pose proof (rw_cells_bytes_at _ _ _ _ RFH) as H. cbn [cells_bytes cbytes] in H.
      rewrite app_nil_r in H. subst G. exact H. }
  do 4 zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply PARSE with (f := bv_unsigned sp + -106) (o := bv_unsigned sp + -144)
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
  { exact HMI. }
  rewrite U144 in PC. rename PC into ST. rename POST into RP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  match goal with H : mem_inv rsegs m3 |- _ => revert H; intro HMI end.
  zstep. zstep. try br_not.
  zstep. u8s. zstep. try br_not.
  zstep. u8s. zstep. try br_not.
  zstep. u8s.
  do 4 zstep.
  eapply evt_cut.
  { eapply EFF with (t := t) (ch := ch) (p := p) (T := T);
      [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HLT | split; [exact HT | exact HT4]]]. }
  intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & ->).
  replace (ret_pc (Z_to_bv 64 0x13dc4)) with (Z_to_bv 64 0x13dc4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite <- Hv.
  zstep. try br_not.
  do 2 zstep.
  pose proof (rw_cells_bytes_at _ _ _ _ RFH) as HB. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  assert (HB01 : bytes_at rsegs m3 (bv_unsigned sp + -106 + 18) [Z_to_bv 8 4; Z_to_bv 8 3]).
  { replace (bv_unsigned sp + -106 + 18) with (bv_unsigned sp + -90 + Z.of_nat 2) by lia.
    replace [Z_to_bv 8 4; Z_to_bv 8 3] with (firstn 2 (skipn 2 G)) by (subst G; reflexivity).
    apply bytes_at_sub; [exact HB | rewrite HLG; lia]. }
  assert (HREC : bytes_at rsegs m3 (bv_unsigned sp + -106 + 34) (firstn 6 (skipn 18 G))).
  { replace (bv_unsigned sp + -106 + 34) with (bv_unsigned sp + -90 + Z.of_nat 18) by lia.
    apply bytes_at_sub; [exact HB | rewrite HLG; lia]. }
  eapply evt_cut.
  { eapply RVC with (p := bv_unsigned sp + -106) (b0 := Z_to_bv 8 4) (b1 := Z_to_bv 8 3)
                    (rec := firstn 6 (skipn 18 G));
      [reflexivity | lia | lia | exact HB01 | rewrite length_firstn, length_skipn, HLG; reflexivity | exact HREC]. }
  intros ms' (y1' & y2' & y3' & y4' & y5' & ->).
  replace (ret_pc (Z_to_bv 64 0x13dd0)) with (Z_to_bv 64 0x13dd0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (hv (Z_to_bv 8 4) (Z_to_bv 8 3) (firstn 6 (skipn 18 G))) with true by (subst G; symmetry; apply ga_hv; lia).
  zstep. try br_not.
  assert (HCK : bytes_at rsegs m3 (bv_unsigned sp + -106 + 18) (skipn 2 G)).
  { pose proof HB as H. rewrite <- (firstn_skipn 2 G) in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite length_firstn, HLG in H. replace (bv_unsigned sp + -106 + 18) with (bv_unsigned sp + -90 + Z.of_nat (Nat.min 2 34))
      by (cbn; lia). exact H. }
  do 2 zstep.
  eapply evt_cut.
  { eapply CKS with (p := bv_unsigned sp + -106) (bs := skipn 2 G);
      [lia | lia | reflexivity | rewrite length_skipn, HLG; reflexivity | exact HCK]. }
  intros ms' (z1 & z2 & z3 & z4 & z5 & ->).
  replace (ret_pc (Z_to_bv 64 0x13ddc)) with (Z_to_bv 64 0x13ddc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (blocksum (skipn 2 G)) with 0 by (subst G; symmetry; apply ga_blocksum; lia).
  rewrite Z.eqb_refl.
  zstep. try br_not.
  assert (RD0 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + -72)) 1 = Some [Z_to_bv 8 1]).
  { replace (bv_unsigned sp + -72) with (bv_unsigned sp + -90 + 18) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD1 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + -71)) 1 = Some [Z_to_bv 8 1]).
  { replace (bv_unsigned sp + -71) with (bv_unsigned sp + -90 + 19) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD2 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + -70)) 1 = Some [Z_to_bv 8 ch]).
  { replace (bv_unsigned sp + -70) with (bv_unsigned sp + -90 + 20) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD3 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + -69)) 1 = Some [Z_to_bv 8 p]).
  { replace (bv_unsigned sp + -69) with (bv_unsigned sp + -90 + 21) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD4 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + -68)) 1 = Some [Z_to_bv 8 v]).
  { replace (bv_unsigned sp + -68) with (bv_unsigned sp + -90 + 22) by lia.
    apply (rd_at _ _ _ _ _ _ HB); [lia | rewrite HLG; cbn; lia | subst G; reflexivity]. }
  assert (RD5 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + -67)) 1 = Some [Z_to_bv 8 (ga_r ch p v)]).
  { replace (bv_unsigned sp + -67) with (bv_unsigned sp + -90 + 23) by lia.
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
  assert (RFH : rw_cells rsegs m3 (bv_unsigned sp + -90) [CB 34 G]) by (split; assumption).
  clear RFHc RFHw.
  do 9 zstep.
  release_frame RP ST (bv_unsigned sp + -108).
  release_frame RPAD ST (bv_unsigned sp + -106).
  release_frame RFL ST (bv_unsigned sp + -90).
  release_frame RFH ST (bv_unsigned sp + -56).
  release_frame RS ST (bv_unsigned sp).
  finish.
Qed.

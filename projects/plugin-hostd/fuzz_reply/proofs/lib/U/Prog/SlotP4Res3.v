From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF RelayModel RelayKeys RelayRep HarnessRep ListRep CheckRep ListTr
  HarnessTr send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c
  SlotMove SlotNcMove3 SlotRun3 SlotP5R3 SlotP5R3G SlotP5Res3 SlotResR3 SlotReads op_add_c TrModel SlotP4Res3Aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotPass4.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zsum_perm' {X : Type} (f : X -> Z) l l' : Permutation l l' -> zsum f l = zsum f l'.
Proof.
  intros P. induction P as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; [reflexivity| | |lia];
    rewrite ?zsum_cons; [rewrite IH; reflexivity|lia].
Qed.

Theorem p4_close E K G out es hj h b al alb L0 A0 L4 A4 b4 G' out' es' hj' dels adds ks :
  RI3_ledger rv_wt (ss_pl E) K (view_of G out es hj) L0 A0 b al alb -> res_ok_pack3 A0 b -> res_ok_pack3 A4 b4 ->
  p3_cap b4 = p3_cap b -> p3_mcap b4 = p3_mcap b -> length (p3_live b4) = 49%nat -> Forall (fun n => 0 <= n) ks ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b4) <= znth c (p3_live b) + bcnt c ks + dl_of dels adds c) ->
  p3_bytes b4 <= p3_bytes b + zsum (fun n => n) ks + db_of dels adds ->
  (forall c, 0 <= c < 49 -> bcnt c ks <= bcnt c (ekeys_hl (hs_expected h)) + cred h c) ->
  zsum (fun n => n) ks <= zsum (fun n => n) (ekeys_hl (hs_expected h)) + credb h ->
  (forall e0, In e0 (p3_mis b4) -> (In e0 (p3_mis b) /\ ~ In (ptr_addr L0 (fst e0)) (map fst dels)) \/
     In (ptr_addr L4 (fst e0)) (rv_nc (view_of G' out' es' hj'))) ->
  Permutation (pend_view hj) (map snd (hl_recs (hs_pending h)) :: pend_view hj') ->
  Permutation (ek_view hj) (ekeys_hl (hs_expected h) ++ ek_view hj') ->
  (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
  nc_move (view_of G out es hj) L0 A0 (view_of G' out' es' hj') L4 A4 dels adds ->
  List.NoDup (map fst (blocks L4 A4)) ->
  (forall p n n', In (p, n) (user_blocks A0) -> In (p, n') (user_blocks A4) ->
     In (ptr_addr L0 p) (rv_nc (view_of G out es hj)) -> ~ In (ptr_addr L0 p) (map fst dels) ->
     In (ptr_addr L4 p) (rv_nc (view_of G' out' es' hj'))) ->
  ncs (view_of G' out' es' hj') L4 A4 <= nc_wt es' hj' -> nc_wt es' hj' <= nc_wt es hj ->
  RI3_reply E K (view_of G' out' es' hj') L4 A4.
Proof.
  intros HL HR HR4 Hc Hm Hl Hks HLv HBy HCc HCb HMis Hp Hek Hes Hhj HM HND HK HWs HWg.
  destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
  apply (step3 E K K (view_of G out es hj) L0 A0 b al alb (view_of G' out' es' hj') L4 A4 b4 ks (dl_of dels adds)
           (db_of dels adds) dels (fun p => In (ptr_addr L4 p) (rv_nc (view_of G' out' es' hj'))) HL HR Hks HR4 Hc Hm Hl
           HLv HBy HMis (fun p H => H) HND HK (nc_len G' out' es' hj' Hes Hhj) G1 G2 HWs).
  - cbn [view_of rv_wt]. unfold zlen, NC_PER, DATA_PER. lia.
  - assert (EK : forall c, ek_c (view_of G out es hj) c =
              bcnt c (ekeys_hl (hs_expected h)) + ek_c (view_of G' out' es' hj') c).
    { intros c. rewrite !ek_c_view, <- bcnt_app. unfold bcnt. apply zsum_perm'. exact Hek. }
    assert (EB : ek_b (view_of G out es hj) =
              zsum (fun n => n) (ekeys_hl (hs_expected h)) + ek_b (view_of G' out' es' hj')).
    { rewrite !ek_b_view, <- zsum_app. apply zsum_perm'. exact Hek. }
    assert (PC : forall c, prom_c (rv_pend (view_of G out es hj)) c =
              cred h c + prom_c (rv_pend (view_of G' out' es' hj')) c).
    { intros c. cbn [view_of rv_pend]. unfold prom_c. rewrite (zsum_perm' _ _ _ Hp), zsum_cons. reflexivity. }
    assert (PB : promb (rv_pend (view_of G out es hj)) = credb h + promb (rv_pend (view_of G' out' es' hj'))).
    { cbn [view_of rv_pend]. unfold promb. rewrite (zsum_perm' _ _ _ Hp), zsum_cons. reflexivity. }
    split.
    + intros c Hc'. rewrite (EK c), (PC c). pose proof (HCc c Hc'). lia.
    + rewrite EB, PB. lia.
  - exact (ek_view_nonneg hj').
Qed.

Lemma entry_dels_sub e x : In x (map fst (entry_dels e)) -> In x (entry_blocks e).
Proof.
  unfold entry_dels, entry_blocks. rewrite map_app, !in_app_iff. intros [H|H]; [left|right; left];
    [destruct (re_cap e =? 0)|destruct (re_hp e =? 0)]; exact H.
Qed.

Lemma arr_lb l x : In x (map fst (arr_sz l)) -> In x (list_blocks l).
Proof.
  intros H. apply arr_sz_in in H as (-> & Hc). unfold list_blocks. rewrite (proj2 (Z.eqb_neq _ _) Hc).
  left. reflexivity.
Qed.

Lemma src_dels_sub h x : In x (map fst (src_dels h)) -> In x (hs_blocks h).
Proof.
  unfold src_dels, hs_blocks. rewrite !map_app, !in_app_iff.
  intros [H|[H|[H|H]]]; [left; exact (arr_lb _ _ H)|right; left; exact H|right; right; left; exact (arr_lb _ _ H)|
    right; right; right; exact (arr_lb _ _ H)].
Qed.

Lemma src_dels_held h x : hl_cap (hs_held h) <> 0 -> x = hl_v (hs_held h) -> In x (map fst (src_dels h)).
Proof.
  intros Hc ->. unfold src_dels. rewrite !map_app, !in_app_iff. right. right. right.
  unfold arr_sz. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
Qed.

Lemma src_dels_exp h x : hl_cap (hs_expected h) <> 0 -> x = hl_v (hs_expected h) -> In x (map fst (src_dels h)).
Proof.
  intros Hc ->. unfold src_dels. rewrite !map_app, !in_app_iff. right. right. left.
  unfold arr_sz. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
Qed.

Theorem p4_res3 : SlotPass4.p4_res pack3_form RI3_reply.
Proof.
  intros E K L0 A0 G out es hj q e h i lv MX CAP HRI HND0 HWF Hcost HNT Hqe Hqh HEB HSB HCAP HMX HCR Hfd Hfind Hd3
    HC1 Hkh HO0 Hes Hhj.
  destruct HRI as (b & al & alb & HR0 & HL).
  pose proof HL as (HLc & HLm & _ & _ & _ & HLa & HLe & _).
  assert (HMX0 : 0 <= MX) by lia. assert (HCAP0 : 0 <= CAP) by lia.
  assert (Hin : In (h, i) hj) by exact (nth_error_In hj q Hqh).
  assert (Hine : In e es) by exact (nth_error_In es q Hqe).
  pose proof HEB as (HEB1 & HEB2 & _).
  assert (Hrc : 0 <= re_cap e) by (destruct HEB1 as [X|X]; [lia|exact (blk_nonneg _ _ _ _ HWF X)]).
  assert (Hka : 0 <= ent_ka e).
  { unfold ent_ka. destruct (Z.eqb_spec (re_hp e) 0) as [X|X]; [lia|].
    destruct HEB2 as [Y|Y]; [contradiction|exact (blk_nonneg _ _ _ _ HWF Y)]. }
  pose proof HSB as ((HSP & _) & HSPa & (HSE & _) & (HSH & _) & _).
  assert (Hec : 0 <= hl_cap (hs_expected h)) by (destruct HSE as [X|X]; [lia|pose proof (blk_nonneg _ _ _ _ HWF X); lia]).
  assert (NV : SlotCaps3.NMAX = 536879104) by reflexivity.
  assert (E3 : DRAIN_B = 1099511627776) by reflexivity.
  assert (BV : BMAX = 17592186044416) by reflexivity.
  set (nm := known_at L0 A0) in *.
  set (a0 := drain_start nm (nm out) e h).
  set (C1 := remove_entry_cap lv MX 0 CAP e h) in *.
  assert (Etr : relay_remove_tr lv MX 0 CAP (re_fd e) es h nm 0 (nm out) = remove_entry_tr lv MX 0 CAP e h 0 a0).
  { unfold relay_remove_tr. rewrite (proj2 (Z.ltb_ge _ _) Hfd), Hfind. reflexivity. }
  rewrite Etr.
  assert (HP : pk3_ok b) by exact (ledger3_pk3 _ _ _ _ _ _ _ _ _ HL).
  assert (HSl : forall c, 0 <= c < 49 -> znth c (p3_live b) + cred h c + 64 <= znth c (p3_cap b)).
  { intros c Hc. pose proof (ledger3_slack _ _ _ _ _ _ _ _ _ c HL Hc). pose proof (cred_le_prom hj h i c Hin).
    cbn [view_of rv_pend] in *. lia. }
  pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HB0. rewrite PB3_MAX_val in HB0.
  assert (HBy : p3_bytes b + 2 * C1 + 2 * DRAIN_B <= BMAX) by lia.
  exists b. split; [exact HR0|]. split.
  - intros qs _. rewrite roomF3.
    destruct (p4_misT_start (ss_pl E) K L0 A0 b al alb G out es hj q e h i CAP qs HL HR0 HND0 Hqe Hqh Hes Hhj Hkh HO0)
      as (S & HS).
    exact (proj1 (rr3 lv MX 0 CAP e h nm (nm out) qs b S 0 C1 Hd3 HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec (Z.le_refl _) HC1
                    HP HSl HBy HS)).
  - intros L1 A1 qs1 _ HR1. rewrite runF3 in HR1.
    destruct (p4_misT_start (ss_pl E) K L0 A0 b al alb G out es hj q e h i CAP qs1 HL HR0 HND0 Hqe Hqh Hes Hhj Hkh HO0)
      as (S1 & HS1).
    destruct (rr3 lv MX 0 CAP e h nm (nm out) qs1 b S1 0 C1 Hd3 HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec (Z.le_refl _) HC1
                HP HSl HBy HS1)
      as (_ & P1 & Cp1 & Mp1 & (dks & Hdks & Hdc & Hdb & L1e & B1e) & B1c & (S1' & r1' & HS1')).
    destruct (rr_model lv MX 0 CAP e h nm (nm out) HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec) as (_ & _ & _ & Hecm & _).
    pose proof (rr_misK (p3_mis b) (slot3 CAP (resolveF qs1 (nm out)) ++ dsl qs1 (drain_init 0 CAP e h) a0 ++ [])
                  lv MX 0 CAP e h nm (nm out) qs1 b [] HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec (misK_init _ _)) as K1.
    pose proof (rr_oq lv MX 0 CAP e h nm (nm out) HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec) as [_ Hoq].
    fold a0 C1 in Hoq, K1, L1e, B1e, B1c, HS1', P1, Cp1, Mp1.
    set (b1 := run3 qs1 b 0 (remove_entry_tr lv MX 0 CAP e h 0 a0)) in *.
    set (s := after_drain lv MX 0 CAP e h) in *.
    set (a1 := after_drain_adr lv MX 0 CAP e h 0 a0) in *.
    hnf. intros OUT' CAP' olv h1 HQL HQN HSL HB1a HB1b HB1c HND1o HOUT Hh1 Hpend1 Hheld1 Hexp1 HSB1 HY1 HN1 HG7 HG8 HG5.
    fold a0 C1 in HQL, HSL.
    assert (HZR : Forall zrange (SlotPass4.p4_lines e h))
      by (unfold SlotPass4.p4_lines; destruct (re_eof e =? 0); [apply p4x_lines_range|constructor]).
    assert (TX1 : texts (hs_expected h1) = rr_lines e h) by exact (texts_lines _ _ Hexp1 HZR).
    assert (EK1 : ekeys_hl (hs_expected h1) = ekeys (rr_lines e h)).
    { change (ekeys_hl (hs_expected h1)) with (ekeys (texts (hs_expected h1))). rewrite TX1. reflexivity. }
    assert (HE1 : hl_cap (hs_expected h1) = ds_ecap s /\ hl_v (hs_pending h1) = hl_v (hs_pending h) /\
                  hl_cap (hs_pending h1) = hl_cap (hs_pending h) /\ hs_partial h1 = hs_partial h).
    { destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
      - rewrite (HG8 Ee). unfold s, after_drain. rewrite (proj2 (Z.eqb_eq _ _) Ee). split; [reflexivity|exact (HG5 Ee)].
      - rewrite (Hh1 Ee). unfold s, after_drain. rewrite (proj2 (Z.eqb_neq _ _) Ee). cbn [drain_init ds_ecap].
        split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    destruct HE1 as (HEc1 & HPv1 & HPc1 & HPa1).
    set (s1 := sh_of (known_at L1 A1) (hs_held h1)) in *.
    set (rs1 := map (shr (known_at L1 A1)) (hl_recs (hs_expected h1))) in *.
    set (ks2 := cnl_keys 0 s1 rs1).
    assert (Hks2 : Forall (fun n => 0 <= n) ks2) by apply cnl_keys_nonneg.
    assert (Kc2 : forall c, bcnt c ks2 <= bcnt c (ekeys (rr_lines e h))) by (intros c; rewrite <- EK1; apply cnl_keys_bcnt_hl).
    assert (Kb2 : zsum (fun n => n) ks2 <= zsum (fun n => n) (ekeys (rr_lines e h))) by (rewrite <- EK1; apply cnl_keys_zsum_hl).
    pose proof P1 as (Hl1 & _).
    pose proof (zsum_id_nonneg _ Hdks) as Zdks. pose proof (zsum_id_nonneg _ Hks2) as Zks2.
    pose proof (credb_le_promb hj h i Hin) as CBP. pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as LCB.
    pose proof (ek_b_nonneg _ HLe) as EBN. pose proof (consb_le (ss_pl E) K) as CBM. rewrite CONSB_MAX_v in CBM.
    cbn [view_of rv_pend] in LCB, EBN.
    exists b1. split; [exact HR1|]. split.
    + intros qs2 _. rewrite roomF3.
      apply (pinv_cnl (ss_pl E) (p3_bytes b1 + zsum (fun n => n) ks2 + 134217728) qs2 rs1 0 s1 b1).
      unfold pinv. fold ks2. split; [rewrite Cp1; exact HLc|]. split; [rewrite Mp1; exact HLm|]. split; [exact Hl1|].
      split; [intros c Hc; exact (misT_count _ _ _ c HS1')|].
      split.
      { intros c Hc. pose proof (L1e c Hc). pose proof (ledger3_slack _ _ _ _ _ _ _ _ _ c HL Hc).
        pose proof (cred_le_prom hj h i c Hin). pose proof (Hdc c Hc). pose proof (Kc2 c).
        pose proof (arr_c_b (sh_cap s1) c). pose proof (ncb_b C1 c). pose proof (ncb_b CAP c).
        pose proof (ncb_b (re_cap e) c). pose proof (ncb_b (ent_ka e) c). pose proof (ncb_b (16 * ds_ecap s) c).
        pose proof (ncb_b (16 * hl_cap (hs_expected h)) c). pose proof (bcnt_nonneg c dks).
        rewrite Cp1. cbn [view_of rv_pend] in *. lia. }
      assert (SN : sh_n s1 = hl_n (hs_held h1)) by (unfold s1; apply sh_n_of).
      split; [exact Hks2|]. split; [rewrite SN; unfold hl_n; lia|].
      split.
      { rewrite SN. pose proof (cnl_keys_len 0 s1 rs1) as X. unfold rs1 in X. rewrite map_snd_shr in X.
        assert (P22 : 2 ^ 22 = 4194304) by reflexivity. fold rs1 ks2 in X. lia. }
      split; [lia|]. split; [pose proof (arr_pot_b (sh_cap s1)); lia|]. lia.
    + intros L2 A2 qs2 _ HR2. rewrite runF3 in HR2.
      pose proof (check_no_loss_effect3 s1 rs1 qs2 b1 Hl1) as X2. cbv zeta in X2. rewrite runF3 in X2.
      fold ks2 in X2. destruct X2 as (C2e & M2e & Hl2 & L2e & B2e & _ & _ & Hfs2).
      pose proof (cnl_misK (p3_mis b1) (slot3 (hl_cap (hs_held h)) (sptr_of L1 A1 (hl_v (hs_held h)))) qs2 [] rs1 0 s1 b1)
        as K2.
      set (b2 := run3 qs2 b1 0 (check_no_loss_tr 0 s1 rs1)) in *.
      set (s' := check_no_loss_sh 0 s1 rs1) in *.
      hnf. intros E' H' HSR HSLV HE'r HE'v HE'c HNDH' HTH' HB2a HB2b HB2c HSB2 HY2 HN2 gone d Hgone.
      exists b2. split; [exact HR2|]. split.
      * intros qs3 Hq3. exact (check_shape_ends_room3 _ _ _ _ _ b2 qs3 Hq3).
      * intros L3 A3 qs3 _ HR3. rewrite runF3 in HR3.
        pose proof (check_shape_ends_effect3 (known_at L2 A2) gone [] (hl_recs H') d qs3 b2 Hl2) as X3.
        cbv zeta in X3. rewrite runF3 in X3. destruct X3 as (C3e & M3e & Hl3 & L3e & B3e & _ & Hfs3).
        set (b3 := run3 qs3 b2 0 (check_shape_ends_tr (known_at L2 A2) gone [] (hl_recs H') d)) in *.
        hnf. intros H'' ds HH''v HH''c HPerm HB3a HB3b HSB3 HY3 HN3.
        exists b3. split; [exact HR3|]. split.
        -- intros qs4 _. apply roomF_frees, reset_free.
        -- intros L4 A4 qs4 _ HR4. rewrite runF3 in HR4.
           set (h3 := set_held (set_exp_held h1 E' H') H'') in *.
           destruct (frees3 qs4 (source_reset_tr (known_at L3 A3) h3) b3 0 (reset_free _ _) Hl3)
             as (Hl4 & C4e & M4e & L4e & B4e).
           set (b4 := run3 qs4 b3 0 (source_reset_tr (known_at L3 A3) h3)) in *.
           hnf. intros HB4a HB4b HY4. hnf. intros G' out' es' hj' Hcov Hpend Hek Hes' Hhj' HM HND4 HK HWs HWg.
           fold s1 rs1 in HSR, HSLV. fold s' in HSR, HSLV.
           destruct HSR as (HR'c & HR'v & _). destruct HSLV as (HSL1 & _).
           assert (EH3 : hs_pending h3 = hs_pending h1 /\ hs_partial h3 = hs_partial h1 /\ hs_expected h3 = E' /\
                         hs_held h3 = H'') by (unfold h3; cbn; auto).
           destruct EH3 as (EH3p & EH3a & EH3e & EH3h).
           assert (CH'' : hl_cap H'' = sh_cap s') by (rewrite HH''c; cbn [set_exp_held hs_held]; exact HR'c).
           assert (VH'' : hl_v H'' = hl_v H') by (rewrite HH''v; reflexivity).
           assert (CS1 : sh_cap s1 = hl_cap (hs_held h)) by (unfold s1, sh_of; cbn [sh_cap]; rewrite Hheld1; reflexivity).
           assert (SC3 : forall c, zsum (fun t => one_if c (band (snd t))) (src_dels h3) =
                     arr_c (hl_cap (hs_pending h)) c + one_if c (band PARTIAL_BYTES) + arr_c (ds_ecap s) c +
                     arr_c (sh_cap s') c).
           { intros c. rewrite src_cls, EH3p, EH3e, EH3h, HPc1, HE'c, HEc1, CH''. reflexivity. }
           assert (SZ3 : zsum snd (src_dels h3) =
                     16 * hl_cap (hs_pending h) + PARTIAL_BYTES + 16 * ds_ecap s + 16 * sh_cap s').
           { rewrite src_sz, EH3p, EH3e, EH3h, HPc1, HE'c, HEc1, CH''. reflexivity. }
           apply (p4_close E K G out es hj h b al alb L0 A0 L4 A4 b4 G' out' es' hj'
                    (SlotPass4.p4_dels out CAP OUT' C1 e h) (SlotPass4.p4_adds out CAP OUT' C1) (dks ++ ks2) HL HR0 HR4);
             [congruence|congruence|exact Hl4|apply Forall_app; split; assumption| | | | | |exact Hpend|exact Hek|
              exact Hes'|exact Hhj'|exact HM|exact HND4|exact HK|exact HWs|exact HWg].
           ++ intros c Hc. pose proof (L4e c Hc) as X4. pose proof (L3e c Hc) as X3. pose proof (L2e c Hc) as X2.
              pose proof (L1e c Hc) as X1.
              pose proof (reset_sum (fun n => one_if c (band n)) (known_at L3 A3) h3
                            (fun x _ => proj1 (one_if_b c (band x)))) as RS. cbv beta in RS. rewrite SC3 in RS.
              change (zsum (fun n => one_if c (band n)) (fsz (source_reset_tr (known_at L3 A3) h3))) with
                (bcnt c (fsz (source_reset_tr (known_at L3 A3) h3))) in RS.
              pose proof (p4_dl_le out CAP OUT' C1 e h c Hkh) as DL. rewrite src_cls in DL.
              unfold SlotPass4.p4_dels, SlotPass4.p4_adds. rewrite bcnt_app.
              pose proof (bcnt_nonneg c (map rec_len (cse_ds (known_at L2 A2) gone [] (hl_recs H') d))).
              pose proof (bcnt_nonneg c (cnl_frees 0 s1 rs1)).
              rewrite (ncb16 (ds_ecap s) c), (ncb16 (hl_cap (hs_expected h)) c) in X1. unfold arr_dl in X2.
              rewrite CS1 in X2. lia.
           ++ pose proof (reset_sum (fun n => n) (known_at L3 A3) h3 (fun x Hx => ltac:(lia))) as RS. cbv beta in RS.
              change (zsum (fun t => snd t) (src_dels h3)) with (zsum snd (src_dels h3)) in RS. rewrite SZ3 in RS.
              unfold SlotPass4.p4_dels, SlotPass4.p4_adds. rewrite (p4_db_eq out CAP OUT' C1 e h Hkh), src_sz.
              pose proof (zsum_id_nonneg _ Hfs2). pose proof (zsum_id_nonneg _ Hfs3).
              rewrite zsum_app. rewrite CS1 in B2e. lia.
           ++ intros c Hc. rewrite bcnt_app. pose proof (Hdc c Hc). pose proof (Kc2 c).
              pose proof (bcnt_nonneg c (ekeys_hl (hs_expected h))). lia.
           ++ rewrite zsum_app. pose proof (zsum_id_nonneg _ (ekeys_nonneg (map (fun r => bzs (snd r)) (hl_recs (hs_expected h))))).
              unfold ekeys_hl. lia.
           ++ pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU0 & _) & _).
              pose proof HR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU1 & _) & _).
              pose proof HR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU2 & _) & _).
              pose proof HR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU3 & _) & _).
              pose proof HR4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU4 & _) & _).
              assert (HK2 : misK (p3_mis b1) (slot3 (hl_cap (hs_held h)) (sptr_of L1 A1 (hl_v (hs_held h))))
                              (slot3 (sh_cap s1) (resolveF qs2 (sh_v s1)) ++ []) (p3_mis b1)).
              { eapply misK_S; [|exact (misK_init _ _)]. intros z Hz. rewrite app_nil_r.
                unfold s1, sh_of. cbn [sh_cap sh_v resolve known_at]. rewrite Hheld1. exact Hz. }
              apply (p4_mis_final L0 L1 L2 L3 L4 A0 A1 A2 A3 A4 (p3_mis b) (p3_mis b1) (p3_mis b2) (p3_mis b3) (p3_mis b4)
                       (slot3 CAP (resolveF qs1 (nm out)) ++ dsl qs1 (drain_init 0 CAP e h) a0 ++ [])
                       out CAP OUT' C1 (ds_ecap s) (hl_cap (hs_held h)) (sh_cap s') 0
                       (resolveF qs1 (remove_entry_out lv MX 0 CAP e h 0 a0)) (resolveF qs1 (da_ev a1))
                       (resolveF qs2 (sh_v s')) (sptr_of L1 A1 (hl_v (hs_held h))) e h h3
                       (view_of G out es hj) (view_of G' out' es' hj')
                       (fun e0 He0 => proj2 (HU0 e0 He0)) (fun e0 He0 => proj2 (HU1 e0 He0))
                       (fun e0 He0 => proj2 (HU2 e0 He0)) (fun e0 He0 => proj2 (HU3 e0 He0))
                       (fun e0 He0 => proj2 (HU4 e0 He0)) HND0 HN1 HN3 HY1 HY2 HY3 HY4 K1 (K2 HK2));
                [| | | |reflexivity|reflexivity| | | | |exact HK].
              ** intros e0 He0. destruct (run3_mis_src2 qs3 b2 0 _ e0 He0) as [(X & _)|X]; [exact X|].
                 exfalso. exact (frees_inplace qs3 0 _ _ (proj1 (ends_free _ _ _ _ _)) X).
              ** intros e0 He0. destruct (run3_mis_src2 qs4 b3 0 _ e0 He0) as [(X & Hu)|X];
                   [|exfalso; exact (frees_inplace qs4 0 _ _ (reset_free _ _) X)].
                 split; [exact X|]. intros x Hx Heq. destruct (reset_free_at (known_at L3 A3) h3 x Hx) as (m & Hm).
                 apply Hu. rewrite Heq. exact (touched_free qs4 _ m _ Hm).
              ** intros x Hx. unfold dsl, a0, nm. cbn [drain_init ds_cap ds_ka ds_ecap drain_start da_buf da_hp da_ev
                   resolve known_at].
                 rewrite !map_app, !in_app_iff in Hx. rewrite !in_app_iff.
                 destruct Hx as [Hx|[Hx|Hx]].
                 --- unfold out_move_dels in Hx. destruct (out_same out CAP OUT' C1 || (CAP =? 0)) eqn:Eo; [destruct Hx|].
                     destruct Hx as [<-|[]]. left. apply slot3_mem. apply orb_false_iff in Eo as [_ Eo].
                     apply Z.eqb_neq. exact Eo.
                 --- unfold entry_dels in Hx. rewrite map_app, in_app_iff in Hx. destruct Hx as [Hx|Hx].
                     +++ destruct (Z.eqb_spec (re_cap e) 0) as [Z0|Z0]; [destruct Hx|]. destruct Hx as [<-|[]].
                         right. left. left. apply slot3_mem. exact Z0.
                     +++ destruct (Z.eqb_spec (re_hp e) 0) as [Z0|Z0]; [destruct Hx|]. destruct Hx as [<-|[]].
                         right. left. right. left. apply slot3_mem. unfold ent_ka.
                         rewrite (proj2 (Z.eqb_neq _ _) Z0). exact (Hkh Z0).
                 --- apply arr_sz_in in Hx as (-> & Z0). right. left. right. right. apply slot3_mem. exact Z0.
              ** intros x Hx. unfold src_dels. rewrite EH3p, EH3a. rewrite !map_app, !in_app_iff.
                 apply in_app_or in Hx as [Hx|Hx].
                 --- left. unfold arr_sz in *. rewrite HPc1, HPv1. exact Hx.
                 --- right. left. rewrite HPa1. exact Hx.
              ** intros Hc'. split; [exact (HSL1 Hc')|]. rewrite <- (HR'v Hc').
                 apply src_dels_held; [rewrite EH3h, CH''; exact Hc'|rewrite EH3h, VH''; reflexivity].
              ** intros Hc' Hmem. apply src_dels_exp; [rewrite EH3e, HE'c, HEc1; exact Hc'|]. rewrite EH3e, HE'v.
                 destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
                 --- pose proof (HSL Ee) as (_ & _ & _ & (HEL & _) & _).
                     assert (Hpos : 0 < hl_cap (hs_expected h1)) by (rewrite HEc1; lia).
                     destruct (HEL Hpos) as (_ & Ha). exact Ha.
                 --- rewrite (Hh1 Ee).
                     assert (Ea1 : a1 = a0) by (unfold a1, after_drain_adr; rewrite (proj2 (Z.eqb_neq _ _) Ee); reflexivity).
                     assert (Es : ds_ecap s = hl_cap (hs_expected h))
                       by (unfold s, after_drain; rewrite (proj2 (Z.eqb_neq _ _) Ee); reflexivity).
                     rewrite Ea1. unfold a0, nm. cbn [drain_start da_ev resolve known_at].
                     destruct HSE as [X|X]; [rewrite Es in Hc'; contradiction|].
                     destruct (sptr_of_spec L0 A0 _ _ (proj2 (stdpp.base.NoDup_ListNoDup _) HND0) X) as (Hu0 & Ha0).
                     destruct Hmem as (n1 & Hn1). rewrite Ea1 in Hn1. unfold a0, nm in Hn1.
                     cbn [drain_start da_ev resolve known_at] in Hn1.
                     rewrite (HY1 _ _ _ Hu0 Hn1). exact Ha0.
              ** intros Hc0 Hne. destruct olv.
                 --- destruct (HQL eq_refl) as (Hu & Ha).
                     change (remove_entry_out lv MX 0 CAP e h 0 (drain_start (known_at L0 A0) (known_at L0 A0 out) e h))
                       with (remove_entry_out lv MX 0 CAP e h 0 a0) in Hu, Ha.
                     split; [exists C1; exact Hu|]. rewrite Ha.
                     apply (nc_move_adds_in _ _ _ _ _ _ _ _ (OUT', C1) HM). unfold SlotPass4.p4_adds, out_move_adds, out_same.
                     rewrite (proj2 (Z.eqb_neq C1 CAP) Hne), andb_false_r. left. reflexivity.
                 --- destruct (HQN eq_refl) as (_ & X). contradiction.
              ** intros Hc0 Heq. pose proof (Hoq Heq) as Eo. rewrite Eo. unfold nm. cbn [resolve known_at].
                 destruct HCAP as [X|X]; [rewrite <- Heq in X; contradiction|].
                 destruct (sptr_of_spec L0 A0 _ _ (proj2 (stdpp.base.NoDup_ListNoDup _) HND0) X) as (Hu0 & Ha0).
                 split; [exists CAP; exact Hu0|]. rewrite Ha0. split; [cbn [view_of rv_nc]; right; left; reflexivity|].
                 assert (EO : OUT' = out).
                 { destruct olv.
                   - destruct (HQL eq_refl) as (Hu & Ha).
                     change (remove_entry_out lv MX 0 CAP e h 0 (drain_start (known_at L0 A0) (known_at L0 A0 out) e h))
                       with (remove_entry_out lv MX 0 CAP e h 0 a0) in Hu, Ha.
                     rewrite Eo in Hu, Ha. unfold nm in Hu, Ha.
                     cbn [resolve known_at] in Hu, Ha. rewrite <- Ha, (HY1 _ _ _ Hu0 Hu). exact Ha0.
                   - exact (proj1 (HQN eq_refl)). }
                 unfold SlotPass4.p4_dels, out_move_dels, out_same. rewrite EO, Z.eqb_refl, Heq, Z.eqb_refl. cbn [andb orb app].
                 intros Hx. unfold target_addrs in HNT. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HNT.
                 apply List.NoDup_cons_iff in HNT as [_ HNT].
                 apply List.NoDup_cons_iff in HNT as [HNo _]. apply HNo. rewrite map_app, in_app_iff in Hx.
                 apply in_app_iff. destruct Hx as [Hx|Hx].
                 --- left. apply in_concat. exists (entry_blocks e). split; [apply in_map; exact Hine|].
                     exact (entry_dels_sub e out Hx).
                 --- right. apply in_concat. exists (hs_blocks h). split; [exact (in_map (fun p => hs_blocks (fst p)) _ _ Hin)|].
                     exact (src_dels_sub h out Hx).
Qed.

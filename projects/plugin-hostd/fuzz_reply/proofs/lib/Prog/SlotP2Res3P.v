From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF RelayModel RelayKeys RelayRep HarnessRep ListRep CheckRep ListTr
  HarnessTr send_line_b_c drain_b_c SlotMove SlotNcMove3 SlotRun3 SlotOp7R3 SlotResR3 SlotP5R3 SlotP5R3G SlotDrain3
  SlotP5Res3 SlotDrainWt3 SlotPass2Mv SlotP2Res3Aux SlotRI3P SlotPeak3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotPass2 SlotPass4.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cnl_RV_lift OK E k L A G out es hj h L' A' qs :
  SlotPass2.p2_cnl_RV_s RI3_reply E k L A G out es hj h L' A' qs -> OK A' ->
  SlotPass2.p2_cnl_RV_s (RI3P OK) E k L A G out es hj h L' A' qs.
Proof. intros H HO. unfold SlotPass2.p2_cnl_RV_s in *. intros. split; [eapply H; eassumption|exact HO]. Qed.

Lemma drain_RV_lift OK E k L A G out es hj e h CAP live fin fa L' A' qs :
  SlotPass2.p2_drain_RV_s RI3_reply E k L A G out es hj e h CAP live fin fa L' A' qs -> OK A' ->
  SlotPass2.p2_drain_RV_s (RI3P OK) E k L A G out es hj e h CAP live fin fa L' A' qs.
Proof. intros H HO. unfold SlotPass2.p2_drain_RV_s in *. intros. split; [eapply H; eassumption|exact HO]. Qed.

Lemma p2_cnl_core_b E k L A G out es hj i h j b al alb :
  res_ok_pack3 A b -> RI3_ledger rv_wt (ss_pl E) k (view_of G out es hj) L A b al alb ->
  List.NoDup (map fst (blocks L A)) -> nth_error hj i = Some (h, j) -> SlotPass4.p4_src_blk L A h ->
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
  (forall qs, length qs = nretF (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h))
                                  (map (shr (known_at L A)) (hl_recs (hs_expected h)))) ->
     roomF pack3_form qs b (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h))
                              (map (shr (known_at L A)) (hl_recs (hs_expected h))))) /\
  (forall L' A' qs, length qs = nretF (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h))
                                        (map (shr (known_at L A)) (hl_recs (hs_expected h)))) ->
     rt_ok pack3_form A' (runF pack3_form qs b (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h))
                                                  (map (shr (known_at L A)) (hl_recs (hs_expected h))))) ->
     SlotPass2.p2_cnl_RV_s RI3_reply E k L A G out es hj h L' A' qs).
Proof.
  intros HR HL HND Hhj HSB HBd.
  pose proof (nth_error_In _ _ Hhj) as Hin.
  pose proof HL as (_ & _ & _ & HlL & _ & _ & _ & _ & _ & _ & _ & HMis & _).
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  split.
  - intros qs Hq.
    exact (check_no_loss_room3 rv_wt (ss_pl E) k (view_of G out es hj) L A b al alb (hs_held h) (hs_expected h) HL HBd
             (fun c _ => ek_view_in G out es hj (h, j) c Hin) (ek_view_in_b G out es hj (h, j) Hin) qs Hq).
  - intros L' A' qs _ HR'.
    intros E' H' HSR _ _ _ _ _ _ _ _ _ _ G' out' es' hj' _ Hpend (k1 & k2 & Ek1 & Ek2) Hes' Hhj' HM HND' HK HWs HWg.
    destruct HSR as (Hsc & Hsv & _).
    pose proof (check_no_loss_effect3 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h)))
                  qs b HlL) as X.
    cbv zeta in X. destruct X as (C1 & C2 & C3 & C4 & C5 & _ & _ & C8).
    pose proof (cnl_misK (p3_mis b)
                  (slot3 (sh_cap (sh_of (known_at L A) (hs_held h))) (resolveF qs (sh_v (sh_of (known_at L A) (hs_held h))))
                   ++ []) qs [] (map (shr (known_at L A)) (hl_recs (hs_expected h))) 0%nat
                  (sh_of (known_at L A) (hs_held h)) b (misK_init _ _)) as GM.
    apply (step3 E k k (view_of G out es hj) L A b al alb (view_of G' out' es' hj') L' A'
             (runF pack3_form qs b (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h))
                (map (shr (known_at L A)) (hl_recs (hs_expected h))))) (ekeys_hl (hs_expected h))
             (fun c => arr_dl (hl_cap (hs_held h)) (hl_cap H') c) (16 * hl_cap H' - 16 * hl_cap (hs_held h))
             (p2_arr_dels (hs_held h) H')
             (fun p => In p (slot3 (hl_cap H') (resolveF qs (sh_v (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
                         (map (shr (known_at L A)) (hl_recs (hs_expected h))))))))
             HL HR).
    + exact (ekeys_nonneg _).
    + exact HR'.
    + exact C1.
    + exact C2.
    + exact C3.
    + intros c Hc. rewrite (C4 c Hc), <- Hsc.
      change (sh_cap (sh_of (known_at L A) (hs_held h))) with (hl_cap (hs_held h)).
      pose proof (cnl_keys_bcnt_hl (known_at L A) 0 (sh_of (known_at L A) (hs_held h)) (hs_expected h) c).
      pose proof (bcnt_nonneg c (cnl_frees 0 (sh_of (known_at L A) (hs_held h))
                    (map (shr (known_at L A)) (hl_recs (hs_expected h))))).
      cbv beta. lia.
    + rewrite C5, <- Hsc. change (sh_cap (sh_of (known_at L A) (hs_held h))) with (hl_cap (hs_held h)).
      pose proof (cnl_keys_zsum_hl (known_at L A) 0 (sh_of (known_at L A) (hs_held h)) (hs_expected h)).
      pose proof (zsum_id_nonneg _ C8). lia.
    + intros e0 He0. destruct (GM e0 He0) as [Hs|(Hm & Hn)].
      * right. cbv beta. rewrite app_nil_r, <- Hsc in Hs. exact Hs.
      * left. split; [exact Hm|]. intros X. destruct (HU e0 Hm) as (_ & n & Hn0). apply Hn.
        revert X. unfold p2_arr_dels.
        destruct (p2_same (hl_v (hs_held h)) (hl_cap (hs_held h)) (hl_v H') (hl_cap H')); cbv beta iota; [intros []|].
        unfold arr_sz. destruct (Z.eqb_spec (hl_cap (hs_held h)) 0) as [C|C]; cbv beta iota; [intros []|].
        intros [X|[]]. cbn [fst] in X.
        rewrite app_nil_r. change (sh_cap (sh_of (known_at L A) (hs_held h))) with (hl_cap (hs_held h)).
        rewrite (slot3_nz _ _ C). left. exact (sptr_at L A (fst e0) n _ HND Hn0 (eq_sym X)).
    + intros p Hp. cbv beta in Hp. apply slot3_in in Hp as (Hc0 & <-).
      assert (Hc1 : sh_cap (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
                      (map (shr (known_at L A)) (hl_recs (hs_expected h)))) <> 0) by (rewrite <- Hsc; exact Hc0).
      rewrite <- (Hsv Hc1).
      destruct (p2_same (hl_v (hs_held h)) (hl_cap (hs_held h)) (hl_v H') (hl_cap H')) eqn:S.
      * pose proof S as S'. unfold p2_same in S'. apply andb_prop in S' as [S1 S2]. apply Z.eqb_eq in S1, S2.
        rewrite S1. destruct HSB as (_ & _ & _ & (HSH & _) & _).
        apply (p2r_keep _ _ _ _ _ _ _ _ _ HM).
        -- apply (p2r_rv_src G out es hj (h, j) _ Hin). apply (p2r_snc_held h). clear S. lia.
        -- unfold p2_arr_dels. rewrite S. cbv beta iota. intros [].
        -- exists (16 * hl_cap (hs_held h)). destruct HSH as [C|C]; [clear S; lia|exact C].
      * apply (nc_move_adds_in _ _ _ _ _ _ _ _ (hl_v H', 16 * hl_cap H') HM). unfold p2_arr_adds, arr_sz. rewrite S.
        cbv beta iota. rewrite (proj2 (Z.eqb_neq (hl_cap H') 0) Hc0). cbv beta iota. left. reflexivity.
    + exact HND'.
    + exact HK.
    + exact (nc_len G' out' es' hj' Hes' Hhj').
    + intros c Hc. pose proof (proj1 (nc_move_grow3 _ _ _ _ _ _ _ _ HM) c Hc) as G1. rewrite p2r_arr_dl in G1.
      cbv beta. unfold arr_dl. lia.
    + pose proof (proj2 (nc_move_grow3 _ _ _ _ _ _ _ _ HM)) as G2. rewrite p2r_arr_db in G2. lia.
    + exact HWs.
    + assert (EK : zlen (ekeys_hl (hs_expected h)) = Z.of_nat (count_begin (texts (hs_expected h))))
        by exact (p2r_ek_cb _).
      change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj').
      change (rv_wt (view_of G out es hj)) with (nc_wt es hj).
      unfold cnl_wt in HWg. rewrite EK. unfold NC_PER, DATA_PER in *. lia.
    + split.
      * intros c Hc. rewrite !ek_c_view. cbn [view_of rv_pend]. rewrite Hpend, Ek1, Ek2, !bcnt_app. lia.
      * rewrite !ek_b_view. cbn [view_of rv_pend]. rewrite Hpend, Ek1, Ek2, !zsum_app. lia.
    + exact (ek_view_nonneg hj').
Qed.

Theorem p2_cnl_res_s_RI3P OK RM : RMH RM -> SlotPass2.p2_cnl_res_s (pack3P OK RM) (RI3P OK).
Proof.
  intros HRM E k L A G out es hj i e h j ((b & al & alb & HR & HL) & HOK) HND _ _ _ _ Hhj HSB HBd.
  destruct (p2_cnl_core_b E k L A G out es hj i h j b al alb HR HL HND Hhj HSB HBd) as [ROOM POST].
  pose proof (nth_error_In _ _ Hhj) as Hin.
  pose proof HL as (HCs & HMc & _ & _ & _ & Halb & _).
  pose proof (cnl_keys_zsum_hl (known_at L A) 0 (sh_of (known_at L A) (hs_held h)) (hs_expected h)) as K1.
  pose proof (ek_view_in_b G out es hj (h, j) Hin) as K2. cbn [fst] in K2.
  pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as K3. pose proof (consb_le (ss_pl E) k) as K4.
  pose proof (promb_nonneg (rv_pend (view_of G out es hj))) as K5.
  pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as K6.
  pose proof (cnl_keys_len 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h))))
    as KL.
  rewrite map_snd_shr in KL.
  pose proof (cnl_keys_nonneg 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h))))
    as KN.
  pose proof (sh_n_of (known_at L A) (hs_held h)) as SN.
  pose proof (arr_pot_b (sh_cap (sh_of (known_at L A) (hs_held h)))) as AP.
  assert (X : PB3_MAX + CONSB_MAX + 201326592 <= CF_MAX) by (apply Z.leb_le; vm_compute; reflexivity).
  rewrite CONSB_MAX_v in X, K4. rewrite P22_v in HBd.
  assert (NV : NMAX = 536879104) by reflexivity.
  hnf. exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs Hq. apply (proj2 (roomF_pack3P OK RM qs b _)). split; [exact (ROOM qs Hq)|].
    apply (RMrun_of_peak RM (ss_pl E) b _
      (zsum (fun n => n) (cnl_keys 0 (sh_of (known_at L A) (hs_held h))
         (map (shr (known_at L A)) (hl_recs (hs_expected h)))) + 201326592) HRM HCs HMc).
    + lia.
    + apply cpk_cnl. unfold cpk. split; [exact KN|]. split; [unfold sh_n; lia|]. lia.
  - intros L' A' qs Hq (HR' & HOK'). apply cnl_RV_lift; [|exact HOK']. exact (POST L' A' qs Hq HR').
Qed.

Lemma p2r_drain_core_b E k L A G out es hj i e h j live mx NO CAP b al alb :
  res_ok_pack3 A b -> RI3_ledger rv_wt (ss_pl E) k (view_of G out es hj) L A b al alb ->
  List.NoDup (map fst (blocks L A)) ->
  List.NoDup (target_addrs G out es hj) -> nth_error es i = Some e -> nth_error hj i = Some (h, j) ->
  SlotPass4.p4_ent_blk L A e -> SlotPass4.p4_src_blk L A h -> (CAP = 0 \/ In (out, CAP) (blocks L A)) ->
  0 <= mx -> 0 <= CAP -> hl_recs (hs_expected h) = [] -> ecap_ok (hl_cap (hs_expected h)) ->
  Z.of_nat (length (pending_stream h)) < WRITE_MAX * OPS_MAX ->
  0 <= re_cap e -> 0 <= ent_ka e -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
  re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 -> Z.of_nat (length (re_U e)) <= re_used e ->
  (re_hp e <> 0 -> re_kh e <> 0) -> ds_ocap (drain_fin live mx NO CAP e h) <= NMAX ->
  (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) -> (length es <= 4)%nat -> (length hj <= 4)%nat ->
  (forall qs, length qs = nretF (drain_tr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)) ->
     roomF pack3_form qs b (drain_tr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h))) /\
  (forall L' A' qs, length qs = nretF (drain_tr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)) ->
     rt_ok pack3_form A' (runF pack3_form qs b
       (drain_tr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h))) ->
     SlotPass2.p2_drain_RV_s RI3_reply E k L A G out es hj e h CAP live (drain_fin live mx NO CAP e h)
       (drain_adr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)) L' A' qs).
Proof.
  intros HR HL HND HTA Hes Hhj HEB HSB HCB Hmx HC Hexp Hok Hps Hrc Hka HJ Hoff Hnh Hu Hkh HON HO0 Hle Hlh.
  destruct (nth_error_split es i Hes) as (es1 & es2 & -> & _).
  destruct (nth_error_split hj i Hhj) as (hj1 & hj2 & -> & _).
  clear Hes Hhj.
  assert (Hl1 : (length es1 + length es2 <= 3)%nat) by (rewrite length_app in Hle; cbn [length] in Hle; lia).
  assert (Hl2 : (length hj1 + length hj2 <= 3)%nat) by (rewrite length_app in Hlh; cbn [length] in Hlh; lia).
  destruct (p2r_target G out es1 e es2 hj1 h j hj2 HTA) as (T1 & T2 & T3 & T4).
  assert (Hin_e : In e (es1 ++ e :: es2)) by (apply in_or_app; right; left; reflexivity).
  assert (Hin_h : In (h, j) (hj1 ++ (h, j) :: hj2)) by (apply in_or_app; right; left; reflexivity).
  pose proof HL as (_ & _ & _ & HlL & _ & _ & _ & _ & _ & HW2 & _ & HMis & _).
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  assert (Hn0 : hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25).
  { unfold hl_n. rewrite Hexp. cbn [length]. unfold WRITE_MAX, OPS_MAX in Hps.
    assert (E25 : 2 ^ 25 = 33554432) by reflexivity. lia. }
  assert (Hpow : hl_cap (hs_expected h) = 0 \/ exists k0, 0 <= k0 /\ hl_cap (hs_expected h) = 8 * 2 ^ k0).
  { pose proof Hok as [E0|(k0 & Hk0 & E0)]; [left; exact E0|right; exists k0; split; [lia|exact E0]]. }
  pose proof (drain3_ecap e h Hoff Hok Hn0 live mx NO CAP) as HEC.
  pose proof (drain3_holds e h Hrc Hka HJ Hoff Hnh Hpow Hn0) as HD3.
  pose proof (drain_wt3_holds e h Hrc Hka HJ Hoff Hnh Hpow Hn0 Hu) as HW3.
  pose proof (HD3 live mx NO CAP Hmx HC) as HD. cbv zeta in HD. destruct HD as [_ HDR].
  assert (Hpk : pk3_ok b) by exact (ledger3_pk3 _ _ _ _ _ _ _ _ _ HL).
  assert (Hlive : forall c, 0 <= c < 49 -> znth c (p3_live b) + cred h c + DRAIN_HR <= znth c (p3_cap b)).
  { intros c Hc. pose proof (ledger3_slack _ _ _ _ _ _ _ _ _ c HL Hc) as SL. cbn [view_of rv_pend] in SL.
    rewrite p2r_pend_split in SL. pose proof (p2r_cred_le (pend_view hj1) (pend_view hj2) h c). unfold DRAIN_HR. lia. }
  assert (Hbytes : p3_bytes b - CAP + 2 * ds_ocap (drain_fin live mx NO CAP e h) + DRAIN_B <= BMAX).
  { pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HB0. rewrite PB3_MAX_val in HB0.
    assert (EB : BMAX = 17592186044416) by reflexivity. assert (EN : NMAX = 536879104) by reflexivity.
    assert (ED : DRAIN_B = 1099511627776) by reflexivity. lia. }
  assert (HmisT : forall qs, misT (slot3 CAP (resolveF qs (known_at L A out)) ++
      dslots qs e h (drain_start (known_at L A) (known_at L A out) e h) ++ map (sptr_of L A) (p2r_rest G es1 es2 hj1 hj2 h))
      (0 + res3 CAP + dres e h) (p3_mis b)).
  { intros qs. exact (p2r_misT L A b G out es1 e es2 hj1 h j hj2 CAP qs HMis HR HND Hkh HO0 Hl1 Hl2). }
  split.
  - intros qs _. rewrite roomF3.
    exact (proj1 (HDR qs b 0%nat (drain_start (known_at L A) (known_at L A out) e h) _ 0%nat Hpk HON Hlive Hbytes
                    (HmisT qs))).
  - intros L' A' qs _ HR'.
    destruct (HDR qs b 0%nat (drain_start (known_at L A) (known_at L A out) e h) _ 0%nat Hpk HON Hlive Hbytes (HmisT qs))
      as (_ & Hpk' & Ecap & Emc & (dks & Hdk & Hdl & Hdb & Hc1 & Hc2) & _ & _).
    intros e' h' OUT' Hlv Hdd Hel Hsl Ecp Eka Eec G' out' es' hj' _ (p1 & p2 & Ep1 & Ep2) (k1 & k2 & Ek1 & Ek2) Hes' Hhj'
      HM HND' HK HWs HWg.
    assert (HR2 : res_ok_pack3 A' (run3 qs b 0 (drain_tr live mx NO CAP e h 0
                    (drain_start (known_at L A) (known_at L A out) e h)))) by exact HR'.
    assert (Hcn : 0 <= ds_cap (drain_fin live mx NO CAP e h))
      by exact (p2r_cap_nn (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) 0%nat dadr0 Hrc).
    pose proof (ecap_ok_lt _ HEC) as Hecn.
    pose proof (HW3 live mx NO CAP Hmx HC) as W3.
    rewrite drain_wt_bridge in HWg.
    assert (DS : zsumZ (fun c => cred h c - bcnt c (ekeys (lines (hs_state h) (bzs (pending_stream h))))) (zseq 0 49) =
                 zsumZ (cred h) (zseq 0 49) - zlen (ekeys (lines (hs_state h) (bzs (pending_stream h)))))
      by exact (p2r_da_sum h _ (ekeys_nonneg _)).
    destruct HEB as (HEB1 & HEB2 & _).
    destruct HSB as (_ & _ & (HSE & _) & _).
    destruct Hel as (Hel1 & Hel2 & _).
    destruct Hsl as (_ & _ & _ & (Hx1 & _) & _).
    assert (GM : misK (p3_mis b)
        (slot3 (ds_ocap (drain_init NO CAP e h)) (resolveF qs (da_out (drain_start (known_at L A) (known_at L A out) e h))) ++
         dsl qs (drain_init NO CAP e h) (drain_start (known_at L A) (known_at L A out) e h) ++ [])
        (slot3 (ds_ocap (drain_fin live mx NO CAP e h))
           (resolveF qs (da_out (drain_adr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)))) ++
         dsl qs (drain_fin live mx NO CAP e h)
           (drain_adr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)) ++ [])
        (p3_mis (run3 qs b 0 (drain_tr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h))))).
    { pose proof (drain_misK (p3_mis b)
        (slot3 (ds_ocap (drain_init NO CAP e h)) (resolveF qs (da_out (drain_start (known_at L A) (known_at L A out) e h))) ++
         dsl qs (drain_init NO CAP e h) (drain_start (known_at L A) (known_at L A out) e h) ++ [])
        qs [] (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) 0%nat
        (drain_start (known_at L A) (known_at L A out) e h) b HC (misK_init _ _)) as X.
      cbv zeta in X. destruct X as [_ X].
      rewrite (drain_st live mx (S (S (length (pending_stream h)))) (drain_init NO CAP e h) 0%nat
                 (drain_start (known_at L A) (known_at L A out) e h) 0%nat dadr0) in X.
      exact X. }
    hnf. eexists; eexists; eexists. split; [exact HR2|].
    apply (ledger3_call3 rv_wt (ss_pl E) k (view_of G out (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2)) L A b al alb k
             (view_of G' out' es' hj') L' A' _
             (fun c => ncb (ds_ocap (drain_fin live mx NO CAP e h)) c - ncb CAP c + dchain e h (drain_fin live mx NO CAP e h) c)
             (ds_ocap (drain_fin live mx NO CAP e h) - CAP + dchainb e h (drain_fin live mx NO CAP e h))
             (fun c => cred h c - bcnt c (ekeys (lines (hs_state h) (bzs (pending_stream h)))))
             (credb h - zsum (fun n => n) (ekeys (lines (hs_state h) (bzs (pending_stream h))))) HL).
    + split; [exact (nc_len G' out' es' hj' Hes' Hhj')|].
      split.
      { intros c Hc. pose proof (proj1 (nc_move_grow3 _ _ _ _ _ _ _ _ HM) c Hc) as G1.
        pose proof (p2r_dr_dl out CAP OUT' e e' h (hs_expected h') (drain_fin live mx NO CAP e h) c Hkh Ecp Eka Eec) as D1.
        cbv beta. lia. }
      split.
      { pose proof (proj2 (nc_move_grow3 _ _ _ _ _ _ _ _ HM)) as G2.
        pose proof (p2r_dr_db out CAP OUT' e e' h (hs_expected h') (drain_fin live mx NO CAP e h) Ecp Eka Eec) as D2. lia. }
      split; [exact HWs|].
      split.
      { change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj').
        change (rv_wt (view_of G out (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2)))
          with (nc_wt (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2)) in HW2.
        rewrite DS. unfold NC_PER, DATA_PER in *. lia. }
      split.
      { intros c Hc. pose proof (ledger3_credit _ _ _ _ _ _ _ _ _ c HL Hc) as LC.
        rewrite ek_c_view in LC. rewrite ek_c_view. cbn [view_of rv_pend] in LC |- *.
        rewrite Ep1, Ek1 in LC. rewrite Ep2, Ek2. rewrite !bcnt_app in LC. rewrite !bcnt_app.
        rewrite p2r_prom in LC. rewrite p2r_prom. rewrite zsum_nil. cbv beta. unfold cred. lia. }
      split.
      { pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as LB.
        rewrite ek_b_view in LB. rewrite ek_b_view. cbn [view_of rv_pend] in LB |- *.
        rewrite Ep1, Ek1 in LB. rewrite Ep2, Ek2. rewrite p2r_promb in LB. rewrite p2r_promb.
        rewrite !zsum_app in LB. rewrite !zsum_app. rewrite zsum_nil. unfold credb. lia. }
      exact (ek_view_nonneg hj').
    + intros c Hc. cbv beta. pose proof (Hc1 c Hc). pose proof (bcnt_nonneg c dks). lia.
    + pose proof (zsum_id_nonneg dks Hdk). lia.
    + exact Ecap.
    + exact Emc.
    + exact (proj1 Hpk').
    + intros c Hc. cbv beta. pose proof (Hdl c Hc). pose proof (Hc1 c Hc). lia.
    + pose proof (zsum_id_nonneg dks Hdk). lia.
    + apply (mis3_keep (view_of G out (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2)) L A (view_of G' out' es' hj') L' A' b _
               (p2_dr_dels out CAP OUT' (ds_ocap (drain_fin live mx NO CAP e h)) e e' (hs_expected h) (hs_expected h'))
               (fun p => In p (slot3 (ds_ocap (drain_fin live mx NO CAP e h))
                                 (resolveF qs (da_out (drain_adr live mx NO CAP e h 0
                                    (drain_start (known_at L A) (known_at L A out) e h)))) ++
                               dsl qs (drain_fin live mx NO CAP e h)
                                 (drain_adr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h))) /\
                         exists n, In (p, n) (user_blocks A'))
               HMis HR HR2 HND' HK).
      * intros e0 He0. destruct (GM e0 He0) as [Hs|(Hm & Hn)].
        -- right. cbv beta. rewrite app_nil_r in Hs. split; [exact Hs|].
           pose proof HR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU' & _) & _).
           destruct (HU' e0 He0) as (_ & n & Hn'). exists n. exact Hn'.
        -- left. split; [exact Hm|]. destruct (HU e0 Hm) as (_ & n & Hb0).
           exact (p2r_excl L A qs NO CAP out e e' h (hs_expected h') OUT' (ds_ocap (drain_fin live mx NO CAP e h))
                    (fst e0) n HND Hb0 Hkh Hn).
      * intros p (Hp & n' & Hn'). rewrite in_app_iff in Hp. unfold dsl in Hp. rewrite !in_app_iff in Hp.
        destruct Hp as [Hp|[Hp|[Hp|Hp]]]; apply slot3_in in Hp as (Hc0 & <-).
        -- destruct live.
           ++ destruct (Hlv eq_refl) as (_ & Ep). rewrite Ep.
              destruct (out_same out CAP OUT' (ds_ocap (drain_fin true mx NO CAP e h))) eqn:Os.
              ** pose proof Os as Os'. unfold out_same in Os'. apply andb_prop in Os' as [O1 O2].
                 apply Z.eqb_eq in O1, O2. rewrite O1. apply (p2r_keep _ _ _ _ _ _ _ _ _ HM).
                 --- exact (p2r_rv_out G out _ _).
                 --- exact (p2r_nd_out out CAP OUT' _ e e' h (hs_expected h') T1 T2 Os).
                 --- exists CAP. destruct HCB as [C0|C0]; [exfalso; clear Os; lia|exact C0].
              ** apply (nc_move_adds_in _ _ _ _ _ _ _ _ (OUT', ds_ocap (drain_fin true mx NO CAP e h)) HM).
                 unfold p2_dr_adds. apply in_or_app. left. unfold out_move_adds. rewrite Os. cbv beta iota.
                 left. reflexivity.
           ++ destruct (Hdd eq_refl) as (EO & Eoc).
              assert (Eo : da_out (drain_adr false mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)) =
                           known_at L A out)
                by exact (p2r_drain_out (S (S (length (pending_stream h)))) mx (drain_init NO CAP e h) 0%nat
                            (drain_start (known_at L A) (known_at L A out) e h)).
              rewrite Eo in Hn' |- *.
              assert (C0 : CAP <> 0) by lia.
              destruct HCB as [X|HCB']; [contradiction|].
              destruct (p2r_sptr_spec L A out CAP HND HCB') as (Hus & Hpa).
              change (resolveF qs (known_at L A out)) with (sptr_of L A out) in Hn' |- *.
              apply (HK (sptr_of L A out) CAP n' Hus Hn').
              ** rewrite Hpa. exact (p2r_rv_out G out _ _).
              ** rewrite Hpa. apply (p2r_nd_out out CAP OUT' _ e e' h (hs_expected h') T1 T2).
                 unfold out_same. rewrite EO, Eoc, !Z.eqb_refl. reflexivity.
        -- assert (Hcp : 0 < re_cap e') by lia.
           destruct (Hel1 Hcp) as (_ & Ep). rewrite Ep.
           destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e')) eqn:S.
           ++ pose proof S as S'. unfold p2_same in S'. apply andb_prop in S' as [S1 S2]. apply Z.eqb_eq in S1, S2.
              assert (C0 : re_cap e <> 0) by (clear S; lia).
              rewrite S1. apply (p2r_keep _ _ _ _ _ _ _ _ _ HM).
              ** exact (p2r_rv_ent G out _ _ e _ Hin_e (p2r_enc_buf e C0)).
              ** exact (p2r_nd_buf out CAP OUT' _ e e' h (hs_expected h') T1 T3 T4 C0 S).
              ** exists (re_cap e). destruct HEB1 as [X|X]; [contradiction|exact X].
           ++ apply (nc_move_adds_in _ _ _ _ _ _ _ _ (re_buf e', re_cap e') HM).
              unfold p2_dr_adds. apply in_or_app. right. apply in_or_app. left.
              unfold p2_buf_adds. rewrite S. cbn [orb]. rewrite (proj2 (Z.eqb_neq (re_cap e') 0) ltac:(lia)).
              cbv beta iota. left. reflexivity.
        -- assert (Hh' : re_hp e' <> 0) by (apply p2r_ka_hp; lia).
           destruct (Hel2 Hh') as (_ & Ep). rewrite Ep.
           destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e')) eqn:S.
           ++ pose proof S as S'. unfold p2_same in S'. apply andb_prop in S' as [S1 S2]. apply Z.eqb_eq in S1, S2.
              assert (C0 : re_hp e <> 0) by (rewrite <- S1; exact Hh').
              rewrite S1. apply (p2r_keep _ _ _ _ _ _ _ _ _ HM).
              ** exact (p2r_rv_ent G out _ _ e _ Hin_e (p2r_enc_hp e C0)).
              ** exact (p2r_nd_hp out CAP OUT' _ e e' h (hs_expected h') T1 T3 T4 C0 S).
              ** exists (re_kh e). destruct HEB2 as [X|X]; [contradiction|exact X].
           ++ apply (nc_move_adds_in _ _ _ _ _ _ _ _ (re_hp e', re_kh e') HM).
              unfold p2_dr_adds. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
              unfold p2_hp_adds. rewrite S. cbn [orb]. rewrite (proj2 (Z.eqb_neq (re_hp e') 0) Hh').
              cbv beta iota. left. reflexivity.
        -- assert (Hcp : 0 < hl_cap (hs_expected h')) by lia.
           destruct (Hx1 Hcp) as (_ & Ep). rewrite Ep.
           destruct (p2_same (hl_v (hs_expected h)) (hl_cap (hs_expected h)) (hl_v (hs_expected h'))
                       (hl_cap (hs_expected h'))) eqn:S.
           ++ pose proof S as S'. unfold p2_same in S'. apply andb_prop in S' as [S1 S2]. apply Z.eqb_eq in S1, S2.
              assert (C0 : hl_cap (hs_expected h) <> 0) by (clear S; lia).
              rewrite S1. apply (p2r_keep _ _ _ _ _ _ _ _ _ HM).
              ** exact (p2r_rv_src G out _ _ (h, j) _ Hin_h (p2r_snc_exp h C0)).
              ** exact (p2r_nd_arr out CAP OUT' _ e e' h (hs_expected h') T2 T4 C0 S).
              ** exists (16 * hl_cap (hs_expected h)). destruct HSE as [X|X]; [contradiction|exact X].
           ++ apply (nc_move_adds_in _ _ _ _ _ _ _ _ (hl_v (hs_expected h'), 16 * hl_cap (hs_expected h')) HM).
              unfold p2_dr_adds. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
              unfold p2_arr_adds, arr_sz. rewrite S. cbv beta iota.
              rewrite (proj2 (Z.eqb_neq (hl_cap (hs_expected h')) 0) ltac:(lia)). cbv beta iota. left. reflexivity.
Qed.

Theorem p2_drain_res_s_RI3P_le OK RM : PB3_MAX + 1912653167 <= CF_MAX -> RMH RM ->
  SlotPass2.p2_drain_res_s (pack3P OK RM) (RI3P OK).
Proof.
  intros X HRM E k L A G out es hj i e h j live mx NO CAP ((b & al & alb & HR & HL) & HOK) HND _ _ _ HTA Hes Hhj _ HEB
    HSB HCB Hmx HNO _ Hexp Hok Hps Hrc Hka HJ Hoff Hnh Hu Hkh HON HO0 Hle Hlh.
  assert (HTA' : List.NoDup (target_addrs G out es hj))
    by (first [exact HTA | exact (proj1 (stdpp.base.NoDup_ListNoDup _) HTA)]).
  destruct (p2r_drain_core_b E k L A G out es hj i e h j live mx NO CAP b al alb HR HL HND HTA' Hes Hhj HEB HSB HCB
    (proj1 Hmx) ltac:(lia) Hexp Hok Hps Hrc Hka HJ Hoff Hnh Hu Hkh HON HO0 Hle Hlh) as [ROOM POST].
  assert (Hn0 : hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25).
  { unfold hl_n. rewrite Hexp. cbn [length]. unfold WRITE_MAX, OPS_MAX in Hps.
    assert (E25 : 2 ^ 25 = 33554432) by reflexivity. lia. }
  assert (Hpow : hl_cap (hs_expected h) = 0 \/ exists k0, 0 <= k0 /\ hl_cap (hs_expected h) = 8 * 2 ^ k0).
  { pose proof Hok as [E0|(k0 & Hk0 & E0)]; [left; exact E0|right; exists k0; split; [lia|exact E0]]. }
  split; [exact (drain3_ecap e h Hoff Hok Hn0 live mx NO CAP)|].
  destruct (drain_peak3 e h live mx NO CAP 0 (drain_start (known_at L A) (known_at L A out) e h) Hrc Hka HJ Hoff Hnh
    Hpow Hn0 (proj1 Hmx) HNO HON) as [PK _].
  pose proof HL as (HCs & HMc & _).
  assert (HPB : p3_bytes b + credb h <= PB3_MAX).
  { pose proof (ledger3_alsum _ _ _ _ _ _ _ _ _ HL) as HS.
    pose proof HL as (_ & _ & _ & _ & _ & _ & HE & HB & HW1 & HW2 & HP & _).
    pose proof (consb_le (ss_pl E) k). pose proof (cdat_le (ss_pl E) k).
    pose proof (ek_b_nonneg _ HE).
    destruct (nth_error_split hj i Hhj) as (hj1 & hj2 & Ehj & _).
    assert (CP : promb (rv_pend (view_of G out es hj)) = promb (pend_view hj1) + credb h + promb (pend_view hj2)).
    { cbn [view_of rv_pend]. rewrite Ehj, p2r_pend_split, p2r_promb. unfold credb. reflexivity. }
    pose proof (promb_nonneg (pend_view hj1)). pose proof (promb_nonneg (pend_view hj2)).
    unfold PB3_MAX, NC_PER, DATA_PER in *. lia. }
  assert (EN : NMAX = 536879104) by reflexivity. assert (EN2 : NMAX / 2 = 268439552) by reflexivity.
  assert (E30 : 2 ^ 30 = 1073741824) by reflexivity.
  unfold WRITE_MAX, OPS_MAX in Hps.
  hnf. exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs Hq. apply (proj2 (roomF_pack3P OK RM qs b _)). split; [exact (ROOM qs Hq)|].
    apply (RMrun_of_peak RM (ss_pl E) b _
      (NMAX / 2 + Z.of_nat (length (pending_stream h)) + 6000 + 32768 + 2 ^ 30 + NMAX + credb h) HRM HCs HMc).
    + lia.
    + apply PK. lia.
  - intros L' A' qs Hq (HR' & HOK'). apply drain_RV_lift; [|exact HOK']. exact (POST L' A' qs Hq HR').
Qed.

Theorem p2_drain_res_s_RI3P OK RM : RMH RM -> SlotPass2.p2_drain_res_s (pack3P OK RM) (RI3P OK).
Proof. apply p2_drain_res_s_RI3P_le. apply Z.leb_le. vm_compute. reflexivity. Qed.

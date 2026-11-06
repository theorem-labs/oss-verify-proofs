From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c SlotRun3 SlotP5R3 SlotP5R3G SlotDrain3Aux SlotDrain3 SlotDrainWt3 SlotP5Res3 SlotRI3P SlotPeak3.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition p5c_res3_fullP (OK : astate -> Prop) (RM : pbound3 -> Z -> Prop) : Prop :=
  forall (E : sstart) (K K' : Z) (L : layout) (A : astate) (G OUT : Z) (es : list rentry) (hs : list (hsrc * nat))
         (lv : bool) (mx NO CAP : Z) (pre : list Z),
    let nm := known_at L A in
    let V := view_of G OUT es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 (nm OUT) in
    RI3P OK E K V L A -> K <= K' ->
    length hs = length es -> (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
    Forall (fun p => re_eof (fst p) = 0 ->
              0 <= re_cap (fst p) /\ 0 <= ent_ka (fst p) /\
              J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p))) /\
              0 <= hs_off (fst (snd p)) /\
              re_nheld (fst p) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 26 /\
              (hl_cap (hs_expected (fst (snd p))) = 0 \/
               exists k, 0 <= k /\ hl_cap (hs_expected (fst (snd p))) = 8 * 2 ^ k) /\
              hl_n (hs_expected (fst (snd p))) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 25 /\
              Z.of_nat (length (re_U (fst p))) <= re_used (fst p)) (combine es hs) ->
    gone_cap lv mx NO CAP pre es hs <= NMAX ->
    Forall (fun p => re_eof (fst p) = 0 -> re_hp (fst p) <> 0 -> re_kh (fst p) <> 0) (combine es hs) ->
    List.NoDup (map fst (blocks L A)) ->
    (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
    tr_peak tr (CF_MAX - PB3_MAX) ->
    exists bnd, rt_ok (pack3P OK RM) A bnd /\
      (forall qs, length qs = nretF tr -> roomF (pack3P OK RM) qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> rt_ok (pack3P OK RM) A' (runF (pack3P OK RM) qs bnd tr) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c + gone_dl lv mx NO CAP pre es hs nm 0 (nm OUT) c <= nc_cnt V' L' A' c) ->
        ncs V L A + gone_db lv mx NO CAP pre es hs nm 0 (nm OUT) <= ncs V' L' A' ->
        ncs V' L' A' <= rv_wt V' ->
        rv_wt V' <= rv_wt V + gone_wd (combine es hs) (gone_states lv mx NO CAP pre es hs) +
                    DATA_PER * (cdat (ss_pl E) K' - cdat (ss_pl E) K) ->
        rv_pend V' = gone_pend es hs ->
        (forall c, 0 <= c < 49 -> ek_c V' c = ek_c V c + bcnt c (gone_ek (combine es hs))) ->
        ek_b V' = ek_b V + zsum (fun n => n) (gone_ek (combine es hs)) ->
        Forall (fun n => 0 <= n) (rv_ek V') ->
        List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) ->
           ~ In (ptr_addr L p) (gone_tch OUT CAP es hs) -> In (ptr_addr L' p) (rv_nc V')) ->
        (gone_cap lv mx NO CAP pre es hs <> 0 ->
           In (ptr_addr L' (resolveF qs (gone_out lv mx NO CAP pre es hs nm 0 (nm OUT)))) (rv_nc V')) ->
        (forall i, (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
           let s := nth i (gone_states lv mx NO CAP pre es hs)
                      (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))) in
           let a := nth i (gone_adrs lv mx NO CAP pre es hs nm 0 (nm OUT)) dadr0 in
           (ds_cap s <> 0 -> In (ptr_addr L' (resolveF qs (da_buf a))) (rv_nc V')) /\
           (ds_ka s <> 0 -> In (ptr_addr L' (resolveF qs (da_hp a))) (rv_nc V')) /\
           (ds_ecap s <> 0 -> In (ptr_addr L' (resolveF qs (da_ev a))) (rv_nc V'))) ->
        RI3P OK E K' V' L' A'.

Definition l2_res_nl3P (OK : astate -> Prop) (RM : pbound3 -> Z -> Prop) : Prop :=
  forall (E : sstart) (K K' : Z) (L : layout) (A : astate) (G OUT : Z) (es : list rentry) (hj : list (hsrc * nat))
         (h : hsrc) (j : nat),
    let nm := known_at L A in
    let V := view_of G OUT es hj in
    let s := sh_of nm (hs_held h) in
    let rs := map (shr nm) (hl_recs (hs_expected h)) in
    let tr := check_no_loss_tr 0 s rs in
    let s' := check_no_loss_sh 0 s rs in
    RI3P OK E K V L A -> K <= K' -> In (h, j) hj ->
    hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
    List.NoDup (map fst (blocks L A)) ->
    exists bnd, rt_ok (pack3P OK RM) A bnd /\
      (forall qs, length qs = nretF tr -> roomF (pack3P OK RM) qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> rt_ok (pack3P OK RM) A' (runF (pack3P OK RM) qs bnd tr) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c + arr_dl (sh_cap s) (sh_cap s') c <= nc_cnt V' L' A' c) ->
        ncs V L A + (16 * sh_cap s' - 16 * sh_cap s) <= ncs V' L' A' ->
        ncs V' L' A' <= rv_wt V' ->
        rv_wt V' <= rv_wt V - nw_list (hs_expected h) - nw_list (hs_held h) + Z.max (16 * hl_cap (hs_expected h)) 128 +
                    Z.max (16 * sh_cap s') (NC_PER * sh_n s' + 128) + DATA_PER * (cdat (ss_pl E) K' - cdat (ss_pl E) K) ->
        rv_pend V' = rv_pend V ->
        (forall c, 0 <= c < 49 -> ek_c V' c + bcnt c (ekeys_hl (hs_expected h)) = ek_c V c) ->
        ek_b V' + zsum (fun n => n) (ekeys_hl (hs_expected h)) = ek_b V ->
        Forall (fun n => 0 <= n) (rv_ek V') ->
        List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) ->
           ptr_addr L p <> hl_v (hs_held h) \/ hl_cap (hs_held h) = 0 -> In (ptr_addr L' p) (rv_nc V')) ->
        (sh_cap s' <> 0 -> In (ptr_addr L' (resolveF qs (sh_v s'))) (rv_nc V')) ->
        RI3P OK E K' V' L' A'.

Definition l2_res_se3P (OK : astate -> Prop) (RM : pbound3 -> Z -> Prop) : Prop :=
  forall (E : sstart) (K K' : Z) (V : rview) (L : layout) (A : astate) (h : hsrc) (gone : Z) (P d : list byte),
    let tr := check_shape_ends_tr (known_at L A) gone P (hl_recs (hs_held h)) d in
    RI3P OK E K V L A -> K <= K' ->
    exists bnd, rt_ok (pack3P OK RM) A bnd /\
      (forall qs, length qs = nretF tr -> roomF (pack3P OK RM) qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> rt_ok (pack3P OK RM) A' (runF (pack3P OK RM) qs bnd tr) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c <= nc_cnt V' L' A' c) ->
        ncs V L A <= ncs V' L' A' -> ncs V' L' A' <= rv_wt V' ->
        rv_wt V' <= rv_wt V + DATA_PER * (cdat (ss_pl E) K' - cdat (ss_pl E) K) ->
        rv_pend V' = rv_pend V -> rv_ek V' = rv_ek V ->
        List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) -> In (ptr_addr L' p) (rv_nc V')) ->
        RI3P OK E K' V' L' A'.

Theorem p5c_res3_fullP_holds OK RM : RMH RM -> p5c_res3_fullP OK RM.
Proof.
  intros HRM E K K' L A G OUT es hs lv mx NO CAP pre. cbv zeta.
  intros ((b & al & alb & HR & HL) & HOK) Hk Hlen Hes Hmx Hc HF HN Hkh HB HO0 HPk.
  assert (HD : Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) (combine es hs)).
  { eapply Forall_impl; [|exact HF]. intros p Hp E0. destruct (Hp E0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
    exact (drain3_holds _ _ H1 H2 H3 H4 H5 H6 H7). }
  assert (HW : Forall (fun p => re_eof (fst p) = 0 -> drain_wt3 (fst p) (fst (snd p))) (combine es hs)).
  { eapply Forall_impl; [|exact HF]. intros p Hp E0. destruct (Hp E0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exact (drain_wt3_holds _ _ H1 H2 H3 H4 H5 H6 H7 H8). }
  assert (HNT : gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT) <= NMAX)
    by (rewrite gone_capT_eq; exact HN).
  pose proof (gone_misT_call (ss_pl E) K L A b al alb G OUT es hs CAP HL HR Hlen Hes Hkh HB HO0) as HS.
  exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs Hq. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
    + exact (gone_room3 rv_wt (ss_pl E) K L A b al alb G OUT es hs lv mx NO CAP pre _ HL HD Hes Hmx Hc HNT HS qs Hq).
    + pose proof HL as (HCs & HMc & _). pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HBy.
      apply (RMrun_of_peak RM (ss_pl E) b _ (CF_MAX - PB3_MAX) HRM HCs HMc); [lia|exact HPk].
  - intros L' A' qs Hq (HR' & HOK') V' HN' HC' HB' HW1' HW' HP' HEc HEb HEF HB2 HO HF12 HF13.
    split; [|exact HOK']. rewrite runF_pack3P in HR'.
    pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HW2 & _ & HMis & _).
    assert (Hstep : call_step3 rv_wt (ss_pl E) K' (view_of G OUT es hs) L A V' L' A' al alb
              (gone_dl lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))
              (gone_db lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT)) (gone_da es hs) (gone_dab es hs)).
    { pose proof (cdat_mono (ss_pl E) K K' Hk). pose proof (consb_mono (ss_pl E) K K' Hk).
      pose proof (gone_wd_le (combine es hs) lv mx NO CAP pre (fun _ => adr0) 0 adr0 Hmx Hc HD HW) as WD.
      unfold gone_states in HW'.
      assert (DA : zsumZ (gone_da es hs) (zseq 0 49) =
                   zsumZ (gone_cred (combine es hs)) (zseq 0 49) - zlen (gone_ek (combine es hs))).
      { unfold gone_da.
        rewrite (zsumZ_ext _ (fun c => gone_cred (combine es hs) c + (-1) * bcnt c (gone_ek (combine es hs))))
          by (intros; lia).
        rewrite zsumZ_add, zsumZ_mul_l, (bcnt_sum _ (gone_ek_nonneg _)). lia. }
      split; [exact HN'|]. split; [exact HC'|]. split; [exact HB'|]. split; [exact HW1'|].
      split; [rewrite DA; unfold NC_PER, DATA_PER in *; lia|].
      split; [|split; [|exact HEF]].
      - intros c Hc'. rewrite (HEc c Hc'), HP'. pose proof (prom_gone es hs c Hlen) as PG.
        pose proof (ledger3_credit _ _ _ _ _ _ _ _ _ c HL Hc') as LC. cbn [view_of rv_pend] in LC.
        pose proof (cons_mono (ss_pl E) K K' c Hk). unfold gone_da. lia.
      - rewrite HEb, HP'. pose proof (promb_gone es hs Hlen). pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as LB.
        cbn [view_of rv_pend] in LB. unfold gone_dab. lia. }
    assert (H0 : misK (p3_mis b) (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] (known_at L A)) (combine es hs)))
                   (slot3 CAP (resolveF qs (known_at L A OUT)) ++ concat (map (gslots qs (known_at L A)) (combine es hs)) ++ [])
                   (p3_mis b))
      by (eapply misK_S; [|apply misK_init]; intros x Hx; rewrite app_nil_r; exact Hx).
    pose proof (gone_misK (p3_mis b) _ qs (combine es hs) lv mx NO CAP pre (known_at L A) 0 (known_at L A OUT) b [] Hc H0)
      as GM.
    cbv zeta in GM.
    assert (Hmis : mis_nc V' L' (p3_mis (runF pack3_form qs b
                     (relay_instance_gone_tr lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))))).
    { apply (mis_nc_post L A b L' A' _ (view_of G OUT es hs) V'
               (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] (known_at L A)) (combine es hs)))
               (slot3 (gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))
                      (resolveF qs (gone_out lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))) ++
                gfin qs (combine es hs) (gone_ssT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))
                  (gone_adrs lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT)))
               HR HMis HR' HB2).
      - rewrite runF3. unfold relay_instance_gone_tr, gone_capT, gone_out, gone_ssT, gone_adrs.
        eapply misK_S; [|exact GM]. intros x Hx. rewrite app_nil_r in Hx. exact Hx.
      - intros p Hp. apply in_app_or in Hp as [Hp|Hp].
        + apply slot3_in in Hp as (Hp0 & <-). rewrite gone_capT_eq in Hp0. exact (HF12 Hp0).
        + destruct (gfin_in qs _ _ _ p Hp) as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5).
          rewrite (combine_len es hs Hlen) in Hi1.
          rewrite (combine_nth es hs i no_entry no_hj (eq_sym Hlen)) in Hi4. cbn [fst] in Hi4.
          destruct (HF13 i Hi1 Hi4) as (F1 & F2 & F3).
          rewrite gone_ssT_eq in Hi2, Hi5.
          rewrite (nth_dflt _ i ds0 (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))) Hi2) in Hi5.
          unfold dsl in Hi5. rewrite !in_app_iff in Hi5.
          destruct Hi5 as [Hp1|[Hp1|Hp1]]; apply slot3_in in Hp1 as (Hp0 & <-);
            first [exact (F1 Hp0) | exact (F2 Hp0) | exact (F3 Hp0)].
      - intros p n Hb Hv Hn. apply (HO p n Hb Hv). exact (gone_tch_cover L A OUT CAP es hs p n HB Hb Hn). }
    exact (gone_ri3 E K K' L A L' A' V' b al alb G OUT es hs lv mx NO CAP pre _ qs HL HD Hes Hmx Hc HNT HS HR' Hstep Hmis).
Qed.

Theorem l2_res_nl3P_holds OK RM : RMH RM -> l2_res_nl3P OK RM.
Proof.
  intros HRM E K K' L A G OUT es hj h j. cbv zeta. intros ((b & al & alb & HR & HL) & HOK) Hk Hin HN HB.
  exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs Hq. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
    + apply (check_no_loss_room3 rv_wt (ss_pl E) K (view_of G OUT es hj) L A b al alb (hs_held h) (hs_expected h) HL HN).
      * intros c Hc. exact (ek_view_in G OUT es hj (h, j) c Hin).
      * exact (ek_view_in_b G OUT es hj (h, j) Hin).
      * exact Hq.
    + pose proof HL as (HCs & HMc & _ & _ & _ & Ha & _).
      pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HBy.
      pose proof (cnl_keys_zsum_hl (known_at L A) 0 (sh_of (known_at L A) (hs_held h)) (hs_expected h)) as KZ.
      pose proof (ek_view_in_b G OUT es hj (h, j) Hin) as KE. cbn [fst] in KE.
      pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as LB.
      pose proof (consb_le (ss_pl E) K) as CB.
      pose proof (promb_nonneg (rv_pend (view_of G OUT es hj))) as PB.
      assert (X : PB3_MAX + CONSB_MAX + 201326592 <= CF_MAX) by (apply Z.leb_le; vm_compute; reflexivity).
      apply (RMrun_of_peak RM (ss_pl E) b _ (zsum (fun n => n) (cnl_keys 0 (sh_of (known_at L A) (hs_held h))
        (map (shr (known_at L A)) (hl_recs (hs_expected h)))) + 201326592) HRM HCs HMc); [lia|].
      apply cpk_cnl. pose proof (arr_pot_b (sh_cap (sh_of (known_at L A) (hs_held h)))) as AP.
      pose proof (cnl_keys_len 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h))))
        as KL.
      rewrite map_snd_shr in KL. rewrite P22_v in HN. rewrite sh_n_of.
      assert (Hn0 : 0 <= hl_n (hs_held h)) by (unfold hl_n; lia).
      pose proof CONSB_MAX_v as CV. pose proof NMAX_v as NV.
      unfold cpk. split; [apply cnl_keys_nonneg|]. lia.
  - intros L' A' qs Hq (HR' & HOK') V' HN' HC' HB' HW1' HW' HP' HEc HEb HEF HB2 HO HF.
    split; [|exact HOK']. rewrite runF_pack3P in HR'.
    pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HW2 & _ & HMis & _).
    destruct (check_no_loss_credit3 rv_wt (ss_pl E) K (view_of G OUT es hj) L A b al alb (hs_held h) (hs_expected h)
                K' V' HL Hk HP' HEc HEb) as (Cc & Cb).
    pose proof (cdat_mono (ss_pl E) K K' Hk).
    assert (Hn0 : 0 <= hl_n (hs_held h)) by (unfold hl_n; lia).
    assert (HnE : 0 <= hl_n (hs_expected h)) by (unfold hl_n; lia).
    destruct (cnl_wt_le (map (shr (known_at L A)) (hl_recs (hs_expected h))) 0 (sh_of (known_at L A) (hs_held h))
                (hl_n (hs_held h)) (hl_cap (hs_held h)) 0 Hn0 (Z.le_refl 0) ltac:(rewrite sh_n_of; lia)
                (Z.le_max_l _ _)) as (W1 & W2).
    assert (WN : rv_wt V' <= NC_FIX + NC_PER * (alsum al + zlen (cnl_keys 0 (sh_of (known_at L A) (hs_held h))
                   (map (shr (known_at L A)) (hl_recs (hs_expected h))))) + DATA_PER * cdat (ss_pl E) K').
    { assert (0 <= zlen (cnl_keys 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h)))))
        by (unfold zlen; lia).
      revert HW' HW2 W1 W2. unfold nw_list. unfold NC_PER, DATA_PER in *. lia. }
    assert (HS : call_step rv_wt (ss_pl E) K' (view_of G OUT es hj) L A V' L' A' al alb
      (cnl_keys 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h))))
      (arr_dl (sh_cap (sh_of (known_at L A) (hs_held h)))
         (sh_cap (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h))))))
      (16 * sh_cap (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h))))
       - 16 * sh_cap (sh_of (known_at L A) (hs_held h)))).
    { split; [exact HN'|]. split; [exact HC'|]. split; [exact HB'|]. split; [exact HW1'|].
      split; [exact WN|]. split; [exact Cc|]. split; [exact Cb|exact HEF]. }
    assert (HM : mis_nc V' L' (p3_mis (runF pack3_form qs b (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h))
                                         (map (shr (known_at L A)) (hl_recs (hs_expected h))))))).
    { apply (mis_nc_post L A b L' A' _ (view_of G OUT es hj) V'
               (slot3 (hl_cap (hs_held h)) (sptr_of L A (hl_v (hs_held h))))
               (slot3 (sh_cap (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
                                 (map (shr (known_at L A)) (hl_recs (hs_expected h)))))
                      (resolveF qs (sh_v (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
                                 (map (shr (known_at L A)) (hl_recs (hs_expected h)))))))
               HR HMis HR' HB2).
      - rewrite runF3. eapply misK_S; [|apply (cnl_misK (p3_mis b) _ qs [])].
        + intros x Hx. rewrite app_nil_r in Hx. exact Hx.
        + eapply misK_S; [|apply misK_init]. intros x Hx. rewrite app_nil_r. exact Hx.
      - intros p Hp. unfold slot3 in Hp. destruct (Z.eqb_spec (sh_cap (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
                                 (map (shr (known_at L A)) (hl_recs (hs_expected h))))) 0) as [Z0|Z0];
          [destruct Hp|]. destruct Hp as [<-|[]]. exact (HF Z0).
      - intros p n Hb Hv Hn. apply (HO p n Hb Hv). destruct (Z.eqb_spec (hl_cap (hs_held h)) 0) as [Z0|Z0]; [right; exact Z0|].
        left. intros Ex. apply Hn. rewrite (slot3_nz _ _ Z0). left. exact (sptr_at L A p n _ HB Hb Ex). }
    destruct (check_no_loss_ledger3 rv_wt (ss_pl E) K (view_of G OUT es hj) L A b al alb (hs_held h) (hs_expected h) qs
                K' V' L' A' HL HS HM) as (al' & alb' & HL').
    eexists _, al', alb'. split; [exact HR'|exact HL'].
Qed.

Theorem l2_res_se3P_holds OK RM : RMH RM -> l2_res_se3P OK RM.
Proof.
  intros HRM E K K' V L A h gone P d. cbv zeta. intros ((b & al & alb & HR & HL) & HOK) Hk.
  exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs Hq. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
    + apply check_shape_ends_room3. exact Hq.
    + pose proof HL as (HCs & HMc & _). pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HBy.
      assert (X : PB3_MAX <= CF_MAX) by (apply Z.leb_le; vm_compute; reflexivity).
      apply (RMrun_of_peak RM (ss_pl E) b _ 0 HRM HCs HMc); [lia|].
      apply tr_peak_frees. rewrite cse_tr. exact (recs_drop_free _).
  - intros L' A' qs Hq (HR' & HOK') V' HN' HC' HB' HW1' HW' HP' HEK HB2 HO.
    split; [|exact HOK']. rewrite runF_pack3P in HR'.
    pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMis & _).
    assert (HS := nc_step_keep (ss_pl E) K K' V L A b al alb V' L' A' HL Hk HN' HC' HB' HW1' HW' HP' HEK).
    assert (HM : mis_nc V' L' (p3_mis (runF pack3_form qs b (check_shape_ends_tr (known_at L A) gone P
                                         (hl_recs (hs_held h)) d)))).
    { apply (mis_nc_post L A b L' A' _ V V' [] [] HR HMis HR' HB2).
      - rewrite runF3. apply misK_nore; [rewrite cse_tr; apply free_nore, recs_drop_free|]. apply misK_init.
      - intros p [].
      - intros p n Hb Hv _. exact (HO p n Hb Hv). }
    destruct (check_shape_ends_ledger3 rv_wt (ss_pl E) K V L A b al alb (known_at L A) gone P (hl_recs (hs_held h)) d
                qs K' V' L' A' HL HS HM) as (al' & alb' & HL').
    exists (runF pack3_form qs b (check_shape_ends_tr (known_at L A) gone P (hl_recs (hs_held h)) d)), al', alb'.
    split; [exact HR'|exact HL'].
Qed.

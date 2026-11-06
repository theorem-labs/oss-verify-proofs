From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF RelayModel RelayKeys RelayRep HarnessRep ListRep CheckRep ListTr
  HarnessTr send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c
  SlotRun3 SlotP5R3 SlotP5R3G.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition gone_pend (es : list rentry) (hs : list (hsrc * nat)) : list (list (list byte)) :=
  map (fun q => if re_eof (fst q) =? 0 then [] else map snd (hl_recs (hs_pending (fst (snd q))))) (combine es hs).

Definition gone_tch (OUT CAP : Z) (es : list rentry) (hs : list (hsrc * nat)) : list Z :=
  (if CAP =? 0 then [] else [OUT]) ++
  concat (map (fun q => if re_eof (fst q) =? 0 then
                          (if re_cap (fst q) =? 0 then [] else [re_buf (fst q)]) ++
                          (if ent_ka (fst q) =? 0 then [] else [re_hp (fst q)]) ++
                          (if hl_cap (hs_expected (fst (snd q))) =? 0 then [] else [hl_v (hs_expected (fst (snd q)))])
                        else []) (combine es hs)).

Definition drain_wt_src (fin : dstate) (h : hsrc) : Z :=
  Z.max (ds_cap fin) (DATA_PER * Z.of_nat (length (ds_u fin)) + 8192) +
  Z.max (ds_ka fin) (8 * Z.of_nat (length (ds_H fin)) + 8) +
  Z.max (16 * hl_cap (hs_pending h)) 128 + op_add_c.PARTIAL_BYTES +
  Z.max (16 * ds_ecap fin)
    (NC_PER * (hl_n (hs_expected h) + Z.of_nat (length (lines (hs_state h) (bzs (pending_stream h))))) + 128) +
  nw_list (hs_held h).

Definition drain_wt3 (e : rentry) (h : hsrc) : Prop :=
  forall (lv : bool) (mx NO CAP : Z), 0 <= mx -> 0 <= CAP ->
    drain_wt_src (drain_fin lv mx NO CAP e h) h - nw_ent e - nw_src h <=
      NC_PER * (zsumZ (cred h) (zseq 0 49) - zlen (ekeys (lines (hs_state h) (bzs (pending_stream h))))).

Fixpoint gone_wd (ps : list (rentry * (hsrc * nat))) (ss : list dstate) : Z :=
  match ps, ss with
  | p :: ps', s :: ss' =>
      (if re_eof (fst p) =? 0 then drain_wt_src s (fst (snd p)) - nw_ent (fst p) - nw_src (fst (snd p)) else 0) +
      gone_wd ps' ss'
  | _, _ => 0
  end.

Definition p5c_res3 : Prop :=
  forall (E : sstart) (K K' : Z) (L : layout) (A : astate) (G OUT : Z) (es : list rentry) (hs : list (hsrc * nat))
         (lv : bool) (mx NO CAP : Z) (pre : list Z),
    let nm := known_at L A in
    let V := view_of G OUT es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 (nm OUT) in
    RI3_reply E K V L A -> K <= K' ->
    length hs = length es -> (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
    Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) (combine es hs) ->
    Forall (fun p => re_eof (fst p) = 0 -> drain_wt3 (fst p) (fst (snd p))) (combine es hs) ->
    gone_cap lv mx NO CAP pre es hs <= NMAX ->
    Forall (fun p => re_eof (fst p) = 0 -> re_hp (fst p) <> 0 -> re_kh (fst p) <> 0) (combine es hs) ->
    List.NoDup (map fst (blocks L A)) ->
    (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
    exists bnd, res_ok_pack3 A bnd /\
      (forall qs, length qs = nretF tr -> roomF pack3_form qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> res_ok_pack3 A' (runF pack3_form qs bnd tr) ->
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
        RI3_reply E K' V' L' A'.

Definition l2_res_nl3 : Prop :=
  forall (E : sstart) (K K' : Z) (L : layout) (A : astate) (G OUT : Z) (es : list rentry) (hj : list (hsrc * nat))
         (h : hsrc) (j : nat),
    let nm := known_at L A in
    let V := view_of G OUT es hj in
    let s := sh_of nm (hs_held h) in
    let rs := map (shr nm) (hl_recs (hs_expected h)) in
    let tr := check_no_loss_tr 0 s rs in
    let s' := check_no_loss_sh 0 s rs in
    RI3_reply E K V L A -> K <= K' -> In (h, j) hj ->
    hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
    List.NoDup (map fst (blocks L A)) ->
    exists bnd, res_ok_pack3 A bnd /\
      (forall qs, length qs = nretF tr -> roomF pack3_form qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> res_ok_pack3 A' (runF pack3_form qs bnd tr) ->
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
        RI3_reply E K' V' L' A'.

Definition l2_res_se3 : Prop :=
  forall (E : sstart) (K K' : Z) (V : rview) (L : layout) (A : astate) (h : hsrc) (gone : Z) (P d : list byte),
    let tr := check_shape_ends_tr (known_at L A) gone P (hl_recs (hs_held h)) d in
    RI3_reply E K V L A -> K <= K' ->
    exists bnd, res_ok_pack3 A bnd /\
      (forall qs, length qs = nretF tr -> roomF pack3_form qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> res_ok_pack3 A' (runF pack3_form qs bnd tr) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c <= nc_cnt V' L' A' c) ->
        ncs V L A <= ncs V' L' A' -> ncs V' L' A' <= rv_wt V' ->
        rv_wt V' <= rv_wt V + DATA_PER * (cdat (ss_pl E) K' - cdat (ss_pl E) K) ->
        rv_pend V' = rv_pend V -> rv_ek V' = rv_ek V ->
        List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) -> In (ptr_addr L' p) (rv_nc V')) ->
        RI3_reply E K' V' L' A'.

Definition misK (M0 : list (sptr * Z)) (S0 S : list sptr) (M : list (sptr * Z)) : Prop :=
  forall e, In e M -> In (fst e) S \/ (In e M0 /\ ~ In (fst e) S0).

Lemma misK_init M0 S0 : misK M0 S0 S0 M0.
Proof.
  intros e He. destruct (In_dec sptr_eq_dec (fst e) S0) as [H|H]; [left; exact H|right; split; assumption].
Qed.

Lemma misK_S M0 S0 S S' M : (forall x, In x S -> In x S') -> misK M0 S0 S M -> misK M0 S0 S' M.
Proof. intros HS HK e He. destruct (HK e He) as [H|H]; [left; exact (HS _ H)|right; exact H]. Qed.

Lemma misK_del M0 S0 S M p : misK M0 S0 S M -> misK M0 S0 S (mis_del M p).
Proof. intros HK e He. unfold mis_del in He. apply filter_In in He as [He _]. exact (HK e He). Qed.

Lemma misK_re M0 S0 S M k n p q : misK M0 S0 (p :: S) M -> misK M0 S0 (q :: S) (mis_realloc M k n p q).
Proof.
  intros HK e He. unfold mis_realloc in He.
  match type of He with In _ (if ?b then _ else _) => destruct b eqn:C end.
  - destruct He as [<-|He].
    + left. left. cbn [fst]. apply andb_prop in C as [C _]. apply andb_prop in C as [C _].
      apply sptr_eqb_eq in C. exact C.
    + unfold mis_del in He. apply filter_In in He as [He Hn]. destruct (HK e He) as [[E|H]|H].
      * exfalso. rewrite E, sptr_eqb_refl in Hn. discriminate.
      * left. right. exact H.
      * right. exact H.
  - unfold mis_del in He. apply filter_In in He as [He Hn]. destruct (HK e He) as [[E|H]|H].
    + exfalso. rewrite E, sptr_eqb_refl in Hn. discriminate.
    + left. right. exact H.
    + right. exact H.
Qed.

Definition no_re (e : tev) : Prop := match e with RRealloc _ _ _ => False | _ => True end.

Lemma misK_nore M0 S0 S qs tr : forall b j, Forall no_re tr -> misK M0 S0 S (p3_mis b) ->
  misK M0 S0 S (p3_mis (run3 qs b j tr)).
Proof.
  induction tr as [|ev tr IH]; intros b j Hn HK; [exact HK|]. apply Forall_cons_iff in Hn as [He Hn].
  destruct ev as [n|n a|k n a]; cbn [no_re] in He; [| |contradiction]; cbn [run_from].
  - apply IH; [exact Hn|exact HK].
  - apply IH; [exact Hn|]. apply misK_del. exact HK.
Qed.

Lemma free_nore tr : Forall ev_free tr -> Forall no_re tr.
Proof.
  intros H. induction H as [|ev tr He _ IH]; constructor; [|exact IH]. destruct ev; cbn in *; tauto.
Qed.

Lemma mis_nc_post L A b L' A' b' V V' (S0 S : list sptr) :
  res_ok_pack3 A b -> mis_nc V L (p3_mis b) -> res_ok_pack3 A' b' -> List.NoDup (map fst (blocks L' A')) ->
  misK (p3_mis b) S0 S (p3_mis b') ->
  (forall p, In p S -> In (ptr_addr L' p) (rv_nc V')) ->
  (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) -> ~ In p S0 -> In (ptr_addr L' p) (rv_nc V')) ->
  mis_nc V' L' (p3_mis b').
Proof.
  intros HA (HI & _) HA' HB' HK HS HP.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  pose proof HA' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HM' & _).
  split; [|exact (mis_nodup L' A' _ _ HB' HM')].
  intros x Hx. unfold mis_addrs in Hx. apply in_map_iff in Hx as (e & <- & He).
  destruct (HK e He) as [Hs|(Hm & Hn)]; [exact (HS _ Hs)|].
  destruct (HU e Hm) as (_ & n & Hb). apply (HP (fst e) n Hb); [|exact Hn].
  apply HI. unfold mis_addrs. exact (in_map (fun e0 => ptr_addr L (fst e0)) _ e Hm).
Qed.

Lemma nc_step_keep pl K K' V L A b al alb V' L' A' :
  RI3_ledger rv_wt pl K V L A b al alb -> K <= K' ->
  (length (rv_nc V') <= NC_MAX)%nat ->
  (forall c, 0 <= c < 49 -> nc_cnt V L A c <= nc_cnt V' L' A' c) ->
  ncs V L A <= ncs V' L' A' -> ncs V' L' A' <= rv_wt V' ->
  rv_wt V' <= rv_wt V + DATA_PER * (cdat pl K' - cdat pl K) ->
  rv_pend V' = rv_pend V -> rv_ek V' = rv_ek V ->
  nc_step rv_wt pl K' V L A V' L' A' al alb (fun _ => 0) 0.
Proof.
  intros (HC & HM & HN & HlL & HL & Ha & HE & HB & HW1 & HW2 & HP & HMis & H) Hk HN' HC' HB' HW1' HW' HP' HEK.
  pose proof (consb_mono pl K K' Hk).
  assert (EB : ek_b V' = ek_b V) by (unfold ek_b; rewrite HEK; reflexivity).
  assert (EC : forall c, ek_c V' c = ek_c V c) by (intros c; unfold ek_c; rewrite HEK; reflexivity).
  split; [exact HN'|]. split; [intros c Hc; pose proof (HC' c Hc); lia|]. split; [lia|]. split; [exact HW1'|].
  split; [unfold NC_PER, DATA_PER in *; lia|].
  split; [|split; [rewrite EB, HP'; lia|rewrite HEK; exact HE]].
  intros c Hc. rewrite EC, HP'. destruct (H c Hc) as (_ & _ & H3). pose proof (cons_mono pl K K' c Hk). lia.
Qed.

Theorem l2_res_se3_holds : l2_res_se3.
Proof.
  intros E K K' V L A h gone P d. cbv zeta. intros (b & al & alb & HR & HL) Hk.
  exists b. split; [exact HR|]. split.
  - intros qs Hq. apply check_shape_ends_room3. exact Hq.
  - intros L' A' qs Hq HR' V' HN' HC' HB' HW1' HW' HP' HEK HB2 HO.
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

Lemma sptr_at L A p n x : List.NoDup (map fst (blocks L A)) -> In (p, n) (user_blocks A) -> ptr_addr L p = x ->
  sptr_of L A x = p.
Proof.
  intros HB Hp Ex.
  assert (Hb : In (x, n) (blocks L A)).
  { rewrite <- Ex. unfold blocks. exact (in_map (fun b0 => (ptr_addr L (fst b0), snd b0)) _ (p, n) Hp). }
  destruct (sptr_of_spec L A x n (proj2 (stdpp.base.NoDup_ListNoDup _) HB) Hb) as (Hs & Es).
  assert (Eq : (sptr_of L A x, n) = (p, n)).
  { apply (nodup_map_eq (fun b0 => ptr_addr L (fst b0)) (user_blocks A)); [|exact Hs|exact Hp|].
    - unfold blocks in HB. rewrite map_map in HB. exact HB.
    - cbn [fst]. rewrite Es. symmetry. exact Ex. }
  injection Eq as E. exact E.
Qed.

Lemma slot3_0 x : slot3 0 x = [].
Proof. reflexivity. Qed.

Lemma misK_slot0 M0 S0 T M c x y : misK M0 S0 (slot3 0 x ++ T) M -> misK M0 S0 (slot3 c y ++ T) M.
Proof. apply misK_S. intros z Hz. apply in_app_iff. right. exact Hz. Qed.

Lemma misK_slot_re M0 S0 T M c c' x q k n : c <> 0 -> c' <> 0 -> misK M0 S0 (slot3 c x ++ T) M ->
  misK M0 S0 (slot3 c' q ++ T) (mis_realloc M k n x q).
Proof. intros H1 H2 HK. rewrite (slot3_nz c x H1) in HK. rewrite (slot3_nz c' q H2). exact (misK_re _ _ _ _ _ _ _ _ HK). Qed.

Lemma gm_misK M0 S0 qs T j s ln b : misK M0 S0 (slot3 (sh_cap s) (resolveF qs (sh_v s)) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (sh_cap (gesture_model_sh j s ln)) (resolveF qs (sh_v (gesture_model_sh j s ln))) ++ T)
    (p3_mis (run3 qs b j (gesture_model_tr s ln))).
Proof.
  intros HK. unfold gesture_model_tr, gesture_model_sh. destruct (gesture ln) as [[[|] x]|]; [| |exact HK].
  - destruct (existsb (list_eqb x) (sh_keys s)); [exact HK|].
    unfold list_push_tr, list_grow_tr, list_push_sh. destruct (sh_n s =? sh_cap s) eqn:En.
    + destruct (Z.eqb_spec (sh_cap s) 0) as [Ec|Ec].
      * cbn [app run_from]. unfold pb3_malloc. cbn [p3_mis sh_cap sh_v]. rewrite Ec in HK. exact (misK_slot0 _ _ _ _ _ _ _ HK).
      * cbn [app run_from]. unfold pb3_malloc. cbn [p3_mis sh_cap sh_v].
        apply Z.eqb_eq in En. assert (Eg : grow_cap (sh_n s) (sh_cap s) = 2 * sh_cap s) by (apply grow_cap_2; assumption).
        rewrite Eg. apply (misK_slot_re _ _ _ _ (sh_cap s) (2 * sh_cap s) _ _ _ _ Ec ltac:(lia) HK).
    + cbn [app run_from]. unfold pb3_malloc. cbn [p3_mis sh_cap sh_v]. exact HK.
  - destruct (find_key x (sh_keys s)) as [i|]; [|exact HK].
    unfold list_drop_tr, rec_drop_tr, list_drop_sh. cbn [run_from]. unfold pb3_free. cbn [p3_mis sh_cap sh_v].
    apply misK_del. exact HK.
Qed.

Lemma cnl_misK M0 S0 qs T rs : forall j s b, misK M0 S0 (slot3 (sh_cap s) (resolveF qs (sh_v s)) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (sh_cap (check_no_loss_sh j s rs)) (resolveF qs (sh_v (check_no_loss_sh j s rs))) ++ T)
    (p3_mis (run3 qs b j (check_no_loss_tr j s rs))).
Proof.
  induction rs as [|r rs IH]; intros j s b HK; [exact HK|]. cbn [check_no_loss_tr check_no_loss_sh].
  rewrite run3_app, run3_app.
  replace (j + nretF (gesture_model_tr s (snd r)) + nretF (rec_drop_tr r))%nat
    with (j + nret sptr (gesture_model_tr s (snd r)))%nat by (cbn [rec_drop_tr nret fold_right rets]; lia).
  apply IH. unfold rec_drop_tr. cbn [run_from]. unfold pb3_free. cbn [p3_mis]. apply misK_del.
  apply gm_misK. exact HK.
Qed.

Ltac zmax_all := repeat match goal with
  | H : context [Z.max ?a ?b] |- _ =>
      let E := fresh "E" in let C := fresh "C" in
      destruct (Z.max_spec a b) as [[C E]|[C E]]; rewrite E in H; clear E
  | |- context [Z.max ?a ?b] =>
      let E := fresh "E" in let C := fresh "C" in
      destruct (Z.max_spec a b) as [[C E]|[C E]]; rewrite E; clear E
  end.

Lemma gm_wt j t ln n0 c0 p : 0 <= n0 -> 0 <= p -> sh_n t <= n0 + p ->
  16 * sh_cap t <= Z.max (16 * c0) (NC_PER * (n0 + p) + 128) ->
  sh_n (gesture_model_sh j t ln) <= n0 + (p + zlen (gm_keys t ln)) /\
  16 * sh_cap (gesture_model_sh j t ln) <= Z.max (16 * c0) (NC_PER * (n0 + (p + zlen (gm_keys t ln))) + 128).
Proof.
  intros Hn Hp H1 H2. pose proof (Z.le_max_r (16 * c0) (NC_PER * (n0 + (p + 1)) + 128)) as M1.
  pose proof (Z.le_max_l (16 * c0) (NC_PER * (n0 + (p + 1)) + 128)) as M2.
  pose proof (Z.le_max_r (16 * c0) (NC_PER * (n0 + p) + 128)) as M3.
  pose proof (Z.le_max_l (16 * c0) (NC_PER * (n0 + p) + 128)) as M4.
  unfold gesture_model_sh, gm_keys. destruct (gesture ln) as [[[|] x]|];
    [destruct (existsb (list_eqb x) (sh_keys t)) eqn:Ex| |]; unfold zlen; cbn [length Z.of_nat]; rewrite ?Z.add_0_r.
  - split; assumption.
  - rewrite sh_n_push, sh_cap_push. destruct (Z.eq_dec (sh_n t) (sh_cap t)) as [En|En].
    + destruct (Z.eq_dec (sh_cap t) 0) as [E0|E0].
      * rewrite (grow_cap_00 _ _ En E0). unfold NC_PER in *. lia.
      * rewrite (grow_cap_2 _ _ En E0). unfold NC_PER in *. lia.
    + rewrite (grow_cap_id _ _ En). unfold NC_PER in *. lia.
  - destruct (find_key x (sh_keys t)) as [i|]; [|split; assumption].
    pose proof (sh_n_drop t i). unfold list_drop_sh in *. cbn [sh_cap]. split; lia.
  - split; assumption.
Qed.

Lemma cnl_wt_le rs : forall j t n0 c0 p, 0 <= n0 -> 0 <= p -> sh_n t <= n0 + p ->
  16 * sh_cap t <= Z.max (16 * c0) (NC_PER * (n0 + p) + 128) ->
  sh_n (check_no_loss_sh j t rs) <= n0 + (p + zlen (cnl_keys j t rs)) /\
  16 * sh_cap (check_no_loss_sh j t rs) <= Z.max (16 * c0) (NC_PER * (n0 + (p + zlen (cnl_keys j t rs))) + 128).
Proof.
  induction rs as [|r rs IH]; intros j t n0 c0 p Hn Hp H1 H2; cbn [check_no_loss_sh cnl_keys].
  - unfold zlen. cbn [length Z.of_nat]. rewrite Z.add_0_r. split; assumption.
  - destruct (gm_wt j t (snd r) n0 c0 p Hn Hp H1 H2) as (G1 & G2).
    assert (Z1 : 0 <= zlen (gm_keys t (snd r))) by (unfold zlen; lia).
    destruct (IH (j + nret sptr (gesture_model_tr t (snd r)))%nat (gesture_model_sh j t (snd r)) n0 c0
                (p + zlen (gm_keys t (snd r))) Hn ltac:(lia) G1 G2) as (I1 & I2).
    assert (EZ : zlen (gm_keys t (snd r) ++ cnl_keys (j + nret sptr (gesture_model_tr t (snd r))) (gesture_model_sh j t (snd r)) rs)
                 = zlen (gm_keys t (snd r)) + zlen (cnl_keys (j + nret sptr (gesture_model_tr t (snd r))) (gesture_model_sh j t (snd r)) rs))
      by (unfold zlen; rewrite length_app; lia).
    rewrite EZ. rewrite (Z.add_assoc p). split; assumption.
Qed.

Theorem l2_res_nl3_holds : l2_res_nl3.
Proof.
  intros E K K' L A G OUT es hj h j. cbv zeta. intros (b & al & alb & HR & HL) Hk Hin HN HB.
  exists b. split; [exact HR|]. split.
  - intros qs Hq.
    apply (check_no_loss_room3 rv_wt (ss_pl E) K (view_of G OUT es hj) L A b al alb (hs_held h) (hs_expected h) HL HN).
    + intros c Hc. exact (ek_view_in G OUT es hj (h, j) c Hin).
    + exact (ek_view_in_b G OUT es hj (h, j) Hin).
    + exact Hq.
  - intros L' A' qs Hq HR' V' HN' HC' HB' HW1' HW' HP' HEc HEb HEF HB2 HO HF.
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

Lemma misK_swap M0 S0 X Y T M : misK M0 S0 (X ++ Y ++ T) M -> misK M0 S0 (Y ++ X ++ T) M.
Proof. apply misK_S. intros z Hz. rewrite !in_app_iff in *. tauto. Qed.

Lemma sl_misK M0 S0 qs T f : forall mx no cap rem j o b, 0 <= cap ->
  misK M0 S0 (slot3 cap (resolveF qs o) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (fst (snd (sl_run f mx no cap rem j o))) (resolveF qs (snd (snd (sl_run f mx no cap rem j o)))) ++ T)
    (p3_mis (run3 qs b j (fst (sl_run f mx no cap rem j o)))).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o b Hc HK; cbn [sl_run]; [exact HK|].
  destruct (rem <=? 0); [exact HK|]. cbv zeta.
  match goal with |- context [if cap <? ?x then _ else _] => destruct (Z.ltb_spec cap x) as [Hl|Hl] end.
  - cbn [fst snd]. destruct (Z.eqb_spec cap 0) as [E0|E0]; cbn [run_from].
    + apply IH; [lia|]. unfold pb3_malloc. cbn [p3_mis]. rewrite E0 in HK. exact (misK_slot0 _ _ _ _ _ _ _ HK).
    + apply IH; [lia|]. unfold pb3_realloc. cbn [p3_mis].
      eapply (misK_slot_re _ _ _ _ cap _ _ _ _ _ E0); [lia|exact HK].
  - apply IH; [exact Hc|exact HK].
Qed.

Lemma send_misK M0 S0 qs T live mx NO cap LEN j o b : 0 <= cap ->
  misK M0 S0 (slot3 cap (resolveF qs o) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (send_line_cap live mx NO cap LEN) (resolveF qs (send_line_out live mx NO cap LEN j o)) ++ T)
    (p3_mis (run3 qs b j (send_line_tr live mx NO cap LEN j o))).
Proof.
  intros Hc HK. unfold send_line_cap, send_line_out, send_line_tr. destruct live; [|exact HK].
  rewrite (sl_capi _ _ _ _ _ 0 adr0 j o). apply sl_misK; assumption.
Qed.

Lemma ge_misK M0 S0 qs T live mx NO cap XL j o b : 0 <= cap ->
  misK M0 S0 (slot3 cap (resolveF qs o) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (gesture_end_cap live mx NO cap XL) (resolveF qs (gesture_end_out live mx NO cap XL j o)) ++ T)
    (p3_mis (run3 qs b j (gesture_end_tr live mx NO cap XL j o))).
Proof.
  intros Hc HK. unfold gesture_end_cap, gesture_end_out, gesture_end_tr. rewrite run3_app.
  apply send_misK; [pose proof (send_mono live mx NO cap XL Hc); lia|]. apply send_misK; assumption.
Qed.

Lemma ke_misK M0 S0 qs T xks : forall live mx no cap j o b, 0 <= cap ->
  misK M0 S0 (slot3 cap (resolveF qs o) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (fst (snd (keys_end_run live mx no cap xks j o)))
                (resolveF qs (snd (snd (keys_end_run live mx no cap xks j o)))) ++ T)
    (p3_mis (run3 qs b j (fst (keys_end_run live mx no cap xks j o)))).
Proof.
  induction xks as [|[xl ka] r IH]; intros live mx no cap j o b Hc HK; cbn [keys_end_run fst snd]; [exact HK|].
  rewrite run3_app. cbn [run_from]. apply IH; [pose proof (ge_mono live mx no cap xl Hc); lia|].
  unfold pb3_free. cbn [p3_mis]. apply misK_del. apply ge_misK; assumption.
Qed.

Lemma grow_misK M0 S0 qs T cap used j bf b :
  misK M0 S0 (slot3 cap (resolveF qs bf) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (fst (snd (grow_tr cap used j bf))) (resolveF qs (snd (snd (grow_tr cap used j bf)))) ++ T)
    (p3_mis (run3 qs b j (fst (grow_tr cap used j bf)))).
Proof.
  intros HK. unfold grow_tr. destruct (cap - used <? 4096); [|exact HK]. cbn [fst snd].
  destruct (Z.eqb_spec cap 0) as [E0|E0]; cbn [run_from].
  - unfold pb3_malloc. cbn [p3_mis]. rewrite E0 in HK. exact (misK_slot0 _ _ _ _ _ _ _ HK).
  - unfold pb3_realloc. cbn [p3_mis]. eapply (misK_slot_re _ _ _ _ cap _ _ _ _ _ E0); [lia|exact HK].
Qed.

Lemma seen_misK M0 S0 qs T H ka l j ha ks b :
  misK M0 S0 (slot3 ka (resolveF qs ha) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (snd (fst (seen_tr H ka l j ha ks))) (resolveF qs (fst (snd (seen_tr H ka l j ha ks)))) ++ T)
    (p3_mis (run3 qs b j (fst (fst (seen_tr H ka l j ha ks))))).
Proof.
  intros HK. unfold seen_tr. destruct (gesture l) as [[[|] x]|]; [| |exact HK].
  - destruct (index_of x H) as [i|]; [exact HK|]. cbn [fst snd].
    destruct (Z.eqb_spec ka 0) as [E0|E0]; cbn [run_from].
    + unfold pb3_malloc. cbn [p3_mis]. rewrite E0 in HK. exact (misK_slot0 _ _ _ _ _ _ _ HK).
    + unfold pb3_malloc, pb3_realloc. cbn [p3_mis]. eapply (misK_slot_re _ _ _ _ ka _ _ _ _ _ E0); [lia|exact HK].
  - destruct (index_of x H) as [i|]; [|exact HK]. cbn [fst snd run_from]. unfold pb3_free. cbn [p3_mis].
    apply misK_del. exact HK.
Qed.

Lemma lines_misK M0 S0 qs T live mx ls : forall no cap H ka j o ha ks b, 0 <= cap ->
  misK M0 S0 (slot3 cap (resolveF qs o) ++ slot3 ka (resolveF qs ha) ++ T) (p3_mis b) ->
  let p := lines_run live mx no cap H ka ls j o ha ks in
  0 <= fst (fst (snd (fst p))) /\
  misK M0 S0 (slot3 (fst (fst (snd (fst p)))) (resolveF qs (fst (fst (snd p)))) ++
              slot3 (snd (snd (fst p))) (resolveF qs (snd (fst (snd p)))) ++ T)
    (p3_mis (run3 qs b j (fst (fst p)))).
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks b Hc HK; cbv zeta; cbn [lines_run fst snd];
    [split; assumption|].
  rewrite !run3_app.
  pose proof (send_mono live mx no cap (Z.of_nat (length l) + 1) Hc) as Mc.
  pose proof (send_misK M0 S0 qs (slot3 ka (resolveF qs ha) ++ T) live mx no cap (Z.of_nat (length l) + 1) j o b Hc HK)
    as K1.
  apply misK_swap in K1.
  pose proof (seen_misK M0 S0 qs _ H ka l (j + nretF (send_line_tr live mx no cap (Z.of_nat (length l) + 1) j o)) ha ks _ K1)
    as K2.
  apply misK_swap in K2.
  refine (IH _ _ _ _ _ _ _ _ _ _ K2). lia.
Qed.

Lemma pushes_misK M0 S0 qs T ls : forall n cap j v rs b,
  misK M0 S0 (slot3 cap (resolveF qs v) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (snd (fst (pushes_run n cap ls j v rs))) (resolveF qs (fst (snd (pushes_run n cap ls j v rs)))) ++ T)
    (p3_mis (run3 qs b j (fst (fst (pushes_run n cap ls j v rs))))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs b HK; cbn [pushes_run fst snd]; [exact HK|].
  rewrite run3_app. apply IH. unfold list_push_tra, push_cap.
  destruct (Z.eqb_spec n cap) as [En|En].
  - destruct (Z.eqb_spec cap 0) as [E0|E0]; cbn [app run_from].
    + unfold pb3_malloc. cbn [p3_mis]. rewrite E0 in HK. exact (misK_slot0 _ _ _ _ _ _ _ HK).
    + unfold pb3_malloc, pb3_realloc. cbn [p3_mis]. eapply (misK_slot_re _ _ _ _ cap _ _ _ _ _ E0); [lia|exact HK].
  - cbn [app run_from]. unfold pb3_malloc. cbn [p3_mis]. exact HK.
Qed.

Definition dsl (qs : list sptr) (s : dstate) (a : dadr) : list sptr :=
  slot3 (ds_cap s) (resolveF qs (da_buf a)) ++ slot3 (ds_ka s) (resolveF qs (da_hp a)) ++
  slot3 (ds_ecap s) (resolveF qs (da_ev a)).

Lemma drop_nore (w : bool) (x : adrF) (y : Z) : Forall no_re (if w then list_drop_tra x y else []).
Proof. destruct w; repeat constructor. Qed.

Ltac misK_perm H := eapply misK_S; [|exact H]; intros ? ?; rewrite ?in_app_iff in *; tauto.

Lemma drain_misK M0 S0 qs T f : forall live mx s j a b, 0 <= ds_ocap s ->
  misK M0 S0 (slot3 (ds_ocap s) (resolveF qs (da_out a)) ++ dsl qs s a ++ T) (p3_mis b) ->
  let r := drain_run f live mx s j a in
  0 <= ds_ocap (fst (snd r)) /\
  misK M0 S0 (slot3 (ds_ocap (fst (snd r))) (resolveF qs (da_out (snd (snd r)))) ++ dsl qs (fst (snd r)) (snd (snd r)) ++ T)
    (p3_mis (run3 qs b j (fst r))).
Proof.
  induction f as [|f IH]; intros live mx s j a b Hc HK; cbv zeta; cbn [drain_run]; [cbn [fst snd]; split; assumption|].
  unfold dsl in HK.
  pose proof (grow_misK M0 S0 qs (slot3 (ds_ocap s) (resolveF qs (da_out a)) ++ slot3 (ds_ka s) (resolveF qs (da_hp a)) ++
                slot3 (ds_ecap s) (resolveF qs (da_ev a)) ++ T) (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a) b)
    as G1.
  assert (G1h : misK M0 S0 (slot3 (ds_cap s) (resolveF qs (da_buf a)) ++ slot3 (ds_ocap s) (resolveF qs (da_out a)) ++
                slot3 (ds_ka s) (resolveF qs (da_hp a)) ++ slot3 (ds_ecap s) (resolveF qs (da_ev a)) ++ T) (p3_mis b))
    by misK_perm HK.
  specialize (G1 G1h). clear G1h.
  destruct (ds_eintr s).
  - cbn [fst snd]. rewrite run3_app.
    match goal with |- context [drain_run f live mx ?s1 ?j1 ?a1] =>
      assert (H1 : misK M0 S0 (slot3 (ds_ocap s1) (resolveF qs (da_out a1)) ++ dsl qs s1 a1 ++ T)
                     (p3_mis (run3 qs b j (fst (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))))
        by (unfold dsl; cbn [ds_ocap ds_cap ds_ka ds_ecap da_out da_buf da_hp da_ev]; misK_perm G1);
      pose proof (IH live mx s1 j1 a1 _ Hc H1) as X; cbv zeta in X; exact X
    end.
  - destruct (ds_pend s) as [|r0 rs].
    + cbn [fst snd]. split; [exact Hc|]. unfold dsl. cbn [ds_ocap ds_cap ds_ka ds_ecap da_out da_buf da_hp da_ev].
      misK_perm G1.
    + match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end.
      * cbn [fst snd]. split; [exact Hc|]. unfold dsl. cbn [ds_ocap ds_cap ds_ka ds_ecap da_out da_buf da_hp da_ev].
        misK_perm G1.
      * match goal with |- context [chunk ?u ?sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
        match goal with |- context [lines_run ?lv ?m ?no ?c ?H ?k rl ?jj ?o ?ha ?ks] =>
          destruct (snd (fst (lines_run lv m no c H k rl jj o ha ks))) as [[oc' H'] ka'] eqn:E1;
          destruct (snd (lines_run lv m no c H k rl jj o ha ks)) as [[o' ha'] ks'] eqn:E2
        end.
        cbn [fst snd]. rewrite !run3_app.
        match goal with |- context [pushes_run ?n0 ?c0 ?ls0 ?j0 ?v0 ?rs0] =>
          pose proof (pushes_misK M0 S0 qs (slot3 (ds_ocap s) (resolveF qs (da_out a)) ++
                        slot3 (fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))
                          (resolveF qs (snd (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))) ++
                        slot3 (ds_ka s) (resolveF qs (da_hp a)) ++ T) ls0 n0 c0 j0 v0 rs0
                        (run3 qs b j (fst (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))) as P1
        end.
        assert (P1h : misK M0 S0 (slot3 (ds_ecap s) (resolveF qs (da_ev a)) ++ slot3 (ds_ocap s) (resolveF qs (da_out a)) ++
                        slot3 (fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))
                          (resolveF qs (snd (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))) ++
                        slot3 (ds_ka s) (resolveF qs (da_hp a)) ++ T)
                   (p3_mis (run3 qs b j (fst (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))))
          by misK_perm G1.
        specialize (P1 P1h). clear P1h.
        match goal with |- context [run3 qs ?b0 ?j0 (if ?w then list_drop_tra ?x ?y else [])] =>
          pose proof (misK_nore M0 S0 _ qs _ b0 j0 (drop_nore w x y) P1) as D1
        end.
        match type of D1 with misK _ _ (slot3 ?ce ?ve ++ _) (p3_mis ?bd) =>
          match goal with |- context [lines_run ?lv ?m ?no ?c ?H ?k rl ?jj ?o ?ha ?ks] =>
            pose proof (lines_misK M0 S0 qs (slot3 ce ve ++
                          slot3 (fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))
                            (resolveF qs (snd (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))) ++ T)
                          lv m rl no c H k jj o ha ks bd Hc) as LM
          end;
          assert (D2 : misK M0 S0 (slot3 (ds_ocap s) (resolveF qs (da_out a)) ++ slot3 (ds_ka s) (resolveF qs (da_hp a)) ++
                         slot3 ce ve ++
                         slot3 (fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))
                           (resolveF qs (snd (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))) ++ T)
                         (p3_mis bd)) by misK_perm D1
        end.
        cbv zeta in LM. rewrite E1, E2 in LM. cbn [fst snd] in LM.
        destruct (LM D2) as (Hc2 & LM2). clear LM D2.
        match goal with |- context [drain_run f live mx ?s2 ?j2 ?a2] =>
          assert (H2 : misK M0 S0 (slot3 (ds_ocap s2) (resolveF qs (da_out a2)) ++ dsl qs s2 a2 ++ T) _)
            by (unfold dsl; cbn [ds_ocap ds_cap ds_ka ds_ecap da_out da_buf da_hp da_ev]; misK_perm LM2);
          pose proof (IH live mx s2 j2 a2 _ Hc2 H2) as X; cbv zeta in X; exact X
        end.
Qed.

Fixpoint gfin (qs : list sptr) (ps : list (rentry * (hsrc * nat))) (ss : list dstate) (das : list dadr) : list sptr :=
  match ps, ss, das with
  | p :: ps', s :: ss', a :: das' => (if re_eof (fst p) =? 0 then dsl qs s a else []) ++ gfin qs ps' ss' das'
  | _, _, _ => []
  end.

Lemma gone_misK M0 S0 qs ps : forall lv mx no cap pre nm j o b T, 0 <= cap ->
  misK M0 S0 (slot3 cap (resolveF qs o) ++ concat (map (gslots qs nm) ps) ++ T) (p3_mis b) ->
  let R := gone_run lv mx no cap pre ps nm j o in
  misK M0 S0 (slot3 (snd (fst (fst R))) (resolveF qs (fst (snd R))) ++ gfin qs ps (snd (fst R)) (snd (snd R)) ++ T)
    (p3_mis (run3 qs b j (fst (fst (fst R))))).
Proof.
  induction ps as [|[e hj] ps IH]; intros lv mx no cap pre nm j o b T Hc HK; cbv zeta.
  - cbn [gone_run fst snd gfin]. exact HK.
  - cbn [gone_run]. cbv zeta.
    match goal with |- context [gone_run lv mx ?n1 ?c1 pre ps nm ?j1 ?o1] =>
      pose proof (IH lv mx n1 c1 pre nm j1 o1) as IH1;
      destruct (gone_run lv mx n1 c1 pre ps nm j1 o1) as [[[t c] ss] [o' das]] eqn:ER
    end.
    cbv zeta in IH1. rewrite ?ER in IH1. cbn [fst snd] in IH1 |- *. cbn [gfin fst snd]. rewrite !run3_app.
    cbn [map concat] in HK. unfold gslots in HK. cbn [fst snd] in HK.
    unfold after_drain, after_drain_adr in *.
    destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
    + unfold drain_tr, drain_fin, drain_adr, drain_go in IH1 |- *.
      set (f := S (S (length (pending_stream (fst hj))))) in *.
      set (a0 := drain_start nm o e (fst hj)) in *.
      rewrite (drain_state_i f lv mx (drain_init no cap e (fst hj)) 0 dadr0 j a0) in IH1 |- *.
      assert (HK0 : misK M0 S0 (slot3 (ds_ocap (drain_init no cap e (fst hj))) (resolveF qs (da_out a0)) ++
                      dsl qs (drain_init no cap e (fst hj)) a0 ++ concat (map (gslots qs nm) ps) ++ T) (p3_mis b)).
      { unfold dsl, dslots, a0 in *. cbn [ds_ocap ds_cap ds_ka ds_ecap drain_init da_out da_buf da_hp da_ev drain_start] in *.
        misK_perm HK. }
      pose proof (drain_misK M0 S0 qs (concat (map (gslots qs nm) ps) ++ T) f lv mx (drain_init no cap e (fst hj)) j a0 b
                    Hc HK0) as DM.
      cbv zeta in DM. destruct DM as (Hc1 & DM).
      set (s1 := fst (snd (drain_run f lv mx (drain_init no cap e (fst hj)) j a0))) in *.
      set (a1 := snd (snd (drain_run f lv mx (drain_init no cap e (fst hj)) j a0))) in *.
      set (td := fst (drain_run f lv mx (drain_init no cap e (fst hj)) j a0)) in *.
      match goal with |- context [keys_end_run lv mx (ds_no s1) (ds_ocap s1) ?xks (j + nretF td)%nat (da_out a1)] =>
        pose proof (ke_misK M0 S0 qs (dsl qs s1 a1 ++ concat (map (gslots qs nm) ps) ++ T) xks lv mx (ds_no s1) (ds_ocap s1)
                      (j + nretF td)%nat (da_out a1) (run3 qs b j td) Hc1 DM) as K1;
        pose proof (ke_mono xks lv mx (ds_no s1) (ds_ocap s1) (j + nretF td)%nat (da_out a1) Hc1) as Mk
      end.
      match type of K1 with misK _ _ (slot3 ?ck ?xk ++ _) (p3_mis ?bk) =>
        assert (K2 : misK M0 S0 (slot3 ck xk ++ concat (map (gslots qs nm) ps) ++ (dsl qs s1 a1 ++ T)) (p3_mis bk))
          by misK_perm K1;
        assert (Hck : 0 <= ck) by lia;
        pose proof (IH1 bk (dsl qs s1 a1 ++ T) Hck K2) as K3
      end.
      unfold dsl in K3 |- *. cbn [da_buf da_hp da_ev] in K3 |- *. misK_perm K3.
    + cbn [run_from].
      match goal with |- context [keys_end_run lv mx ?n0 ?c0 ?xks ?j0 ?o0] =>
        pose proof (ke_misK M0 S0 qs (concat (map (gslots qs nm) ps) ++ T) xks lv mx n0 c0 j0 o0 b Hc HK) as K1;
        pose proof (ke_mono xks lv mx n0 c0 j0 o0 Hc) as Mk;
        assert (Hc0 : 0 <= c0) by exact Hc
      end.
      match type of K1 with misK _ _ (slot3 ?ck ?xk ++ _) (p3_mis ?bk) =>
        assert (Hck : 0 <= ck) by lia;
        pose proof (IH1 bk T Hck K1) as K3
      end.
      exact K3.
Qed.

Lemma combine_len {X Y : Type} (l : list X) (l' : list Y) : length l' = length l -> length (combine l l') = length l.
Proof. revert l'. induction l as [|x l IH]; intros [|y l'] H; cbn [combine length] in *; try lia. rewrite IH; lia. Qed.

Lemma in_combine_l {X Y : Type} (dx : X) (dy : Y) (l : list X) (l' : list Y) x :
  In x l -> length l' = length l -> exists y, In (x, y) (combine l l').
Proof.
  intros Hx Hl. destruct (In_nth l x dx Hx) as (i & Hi & Ei). exists (nth i l' dy). rewrite <- Ei.
  rewrite <- (combine_nth l l' i dx dy) by lia. apply nth_In. rewrite combine_len; lia.
Qed.

Lemma in_combine_r {X Y : Type} (dx : X) (dy : Y) (l : list X) (l' : list Y) y :
  In y l' -> length l' = length l -> exists x, In (x, y) (combine l l').
Proof.
  intros Hy Hl. destruct (In_nth l' y dy Hy) as (i & Hi & Ei). exists (nth i l dx). rewrite <- Ei.
  rewrite <- (combine_nth l l' i dx dy) by lia. apply nth_In. rewrite combine_len; lia.
Qed.

Lemma prom_gone es hs c : length hs = length es ->
  prom_c (gone_pend es hs) c + gone_cred (combine es hs) c = prom_c (pend_view hs) c.
Proof.
  revert hs. induction es as [|e es IH]; intros [|p hs] Hl; cbn [length] in Hl; try discriminate.
  - unfold prom_c, gone_pend, gone_cred, pend_view. cbn [combine map]. rewrite !zsum_nil. reflexivity.
  - injection Hl as Hl. specialize (IH hs Hl).
    unfold prom_c, gone_pend, gone_cred, pend_view in *. cbn [combine map]. rewrite !zsum_cons. cbn [fst snd].
    destruct (re_eof e =? 0); unfold cred in IH |- *; rewrite ?zsum_nil; lia.
Qed.

Lemma promb_gone es hs : length hs = length es ->
  promb (gone_pend es hs) + gone_credb (combine es hs) = promb (pend_view hs).
Proof.
  revert hs. induction es as [|e es IH]; intros [|p hs] Hl; cbn [length] in Hl; try discriminate.
  - unfold promb, gone_pend, gone_credb, pend_view. cbn [combine map]. rewrite !zsum_nil. reflexivity.
  - injection Hl as Hl. specialize (IH hs Hl).
    unfold promb, gone_pend, gone_credb, pend_view in *. cbn [combine map]. rewrite !zsum_cons. cbn [fst snd].
    destruct (re_eof e =? 0); unfold credb in IH |- *; rewrite ?zsum_nil; lia.
Qed.

Lemma gone_cred_sum e hj ps : zsumZ (gone_cred ((e, hj) :: ps)) (zseq 0 49) =
  (if re_eof e =? 0 then zsumZ (cred (fst hj)) (zseq 0 49) else 0) + zsumZ (gone_cred ps) (zseq 0 49).
Proof.
  rewrite (zsumZ_ext _ (fun c => (if re_eof e =? 0 then cred (fst hj) c else 0) + gone_cred ps c))
    by (intros c _; apply gone_cred_cons).
  rewrite zsumZ_add. destruct (re_eof e =? 0); [reflexivity|].
  change (zsumZ (fun _ : Z => 0) (zseq 0 49)) with 0. reflexivity.
Qed.

Lemma gone_ek_zlen e hj ps : zlen (gone_ek ((e, hj) :: ps)) =
  (if re_eof e =? 0 then zlen (ekeys (lines (hs_state (fst hj)) (bzs (pending_stream (fst hj))))) else 0) +
  zlen (gone_ek ps).
Proof. rewrite gone_ek_cons. unfold zlen. rewrite length_app. destruct (re_eof e =? 0); cbn [length]; lia. Qed.

Lemma after_ocap lv mx no cap e h : 0 <= mx -> 0 <= cap -> (re_eof e = 0 -> drain3 e h) ->
  0 <= ds_ocap (after_drain lv mx no cap e h).
Proof.
  intros Hm Hc Hd. unfold after_drain. destruct (Z.eqb_spec (re_eof e) 0) as [E|E].
  - destruct (Hd E lv mx no cap Hm Hc) as [H _]. lia.
  - cbn [drain_init ds_ocap]. exact Hc.
Qed.

Lemma gone_wd_le ps : forall lv mx no cap pre nm j o, 0 <= mx -> 0 <= cap ->
  Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps ->
  Forall (fun p => re_eof (fst p) = 0 -> drain_wt3 (fst p) (fst (snd p))) ps ->
  gone_wd ps (snd (fst (gone_run lv mx no cap pre ps nm j o))) <=
    NC_PER * (zsumZ (gone_cred ps) (zseq 0 49) - zlen (gone_ek ps)).
Proof.
  induction ps as [|[e hj] ps IH]; intros lv mx no cap pre nm j o Hm Hc HD HW.
  - cbn [gone_run fst snd gone_wd].
    rewrite (zsumZ_ext _ (fun _ => 0)) by (intros; reflexivity). change (zsumZ (fun _ : Z => 0) (zseq 0 49)) with 0.
    unfold zlen. cbn [gone_ek map concat length Z.of_nat]. unfold NC_PER. lia.
  - apply Forall_cons_iff in HD as [Hd HD]. apply Forall_cons_iff in HW as [Hw HW]. cbn [fst snd] in Hd, Hw.
    pose proof (after_ocap lv mx no cap e (fst hj) Hm Hc Hd) as Ho.
    cbn [gone_run]. cbv zeta.
    match goal with |- context [gone_run lv mx ?n1 ?c1 pre ps nm ?j1 ?o1] =>
      assert (Hc1 : 0 <= c1) by (eapply Z.le_trans; [exact Ho|apply ke_mono; exact Ho]);
      pose proof (IH lv mx n1 c1 pre nm j1 o1 Hm Hc1 HD HW) as IH1;
      destruct (gone_run lv mx n1 c1 pre ps nm j1 o1) as [[[t c] ss] [o' das]] eqn:ER
    end.
    cbn [fst snd] in IH1 |- *. cbn [gone_wd fst snd]. rewrite gone_cred_sum, gone_ek_zlen.
    unfold after_drain. destruct (Z.eqb_spec (re_eof e) 0) as [E|E].
    + pose proof (Hw E lv mx no cap Hm Hc) as W. unfold NC_PER in *. lia.
    + unfold NC_PER in *. lia.
Qed.

Definition ds0 : dstate := drain_init 0 0 no_entry (fst no_hj).

Lemma nth_dflt {X : Type} (l : list X) i d d' : (i < length l)%nat -> nth i l d = nth i l d'.
Proof. intros H. apply nth_indep. exact H. Qed.

Lemma gfin_in qs ps : forall ss das p, In p (gfin qs ps ss das) ->
  exists i, (i < length ps)%nat /\ (i < length ss)%nat /\ (i < length das)%nat /\
    re_eof (fst (nth i ps (no_entry, no_hj))) = 0 /\ In p (dsl qs (nth i ss ds0) (nth i das dadr0)).
Proof.
  induction ps as [|q ps IH]; intros [|s ss] [|a das] p H; cbn [gfin] in H; try destruct H.
  apply in_app_or in H as [H|H].
  - destruct (Z.eqb_spec (re_eof (fst q)) 0) as [E|E]; [|destruct H].
    exists 0%nat. cbn [length nth]. split; [lia|]. split; [lia|]. split; [lia|]. split; assumption.
  - destruct (IH ss das p H) as (i & H1 & H2 & H3 & H4 & H5). exists (S i). cbn [length nth].
    split; [lia|]. split; [lia|]. split; [lia|]. split; assumption.
Qed.

Lemma slot3_in p n x : In p (slot3 n x) -> n <> 0 /\ x = p.
Proof. unfold slot3. destruct (Z.eqb_spec n 0) as [E|E]; [intros []|intros [<-|[]]; split; [exact E|reflexivity]]. Qed.

Lemma gone_tch_cover L A OUT CAP es hs p n :
  List.NoDup (map fst (blocks L A)) -> In (p, n) (user_blocks A) ->
  ~ In p (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] (known_at L A)) (combine es hs))) ->
  ~ In (ptr_addr L p) (gone_tch OUT CAP es hs).
Proof.
  intros HB Hp Hn Ht. apply Hn. unfold gone_tch in Ht. apply in_app_or in Ht as [Ht|Ht].
  - destruct (Z.eqb_spec CAP 0) as [E|E]; [destruct Ht|]. destruct Ht as [Ht|[]].
    apply in_app_iff. left. rewrite (slot3_nz _ _ E). left. exact (sptr_at L A p n _ HB Hp (eq_sym Ht)).
  - apply in_concat in Ht as (l & Hl & Hx). apply in_map_iff in Hl as (q & <- & Hq).
    apply in_app_iff. right. apply in_concat. exists (gslots [] (known_at L A) q). split; [apply in_map; exact Hq|].
    unfold gslots, dslots. destruct (re_eof (fst q) =? 0); [|destruct Hx].
    cbn [resolve da_buf da_hp da_ev drain_start known_at].
    apply in_app_or in Hx as [Hx|Hx]; [|apply in_app_or in Hx as [Hx|Hx]].
    + destruct (Z.eqb_spec (re_cap (fst q)) 0) as [E|E]; [destruct Hx|]. destruct Hx as [Hx|[]].
      apply in_app_iff. left. rewrite (slot3_nz _ _ E). left. exact (sptr_at L A p n _ HB Hp (eq_sym Hx)).
    + destruct (Z.eqb_spec (ent_ka (fst q)) 0) as [E|E]; [destruct Hx|]. destruct Hx as [Hx|[]].
      apply in_app_iff. right. apply in_app_iff. left. rewrite (slot3_nz _ _ E). left.
      exact (sptr_at L A p n _ HB Hp (eq_sym Hx)).
    + destruct (Z.eqb_spec (hl_cap (hs_expected (fst (snd q)))) 0) as [E|E]; [destruct Hx|]. destruct Hx as [Hx|[]].
      apply in_app_iff. right. apply in_app_iff. right. rewrite (slot3_nz _ _ E). left.
      exact (sptr_at L A p n _ HB Hp (eq_sym Hx)).
Qed.

Definition gone_keep (G : Z) (es : list rentry) (hs : list (hsrc * nat)) : list Z :=
  G :: concat (map (fun q => if re_eof (fst q) =? 0 then [] else entry_nc (fst q)) (combine es hs)) ++
  concat (map (fun q => if re_eof (fst q) =? 0
                        then arr_nc (hs_pending (fst (snd q))) ++ [hs_partial (fst (snd q))] ++ arr_nc (hs_held (fst (snd q)))
                        else src_nc (fst (snd q))) (combine es hs)).

Lemma slot3_res n x : (length (slot3 n x) + res3 n = 1)%nat.
Proof. unfold slot3, res3. destruct (n =? 0); reflexivity. Qed.

Lemma arr_nc_len l : (length (arr_nc l) <= 1)%nat.
Proof. unfold arr_nc. destruct (hl_cap l =? 0); cbn [length]; lia. Qed.

Lemma cnt_pairs nm ps :
  (length (concat (map (gslots [] nm) ps)) + list_sum (map gres ps) +
   length (concat (map (fun q : rentry * (hsrc * nat) => if (re_eof (fst q) =? 0)%Z then [] else entry_nc (fst q)) ps)) +
   length (concat (map (fun q : rentry * (hsrc * nat) => if (re_eof (fst q) =? 0)%Z
                        then arr_nc (hs_pending (fst (snd q))) ++ [hs_partial (fst (snd q))] ++ arr_nc (hs_held (fst (snd q)))
                        else src_nc (fst (snd q))) ps)) <= 6 * length ps)%nat.
Proof.
  induction ps as [|[e [h i]] ps IH]; [cbn; lia|]. cbn [map concat length]. rewrite !length_app.
  change (list_sum (?x :: ?l)) with (x + list_sum l)%nat.
  set (X2 := list_sum (map gres ps)) in *.
  repeat match goal with |- context [length (concat (map ?f ps))] =>
    let X := fresh "X" in set (X := length (concat (map f ps))) in * end.
  unfold gslots, gres, dslots, dres. cbn [fst snd]. destruct (re_eof e =? 0).
  - rewrite !length_app. cbn [length].
    pose proof (slot3_res (re_cap e) (resolveF [] (da_buf (drain_start nm adr0 e h)))).
    pose proof (slot3_res (ent_ka e) (resolveF [] (da_hp (drain_start nm adr0 e h)))).
    pose proof (slot3_res (hl_cap (hs_expected h)) (resolveF [] (da_ev (drain_start nm adr0 e h)))).
    pose proof (arr_nc_len (hs_pending h)). pose proof (arr_nc_len (hs_held h)). lia.
  - unfold entry_nc, src_nc. rewrite !length_app. cbn [length].
    pose proof (arr_nc_len (hs_pending h)). pose proof (arr_nc_len (hs_held h)). pose proof (arr_nc_len (hs_expected h)).
    destruct (re_cap e =? 0); destruct (re_hp e =? 0); cbn [length]; lia.
Qed.

Lemma gone_misT_call pl K L A b al alb G OUT es hs CAP :
  RI3_ledger rv_wt pl K (view_of G OUT es hs) L A b al alb -> res_ok_pack3 A b ->
  length hs = length es -> (length es <= 4)%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> re_hp (fst p) <> 0 -> re_kh (fst p) <> 0) (combine es hs) ->
  List.NoDup (map fst (blocks L A)) -> (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
  misT (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] (known_at L A)) (combine es hs)) ++
        map (sptr_of L A) (gone_keep G es hs))
       (res3 CAP + list_sum (map gres (combine es hs))) (p3_mis b).
Proof.
  intros HL HA Hlen Hes Hkh HB HO0.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HI & _) & _).
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (HN & HU & _) & _).
  split; [exact HN|]. split.
  - intros p Hp. apply in_map_iff in Hp as (e0 & <- & He0).
    destruct (HU e0 He0) as (_ & n & Hb).
    assert (Hx : In (ptr_addr L (fst e0)) (rv_nc (view_of G OUT es hs))).
    { apply HI. unfold mis_addrs. exact (in_map (fun e1 => ptr_addr L (fst e1)) _ e0 He0). }
    rewrite <- (sptr_at L A (fst e0) n _ HB Hb eq_refl).
    assert (Hxb : In (ptr_addr L (fst e0), n) (blocks L A))
      by (unfold blocks; exact (in_map (fun b0 => (ptr_addr L (fst b0), snd b0)) _ (fst e0, n) Hb)).
    set (x := ptr_addr L (fst e0)) in *. clearbody x. clear He0 Hb.
    cbn [view_of rv_nc] in Hx. rewrite !in_app_iff.
    destruct Hx as [Hx|[Hx|Hx]].
    + right. right. apply in_map. left. exact Hx.
    + destruct (Z.eqb_spec CAP 0) as [E|E].
      * exfalso. subst x. exact (HO0 E n Hxb).
      * left. rewrite (slot3_nz _ _ E). left. rewrite Hx. reflexivity.
    + apply in_app_or in Hx as [Hx|Hx].
      * apply in_concat in Hx as (l & Hl & Hxl). apply in_map_iff in Hl as (e & <- & He).
        destruct (in_combine_l no_entry no_hj es hs e He Hlen) as (y & Hey).
        destruct (Z.eqb_spec (re_eof e) 0) as [E|E].
        -- right. left. apply in_concat. exists (gslots [] (known_at L A) (e, y)). split; [apply in_map; exact Hey|].
           unfold gslots, dslots. cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) E).
           cbn [resolve da_buf da_hp da_ev drain_start known_at].
           unfold entry_nc in Hxl. apply in_app_or in Hxl as [Hxl|Hxl].
           ++ destruct (Z.eqb_spec (re_cap e) 0) as [C|C]; [destruct Hxl|]. destruct Hxl as [Hxl|[]].
              apply in_app_iff. left. rewrite (slot3_nz _ _ C). left. rewrite Hxl. reflexivity.
           ++ destruct (Z.eqb_spec (re_hp e) 0) as [C|C]; [destruct Hxl|]. destruct Hxl as [Hxl|[]].
              rewrite Forall_forall in Hkh. pose proof (Hkh (e, y) Hey E C) as Hk. cbn [fst] in Hk.
              assert (Ek : ent_ka e <> 0) by (unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ _) C); exact Hk).
              apply in_app_iff. right. apply in_app_iff. left. rewrite (slot3_nz _ _ Ek). left. rewrite Hxl.
              reflexivity.
        -- right. right. apply in_map. right. apply in_app_iff. left. apply in_concat.
           exists (entry_nc e). split; [|exact Hxl].
           apply in_map_iff. exists (e, y). cbn [fst]. rewrite (proj2 (Z.eqb_neq _ _) E). split; [reflexivity|exact Hey].
      * apply in_concat in Hx as (l & Hl & Hxl). apply in_map_iff in Hl as (y & <- & Hy).
        destruct (in_combine_r no_entry no_hj es hs y Hy Hlen) as (e & Hey).
        destruct (Z.eqb_spec (re_eof e) 0) as [E|E].
        -- unfold src_nc in Hxl. rewrite !in_app_iff in Hxl. destruct Hxl as [Hxl|[Hxl|[Hxl|Hxl]]].
           ++ right. right. apply in_map. right. apply in_app_iff. right. apply in_concat.
              exists (arr_nc (hs_pending (fst y)) ++ [hs_partial (fst y)] ++ arr_nc (hs_held (fst y))). split.
              ** apply in_map_iff. exists (e, y). cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) E).
                 split; [reflexivity|exact Hey].
              ** apply in_app_iff. left. exact Hxl.
           ++ right. right. apply in_map. right. apply in_app_iff. right. apply in_concat.
              exists (arr_nc (hs_pending (fst y)) ++ [hs_partial (fst y)] ++ arr_nc (hs_held (fst y))). split.
              ** apply in_map_iff. exists (e, y). cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) E).
                 split; [reflexivity|exact Hey].
              ** apply in_app_iff. right. apply in_app_iff. left. exact Hxl.
           ++ right. left. apply in_concat. exists (gslots [] (known_at L A) (e, y)). split; [apply in_map; exact Hey|].
              unfold gslots, dslots. cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) E).
              cbn [resolve da_buf da_hp da_ev drain_start known_at].
              unfold arr_nc in Hxl. destruct (Z.eqb_spec (hl_cap (hs_expected (fst y))) 0) as [C|C]; [destruct Hxl|].
              destruct Hxl as [Hxl|[]]. apply in_app_iff. right. apply in_app_iff. right. rewrite (slot3_nz _ _ C).
              left. rewrite Hxl. reflexivity.
           ++ right. right. apply in_map. right. apply in_app_iff. right. apply in_concat.
              exists (arr_nc (hs_pending (fst y)) ++ [hs_partial (fst y)] ++ arr_nc (hs_held (fst y))). split.
              ** apply in_map_iff. exists (e, y). cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) E).
                 split; [reflexivity|exact Hey].
              ** apply in_app_iff. right. apply in_app_iff. right. exact Hxl.
        -- right. right. apply in_map. right. apply in_app_iff. right. apply in_concat.
           exists (src_nc (fst y)). split; [|exact Hxl]. apply in_map_iff. exists (e, y). cbn [fst snd].
           rewrite (proj2 (Z.eqb_neq _ _) E). split; [reflexivity|exact Hey].
  - rewrite !length_app, length_map. unfold gone_keep. cbn [length]. rewrite length_app.
    pose proof (cnt_pairs (known_at L A) (combine es hs)) as Hc.
    rewrite (combine_len es hs Hlen) in Hc. pose proof (slot3_res CAP (sptr_of L A OUT)). unfold NC_MAX. lia.
Qed.

Lemma gone_ek_nonneg ps : Forall (fun n => 0 <= n) (gone_ek ps).
Proof.
  induction ps as [|[e hj] ps IH]; [constructor|]. rewrite gone_ek_cons. apply Forall_app.
  split; [destruct (re_eof e =? 0); [apply ekeys_nonneg|constructor]|exact IH].
Qed.

Theorem p5c_res3_holds : p5c_res3.
Proof.
  intros E K K' L A G OUT es hs lv mx NO CAP pre. cbv zeta.
  intros (b & al & alb & HR & HL) Hk Hlen Hes Hmx Hc HD HW HN Hkh HB HO0.
  assert (HNT : gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT) <= NMAX)
    by (rewrite gone_capT_eq; exact HN).
  pose proof (gone_misT_call (ss_pl E) K L A b al alb G OUT es hs CAP HL HR Hlen Hes Hkh HB HO0) as HS.
  exists b. split; [exact HR|]. split.
  - intros qs Hq.
    exact (gone_room3 rv_wt (ss_pl E) K L A b al alb G OUT es hs lv mx NO CAP pre _ HL HD Hes Hmx Hc HNT HS qs Hq).
  - intros L' A' qs Hq HR' V' HN' HC' HB' HW1' HW' HP' HEc HEb HEF HB2 HO HF12 HF13.
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

Lemma lines_cap_dead mx ls : forall no cap H ka j o ha ks,
  fst (fst (snd (fst (lines_run false mx no cap H ka ls j o ha ks)))) = cap.
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks; cbn [lines_run fst snd]; [reflexivity|].
  cbv zeta. cbn [fst snd]. rewrite IH. reflexivity.
Qed.

Lemma lines_out_dead mx ls : forall no cap H ka j o ha ks,
  fst (fst (snd (lines_run false mx no cap H ka ls j o ha ks))) = o.
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks; cbn [lines_run fst snd]; [reflexivity|].
  cbv zeta. cbn [fst snd]. rewrite IH. reflexivity.
Qed.

Lemma drain_dead f : forall mx s j a,
  ds_ocap (fst (snd (drain_run f false mx s j a))) = ds_ocap s /\ da_out (snd (snd (drain_run f false mx s j a))) = da_out a.
Proof.
  induction f as [|f IH]; intros mx s j a; cbn [drain_run]; cbv zeta; [split; reflexivity|].
  destruct (ds_eintr s).
  - cbn [fst snd]. match goal with |- context [drain_run f false mx ?s1 ?j1 ?a1] => destruct (IH mx s1 j1 a1) as [E1 E2] end.
    rewrite E1, E2. split; reflexivity.
  - destruct (ds_pend s) as [|r0 rs]; [split; reflexivity|].
    match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end; [split; reflexivity|].
    match goal with |- context [chunk ?u ?sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run false ?m ?no ?c ?H ?k rl ?jj ?o ?ha ?ks] =>
      pose proof (lines_cap_dead m rl no c H k jj o ha ks) as D1;
      pose proof (lines_out_dead m rl no c H k jj o ha ks) as D2;
      destruct (snd (fst (lines_run false m no c H k rl jj o ha ks))) as [[oc' H'] ka'] eqn:E1;
      destruct (snd (lines_run false m no c H k rl jj o ha ks)) as [[o' ha'] ks'] eqn:E2
    end.
    cbn [fst snd] in D1, D2 |- *.
    match goal with |- context [drain_run f false mx ?s2 ?j2 ?a2] => destruct (IH mx s2 j2 a2) as [F1 F2] end.
    rewrite F1, F2. cbn [ds_ocap da_out]. split; [exact D1|exact D2].
Qed.

Lemma geia_gei f : forall pre n (H : list (list Z * adrF)),
  map fst (fst (geia_loop f pre n H)) = fst (gei_loop f pre n (map fst H)).
Proof.
  induction f as [|f IH]; intros pre n H; cbn [geia_loop gei_loop]; [reflexivity|].
  rewrite length_map. destruct (Nat.ltb n (length H)); [|reflexivity].
  assert (HN : fst (nth n H ([], adr0)) = nth n (map fst H) []) by (symmetry; exact (map_nth fst H ([], adr0) n)).
  rewrite <- HN. destruct (has_prefix pre (fst (nth n H ([], adr0)))); [|apply IH].
  pose proof (IH pre n (swap_remove ([], adr0) n H)) as R. rewrite map_swap_remove in R. cbn [fst] in R.
  destruct (geia_loop f pre n (swap_remove ([], adr0) n H)) as [E1 K1].
  destruct (gei_loop f pre n (swap_remove [] n (map fst H))) as [E2 K2]. cbn [fst map] in *. rewrite R. reflexivity.
Qed.

Lemma gone_ss_len ps : forall lv mx no cap pre nm j o, length (snd (fst (gone_run lv mx no cap pre ps nm j o))) = length ps.
Proof.
  induction ps as [|[e hj] ps IH]; intros lv mx no cap pre nm j o; [reflexivity|].
  cbn [gone_run]. cbv zeta.
  match goal with |- context [gone_run lv mx ?n1 ?c1 pre ps nm ?j1 ?o1] =>
    pose proof (IH lv mx n1 c1 pre nm j1 o1) as IH1;
    destruct (gone_run lv mx n1 c1 pre ps nm j1 o1) as [[[t c] ss] [o' das]] eqn:ER
  end.
  cbn [fst snd length] in IH1 |- *. rewrite IH1. reflexivity.
Qed.

Lemma gone_quiet ps : forall lv mx no cap pre nm j o,
  Forall (fun p => re_eof (fst p) = 0 ->
            forall (lv' : bool) (mx' NO' CAP' : Z) (j' : nat) (a : dadr),
              drain_go lv' mx' NO' CAP' (fst p) (fst (snd p)) j' a = drain_go false mx' NO' CAP' (fst p) (fst (snd p)) j' a)
    ps ->
  Forall (fun s => fst (gei pre (ds_H s)) = []) (snd (fst (gone_run lv mx no cap pre ps nm j o))) ->
  snd (fst (fst (gone_run lv mx no cap pre ps nm j o))) = cap /\ fst (snd (gone_run lv mx no cap pre ps nm j o)) = o.
Proof.
  induction ps as [|[e hj] ps IH]; intros lv mx no cap pre nm j o HQ HK; [split; reflexivity|].
  apply Forall_cons_iff in HQ as [Hq HQ]. cbn [fst snd] in Hq.
  cbn [gone_run] in HK |- *. cbv zeta in HK |- *.
  match goal with |- context [gone_run lv mx ?n1 ?c1 pre ps nm ?j1 ?o1] =>
    pose proof (IH lv mx n1 c1 pre nm j1 o1 HQ) as IH1;
    destruct (gone_run lv mx n1 c1 pre ps nm j1 o1) as [[[t c] ss] [o' das]] eqn:ER
  end.
  cbn [fst snd] in HK, IH1 |- *. apply Forall_cons_iff in HK as [Hk HK].
  destruct (IH1 HK) as (C1 & O1). rewrite C1, O1.
  set (s := after_drain lv mx no cap e (fst hj)) in *.
  set (a := after_drain_adr lv mx no cap e (fst hj) j (drain_start nm o e (fst hj))) in *.
  assert (Hl : length (da_keys a) = length (ds_H s)) by (unfold s, a; apply after_keys_len).
  assert (Hlc : length (combine (ds_H s) (da_keys a)) = length (ds_H s)) by (apply combine_len; exact Hl).
  assert (EG : geia pre (combine (ds_H s) (da_keys a)) = geia_loop (length (ds_H s)) pre 0 (combine (ds_H s) (da_keys a)))
    by (unfold geia; rewrite Hlc; reflexivity).
  pose proof (geia_gei (length (ds_H s)) pre 0 (combine (ds_H s) (da_keys a))) as GG.
  rewrite (combine_fst _ _ Hl) in GG. change (gei_loop (length (ds_H s)) pre 0 (ds_H s)) with (gei pre (ds_H s)) in GG.
  rewrite Hk in GG. apply map_eq_nil in GG. rewrite EG, GG. cbn [map keys_end_run fst snd].
  unfold s, a, after_drain, after_drain_adr. destruct (Z.eqb_spec (re_eof e) 0) as [E|E].
  - unfold drain_fin, drain_adr.
    rewrite (Hq E lv mx no cap 0%nat dadr0), (Hq E lv mx no cap j (drain_start nm o e (fst hj))). unfold drain_go.
    destruct (drain_dead (S (S (length (pending_stream (fst hj))))) mx (drain_init no cap e (fst hj)) 0%nat dadr0)
      as [D1 _].
    destruct (drain_dead (S (S (length (pending_stream (fst hj))))) mx (drain_init no cap e (fst hj)) j
                (drain_start nm o e (fst hj))) as [_ D2].
    rewrite D1, D2. split; reflexivity.
  - split; reflexivity.
Qed.

Definition gone_tot0 : Prop :=
  forall (lv : bool) (mx NO CAP : Z) (pre : list Z) (es : list rentry) (hs : list (hsrc * nat))
         (kss : list (list (list Z))) (nm : Z -> adrF) (j : nat) (o : adrF),
    length hs = length es ->
    Forall (fun p => re_eof (fst p) = 0 ->
              lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p)))) = [] ->
              forall (lv' : bool) (mx' NO' CAP' : Z) (j' : nat) (a : dadr),
                drain_go lv' mx' NO' CAP' (fst p) (fst (snd p)) j' a = drain_go false mx' NO' CAP' (fst p) (fst (snd p)) j' a)
      (combine es hs) ->
    (forall i, (i < length es)%nat ->
       nth i kss [] = ds_H (nth i (gone_states lv mx NO CAP pre es hs)
                              (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))))) ->
    concat (map (fun i => gone_segment pre (entry_lines (nth i es no_entry) (nth i hs no_hj)) (nth i kss []))
                (seq 0 (length es))) = [] ->
    gone_cap lv mx NO CAP pre es hs = CAP /\ gone_out lv mx NO CAP pre es hs nm j o = o.

Theorem gone_tot0_holds : gone_tot0.
Proof.
  intros lv mx NO CAP pre es hs kss nm j o Hlen HQ HK HT.
  apply concat_nil_Forall in HT. rewrite Forall_map, Forall_forall in HT.
  assert (Hseg : forall i, (i < length es)%nat ->
            gone_segment pre (entry_lines (nth i es no_entry) (nth i hs no_hj)) (nth i kss []) = []).
  { intros i Hi. apply HT. apply in_seq. lia. }
  assert (HQ' : Forall (fun p => re_eof (fst p) = 0 ->
            forall (lv' : bool) (mx' NO' CAP' : Z) (j' : nat) (a : dadr),
              drain_go lv' mx' NO' CAP' (fst p) (fst (snd p)) j' a = drain_go false mx' NO' CAP' (fst p) (fst (snd p)) j' a)
            (combine es hs)).
  { apply Forall_forall. intros p Hp E0. apply (proj1 (Forall_forall _ _) HQ p Hp E0).
    destruct (In_nth _ _ (no_entry, no_hj) Hp) as (i & Hi & Ei). rewrite (combine_len es hs Hlen) in Hi.
    rewrite (combine_nth es hs i no_entry no_hj (eq_sym Hlen)) in Ei. subst p. cbn [fst snd] in *.
    pose proof (Hseg i Hi) as S0. unfold gone_segment in S0. apply app_eq_nil in S0 as [S1 _].
    unfold entry_lines in S1. rewrite (proj2 (Z.eqb_eq _ _) E0) in S1.
    destruct (lines (hs_state (fst (nth i hs no_hj))) (bzs (pending_stream (fst (nth i hs no_hj))))) as [|l Ls];
      [reflexivity|].
    unfold with_nul in S1. cbn [map concat] in S1. apply app_eq_nil in S1 as [S2 _]. apply app_eq_nil in S2 as [_ S3].
    discriminate. }
  assert (HKs : Forall (fun s => fst (gei pre (ds_H s)) = []) (gone_states lv mx NO CAP pre es hs)).
  { apply (proj2 (Forall_nth _ _)). intros i d Hi.
    assert (Hi' : (i < length es)%nat).
    { unfold gone_states in Hi. rewrite gone_ss_len, (combine_len es hs Hlen) in Hi. exact Hi. }
    rewrite (nth_dflt _ i d (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))) Hi), <- (HK i Hi').
    pose proof (Hseg i Hi') as S0. unfold gone_segment in S0. apply app_eq_nil in S0 as [_ S1].
    destruct (fst (gei pre (nth i kss []))) as [|x xs]; [reflexivity|].
    cbn [map concat] in S1. apply app_eq_nil in S1 as [S2 _]. apply app_eq_nil in S2 as [_ S3]. discriminate. }
  split.
  - unfold gone_cap. exact (proj1 (gone_quiet (combine es hs) lv mx NO CAP pre (fun _ => adr0) 0 adr0 HQ' HKs)).
  - unfold gone_out. apply (gone_quiet (combine es hs) lv mx NO CAP pre nm j o HQ').
    change (snd (fst (gone_run lv mx NO CAP pre (combine es hs) nm j o))) with (gone_ssT lv mx NO CAP pre es hs nm j o).
    rewrite gone_ssT_eq. exact HKs.
Qed.

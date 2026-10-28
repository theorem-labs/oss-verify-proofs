(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps
  AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree RSim RSimProg AsanOK.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AProto ATsafeCore ATsafeEv ATsafeAlloc.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation atot := (atotal aok apost).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition NLK0 : Z := EAGER0 + CBM + 2^34 + 2^31.

Section OpsM.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK0 + NMAXZ * 4096 <= LIMIT.
Hypothesis ABASE_SH : forall z',
  (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation KI := (ATsafeAlloc.KI Abase NLK0).
Local Notation TSM := (TSM NMAX (St:=APS)).
Local Notation TS := (TS NMAX).

(* [comment removed for export] *)
Definition JJ (Y : list (AsanCtrl.aptr * Z)) (v : Z) : preT (St:=APS) :=
  fun RNG A s mo =>
    AI Y s mo /\ aps_atop s = ATOP      (* [comment removed for export] *)
    /\ RNG = fp_ok (m_vm_lazy mo) A /\ a_space_beg (aps_m s) = SB /\ a_ptr_array (aps_m s) = PA /\ 0 <= v /\
    exists G k, QOK G (aps_m s) /\ alw_le Abase A /\ GA G A /\ abud A k /\ 0 <= k /\ k + v / 1024 <= NMAXZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_of_AMI : forall RESV ch st mo, AMI RESV ATOP ch st mo -> MOK mo.
Proof.
  intros RESV ch st mo HM. pose proof (AMI_ivs_wf _ _ _ HM) as W. destruct HM as (M1 & M2 & _ & _ & _ & M6 & _ & _ & M9 & [_ M10] & _).
  split; [exact M1|]. split; [exact M2|]. split; [exact W|]. split; [exact M9| split; [exact M6| exact M10]].
Qed.

Lemma LW_of_AINV : forall st, AINV ATOP [] [] st -> LW (a_space_beg st) (a_ptr_array st) st.
Proof.
  intros st HA. pose proof HA as (HC & _ & _ & _ & _ & _ & Hres & _).
  split; [reflexivity|]. split; [reflexivity|]. split; [unfold K_CHUNKS_BLOCK in Hres; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in X. cbv zeta in X. unfold cls_lw. lia.
Qed.

Lemma CH_bound_AI : forall Y s mo, AI Y s mo -> zsum2 (CH [] [] (aps_m s)) <= 2^34.
Proof.
  intros Y s mo ((HA & _) & _ & Hq1 & Hq2 & _).
  destruct (CH_bounds [] [] (aps_m s) HA) as [_ X]; [| unfold zlen; cbn; lia| cbn; lia| exact X].
  unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia.
Qed.

Lemma KI_entry : forall Y v RNG A s mo extra,
  JJ Y v RNG A s mo -> 0 <= extra <= 2^31 ->
  exists G k, KI (PHI (aps_m s) + extra) G A k mo /\ QOK G (aps_m s) /\ k + v / 1024 <= NMAXZ /\ LW SB PA (aps_m s) /\ next_fresh (aps_m s).
Proof.
  intros Y v RNG A s mo extra HJ Hex. pose proof HJ as (HAI & HAT & _ & HSB' & HPA' & Hv & G & k & HQ & HAB & HGA & HBU & Hk & Hkv).
  pose proof HAI as ((HA & HM) & _). rewrite HAT in HA, HM. exists G, k.
  assert (HL : LW SB PA (aps_m s)) by (rewrite <- HSB', <- HPA'; apply LW_of_AINV; exact HA).
  split; [| split; [exact HQ| split; [exact Hkv| split; [exact HL| destruct HA as (_ & _ & _ & _ & _ & _ & _ & NF & _); exact NF]]]].
  pose proof (PHI_nonneg SB PA _ HL). pose proof (commit_bytes_LW SB PA _ HL).
  pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)). pose proof (CH_bound_AI _ _ _ HAI).
  split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [unfold PHI, NLK0 in *; lia|].
  split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

Lemma JJ_acct : forall Y v RNG A s mo, JJ Y v RNG A s mo -> acct_ok NMAX RNG A mo.
Proof.
  intros Y v RNG A s mo HJ. destruct (KI_entry Y v RNG A s mo 0 HJ ltac:(lia)) as (G & k & HK & _ & Hkv & _).
  pose proof HJ as (_ & _ & -> & _ & _ & Hv & _). pose proof (Z.div_pos v 1024).
  eapply KI_acct_ok; [exact HLIM| exact HK| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma div_add_le : forall a b m, 0 < m -> a / m + b / m <= (a + b) / m.
Proof.
  intros a b m Hm. apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le a m ltac:(lia)). pose proof (Z.mul_div_le b m ltac:(lia)). lia.
Qed.

Lemma pcost_sec : forall n, 64512 < n <= 2^40 -> pcost (sec_map_size n) <= n / 1024.
Proof.
  intros n Hn. pose proof (sec_map_size_bounds n Hn) as SBn. unfold pcost.
  set (s := sec_map_size n) in *.
  pose proof (Z.div_le_mono s (n + 12296) 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono s (n + 12296) 32768 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 4096 ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 32768 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 32768 ltac:(lia)).
  pose proof (Z.div_mod n 1024 ltac:(lia)). pose proof (Z.mod_pos_bound n 1024 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma TS_alift : forall {R X} (t : AM R) (s : APS) RNG A mo (Q1 : postT R) (Q : postM (St:=APS) X) (f : R -> X * APS),
  TS RNG A (aembed ATOP t) mo (EQ Q1) ->
  (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 r RNG' A' mo' -> Q (fst (f r)) RNG' A' (snd (f r)) mo') ->
  TS RNG A (ebind (aembed ATOP t) (fun r => Ret (Ok (f r)))) mo (MQ Q).
Proof.
  intros R X t s RNG A mo Q1 Q f H HQ. eapply TS_ebind; [exact H|].
  intros r RNG' A' mo' HA H1. apply TS_ret_ok; [exact HA|]. cbn. apply HQ; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma HLB_of_HISTOK : forall RESV Y st mo n, INV RESV ATOP [] [] st mo -> Permutation Y (live_pairs st) -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st).
Proof.
  intros RESV Y st mo n HI HPY Hn HH mb ms.
  set (dummy := mkch n 70368744177664 (sec_map_size n)).
  assert (Hwf : chunk_wf ATOP dummy).
  { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
    - cbn. split; [|reflexivity]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
    - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)).
      unfold KHIGH. unfold REQMAX in Hn. atop_facts. repeat split; try lia. }
  apply (live_budget_list_sig dummy). { unfold dummy, mkch. destruct (is_primary n); reflexivity. }
  apply (live_budget_of_HISTOK (ATOP:=ATOP)).
  + constructor; [exact Hwf|]. destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW.
    apply Forall_app in HW as [HWl _]. exact HWl.
  + unfold sizes. cbn [map]. replace (chunk_size dummy) with n by (unfold dummy, mkch; destruct (is_primary n); reflexivity).
    fold (sizes (live_chunks st)). rewrite <- sizes_live_pairs. eapply HISTOK_perm; [|exact HH]. apply perm_skip. apply Permutation_map. exact HPY.
Qed.

Lemma U_malloc : forall Y v n,
  0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  TSM (fun RNG A s mo => JJ Y v RNG A s mo /\ n <= v) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JJ ((q, n) :: Y) (v - n) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v n Hn HH. unfold amalloc_M.
  apply TSM_bind_get; [| intros RNG A s mo [HJ _]; eapply JJ_acct; exact HJ].
  intros s0.
  set (pc := if is_primary n then 0 else pcost (sec_map_size n)).
  eapply TSM_bind with (Q1 := fun x RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     Permutation Y (live_pairs (aps_m s0)) /\ a_qloc_bytes (aps_m s0) <= Q_CACHE /\ a_qglob_bytes (aps_m s0) <= Q_MAX /\ n <= v /\
     exists G' b' k', RPm SB PA G' x /\ malloc_post (RESV:=aps_resv s0) (ATOP:=ATOP) (aps_m s0) n x mo /\ minv (strip mo) /\ m_halted mo = None
                        /\ KI b' G' A k' mo /\ k' + (v - n) / 1024 <= NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A).
  - (* [comment removed for export] *)
    intros RNG A s mo (-> & HJ & Hnv). destruct s0 as [st so RESV atp].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & _). cbn [aps_m] in HSB', HPA'. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2.
    assert (Hex : 0 <= (if is_primary n then 0 else sec_map_size n) <= 2^31).
    { destruct (is_primary n) eqn:EP; [lia|]. pose proof (not_primary_large n ltac:(lia) EP).
      pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)). unfold REQMAX in Hn. lia. }
    destruct (KI_entry Y v _ A _ mo _ HJ Hex) as (G & k & HK & HQ & Hkv & HL & HNF). cbn [aps_m] in HK, HQ, HL, HNF.
    assert (PC : 0 <= pc <= n / 1024).
    { subst pc. destruct (is_primary n) eqn:EP; [pose proof (Z.div_pos n 1024); lia|].
      pose proof (not_primary_large n ltac:(lia) EP). unfold REQMAX in Hn.
      pose proof (pcost_sec n ltac:(lia)). pose proof (pcost_nonneg (sec_map_size n) ltac:(pose proof (sec_map_size_bounds n ltac:(lia)); lia)). lia. }
    eapply (TS_alift (amalloc ATOP RESV st n) (mkAPS st so RESV ATOP) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP))).
    + eapply (TS_aembed NMAX SB PA Abase NLK0 HLIM ABASE_SH (amalloc ATOP RESV st n) (RPm SB PA)
                (fun r mo' => malloc_post st n r mo' /\ FR mo mo') _ G _ A k (k + pc) mo).
      * apply atotal_FR. apply (amalloc_core st mo n HI Hq1 Hq2 ltac:(unfold REQMAX in Hn; lia)). eapply HLB_of_HISTOK; eauto.
      * apply evq_amalloc; [exact HL| exact HQ| exact HNF| lia].
      * exact HK.
      * destruct (is_primary n); constructor; [lia| constructor].
      * subst pc. destruct (is_primary n); cbn; lia.
      * pose proof (Z.div_le_mono n v 1024 ltac:(lia) Hnv). lia.
    + intros r RNG' A' mo' HA HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hnv|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [| exact H6].
      pose proof (div_add_le n (v - n) 1024 ltac:(lia)). replace (n + (v - n)) with v in H by lia. lia.
  - (* [comment removed for export] *)
    intros x. eapply TSM_bind; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|].
    intros []. apply TSM_ret. intros RNG A s mo (HA & s1 & -> & _ & -> & HAT0 & HP). split; [exact HA|].
    destruct HP as (HPY & Hq1 & Hq2 & Hnv & G' & b' & k' & HRP & HMP & Hmi & Hh & HK & Hkv & ->).
    destruct s0 as [st so RESV atp]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m] in HMP.
    destruct x as [st' op]. destruct HMP as (ch & Hop & HI2 & Hlive & Hnone & Hsz & Eq1 & Eq2 & Eq3 & Eq4). cbn [fst snd] in *.
    subst op. exists (a_next st). split; [reflexivity|]. split; [| unfold REQMAX in Hn; lia].
    destruct HRP as [HL' HQ']. pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
    split; [| split; [reflexivity| split; [reflexivity| split; [exact (proj1 HL')| split; [exact (proj1 (proj2 HL'))| split; [lia|]]]]]].
    + (* [comment removed for export] *)
      unfold AI. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split; [exact HI2|]. split.
      * unfold live_pairs. rewrite Hlive.
        eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
        cbn [map fst snd]. rewrite Hsz. apply perm_skip. exact HPY.
      * rewrite Eq1, Eq2. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hmi| exact Hh].
    + exists G', k'. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0| exact Hkv].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma U_free : forall Y v q n,
  TSM (JJ ((q, n) :: Y) v) (afree_M q) (fun _ RNG A s mo => JJ Y v RNG A s mo).
Proof.
  intros Y v q n. unfold afree_M.
  apply TSM_bind_get; [| intros RNG A s mo HJ; eapply JJ_acct; exact HJ].
  intros s0.
  eapply TSM_bind with (Q1 := fun st' RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     exists G' b' k', RPst SB PA G' st' /\ free_post (RESV:=aps_resv s0) (ATOP:=ATOP) (aps_m s0) q st' mo /\ minv (strip mo) /\ m_halted mo = None
                      /\ KI b' G' A k' mo /\ k' + v / 1024 <= NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A /\ 0 <= v
                      /\ Permutation ((q, n) :: Y) (live_pairs (aps_m s0))).
  - intros RNG A s mo (-> & HJ). destruct s0 as [st so RESV atp].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & _). cbn [aps_m] in HSB', HPA'. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2.
    assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
    destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
    destruct (KI_entry _ v _ A _ mo 0 HJ ltac:(lia)) as (G & k & HK & HQ & Hkv & HL & HNF). cbn [aps_m] in HK, HQ, HL, HNF.
    eapply (TS_alift (afree st (Some q)) (mkAPS st so RESV ATOP) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP))).
    + eapply (TS_aembed NMAX SB PA Abase NLK0 HLIM ABASE_SH (afree st (Some q)) (RPst SB PA)
                (fun st' mo' => free_post (RESV:=RESV) (ATOP:=ATOP) st q st' mo' /\ FR mo mo') [] G (PHI st + 0) A k k mo).
      * apply atotal_FR. eapply (afree_core (ATOP:=ATOP)); eauto.
      * apply evq_afree; [exact HL| exact HQ].
      * exact HK.
      * constructor.
      * cbn. lia.
      * pose proof (Z.div_pos v 1024). lia.
    + intros r RNG' A' mo' HA HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia|]. split; [exact H6|]. split; [exact Hv| exact HPY].
  - intros st'. eapply TSM_post; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|]. cbv beta.
    intros [] RNG A s mo HA (s1 & -> & _ & -> & HAT0 & HP).
      destruct HP as (G' & b' & k' & [HL' HQ'] & HFP & Hmi & Hh & HK & Hkv & -> & Hv & HPY).
      destruct s0 as [st so RESV atp]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m aps_resv aps_atop] in HFP, HPY.
      destruct HFP as (HI2 & Hlive & Hnext & Hq1' & Hq2').
      pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
      assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
      destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
      split; [| split; [reflexivity| split; [reflexivity| split; [exact (proj1 HL')| split; [exact (proj1 (proj2 HL'))| split; [exact Hv|]]]]]].
      * unfold AI. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split; [exact HI2|]. split.
        -- unfold live_pairs. rewrite Hlive. eapply (Permutation_cons_inv (a := (q, n))).
           eapply Permutation_trans; [exact HPY|]. unfold live_pairs. rewrite <- Hsz.
           change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
             with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
           apply Permutation_map. apply Permutation_sym. apply map_to_list_delete. exact Hl.
        -- split; [exact Hq1'|]. split; [exact Hq2'|]. split; [exact Hmi| exact Hh].
      * exists G', k'. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0| exact Hkv].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma U_annot : forall Y v q cap old new,
  In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  TSM (JJ Y v) (aannot_M q cap old new) (fun _ RNG A s mo => JJ Y v RNG A s mo).
Proof.
  intros Y v q cap old new Hin Hold Hnew Hmin. unfold aannot_M.
  apply TSM_bind_get; [| intros RNG A s mo HJ; eapply JJ_acct; exact HJ].
  intros s0.
  eapply TSM_bind with (Q1 := fun st' RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     exists G' b' k', RPst SB PA G' st' /\ (st' = aps_m s0 /\ INV (aps_resv s0) (aps_atop s0) [] [] (aps_m s0) mo) /\ minv (strip mo) /\ m_halted mo = None
                      /\ KI b' G' A k' mo /\ k' + v / 1024 <= NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A /\ 0 <= v
                      /\ Permutation Y (live_pairs (aps_m s0)) /\ a_qloc_bytes (aps_m s0) <= Q_CACHE /\ a_qglob_bytes (aps_m s0) <= Q_MAX).
  - intros RNG A s mo (-> & HJ). destruct s0 as [st so RESV atp].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & _). cbn [aps_m] in HSB', HPA'. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2.
    assert (Hin' : In (q, cap) (live_pairs st)) by (eapply Permutation_in; [exact HPY| exact Hin]).
    destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
    destruct (KI_entry _ v _ A _ mo 0 HJ ltac:(lia)) as (G & k & HK & HQ & Hkv & HL & HNF). cbn [aps_m] in HK, HQ, HL, HNF.
    eapply (TS_alift (aannotate st q cap old new) (mkAPS st so RESV ATOP) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP))).
    + eapply (TS_aembed NMAX SB PA Abase NLK0 HLIM ABASE_SH (aannotate st q cap old new) (RPst SB PA)
                (fun st' mo' => (st' = st /\ INV RESV ATOP [] [] st mo') /\ FR mo mo') [] G (PHI st + 0) A k k mo).
      * apply atotal_FR. eapply (aannotate_core RESV ATOP); eauto.
      * eapply evq_aannotate; [exact HL| exact HQ| exact Hl| lia].
      * exact HK.
      * constructor.
      * cbn. lia.
      * pose proof (Z.div_pos v 1024). lia.
    + intros r RNG' A' mo' HA HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia|]. split; [exact H6|]. split; [exact Hv|]. split; [exact HPY|]. split; [exact Hq1| exact Hq2].
  - intros st'. eapply TSM_post; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|]. cbv beta.
    intros [] RNG A s mo HA (s1 & -> & _ & -> & HAT0 & HP).
      destruct HP as (G' & b' & k' & [HL' HQ'] & [-> HI2] & Hmi & Hh & HK & Hkv & -> & Hv & HPY & Hq1 & Hq2).
      destruct s0 as [st so RESV atp]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m aps_resv aps_atop] in HI2, HPY, Hq1, Hq2, HL', HQ'.
      pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
      split; [| split; [reflexivity| split; [reflexivity| split; [exact (proj1 HL')| split; [exact (proj1 (proj2 HL'))| split; [exact Hv|]]]]]].
      * unfold AI. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split; [exact HI2|]. split; [exact HPY|].
        split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hmi| exact Hh].
      * exists G', k'. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0| exact Hkv].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma JJ_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> JJ Y v RNG A s mo -> JJ Y' v RNG A s mo.
Proof. intros Y Y' v RNG A s mo HP (HAI & H). split; [eapply AI_perm; [exact HP| exact HAI]| exact H]. Qed.

Lemma JJ_so : forall Y v RNG A s mo w, JJ Y v RNG A s mo -> JJ Y v RNG A (aset_so w s) mo.
Proof. intros Y v RNG A [st so RESV atp] mo w (HAI & H). split; [apply AI_so; exact HAI| exact H]. Qed.

Lemma JJ_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> JJ Y v RNG A s mo -> JJ Y v' RNG A s mo.
Proof.
  intros Y v v' RNG A s mo Hv (HAI & HAT & HR & HSB' & HPA' & _ & G & k & HQ & HAB & HGA & HBU & Hk & Hkv).
  split; [exact HAI|]. split; [exact HAT|]. split; [exact HR|]. split; [exact HSB'|]. split; [exact HPA'|]. split; [lia|].
  exists G, k. pose proof (Z.div_le_mono v' v 1024 ltac:(lia) ltac:(lia)). repeat (split; [assumption|]). lia.
Qed.

Lemma AMI_with_tid : forall RESV atop ch st t mo, AMI RESV atop ch st (with_tid t mo) <-> AMI RESV atop ch st mo.
Proof. intros. unfold AMI, Pm. cbn. tauto. Qed.

Lemma JJ_model : forall Y v RNG A s mo, JJ Y v RNG A s mo -> minvA mo /\ m_halted mo = None.
Proof. intros Y v RNG A s mo (HAI & _). exact (AI_model _ _ _ HAI). Qed.

(* [comment removed for export] *)
Lemma JJ_io : forall n Y v RNG A s mo rsp mo' evs,
  io_node n -> nstep n mo rsp mo' evs -> JJ Y v RNG A s mo -> JJ Y v RNG A s mo'.
Proof.
  intros n Y v RNG A s mo rsp mo' evs Hio Hst HJ.
  pose proof HJ as (HAI & HAT & HR & Hrest). pose proof (AI_model _ _ _ HAI) as [HMA Hh].
  destruct (asan_ok_MI2 n mo rsp mo' evs Hst Hio HMA Hh) as [HMA' Hh']. pose proof (proj1 HMA') as Hmi'.
  destruct (nstep_io_shape n mo rsp mo' evs Hio Hst) as [-> | [(f & ->) | (t & ->)]].
  - exact HJ.
  - split; [apply AI_fds; [exact HAI| exact HMA'| exact Hh']|]. split; [exact HAT|]. split; [exact HR| exact Hrest].
  - split; [| split; [exact HAT| split; [exact HR| exact Hrest]]].
    destruct s as [st so RESV atp]. destruct HAI as ([HA HM] & HP & Hq1 & Hq2 & _). unfold AI. cbn [aps_m aps_resv aps_atop] in *.
    split; [split; [exact HA| apply AMI_with_tid; exact HM]|]. split; [exact HP|]. split; [exact Hq1|]. split; [exact Hq2|].
    split; [exact Hmi'| exact Hh'].
Qed.
End OpsM.
End CANSEC1.

(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps
  AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree RSim RSimProg AsanOK.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AProto ATsafeCore ATsafeEv ATsafeAlloc.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Section OpsM.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Local Notation NMAXZ := (Z.of_nat NMAX).
(* [comment removed for export] *)
Hypothesis HRES : NMAXZ * 4096 <= RESERVE34.
(* [comment removed for export] *)
Hypothesis ABASE_SH : forall z',
  ((exists c, 1 <= c <= 31 /\
      (shad (SB + c * K_REGION) <= z' < shad (SB + c * K_REGION + UWIN)
       \/ shad (SB + c * K_REGION + K_FREEARR_OFF) <= z' < shad (SB + c * K_REGION + K_FREEARR_OFF + FWIN)))
   \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation KI := (ATsafeAlloc.KI Abase).
Local Notation TSM := (TSM NMAX (St:=APS)).
Local Notation TS := (TS NMAX).

(* [comment removed for export] *)
Definition pcred (v w : Z) : Z := v / 4096 + v / 32768 + 9 * w.

#[using="rc NMAX"] Lemma pcred_nonneg : forall v w, 0 <= v -> 0 <= w -> 0 <= pcred v w.
Proof. intros v w Hv Hw. unfold pcred. Local Ltac2 Set LiaHints.tbl := fun () => "0030>18928845742.1518930958230.143508332691.16 00000400500<S2HvSS2Hv2Hw".
pose proof (Z.div_pos v 4096 Hv ltac:(lia)). pose proof (Z.div_pos v 32768 Hv ltac:(lia)). lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc NMAX"] Lemma div_add_le : forall a b m, 0 < m -> a / m + b / m <= (a + b) / m.
Proof.
  intros a b m Hm. Local Ltac2 Set LiaHints.tbl := fun () => "0030>36224569477.1436226673853.1551758037678.1600000400800AS2HmS2HmS2Hm1H2H0".
apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le a m ltac:(lia)). pose proof (Z.mul_div_le b m ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc NMAX"] Lemma pcred_mono : forall v w v' w', 0 <= v' <= v -> 0 <= w' <= w -> pcred v' w' <= pcred v w.
Proof.
  intros v w v' w' Hv Hw. unfold pcred.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>1343847615.17 1350123655.16 18928845742.1718930958230.1631597717089.1800000400800900:00FS2HvS2HvSSS2Hv2Hw1H2H0".
pose proof (Z.div_le_mono v' v 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono v' v 32768 ltac:(lia) ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc NMAX"] Lemma pcred_split : forall v w n, 0 <= n <= v -> 1 <= w -> n / 4096 + n / 32768 + 9 + pcred (v - n) (w - 1) <= pcred v w.
Proof.
  intros v w n Hn Hw. unfold pcred.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>18810493718.1718930958230.1518930958230.1619892069919.1700000100200300=SSSS2Hn2D12D2".
pose proof (div_add_le n (v - n) 4096 ltac:(lia)) as D1. pose proof (div_add_le n (v - n) 32768 ltac:(lia)) as D2.
  replace (n + (v - n)) with v in D1, D2 by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition JJ (Y : list (AsanCtrl.aptr * Z)) (v w : Z) : preT (St:=APS) :=
  fun RNG A s mo =>
    AI0 Y s mo /\ aps_atop s = ATOP
    /\ RNG = fp_ok (m_vm_lazy mo) A /\ a_space_beg (aps_m s) = SB /\ a_ptr_array (aps_m s) = PA /\ 0 <= v
    /\ (0 <= w /\ Z.of_N (a_next (aps_m s)) + w <= NOPS)
    /\ exists G k, QOK G (aps_m s) /\ alw_le Abase A /\ GA G A /\ abud A k /\ 0 <= k /\ k + pcred v w <= NMAXZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma MOK_of_AMI : forall RESV ch st mo, AMI RESV ATOP ch st mo -> MOK mo.
Proof.
  intros RESV ch st mo HM. pose proof (AMI_ivs_wf _ _ _ HM) as W. destruct HM as (M1 & M2 & _ & _ & _ & M6 & _ & _ & M9 & [_ M10] & _).
  split; [exact M1|]. split; [exact M2|]. split; [exact W|]. split; [exact M9| split; [exact M6| exact M10]].
Qed.

#[using="NMAX"] Lemma LW_of_AINV : forall st, AINV ATOP [] [] st -> LW (a_space_beg st) (a_ptr_array st) st.
Proof.
  intros st HA. pose proof HA as (HC & _ & _ & _ & _ & _ & Hres & _).
  split; [reflexivity|]. split; [reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "0030>42241182548.1758520610802.1464456719525.1400000300900?S1XS4HresS4Hres".
split; [unfold K_CHUNKS_BLOCK in Hres; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in X. cbv zeta in X. unfold cls_lw. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc NMAX"] Lemma CH_bound_AI : forall Y s mo, AI0 Y s mo -> zsum2 (CH [] [] (aps_m s)) <= 2^32 + 2^31.
Proof.
  intros Y s mo (((HA & _) & _ & Hq1 & Hq2 & _) & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>44133323233.1664586132308.1768364165876.1600000100B00CSS3Hb13Hb23Hq13Hq2S".
destruct (CH_bounds [] [] (aps_m s) HA) as [_ X]; [| unfold zlen; cbn; lia| cbn; lia| exact X].
  unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma KI_entry : forall Y v w RNG A s mo extra,
  JJ Y v w RNG A s mo -> 0 <= extra <= 2^31 ->
  exists G k, KI (PHI (aps_m s) + extra) G A k mo /\ QOK G (aps_m s) /\ k + pcred v w <= NMAXZ /\ LW SB PA (aps_m s) /\ next_fresh (aps_m s).
Proof.
  intros Y v w RNG A s mo extra HJ Hex. pose proof HJ as (HAI & HAT & _ & HSB' & HPA' & Hv & Hw & G & k & HQ & HAB & HGA & HBU & Hk & Hkv).
  pose proof HAI as (((HA & HM) & _ & Hq1 & Hq2 & _) & (HFA & HAN & HVC)). pose proof (CH_bound_AI _ _ _ HAI) as CB. rewrite HAT in HA, HM. exists G, k.
  assert (HL : LW SB PA (aps_m s)) by (rewrite <- HSB', <- HPA'; apply LW_of_AINV; exact HA).
  split; [| split; [exact HQ| split; [exact Hkv| split; [exact HL| destruct HA as (_ & _ & _ & _ & _ & _ & _ & NF & _); exact NF]]]].
  pose proof (PHI_nonneg SB PA _ HL). pose proof (commit_bytes_LW SB PA _ HL).
  pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)) as NB. pose proof (commit_le_VC _ HFA) as CV.
  split; [eapply MOK_of_AMI; exact HM|]. Local Ltac2 Set LiaHints.tbl := fun () => "0020>4352167593.48 44634979053.4700000D00KS2Hw3HVC2CB2NB2CV2H1S3Hex1H".
split; [lia|]. split.
  { (* [comment removed for export] *)
    unfold VCB, VC0, NOPS, EAGER0, RESERVE34, LIMIT34 in *. pose proof (Nat2Z.is_nonneg (length Y)). lia. }
  split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="HRES"] Lemma JJ_acct : forall Y v w RNG A s mo, JJ Y v w RNG A s mo -> acct_ok NMAX RNG A mo.
Proof.
  intros Y v w RNG A s mo HJ. Local Ltac2 Set LiaHints.tbl := fun () => "0020>40621314847.246642786458.18 000007008S3Hkv1HS".
destruct (KI_entry Y v w RNG A s mo 0 HJ ltac:(lia)) as (G & k & HK & _ & Hkv & _).
  pose proof HJ as (_ & _ & -> & _ & _ & Hv & [Hw _] & _). pose proof (pcred_nonneg v w Hv Hw).
  eapply KI_acct_ok; [exact HRES| exact HK| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="rc NMAX"] Lemma pcost_sec : forall n, 64512 < n <= 2^40 -> pcost (sec_map_size n) <= n / 1024.
Proof.
  intros n Hn. pose proof (sec_map_size_bounds n Hn) as SBn. unfold pcost.
  set (s := sec_map_size n) in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "00;0>18926759025.1818926759283.2018926759799.1618928844968.2118928845226.1918928845484.1718928845742.1518930958230.1439135398388.2251685822152.1551687928560.1400000100200300400500600700800Q00V00[SSSSSSSSS2Hn3SBn1H2H02H12H32H52H6S3SBnS3SBn".
pose proof (Z.div_le_mono s (n + 12296) 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono s (n + 12296) 32768 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 4096 ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 32768 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 32768 ltac:(lia)).
  pose proof (Z.div_mod n 1024 ltac:(lia)). pose proof (Z.mod_pos_bound n 1024 ltac:(lia)).
  lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc NMAX"] Lemma pcost_sec2 : forall n, 64512 < n <= 2^40 -> pcost (sec_map_size n) <= n / 4096 + n / 32768 + 9.
Proof.
  intros n Hn. pose proof (sec_map_size_bounds n Hn) as SBn. unfold pcost.
  set (s := sec_map_size n) in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "00=0>18926758525.2218926759025.1818926759283.2018926759799.1618928844968.2118928845226.1918928845484.1718928845742.1518928846758.2318930958230.1451685822152.1551687928560.1463317054445.2400000100200300400500600700800900:00?00D00cSSSSSSSSSSS3SBnS3SBnS2Hn3SBn1H2H02H12H32H52H62H72H8".
pose proof (Z.div_le_mono s (n + 12296) 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono s (n + 12296) 32768 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 4096 ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 32768 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 32768 ltac:(lia)).
  pose proof (Z.div_mod n 4096 ltac:(lia)). pose proof (Z.mod_pos_bound n 4096 ltac:(lia)).
  pose proof (Z.div_mod n 32768 ltac:(lia)). pose proof (Z.mod_pos_bound n 32768 ltac:(lia)).
  lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma TS_alift : forall {R X} (t : AM R) (s : APS) RNG A mo (Q1 : postT R) (Q : postM (St:=APS) X) (f : R -> X * APS),
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
#[using="NMAX"] Lemma HLB_of_HISTOK : forall RESV Y st mo n, INV RESV ATOP [] [] st mo -> Permutation Y (live_pairs st) -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st).
Proof.
  intros RESV Y st mo n HI HPY Hn HH mb ms.
  set (dummy := mkch n 70368744177664 (sec_map_size n)).
  assert (Hwf : chunk_wf ATOP dummy).
  { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
    - cbn. split; [|reflexivity]. Local Ltac2 Set LiaHints.tbl := fun () => "0060>2431248216.23 47473516478.2453679296932.2557455134063.256720561927.25 6726852284.24 00000400:00D00G00K00OS2HnS2Hn1HS2Hn2H02H1S1HS2HnS2n0".
split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
    - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)).
      unfold KHIGH. unfold REQMAX in Hn. atop_facts. repeat split; try lia. }
  apply (live_budget_list_sig dummy). { unfold dummy, mkch. destruct (is_primary n); reflexivity. }
  apply (live_budget_of_HISTOK (ATOP:=ATOP)).
  + constructor; [exact Hwf|]. destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW.
    apply Forall_app in HW as [HWl _]. exact HWl.
  + unfold sizes. cbn [map]. replace (chunk_size dummy) with n by (unfold dummy, mkch; destruct (is_primary n); reflexivity).
    fold (sizes (live_chunks st)). rewrite <- sizes_live_pairs. eapply HISTOK_perm; [|exact HH]. apply perm_skip. apply Permutation_map. exact HPY.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="HRES ABASE_SH"] Lemma U_malloc : forall Y v w n,
  0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  TSM (fun RNG A s mo => JJ Y v w RNG A s mo /\ n <= v /\ 1 <= w) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JJ ((q, n) :: Y) (v - n) (w - 1) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v w n Hn HH. unfold amalloc_M.
  apply TSM_bind_get; [| intros RNG A s mo [HJ _]; eapply JJ_acct; exact HJ].
  intros s0.
  set (pc := if is_primary n then 0 else pcost (sec_map_size n)).
  eapply TSM_bind with (Q1 := fun x RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     Permutation Y (live_pairs (aps_m s0)) /\ a_qloc_bytes (aps_m s0) <= Q_CACHE /\ a_qglob_bytes (aps_m s0) <= Q_MAX /\ n <= v /\
     (1 <= w /\ Z.of_N (a_next (aps_m s0)) + w <= NOPS /\ VC (aps_m s0) <= VCB (Z.of_N (a_next (aps_m s0))) (Z.of_nat (length Y))) /\
     exists G' b' k', RPm SB PA G' x /\ malloc_post (RESV:=aps_resv s0) (ATOP:=ATOP) (aps_m s0) n x mo /\ minv (strip mo) /\ m_halted mo = None
                        /\ KI b' G' A k' mo /\ k' + pcred (v - n) (w - 1) <= NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A).
  - (* [comment removed for export] *)
    intros RNG A s mo (-> & HJ & Hnv & Hw1). destruct s0 as [st so RESV atp].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & [Hw0 Hwn] & _). cbn [aps_m] in HSB', HPA', Hwn. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as ((HI & HPY & Hq1 & Hq2 & Hmi & Hh) & (HFA & HAN & HVC)). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2, HFA, HAN, HVC.
    assert (Hex : 0 <= (if is_primary n then 0 else sec_map_size n) <= 2^31).
    { Local Ltac2 Set LiaHints.tbl := fun () => "00N0>11948295747.5118928845742.5018930958230.4919059927339.512282299348.49 2424953571.52 2424953696.50 2431248216.41 2431248216.49 2431248216.51 37263503482.5138587224159.5242991119407.5644545189647.5245226041185.4945226041185.5646792652210.5647473515835.5447473516220.5347473516478.4249038045545.5053924984795.4355959996251.6762452185180.5663705752682.5065866776848.5565943351417.486642786458.41 6646549340.55 6648657248.51 00000A00B00C00M00R00V00Z00^00b00f00j01801I01M01R01]01l02302:02@02A02J02[02j02k03203:03;03@03ES2Hn3Hkv2PS2PN2PCSSS2Hn5HnextS3Hw1S2HnS2HnS2HnS2HnS2HnS2HnS2Hn3HAN3HVC1HS4HVC04HVC25HnextS2HnS3HnvS3Hnv5HnextS3Hw13Hwn5HnextS2Hn2H1S2Hn2H1S2Hn1HSS2Hn1H2H0S2Hn3Hkv2PS2PC2H4S3Hw13Hwn5HnextSS2H22H3S2Hn3HnvSS3HexS3Hex".
destruct (is_primary n) eqn:EP; [lia|]. pose proof (not_primary_large n ltac:(lia) EP).
      pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)). unfold REQMAX in Hn. lia. }
    destruct (KI_entry Y v w _ A _ mo _ HJ Hex) as (G & k & HK & HQ & Hkv & HL & HNF). cbn [aps_m] in HK, HQ, HL, HNF.
    pose proof (pcred_split v w n ltac:(lia) Hw1) as PS. pose proof (pcred_nonneg (v - n) (w - 1) ltac:(lia) ltac:(lia)) as PN.
    assert (PC : 0 <= pc <= n / 4096 + n / 32768 + 9).
    { subst pc. pose proof (Z.div_pos n 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 32768 ltac:(lia) ltac:(lia)).
      destruct (is_primary n) eqn:EP; [lia|].
      pose proof (not_primary_large n ltac:(lia) EP). unfold REQMAX in Hn.
      pose proof (pcost_sec2 n ltac:(lia)). pose proof (pcost_nonneg (sec_map_size n) ltac:(pose proof (sec_map_size_bounds n ltac:(lia)); lia)). lia. }
    eapply (TS_alift (amalloc ATOP RESV st n) (mkAPS st so RESV ATOP) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP))).
    + eapply (TS_aembed NMAX SB PA Abase HRES ABASE_SH (amalloc ATOP RESV st n) (RPm SB PA)
                (fun r mo' => malloc_post st n r mo' /\ FR mo mo') _ G _ A k (k + pc) mo).
      * apply (atotal_FR_gen ATOP). apply (amalloc_core st mo n HI Hq1 Hq2 ltac:(unfold REQMAX in Hn; lia)).
        -- eapply HLB_of_HISTOK; eauto.
        -- exact HFA.
        -- (* [comment removed for export] *) unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length Y)). lia.
        -- split; [exact HSB'| exact HPA'].
      * apply evq_amalloc; [exact HL| exact HQ| exact HNF| lia].
      * exact HK.
      * destruct (is_primary n); constructor; [lia| constructor].
      * subst pc. destruct (is_primary n); cbn; lia.
      * lia.
    + intros r RNG' A' mo' HA HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hnv|]. split; [split; [exact Hw1| split; [exact Hwn| exact HVC]]|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia| exact H6].
  - (* [comment removed for export] *)
    intros x. eapply TSM_bind; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|].
    intros []. apply TSM_ret. intros RNG A s mo (HA & s1 & -> & _ & -> & HAT0 & HP). split; [exact HA|].
    destruct HP as (HPY & Hq1 & Hq2 & Hnv & (Hw1 & Hwn & HVC0) & G' & b' & k' & HRP & HMP & Hmi & Hh & HK & Hkv & ->).
    destruct s0 as [st so RESV atp]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m] in HMP, Hwn, HVC0.
    destruct x as [st' op]. destruct HMP as (ch & Hop & HI2 & Hlive & Hnone & Hsz & Eq1 & Eq2 & Eq3 & Eq4 & HFA2 & HVC2 & Hnext). cbn [fst snd] in *.
    subst op. exists (a_next st). split; [reflexivity|]. split; [| unfold REQMAX in Hn; lia].
    destruct HRP as [HL' HQ']. pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
    split.
    + (* [comment removed for export] *)
      unfold AI0. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split.
      * split; [exact HI2|]. split.
        -- unfold live_pairs. rewrite Hlive.
           eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
           cbn [map fst snd]. rewrite Hsz. apply perm_skip. exact HPY.
        -- rewrite Eq1, Eq2. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hmi| exact Hh].
      * split; [exact HFA2|]. split; [rewrite Hnext, N2Z.inj_succ; lia|].
        cbn [length]. rewrite Hnext, N2Z.inj_succ, Nat2Z.inj_succ. unfold VCB in *. lia.
    + split; [reflexivity|]. split; [reflexivity|]. split; [exact (proj1 HL')|]. split; [exact (proj1 (proj2 HL'))|]. split; [lia|].
      split; [cbn [aps_m]; rewrite Hnext, N2Z.inj_succ; lia|].
      exists G', k'. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0| exact Hkv].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="HRES ABASE_SH"] Lemma U_free : forall Y v w q n,
  TSM (JJ ((q, n) :: Y) v w) (afree_M q) (fun _ RNG A s mo => JJ Y v w RNG A s mo).
Proof.
  intros Y v w q n. unfold afree_M.
  apply TSM_bind_get; [| intros RNG A s mo HJ; eapply JJ_acct; exact HJ].
  intros s0.
  (* [comment removed for export] *)
  apply TSM_if; intros _; [| apply TSM_munr; intros RNG A s mo (_ & HJ); eapply JJ_acct; exact HJ].
  eapply TSM_bind with (Q1 := fun st' RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     exists G' b' k', RPst SB PA G' st' /\ free_post (RESV:=aps_resv s0) (ATOP:=ATOP) (aps_m s0) q st' mo /\ minv (strip mo) /\ m_halted mo = None
                      /\ KI b' G' A k' mo /\ k' + pcred v w <= NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A /\ 0 <= v
                      /\ (0 <= w /\ Z.of_N (a_next (aps_m s0)) + w <= NOPS /\ VC (aps_m s0) <= VCB (Z.of_N (a_next (aps_m s0))) (Z.of_nat (length ((q, n) :: Y))))
                      /\ Permutation ((q, n) :: Y) (live_pairs (aps_m s0))).
  - intros RNG A s mo (-> & HJ). destruct s0 as [st so RESV atp].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & [Hw0 Hwn] & _). cbn [aps_m] in HSB', HPA', Hwn. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as ((HI & HPY & Hq1 & Hq2 & Hmi & Hh) & (HFA & HAN & HVC)). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2, HFA, HAN, HVC.
    assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
    destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
    Local Ltac2 Set LiaHints.tbl := fun () => "0070>2202121841.47 29597915466.5132333666502.6338587224159.4840621314847.4942991119407.516642786458.40 00000100@00H00W00^00o010SS5Hnext3Hw03HwnS3Hkv2H4S3Hw03Hwn3HVC1HS3Hkv1HS5Hnext4HVC24HVC0S".
destruct (KI_entry _ v w _ A _ mo 0 HJ ltac:(lia)) as (G & k & HK & HQ & Hkv & HL & HNF). cbn [aps_m] in HK, HQ, HL, HNF.
    eapply (TS_alift (afree st (Some q)) (mkAPS st so RESV ATOP) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP))).
    + eapply (TS_aembed NMAX SB PA Abase HRES ABASE_SH (afree st (Some q)) (RPst SB PA)
                (fun st' mo' => free_post (RESV:=RESV) (ATOP:=ATOP) st q st' mo' /\ FR mo mo') [] G (PHI st + 0) A k k mo).
      * apply (atotal_FR_gen ATOP). apply (afree_core st mo q ch HI Hq1 Hq2 Hl HFA); [| split; [exact HSB'| exact HPA']].
        (* [comment removed for export] *) cbn [length] in HVC. unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length Y)). lia.
      * apply evq_afree; [exact HL| exact HQ].
      * exact HK.
      * constructor.
      * cbn. lia.
      * pose proof HJ as (_ & _ & _ & _ & _ & _ & [Hw0' _] & _). pose proof (pcred_nonneg v w Hv Hw0'). lia.
    + intros r RNG' A' mo' HA HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia|]. split; [exact H6|]. split; [exact Hv|]. split; [split; [exact Hw0| split; [exact Hwn| exact HVC]]| exact HPY].
  - intros st'. eapply TSM_post; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|]. cbv beta.
    intros [] RNG A s mo HA (s1 & -> & _ & -> & HAT0 & HP).
      destruct HP as (G' & b' & k' & [HL' HQ'] & HFP & Hmi & Hh & HK & Hkv & -> & Hv & (Hw0 & Hwn & HVC0) & HPY).
      destruct s0 as [st so RESV atp]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m aps_resv aps_atop] in HFP, HPY, Hwn, HVC0.
      destruct HFP as (HI2 & Hlive & Hnext & Hq1' & Hq2' & HFA2 & HVC2).
      pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
      assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
      destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
      split.
      * unfold AI0. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split.
        -- split; [exact HI2|]. split.
           ++ unfold live_pairs. rewrite Hlive. eapply (Permutation_cons_inv (a := (q, n))).
              eapply Permutation_trans; [exact HPY|]. unfold live_pairs. rewrite <- Hsz.
              change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
                with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
              apply Permutation_map. apply Permutation_sym. apply map_to_list_delete. exact Hl.
           ++ split; [exact Hq1'|]. split; [exact Hq2'|]. split; [exact Hmi| exact Hh].
        -- (* [comment removed for export] *)
           split; [exact HFA2|]. split; [rewrite Hnext; lia|]. rewrite Hnext. cbn [length] in HVC0. unfold VCB in *. lia.
      * split; [reflexivity|]. split; [reflexivity|]. split; [exact (proj1 HL')|]. split; [exact (proj1 (proj2 HL'))|]. split; [exact Hv|].
        split; [cbn [aps_m]; rewrite Hnext; split; [exact Hw0| exact Hwn]|].
        exists G', k'. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0| exact Hkv].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="HRES ABASE_SH"] Lemma U_annot : forall Y v w q cap old new,
  In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  TSM (JJ Y v w) (aannot_M q cap old new) (fun _ RNG A s mo => JJ Y v w RNG A s mo).
Proof.
  intros Y v w q cap old new Hin Hold Hnew Hmin. unfold aannot_M.
  apply TSM_bind_get; [| intros RNG A s mo HJ; eapply JJ_acct; exact HJ].
  intros s0.
  eapply TSM_bind with (Q1 := fun st' RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     exists G' b' k', RPst SB PA G' st' /\ (st' = aps_m s0 /\ INV (aps_resv s0) (aps_atop s0) [] [] (aps_m s0) mo) /\ minv (strip mo) /\ m_halted mo = None
                      /\ KI b' G' A k' mo /\ k' + pcred v w <= NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A /\ 0 <= v
                      /\ (0 <= w /\ Z.of_N (a_next (aps_m s0)) + w <= NOPS
                          /\ FAINV (aps_m s0) /\ Z.of_N (a_next (aps_m s0)) <= NOPS /\ VC (aps_m s0) <= VCB (Z.of_N (a_next (aps_m s0))) (Z.of_nat (length Y)))
                      /\ Permutation Y (live_pairs (aps_m s0)) /\ a_qloc_bytes (aps_m s0) <= Q_CACHE /\ a_qglob_bytes (aps_m s0) <= Q_MAX).
  - intros RNG A s mo (-> & HJ). destruct s0 as [st so RESV atp].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & [Hw0 Hwn] & _). cbn [aps_m] in HSB', HPA', Hwn. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as ((HI & HPY & Hq1 & Hq2 & Hmi & Hh) & (HFA & HAN & HVC)). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2, HFA, HAN, HVC.
    assert (Hin' : In (q, cap) (live_pairs st)) by (eapply Permutation_in; [exact HPY| exact Hin]).
    destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
    Local Ltac2 Set LiaHints.tbl := fun () => "0060>2202121841.53 32333666502.6937575446427.5440621314847.545386939410.53 6642786458.46 00000100900H00O00T00USS3Hkv2H4S3Hw03Hwn3HVC1HS3Hkv1HS3HszS".
destruct (KI_entry _ v w _ A _ mo 0 HJ ltac:(lia)) as (G & k & HK & HQ & Hkv & HL & HNF). cbn [aps_m] in HK, HQ, HL, HNF.
    eapply (TS_alift (aannotate st q cap old new) (mkAPS st so RESV ATOP) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP))).
    + eapply (TS_aembed NMAX SB PA Abase HRES ABASE_SH (aannotate st q cap old new) (RPst SB PA)
                (fun st' mo' => (st' = st /\ INV RESV ATOP [] [] st mo') /\ FR mo mo') [] G (PHI st + 0) A k k mo).
      * apply (atotal_FR_gen ATOP). apply (aannotate_core RESV ATOP _ _ st mo q cap old new ch HI Hq1 Hq2 Hl Hsz Hold Hnew Hmin HFA).
        (* [comment removed for export] *)
        unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length Y)). lia.
      * eapply evq_aannotate; [exact HL| exact HQ| exact Hl| lia].
      * exact HK.
      * constructor.
      * cbn. lia.
      * pose proof (pcred_nonneg v w Hv Hw0). lia.
    + intros r RNG' A' mo' HA HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia|]. split; [exact H6|]. split; [exact Hv|].
      split; [split; [exact Hw0| split; [exact Hwn| split; [exact HFA| split; [exact HAN| exact HVC]]]]|].
      split; [exact HPY|]. split; [exact Hq1| exact Hq2].
  - intros st'. eapply TSM_post; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|]. cbv beta.
    intros [] RNG A s mo HA (s1 & -> & _ & -> & HAT0 & HP).
      destruct HP as (G' & b' & k' & [HL' HQ'] & [-> HI2] & Hmi & Hh & HK & Hkv & -> & Hv & (Hw0 & Hwn & HFA & HAN & HVC) & HPY & Hq1 & Hq2).
      destruct s0 as [st so RESV atp]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m aps_resv aps_atop] in HI2, HPY, Hq1, Hq2, HL', HQ', Hwn, HFA, HAN, HVC.
      pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
      split.
      * unfold AI0. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split.
        -- split; [exact HI2|]. split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hmi| exact Hh].
        -- split; [exact HFA|]. split; [exact HAN| exact HVC].
      * split; [reflexivity|]. split; [reflexivity|]. split; [exact (proj1 HL')|]. split; [exact (proj1 (proj2 HL'))|]. split; [exact Hv|].
        split; [cbn [aps_m]; split; [exact Hw0| exact Hwn]|].
        exists G', k'. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0| exact Hkv].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma JJ_perm : forall Y Y' v w RNG A s mo, Permutation Y Y' -> JJ Y v w RNG A s mo -> JJ Y' v w RNG A s mo.
Proof. intros Y Y' v w RNG A s mo HP (HAI & H). split; [eapply AI0_perm; [exact HP| exact HAI]| exact H]. Qed.

#[using="Type"] Lemma JJ_so : forall Y v w RNG A s mo x, JJ Y v w RNG A s mo -> JJ Y v w RNG A (aset_so x s) mo.
Proof. intros Y v w RNG A [st so RESV atp] mo x (HAI & H). split; [apply AI0_so; exact HAI| exact H]. Qed.

#[using="Type"] Lemma JJ_credit : forall Y v w v' w' RNG A s mo, 0 <= v' <= v -> 0 <= w' <= w -> JJ Y v w RNG A s mo -> JJ Y v' w' RNG A s mo.
Proof.
  intros Y v w v' w' RNG A s mo Hv Hw (HAI & HAT & HR & HSB' & HPA' & _ & [_ Hwn] & G & k & HQ & HAB & HGA & HBU & Hk & Hkv).
  split; [exact HAI|]. split; [exact HAT|]. split; [exact HR|]. split; [exact HSB'|]. split; [exact HPA'|]. Local Ltac2 Set LiaHints.tbl := fun () => "0030>10024596470.3537701183947.3538180647495.3600000800<00CS2Hw3HwnS2HvS3Hkv1H".
split; [lia|]. split; [lia|].
  exists G, k. pose proof (pcred_mono v w v' w' Hv Hw). repeat (split; [assumption|]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma JJ_nonneg : forall Y v w RNG A s mo, JJ Y v w RNG A s mo -> 0 <= v /\ 0 <= w.
Proof. intros Y v w RNG A s mo (_ & _ & _ & _ & _ & Hv & [Hw _] & _). split; [exact Hv| exact Hw]. Qed.

#[using="rc SB PA HSB HPA"] Lemma AMI_with_tid : forall RESV atop ch st t mo, AMI RESV atop ch st (with_tid t mo) <-> AMI RESV atop ch st mo.
Proof. intros. unfold AMI, Pm. cbn. tauto. Qed.

#[using="Type"] Lemma JJ_model : forall Y v w RNG A s mo, JJ Y v w RNG A s mo -> minvA mo /\ m_halted mo = None.
Proof. intros Y v w RNG A s mo (HAI & _). exact (AI0_model _ _ _ HAI). Qed.

(* [comment removed for export] *)
#[using="HSB HPA"] Lemma JJ_io : forall n Y v w RNG A s mo rsp mo' evs,
  io_node n -> nstep n mo rsp mo' evs -> JJ Y v w RNG A s mo -> JJ Y v w RNG A s mo'.
Proof.
  intros n Y v w RNG A s mo rsp mo' evs Hio Hst HJ.
  pose proof HJ as (HAI & HAT & HR & Hrest). pose proof (AI0_model _ _ _ HAI) as [HMA Hh].
  destruct (asan_ok_MI2 n mo rsp mo' evs Hst Hio HMA Hh) as [HMA' Hh']. pose proof (proj1 HMA') as Hmi'.
  destruct (nstep_io_shape n mo rsp mo' evs Hio Hst) as [-> | [(f & ->) | (t & ->)]].
  - exact HJ.
  - split; [apply AI0_fds; [exact HAI| exact HMA'| exact Hh']|]. split; [exact HAT|]. split; [exact HR| exact Hrest].
  - split; [| split; [exact HAT| split; [exact HR| exact Hrest]]].
    destruct s as [st so RESV atp]. destruct HAI as (([HA HM] & HP & Hq1 & Hq2 & _) & HC). unfold AI0. cbn [aps_m aps_resv aps_atop] in *.
    split; [| exact HC].
    split; [split; [exact HA| apply AMI_with_tid; exact HM]|]. split; [exact HP|]. split; [exact Hq1|]. split; [exact Hq2|].
    split; [exact Hmi'| exact Hh'].
Qed.
End OpsM.
End CANSEC1.

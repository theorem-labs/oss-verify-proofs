(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import AcctCore ModelX MmXfer NodesA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanCtrlProps SizeHist Gap AsanEmbed AsanProgDeps
  AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree AsanFreeG StepB RSim RSimProg EquivPA.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Notation atot a := (atotal (aok a) (apost a)) (only parsing).
Local Notation STOTA := (STOT (St:=APS) nstepA (fun R0 => texit (R:=R0) nstepA nexit)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition live_pairs (st : astate) : list (AsanCtrl.aptr * Z) :=
  map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (a_live st)).

(* [comment removed for export] *)
Definition VCB (a y : Z) : Z := VC0 + 2^19 * (2 * a + 1 - y).

Definition AI0 (Y : list (AsanCtrl.aptr * Z)) (s : APS) (mo : Model) : Prop :=
  (INV (aps_resv s) (aps_atop s) [] [] (aps_m s) mo
   /\ Permutation Y (live_pairs (aps_m s))
   /\ a_qloc_bytes (aps_m s) <= Q_CACHE /\ a_qglob_bytes (aps_m s) <= Q_MAX
   /\ minv (strip mo) /\ m_halted mo = None)
  /\ (FAINV (aps_m s) /\ Z.of_N (a_next (aps_m s)) <= NOPS
      /\ VC (aps_m s) <= VCB (Z.of_N (a_next (aps_m s))) (Z.of_nat (length Y))).   (* [comment removed for export] *)

Lemma AI0_perm : forall Y Y' s mo, Permutation Y Y' -> AI0 Y s mo -> AI0 Y' s mo.
Proof.
  intros Y Y' s mo HP [(H1 & H2 & H3) (H4 & H4' & H5)]. split; [| split; [exact H4| split; [exact H4'| rewrite <- (Permutation_length HP); exact H5]]].
  split; [exact H1|]. split; [|exact H3]. eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H2].
Qed.

Lemma AI0_so : forall Y s mo v, AI0 Y s mo -> AI0 Y (aset_so v s) mo.
Proof. intros Y [m so rv atp] mo v H. exact H. Qed.

Lemma AI0_model : forall Y s mo, AI0 Y s mo -> minvA mo /\ m_halted mo = None.
Proof. intros Y s mo [(HI & _ & _ & _ & Hmi & Hh) _]. split; [|exact Hh]. split; [exact Hmi|]. destruct HI as [_ (M1 & _)]. exact M1. Qed.

Lemma AI0_fds : forall Y s mo f, AI0 Y s mo -> minvA (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI0 Y s (with_fds f mo).
Proof.
  intros Y s mo f [(HI & HP & Hq1 & Hq2 & Hmi & Hh) HC] [Hmi' _] Hh'. unfold AI0. split; [| exact HC].
  split; [| repeat (split; [assumption|]); assumption].
  destruct HI as [HA HM]. split; [exact HA|]. apply AMI_with_fds. exact HM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FR (mo mo' : Model) : Prop :=
  (minv (strip mo) -> minv (strip mo')) /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo.

Lemma FR_refl : forall mo, FR mo mo. Proof. intros. unfold FR. split; [intros H; exact H|]. split; [reflexivity|]. split; reflexivity. Qed.
Lemma FR_trans : forall m1 m2 m3, FR m1 m2 -> FR m2 m3 -> FR m1 m3.
Proof. intros m1 m2 m3 (A1&A2&A3&A4) (B1&B2&B3&B4). unfold FR. split; [intros H; apply B1, A1, H|]. split; [congruence|]. split; congruence. Qed.

(* [comment removed for export] *)
Lemma FR_with_vmmaps_strip : forall mo mo' h, strip mo' = with_vmmaps h (strip mo) ->
  vm_init_sp h = vm_init_sp (m_vmmaps mo) ->
  m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> m_halted mo' = m_halted mo -> FR mo mo'.
Proof.
  intros mo mo' h Hs Hsp Hf Hfs Hh. unfold FR. split; [| split; [exact Hf| split; [exact Hfs| exact Hh]]].
  intros Hmi. rewrite Hs. eapply minv_vm_only; [apply vm_only_with_vmmaps; exact Hsp| exact Hmi].
Qed.

Lemma apost_FR : forall atop e mo z mo', apost atop e mo z mo' -> FR mo mo'.
Proof.
  intros atop e mo z mo' H. destruct e as [t|b|addr len prot flags|addr len|a l p|w]; cbn [AsanNodeSem.apost] in H; try contradiction.
  - destruct (addr =? 0).
    + destruct H as (_ & _ & _ & _ & ->). unfold grant_model. eapply FR_with_vmmaps_strip; try reflexivity.
    + destruct H as (_ & ->). unfold fixed_model. eapply (FR_with_vmmaps_strip _ _ (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)))).
      * rewrite strip_with_mmap_replacement. apply strip_with_vmmaps.
      * reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
  - destruct H as (_ & ->). unfold munmap_model. eapply FR_with_vmmaps_strip; try reflexivity.
Qed.

Lemma atotal_FR : forall atop {R} (t : AM R) mo (Post : R -> Model -> Prop),
  atot atop t mo Post -> atot atop t mo (fun r mo' => Post r mo' /\ FR mo mo').
Proof.
  intros atop R t. induction t as [r|e k IH]; intros mo Post H; cbn in *.
  - split; [exact H| apply FR_refl].
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp.
    eapply atotal_mono; [| apply IH; exact (Hk _ _ Hp)]. cbv beta. intros r mo'' [HP HF]. split; [exact HP|].
    eapply FR_trans; [apply (apost_FR _ _ _ _ _ Hp)| exact HF].
Qed.

(* [comment removed for export] *)
Lemma atotal_FR_gen : forall atop (ok : aev -> Model -> Prop) {R} (t : AM R) mo (Post : R -> Model -> Prop),
  atotal ok (apost atop) t mo Post -> atotal ok (apost atop) t mo (fun r mo' => Post r mo' /\ FR mo mo').
Proof.
  intros atop ok R t. induction t as [r|e k IH]; intros mo Post H; cbn in *.
  - split; [exact H| apply FR_refl].
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp.
    eapply atotal_mono; [| apply IH; exact (Hk _ _ Hp)]. cbv beta. intros r mo'' [HP HF]. split; [exact HP|].
    eapply FR_trans; [apply (apost_FR _ _ _ _ _ Hp)| exact HF].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sizes_live_pairs : forall st, map snd (live_pairs st) = sizes (live_chunks st).
Proof. intros. unfold live_pairs, sizes, live_chunks. rewrite !map_map. reflexivity. Qed.

Lemma HISTOK_perm : forall M M', Permutation M M' -> HISTOK M -> HISTOK M'.
Proof.
  intros M M' HP (I & Zl & H1 & H2 & H3 & H4 & H5). exists I, Zl. split; [|auto].
  eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H1].
Qed.

Theorem asan_ok_malloc0 : forall Y n s mo,
  AI0 Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  Z.of_N (a_next (aps_m s)) < NOPS ->                                     (* [comment removed for export] *)
  STOTA (amalloc_M n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AI0 ((q, n) :: Y) s' mo' /\ n < 2^63
                         /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                         /\ a_qloc_bytes (aps_m s') = a_qloc_bytes (aps_m s) /\ a_qglob_bytes (aps_m s') = a_qglob_bytes (aps_m s)
                         /\ a_next (aps_m s') = N.succ (a_next (aps_m s))).                 (* [comment removed for export] *)
Proof.
  intros Y n [st so RESV ATOP] mo HAI Hn HH HCNT. pose proof HAI as [(HI & HPY & Hq1 & Hq2 & Hmi & Hh) (HFA & HAN & HVC)]. cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  unfold amalloc_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR. apply (atot34_atot (SBc:=a_space_beg st) (PAc:=a_ptr_array st)). Local Ltac2 Set LiaHints.tbl := fun () => "00;0>19066050327.412424961824.27 37267553863.2338580939879.2442985050643.4147475614598.2850648877125.2957455133932.2962446044768.416720561796.29 6720987780.28 00000:00>00B00N00^00d00o01201>01B01FS2Hn5HnextS2HnS2HnS4HCNT3HVC1HS3HVC4HVC25HnextS2Hn1HS2Hn3AT12H0S1HS4HCNT5HnextS2HnS2n0".
apply (amalloc_core st mo n HI Hq1 Hq2 ltac:(unfold REQMAX in Hn; lia)).
    2:{ exact HFA. }
    2:{ unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length Y)). lia. }
    2:{ split; reflexivity. }
    intros mb ms.
    (* [comment removed for export] *)
    set (dummy := mkch n 70368744177664 (sec_map_size n)).
    assert (Hwf : chunk_wf ATOP dummy).
    { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
      - cbn. split; [|reflexivity]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
      - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)).
        unfold KHIGH. unfold REQMAX in Hn. repeat split; try lia. }
    apply (live_budget_list_sig dummy). { unfold dummy, mkch. destruct (is_primary n); reflexivity. }
    apply (live_budget_of_HISTOK (ATOP:=ATOP)).
    + constructor; [exact Hwf|]. destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW.
      apply Forall_app in HW as [HWl _]. exact HWl.
    + unfold sizes. cbn [map]. replace (chunk_size dummy) with n by (unfold dummy, mkch; destruct (is_primary n); reflexivity).
      fold (sizes (live_chunks st)). rewrite <- sizes_live_pairs. eapply HISTOK_perm; [|exact HH]. apply perm_skip. apply Permutation_map. exact HPY. }
  cbv beta. intros [st' op] s2 mo2 (-> & (ch & Hop & HI2 & Hlive & Hnone & Hsz & Eq1 & Eq2 & Eq3 & Eq4 & HFA2 & HVC2 & Hnext) & HFR). cbn [fst snd] in *.
  eapply STOT_bind; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  eapply STOT_mono; [apply STOT_ret|]. cbv beta. intros r s4 mo4 (-> & -> & ->).
  exists (a_next st). subst op. split; [reflexivity|]. destruct HFR as (F1 & F2 & F3 & F4).
  split; [| split; [unfold REQMAX in Hn; lia| repeat split; auto; cbn; auto]].
  unfold AI0. cbn [aps_m aset_m aps_so aps_atop aps_resv]. split; [| split; [exact HFA2| split]].
  2:{ rewrite Hnext, N2Z.inj_succ. lia. }
  2:{ (* [comment removed for export] *)
      cbn [length]. rewrite Hnext, N2Z.inj_succ, Nat2Z.inj_succ. unfold VCB in *. lia. }
  split; [exact HI2|]. split.
  - unfold live_pairs. rewrite Hlive.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
    cbn [map fst snd]. rewrite Hsz. apply perm_skip. exact HPY.
  - rewrite Eq1, Eq2. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_pairs_In : forall st p cap, In (p, cap) (live_pairs st) -> exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = cap.
Proof.
  intros st p cap H. unfold live_pairs in H. apply in_map_iff in H as ([k ch] & E & Hin). cbn in E. injection E as -> <-.
  exists ch. split; [|reflexivity]. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin.
Qed.

(* [comment removed for export] *)
Theorem aannotate_core : forall RESV ATOP SBc PAc st mo p cap old new ch,
  INV RESV ATOP [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  (a_live st) !! p = Some ch -> chunk_size ch = cap ->
  0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  FAINV st -> VC st <= VCMAX ->
  atotal (aok34 (ATOP:=ATOP) (SBc:=SBc) (PAc:=PAc)) (apost ATOP) (aannotate st p cap old new) mo (fun st' mo' => st' = st /\ INV RESV ATOP [] [] st mo').
Proof.
  intros RESV ATOP SBc PAc st mo p cap old new ch HI Hq1 Hq2 Hl Hsz Hold Hnew Hmin HFA HVC.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & _).
  assert (Hwf : chunk_wf ATOP ch).
  { unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HWl _]. unfold live_chunks in HWl.
    rewrite Forall_forall in HWl. apply HWl. apply in_map_iff. exists (p, ch). split; [reflexivity|].
    apply list_elem_of_In. apply elem_of_map_to_list. exact Hl. }
  Local Ltac2 Set LiaHints.tbl := fun () => "00N0>10157551586.2610161309472.3410599538806.4011483650719.2714448126601.2622183487811.2623026602635.4026677439224.4035164359060.3936001135701.3743231703787.294355129173.37 44137516179.3846150050660.2446150050660.2552673814101.3757454704725.3757457241406.3658427279801.4060091127893.3762247899221.3763175434673.2863368414764.3463368414893.3363370422393.2863370422634.3264590329382.3967774726214.2668359978886.389881053269.37 00000600<00D00L00R00X00k01P01U01Y01h01l01m02202702;02?02C02D02H02L02R02S02T02U02V02g02m02n032S4HoldS4HoldS3Hmb2R0S4Hcap1HS4HnewS4HnewS4Hnew2Hn2R22R03HabS4Hnew2Hn3Hmb6Hrange3Hne3Hlt2R22R02SGS3HCSS2HnS4Hmin3Hne4HrdnS2HnSS3HwfS3HwfS2HnS2HnS2HnFS2HnS2HnS4HcapSSSSS3Hq13Hq23Hb13Hb2S4HoldSS2Hn".
assert (Hcap : 0 <= cap <= 2^30) by (subst cap; destruct ch; cbn in Hwf |- *; lia).
  unfold aannotate. rewrite Hl.
  replace (negb ((0 <=? old) && (old <=? cap) && (0 <=? new) && (new <=? cap))) with false.
  2:{ symmetry. rewrite (proj2 (Z.leb_le 0 old)), (proj2 (Z.leb_le old cap)), (proj2 (Z.leb_le 0 new)), (proj2 (Z.leb_le new cap)) by lia. reflexivity. }
  destruct (Z.ltb_spec (2^40) cap); [lia|].
  destruct (Z.eqb_spec old new) as [|Hne]; [apply atotal_ret; auto|].
  assert (Hrdn : 0 <= rdn cap 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  replace (rdn cap 8 <? Z.min old new) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
  destruct (Z.ltb_spec old new) as [Hlt|]; [|apply atotal_ret; auto].
  destruct ch as [c n|mb ms n]; [apply atotal_ret; auto|]. cbv zeta. cbn [chunk_user_beg].
  pose proof (rdn_le old 8 ltac:(lia)) as R1. pose proof (rdn_le new 8 ltac:(lia)) as R2.
  assert (R0 : 0 <= rdn old 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  destruct (Z.ltb_spec (rdn old 8) (rdn new 8)) as [Hab|]; [|apply atotal_ret; auto].
  cbn in Hwf. destruct Hwf as (Hn & -> & Hal & Hmb & Hrange). cbn in Hsz. subst cap.
  pose proof (sec_map_size_ge n ltac:(lia)) as SG.
  assert (Hrz : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). rewrite Hrz. unfold PG.
  destruct (CH_bounds [] [] st HA) as [_ HCS].
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  { unfold zlen; cbn; lia. } { cbn; lia. }
  assert (HCS' : zsum2 (CH [] [] st) <= SECM) by (unfold SECM; lia).   (* [comment removed for export] *)
  apply (@poison0_ok RESV ATOP SBc PAc _ _ [] [] st _ mo); auto; try lia.
  all: try (destruct Hrange as [Hlo|[Hh1 Hh2]]; [left; lia| right; lia]).
  intros mo' HI'. apply atotal_ret. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Theorem asan_ok_annot0 : forall Y q cap old new s mo,
  AI0 Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  STOTA (aannot_M q cap old new s) mo
        (fun _ s' mo' => AI0 Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                         /\ a_qloc_bytes (aps_m s') = a_qloc_bytes (aps_m s) /\ a_qglob_bytes (aps_m s') = a_qglob_bytes (aps_m s)
                         /\ a_next (aps_m s') = a_next (aps_m s)).                                (* [comment removed for export] *)
Proof.
  intros Y q cap old new [st so RESV ATOP] mo HAI Hin Hold Hnew Hmin. pose proof HAI as [(HI & HPY & Hq1 & Hq2 & Hmi & Hh) HC]. cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, cap) (live_pairs st)) by (eapply Permutation_in; [exact HPY| exact Hin]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  unfold aannot_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR.
    apply (atot34_atot (SBc:=a_space_beg st) (PAc:=a_ptr_array st)). pose proof HC as (HFA & HAN & HVC).
    apply (aannotate_core RESV ATOP _ _ st mo q cap old new ch HI Hq1 Hq2 Hl Hsz Hold Hnew Hmin HFA).
    unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length Y)). Local Ltac2 Set LiaHints.tbl := fun () => "0010>37577552803.3300000;S3HAN3HVC1H".
lia. }
  cbv beta. intros st' s2 mo2 (-> & [-> HI2] & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| repeat split; auto; cbn; auto].
  unfold AI0. cbn [aps_m aset_m aps_atop aps_resv]. split; [| exact HC].
  split; [exact HI2|]. split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition qsum (Y : list (AsanCtrl.aptr * Z)) : Z := fold_right (fun qn acc => Z.max 0 (snd qn) + 8192 + acc) 0 Y.

Lemma qsum_nonneg : forall Y, 0 <= qsum Y.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=11520766495.439280637297.0000004005S2IHS".
induction Y as [|[q n] Y IH]; cbn [qsum fold_right snd]; [lia|]. fold (qsum Y). lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma qsum_cons : forall q n Y, qsum ((q, n) :: Y) = Z.max 0 n + 8192 + qsum Y.
Proof. reflexivity. Qed.
Lemma qsum_perm : forall Y Y', Permutation Y Y' -> qsum Y = qsum Y'.
Proof.
  intros Y Y' HP. induction HP as [|[q n] l l' HP IH|[q n] [q' n'] l|l l' l'' HP1 IH1 HP2 IH2].
  - reflexivity.
  - rewrite !qsum_cons, IH. reflexivity.
  - rewrite !qsum_cons. Local Ltac2 Set LiaHints.tbl := fun () => "0010=41120516190.5000001S".
lia.
  - congruence.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition qbytes (s : APS) : Z := a_qloc_bytes (aps_m s) + a_qglob_bytes (aps_m s).

Theorem asan_ok_free0 : forall Y q n s mo,
  AI0 ((q, n) :: Y) s mo -> qbytes s + qsum ((q, n) :: Y) <= Q_MAX ->
  STOTA (afree_M q s) mo
        (fun _ s' mo' => AI0 Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                         /\ qbytes s' + qsum Y <= qbytes s + qsum ((q, n) :: Y)
                         /\ a_next (aps_m s') = a_next (aps_m s)).                                (* [comment removed for export] *)
Proof.
  intros Y q n [st so RESV ATOP] mo HAI HQ. pose proof HAI as [(HI & HPY & Hq1 & Hq2 & Hmi & Hh) (HFA & HAN & HVC)]. unfold qbytes in *. cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  pose proof (INV_qbytes_nonneg st mo HI) as [Hl0 Hg0]. pose proof (qsum_nonneg Y) as HY0. rewrite qsum_cons in HQ.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>34896978004.2938580939879.3142985050643.4457064599224.4400000800C00S00_S2HQ3HY0S3HAN3HVC1HS3HVC5Hnext4HVC2S5Hnext4HSUM".
assert (HG : a_qloc_bytes st + a_qglob_bytes st + chunk_size ch + Q_BATCH_BYTES <= Q_MAX) by (rewrite Hsz; unfold Q_BATCH_BYTES; lia).
  unfold afree_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  (* [comment removed for export] *)
  replace (qb_ok (aps_m (mkAPS st so RESV ATOP)) q) with true.
  2:{ symmetry. unfold qb_ok. cbn [aps_m]. rewrite Hl.
      rewrite (proj2 (Z.leb_le 0 _) Hl0), (proj2 (Z.leb_le 0 _) Hg0), (proj2 (Z.leb_le _ _) HG). reflexivity. }
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR.
    apply (atot34_atot (SBc:=a_space_beg st) (PAc:=a_ptr_array st)).
    apply (afree_core_g st mo q ch HI Hq1 Hq2 Hl HG HFA); [| split; reflexivity].
    unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length ((q, n) :: Y))). lia. }
  cbv beta. intros st' s2 mo2 (-> & ((HI2 & Hlive & Hnext & Hq1' & Hq2' & HFA2 & HVC2) & HSUM) & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| split; [reflexivity| split; [exact F2| split; [exact F3| split; [| cbn [aps_m aset_m]; exact Hnext]]]]].
  - unfold AI0. cbn [aps_m aset_m aps_atop aps_resv].
    split; [| split; [exact HFA2| split; [rewrite Hnext; exact HAN| rewrite Hnext; cbn [length] in HVC; unfold VCB in *; lia]]].
    split; [exact HI2|]. split.
    + unfold live_pairs. rewrite Hlive. eapply (Permutation_cons_inv (a := (q, n))).
      eapply Permutation_trans; [exact HPY|]. unfold live_pairs. rewrite <- Hsz.
      change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
        with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
      apply Permutation_map. apply Permutation_sym. apply map_to_list_delete. exact Hl.
    + split; [exact Hq1'|]. split; [exact Hq2'|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
  - cbn [aps_m aset_m]. rewrite qsum_cons. rewrite Hsz in HSUM. unfold Q_BATCH_BYTES in HSUM. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mat_with_fds : forall x m, m_vm_materialized (with_fds x m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma halted_with_fds : forall x m, m_halted (with_fds x m) = m_halted m. Proof. reflexivity. Qed.
Lemma mat_with_tid : forall x m, m_vm_materialized (with_tid x m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma halted_with_tid : forall x m, m_halted (with_tid x m) = m_halted m. Proof. reflexivity. Qed.

Lemma nstep_close_strip : forall fd m eff mo' evs,
  nstep (NClose fd) m eff mo' evs -> nstep (NClose fd) (strip m) eff (strip mo') evs /\ (mo' = m \/ exists x, mo' = with_fds x m).
Proof.
  intros fd m eff mo' evs Hn. cbn [nstep] in Hn |- *. rewrite m_fds_strip. destruct Hn as (He & Hr & H).
  destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)).
  - destruct H as [Heff ->]. rewrite strip_with_fds. split; [| right; eexists; reflexivity]. auto.
  - destruct H as [Heff ->]. split; [| left; reflexivity]. auto.
Qed.

Theorem asan_ok_MI2 : forall n mo rsp mo' evs,
  nstep n mo rsp mo' evs -> io_node n -> minvA mo -> m_halted mo = None -> minvA mo' /\ m_halted mo' = None.
Proof.
  intros n mo rsp mo' evs Hst Hio [Hmi Hmat] Hh.
  assert (Hsh : m_halted (strip mo) = None) by (rewrite m_halted_strip; exact Hh).
  destruct n as [fd bs|fd bufs|path|fd buf count|fd|fd req| |code|req|a l p f|a l|a l p]; cbn [io_node] in Hio; try contradiction.
  - destruct Hst as (k & _ & _ & -> & _). split; [split|]; assumption.
  - destruct Hst as [-> _]. split; [split|]; assumption.
  - pose proof (minv_preserved _ _ _ _ _ Hmi Hsh (nstep_open_strip _ _ _ _ _ Hst)) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct (nstep_open_shape _ _ _ _ _ Hst) as [-> | (x & ->)]; [exact Hmat| rewrite mat_with_fds; exact Hmat].
  - pose proof (minv_preserved _ _ _ _ _ Hmi Hsh (nstep_read_strip _ _ _ _ _ _ _ Hst)) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct (nstep_read_shape _ _ _ _ _ _ _ Hst) as [(E & _) | (x & ->)]; [rewrite E; exact Hmat| rewrite mat_with_fds; exact Hmat].
  - destruct (nstep_close_strip _ _ _ _ _ Hst) as [Hs Hsh2].
    pose proof (minv_preserved _ _ _ _ _ Hmi Hsh Hs) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct Hsh2 as [-> | (x & ->)]; [exact Hmat| rewrite mat_with_fds; exact Hmat].
  - destruct Hst as (_ & _ & ->). split; [split|]; assumption.
  - destruct Hst as (_ & t & _ & H). destruct (m_tid mo); destruct H as [_ ->]; [split; [split|]; assumption|].
    split; [split; [rewrite strip_with_tid; exact Hmi| rewrite mat_with_tid; exact Hmat]| rewrite halted_with_tid; exact Hh].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PhiA : node -> Model -> Prop := fun _ _ => True.

Lemma nstepA_sub : forall n mo r mo' e, ~ nf_node n -> nstepA n mo r mo' e -> nstep n mo r mo' e.
Proof. intros n mo r mo' e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstepA n mo r mo e.
Proof. intros n mo r e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_io : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstepA n mo r mo' e.
Proof. intros n mo r mo' e Hio H; destruct n; cbn [io_node] in Hio; try contradiction; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AI (v : Z) (Y : list (AsanCtrl.aptr * Z)) (s : APS) (mo : Model) : Prop :=
  AI0 Y s mo /\ 0 <= v /\ qbytes s + qsum Y + v <= Q_MAX
  /\ Z.of_N (a_next (aps_m s)) + v / OPCOST <= NOPS.

Lemma OPCOST_pos : 0 < OPCOST. Proof. unfold OPCOST. Local Ltac2 Set LiaHints.tbl := fun () => "0010=55588686165.0000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma opc_mono : forall v v', v' <= v -> v' / OPCOST <= v / OPCOST.
Proof. intros v v' H. apply Z.div_le_mono; [exact OPCOST_pos| exact H]. Qed.
Lemma opc_nonneg : forall v, 0 <= v -> 0 <= v / OPCOST.
Proof. intros v H. apply Z.div_pos; [exact H| exact OPCOST_pos]. Qed.
(* [comment removed for export] *)
Lemma opc_pay : forall v n, FCOST n <= v -> 0 <= n -> (v - FCOST n) / OPCOST <= v / OPCOST - 1.
Proof.
  intros v n Hv Hn. apply (Z.le_trans _ ((v - OPCOST) / OPCOST)).
  - apply opc_mono. unfold FCOST, OPCOST in *. Local Ltac2 Set LiaHints.tbl := fun () => "0040=18713715309.424887067997.435565800962.552248058902.4000001005008009SS2HnS1HS".
lia.
  - replace (v - OPCOST) with (v + (-1) * OPCOST) by lia. rewrite Z.div_add by (pose proof OPCOST_pos; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma opc_one : forall v n, FCOST n <= v -> 0 <= n -> 1 <= v / OPCOST.
Proof. intros v n Hv Hn. pose proof (opc_pay v n Hv Hn). Local Ltac2 Set LiaHints.tbl := fun () => "0020=2408916121.6 30248970193.500000600:S1H2H0S2Hv".
pose proof (opc_nonneg (v - FCOST n) ltac:(lia)). lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma AI_perm : forall v Y Y' s mo, Permutation Y Y' -> AI v Y s mo -> AI v Y' s mo.
Proof. intros v Y Y' s mo HP (H0 & Hv & HQ & HC). split; [eapply AI0_perm; eauto|]. split; [exact Hv|]. rewrite <- (qsum_perm _ _ HP). split; [exact HQ| exact HC]. Qed.
Lemma AI_credit : forall v v' Y s mo, 0 <= v' <= v -> AI v Y s mo -> AI v' Y s mo.
Proof. intros v v' Y s mo Hv' (H0 & Hv & HQ & HC). split; [exact H0|]. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1343833610.10 23206693907.1124474174547.1137701183947.1100000500;00C00HS3Hv'S2HC1HS3Hv'2HQS3Hv'".
pose proof (opc_mono v v' ltac:(lia)). split; [lia|]. split; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma AI_so : forall v Y s mo w, AI v Y s mo -> AI v Y (aset_so w s) mo.
Proof. intros v Y s mo w (H0 & Hv & HQ & HC). split; [apply AI0_so; exact H0|]. split; [exact Hv|]. destruct s; split; [exact HQ| exact HC]. Qed.
Lemma AI_model : forall v Y s mo, AI v Y s mo -> minvA mo /\ m_halted mo = None.
Proof. intros v Y s mo (H0 & _). exact (AI0_model _ _ _ H0). Qed.
Lemma AI_fds : forall v Y s mo f, AI v Y s mo -> minvA (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI v Y s (with_fds f mo).
Proof. intros v Y s mo f (H0 & Hv & HQ & HC) M Hh. split; [apply AI0_fds; assumption|]. split; [exact Hv|]. split; assumption. Qed.

Lemma MAIN_QCOST_ok : 0 <= MAIN_QCOST <= Q_MAX.
Proof. unfold MAIN_QCOST, READ_QCOST, RUN_QCOST, FUZZ_QCOST, FCOST, OPCOST, Driver.MAX_INPUT, Harness.PRODUCER_SIZE, Harness.BUFF_MAX, Q_MAX. Local Ltac2 Set LiaHints.tbl := fun () => "0010=37810248526.0000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
Lemma MAIN_QCOST_ops : MAIN_QCOST / OPCOST <= NOPS.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma AI_of_AI0 : forall v s mo, AI0 [] s mo -> a_qloc_bytes (aps_m s) = 0 -> a_qglob_bytes (aps_m s) = 0 ->
  a_next (aps_m s) = 0%N -> 0 <= v <= MAIN_QCOST -> AI v [] s mo.
Proof.
  intros v s mo H0 E1 E2 E3 Hv. pose proof MAIN_QCOST_ok. pose proof MAIN_QCOST_ops. Local Ltac2 Set LiaHints.tbl := fun () => "0030>38210790577.1148659781173.1054240447258.1100000?00C00GS2E32Hv1H2H12H2S2HvS2Hv".
pose proof (opc_mono MAIN_QCOST v ltac:(lia)).
  split; [exact H0|]. split; [lia|]. unfold qbytes. rewrite E1, E2, E3. cbn [qsum fold_right Z.of_N]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Theorem asan_ok_malloc : forall v Y n s mo,
  AI v Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) -> FCOST n <= v ->
  STOTA (amalloc_M n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AI (v - FCOST n) ((q, n) :: Y) s' mo' /\ n < 2^63
                         /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros v Y n s mo (H0 & Hv & HQ & HC) Hn HH Hc.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060>2424957760.13 2424959413.12 43731489591.2553887418442.2562445880807.146437948536.25 00000400800E00R00Y00cS2HnS2HnS2HQ2Hn5HnextS2HC2HP5HnextS2HC2H1S2Hc5Hnext".
pose proof (opc_pay v n Hc ltac:(lia)) as HP. pose proof (opc_one v n Hc ltac:(lia)) as H1.
  eapply STOT_mono; [apply (asan_ok_malloc0 Y n s mo H0 Hn HH ltac:(lia))|]. cbv beta.
  intros r s' mo' (q & -> & H0' & Hn63 & Hso & Hfd & Hfs & E1 & E2 & Hnext). exists q. split; [reflexivity|].
  split; [| auto]. split; [exact H0'|]. split; [unfold FCOST, OPCOST in *; lia|]. unfold qbytes in *. rewrite E1, E2, qsum_cons, Hnext, N2Z.inj_succ.
  split; [unfold FCOST, OPCOST in *; lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Theorem asan_ok_free : forall v Y q n s mo,
  AI v ((q, n) :: Y) s mo ->
  STOTA (afree_M q s) mo
        (fun _ s' mo' => AI v Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros v Y q n s mo (H0 & Hv & HQ & HC).
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>16749212396.1856409936864.1000000=00DS2HQ2HS5HnextS2Hv2HQ".
eapply STOT_mono; [apply (asan_ok_free0 Y q n s mo H0 ltac:(lia))|]. cbv beta.
  intros [] s' mo' (H0' & Hso & Hfd & Hfs & HS & Hnext). split; [| auto].
  split; [exact H0'|]. split; [exact Hv|]. split; [lia| rewrite Hnext; exact HC].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Theorem asan_ok_annot : forall v Y q cap old new s mo,
  AI v Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  STOTA (aannot_M q cap old new s) mo
        (fun _ s' mo' => AI v Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros v Y q cap old new s mo (H0 & Hv & HQ & HC) Hin Ho Hn Hz.
  eapply STOT_mono; [apply (asan_ok_annot0 Y q cap old new s mo H0 Hin Ho Hn Hz)|]. cbv beta.
  intros [] s' mo' (H0' & Hso & Hfd & Hfs & E1 & E2 & Hnext). split; [| auto]. split; [exact H0'|]. split; [exact Hv|]. unfold qbytes in *. rewrite E1, E2, Hnext.
  split; [exact HQ| exact HC].
Qed.

Definition AAllocAsanOK : AAllocOK AAllocAsan nstepA PhiA minvA :=
  mkAAllocOK AAllocAsan nstepA PhiA minvA nstepA_sub nstepA_same nstepA_io asan_ok_MI2
    aps_get_set aps_set_set aps_set_get aps_addr_so
    AI AI_perm AI_credit AI_so AI_model AI_fds
    (fun v Y n s mo HA Hn HH Hc _ => asan_ok_malloc v Y n s mo HA Hn HH Hc)
    (fun v Y q n s mo HA _ => asan_ok_free v Y q n s mo HA)
    (fun v Y q cap old new s mo HA Hin Ho Hn Hz _ => asan_ok_annot v Y q cap old new s mo HA Hin Ho Hn Hz).

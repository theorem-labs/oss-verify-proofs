(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP
     AKitQ AMalloc_iface ADepot_iface ASec ASecFacts ASecFrame ASecModel AModelFacts APrimFacts F_amalloc_arep ARepExt.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma sec_chunk_in_ranges : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (asec_ranges st).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  unfold asec_ranges. apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

#[using="Type"] Lemma avoids_all_In : forall a n l iv, avoids_all a n l = true -> In iv l -> a + n <= fst iv \/ snd iv <= a.
Proof.
  intros a n l iv H Hin. unfold avoids_all in H. rewrite forallb_forall in H. specialize (H iv Hin).
  unfold iv_clear in H. apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma asec_wf_all : forall L st cs ch, asec_wf L st cs -> In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st cs ch (_ & _ & _ & _ & _ & WF1 & _) Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1.
  destruct ch as [c n|mb ms n]; [destruct W1|]. exists mb, ms, n. split; [reflexivity| exact W1].
Qed.

Section Valid.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (n a : Z).
Let ms := sec_map_size n.
Hypothesis ALO : alayout_ok L.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis FR : sfresh RESV st n a = true.
Hypothesis ROK : aresv_ok L RESV.

#[using="L RESV st N PRIM FR ROK"] Lemma valid_geo : a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP /\ 0 < ms /\ ms = sec_map_size n.
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & POS & AL & TOPB & _).   (* [comment removed for export] *)
  pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSB).
  destruct ROK as (R1 & R2 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=50850525385.053840268713.96644513770.2 00000100E00JSS3POS4TOPB3MSB2C12C2S3MSB".
pose proof (pcov_clear _ _ _ _ _ R1 AV ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -MSB; lia)) as C1.   (* [comment removed for export] *)
  pose proof (pcov_clear _ _ _ _ _ R2 AV ltac:(clear; lia) ltac:(clear -MSB; lia)) as C2.                    (* [comment removed for export] *)
  subst ms. split; [exact AL|]. split; [| split; [exact TOPB| split; [clear -MSB; lia| reflexivity]]].
  unfold ablk, KLS. unfold AIMG_HI in *. clear -C1 C2 POS TOPB MSB. lia.   (* [comment removed for export] *)
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc RESV st N PRIM FR ROK"] Lemma valid_hulls : Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & _ & _ & _ & _).   (* [comment removed for export] *)
  pose proof valid_geo as (_ & _ & _ & MSP & _).
  destruct ROK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  unfold astartup_hulls. fold (al_res L) in R3. change (4096 * al_V L 323%nat) with (al_dtls L) in R10.
  repeat (apply Forall_cons; [cbn [fst snd]; eapply pcov_clear; [eassumption| exact AV| clear; lia| exact MSP] |]). apply Forall_nil.
Qed.

#[using="rc RESV st N PRIM FR ROK"] Lemma valid_clear : sec_clear L a ms.
Proof.
  pose proof valid_hulls as H. unfold astartup_hulls in H.
  repeat lazymatch type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] | _ => idtac end.
  cbn [fst snd] in *. unfold sec_clear. Local Ltac2 Set LiaHints.tbl := fun () => "0010>39499910128.2600000JS2H82H72H93H122H32H22H42H5".
repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc L RESV N PRIM FR ROK"] Lemma valid_chunks : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) (sec_chunks_of st).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & _ & AV & _ & _ & _ & _).   (* [comment removed for export] *)
  apply Forall_forall. intros ch Hin. destruct ch as [c k|mb ms' k]; cbn [sec_mb sec_ms].
  - pose proof valid_geo as (_ & G & _). pose proof (ablk_lin _ _ G) as (_ & G0 & _). right. clear -G0. Local Ltac2 Set LiaHints.tbl := fun () => "0010=58669667472.2000004S2G0".
lia.   (* [comment removed for export] *)
  - pose proof (avoids_all_In _ _ _ _ AV (sec_chunk_in_ranges st mb ms' k Hin)) as D. cbn [fst snd] in D. exact D.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="RESV st N PRIM FR ROK"] Lemma valid_wf1 : sec_wf1 L (CSec a ms n).
Proof.
  pose proof valid_geo as (G1 & G2 & G3 & G4 & G5). pose proof (sec_facts n N PRIM) as (NB & _).
  cbn [sec_wf1]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G5|].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=6414719921.19000006S1N2NB".
split; [lia|]. split; [exact PRIM| exact valid_clear].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Valid.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma wview_some : forall m (x : word) b, m x = Some b -> wview bsegs m x = Some b.
Proof. intros m x b H. unfold wview. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma ashz_azero : forall L cs m a ms,
  ashz L cs m ->
  a mod 8 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= ms ->
  Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L) ->
  Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs ->
  azero m (shad a) (ms / 8).
Proof.
  intros L cs m a ms SHZ A8 ALO AHI MS0 HH HC.
  assert (PT : forall i, 0 <= i < ms / 8 -> m (wa (shad a + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0070>13415109785.1626294862582.7 34303992433.7 34303993199.7 35924352844.3 3901711215.16 53299215280.8 00000400=00E00M00Q00U00dS2SRS3AHI3AL2S2Hi3HivS2Hi3HchS2A8S2SRS2A83ALO3AHI2Hi".
replace (shad a + i) with (shad (a + 8 * i)) by (rewrite !shad_div; clear -A8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    apply SHZ.
    - unfold ablk, KLS, K_HIGH_MEM in *. unfold AIMG_HI in *. clear -Hi ALO AHI A8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.   (* [comment removed for export] *)
    - eapply Forall_impl; [| exact HH]. cbn beta. intros iv Hiv. clear -Hi Hiv A8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - eapply Forall_impl; [| exact HC]. cbn beta. intros ch Hch. clear -Hi Hch A8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (SR : 0 <= shad a /\ shad a + ms / 8 <= 2^64).
  { pose proof (ablk_lin _ _ ALO) as (AL1 & AL2 & AL3 & AL4). rewrite shad_div. unfold ASHOFF in *. clear -AL2 AL4 AHI MS0. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }   (* [comment removed for export] *)
  split; [exact PT|]. split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_some _ _ _ (PT i Hi)). discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_insert_sec : forall st st' p mb ms n,
  (a_live st) !! p = None ->
  a_live st' = <[p := CSec mb ms n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  Permutation (sec_chunks_of st') (CSec mb ms n :: sec_chunks_of st).
Proof.
  intros st st' p mb ms n NONE E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
  apply Permutation_app_tail.
  pose proof (map_to_list_insert (a_live st) p (CSec mb ms n) NONE) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_trans; [apply filter_is_sec_perm; exact P|]. cbn. apply Permutation_refl.
Qed.

#[using="Type"] Lemma awf_fresh_none : forall L st X, awf L st X -> (a_live st) !! (a_next st) = None.
Proof.
  intros L st X WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59314971621.2000003S1F".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma awf_sec : forall L st X nres' a ms n, awf L st X -> awf L (st_sec st nres' a ms n) X.
Proof.
  intros L st X nres' a ms n WF.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  unfold awf. rewrite E1, E2, E7, E8.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. rewrite get_cls_st_sec, max_count_st_sec. unfold ndist. rewrite get_cls_st_sec. exact (PERC c Hc). }
  split. { intros c Hc. rewrite get_cls_st_sec. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CLB M]. split; [exact CLB|]. destruct (xb_st b) as [p| |]; try exact M.
           destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat (split; [assumption|]).
           rewrite lookup_insert_ne; [exact M6|]. intros E. assert (X0 : a_live st !! p = None) by (rewrite <- E; exact NONE). rewrite X0 in M6. discriminate. }
  split. { intros p c k Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
           - rewrite lookup_insert_eq in Hp. discriminate.
           - rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact (LIVE p c k Hp). }
  split. { intros p ch Hp. Local Ltac2 Set LiaHints.tbl := fun () => "0020>30151628886.3640501545124.3900000400:S2E8S2E81H".
destruct (N.eq_dec p (a_next st)) as [->|NE]; [lia|].
           rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). pose proof (FRESH p ch Hp). lia. }
  exact UNIQ.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma ablocks_sec : forall L st X LB nres' a ms n,
  awf L st X -> ablocks L st X LB -> sec_wf1 L (CSec a ms n) ->
  ablocks L (st_sec st nres' a ms n) X (HB (a_next st) (a + SEC_UOFF) n :: LB).
Proof.
  intros L st X LB nres' a ms n WF (BH & BF & NDI & NDL) W1.
  pose proof (awf_fresh_none L st X WF) as NONE.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & E7 & _).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms' & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. right. exists a, ms. rewrite E7, lookup_insert_eq. split; [reflexivity|]. split; [reflexivity| exact W1].
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms' & Lp & R)].
      * left. exists b. split; [exact Hb| exact R].
      * right. exists mb, ms'. split; [| exact R]. rewrite E7, lookup_insert_ne; [exact Lp|].
        intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59314971621.2000003S1F".
lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hp).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma arng_sec : forall L RNG RNG' st X nres' a ms n,
  awf L st X -> arng L RNG st -> fp_le RNG RNG' ->
  rng RNG' a ms -> rng RNG' (shad a) (ms / 8) -> rng RNG' (al_ptr_array L) (8 * nres') ->
  arng L RNG' (st_sec st nres' a ms n).
Proof.
  intros L RNG RNG' st X nres' a ms n WF AR LE R1 R2 R3.
  pose proof (arng_mono L RNG RNG' st LE AR) as (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & E3 & _ & _ & _ & E7 & _ & E9 & _ & E11 & _).
  unfold arng. rewrite E3. repeat (split; [assumption|]). split; [| exact A10].
  eapply RSEC_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [eapply awf_fresh_none; exact WF| exact E7| exact E9| exact E11]|].
  constructor; [| exact A9]. cbn [sec_mb sec_ms]. split; [exact R1| exact R2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Proof.
  intros cs cs' L st X m P (WFS & ARR & INST & PZ & SHZ).
  split; [| split; [| split; [exact INST| split; [exact PZ|]]]].
  - destruct WFS as (ALO & WP & WR & WL & WB & WF1 & WD). unfold asec_wf.
    split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [rewrite <- (Permutation_length P); exact WL|]. split; [exact WB|].
    split; [| eapply sec_disjoint_perm; [exact P| exact WD]].
    rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
  - destruct ARR as (order & PO & U64 & JK & PER). exists order. split; [eapply Permutation_trans; [exact PO| exact P]|].
    split; [exact U64| split; [exact JK| exact PER]].
  - intros x Hx HF HC. apply (SHZ x Hx HF). rewrite Forall_forall in HC |- *. intros ch Hin. apply HC.
    eapply Permutation_in; [exact P| exact Hin].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma asec_chunk_frameW : forall L W m m' mb ms n idx lv,
  munch W m m' -> wmono bsegs m m' ->
  sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WM WF1 DC DS CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "00I0>11624291152.8 15653492877.8 1785468914.7  18107032235.4 21842504200.8 22014303259.8 22096821547.5 24963147917.6 28989849047.5 29293361451.7 33671246594.7 34438769839.8 34737325243.8 35864023691.6 40397452967.6 40799456635.2 4650438331.8  48175602055.6 51613910273.2352392744836.8 59335169898.8 66028962729.8 6644414584.5  66500705481.5 9937142902.9  00000@00P00`00a00b01201;01<01A01B01C01S01T01U01Z01^01_01d01h01i01j02:02?02@02WS2G53RSR3NSE3MSRS2G53RSR3NSE3MSRS2G53RSR3NSE3MSRSSS2G53RSR3NSE3MSRS3GR13GR3SS3POSSSS2G53RSR3NSE3MSRSSS3GR1S2G5SS3GR3S2G5SSS2G53RSR3NSE3MSRS3GRPSS2G12G53RSR3NSE3MSR3MSM".
pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma junk_zero_len : forall m A n, junk_at m A n -> n <= 0 -> forall m', junk_at m' A n.
Proof.
  intros m A n [bs H] Hn m'. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  Local Ltac2 Set LiaHints.tbl := fun () => "0070>1312006957.14 14229629860.1620742173918.1624931663515.1440669959007.1459648026050.1468686216788.1600000600?00H00Q00Z00c00oS1L2W1S2Hn1L2W1S1L2W12HiS1L2B02W1S2Hn1L2W1S2Hn1L2W1S2Hn1L2W12Hi".
assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
  split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section Append.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Variables (st : astate) (X : aconc) (nres' a n id : Z).
Let ms := sec_map_size n.
Let cs := sec_chunks_of st.
Let nsec := a_nsec st.
Let nres := a_nres st.
Let PA := al_ptr_array L.
Let UB := a + 6144.
Hypothesis WF : awf L st X.
Hypothesis SEC : ASECc cs L st X m.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis W1 : sec_wf1 L (CSec a ms n).
Hypothesis DJ : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs.
Hypothesis NR' : (nsec <> nres /\ nres' = nres)
              \/ (nsec = nres /\ nres' = nres + 16384
                  /\ rw_cells bsegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]).
Hypothesis NRB : nres' <= 1048576.
(* [comment removed for export] *)
Hypothesis Wch : forall ch, In ch cs ->
     (forall A k, sec_mb ch <= A -> A + k <= sec_mb ch + sec_ms ch -> 0 < k -> disjoint_from W A k)
  /\ (forall A k, shad (sec_mb ch) <= A -> A + k <= shad (sec_mb ch) + sec_ms ch / 8 -> 0 < k -> disjoint_from W A k).
Hypothesis Wpa : 0 < nsec -> disjoint_from W PA (8 * nsec).
Hypothesis Wpj : nsec + 1 < nres -> disjoint_from W (PA + 8 * nsec + 8) (8 * (nres - nsec - 1)).
Hypothesis Wbase : disjoint_from W (AINSTANCE + 80) 8.
Hypothesis Wp0 : disjoint_from W (shad (al_space_beg L)) (shlen K_REGION).
Hypothesis Wshz : forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) -> (x < a \/ a + ms <= x) -> disjoint_from W (shad x) 1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis C_srt : rw_cells bsegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)].
Hypothesis C_jst : junk_at m' (AINSTANCE + 136) 32.
Hypothesis C_jbs : junk_at m' (AINSTANCE + 168) 512.
Hypothesis C_mtx : rw_cells bsegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Hypothesis C_jgl : junk_at m' (AINSTANCE + 704) 16.
Hypothesis C_slot : rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].
Hypothesis C_hdr : rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)].
Hypothesis C_pgj : junk_at m' (a + 32) (4096 - 32).
Hypothesis C_mag : rw_cells bsegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))].
Hypothesis C_lcj : junk_at m' (a + 4096 + 16) (2048 - 32).
Hypothesis C_ahd : rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Hypothesis IDR : 0 < id < 2^31.
Hypothesis C_usr : junk_at m' UB (ms - 6144).
Hypothesis C_shf : fill_at m' (shad a) 768 0xfa.
Hypothesis C_shu : rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Hypothesis C_sht : fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa.

#[using="rc L id nres PA UB C_hdr C_pgj C_mag C_lcj C_ahd IDR C_usr C_shf C_shu C_sht"] Lemma asec_chunk_new : asec_chunk m' (CSec a ms n) nsec true.
Proof.
  cbn [asec_chunk]. unfold SEC_UOFF, SEC_MAGIC. fold UB.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>12595520980.4962848447571.5066571356122.50000001002007SSS3IDR".
replace (UB - 16) with (UB + -16) by (subst UB; lia).
  split; [exact C_hdr|]. split; [exact C_pgj|]. split; [exact C_mag|]. split; [exact C_lcj|].
  split. { exists 17, id. split; [exact C_ahd|]. split; [lia|]. split; [reflexivity| lia]. }
  split; [unfold SEC_UOFF; exact C_usr|]. split; [exact C_shf|]. split; [| exact C_sht].
  unfold sec_user_shadow. exact C_shu.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="W m MU WM id cs nsec nres PA UB WF SEC N PRIM W1 DJ NR' NRB Wch Wpa Wpj Wbase Wp0 Wshz C_srt C_jst C_jbs C_mtx C_jgl C_slot C_hdr C_pgj C_mag C_lcj C_ahd IDR C_usr C_shf C_shu C_sht"] Theorem asec_append : ASEC_of L (st_sec st nres' a ms n) X m'.
Proof.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  destruct SEC as (WFS & ARR & INST & PZ & SHZ).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof W1 as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. fold PA in OP.
  assert (NEWNOT : ~ In (CSec a ms n) cs).
  { intros Hin. pose proof (proj1 (Forall_forall _ _) DJ _ Hin) as D. cbn [sec_mb sec_ms] in D. clear -D MSB. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11465153921.9612478326483.4 21550530669.3 21550530669.4 26729587044.6 29071375129.4 30900958236.3 32832983353.1 33158473233.2 35538096198.4 36172690305.5 38302138503.4 39332637397.0 4209879811.3  42763184905.5 47803412682.3 49459273621.6 54046652698.5 56952125693.3 57423469579.4 59314938599.5 65253966880.1 66281486796.3 8722090879.8  9373699592.5  9494891502.5  00000400=00>00?00L00Q00R00S00X00]00a00h00i00j00m01101601901@01D01K01L01P01U01[01eS2E8S3NS03NS1SSS3NRB3NS03NS1S3LENSSS3WRMS3LENS2OPS2EK2GESSS1DS2HxS3LENS1DS2WB2A1S2GES3MSB1DSS2WLS3HCnS2OP1HS2WB2A12A2".
lia. }
  assert (NSR : 0 <= nsec /\ nsec + 1 <= nres' /\ (nres' = nres \/ nres' = nres + 16384)).
  { subst nsec nres. destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia. }
  destruct NSR as (NS0 & NS1 & NS2).
  unfold ASEC_of. eapply ASECc_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [exact NONE| exact E7| exact E9| exact E11]|].
  fold cs. split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    unfold asec_wf. rewrite E2, E3, E4. split; [exact ALO|]. split; [exact WP|].
    split. { split; [| clear -NRB NS0 NS1; lia]. destruct WR as [WRM _]. destruct NS2 as [-> | ->]; [exact WRM|].
             subst nres. clear -WRM. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    split; [cbn [length]; subst nsec; clear -WL; lia|]. split; [clear -NS0 NS1; subst nsec; lia|].
    split; [constructor; [exact W1| exact WF1]|].
    destruct WD as [ND PW]. split; [constructor; [exact NEWNOT| exact ND]|].
    intros ci cj [<-|Hi] [<-|Hj] NE; [exfalso; exact (NE eq_refl)| | |].
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hj) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hi) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + exact (PW ci cj Hi Hj NE).
  - (* [comment removed for export] *)
    destruct ARR as (order & PO & U64 & JK & PER). unfold asec_arr. rewrite E3, E4. fold PA. fold nsec.
    assert (LEN : Z.of_nat (length order) = nsec) by (rewrite (Permutation_length PO); exact WL).
    exists (order ++ [CSec a ms n]).
    split. { eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact PO. }
    split; [| split].
    + rewrite map_app. cbn [map sec_mb]. apply u64arr_snoc.
      * destruct order as [|o0 order'].
        { destruct U64 as [[B0 [B1 _]] _]. apply u64arr_nil; [clear -OP; lia| clear -OP; atop_facts; lia]. }
        eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. cbn [length] in LEN |- *.
        replace (8 * Z.of_nat (S (length order'))) with (8 * nsec) by (clear -LEN; lia). apply Wpa. clear -LEN; lia.
      * rewrite length_map. replace (PA + 8 * Z.of_nat (length order)) with (PA + 8 * nsec) by (clear -LEN; lia). exact C_slot.
    + destruct NR' as [(A1 & A2)|(A1 & A2 & ZC)].
      * rewrite A2. destruct (junk_split m (PA + 8 * nsec) 8 (8 * (nres - nsec - 1))
                      ltac:(replace (8 + 8 * (nres - nsec - 1)) with (8 * (nres - nsec)) by (clear; lia); exact JK) ltac:(clear; lia) ltac:(clear -A1 WB; subst nsec nres; lia))
          as [_ JR].
        replace (PA + 8 * (nsec + 1)) with (PA + 8 * nsec + 8) by (clear; lia).
        replace (8 * (nres - (nsec + 1))) with (8 * (nres - nsec - 1)) by (clear; lia).
        destruct (Z_lt_le_dec (nsec + 1) nres) as [LT|GE].
        { eapply junk_frame; [exact JR| exact MU| exact WM| intros _; apply Wpj; exact LT]. }
        eapply junk_zero_len; [exact JR| clear -GE; lia].
      * rewrite A2, A1. subst nres. replace (PA + 8 * (a_nres st + 1)) with (PA + 8 * a_nres st + 8) by (clear; lia).
        replace (8 * (a_nres st + 16384 - (a_nres st + 1))) with (131072 - 8) by (clear; lia). eexists. exact ZC.
    + intros i ch Hi.
      destruct (Nat.lt_ge_cases i (length order)) as [LT|GE].
      * rewrite nth_error_app1 in Hi by exact LT. destruct (PER i ch Hi) as (lv & LV & CH).
        assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        destruct (asec_wf_all L st cs ch WFS Hin) as (mb & ms' & n' & -> & WF1c).
        exists lv. split.
        { rewrite LV. unfold sec_live. rewrite E7. split; intros [p Hp].
          - exists p. rewrite lookup_insert_ne; [exact Hp|]. intros E. subst p. rewrite NONE in Hp. discriminate.
          - destruct (N.eq_dec p (a_next st)) as [->|NE].
            + rewrite lookup_insert_eq in Hp. injection Hp as Ea Em En. exfalso. apply NEWNOT. rewrite <- Ea, <- Em, <- En in Hin. exact Hin.
            + exists p. rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact Hp. }
        destruct (Wch _ Hin) as [DC DS]. cbn [sec_mb sec_ms] in DC, DS.
        eapply asec_chunk_frameW; [exact MU| exact WM| exact WF1c| exact DC| exact DS| exact CH].
      * rewrite nth_error_app2 in Hi by exact GE.
        assert (EI : i = length order) by (destruct (i - length order)%nat as [|k] eqn:EK; [clear -GE EK; lia| cbn in Hi; destruct k; discriminate]).
        subst i. rewrite Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-.
        exists true. split.
        { split; [intros _| reflexivity]. exists (a_next st). rewrite E7, lookup_insert_eq. reflexivity. }
        rewrite LEN. exact asec_chunk_new.
  - (* [comment removed for export] *)
    destruct INST as (I1 & _ & _ & _ & _ & _). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; exact Wbase]|].
    split; [exists (Z_to_bv 8 0); exact C_srt|]. split; [exact C_jst|]. split; [exact C_jbs|]. split; [| exact C_jgl].
    pose proof C_mtx as M4. rw_split M4 1%nat M0 M3. exact M3.
  - (* [comment removed for export] *)
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM| intros _; exact Wp0].
  - (* [comment removed for export] *)
    intros x Hx HF HC. apply Forall_cons_iff in HC. destruct HC as [HCn HC]. cbn [sec_mb sec_ms] in HCn.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia]. apply Wshz; [exact Hx| clear -HCn Hx; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Append.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WT (L : alayout) (sp a ms nsec nres nres' : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (al_t L + 2800, al_t L + 3169); (AINSTANCE + 112, AINSTANCE + 720);
   (al_ptr_array L + 8 * nsec, al_ptr_array L + 8 * nsec + 8); (al_ptr_array L + 8 * nres, al_ptr_array L + 8 * nres');
   (a, a + ms); (shad a, shad a + ms / 8);
   (0x172f08, 0x5c2f50); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z.

(* [comment removed for export] *)
Definition wt_facts (L : alayout) (sp lo a ms nsec nres nres' : Z) : Prop :=
     alayout_ok L /\ ATOP <= lo /\ lo <= sp - 4096
  /\ ablk a (a + ms) /\ a + ms <= ATOP /\ a mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 < ms /\ sec_clear L a ms
  /\ 0 <= nsec /\ nsec + 1 <= nres' /\ 8 * nres' <= 8388608 /\ 0 <= nres <= nres'.

(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->      (* [comment removed for export] *)
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6250496 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>25807118408.1036002021247.103826536157.10 48752954456.1000000600:00D00MS2H21HS2H3S2H22H52HnS2H31H2H0".
split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6250496 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=25807118408.836072040845.83826536157.8 48752954456.800000900=00A00MS2H21H2H5S2H3S2H2S2H31H2H02H5".
split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section KW.
Variables (L : alayout) (sp lo a ms nsec nres nres' : Z).
Hypothesis WTF : wt_facts L sp lo a ms nsec nres nres'.
Let W' := List.filter nonempty (WT L sp a ms nsec nres nres').

Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
  destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
Local Ltac facts :=
  lazymatch goal with |- _ =>
  pose proof WTF as (ALO & CEIL & LO & AHI0 & ACE & AAL & MSM & MSP & (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d) & NS0 & NS1 & NS8 & NS9);
  pose proof (ao_t L ALO) as OT; pose proof (ao_ctx L ALO) as OC; pose proof (ao_res L ALO) as ORS; pose proof (ao_nodes L ALO) as ON;
  pose proof (ao_store L ALO) as OS; pose proof (ao_ptr L ALO) as OP; unfold aobj in OT, OC, ORS, ON, OS, OP;
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]); pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]);   (* [comment removed for export] *)
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]); pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]);
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]); pose proof (ao_res_hi L ALO) as RHI;
  destruct (ablk_int _ _ AHI0) as [kA ABND]; pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _); unfold AIMG_HI in AL1;   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res; pose proof (ad_nodes_res L ALO) as D_n_res; pose proof (ad_store_res L ALO) as D_s_res;
  pose proof (ad_ptr_res L ALO) as D_p_res; pose proof (ad_t_ctx L ALO) as D_t_c; pose proof (ad_t_nodes L ALO) as D_t_n;
  pose proof (ad_t_store L ALO) as D_t_s; pose proof (ad_t_ptr L ALO) as D_t_p; pose proof (ad_ctx_nodes L ALO) as D_c_n;
  pose proof (ad_ctx_store L ALO) as D_c_s; pose proof (ad_ctx_ptr L ALO) as D_c_p;
  unfold adisj in D_t_res, D_n_res, D_s_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_p, D_c_n, D_c_s, D_c_p
  end.

#[using="rc L sp lo nsec nres nres' WTF"] Lemma WT_shad : 0x800b6c00 <= shad a /\ shad a + ms / 8 = shad (a + ms) /\ shad (a + ms) <= 0x10007fef8000      (* [comment removed for export] *)
                /\ (forall x, x < a -> shad x + 1 <= shad a) /\ (forall x, a + ms <= x -> shad (a + ms) <= shad x).
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060=23617940675.427485465639.430722005683.450850525385.055661494050.255682798412.400000800=00F00G00L00PS3AAL2HxS3ACES3AAL3MSMSS3AL1S2Hx".
facts. rewrite !shad_div. unfold ASHOFF in *. split; [clear -AL1; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|].
  split; [clear -AAL MSM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. split; [clear -ACE; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|].
  split; intros x Hx; rewrite shad_div; unfold ASHOFF; [clear -Hx AAL| clear -Hx]; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma KT_X : forall A k, 0 <= k ->
  (forall iv, In iv (WT L sp a ms nsec nres nres') -> fst iv < snd iv -> A + k <= fst iv \/ snd iv <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk H. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros iv Hiv.
  apply List.filter_In in Hiv. destruct Hiv as [Hiv NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV. exact (H iv Hiv NEV).
Qed.

#[using="rc lo WTF"] Lemma KT_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
  (A + k <= AINSTANCE + 112 \/ AINSTANCE + 720 <= A) -> (A + k <= 0x172f08 \/ 0x5c2f50 <= A) -> disjoint_from W' A k.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0>21035583471.4126340350319.4033399290401.4134504378725.4036025172803.4044605239152.4050850525385.0 52786865963.405616681703.40 59755849144.4000000800C00K00W00[00i00j01601:01FS3AL12H3S3OTi2H12H3S3SA12H3S3NS03OPi2H3S2H5S4CEIL2LO2H31HSS3NS93OPi2H3S2H4S3ONi2H33OSi".
facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4 H5. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 H5 NEV CEIL LO OT OP AL1 SA1 ON OS NS0 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="lo WTF"] Lemma KT_obj : forall A k, (A + k <= 65536 \/ 6250496 <= A) -> (A + k <= 2147446784 \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ATOP ->      (* [comment removed for export] *)
  (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> (A + k <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
  (A + k <= a \/ a + ms <= A) -> (A + k <= al_nodes L \/ al_nodes L + 1048576 <= A) -> (A + k <= al_store L \/ al_store L + 8388608 <= A) ->
  disjoint_from W' A k.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0>21035583471.3126340350319.3133399290401.3134504378725.3136025172803.3144605239152.3150850525385.0 52786865963.315616681703.31 59755849144.3100000400800K00^00b00n00o01>01B01IS2H6S2H4S3SA13SA23SA32H12H2S3NS03NS13NS82H22H5S2H0S4CEIL2LO2H3SS3NS83NS92H22H5S2H0S2H72H8".
facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H0 H1 H2 H3 H4 H5 H6 H7 H8. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H0 H1 H2 H3 H4 H5 H6 H7 H8 NEV CEIL LO NS0 NS1 NS8 NS9 SA1 SA2 SA3; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc lo WTF"] Lemma KT_shad : forall A k, 2147446784 <= A -> 0 <= k -> A + k <= 17594333495296 ->      (* [comment removed for export] *)
  (A + k <= shad a \/ shad (a + ms) <= A) -> disjoint_from W' A k.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0>21035583471.4326340350319.4333399290401.4334504378725.4336025172803.4344605239152.4350850525385.0 52786865963.435616681703.43 59755849144.4300000<00G00_01601:01H01I01\01`01oS4ABND2H12H3S3OTs2H12H3S2OT2ON2OS2OP3SA22H43NEVS3NS03NS13NS83OPs2H12H3S2H1S4CEIL2LO2H31HSS3NS83NS93OPs2H12H3S2H1S3ONs2H12H33OSs".
facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 NEV CEIL LO OT OP ABND ON OS SA2 NS0 NS1 NS8 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)

#[using="rc lo WTF"] Lemma KT_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W' A k.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0070>10348506307.1921035583471.1926340350319.1948880235586.1950850525385.0 51796692231.1959755849144.1900000?00M00Q00X00Y00]019S3OTi2H12H33OTsS3C_t2OT2H12H3S2H3S2OT2H3SS2H2S2OT5D_t_p2H12H35D_t_n5D_t_s".
facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OT D_t_p C_t D_t_n D_t_s OTs OTi; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".   (* [comment removed for export] *)

#[using="rc lo WTF"] Lemma KT_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0070>10348506307.2421035583471.2426340350319.2448880235586.2450850525385.0 51796692231.2459755849144.2400000?00P00c00m00n01201QS3OCi2H13OCs2H3S3C_c2OT2OC2H12H3S2OT2OC5D_t_c2H12H3S2OT2OC2H3SS2H2S2OT2OC5D_c_p2H12H35D_c_n5D_c_s".
facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OC OT D_t_c D_c_p C_c D_c_n D_c_s OTs OTi OCs OCi; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc lo WTF"] Lemma KT_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0070>10348506307.2221035583471.2226340350319.2248880235586.2250850525385.0 51796692231.2259755849144.2200000800J00`00k00l01001VS3RHI2H1S3C_r2OT3ORS2H12H3S2OT3ORS7D_t_res2H12H3S2OT3ORS2H3SS2H2S2OT3ORS7D_p_res2H12H37D_n_res7D_s_res".
facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 ORS RHI OT D_t_res D_p_res C_r D_n_res D_s_res OTs OTi; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".   (* [comment removed for export] *)

#[using="rc sp lo nsec nres nres' WTF"] Lemma KT_res_geo : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                   /\ shad (al_res L + 137439023104) <= 0x10007fef8000      (* [comment removed for export] *)
                   /\ (shad (al_res L + 137439023104) <= shad a \/ shad (a + ms) <= shad (al_res L)).
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=13845253054.850850525385.000000A00BS3AAL3C_r3ORS3RHIS".
facts. rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI C_r AAL. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc lo WTF"] Lemma KT_res_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof. pose proof KT_res_geo as (SR1 & SR2 & SR3 & SR4). intros A k H1 H2 H3. apply KT_shad; clear -H1 H2 H3 SR1 SR3 SR4; lia. Qed.

(* [comment removed for export] *)
#[using="rc lo WTF"] Lemma KT_rt : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt L m -> arep_rt L m'.
Proof.
  intros m m' MU WM RT. eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
  repeat (apply Forall_cons; [cbn [fst snd]; first [apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia | apply KT_ctx; clear; lia] |]). apply Forall_nil.
Qed.
#[using="rc lo WTF"] Lemma KT_rt2 : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt2 m -> arep_rt2 m'.
Proof. intros m m' MU WM RT2. eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia. Qed.
#[using="rc lo WTF"] Lemma KT_rt3 : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt3 m -> arep_rt3 m'.
Proof.
  intros m m' MU WM RT3. eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]. unfold rt3_hulls.
  repeat (apply Forall_cons; [cbn [fst snd]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia |]). apply Forall_nil.
Qed.
#[using="rc lo WTF"] Lemma KT_relro : forall m m', munch W' m m' -> arelro m -> arelro m'.
Proof. intros m m' MU HRO. eapply arelro_frame; [exact MU | exact HRO | apply KT_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]. Qed.
End KW.

Section Store.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Let AHS : aholes := AH DI AQ ASEC_of AFK.
Hypothesis HL : ahole_laws AHS.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

#[using="HL CI_OK CI_OK2"] Theorem store_sec : forall (L : alayout) (RNG RNG' : footprint) (sp lo : Z) (m m' : amem) (st : astate) (X : aconc) (LB : list ablock)
    (n a nres' id : Z) (sj' : list word) (RESV : list (Z * Z)),
  let nsec := a_nsec st in let nres := a_nres st in let PA := al_ptr_array L in let ms := sec_map_size n in
  let UB := a + 6144 in let t := al_t L in
  alayout_ok L -> arng L RNG st -> AREP AHS L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  sfresh RESV st n a = true -> aresv_ok L RESV ->
  ATOP <= lo -> lo <= sp - 4096 -> sp <= 2^47 ->
  fp_le RNG RNG' -> rng RNG' a ms -> rng RNG' (shad a) (ms / 8) ->
  ((nsec <> nres /\ nres' = nres)
   \/ (nsec = nres /\ nres' = nres + 16384
       /\ rw_cells bsegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])) ->
  nres' <= 1048576 -> rng RNG' PA (8 * nres') ->
  munch (WT L sp a ms nsec nres nres') m m' -> wmono bsegs m m' ->
  (* [comment removed for export] *)
  u64arr bsegs m' (t + 2800) sj' -> length sj' = 46%nat -> rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m' (AINSTANCE + 112) [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))] ->
  rw_cells bsegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)] -> junk_at m' (AINSTANCE + 136) 32 -> junk_at m' (AINSTANCE + 168) 512 ->
  rw_cells bsegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m' (AINSTANCE + 704) 16 ->
  rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)] ->
  rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)] ->
  junk_at m' (a + 32) (4096 - 32) ->
  rw_cells bsegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))] ->
  junk_at m' (a + 4096 + 16) (2048 - 32) ->
  rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 < id < 2^31 ->
  junk_at m' UB (ms - 6144) ->
  fill_at m' (shad a) 768 0xfa ->
  rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa ->
  ADEPOT DI L m' ->
     aheap_pres CI LB sp m m'
  /\ AHEAP_P AHS L RNG' (st_sec st nres' a ms n) (HB (a_next st) UB n :: LB) m'.
Proof.
  intros until RESV. cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM FRSH ROK CEIL LO SP47 FPLE RA RSA NR' NRB RPA' MU0 WM
         STATS LSJ UNW I112 I128 J136 J168 I680 J704 SLOT HDR PGJ MAG LCJ AHD IDR USR SHF SHU SHT DEP.
  set (ms := sec_map_size n) in *.
  (* [comment removed for export] *)
  pose proof (valid_geo L RESV st n a N PRIM FRSH ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
  pose proof (valid_clear L RESV st n a N PRIM FRSH ROK) as VC. fold ms in VC.
  pose proof (valid_hulls L RESV st n a N PRIM FRSH ROK) as VH. fold ms in VH.
  pose proof (valid_chunks L RESV st n a N PRIM FRSH ROK) as VK. fold ms in VK.
  pose proof (valid_wf1 L RESV st n a N PRIM FRSH ROK) as VW. fold ms in VW.
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  destruct VC as (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d).
  unfold K_HIGH_MEM in AHI0.
  pose proof (munch_filter_nonempty _ m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres')) in *.
  assert (NE : Forall (fun iv => fst iv < snd iv) W') by (apply nonempty_filter).
  (* [comment removed for export] *)
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_fake L ALO) as OFK. pose proof (ao_ptr L ALO) as OP. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, OP, OD. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]). Local Ltac2 Set LiaHints.tbl := fun () => "0770?1003498417.42  10107077370.0  1024918769.42  10313546700.2  10317707088.1  10348506307.21 10350661516.58 1036400023.46  10418250229.0  10558272481.0  10561104689.58 10657196691.2  11393903428.42 11399205489.58 11771838668.58 11960425209.58 12085054665.47 1213507121.0   12230333729.0  12252311136.58 12466536006.7  12473221242.46 12702930569.46 12734860680.42 12806942364.58 12842659686.42 12877090629.1  12882494444.58 12911672881.58 13097809467.1  13363103644.58 13374621338.0  13379636597.0  1354531031.42  13841995460.58 13842812599.14 13855525184.11 14003831931.2  14334904049.0  14350564129.0  14512388544.47 14599312949.0  14909706256.0  15385380214.0  15515497321.5  15515743081.5  15600913946.0  15641247130.0  15884633525.0  16171675966.47 16241277347.46 16519857078.8  16534157257.1  16618243449.58 16761533409.0  16819224858.0  1685717371.0   17182596419.4  17319127324.42 1752366103.0   1806999749.0   1808867361.0   18106462146.4  18162831764.58 18190976604.7  18212684137.58 18624216289.0  18819676314.0  19272463841.0  19326977656.2  19391632715.42 19624560922.0  19661371593.1  19678020314.0  19747427649.58 1984505903.42  19997301913.4  20036365281.0  20074192588.42 20129501903.47 20194707655.46 20360563220.47 2070300449.42  20928953744.0  20940279735.47 21035583471.21 21320301010.42 21729042401.0  22151024481.0  22274997856.53 22380900506.0  22667418865.0  22963339297.0  23117814972.58 23206159049.58 23797021921.0  23851311830.1  24161383989.0  24313481904.7  244470796.58   24584451792.46 2466419681.0   25096308066.5  25244543118.0  25302471033.58 25306219862.53 25368144993.0  25504777043.3  25547068508.42 25746336150.47 25866020593.0  25927571866.0  2598582810.0   26019069273.42 26238245128.0  26340350319.21 26348676725.0  26798547658.0  2681174948.0   26948201232.0  27424445493.0  27585758071.47 27646578572.58 27835980597.0  27964496844.0  28293211455.42 28636935202.1  28730407438.0  28864672450.3  29052223718.58 29128369359.53 29280591733.0  29367392726.58 29566964324.58 29876442010.0  30002758177.0  30096494156.0  30289262305.0  30375204292.58 30459694352.0  30818340360.12 30853749936.46 30912897340.3  30982273841.58 31643461955.1  31846761820.58 31933984517.3  32061470433.0  32197473439.46 32322652420.42 32837901993.58 32895681066.0  32917795153.6  32967448720.0  33226120534.42 33296739851.47 3348895365.0   33678399737.42 33701439324.42 34087601377.0  34249316982.46 34430840181.0  34447177505.0  34496073500.58 34505139028.58 34521219823.7  34605942042.0  34873384142.21 34873384142.22 34873384142.46 35023214204.58 35185949340.58 3533635125.0   35767348052.42 35830687525.0  36038528230.58 36168437292.58 36181653045.0  36449675461.1  36470333909.0  36478104782.2  36478941840.0  36662401190.58 36782690527.2  36887120666.0  36958550341.1  3701201205.0   37012665662.21 37012665662.22 37012665662.46 37154438636.58 37197491598.0  37293425473.46 37321368305.0  37391252247.53 37613994522.0  37702623886.0  38156309810.46 38340672736.47 38436634709.0  38486419344.0  38582832014.0  38634481703.53 38688441017.53 38692635477.0  38907343899.9  38948636245.0  39012636437.0  39061900985.58 39076636629.0  39109405821.53 39172636981.0  39188636933.0  39220637093.0  39268637205.0  39300866430.47 39332637397.0  39396637589.0  39412637669.0  39499910128.58 39564465382.58 39805717596.58 39825569382.58 39877252253.21 39877252253.22 39877252253.46 39880018058.0  3999224260.58  4062230170.0   40748257.0     40851493414.42 40878242572.58 41086855884.0  41120432332.3  41304414244.0  41484538908.58 41781849818.0  42067573343.46 42068696334.0  42411609006.0  42423887244.42 4253627674.0   42949876977.58 4303884257.0   4347338828.0   43521793446.6  43521793446.8  43521793446.9  43554307580.3  43726251286.42 43781106499.3  44528309601.0  44982870197.0  44994127980.58 45031930741.0  45083664282.0  45281718036.58 4538805664.58  45417986616.3  45564613988.58 45682890198.58 4590280113.58  45915496212.58 45966287030.58 46035800858.0  46202803425.0  46505921502.7  46653580506.47 46757233518.7  46938111414.58 47010513865.0  47138514249.0  47266514633.0  473139435.0    47323661732.0  47382160817.0  47391408284.58 47505523338.2  47521224125.4  47521224125.8  47521224125.9  47522515401.0  47555048462.0  47648606362.0  47995803164.42 48036252314.0  48144990612.58 48192559857.0  48308593333.0  48607931693.47 48880235586.21 49133592978.47 49167139738.0  49214230042.0  49316297882.0  49449657548.0  4962568370.5   4962692735.3   49987230624.58 50507719301.0  50722525001.0  50807741237.0  50842804144.1  50850525385.0  51058076257.0  51106526153.0  51169068801.47 51193994209.0  51298526729.0  51362526921.0  51426527113.0  51565560309.46 51581654860.0  51585635637.0  51682527881.0  51746528073.0  51794604986.14 51796692231.21 51922528697.0  51938152724.42 52092015925.0  52118410402.58 52131486133.0  52322529801.0  52386529993.0  52489829152.4  52500980810.0  52551278971.4  53151677237.0  53176367772.58 53238998938.2  53241087642.2  53342909220.0  53538588424.47 53697866677.0  53713652172.0  53765873925.0  53794534217.0  54045862543.53 54242535561.0  54383971025.23954434536137.0  54765217882.58 54914115332.58 54953652027.5  55347908438.58 55588686165.0  55820075385.58 55850663588.0  55966506250.0  55970540745.0  56098541129.0  56109098293.0  56130541289.0  56161778022.58 56226541513.0  56238242452.58 56339599370.0  56354541897.0  56952294234.3  57378544969.0  57506545353.0  57890546505.0  58146547273.0  58262569709.47 58345831445.0  58402548041.0  58516399889.0  58527212280.2  5876345733.0   588087689.1    58867622849.9  58909763434.0  59028527489.0  59050112737.0  59170550345.0  59308586510.3  59362156708.0  59560683771.42 59728604922.21 59728604922.22 59747240486.58 59755849144.21 59938552649.0  6002171896.14  60178217930.0  60432239777.0  60578554569.0  60910355765.0  60962555721.0  61111562977.0  61310551231.53 61602557641.0  61700544005.0  61820339768.4  61858558409.0  62114559177.0  62271447194.0  62501751258.0  63667678773.0  63679728986.0  63897306209.0  64145643061.0  64557663237.0  65381404196.0  6538579724.58  65445025434.0  65459601425.3  65817757142.58 65818118554.0  66048936517.1  66211542331.7  66240208154.0  66263364923.1  66429798709.0  66466160830.4  66466160830.8  66466160830.9  66888073492.58 67137498436.58 6753655066.7   6755542714.7   6755569814.4   6755569814.8   6755569814.9   6758013062.21  6758013062.22  67656215317.47 67723395739.5  67834325550.14 68065236533.0  68150908601.42 68331430219.0  68394867509.0  68469171356.58 68538155588.46 6859089733.7   7029766554.0   7133277749.0   7156509974.58  7457518318.6   7628471526.46  7630963418.7   8088179100.2   8227584993.0   8611333452.0   8938650181.58  8950590234.0   9173904202.3   9237344084.2   9393026273.0   9498883483.14  9653081878.21  9653081878.22  9813476725.0   00000;00<00G00L00M00W00c00d00e00f01101501601I01U01^01g01h01i02E02K02Z03903B03H03M03N03`03k03l04104204304404504G04Y04Z04[04\05905:05;05<05C05M05N05O05P05T06206;06<06E06F06G06H06P06U06V06W06X06`06a06l07507607707807<07H07I07J07K07V07\07`07a07m08J08O09409=09>09?09H09S09T09U0:<0:=0:>0:?0:K0:l0:m0:n0:o0;:0;F0;S0;T0;\0;]0;f0<G0<H0<M0<S0=00=10=20=30=80=90=C0=D0=E0=F0=G0=H0=i0>30>40>50>:0>;0><0>E0>J0>R0>S0>\0>a0>b0>c0>d0>e0>f0>g0?40?U0?Z0?e0?f0?k0?o0@00@50@60@K0@L0@W0@X0@a0AC0AD0AM0AR0AS0Am0An0Ao0B40B50BA0BB0BS0Bd0C60CL0CR0CS0CT0CU0CZ0C`0Ca0Cb0Cc0Cg0Ch0DE0DI0DJ0DK0DL0D_0E10EJ0EO0EP0Ea0Eb0FA0FB0FC0F`0Fa0Fb0Fc0Fd0GC0Gn0Go0HA0HB0HC0HL0HM0H]0H^0H_0H`0Ha0Hf0Hg0Hh0Hi0I20I70I=0IF0Ie0J=0JV0JW0JX0JY0JZ0J_0Jk0Jl0K10K20K80K90K>0K?0K@0KL0KM0KX0KY0KZ0Kb0Kf0Kn0L30L<0L@0LA0LB0Lm0Ln0Lo0M40M>0MB0MC0ML0MW0MX0Mi0Mj0Mk0N10NL0N]0Nb0Nc0Nd0Ne0Nf0Ng0Nh0Nm0O10O50OE0OM0ON0OO0OP0OV0OW0OX0OY0OZ0O[0Ob0Og0Oh0Oi0Oj0Ok0P40P80P\0P]0P^0P_0P`0Pa0Pb0Pc0QB0QC0QD0QE0QF0QK0QL0QM0QN0QO0QS0QW0QX0QY0QZ0RF0RG0RH0RI0RP0RQ0RR0RS0RY0R^0Rb0Rc0S<0S=0S>0S?0S@0SH0SI0SU0SV0Sc0Sd0Sl0T50T60T?0T@0TA0TB0TC0TD0TE0TJ0TK0TL0TM0TN0TR0TS0TT0TU0TV0T_0T`0Ta0Tb0Tf0Tg0Th0U=0U>0U?0U@0UA0UE0UF0UG0UZ0Uh0Um0V=0V>0VF0VG0VH0VI0VJ0VK0VL0W60W70W80W@0WA0WB0WC0WD0WE0WF0WG0WH0WI0WJ0WV0WW0W[0Wd0We0Wf0Wl0Wm0Wn0Wo0X30X70X?0X@0XA0XB0XC0XD0XE0XF0XG0XH0Xi0Y10Y=0Y>0YG0YH0YI0YN0Ye0Yn0Yo0Z00Z90ZE0ZT0ZZ0Z_0Z`0Za0[:0[;0[@0[E0[F0[X0[b0\00\1S4CEIL2LO1HSS4CEIL2LO1HS3RSPSS2GB2H12H2S3OPi2WB3NS0SSSS4CEIL2LO1HS2SXSS4CEIL2LO3SF23SF31HS3OPi2WB3NS0S3ONi3OSiS3OPi3NS0SSS3OPs2WB3NS03NS83SF13SF23SF3S1R2Q2S4CEIL2LO3STa1HS2OT2ON2OS2OP5D_t_p3NS03NS13NS8S3ONi3OSiS4ABNDS3OTiSS4ABND3SF13SF23SF3S4CEIL2LO1HFS3SA1SSSSS3AAL2G11D4MSM'2GBS3AAL3C_f3OFK4OFKiSSSS4CEIL2LO2OT2ON2OS2OP3NS83NS9SSSS2RM2AMS2Q42RM2Q7SSSS2WBS2OT2ON2OS2OP5D_t_p2WB3NS03NS8S3ACE3STaSS3ONi3OSiSSSS3RSP2HcS3SA1SSSS3RSP2HcSS1R3Bb23FITS3ONi3OSiSSSS2QSS3OPi2WB3NS0SSSS4CEIL2LO1HS4ABNDS2ALSS3OPi2WB3NS0S3OPs3NS03NS83NS93SA13SA23SA3S3C_tS2OT2ON2OS2OP5D_n_p3NS03NS83NS95D_s_pS3OPi3NS0SSS1D2H12H2S4CEIL2LO1HSSS2OT3ORS2ON2OS2OP7D_n_res2B12B27D_s_resSSSS3OPi2WB3NS0S4CEIL2LO2OT2ON2OS3OFK2OP2OD4ABNDSSSS1R3Bb13FITS3OPi2WB3NS0S5D_t_n5D_t_sSS2Q13RI1SS3ONi3OSiS4CEIL2LO2OT3ORS2ON2OS2OP4ABND2B2SS3STaS4ABNDS3C_p2OT2ON2OS2OP3NS13NS83NEVSSSS3SA1SS2Ct2H12H2SSSSSS2OT2ON2OS2OP5D_n_p3NS13NS85D_s_pS4OFKi3ODiSSS3OTiSSS2QS4QS16S3OTiS3RHI2B1SS3OPi3NS0S3SF1SSSSSSS3OFK1R2K12K3S4CEIL2LO2OT2ON2OS2OP3NS13NS83STaS3POSS4CEIL2LO1HSS3SA1S2Q6SS3OTiSS3ONs3SF13SF23SF33OSsSS2Q52Q63RI1SS3OPi3NS0S4CEIL2LO2OT2ON2OS2OP4ABND3NS13NS8SS3ONi3OSiS3SA1SS4CEIL2LO2OT2ON2OS2OP4ABNDSSS3SA1SS2Q23RI23RI3SS3C_f3OFK1R2K12K3S1R3Gs43Gs51D3SFcS4CEIL2LO4ABND3STaS4OFKs3SA13SA23SA33ODsS4ABNDSSSS3OTiS4ABNDSSSS2HcSS3OPs3NS03NS13NS83SF13SF23SF3S2QSSSSS3OFK5D_t_f1R2K12K3S1R3Gs43Gs52Ct3SFcS4CEIL2LO2OT2ON2OS2OP3STaS3SA1SS3OTs3SA13SA23SA3SS3C_r2OT3ORS2ON2OS2OP3NEV2B12B2SSS4CEIL2LO2OT2ON2OS2OP3NS83STaSSSSS2OT3ORS2ON2OS2OP7D_t_res2B12B2S2OT3ORS2ON2OS2OP7D_p_res3NS03NS13NS82B12B2SS2Q12Q23RI23RI32P4SSS3ONi3OSiSS3RHI3SA23SA32B1SSSSS3OPiSSSS3C_f3C_dS3OTiS4ABNDS3OPi3NS0S3OFK5D_f_p1R2K12K35D_n_f5D_s_fS1R3Gs43Gs52Cp3SFc2Cn2CsS4CEIL2LO2OT2ON2OS2OP3STaSSSSS3OTiS3OPi2WB3NS0SS3POSSS4ABNDSS3OTiSSS3OPi2WB3NS0SS4CEIL2LO1HSSS3SA12SXS2SXS3SF42SXS3RI1S3OPi3NS0S2HcSSS2OT2ON2OS3OFK2OP2OD5D_f_p2WB3NS03NS85D_d_pSSS3SF1S4OFKi3ODiS2HcSS3OPi3NS0S4CEIL2LO1HSS3OTs3SF13SF23SF3SSS1R2Q1S2OT2ON2OS2OP5D_t_p3NS13NS8S2A12A22WR2WB3NRBS3OTiSSSSSSS3SA1S2SXS2SXS3MSB3SA13SA22SXS3SF12SXSSSS4ABNDSSSSSS2GB2H2S3OPiSSSSS1R2Q12Q3S2HxS2OT2ON2OS3OFK2OP2OD3SA23SF23SF43NEVSSSSSSSS2OT2ON2OS2OP5D_t_p3NS03NS83NS9SSSSS3STaSSSSS2H3S2H3SSSS2OT2ON2OS3OFK2OP2OD5D_f_p3NS03NS13NS85D_d_pSSSS2Q52Q6SSSS4ABNDS3Gs5S2G5SS3OPs3NS13NS83SA13SA23SA3SSSSS3RHI2B1SS3LSJ3AL22E8SS5D_t_f5D_t_dSS3RI12P5S3OPi3NS0SS3ONi3OSiSSSSSSS3OTiSSSSS2LTSSSSS3OPi3NS0SSSS2WBSSS3RSP3CLB2Q12Q22P52P4SSSSS2HkSSS4OFKi1R2K14OFKs2K3S1R2GB3Gs43SFcS3OTiS2Cp2H12H22Cn2CsSS3SC12H1SSSSSSS2OT3ORS2ON2OS2OP7D_p_res2WB3NS03NS82B12B2SSS3RSP2HcSSSSSSSSSSS3OPi2WB3NS0SS2RMS3OPi3NS0SSS1R2Q3SFSS2SXS2SXS3SF32SXSSSSSSSSSS3C_p2OT2ON2OS2OP3NS03NS83NS93NEVS2Q13RI1S3SC23SC32H2SS3ONi3OSiSSS3SA1S4CEIL2LO3SA23SA33STa1HS3RI23RI3SSS3OPi3NS0S2Q63RI23RI3S4CEIL2LO3STa1HS1R2Q4S3POSSSS5D_n_f5D_n_d5D_s_f5D_s_dSS3POSS3RSPSS3SC23SC42H12H22H3S3OFK1R2K3S1R3Gs43SFc2GBS".
pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]).   (* [comment removed for export] *)
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]). pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & [kF OFKs]).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD ODs] & [jD ODi]). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ AHI0) as [kA ABND]. pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _). unfold AIMG_HI in AL1.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ad_t_ctx L ALO) as D_t_c.
  pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_ptr L ALO) as D_t_p.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_ctx_ptr L ALO) as D_c_p.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_fake L ALO) as D_s_f. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d. pose proof (ad_fake_dtls L ALO) as D_f_d.
  unfold adisj in D_t_res, D_c_res, D_n_res, D_s_res, D_f_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_p, D_c_n, D_c_s, D_c_f, D_c_p,
                   D_n_f, D_n_p, D_s_f, D_s_p, D_f_p, D_d_res, D_t_d, D_d_p, D_n_d, D_s_d, D_f_d.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof HS as HS0. unfold AHS, AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  pose proof HS0 as (WFS & ARR & INST2 & PZ & SHZ). pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (NSR : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ 8 * nres' <= 8388608 /\ a_nres st <= nres').
  { destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB NRB WR; lia. }
  destruct NSR as (NS0 & NS1 & NS8 & NS9).
  (* [comment removed for export] *)
  assert (WTF : wt_facts L sp lo a ms (a_nsec st) (a_nres st) nres').
  { unfold wt_facts. repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    - unfold sec_clear. repeat (split; [assumption|]). assumption.
    - clear -WB; lia. }
  pose proof (WT_shad L sp lo a ms _ _ _ WTF) as (SA1 & SA2 & SA3 & SAlt & SAge).
  pose proof (KT_X L sp a ms (a_nsec st) (a_nres st) nres') as KX. pose proof (KT_img L sp lo a ms _ _ _ WTF) as Kimg.
  pose proof (KT_obj L sp lo a ms _ _ _ WTF) as Kobj. pose proof (KT_shad L sp lo a ms _ _ _ WTF) as Kshad.
pose proof (KT_t L sp lo a ms _ _ _ WTF) as Kt.   (* [comment removed for export] *)
  pose proof (KT_ctx L sp lo a ms _ _ _ WTF) as Kctx. pose proof (KT_res L sp lo a ms _ _ _ WTF) as Kres.
  pose proof (KT_res_sh L sp lo a ms _ _ _ WTF) as Kres_sh. pose proof (KT_res_geo L sp lo a ms _ _ _ WTF) as (SR1 & SR2 & SR3 & SR4).
  fold W' in KX, Kimg, Kobj, Kshad, Kt, Kctx, Kres, Kres_sh.
  Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  set (st2 := st_sec st nres' a ms n) in *.
  (* [comment removed for export] *)
  assert (AR' : AREP AHS L st2 X m').
  { split; [apply awf_sec; exact WF|].
    split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
    split. { (* [comment removed for export] *)
      destruct INST as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold ainstance. subst st2. rewrite E3, E4.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I3| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I4| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [exact I112|].
      split; [pose proof I680 as M4; rw_split M4 1%nat M0 M3; exact M0|].
      split; [eapply cells_frame; [exact I7| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I8| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      eapply cells_frame; [exact I9| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]. }
    split. { (* [comment removed for export] *)
      destruct THR as (T0 & T40 & CACHES & CSTATS & _ & _). unfold athread.
      split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | subst st2; reflexivity | subst st2; reflexivity | reflexivity |].
               unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
      split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
      split; [exists sj'; split; [exact STATS| exact LSJ]| exact UNW]. }
    split. { (* [comment removed for export] *)
      intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
      destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
      pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
      assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                   /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
      { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
      destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
      split; [| split; [| split]].
      - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity |].
        apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
      - eapply afreearray_frame; [exact MU | exact WM | exact FARR | subst st2; reflexivity | subst st2; reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
        + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
        + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
      - eapply (aslots_update L W' m m' MU WM st st2 X X c (-1)); [exact SLOTS | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          split; [reflexivity|]. split.
          * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_update L W' m m' MU WM st st2 X X c (-1)); [exact SHADOW | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
          split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | rewrite shlen_div; clear -QS QS16; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia |].
          rewrite <- shad_add_shlen by (clear -AL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
          apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
    split. { (* [comment removed for export] *)
      eapply (hq_frame _ HL L st st2 X X m m' W'); [exact HQ | exact MU | exact WM | |].
      - unfold quar_untouched. apply Forall_forall. intros iv Hin.
        unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
        inWT Hin. all: unfold AINSTANCE in *.
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS C_t D_t_p D_t_n D_t_s NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |];
          clear -NEV B1 B2 CEIL LO OT OP ORS AHI0 SA1 SA2 SA3 SR1 ON OS D_t_res D_p_res C_r D_n_res D_s_res NS0 NS1 NS8 NS9 WB ABND AL1 RHI OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - unfold quar_same. subst st2. rewrite E9, E10, E11, E12, E1. repeat (split; [reflexivity|]).
        split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
    split. { (* [comment removed for export] *)
      unfold AHS, AH. cbn [ah_sec]. subst st2.
      eapply (asec_append L W' m m' MU WM st X nres' a n id WF HS0 N PRIM VW VK NR' NRB).
      - intros ch Hin. destruct (asec_wf_all L st _ ch WFS Hin) as (mb & ms' & n' & -> & W1c). cbn [sec_mb sec_ms].
        pose proof W1c as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
        pose proof (sec_facts n' ltac:(clear -G5; lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM' & MSB'). rewrite <- G4 in MSM', MSB'.
        destruct (ablk_int _ _ G2) as [kB GB].   (* [comment removed for export] *)
        assert (SHc : 0x800b6c00 <= shad mb /\ shad mb + ms' / 8 = shad (mb + ms') /\ shad (mb + ms') <= 0x10007fef8000
                      /\ (shad (mb + ms') <= shad a \/ shad (a + ms) <= shad mb)).
        { rewrite !shad_div. unfold ASHOFF, K_HIGH_MEM in *. clear -G1 GB G3 MSM' D AAL MSM. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
        destruct SHc as (SC1 & SC2 & SC3 & SC4). unfold K_HIGH_MEM in *.
        split; intros A k H1 H2 H3.
        + apply Kobj; clear -H1 H2 H3 GB G3 Ct Cp Cn Cs D; lia.
        + apply Kshad; clear -H1 H2 H3 SC1 SC2 SC3 SC4; lia.
      - intros POS. apply KX; [clear -POS; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -POS NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - intros LT. apply KX; [clear -LT NS0; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -LT NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia.
      - replace (shlen K_REGION) with 536870912 by reflexivity.
        apply Kres_sh; [apply shad_mono; clear -RSP; lia| clear; lia|].
        rewrite !shad_div. clear -RSP. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - intros x Hx Hxa. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
        assert (SX : 2147446784 <= shad x /\ shad x + 1 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).   (* [comment removed for export] *)
        apply Kshad; [clear -SX; lia| clear; lia| clear -SX; lia|].
        destruct Hxa as [Hxa|Hxa]; [left; apply SAlt; exact Hxa| right; apply SAge; exact Hxa].
      - exact I128. - exact J136. - exact J168. - exact I680. - exact J704. - exact SLOT. - exact HDR. - exact PGJ. - exact MAG. - exact LCJ.
      - exact AHD. - exact IDR. - exact USR. - exact SHF. - exact SHU. - exact SHT. }
    split; [exact DEP|].
    split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]|].
    split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia|].
    split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia |]); apply Forall_nil].
    intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | subst st2; reflexivity | subst st2; reflexivity | |].
    - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
    - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  assert (SHFK : 0x800b6c00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 = shad (al_fake L + 11571200)      (* [comment removed for export] *)
                 /\ shad (al_fake L + 11571200) <= 0x10007fef8000
                 /\ (shad (a + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad a)).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK C_f AAL OFKs OFKi. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHFK as (SF1 & SF2 & SF3 & SF4).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  split.
  - (* [comment removed for export] *)
    intros x Hx CL. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Hx.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    + eapply (disjoint_outside W' x 1); [| clear; lia]. apply KX; [clear; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
        clear -STa NEV CEIL LO OT OP AHI0 ACE ON OS SA2 SA3 NS0 NS1 NS8 NS9 WB SP47 ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Kimg x 1); unfold AIMG_HI, AINSTANCE in *; clear -R Q1 Q2 Q3 Q4; lia | clear; lia].
    + destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      * destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        -- destruct (BB xb Hxb) as [Bb1 Bb2].
           pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
           eapply disjoint_outside; [eapply (Kres x 1) | clear; lia]; clear -R Bb1 Bb2 FIT; lia.
        -- (* [comment removed for export] *)
           assert (Hin : In (CSec mb0 ms0 n') (sec_chunks_of st)).
           { unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
             apply in_map_iff. exists (p, CSec mb0 ms0 n'). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp. }
           pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
           cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
           pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SFc. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
           destruct (ablk_int _ _ Gs2) as [kB GB].   (* [comment removed for export] *)
           eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R GB Gs3 Gs4 Gs5 SFc Ct Cp Cn Cs D; lia.
      * destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R K1 K3 OFK D_t_f D_f_p C_f D_n_f D_s_f OFKs OFKi; lia.
    + destruct SH as (x' & Hx' & ->).
      destruct Hx' as [STa | [CIa | FK]].
      * assert (SX : shad (a + ms) <= shad x' /\ shad x' + 1 <= 17594333495296).
        { split; [apply SAge; atop_facts; clear -STa ACE; lia|]. rewrite shad_div. unfold ASHOFF. clear -STa. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1 SA2 MSB; lia | clear; lia].
      * destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        assert (SX : 2147446784 <= shad x' /\ shad x' + 1 <= 0x800b6c00) by (rewrite shad_div; unfold ASHOFF, AIMG_HI in *; clear -R Q1 Q3; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).   (* [comment removed for export] *)
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1; lia | clear; lia].
      * destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3).
        assert (SX : shad (al_fake L) <= shad x' /\ shad x' + 1 <= shad (al_fake L + 11571200)).
        { rewrite !shad_div. clear -R K1 K3 OFK OFKs OFKi. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1) | clear; lia]; clear -SX SF1 SF3 SF4; lia.
  - (* [comment removed for export] *)
    split; [exact ALO|].
    split; [eapply (arng_sec L RNG RNG' st X); [exact WF| exact ARNG| exact FPLE| exact RA| exact RSA| exact RPA']|].
    split; [exists X; split; [exact AR'| replace (a + 6144) with (a + SEC_UOFF) by reflexivity; apply ablocks_sec; [exact WF| exact BL| exact VW]]|].
    unfold AHS, AH. cbn [ah_fake].
    eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |] |].
    + unfold fake_untouched. apply Forall_forall. intros iv Hin.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
      inWT Hin. all: unfold AINSTANCE in *.
      all: clear -NEV CEIL LO OT OP OFK OD AHI0 ACE SA1 SA2 SA3 SF1 SF2 SF3 SF4 ON OS D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi OFKs OFKi ODs ODi.
      (* [comment removed for export] *)
      all: first [ lazymatch goal with
                   | |- context [al_t _] => clear D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_ptr_array _] => clear D_t_f D_t_d C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_nodes _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_s_f D_s_d
                   | |- context [al_store _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_n_d
                   | |- _ => clear D_t_f D_t_d D_f_p D_d_p D_n_f D_s_f D_n_d D_s_d
                   end; repeat (split; [lia|]); lia
                 | repeat (split; [lia|]); lia ].
    + intros c F n'. split; [intros H; cbn [In] in H; destruct H as [H|H]; [discriminate H| exact H]| intros H; cbn [In]; right; exact H].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Store.
End CANSEC1.

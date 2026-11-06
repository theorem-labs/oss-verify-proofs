(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanCtrlProps SizeHist Gap AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
(* [comment removed for export] *)
Context {SBc PAc : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation AMI := (AsanInv.AMI RESV ATOP).
Local Notation AINV := (AsanInv.AINV ATOP).
Local Notation aok := (AsanNodeSem.aok ATOP).
Local Notation apost := (AsanNodeSem.apost ATOP).
Local Notation atot := (atotal (aok34 (ATOP:=ATOP) (SBc:=SBc) (PAc:=PAc)) apost).   (* [comment removed for export] *)
Local Notation SBP st := (a_space_beg st = SBc /\ a_ptr_array st = PAc) (only parsing).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

(* [comment removed for export] *)
Definition qframe (st st' : astate) : Prop :=
  a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st
  /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st.
#[using="Type"] Lemma qframe_refl : forall st, qframe st st. Proof. intros. unfold qframe. repeat split; reflexivity. Qed.
#[using="Type"] Lemma qframe_trans : forall a b c, qframe a b -> qframe b c -> qframe a c.
Proof. intros a b c (A1&A2&A3&A4&A5&A6&A7&A8) (B1&B2&B3&B4&B5&B6&B7&B8). unfold qframe. repeat split; congruence. Qed.
#[using="Type"] Lemma qframe_same_but : forall c st st', same_but c st st' -> qframe st st'.
Proof. intros c st st' (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12). unfold qframe. repeat split; assumption. Qed.
#[using="Type"] Lemma qframe_init_cache : forall st, qframe st (init_cache st).
Proof. intros. unfold qframe, init_cache. destruct (a_cinit st); repeat split; reflexivity. Qed.
#[using="Type"] Lemma SBP_qframe : forall st st', qframe st st' -> SBP st -> SBP st'.
Proof. intros st st' (_&_&_&_&_&_&E1&E2) [H1 H2]. rewrite E1, E2. split; assumption. Qed.
#[using="Type"] Lemma SBP_init_cache : forall st, SBP st -> SBP (init_cache st).
Proof. intros st H. unfold init_cache. destruct (a_cinit st); exact H. Qed.
#[using="Type"] Lemma qframe_lists : forall pc pb st st', qframe st st' ->
  all_chunks pc pb st' = all_chunks pc pb st /\ qbatches pb st' = qbatches pb st /\ CH pc pb st' = CH pc pb st.
Proof. intros pc pb st st' (H1&H2&H3&H4&H5&H6&_). unfold CH, all_chunks, qbatches, live_chunks. rewrite H1, H3, H5. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_dealloc_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> AM R) mo,
  INV (CPrim c n :: pc) pb st mo -> 1 <= c <= 31 ->
  zsum2 (CH pc pb st) <= SECM ->
  FAINV st -> VC st <= VCMAX -> SBP st ->                               (* [comment removed for export] *)
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> FAINV st' -> VC st' = VC st -> atot (k st') mo' P) ->
  atot (cache_dealloc st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hc HSB HFA HVC HSBP Hk.
  pose proof (INV_init_cache _ _ _ _ HI) as HI1.
  pose proof HI1 as [HA1 HM1]. pose proof (AINV_cls _ _ _ _ HA1 Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  rewrite max_count_init_cache in C9. rewrite all_chunks_cons, cntP_cons in C10. cbn [is_prim_of] in C10. rewrite Z.eqb_refl in C10.
  assert (Hwfpc : Forall chunk_wf pc) by (destruct HA1 as (_ & HW & _); rewrite all_chunks_cons in HW; apply Forall_cons_iff in HW as [_ HW]; unfold all_chunks in HW; apply Forall_app in HW as [X _]; exact X).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb (init_cache st)) /\ 0 <= nbatch c (qbatches pb (init_cache st))).
  { split; [apply cntP_nonneg|]. unfold nbatch. Local Ltac2 Set LiaHints.tbl := fun () => "00f0>11007710484.7211022514395.3812119184177.7212123263146.6212455700236.7212457642691.3814597877006.5914597994717.3815034641751.3419314515925.4219325000533.4122329323787.3624168266040.4124168266040.622424961824.37 26140274107.7226140378154.4226146672246.432767257602.38 29952099896.4129952099896.6231403210810.4132225777125.7233713060049.4233719349217.4235634581739.7237063016318.4237063153391.7237073500960.3841177670159.3841413886354.3841413888920.3945324012221.4448922905126.7250133758430.3851296473798.4252489713956.4154239174649.4154239174649.6256037635185.7256052160864.4156052160958.3856796295580.3956909035359.7256923560592.3857494252179.4358986455502.4260722348053.5960722501062.3862900945643.7262907366474.4262911557412.3865363225953.386718459268.36 00000:00A00E00I00R00W00]00^00_00d00i00m00n00o01301=01G01Q01W01^01e02702;02@02E02R02V02Z02^02a02b02c03203D03L03^03b04K05;05?05F05M05S05W05[05`05c05d05e05i05m06706;06?S2C52D52D7S2C52C7S2D6S2X2S3C103D10S3C10S4HVC2SSS3HszS3HszS2HnSSS2HnS5Hhalf2D8S2C85HhalfS2C85HhalfS4Hmc'S2X02X1S2X02X1S5Hcnt04Hmc'5HfullS2D6S3HszS3HszS5Hfull5HhalfS2C2S2C2S2C2S1FSSS4Hmc'5Hhalf2H0S4Hmc'5Hfull5HhalfS2C93HnfS5Hcnt04Hmc'5HhalfS2X2S2C22C52C62C72C82C93C105Hcnt03Hsz3Hnf3HneS2C22C52C62C72C83C105Hcnt03Hsz4Hmc'5Hfull2E43HneS2C3S2C22C3S2C32C6S4Hmc'S2C4S2C4S3Hm8S1HSSS2C1S2C8S2C12C62C8S2C9S2Hn".
destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  assert (F : 32 <= size_of_class c <= 65536 /\ 2 <= max_cached c <= 16).
  { destruct HA1 as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _]. cbn in Hwf. destruct Hwf as [Hn Hcl].
    assert (Hp : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. rewrite <- Hcl in F. lia. }
  destruct F as [Hsz Hmc'].
  unfold cache_dealloc. cbv zeta. rewrite max_count_init_cache.
  destruct (Z.eqb_spec (c_count (get_cls (init_cache st) c)) (max_cached c)) as [Hfull|Hnf].
  - (* [comment removed for export] *)
    assert (Hhalf : 1 <= max_cached c / 2 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split; [apply Z.div_le_lower_bound; lia| apply Z.mul_div_le; lia]. }
    assert (Hm8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
    set (m := max_cached c / 2) in *. clearbody m.
    assert (Hnf8 : 4 * (c_num_freed (get_cls (init_cache st) c) + m) + K_FREEARR_MAP <= K_FREEARR_MAX).
    { assert (size_of_class c * c_num_freed (get_cls (init_cache st) c) <= K_FREEARR_OFF).
      { apply Z.le_trans with (c_allocated_user (get_cls (init_cache st) c)); [|lia]. rewrite C10. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (32 * c_num_freed (get_cls (init_cache st) c) <= K_FREEARR_OFF).
      { apply Z.le_trans with (size_of_class c * c_num_freed (get_cls (init_cache st) c)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
      assert (m <= 8) by lia.
      unfold K_FREEARR_OFF, K_FREEARR_MAP, K_FREEARR_MAX in *. lia. }
    assert (Hcarved : 32 * (c_num_freed (get_cls (init_cache st) c) + m) <= c_mapped_user (get_cls (init_cache st) c)).
    { apply Z.le_trans with (size_of_class c * (c_num_freed (get_cls (init_cache st) c) + m)); [apply Z.mul_le_mono_nonneg_r; lia|].
      apply Z.le_trans with (c_allocated_user (get_cls (init_cache st) c)); [|lia]. rewrite C10.
      apply Z.mul_le_mono_nonneg_l; [lia|]. rewrite Hfull in *. lia. }
    apply (ensure_ok R P (CPrim c n :: pc) pb (init_cache st) c (c_num_freed (get_cls (init_cache st) c) + m) _ mo HI1 Hc ltac:(lia) Hnf8).
    { rewrite CH_cons. cbn [sec_of app]. rewrite CH_init_cache. exact HSB. }
    { apply FAINV_init_cache. exact HFA. }
    { rewrite VC_init_cache. exact HVC. }
    { exact Hcarved. }
    { apply SBP_init_cache. exact HSBP. }
    intros st2 mo2 HI2 HSB2 E1 E2 E3 E4 E5 HFA2 HVC2. cbn [negb]. rewrite VC_init_cache in HVC2.
    pose proof HI2 as [HA2 HM2].
    destruct (qframe_lists (CPrim c n :: pc) pb (init_cache st) st2 (qframe_same_but _ _ _ HSB2)) as (AC1 & AC2 & AC3).
    apply Hk.
    + apply (INV_repc (CPrim c n :: pc)); auto.
      * intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
      * unfold CLSOK. cproj. pose proof (AINV_cls _ _ _ _ HA2 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
        rewrite (max_count_same_but _ _ _ c HSB2), max_count_init_cache in *.
        destruct (qframe_lists pc pb (init_cache st) st2 (qframe_same_but _ _ _ HSB2)) as (AC1' & AC2' & AC3').
        rewrite all_chunks_cons, cntP_cons in D10. cbn [is_prim_of] in D10. rewrite Z.eqb_refl in D10.
        rewrite AC1', AC2' in D10 |- *. rewrite E1, E2, E3, E4 in *. repeat split; try lia.
      * unfold cls_mapped_bytes'. cproj. lia.
    + eapply qframe_trans; [apply qframe_init_cache|]. eapply qframe_trans; [apply (qframe_same_but c); exact HSB2|]. apply (qframe_same_but c). apply same_but_put.
    + apply FAINV_put; [exact Hc| exact HFA2| |]; cproj; pose proof (HFA2 c Hc) as [[X0 X1] X2]; lia.
    + rewrite VC_put by exact Hc. unfold vc_cls. cproj. lia.
  - (* [comment removed for export] *)
    apply Hk.
    + apply (INV_repc (CPrim c n :: pc)); auto.
      * intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
      * unfold CLSOK. cproj. rewrite max_count_init_cache. repeat split; try lia.
      * unfold cls_mapped_bytes'. cproj. lia.
    + eapply qframe_trans; [apply qframe_init_cache|]. apply (qframe_same_but c). apply same_but_put.
    + apply FAINV_put; [exact Hc| apply FAINV_init_cache; exact HFA| |]; cproj; rewrite ?get_cls_init_cache; pose proof (HFA c Hc) as [[X0 X1] X2]; lia.
    + rewrite VC_put by exact Hc. rewrite VC_init_cache, get_cls_init_cache. unfold vc_cls. cproj. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma large_dealloc_ok : forall R (P : R -> Model -> Prop) pc pb st mb ms n (k : astate -> AM R) mo,
  INV (CSec mb ms n :: pc) pb st mo ->
  zsum2 (CH (CSec mb ms n :: pc) pb st) <= SECM ->
  FAINV st -> VC st <= VCMAX ->                                        (* [comment removed for export] *)
  (forall mo', INV pc pb (set_nsec (a_nsec st - 1) st) mo' -> atot (k (set_nsec (a_nsec st - 1) st)) mo' P) ->
  atot (large_dealloc st mb ms k) mo P.
Proof.
  intros R P pc pb st mb ms n k mo HI HSB HFA HVC Hk.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _].
  cbn in Hwf. destruct Hwf as (Hn & -> & Hal & Hmb & Hrange).
  Local Ltac2 Set LiaHints.tbl := fun () => "00@0>15327941232.3119107843036.2823993942799.3128398959101.3330440072420.314409144783.31 4409228031.29 47465132265.2753922792683.2953922876379.3154077156251.4156015522257.3356017570414.316644462811.31 6646609764.33 8140464396.33 00000500600700800=00B00G00K00R00Y00]00m01=01D01K01LS3HalSFFS3MSAS3HmbS3HmbS2HnS2Hn2SBS2Hn2SBS2H6S3AT13Hmb6HrangeS3AT13Hmb6HrangeS2Hn2SBS2Hn2SBS".
pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (MSA : sec_map_size n mod 4096 = 0).
  { unfold sec_map_size, rup, PG. match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end. apply Z_mod_mult. }
  unfold large_dealloc.
  apply (poison0_ok _ _ (CSec mb (sec_map_size n) n :: pc) pb st _ mo mb (sec_map_size n) HI ltac:(lia) ltac:(lia) Hrange HSB HFA HVC).
  intros mo1 HI1. unfold ev. apply atotal_vis.
  { apply (INV_munmap_aok _ _ _ _ mb (sec_map_size n) HI1); try lia.
    - rewrite CH_cons. cbn. left. reflexivity.
    - unfold LS_LO, ACEIL in *. lia. }
  intros z mo2 Hpost. cbn [apost] in Hpost. destruct Hpost as [-> ->]. rewrite Z.eqb_refl.
  apply Hk.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n) by (apply mmap_len_id; lia). rewrite ML.
  destruct HI1 as [HA1 HM1]. split.
  - unfold AINV in *. destruct HA1 as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec a_cinit] in *.
    rewrite all_chunks_set_nsec. change (qbatches pb (set_nsec (a_nsec st - 1) st)) with (qbatches pb st).
    change (CH pc pb (set_nsec (a_nsec st - 1) st)) with (CH pc pb st).
    rewrite all_chunks_cons in *. rewrite CH_cons in H6. cbn [sec_of app] in H6. rewrite zlen_cons in H6.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec] in *.
             rewrite all_chunks_set_nsec. rewrite all_chunks_cons, cntP_cons in X. cbn [is_prim_of] in X.
             change (qbatches pb (set_nsec (a_nsec st - 1) st)) with (qbatches pb st). rewrite Z.add_0_l in X. exact X. }
    split. { apply Forall_cons_iff in H2 as [_ H2]. exact H2. }
    split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [lia|]. split; [exact H7|]. split; [exact H8|].
    unfold live_budget, live_chunks in *. cbn [a_live set_nsec]. exact H9.
  - change (CH pc pb (set_nsec (a_nsec st - 1) st)) with (CH pc pb st).
    rewrite CH_cons in HM1. cbn [sec_of app] in HM1.
    apply (AMI_munmap [] (CH pc pb st) st); auto; try lia; try (unfold LS_LO, ACEIL in *; lia).
    unfold commit_bytes, csum, get_cls. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma recycle_chunk_ok : forall R (P : R -> Model -> Prop) pc pb st ch (k : astate -> AM R) mo,
  INV (ch :: pc) pb st mo -> zsum2 (CH (ch :: pc) pb st) <= SECM ->
  FAINV st -> VC st <= VCMAX -> SBP st ->                               (* [comment removed for export] *)
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> FAINV st' -> VC st' = VC st -> atot (k st') mo' P) ->
  atot (recycle_chunk st ch k) mo P.
Proof.
  intros R P pc pb st ch k mo HI HSB HFA HVC HSBP Hk. unfold recycle_chunk. destruct ch as [c n|mb ms n].
  - pose proof HI as [HA _]. pose proof HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _]. cbn in Hwf. destruct Hwf as [Hn Hcl].
    Local Ltac2 Set LiaHints.tbl := fun () => "0040>22316741847.222424961824.23 48092744413.246722652248.22 00000400800;00?S2HnS2HnS1FS2Hn".
assert (Hp : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. rewrite <- Hcl in F.
    apply (cache_dealloc_ok R P pc pb st c n k mo HI ltac:(lia)).
    + rewrite CH_cons in HSB. cbn [sec_of app] in HSB. exact HSB.
    + exact HFA.
    + exact HVC.
    + exact HSBP.
    + exact Hk.
  - apply (large_dealloc_ok R P pc pb st mb ms n k mo HI HSB HFA HVC).
    intros mo' HI'. apply Hk; [exact HI'| | eapply FAINV_frame; [| exact HFA]; intros; reflexivity | reflexivity]. unfold qframe. cbn. repeat split; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma recycle_chunks_ok : forall R (P : R -> Model -> Prop) l pc pb st (k : astate -> AM R) mo,
  INV (l ++ pc) pb st mo -> zsum2 (CH (l ++ pc) pb st) <= SECM ->
  FAINV st -> VC st <= VCMAX -> SBP st ->                               (* [comment removed for export] *)
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> FAINV st' -> VC st' = VC st -> atot (k st') mo' P) ->
  atot (recycle_chunks st l k) mo P.
Proof.
  intros R P l. induction l as [|ch l IH]; intros pc pb st k mo HI HSB HFA HVC HSBP Hk; cbn [recycle_chunks app] in *.
  - apply Hk; [exact HI| apply qframe_refl| exact HFA| reflexivity].
  - apply (recycle_chunk_ok R P (l ++ pc) pb st ch _ mo HI HSB HFA HVC HSBP).
    intros st1 mo1 HI1 HQ1 HFA1 HVC1. apply (IH pc pb st1 k mo1 HI1).
    + destruct (qframe_lists (l ++ pc) pb st st1 HQ1) as (_ & _ & ->). rewrite CH_cons in HSB. rewrite zsum2_app in HSB.
      assert (0 <= zsum2 (sec_of ch)).
      { destruct HI as [HA _]. destruct HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _].
        Local Ltac2 Set LiaHints.tbl := fun () => "0040>15032548481.2716473325804.2732238463205.2847469323581.2700000100800>00BSS3HSB1HS2Hn1HS2Hn".
destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct Hwf as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
      lia.
    + exact HFA1.
    + rewrite HVC1. exact HVC.
    + exact (SBP_qframe _ _ HQ1 HSBP).
    + intros st2 mo2 HI2 HQ2 HFA2 HVC2. apply Hk; [exact HI2| | exact HFA2| congruence]. eapply qframe_trans; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma zsum2_perm : forall l l', Permutation l l' -> zsum2 l = zsum2 l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.

#[using="Type"] Lemma AINV_requeue : forall pc pb pb' st ql lb qg gb,
  AINV pc pb st ->
  Permutation (qchunks (pb' ++ ql ++ qg)) (qchunks (qbatches pb st)) ->
  zlen (pb' ++ ql ++ qg) = zlen (qbatches pb st) ->
  Forall batch_wf (pb' ++ ql ++ qg) -> lb = bsum ql -> gb = bsum qg ->
  AINV pc pb' (set_qglob qg gb (set_qloc ql lb st)).
Proof.
  intros pc pb pb' st ql lb qg gb HA HP HL HB Hlb Hgb. unfold AINV in *.
  destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_qglob set_qloc a_cinit] in *.
  assert (Hq : qbatches pb' (set_qglob qg gb (set_qloc ql lb st)) = pb' ++ ql ++ qg) by reflexivity.
  assert (HPa : Permutation (all_chunks pc pb' (set_qglob qg gb (set_qloc ql lb st))) (all_chunks pc pb st)).
  { unfold all_chunks. rewrite Hq. unfold live_chunks. cbn [a_live set_qglob set_qloc]. apply Permutation_app_head. apply Permutation_app_head. exact HP. }
  rewrite Hq.
  split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_qglob set_qloc] in *.
           rewrite Hq. rewrite (cntP_perm c _ _ HPa). unfold nbatch in *. rewrite HL. exact X. }
  split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa| exact H2]. }
  split; [exact HB|]. split; [exact Hlb|]. split; [exact Hgb|].
  split. { rewrite H6. unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. apply Permutation_sym. exact HPa. }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  unfold live_budget, live_chunks in *. cbn [a_live set_qglob set_qloc]. exact H13.
Qed.

#[using="Type"] Lemma INV_requeue : forall pc pb pb' st ql lb qg gb mo,
  INV pc pb st mo ->
  Permutation (qchunks (pb' ++ ql ++ qg)) (qchunks (qbatches pb st)) ->
  zlen (pb' ++ ql ++ qg) = zlen (qbatches pb st) ->
  Forall batch_wf (pb' ++ ql ++ qg) -> lb = bsum ql -> gb = bsum qg ->
  INV pc pb' (set_qglob qg gb (set_qloc ql lb st)) mo.
Proof.
  intros pc pb pb' st ql lb qg gb mo [HA HM] HP HL HB Hlb Hgb. split; [eapply AINV_requeue; eauto|].
  apply (AMI_perm (CH pc pb st)).
  - unfold CH. apply secs_perm. unfold all_chunks. change (qbatches pb' (set_qglob qg gb (set_qloc ql lb st))) with (pb' ++ ql ++ qg).
    unfold live_chunks. cbn [a_live set_qglob set_qloc]. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact HP.
  - apply (AMI_mono _ st); auto. unfold commit_bytes, csum, get_cls. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8138322914.20000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition shell : achunk := CPrim K_BATCH_CLASS 7000.
#[using="Type"] Lemma shell_class : class_id (needed_size 7000) = K_BATCH_CLASS. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma shell_wf : chunk_wf shell. Proof. cbn -[class_id needed_size]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=63125897534.4000001S".
split; [lia|]. symmetry. exact shell_class. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma INV_open_batch : forall pc b pb st mo,
  INV pc (b :: pb) st mo -> INV (rev (b_chunks b) ++ shell :: pc) pb st mo.
Proof.
  intros pc b pb st mo [HA HM].
  assert (HPa : Permutation (all_chunks (rev (b_chunks b) ++ shell :: pc) pb st) (shell :: all_chunks pc (b :: pb) st)).
  { unfold all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite <- !app_assoc. cbn [app].
    eapply Permutation_trans. { apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    (* [comment removed for export] *)
    rewrite (app_assoc pc). rewrite (app_assoc pc (live_chunks st)).
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
    apply Permutation_app_swap_app. }
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    rewrite qbatches_cons in *.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa), cntP_cons. cbn [is_prim_of shell].
             unfold nbatch in *. rewrite qbatches_cons, zlen_cons in X.
             destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|Hne].
             { replace (K_BATCH_CLASS =? K_BATCH_CLASS) with true by reflexivity. Local Ltac2 Set LiaHints.tbl := fun () => "0030>36543086922.2439057787594.2239061721525.2400000:00=00@S2H91X3HneS1XS1X".
lia. }
             replace (K_BATCH_CLASS =? c) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
    split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa|]. constructor; [apply shell_wf| exact H2]. }
    split. { apply Forall_cons_iff in H3 as [_ H3]. exact H3. }
    split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. symmetry. etransitivity. { apply Permutation_length. apply secs_perm. exact HPa. } reflexivity. }
    exact (conj H7 (conj H8 H9)).
  - apply (AMI_perm (CH pc (b :: pb) st)); [| exact HM]. unfold CH. etransitivity; [| apply secs_perm; apply Permutation_sym; exact HPa]. cbn. apply Permutation_refl.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma do_recycle_ok : forall R (P : R -> Model -> Prop) bs pc st (k : astate -> AM R) mo,
  INV pc bs st mo -> zsum2 (CH pc bs st) <= SECM ->
  FAINV st -> VC st <= VCMAX -> SBP st ->                               (* [comment removed for export] *)
  (forall st' mo', INV pc [] st' mo' -> qframe st st' -> FAINV st' -> VC st' = VC st -> atot (k st') mo' P) ->
  atot (do_recycle st bs k) mo P.
Proof.
  intros R P bs. induction bs as [|b bs IH]; intros pc st k mo HI HSB HFA HVC HSBP Hk; cbn [do_recycle].
  - apply Hk; [exact HI| apply qframe_refl| exact HFA| reflexivity].
  - pose proof (INV_open_batch _ _ _ _ _ HI) as HI1.
    assert (HPC : Permutation (CH (rev (b_chunks b) ++ shell :: pc) bs st) (CH pc (b :: bs) st)).
    { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite !secs_app, secs_cons. cbn [sec_of shell]. rewrite app_nil_l. rewrite <- !app_assoc.
      eapply Permutation_trans. { apply Permutation_app_tail. apply secs_perm. apply Permutation_sym. apply Permutation_rev. }
      rewrite (app_assoc (secs pc) (secs (live_chunks st))). rewrite (app_assoc (secs pc) (secs (live_chunks st)) (secs (b_chunks b) ++ _)).
      apply Permutation_app_swap_app. }
    apply (recycle_chunks_ok R P (rev (b_chunks b)) (shell :: pc) bs st _ mo HI1).
    + rewrite (zsum2_perm _ _ HPC). exact HSB.
    + exact HFA.
    + exact HVC.
    + exact HSBP.
    + intros st1 mo1 HI2 HQ1 HFA1 HVC1. Local Ltac2 Set LiaHints.tbl := fun () => "0090>15045128875.3 21705301447.8 26274361860.2747471404002.8 50191223586.3550193331994.2961687854140.2961687854140.3564081846100.9 00000100600700;00?00B00J00R00\SS3IHlSS2HnS2H0S1HS3HSB2E2S3HSB2E2S2Hn3IHl1H".
apply (cache_dealloc_ok R P pc bs st1 K_BATCH_CLASS 7000 _ mo1 HI2 ltac:(unfold K_BATCH_CLASS; lia)).
      * destruct (qframe_lists pc bs st st1 HQ1) as (_ & _ & ->).
        pose proof (zsum2_perm _ _ HPC) as E. rewrite CH_cons in E || idtac.
        assert (E2 : zsum2 (CH pc bs st) <= zsum2 (CH pc (b :: bs) st)).
        { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons, !secs_app, !zsum2_app.
          assert (0 <= zsum2 (secs (b_chunks b))); [|lia].
          destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. rewrite qbatches_cons, qchunks_cons in HW.
          apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [HW _].
          clear - HW. induction (b_chunks b) as [|ch l IHl]; [cbn; lia|]. apply Forall_cons_iff in HW as [H1 HW]. rewrite secs_cons, zsum2_app.
          specialize (IHl HW). destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
        lia.
      * exact HFA1.
      * rewrite HVC1. exact HVC.
      * exact (SBP_qframe _ _ HQ1 HSBP).
      * intros st2 mo2 HI3 HQ2 HFA2 HVC2. apply (IH pc st2 k mo2 HI3).
        -- destruct (qframe_lists pc bs st st2 (qframe_trans _ _ _ HQ1 HQ2)) as (_ & _ & ->).
           pose proof (zsum2_perm _ _ HPC). 
           assert (E2 : zsum2 (CH pc bs st) <= zsum2 (CH pc (b :: bs) st)).
           { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons, !secs_app, !zsum2_app.
             assert (0 <= zsum2 (secs (b_chunks b))); [|lia].
             destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. rewrite qbatches_cons, qchunks_cons in HW.
             apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [HW _].
             clear - HW. induction (b_chunks b) as [|ch l IHl]; [cbn; lia|]. apply Forall_cons_iff in HW as [H1 HW]. rewrite secs_cons, zsum2_app.
             specialize (IHl HW). destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
           lia.
        -- exact HFA2.
        -- rewrite HVC2, HVC1. exact HVC.
        -- exact (SBP_qframe _ _ (qframe_trans _ _ _ HQ1 HQ2) HSBP).
        -- intros st3 mo3 HI4 HQ3 HFA3 HVC3. apply Hk; [exact HI4| | exact HFA3| congruence]. eapply qframe_trans; [exact HQ1|]. eapply qframe_trans; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma merge_batches_spec : forall rest cur,
  Forall batch_wf (cur :: rest) ->
  let '(l, ex, exb) := merge_batches cur rest in
  Permutation (qchunks (l ++ ex)) (qchunks (cur :: rest)) /\ zlen (l ++ ex) = zlen (cur :: rest)
  /\ bsum l + exb = bsum (cur :: rest) /\ bsum ex = exb /\ Forall batch_wf (l ++ ex) /\ 0 <= exb.
Proof.
  induction rest as [|nx rest IH]; intros cur HB.
  - cbn [merge_batches]. rewrite app_nil_r. cbn [bsum]. rewrite zlen_cons, zlen_nil. Local Ltac2 Set LiaHints.tbl := fun () => "00>0>12536795481.2013354681004.2015045132080.6 2622837819.23 33584114126.2134904868911.233830791556.21 42278067674.2443716502761.2044966675318.2348831909090.2360651257085.2061291241959.248676726031.6  00000700<00=00A00E00I00M00N00U00Y00]00^00_00`S2C32N3S3HleSS2I4S2I2S2I3S2I3FS2C12N1S2I6S2I2FSS".
repeat split; auto; lia.
  - cbn [merge_batches]. apply Forall_cons_iff in HB as [Hc HB]. pose proof HB as HB0. apply Forall_cons_iff in HB as [Hn HB].
    destruct (Z.leb_spec (b_count cur + b_count nx) Q_BATCH) as [Hle|Hgt].
    + set (cur' := mkABatch (b_count cur + b_count nx) (b_size cur + (b_size nx - Q_BATCH_BYTES)) (b_chunks nx ++ b_chunks cur)).
      assert (Hc' : batch_wf cur').
      { destruct Hc as (C1 & C2 & C3 & C4). destruct Hn as (N1 & N2 & N3 & N4). unfold batch_wf, cur'. cbn [b_count b_size b_chunks].
        rewrite zlen_app, zsumc_app. repeat split; try lia. apply Forall_app; split; assumption. }
      specialize (IH cur' ltac:(constructor; assumption)). destruct (merge_batches cur' rest) as [[l ex] exb]. destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
      split; [|split; [|split; [|split; [|split]]]].
      * rewrite !qchunks_app in *. rewrite qchunks_cons. cbn [b_chunks app]. rewrite !qchunks_cons.
        eapply Permutation_trans. { rewrite app_nil_l || idtac. exact I1. }
        rewrite qchunks_cons. unfold cur'. cbn [b_chunks]. rewrite <- app_assoc. eapply Permutation_trans; [apply Permutation_app_swap_app|]. rewrite app_assoc. apply Permutation_refl.
      * rewrite !zlen_app, !zlen_cons in *. lia.
      * cbn [bsum] in *. unfold cur' in I3. cbn [b_size] in I3. lia.
      * cbn [bsum b_size]. lia.
      * apply Forall_app in I5 as [I5a I5b]. apply Forall_app. split; [exact I5a|]. constructor; [|exact I5b].
        unfold batch_wf. cbn. unfold Q_BATCH, Q_BATCH_BYTES. repeat split; try lia. constructor.
      * unfold Q_BATCH_BYTES. lia.
    + specialize (IH nx HB0). destruct (merge_batches nx rest) as [[l ex] exb]. destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
      split; [|split; [|split; [|split; [|split]]]].
      * cbn [app]. rewrite !qchunks_cons. apply Permutation_app_head. exact I1.
      * cbn [app]. rewrite !zlen_cons in *. lia.
      * cbn [bsum] in *. lia.
      * exact I4.
      * cbn [app]. constructor; assumption.
      * exact I6.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma dequeue_while_spec : forall l bytes mn,
  let '(taken, rest, bytes') := dequeue_while l bytes mn in
  taken ++ rest = l /\ bytes' = bytes - bsum taken /\ (bytes' <= mn \/ rest = []).
Proof.
  induction l as [|b l IH]; intros bytes mn; cbn [dequeue_while].
  - repeat split; auto. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0030>23043829939.6 23050691541.1052327374130.15000001002006SSS2I2".
lia.
  - destruct (Z.ltb_spec mn bytes).
    + specialize (IH (bytes - b_size b) mn). destruct (dequeue_while l (bytes - b_size b) mn) as [[taken rest] bytes'].
      destruct IH as (I1 & I2 & I3). cbn [app bsum]. rewrite I1. repeat split; auto. lia.
    + repeat split; auto. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma set_qloc_eta : forall st, set_qloc (a_qloc st) (a_qloc_bytes st) st = st.
Proof. intros st. destruct st; reflexivity. Qed.
#[using="Type"] Lemma set_qglob_eta : forall st, set_qglob (a_qglob st) (a_qglob_bytes st) st = st.
Proof. intros st. destruct st; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_pc_perm : forall pc pc' pb st mo, Permutation pc pc' -> INV pc pb st mo -> INV pc' pb st mo.
Proof.
  intros pc pc' pb st mo HP [HA HM].
  assert (HPa : Permutation (all_chunks pc' pb st) (all_chunks pc pb st)) by (unfold all_chunks; apply Permutation_app_tail; apply Permutation_sym; exact HP).
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7).
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa). exact X. }
    split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa| exact H2]. }
    split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. apply Permutation_sym. exact HPa. }
    exact H7.
  - apply (AMI_perm (CH pc pb st)); [| exact HM]. unfold CH. apply secs_perm. apply Permutation_sym. exact HPa.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_close_batch : forall pc b pb st mo,
  INV (rev (b_chunks b) ++ shell :: pc) pb st mo -> batch_wf b -> INV pc (b :: pb) st mo.
Proof.
  intros pc b pb st mo [HA HM] Hb.
  assert (HPa : Permutation (all_chunks (rev (b_chunks b) ++ shell :: pc) pb st) (shell :: all_chunks pc (b :: pb) st)).
  { unfold all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite <- !app_assoc. cbn [app].
    eapply Permutation_trans. { apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    rewrite (app_assoc pc). rewrite (app_assoc pc (live_chunks st)).
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
    apply Permutation_app_swap_app. }
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    rewrite qbatches_cons in *.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa), cntP_cons in X. cbn [is_prim_of shell] in X.
             unfold nbatch in *. rewrite qbatches_cons, zlen_cons.
             destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|Hne].
             { replace (K_BATCH_CLASS =? K_BATCH_CLASS) with true in X by reflexivity. Local Ltac2 Set LiaHints.tbl := fun () => "0030>36543086922.2539057787594.2339061721525.2500000:00=00@S2H91X3HneS1XS1X".
lia. }
             replace (K_BATCH_CLASS =? c) with false in X by (symmetry; apply Z.eqb_neq; lia). lia. }
    split. { pose proof (Permutation_Forall HPa H2) as X. apply Forall_cons_iff in X as [_ X]. exact X. }
    split. { constructor; assumption. }
    split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. etransitivity. { apply Permutation_length. apply secs_perm. exact HPa. } reflexivity. }
    exact (conj H7 (conj H8 H9)).
  - apply (AMI_perm (CH (rev (b_chunks b) ++ shell :: pc) pb st)); [| exact HM]. unfold CH. etransitivity; [apply secs_perm; exact HPa|]. cbn. apply Permutation_refl.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma recycle_ok : forall R (P : R -> Model -> Prop) st (k : astate -> AM R) mo,
  INV [] [] st mo -> a_qloc st = [] -> a_qloc_bytes st = 0 -> bsum (a_qglob st) <= 2^30 ->
  FAINV st -> VC st <= VCMAX -> SBP st ->                               (* [comment removed for export] *)
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st -> a_qloc st' = [] -> a_qloc_bytes st' = 0 ->
     0 <= a_qglob_bytes st' <= Q_MIN -> FAINV st' -> VC st' = VC st -> SBP st' -> atot (k st') mo' P) ->
  atot (recycle st Q_MIN k) mo P.
Proof.
  intros R P st k mo HI Hql Hqlb HQ HFA HVC [HSB0 HPA0] Hk.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  assert (Hqb : qbatches [] st = a_qglob st) by (unfold qbatches; rewrite Hql; reflexivity).
  rewrite Hqb in HBW. 
  assert (HWq : Forall chunk_wf (qchunks (a_qglob st))).
  { unfold all_chunks in HW. rewrite Hqb in HW. cbn [app] in HW. apply Forall_app in HW as [_ HW]. exact HW. }
  Local Ltac2 Set LiaHints.tbl := fun () => "00A0>15032542919.2815045166469.1 22529485560.2937425493680.4838302173815.423901711215.10 39382791686.4644137518170.475021882636.60 52884318596.2654213479986.5858284282868.2859315137787.4559315137787.4762550847029.9 68359972687.479280288580.45 00000100200900<00C00F00G00H00Z00[00d00e00m01201;01<01KSSS3Hov1XS1XS2M32D2S1HSSS1H4Hb2'6Hrest02Q2SS4Hb2'2Q2SS4Hb2'1XS1H1XS2B32IH1HSS2HQ2M42D24Hb2'".
destruct (quarantine_class_bound 1 (a_qglob st) ltac:(lia) HBW HWq) as (_ & Hov & Hpos).
  unfold recycle. cbv zeta. rewrite Hb2.
  destruct (Z.ltb_spec (bsum (a_qglob st)) (Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)))) as [X|_]; [unfold Q_BATCH_BYTES, zlen in *; lia|].
  (* [comment removed for export] *)
  assert (HMB : forall gl ex exb,
    (if (Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)) <? bsum (a_qglob st)) && (bsum (a_qglob st) * 100 <? Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)) * 200)
     then match a_qglob st with [] => ([], [], 0) | b :: rest => merge_batches b rest end
     else (a_qglob st, [], 0)) = (gl, ex, exb) ->
    Permutation (qchunks (gl ++ ex)) (qchunks (a_qglob st)) /\ zlen (gl ++ ex) = zlen (a_qglob st)
    /\ bsum gl + exb = bsum (a_qglob st) /\ bsum ex = exb /\ Forall batch_wf (gl ++ ex) /\ 0 <= exb).
  { intros gl ex exb E. destruct (_ && _).
    - destruct (a_qglob st) as [|b rest] eqn:Eq.
      + injection E as <- <- <-. cbn. repeat split; auto; try lia; try constructor.
      + pose proof (merge_batches_spec rest b HBW) as MS. rewrite E in MS. exact MS.
    - injection E as <- <- <-. rewrite app_nil_r. cbn [bsum]. repeat split; auto; lia. }
  destruct (if _ && _ then _ else _) as [[gl ex] exb] eqn:E. specialize (HMB gl ex exb eq_refl). destruct HMB as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (dequeue_while_spec gl (bsum (a_qglob st) - exb) Q_MIN) as DS.
  destruct (dequeue_while gl (bsum (a_qglob st) - exb) Q_MIN) as [[taken rest] bytes2]. destruct DS as (D1 & D2 & D3).
  assert (Hb2' : bytes2 = bsum rest) by (subst gl; rewrite bsum_app in M3; lia).
  assert (Hrest0 : 0 <= bsum rest).
  { apply Forall_app in M5 as [M5 _]. subst gl. apply Forall_app in M5 as [_ M5].
    clear - M5. induction rest as [|b rest IH]; [cbn; lia|]. apply Forall_cons_iff in M5 as [(B1&B2&B3&B4) M5]. cbn. specialize (IH M5).
    assert (0 <= zsumc (b_chunks b)) by (apply zsumc_nonneg; eapply Forall_impl; [|exact B4]; cbv beta; intros; lia). unfold Q_BATCH_BYTES in B3. lia. }
  destruct (Z.ltb_spec Q_MIN bytes2) as [X|_].
  { exfalso. destruct D3 as [?|Hr]; [lia|]. subst rest. cbn in Hb2'. unfold Q_MIN in X. lia. }
  (* [comment removed for export] *)
  assert (HI1 : INV [] (ex ++ taken) (set_qglob rest bytes2 st) mo).
  { replace (set_qglob rest bytes2 st) with (set_qglob rest bytes2 (set_qloc (a_qloc st) (a_qloc_bytes st) st)) by (rewrite set_qloc_eta; reflexivity).
    rewrite Hql, Hqlb.
    apply (INV_requeue [] [] (ex ++ taken) st [] 0 rest bytes2 mo HI).
    - rewrite Hqb. cbn [app]. rewrite <- app_assoc. eapply Permutation_trans; [|exact M1].
      rewrite <- D1. rewrite !qchunks_app. eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_refl.
    - rewrite Hqb, <- M2, <- D1. cbn [app]. rewrite !zlen_app. lia.
    - cbn [app]. rewrite <- D1 in M5. apply Forall_app in M5 as [M5a M5b]. apply Forall_app in M5a as [M5t M5r].
      apply Forall_app; split; [apply Forall_app; split; assumption| exact M5r].
    - reflexivity.
    - exact Hb2'. }
  apply (do_recycle_ok R P (ex ++ taken) [] (set_qglob rest bytes2 st) k mo HI1).
  - destruct HI1 as [HA1 _]. destruct (CH_bounds2 [] (ex ++ taken) (set_qglob rest bytes2 st) HA1) as [_ X]; [| unfold zlen; cbn; lia| cbn; lia| unfold SECM; lia].
    unfold qbatches. cbn [a_qloc a_qglob set_qglob]. rewrite Hql. cbn [app]. rewrite !bsum_app. subst gl. rewrite bsum_app in M3. lia.
  - eapply FAINV_frame; [| exact HFA]; intros; reflexivity.
  - rewrite VC_set_qglob. exact HVC.
  - cbn [a_space_beg a_ptr_array set_qglob]. split; assumption.
  - intros st' mo' HI' HQ' HFA' HVC'. destruct HQ' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). cbn in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8.
    rewrite VC_set_qglob in HVC'.
    apply Hk; auto; try congruence; try (split; congruence). rewrite Q6. destruct D3 as [?|Hr]; [lia|]. subst rest. cbn in Hb2'. unfold Q_MIN. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bsum_nonneg : forall bs, Forall batch_wf bs -> 0 <= bsum bs.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>15045132080.5 3901711215.14 67362234900.1300000100400=SS1HS2IH2B31H".
induction bs as [|b bs IH]; intros HB; [cbn; lia|]. apply Forall_cons_iff in HB as [(B1&B2&B3&B4) HB]. cbn. specialize (IH HB).
  assert (0 <= zsumc (b_chunks b)) by (apply zsumc_nonneg; eapply Forall_impl; [|exact B4]; cbv beta; intros; lia). unfold Q_BATCH_BYTES in B3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma drain_ok : forall R (P : R -> Model -> Prop) st (k : astate -> AM R) mo,
  INV [] [] st mo -> a_qloc_bytes st + a_qglob_bytes st <= 2^30 ->
  FAINV st -> VC st <= VCMAX -> SBP st ->                               (* [comment removed for export] *)
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st -> a_qloc st' = [] -> a_qloc_bytes st' = 0 ->
     0 <= a_qglob_bytes st' <= Q_MAX -> FAINV st' -> VC st' = VC st -> SBP st' -> atot (k st') mo' P) ->
  atot (drain st k) mo P.
Proof.
  intros R P st k mo HI HQ HFA HVC HSBP Hk. pose proof HI as [HA HM]. pose proof HA as (_ & _ & HBW & Hb1 & Hb2 & _).
  unfold drain. cbv zeta. cbn [a_qglob a_qglob_bytes a_qloc a_qloc_bytes set_qloc].
  set (st1 := set_qglob (a_qglob st ++ a_qloc st) (a_qglob_bytes st + a_qloc_bytes st) (set_qloc [] 0 st)).
  assert (HI1 : INV [] [] st1 mo).
  { unfold st1. apply (INV_requeue [] [] [] st [] 0 _ _ mo HI).
    - unfold qbatches. cbn [app]. rewrite !qchunks_app. apply Permutation_app_comm.
    - unfold qbatches. cbn [app]. rewrite !zlen_app. Local Ltac2 Set LiaHints.tbl := fun () => "0050>19294296526.3526751509411.2128312564169.2431114173809.2146951844549.2400000700@00T00U00aS2E22E5S3Hb13Hb2S3Hb13Hb23HBq6HsmallSS2HQ3Hb13Hb2".
lia.
    - unfold qbatches in HBW. cbn [app] in *. apply Forall_app in HBW as [X Y]. apply Forall_app; split; assumption.
    - reflexivity.
    - rewrite bsum_app. lia. }
  assert (HBq : 0 <= bsum (a_qglob st) /\ 0 <= bsum (a_qloc st)).
  { unfold qbatches in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X Y]. split; apply bsum_nonneg; assumption. }
  change (a_qglob_bytes st1) with (a_qglob_bytes st + a_qloc_bytes st).
  destruct (Z.ltb_spec Q_MAX (a_qglob_bytes st + a_qloc_bytes st)) as [Hbig|Hsmall].
  - apply (recycle_ok R P st1 k mo HI1); try reflexivity.
    + unfold st1. cbn. rewrite bsum_app. lia.
    + eapply FAINV_frame; [| exact HFA]; intros; reflexivity.
    + unfold st1. rewrite VC_set_qglob, VC_set_qloc. exact HVC.
    + exact HSBP.
    + intros st' mo' HI' E1 E2 E3 E4 E5 HFA' HVC' HSBP'. unfold st1 in HVC'. rewrite VC_set_qglob, VC_set_qloc in HVC'. apply Hk; auto. unfold Q_MIN, Q_MAX in *. lia.
  - apply Hk; auto; unfold st1; cbn; try reflexivity; try lia; try exact HSBP; try (eapply FAINV_frame; [| exact HFA]; intros; reflexivity).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma is_primary_7000 : is_primary 7000 = true. Proof. reflexivity. Qed.

#[using="Type"] Lemma enqueue_ok : forall R (P : R -> Model -> Prop) st ch n (k : astate -> AM R) mo,
  INV [ch] [] st mo -> chunk_size ch = n -> 0 <= n <= Q_MAX ->
  a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  FAINV st -> VC st + 2^19 <= VCMAX -> SBP st ->                        (* [comment removed for export] *)
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st ->
     a_qglob_bytes st' = a_qglob_bytes st ->
     a_qloc_bytes st <= a_qloc_bytes st' <= a_qloc_bytes st + n + Q_BATCH_BYTES -> FAINV st' -> VC st' <= VC st + 2^19 -> SBP st' -> atot (k st') mo' P) ->
  atot (enqueue st ch k) mo P.
Proof.
  intros R P st ch n k mo HI Hsz Hn Hql Hqg HFA HVC HSBP Hk.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf HW].
  Local Ltac2 Set LiaHints.tbl := fun () => "00O0>10524169866.4211550525402.3912191929400.5713968900832.4013968900839.5916107620244.5916135434596.3726237403908.4226289043207.412639509880.37 27428383543.3728718414661.4330686466952.3931819485077.4235292800527.4137015493299.4141672720490.3942220690860.4343513855161.5744137517657.4247621104938.5648361086668.4050865427797.5654005931079.2754008723932.395443559309.51 59606175150.4159815762309.3763797491228.5766373106166.3968359971148.4200000<00D00K00L00S00Z00[00g00k00l01001401801>01B01F01G01O01V01Z01d01e02602:02>02?02C02D02E02I02MS3Hql3Hqg2E2S3Hne2B2S2E22F2SS2E22F2S2E22F2SS3Hql3Hqg2E2S2E2SS2HnS2E2S2B3S2E21XS2E2S2E2FS3Hwf2E2S2E22F2S2E2S2Hn2E22F2SS2E24HVC04HVC12F2S2HnS2HnSS2E2SFS2B1S2E2".
assert (Hchsz : Forall (fun c => 0 <= chunk_size c <= Q_MAX) [ch]) by (constructor; [rewrite Hsz; lia| constructor]).
  (* [comment removed for export] *)
  assert (NEWB : forall st0, INV [ch] [] st0 mo -> a_live st0 = a_live st -> a_next st0 = a_next st -> a_qloc st0 = a_qloc st -> a_qloc_bytes st0 = a_qloc_bytes st ->
            a_qglob st0 = a_qglob st -> a_qglob_bytes st0 = a_qglob_bytes st -> FAINV st0 -> VC st0 = VC st -> SBP st0 ->
            atot (cache_alloc st0 K_BATCH_CLASS (fun st1 ok =>
                     if negb ok then aundef_ USpin (k st1)
                     else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (n + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1))) mo P).
  { intros st0 HI0 E1 E2 E3 E4 E5 E6 HFA0 HVC0 HSBP0. pose proof HI0 as [HA0 HM0].
    apply (cache_alloc_ok R P [ch] [] st0 K_BATCH_CLASS 7000 _ mo HI0 ltac:(lia) is_primary_7000 (eq_sym shell_class)).
    - apply (room_of_AINV (ATOP:=ATOP)); auto; [unfold K_BATCH_CLASS; lia | vm_compute; congruence | vm_compute; congruence | |].
      + unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA0 as (_ & _ & _ & B1 & B2 & _). rewrite <- B1, <- B2, E4, E6. unfold Q_CACHE, Q_MAX in *. lia.
      + change (size_of_class K_BATCH_CLASS) with 8192. rewrite cntP_cons, cntP_nil. destruct (is_prim_of K_BATCH_CLASS ch); lia.
    - destruct (CH_bounds [ch] [] st0 HA0) as [_ X]; [| | | unfold SECM; lia].
      + unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA0 as (_ & _ & _ & B1 & B2 & _). rewrite <- B1, <- B2, E4, E6. unfold Q_CACHE, Q_MAX in *. lia.
      + destruct ch; cbn; unfold zlen; cbn; lia.
      + destruct ch; cbn in *; lia.
    - exact HFA0.
    - rewrite HVC0. exact HVC.
    - exact HSBP0.
    - intros st1 mo1 HI1 HSB1 HFA1 HVC1. cbn [negb].
      assert (F : a_live st1 = a_live st /\ a_next st1 = a_next st /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st /\ a_qglob st1 = a_qglob st /\ a_qglob_bytes st1 = a_qglob_bytes st
                  /\ a_space_beg st1 = a_space_beg st0 /\ a_ptr_array st1 = a_ptr_array st0).
      { destruct HSB1 as [X|X]; destruct X as (S1&S2&_&_&_&L1&L2&L3&L4&L5&L6&_); [| unfold init_cache in *; destruct (a_cinit st0); cbn in *]; repeat split; congruence. }
      destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). destruct HSBP0 as [HSB00 HPA00].
      apply Hk; [| cbn [a_live set_qloc]; congruence| cbn [a_next set_qloc]; congruence| cbn [a_qglob_bytes set_qloc]; congruence| cbn [a_qloc_bytes set_qloc]; rewrite F4; unfold Q_BATCH_BYTES; lia
                | eapply FAINV_frame; [| exact HFA1]; intros; reflexivity | rewrite VC_set_qloc; lia | cbn [a_space_beg a_ptr_array set_qloc]; split; congruence].
      (* [comment removed for export] *)
      set (nb := mkABatch 1 (n + Q_BATCH_BYTES) [ch]).
      assert (Hnb : batch_wf nb).
      { unfold batch_wf, nb. cbn. unfold zlen. cbn. rewrite Hsz. unfold Q_BATCH. repeat split; try lia. exact Hchsz. }
      assert (HI2 : INV [] [nb] st1 mo1).
      { apply INV_close_batch; [|exact Hnb]. unfold nb. cbn [b_chunks rev app]. apply (INV_pc_perm [shell; ch]); [apply perm_swap| exact HI1]. }
      replace (set_qloc (a_qloc st1 ++ [nb]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1)
        with (set_qglob (a_qglob st1) (a_qglob_bytes st1) (set_qloc (a_qloc st1 ++ [nb]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1)) by (destruct st1; reflexivity).
      apply (INV_requeue [] [nb] [] st1 _ _ _ _ mo1 HI2).
      + unfold qbatches. cbn [app]. rewrite !qchunks_app. cbn. fold (qchunks (a_qloc st1 ++ a_qglob st1)). rewrite qchunks_app.
        eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|]. cbn. apply Permutation_refl.
      + unfold qbatches. cbn [app]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
      + destruct HI2 as [(_ & _ & HB2 & _) _]. unfold qbatches in HB2. cbn [app] in *. apply Forall_cons_iff in HB2 as [X Y]. apply Forall_app in Y as [Y1 Y2].
        apply Forall_app; split; [apply Forall_app; split; [exact Y1| constructor; [exact X| constructor]]| exact Y2].
      + destruct HI2 as [(_ & _ & _ & B1 & _) _]. cbn in B1. rewrite bsum_app, <- B1. cbn. lia.
      + destruct HI2 as [(_ & _ & _ & _ & B2 & _) _]. exact B2. }
  unfold enqueue. rewrite Hsz. cbv zeta.
  destruct (rev (a_qloc st)) as [|b rl] eqn:Hrev.
  - apply NEWB; auto.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [|Hne]; [apply NEWB; auto|].
    (* [comment removed for export] *)
    assert (Hql' : a_qloc st = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc st)), Hrev; reflexivity).
    assert (Hb : batch_wf b).
    { unfold qbatches in HBW. rewrite Hql' in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X _]. apply Forall_app in X as [_ X]. apply Forall_cons_iff in X as [X _]. exact X. }
    set (b' := mkABatch (b_count b + 1) (b_size b + n) (ch :: b_chunks b)).
    assert (Hb' : batch_wf b').
    { destruct Hb as (B1&B2&B3&B4). unfold batch_wf, b'. cbn. rewrite zlen_cons, Hsz. repeat split; try lia. constructor; [rewrite Hsz; lia| exact B4]. }
    apply Hk; [| reflexivity| reflexivity| reflexivity| cbn [a_qloc_bytes set_qloc]; unfold Q_BATCH_BYTES; lia
              | eapply FAINV_frame; [| exact HFA]; intros; reflexivity | rewrite VC_set_qloc; lia | exact HSBP].
    (* [comment removed for export] *)
    assert (HI1 : INV [ch] [b] (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)) mo).
    { apply (INV_requeue [ch] [] [b] st); auto.
      - unfold qbatches. rewrite Hql'. cbn [app]. rewrite !qchunks_app. cbn. rewrite app_nil_r. fold (qchunks (rev rl ++ a_qglob st)). rewrite qchunks_app.
        rewrite <- app_assoc. apply Permutation_app_swap_app.
      - unfold qbatches. rewrite Hql'. cbn [app]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
      - unfold qbatches in *. rewrite Hql' in HBW. cbn [app] in *. apply Forall_app in HBW as [X Y]. apply Forall_app in X as [X1 X2]. apply Forall_cons_iff in X2 as [X2 _].
        constructor; [exact X2|]. apply Forall_app; split; assumption.
      - rewrite Hb1, Hql', bsum_app. cbn. lia. }
    pose proof (INV_open_batch _ _ _ _ _ HI1) as HI2.
    assert (HI3 : INV [] [b'] (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)) mo).
    { apply INV_close_batch; [|exact Hb']. unfold b'. cbn [b_chunks]. cbn [rev]. rewrite <- app_assoc. cbn [app].
      apply (INV_pc_perm (rev (b_chunks b) ++ [shell; ch])); [| exact HI2].
      apply Permutation_app_head. apply perm_swap. }
    replace (set_qloc (rev (b' :: rl)) (a_qloc_bytes st + n) st)
      with (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl ++ [b']) (a_qloc_bytes st - b_size b + b_size b') (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)))).
    2:{ destruct st; cbn. unfold b', set_qloc, set_qglob. cbn. f_equal. lia. }
    apply (INV_requeue [] [b'] [] _ _ _ _ _ mo HI3).
    + unfold qbatches. cbn [app a_qloc a_qglob set_qglob set_qloc]. rewrite !qchunks_app. cbn. fold (qchunks (rev rl ++ a_qglob st)). rewrite qchunks_app.
      rewrite app_nil_r. rewrite <- app_assoc. rewrite (app_comm_cons). apply (Permutation_app_swap_app (qchunks (rev rl)) (ch :: b_chunks b)).
    + unfold qbatches. cbn [app a_qloc a_qglob set_qglob set_qloc]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
    + destruct HI3 as [(_ & _ & HB3 & _) _]. unfold qbatches in HB3 |- *. cbn [app a_qloc a_qglob set_qglob set_qloc] in *. apply Forall_cons_iff in HB3 as [X Y]. apply Forall_app in Y as [Y1 Y2].
      apply Forall_app; split; [apply Forall_app; split; [exact Y1| constructor; [exact X| constructor]]| exact Y2].
    + rewrite Hb1, Hql'. rewrite !bsum_app. unfold b'. cbn [bsum b_size]. lia.
    + exact Hb2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma size_of_class_nonneg : forall c, 1 <= c <= 31 -> 0 <= size_of_class c.
Proof.
  intros c Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0040=35497643387.644015172475.658836250519.76550410081.7 00000100200800>SSS2Hc1lS2Hc1n".
destruct (Z_le_dec 3 c); [apply budget_chk_ok; lia|].
  assert (c = 1 \/ c = 2) as [-> | ->] by lia; [change (size_of_class 1) with 32| change (size_of_class 2) with 64]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma INV_live_to_hand : forall st id ch mo,
  INV [] [] st mo -> (a_live st) !! id = Some ch ->
  INV [ch] [] (set_live (delete id (a_live st)) st) mo.
Proof.
  intros st id ch mo [HA HM] Hl. pose proof HA as (_ & HW0 & _).
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  assert (HPa : Permutation (all_chunks [ch] [] (set_next (a_next st) (set_live (delete id (a_live st)) st))) (all_chunks [] [] st)).
  { unfold all_chunks. cbn [app]. unfold live_chunks in *. cbn [a_live set_next set_live] in *.
    change (qbatches [] (set_next (a_next st) (set_live (delete id (a_live st)) st))) with (qbatches [] st).
    eapply Permutation_trans. 2:{ apply Permutation_app_tail. apply Permutation_sym. exact HPl. } cbn. apply Permutation_refl. }
  assert (E : set_live (delete id (a_live st)) st = set_next (a_next st) (set_live (delete id (a_live st)) st)) by (destruct st; reflexivity).
  rewrite E. split.
  - apply (AINV_live_perm []); auto.
    + intros id' ch' Hl'. destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). apply (Hid id' ch').
      destruct (N.eq_dec id' id) as [->|Hne]; [rewrite lookup_delete_eq in Hl'; discriminate|]. rewrite lookup_delete_ne in Hl' by congruence. exact Hl'.
    + destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLB). apply live_budget_list_iff in HLB. apply live_budget_list_iff.
      unfold live_chunks in *. cbn [a_live set_next set_live] in *.
      destruct HLB as (B1 & B2 & B3). unfold live_chunks in B1, B2, B3 |- *. cbn [a_live set_next set_live] in B1, B2, B3 |- *. split; [|split].
      * intros c Hc. specialize (B1 c Hc). rewrite (cntP_perm c _ _ HPl), cntP_cons in B1. pose proof (cntP_nonneg c (map snd (map_to_list (delete id (a_live st))))).
        pose proof (size_of_class_nonneg c Hc). destruct (is_prim_of c ch); nia.
      * unfold zlen in *. rewrite (Permutation_length (secs_perm _ _ HPl)) in B2. rewrite secs_cons, length_app in B2. Local Ltac2 Set LiaHints.tbl := fun () => "00?0>150060430.24  15833096338.2320311832818.1920311832818.2020313716200.2124926274299.1733773570348.2233783453552.2036196656970.2238493175293.1750822906301.2357745617343.2466203049950.2366742810639.248142693511.15 00000100200600700=00>00?00@00A00E00K00Z00[00a00bSSS2B3FS2B31XSFFSS2B2S4IHP0S6IHP0_16IHP0_2SS4IHP0S".
lia.
      * assert (EB : forall l l', Permutation l l' -> secbytes l = secbytes l') by (intros l l' P0; induction P0; cbn; try lia; [destruct x; lia| destruct x, y; lia]).
        rewrite (EB _ _ HPl) in B3. cbn in B3. destruct ch; cbn in B3; try lia.
        unfold all_chunks, live_chunks in HW0. cbn [app] in HW0. apply Forall_app in HW0 as [HW0 _].
        pose proof (Permutation_Forall HPl HW0) as X. apply Forall_cons_iff in X as [X _]. cbn in X. lia.
  - apply (AMI_perm (CH [] [] st)).
    + unfold CH. apply secs_perm. apply Permutation_sym. exact HPa.
    + apply (AMI_mono _ st); auto. unfold commit_bytes, csum, get_cls. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition free_post (st : astate) (id : AsanCtrl.aptr) (st' : astate) (mo' : Model) : Prop :=
  INV [] [] st' mo' /\ a_live st' = delete id (a_live st) /\ a_next st' = a_next st
  /\ a_qloc_bytes st' <= Q_CACHE /\ a_qglob_bytes st' <= Q_MAX
  /\ FAINV st' /\ VC st' <= VC st + 2^19.                                (* [comment removed for export] *)

#[using="Type"] Theorem afree_core : forall st mo id ch,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> (a_live st) !! id = Some ch ->
  FAINV st -> VC st + 2^19 <= VCMAX -> SBP st ->                         (* [comment removed for export] *)
  atot (afree st (Some id)) mo (free_post st id).
Proof.
  intros st mo id ch HI Hql Hqg Hl HFA HVC HSBP.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  pose proof (INV_live_to_hand st id ch mo HI Hl) as HI1.
  set (st1 := set_live (delete id (a_live st)) st) in *.
  assert (Hwf : chunk_wf ch).
  { destruct HI1 as [HA1 _]. destruct HA1 as (_ & HW1 & _). rewrite all_chunks_cons in HW1. apply Forall_cons_iff in HW1 as [X _]. exact X. }
  Local Ltac2 Set LiaHints.tbl := fun () => "00G0>18939345579.4922322045011.3223640271624.3823644466957.3828707924252.3230693498206.4233061727918.4034930053516.403828661766.38 3830755032.42 43979785036.3144127027200.3146150050660.2546150050660.2651233554202.4955472255570.4958528998088.4261549098435.3061737395000.4264575650485.3065272031088.4065700439599.3068357878549.3100000700=00L00Y00Z00b01101<01E01N01Q01R01W01\01m02702C02P02\02m03F03K03LS2E22F2S4HszbS2E26Hsmall3Hq2S3HVC2E24HVC2SS3Hqg2Q2S3Hb13HQB2E22E4S3Hqg2E22E3S2E24HVC2S2Q24HVC2S1XSS3HwfS3HwfS2E24HVC22F24HVC3S2E22F22F5S3Hb13HQB2Q2S4Hszb6HsmallS3Hql3Hqg2Q2S3Hql3Hqg3Hb13Hb2S3Hql3Hqg6Hsmall2E22E32E4S3HVCS".
assert (Hszb : 0 <= chunk_size ch <= 2^30) by (destruct ch; cbn in Hwf |- *; lia).
  assert (HQB : 0 <= bsum (a_qloc st) /\ 0 <= bsum (a_qglob st)).
  { unfold qbatches in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X Y]. split; apply bsum_nonneg; assumption. }
  unfold afree. rewrite Hl. fold st1. cbv zeta.
  (* [comment removed for export] *)
  assert (AFTER : forall st2 mo2, INV [] [] st2 mo2 -> a_live st2 = a_live st1 -> a_next st2 = a_next st1 ->
            0 <= a_qloc_bytes st2 -> a_qloc_bytes st2 + a_qglob_bytes st2 <= 2^30 -> a_qglob_bytes st2 <= Q_MAX ->
            FAINV st2 -> VC st2 <= VC st + 2^19 -> SBP st2 ->
            atot (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2) mo2 (free_post st id)).
  { intros st2 mo2 HI2 E1 E2 Hq0 Hq1 Hq2 HFA2 HVC2 HSBP2. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [Hbig|Hsmall].
      apply (drain_ok _ _ st2 _ mo2 HI2 Hq1 HFA2 ltac:(lia) HSBP2). intros st3 mo3 HI3 F1 F2 F3 F4 F5 HFA3 HVC3 HSBP3. apply atotal_ret. unfold free_post.
      rewrite F1, F2, E1, E2, F4. unfold st1. cbn. unfold Q_CACHE. split; [exact HI3|]. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [lia|]. split; [exact HFA3| lia].
    - apply atotal_ret. unfold free_post. rewrite E1, E2. unfold st1. cbn. split; [exact HI2|]. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [lia|]. split; [exact HFA2| lia]. }
  assert (HFA1 : FAINV st1) by (eapply FAINV_frame; [| exact HFA]; intros; reflexivity).
  assert (HVC1 : VC st1 = VC st) by reflexivity.
  destruct (Z.leb_spec (chunk_size ch) Q_MAX) as [Hsmall|Hbig].
  - (* [comment removed for export] *)
    apply (enqueue_ok _ _ st1 ch (chunk_size ch) _ mo HI1 eq_refl ltac:(lia));
      [unfold st1; cbn; assumption| unfold st1; cbn; assumption| exact HFA1| rewrite HVC1; exact HVC| exact HSBP|].
    intros st2 mo2 HI2 E1 E2 E3 E4 HFA2 HVC2 HSBP2. unfold st1 in E1, E2, E3, E4. cbn [a_live a_next a_qglob_bytes a_qloc_bytes set_live] in E1, E2, E3, E4.
    rewrite HVC1 in HVC2.
    apply AFTER; auto; rewrite <- ?Hb1 in E4; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *; lia.
  - (* [comment removed for export] *)
    apply (recycle_chunk_ok _ _ [] [] st1 ch _ mo HI1).
    + destruct HI1 as [HA1 _]. enough (X : zsum2 (CH [ch] [] st1) <= 2^32 + 2^31) by (unfold SECM; lia). apply (CH_bounds (ATOP:=ATOP)); auto.
      * unfold qbatches, st1. cbn [app a_qloc a_qglob set_live]. rewrite bsum_app. unfold Q_CACHE, Q_MAX in *. lia.
      * destruct ch; cbn; unfold zlen; cbn; lia.
      * destruct ch; cbn in *; lia.
    + exact HFA1.
    + rewrite HVC1. lia.
    + exact HSBP.
    + intros st2 mo2 HI2 HQ HFA2 HVC2. pose proof (SBP_qframe _ _ HQ HSBP) as HSBP2.
      destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). unfold st1 in Q1, Q2, Q3, Q4, Q5, Q6. cbn [a_live a_next a_qglob_bytes a_qloc_bytes a_qloc a_qglob set_live] in Q1, Q2, Q3, Q4, Q5, Q6.
      rewrite HVC1 in HVC2.
      apply AFTER; auto; rewrite ?Q4, ?Q6; unfold Q_CACHE, Q_MAX in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End WithResv.

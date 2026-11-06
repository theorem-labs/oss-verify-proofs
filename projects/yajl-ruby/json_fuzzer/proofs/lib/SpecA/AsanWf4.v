(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf2 AsanWf3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section WF.
Variable E : aenv.
Variable P : list Z.        (* [comment removed for export] *)
Variable D : list batch.    (* [comment removed for export] *)
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma carved_blocks_disjoint : forall s c a c' a',
  1 <= c <= kLargestClassID -> 1 <= c' <= kLargestClassID -> wf_regions E s ->
  carved E s c a -> carved E s c' a' -> (c = c' /\ a = a') \/ a + class_size c <= a' \/ a' + class_size c' <= a.
Proof.
  intros s c a c' a' Hc Hc' WR C1 C2.
  pose proof (class_size_mod c Hc) as [_ S1]. pose proof (class_size_mod c' Hc') as [_ S2].
  destruct (Z.eq_dec c c') as [<-|NE].
  - destruct C1 as (k & Hk & -> & _). destruct C2 as (k' & Hk' & -> & _).
    destruct (Z.lt_trichotomy k k') as [LT|[->|GT]].
    + right; left. assert ((k + 1) * class_size c <= k' * class_size c) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    + left; split; reflexivity.
    + right; right. assert ((k' + 1) * class_size c <= k * class_size c) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - right. pose proof (carved_range E s c a Hc WR C1) as [L1 U1]. pose proof (carved_range E s c' a' Hc' WR C2) as [L2 U2].
    unfold region_beg, kFreeArrayOffset, kRegionSize, kLargestClassID in *.
    destruct (Z.lt_trichotomy c c') as [LT|[EQ|GT]]; [| exfalso; exact (NE EQ) |]; nia.
Qed.

(* [comment removed for export] *)
Lemma carved_in_space : forall s c a, 1 <= c <= kLargestClassID -> wf_regions E s -> carved E s c a ->
  SB + kRegionSize <= a /\ a + class_size c <= SB + kSpaceSize.
Proof.
  intros s c a Hc WR C. pose proof (carved_range E s c a Hc WR C) as [L U].
  unfold region_beg, kFreeArrayOffset, kRegionSize, kLargestClassID, kSpaceSize in *. nia.
Qed.

(* [comment removed for export] *)
Lemma rz_lt_class : forall n, 0 <= n <= 64512 -> rz_size n + 8 <= class_size (malloc_class n).
Proof.
  intros n Hn. pose proof (malloc_class_ok n Hn) as [_ LE]. unfold needed1 in LE.
  pose proof (rounded_ge n). lia.
Qed.

Lemma map_size_ge : forall n, needed n + kPageSize <= map_size n.
Proof. intros n. unfold map_size. pose proof (round_up_ge (needed n) kPageSize ltac:(unfold kPageSize; lia)). lia. Qed.

Lemma needed_ge : forall n, n + rz_size n <= needed n.
Proof.
  intros n. unfold needed, needed1. pose proof (rounded_ge n). pose proof (rz_size_pos n).
  destruct (from_primary n); lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_beg_loc : forall s cb cm, AWF s -> as_chunks s !! cb = Some cm ->
  match cm_prim cm with
  | Some c => 1 <= c <= kLargestClassID /\ carved E s c (cm_alloc_beg cm)
              /\ cm_alloc_beg cm <= cb /\ cb + 8 < cm_alloc_beg cm + class_size c
  | None => exists sc, In sc (as_sec s) /\ sc_map_beg sc <= cb /\ cb + 8 < sc_map_beg sc + sc_map_size sc
              /\ (sc_map_beg sc + sc_map_size sc <= SB \/ SB + kSpaceSize <= sc_map_beg sc)
  end.
Proof.
  intros s cb cm WF Hcm. destruct WF as (WE & WR & WC & [K1 _] & WQ & WS & WD).
  destruct (K1 cb cm Hcm) as (A & B & C & D0 & _).
  unfold cm_chunk_beg, cm_user_beg, kChunkHeaderSize in A. rewrite C in A.
  change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in A.
  pose proof (rz_size_pos (cm_n cm)) as RP.
  destruct (cm_prim cm) as [c|].
  - destruct D0 as (D1 & D2 & D3 & _).
    pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1) as LE.
    assert (Hc : 1 <= c <= kLargestClassID) by (subst c; apply malloc_class_ok; lia).
    pose proof (rz_lt_class (cm_n cm) ltac:(lia)) as RZ. rewrite <- D2 in RZ.
    split; [exact Hc|]. split; [exact D3|]. lia.
  - destruct D0 as (D1 & sc & Hsc & Hab & Hms & Hnd). exists sc. split; [exact Hsc|].
    destruct WS as (_ & _ & S3 & _). destruct (S3 sc Hsc) as (_ & _ & _ & P1 & P2 & P3 & _).
    pose proof (map_size_ge (cm_n cm)) as MG. pose proof (needed_ge (cm_n cm)) as NG.
    rewrite <- Hms in MG. unfold kPageSize in *. split; [lia|]. split; [lia| exact P3].
Qed.

(* [comment removed for export] *)
Lemma avail_chunk_key_fresh : forall s c ab n,
  AWF s -> 1 <= c <= kLargestClassID -> avail E D s c ab -> 0 <= n <= 64512 -> c = malloc_class n ->
  as_chunks s !! (ab + rz_size n - kChunkHeaderSize) = None.
Proof.
  intros s c ab n WF Hc (CV & NF & NC & [NB _]) Hn Hcl.
  destruct (as_chunks s !! (ab + rz_size n - kChunkHeaderSize)) as [cm|] eqn:Hcm; [|reflexivity]. exfalso.
  pose proof (chunk_beg_loc s _ cm WF Hcm) as LOC.
  pose proof WF as X. destruct X as (WE & WR & _).
  pose proof (rz_lt_class n Hn) as RZ. rewrite <- Hcl in RZ. pose proof (rz_size_pos n) as RP.
  unfold kChunkHeaderSize in *.
  destruct (cm_prim cm) as [c'|].
  - destruct LOC as (Hc' & CV' & L1 & L2).
    destruct (carved_blocks_disjoint s c ab c' (cm_alloc_beg cm) Hc Hc' WR CV CV') as [[<- EQ]|[DJ|DJ]]; [| lia | lia].
    apply NB. exists (ab + rz_size n - 16), cm. split; [exact Hcm| symmetry; exact EQ].
  - destruct LOC as (sc & Hsc & L1 & L2 & OUT).
    pose proof (carved_in_space s c ab Hc WR CV) as [I1 I2]. unfold kRegionSize, kSpaceSize in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma remap_range_pos : forall u L, needs_remap L = true -> 0 < snd (remap_range u L).
Proof.
  intros u L H. unfold needs_remap, kClearShadowMmapThreshold in H. apply Z.leb_le in H.
  unfold remap_range. cbn [snd]. unfold round_down, kPageSize.
  pose proof (round_up_lt (mem_to_shadow u) 4096 ltac:(lia)) as U.
  set (x := mem_to_shadow u + L / 8). pose proof (Z.mul_div_le x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  pose proof (Z.div_mod x 4096 ltac:(lia)). lia.
Qed.

Lemma poison_zero_frame : forall (PP : astate -> Prop) u L,
  hoare PP (poison_zero u L) (fun s' _ => PP s').
Proof.
  intros PP u L. unfold poison_zero. apply hoare_ret; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wf_chunk_frame : forall s s' cb cm,
  as_regions s' = as_regions s -> as_cache s' = as_cache s -> as_tq s' = as_tq s -> as_gq s' = as_gq s -> as_sec s' = as_sec s ->
  wf_chunk E P D s cb cm -> wf_chunk E P D s' cb cm.
Proof.
  intros s s' cb cm HR HC HT HG HS W.
  unfold wf_chunk, carved, in_free, in_cache, is_batch, all_batches, region_of, get_region, get_cache in *.
  rewrite HR, HC, HT, HG, HS. exact W.
Qed.

Lemma wf_cache_same : forall s s', as_regions s' = as_regions s -> as_cache s' = as_cache s -> as_cache_inited s' = as_cache_inited s ->
  wf_cache E s -> wf_cache E s'.
Proof.
  intros s s' HR HC HI W. unfold wf_cache, carved, region_of, get_region, get_cache in *. rewrite HR, HC, HI. exact W.
Qed.

Lemma AWf_register_chunk : forall s cb cm f,
  AWF s -> as_chunks s !! cb = None -> wf_chunk E P D s cb cm -> untracked D s (cm_alloc_beg cm) ->
  AWF (upd_dead f (upd_chunks (fun m => <[cb := cm]> m) s)).
Proof.
  intros s cb cm f WF NONE WCM [NCB NBA].
  set (s' := upd_dead f _).
  assert (HK : as_chunks s' = <[cb := cm]> (as_chunks s)) by reflexivity.
  assert (OLD : forall cb' cm', as_chunks s !! cb' = Some cm' -> cb' <> cb /\ as_chunks s' !! cb' = Some cm').
  { intros cb' cm' H. assert (NE : cb' <> cb) by (intros ->; rewrite NONE in H; discriminate).
    split; [exact NE|]. rewrite HK, lookup_insert_ne by auto. exact H. }
  assert (ICB : forall a, is_chunk_block s' a -> a = cm_alloc_beg cm \/ is_chunk_block s a).
  { intros a (cb' & cm' & H & Ha). rewrite HK in H. destruct (Z.eq_dec cb cb') as [<-|NE].
    - rewrite lookup_insert_eq in H. injection H as <-. left; symmetry; exact Ha.
    - rewrite lookup_insert_ne in H by auto. right. exists cb', cm'. auto. }
  assert (CUS : forall cb', as_chunks s !! cb' <> None -> chunk_used_size s' cb' = chunk_used_size s cb').
  { intros cb' H. unfold chunk_used_size. rewrite HK. destruct (Z.eq_dec cb cb') as [<-|NE]; [exfalso; exact (H NONE)|].
    rewrite lookup_insert_ne by auto. reflexivity. }
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  assert (BATB : forall b, In b (all_batches D s) -> ~ is_chunk_block s (b_addr b) -> ~ is_chunk_block s' (b_addr b)).
  { intros b Hb NB X. destruct (ICB _ X) as [EQ|Y]; [| exact (NB Y)]. apply NBA. exists b. split; [exact Hb| exact EQ]. }
  split; [exact WE|]. split; [eapply wf_regions_same; [| exact WR]; reflexivity|].
  split; [eapply wf_cache_same; [| | | exact WC]; reflexivity|].
  split; [|split; [|split; [exact WS| exact WD]]].
  - (* [comment removed for export] *) split.
    + intros cb0 cm0 H. rewrite HK in H. destruct (Z.eq_dec cb cb0) as [<-|NE].
      * rewrite lookup_insert_eq in H. injection H as <-. eapply wf_chunk_frame; [| | | | | exact WCM]; reflexivity.
      * rewrite lookup_insert_ne in H by auto. eapply wf_chunk_frame; [| | | | | exact (K1 _ _ H)]; reflexivity.
    + intros cb1 cm1 cb2 cm2 H1 H2 NE. rewrite HK in H1, H2.
      destruct (Z.eq_dec cb cb1) as [<-|NE1]; destruct (Z.eq_dec cb cb2) as [<-|NE2].
      * exfalso; exact (NE eq_refl).
      * rewrite lookup_insert_eq in H1. injection H1 as <-. rewrite lookup_insert_ne in H2 by auto.
        intros EQ. apply NCB. exists cb2, cm2. split; [exact H2| symmetry; exact EQ].
      * rewrite lookup_insert_eq in H2. injection H2 as <-. rewrite lookup_insert_ne in H1 by auto.
        intros EQ. apply NCB. exists cb1, cm1. split; [exact H1| exact EQ].
      * rewrite lookup_insert_ne in H1 by auto. rewrite lookup_insert_ne in H2 by auto. exact (K2 _ _ _ _ H1 H2 NE).
  - (* [comment removed for export] *) unfold wf_quarantine. change (all_batches D s') with (all_batches D s).
    change (as_tq s') with (as_tq s). change (as_gq s') with (as_gq s).
    split; [|split; [|split; [exact Q2| exact Q3]]].
    + intros b Hb. destruct (Q1 b Hb) as [(B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) NB]. split; [|exact NB].
      assert (HbA : In b (all_batches D s)) by (unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact (BATB b HbA B4)|]. split; [exact B5|].
      split.
      { rewrite B6. f_equal. clear -B8 CUS. induction (b_items b) as [|i l IH]; [reflexivity|]. cbn.
        rewrite CUS; [| destruct (B8 i (or_introl eq_refl)) as (cm' & i' & j' & H & _); rewrite H; discriminate].
        rewrite IH; [reflexivity|]. intros cb' H'. apply B8. right; exact H'. }
      split; [exact B7|].
      intros cb' H'. destruct (B8 cb' H') as (cm' & i' & j' & H & Hs). exists cm', i', j'. split; [|exact Hs].
      exact (proj2 (OLD _ _ H)).
    + intros b Hb. destruct (QD b Hb) as (B1 & B2 & B3 & B4 & B7).
      assert (HbA : In b (all_batches D s)) by (unfold all_batches; apply in_app_iff; right; apply in_app_iff; right; exact Hb).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact (BATB b HbA B4)| exact B7].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma req_geom : forall n, rz_log (req n) = rz_log n /\ needed1 (req n) = needed1 n /\ from_primary (req n) = from_primary n
  /\ needed (req n) = needed n /\ 1 <= req n.
Proof.
  intros n. unfold req. destruct (Z.le_gt_cases 1 n).
  - rewrite Z.max_l by lia. repeat split; lia.
  - rewrite Z.max_r by lia.
    assert (RZ : rz_log n = rz_log 1) by (unfold rz_log; rewrite !(proj2 (Z.leb_le _ _)) by lia; reflexivity).
    assert (N1 : needed1 n = needed1 1).
    { unfold needed1, rounded, rz_size. rewrite RZ. unfold kChunkHeader2Size. rewrite Z.max_r by lia. reflexivity. }
    assert (FP : from_primary n = from_primary 1) by (unfold from_primary; rewrite N1; reflexivity).
    unfold needed. rewrite FP, N1. unfold rz_size. rewrite RZ. repeat split; lia.
Qed.

Lemma avail_frame : forall s s' c a,
  as_regions s' = as_regions s -> as_cache s' = as_cache s -> as_chunks s' = as_chunks s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  avail E D s c a -> avail E D s' c a.
Proof.
  intros s s' c a HR HC HK HT HG AV.
  unfold avail, untracked, carved, in_free, in_cache, is_chunk_block, is_batch, all_batches, region_of, get_region, get_cache in *.
  rewrite HR, HC, HK, HT, HG. exact AV.
Qed.

(* [comment removed for export] *)
Definition malloc_pre (s : astate) (n : Z) : Prop :=
  if from_primary n then room s (class_id (needed1 n)) else n_chunks s < kChunksBlockCount.

(* [comment removed for export] *)
Definition new_chunk (ab n id : Z) : chunkmeta :=
  mkCM ab (rz_log n) (req n) (if from_primary n then Some (class_id (needed1 n)) else None) (CAllocated id).

Lemma amalloc_core_prim_spec : forall s0 key n,
  depot_ok E s0 key -> 0 <= n -> from_primary n = true -> AWF s0 -> malloc_pre s0 n ->
  hoare (fun s => s = s0) (amalloc_core E key n)
    (fun s' r => AWF s' /\ depot_n_ids E s' <= depot_n_ids E s0 + 1 /\
       match r with
       | None => as_chunks s' = as_chunks s0
       | Some p => exists ab id, p = ab + rz_size n /\ 1 <= id
                   /\ as_chunks s0 !! (p - kChunkHeaderSize) = None
                   /\ as_chunks s' = <[p - kChunkHeaderSize := new_chunk ab n id]> (as_chunks s0)
                   /\ carved E s' (class_id (needed1 n)) ab /\ p mod 16 = 0
       end).
Proof.
  intros s0 key n HK Hn PR WF PRE. unfold malloc_pre in PRE. rewrite PR in PRE.
  pose proof (proj1 (from_primary_iff n Hn) PR) as LE.
  pose proof (malloc_class_ok n ltac:(lia)) as [Hc _]. unfold malloc_class in Hc.
  set (c := class_id (needed1 n)) in *.
  unfold amalloc_core. rewrite PR.
  unfold acheck. replace (n <? 2 ^ 40) with true by (symmetry; apply Z.ltb_lt; lia).
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s0); auto|]. intros [].
  apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->). set (s0' := upd_nprimc _ _ s0).
  assert (WF0' : AWF s0') by (eapply AWf_same_core; [| exact WF]; unfold same_core; repeat split; reflexivity).
  change (as_chunks s0) with (as_chunks s0').
  eapply hoare_bind; [apply (cache_pop_spec E P D s0' c Hc WF0' PRE)|].
  intros r. apply hoare_pre. intros s1 (WF1 & PF1 & CV1 & OC1 & R1).
  destruct PF1 as (HK1 & _ & _ & _ & _ & HKy1 & _).
  assert (HK1' : depot_ok E s1 key) by (unfold depot_ok, depot_n_ids in *; rewrite HKy1; exact HK).
  destruct r as [ab|].
  2:{ apply hoare_upd_bind. apply hoare_ret. intros s' (s & -> & ->).
      split; [eapply AWf_same_core; [apply same_core_upd_oom| exact WF1]|]. split; [unfold depot_n_ids in *; cbn; rewrite HKy1; cbn; lia|]. cbn. exact HK1. }
  destruct R1 as (HI1 & AV1 & (x & Hx & Mx)).
  eapply hoare_bind; [apply (depot_put_wf E P D s1 key HK1' WF1)|].
  intros id. apply hoare_pre. intros s2 (WF2 & (SR & SC & SI & SK & ST & SG & SS & SP) & ID & NID).
  assert (AV2 : avail E D s2 c ab) by (eapply avail_frame; [..|exact AV1]; assumption).
  set (cb := ab + rz_size n - kChunkHeaderSize).
  assert (NONE : as_chunks s2 !! cb = None).
  { subst cb. apply (avail_chunk_key_fresh s2 c ab n WF2 Hc AV2 ltac:(lia)). reflexivity. }
  apply hoare_get_bind. intros s ->. rewrite NONE.
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s2); auto|]. intros []. apply hoare_pre. intros s ->.
  apply hoare_upd_bind. apply hoare_pre. intros s3 (s & -> & ->).
  set (cm := mkCM ab (rz_log n) (req n) (Some c) (CAllocated id)).
  set (s3 := upd_dead _ (upd_chunks _ s2)).
  pose proof (req_geom n) as (G1 & G2 & G3 & G4 & G5).
  assert (WCM : wf_chunk E P D s2 cb cm).
  { destruct AV2 as (CV & NF & NC & NCB & NB). unfold wf_chunk. subst cm; cbn [cm_n cm_prim cm_state cm_rz_log cm_alloc_beg].
    split; [unfold cm_chunk_beg, cm_user_beg; cbn [cm_rz_log cm_alloc_beg]; subst cb; unfold rz_size; reflexivity|].
    split; [clear -G5 LE Hn; unfold req in *; lia|]. split; [symmetry; exact G1|]. split; [|exact ID].
    split; [rewrite G3; exact PR|]. split; [unfold malloc_class; rewrite G2; reflexivity|].
    split; [exact CV|]. split; [exact NF|]. split; [exact NC| exact NB]. }
  assert (WF3 : AWF s3).
  { subst s3. replace (ab + rz_size n - kChunkHeaderSize) with cb by reflexivity.
    apply AWf_register_chunk; [exact WF2| exact NONE| exact WCM|]. destruct AV2 as (_ & _ & _ & U). exact U. }
  eapply hoare_bind; [apply (poison_zero_frame (fun s => s = s3)); reflexivity|]. intros [].
  apply hoare_pre. intros s ->.
  apply hoare_upd_bind. apply hoare_ret. intros s' (s & -> & ->).
  split; [eapply AWf_same_core; [apply same_core_upd_ts| exact WF3]|].
  split; [unfold depot_n_ids in *; cbn; rewrite HKy1 in NID; cbn in NID; lia|].
  exists ab, id. split; [reflexivity|]. split; [exact ID|].
  replace (ab + rz_size n - kChunkHeaderSize) with cb by reflexivity.
  split; [rewrite <- HK1, <- SK; exact NONE|].
  split; [cbn; rewrite SK, HK1; unfold new_chunk; rewrite PR; reflexivity|].
  split.
  - destruct AV2 as (CV & _). unfold carved, region_of in *. cbn. exact CV.
  - destruct AV2 as ((k & Hk & Hab & _) & _). rewrite Hab. unfold region_beg, kRegionSize.
    destruct WF as ((SBM & _) & _). pose proof (class_size_mod c Hc) as [CM _]. pose proof (rz_size_mod16 n) as RM.
    rewrite <- Z.add_assoc, <- Z.add_assoc. rewrite Z.add_mod by lia.
    replace (SB mod 16) with 0.
    2:{ symmetry. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SBM; [|lia]. destruct SBM as [q Hq]. exists (q * 2^12). lia. }
    rewrite Z.add_0_l, Z.mod_mod by lia. rewrite Z.add_mod by lia.
    replace ((c * 2 ^ 32) mod 16) with 0 by (symmetry; apply Z.mod_divide; [lia|]; exists (c * 2^28); lia).
    rewrite Z.add_0_l, Z.mod_mod by lia. rewrite Z.add_mod, RM, Z.add_0_r, Z.mod_mod by lia.
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in CM; [|lia]. destruct CM as [q Hq]. exists (k * q * 2). lia.
Qed.

End WF.
End RC__1.

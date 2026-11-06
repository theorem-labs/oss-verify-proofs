(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanKern AsanDepot
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RCA.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).

(* [comment removed for export] *)
Lemma arep_batch_list_indep : forall s1 s2 l m, arep_batch_list segs s1 l m -> arep_batch_list segs s2 l m.
Proof. intros s1 s2 l m. induction l as [|b l IH]; cbn; [intros X; exact X|]. intros [H1 H2]. split; [exact H1| exact (IH H2)]. Qed.

(* [comment removed for export] *)
Lemma ARep_thr_xfer : forall s s' m,
  as_regions s' = as_regions s -> as_cache_inited s' = as_cache_inited s ->
  as_ptr_committed s' = as_ptr_committed s -> as_sec s' = as_sec s -> as_sec_stale s' = as_sec_stale s -> as_sec_stats s' = as_sec_stats s ->
  as_glob_allocated s' = as_glob_allocated s -> as_glob_mapped s' = as_glob_mapped s -> as_oom s' = as_oom s ->
  as_chunks s' = as_chunks s -> as_dead s' = as_dead s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  as_keys s' = as_keys s -> as_frames s' = as_frames s -> as_ia_inited s' = as_ia_inited s ->
  as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s -> as_store_stored s' = as_store_stored s -> as_ndepot_ins s' = as_ndepot_ins s ->
  arep_instance segs E s m -> arep_regioninfo segs E s m -> arep_region_mem segs E s m -> arep_thread segs E s' m ->
  arep_secondary segs E s m -> arep_chunks segs s m -> arep_batches segs s m -> arep_depot (DepotR segs E) s m ->
  arep_globals segs E s m -> arep_shadow segs E s m -> AREP s' m.
Proof.
  intros s s' m. destruct s, s'; cbn. intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.
  intros RA RB RC RD' RE RF RG RH RI RJ.
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD'|]. split; [exact RE|]. split; [exact RF|].
  split; [destruct RG as [RG1 RG2]; split; eapply arep_batch_list_indep; eassumption|]. split; [exact RH|]. split; [exact RI| exact RJ].
Qed.

(* [comment removed for export] *)
Section POP.
Variables (n : Z) (s : astate).
#[warnings="-notation-for-abbreviation"] Notation c := (hc n).
#[warnings="-notation-for-abbreviation"] Notation s' := (pop_st n s).
Lemma pop_cache : as_cache s' = <[c := removelast (get_cache s c)]> (as_cache s). Proof. destruct s; reflexivity. Qed.
Lemma pop_get_cache : forall c', get_cache s' c' = if decide (c' = c) then removelast (get_cache s c) else get_cache s c'.
Proof. intros c'. unfold get_cache at 1. rewrite pop_cache. destruct (decide (c' = c)) as [->|NE]; [rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. Qed.
Lemma pop_cache_inited : as_cache_inited s' = as_cache_inited s. Proof. destruct s; reflexivity. Qed.
Lemma pop_cache_allocated : as_cache_allocated s' = as_cache_allocated s + class_size c. Proof. destruct s; reflexivity. Qed.
Lemma pop_cache_mapped : as_cache_mapped s' = as_cache_mapped s. Proof. destruct s; reflexivity. Qed.
Lemma pop_ts : as_ts s' = as_ts s. Proof. destruct s; reflexivity. Qed.
Lemma pop_tq : as_tq s' = as_tq s. Proof. destruct s; reflexivity. Qed.
Lemma pop_regions : as_regions s' = as_regions s. Proof. destruct s; reflexivity. Qed.
Lemma pop_sec : as_sec s' = as_sec s. Proof. destruct s; reflexivity. Qed.
Lemma pop_chunks : as_chunks s' = as_chunks s. Proof. destruct s; reflexivity. Qed.
Lemma pop_nprim : as_nprim_ever s' = as_nprim_ever s + 1. Proof. destruct s; reflexivity. Qed.
Lemma pop_residue : as_residue s' = as_residue s. Proof. destruct s; reflexivity. Qed.
Lemma pop_ndepot : as_ndepot_ins s' = as_ndepot_ins s. Proof. destruct s; reflexivity. Qed.
Lemma pop_node_blocks : as_node_blocks s' = as_node_blocks s. Proof. destruct s; reflexivity. Qed.
Lemma pop_store_blocks : as_store_blocks s' = as_store_blocks s. Proof. destruct s; reflexivity. Qed.
Lemma pop_ptr : as_ptr_committed s' = as_ptr_committed s. Proof. destruct s; reflexivity. Qed.
Lemma pop_keys : as_keys s' = as_keys s. Proof. destruct s; reflexivity. Qed.
Lemma pop_frames : as_frames s' = as_frames s. Proof. destruct s; reflexivity. Qed.
Lemma tq_bytes_pop : tq_bytes s' = tq_bytes s. Proof. destruct s; reflexivity. Qed.
End POP.

(* [comment removed for export] *)
Section CAPOP.
Variables (n : Z) (s : astate) (m m' : mem) (lo : Z).
#[warnings="-notation-for-abbreviation"] Notation c := (hc n).
#[warnings="-notation-for-abbreviation"] Notation s' := (pop_st n s).
#[warnings="-notation-for-abbreviation"] Notation ROWc := (T + kThrCache + kPerClassSize * c).
#[warnings="-notation-for-abbreviation"] Notation CST := (T + kThrCacheStats + 16).

(* [comment removed for export] *)
Definition FPWca (z : Z) : Prop := lo <= z \/ (ROWc <= z < ROWc + 4) \/ (CST <= z < CST + 8).

Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWca z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis REP : AREP s m.
Hypothesis WF : AWf E [] [] s.
Hypothesis BS : blocks_sep E s.
Hypothesis Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.
Hypothesis IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Hypothesis IMG_LO : 0x10000 <= fst (ae_img E).
Hypothesis IMG_LOW : forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
Hypothesis HCc : 1 <= c < kNumClasses.
Hypothesis Hl : get_cache s c <> [].
Hypothesis CI : as_cache_inited s = true.
(* [comment removed for export] *)
Hypothesis NC_row : RW m' ROWc [C4 (zw (zlen (get_cache s c) - 1))].
Hypothesis NC_cst : RW m' CST [C8 (zw (as_cache_allocated s + class_size c))].

(* [comment removed for export] *)
Lemma fp_range : forall a, arep_fp E (DepotFP E) s a -> 0 <= a < alloc_ceiling.
Proof.
  intros a Ha. split; [| exact (fp_below_ceiling E (DepotFP E) [] [] IMG_IN (DepotFP_where E) s a WF BS Ha)].
  destruct (fp_locate E (DepotFP E) [] [] IMG_IN (DepotFP_where E) s a WF BS Ha) as [X|[[X _]|[X _]]].
  - destruct X as (r & Hr & R). pose proof (IMG_IN r Hr). clear -R H IMG_LO. lia.
  - pose proof (sh_band_below_ceiling a X). rewrite kLowAppEnd_val in *. clear -H. lia.
  - unfold app_addr in X. rewrite kHighMemBeg_val in X. clear -X. lia.
Qed.
Lemma AG_fp_nonthr : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT. pose proof (fp_range a Ha) as BC. pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BC CR; lia| unfold FPWca; unfold kThrCache, kPerClassSize, kThrCacheStats, kNumClasses in *; clear -NT BC LO HCc; lia].
Qed.

Hypothesis AK : exists mo, AKern E s mo.
Hypothesis TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.

(* [comment removed for export] *)
Lemma Tpage_apart : forall a, T <= a < T + 4096 ->
     ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
  /\ ~ (ae_ptr_array E <= a < ae_ptr_array E + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall b len, (In b (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len))
  /\ ~ (kLowAppEnd < a < kHighMemBeg) /\ ~ (0x10000 <= a < 0x603000).
Proof.
  intros a Ha. destruct AK as [mo K]. pose proof WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & S3 & _).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  split; [clear -Ha E19; lia|]. split; [clear -Ha E23; lia|]. split.
  { intros sc Hsc. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  split.
  { intros b len H. destruct H as [[[<-|Hb] ->]|[[<-|Hb] ->]].
    - clear -Ha TDN. lia.
    - destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia.
    - pose proof (ak_store_sep _ _ _ K) as (_ & _ & X & _). unfold kPageSize, kStoreBlockBytes in *. clear -Ha X. lia.
    - destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  unfold app_mem in E14. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. pose proof Tpl as [[T1 T2] T3]. clear -Ha E14 T1 T2 T3. split; lia.
Qed.

(* [comment removed for export] *)
Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_fp_nonthr; [left; exact Ha|]. destruct Ha as (r & Hr & R).
  pose proof (IMG_LOW r ltac:(apply in_app_iff; left; exact Hr)) as [L1 L2]. pose proof Tpl as [[T1 T2] T3]. clear -R L1 L2 T1 T2. lia.
Qed.
Lemma AGri : forall a, ae_region_info E <= a < ae_region_info E + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_fp_nonthr; [right; left; exact Ha|]. intros HT. destruct (Tpage_apart a HT) as (NR & _).
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha NR E3 E4. lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_fp_nonthr; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]|]. intros HT. destruct (Tpage_apart a HT) as (NR & _).
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E [] [] s a WF RM) as SP. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). unfold kSpaceSize in *. clear -SP NR E3 E4. lia.
Qed.
Lemma AGptr : forall a, ae_ptr_array E <= a < ae_ptr_array E + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_fp_nonthr; [do 4 right; left; exact Ha|]. intros HT. destruct (Tpage_apart a HT) as (_ & NP & _). unfold kChunksBlockCount in Ha. clear -Ha NP. lia.
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. apply AG_fp_nonthr; [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]|]. intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _).
  pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. pose proof (NS sc Hsc). unfold kPageSize in *. clear -Ha GE H. lia.
Qed.
Lemma AGcm : forall a cb cm, as_chunks s !! cb = Some cm -> chunk_meta_fp cm a -> m' (wa a) = m (wa a).
Proof.
  intros a cb cm Hcm Ha. apply AG_fp_nonthr; [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]|]. intros HT.
  destruct (Tpage_apart a HT) as (NR & _ & NS & _).
  pose proof (chunk_meta_in_block E [] [] s cb cm a WF Hcm Ha) as [BL BU].
  destruct (block_where E [] [] s cb cm WF Hcm) as [(I1 & I2 & _)|(sc & Hsc & _ & L1 & L2)].
  - pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). unfold kSpaceSize in *. clear -BL BU I1 I2 NR E3 E4. lia.
  - pose proof (NS sc Hsc). unfold kPageSize in *. clear -BL BU L1 L2 H. lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. apply AG_fp_nonthr; [do 7 right; left; exists b; split; [exact Hb| exact Ha]|]. intros HT. destruct (Tpage_apart a HT) as (NR & _).
  pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E [] s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [I1 I2].
  assert (CS : class_size kBatchClass = 8192) by reflexivity.
  pose proof WE as (E1 & E2 & E3 & E4 & _). unfold kBatchCap, kSpaceSize, kRegionSize in *. clear -Ha NR I1 I2 CS E3 E4. lia.
Qed.
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_fp_nonthr; [do 8 right; left; exact Ha|]. intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _ & NI).
  destruct (DepotFP_where E s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - pose proof (IMG_LOW r ltac:(apply in_app_iff; right; exact Hr)) as [L1 L2]. clear -R L1 L2 NI. lia.
  - exact (False_ind _ (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R)).
  - exact (False_ind _ (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R)).
Qed.
Lemma AGsh : forall g v, Sh E s (8 * g) = Some v -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg. apply AG_fp_nonthr; [do 9 right; exists g, v; split; [reflexivity| exact Hg]|]. intros HT. destruct (Tpage_apart _ HT) as (_ & _ & _ & _ & NBAND & _).
  destruct (fp_locate E (DepotFP E) [] [] IMG_IN (DepotFP_where E) s (kShadowBase + g) WF BS ltac:(do 9 right; exists g, v; split; [reflexivity| exact Hg])) as [X|[[X _]|X]].
  - destruct X as (r & Hr & R). pose proof (IMG_LOW r Hr) as [L1 L2]. destruct (Tpage_apart _ HT) as (_ & _ & _ & _ & _ & NI). clear -R L1 L2 NI. lia.
  - pose proof (sh_band_below_ceiling _ X). clear -H NBAND. lia.
  - (* [comment removed for export] *)
    exfalso. destruct X as (_ & _ & _ & _).
    unfold Sh in Hg. pose proof WF as WF0.
    destruct (in_some_region_map E s (8 * g)) eqn:RM.
    + pose proof (region_map_in_space E [] [] s (8 * g) WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
      pose proof alloc_ceiling_range as CR. rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kSpaceSize, kShadowBase in *. clear -SP E2 E3 E4 E5 CR HT NBAND Tpl. lia.
    + destruct (in_some_sec_map s (8 * g)) eqn:SM.
      * unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
        pose proof alloc_ceiling_range as CR. unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kShadowBase in *. clear -B1 B2 HB S CR HT NBAND Tpl. lia.
      * cbn [orb] in Hg. destruct (sh_default_dom E (8 * g) && negb (sh_excluded E (8 * g))) eqn:C; [|discriminate].
        apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
        -- apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
           rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kShadowBase in *. clear -C1 C2 HT NBAND Tpl. lia.
        -- apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
           rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kShadowBase, kHighMemEnd in *. clear -C1 C2 HT NBAND Tpl. lia.
Qed.

(* [comment removed for export] *)
Lemma AGthr_cells : forall A k, T <= A -> A + k <= T + 4096 ->
  (A + k <= T + kThrCache + kPerClassSize * c \/ T + kThrCache + kPerClassSize * c + 4 <= A) ->
  (A + k <= T + kThrCacheStats + 16 \/ T + kThrCacheStats + 24 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 H3 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  apply AG; [clear -Hz H0 H1 T1 T3 CR; lia|]. unfold FPWca. clear -Hz H0 H1 H2 H3 T3 LO. lia.
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.

Lemma repD_pop : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8). pose proof HCc as HC.
  unfold arep_thread. rewrite (pop_tq n s), (pop_cache_allocated n s), (pop_cache_mapped n s), (pop_ts n s), (tq_bytes_pop n s).
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D3]; thr_ag|].
  split.
  { (* [comment removed for export] *)
    intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). rewrite (pop_get_cache n s c').
    unfold percls_cells. rewrite (pop_get_cache n s c'), (pop_cache_inited n s). unfold kNumClasses in Hc'.
    destruct (decide (c' = c)) as [->|NE].
    - destruct (removelast_facts (get_cache s c) Hl) as [EL LL]. rewrite CI.
      split.
      + (* [comment removed for export] *)
        unfold percls_cells in X1. rewrite CI in X1. apply rh_split with (cs1 := [C4 (zw (zlen (get_cache s c)))]) in X1. destruct X1 as [_ X1].
        apply (rh_join_at segs m' _ (T + kThrCache + kPerClassSize * c + 4) [C4 (zw (zlen (removelast (get_cache s c))))]).
        * replace (zlen (removelast (get_cache s c))) with (zlen (get_cache s c) - 1); [exact NC_row|]. unfold zlen. rewrite LL.
          destruct (get_cache s c) eqn:GC; [exfalso; congruence| cbn [length Nat.pred]; lia].
        * eapply rw_cells_agree'; [| exact X1]. thr_ag.
        * cbn. lia.
      + exists (zw (List.last (get_cache s c) 0) :: junk). split.
        * replace (map zw (removelast (get_cache s c)) ++ zw (List.last (get_cache s c) 0) :: junk) with (map zw (get_cache s c) ++ junk).
          2:{ rewrite EL at 1. rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity. }
          eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag.
        * cbn [length]. rewrite LL. destruct (get_cache s c) eqn:GC; [exfalso; congruence| cbn [length Nat.pred] in *; lia].
    - split.
      + eapply rw_cells_agree'; [| exact X1]. unfold percls_cells. thr_ag.
      + exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag. }
  split.
  { apply rh_split with (cs1 := [C8 (zw (as_cache_allocated s))]) in D5. destruct D5 as [_ D5].
    apply (rh_join_at segs m' _ (T + kThrCacheStats + 16 + 8) [C8 (zw (as_cache_allocated s + class_size c))]); [exact NC_cst| | cbn; lia].
    eapply rw_cells_agree'; [| exact D5]. thr_ag. }
  split; [eapply u64arr_agree; [| exact D6]; unfold tstats_words; cbn [length map]; thr_ag|].
  split; [eapply u64arr_agree; [| exact D7]; rewrite length_map, length_ziota; thr_ag|].
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.

Theorem ARep_capop : AREP s' m'.
Proof.
  pose proof REP as (RA & RB & RC & _ & RE & RF & RG & RH & RI & RJ).
  apply (ARep_thr_xfer s s' m'); try (destruct s; reflexivity).
  - exact (frameA' segs E s m m' AGimg RA).
  - exact (frameB' segs E s m m' AGri RB).
  - exact (frameC' segs E s m m' WM AGfa RC).
  - exact repD_pop.
  - exact (frameE' segs E s m m' WM AGptr AGsec RE).
  - exact (frameF' segs s m m' AGcm RF).
  - exact (frameG' segs s m m' AGbat RG).
  - exact (frameH' segs E s m m' WM AGdep RH).
  - exact (frameI' segs E s m m' WM AGimg RI).
  - exact (frameJ' segs E s m m' AGsh RJ).
Qed.
End CAPOP.
End RCA.
End RC__1.

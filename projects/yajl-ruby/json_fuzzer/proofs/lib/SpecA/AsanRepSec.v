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
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHit AsanRepX AsanRepCa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Definition sec_commit (a : astate) : astate :=
  if n_chunks a =? as_ptr_committed a then upd_ptr_committed (as_ptr_committed a + kChunksBlockCount) a else a.
Definition sec_st (a : astate) (mb msz need : Z) : astate :=
  let a1 := sec_commit (upd_ts (ts_on_mmap msz) a) in
  let idx := n_chunks a in
  upd_glob (fun x => x + msz) (fun x => x + msz)
    (upd_sec_stats (fun st => mkSecStats (ss_n_allocs st + 1) (ss_n_frees st) (ss_cur st + msz) (Z.max (ss_max st) (ss_cur st + msz))
                                         (bump (ss_by_size_log st) (zlog2 msz) 1))
      (upd_sec_stale (delete idx)
        (upd_sec (fun l => l ++ [mkSec mb msz need])
          (upd_residue (fun r => r ++ residue_pages mb msz) a1)))).

Section RSX.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation INST := (ae_instance E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).
#[warnings="-notation-for-abbreviation"] Notation AREPX := (ARepX segs E (DepotR segs E)).

(* [comment removed for export] *)
Section FLD.
Variables (a : astate) (mb msz need : Z).
#[warnings="-notation-for-abbreviation"] Notation a' := (sec_st a mb msz need).
Ltac fld := unfold sec_st, sec_commit; destruct (n_chunks _ =? _); destruct a; reflexivity.
Lemma sec_regions : as_regions a' = as_regions a. Proof. fld. Qed.
Lemma sec_cache_inited : as_cache_inited a' = as_cache_inited a. Proof. fld. Qed.
Lemma sec_cache : as_cache a' = as_cache a. Proof. fld. Qed.
Lemma sec_cache_allocated : as_cache_allocated a' = as_cache_allocated a. Proof. fld. Qed.
Lemma sec_cache_mapped : as_cache_mapped a' = as_cache_mapped a. Proof. fld. Qed.
Lemma sec_chunks : as_chunks a' = as_chunks a. Proof. fld. Qed.
Lemma sec_dead : as_dead a' = as_dead a. Proof. fld. Qed.
Lemma sec_tq : as_tq a' = as_tq a. Proof. fld. Qed.
Lemma sec_gq : as_gq a' = as_gq a. Proof. fld. Qed.
Lemma sec_keys : as_keys a' = as_keys a. Proof. fld. Qed.
Lemma sec_frames : as_frames a' = as_frames a. Proof. fld. Qed.
Lemma sec_ia : as_ia_inited a' = as_ia_inited a. Proof. fld. Qed.
Lemma sec_node_blocks : as_node_blocks a' = as_node_blocks a. Proof. fld. Qed.
Lemma sec_store_blocks : as_store_blocks a' = as_store_blocks a. Proof. fld. Qed.
Lemma sec_store_stored : as_store_stored a' = as_store_stored a. Proof. fld. Qed.
Lemma sec_ndepot : as_ndepot_ins a' = as_ndepot_ins a. Proof. fld. Qed.
Lemma sec_nprim : as_nprim_ever a' = as_nprim_ever a. Proof. fld. Qed.
Lemma sec_oom : as_oom a' = as_oom a. Proof. fld. Qed.
Lemma sec_sec : as_sec a' = as_sec a ++ [mkSec mb msz need]. Proof. fld. Qed.
Lemma sec_ptr : as_ptr_committed a' = (if n_chunks a =? as_ptr_committed a then as_ptr_committed a + kChunksBlockCount else as_ptr_committed a).
Proof. fld. Qed.
Lemma sec_stats : as_sec_stats a' =
  mkSecStats (ss_n_allocs (as_sec_stats a) + 1) (ss_n_frees (as_sec_stats a)) (ss_cur (as_sec_stats a) + msz)
             (Z.max (ss_max (as_sec_stats a)) (ss_cur (as_sec_stats a) + msz)) (bump (ss_by_size_log (as_sec_stats a)) (zlog2 msz) 1).
Proof. fld. Qed.
Lemma sec_glob_allocated : as_glob_allocated a' = as_glob_allocated a + msz. Proof. fld. Qed.
Lemma sec_glob_mapped : as_glob_mapped a' = as_glob_mapped a + msz. Proof. fld. Qed.
Lemma sec_ts : as_ts a' = ts_on_mmap msz (as_ts a). Proof. fld. Qed.
Lemma sec_residue : as_residue a' = as_residue a ++ residue_pages mb msz. Proof. fld. Qed.
Lemma sec_n_chunks : n_chunks a' = n_chunks a + 1.
Proof. unfold n_chunks. rewrite sec_sec, length_app. cbn [length]. lia. Qed.
Lemma tq_bytes_sec : tq_bytes a' = tq_bytes a. Proof. fld. Qed.
Lemma gq_bytes_sec : gq_bytes a' = gq_bytes a. Proof. fld. Qed.
Lemma sec_get_cache : forall c, get_cache a' c = get_cache a c. Proof. intros c. unfold get_cache. rewrite sec_cache. reflexivity. Qed.
Lemma sec_region_of : forall c, region_of a' c = region_of a c. Proof. intros c. unfold region_of, get_region. rewrite sec_regions. reflexivity. Qed.
End FLD.

(* [comment removed for export] *)
Lemma ARepX_sec_xfer : forall s s' m blo bhi,
  as_regions s' = as_regions s -> as_cache_inited s' = as_cache_inited s -> as_cache s' = as_cache s -> as_cache_stale s' = as_cache_stale s ->
  as_cache_allocated s' = as_cache_allocated s -> as_cache_mapped s' = as_cache_mapped s -> as_oom s' = as_oom s ->
  as_chunks s' = as_chunks s -> as_dead s' = as_dead s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  as_keys s' = as_keys s -> as_frames s' = as_frames s -> as_ia_inited s' = as_ia_inited s ->
  as_nprim_ever s' = as_nprim_ever s -> as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s ->
  as_store_stored s' = as_store_stored s -> as_ndepot_ins s' = as_ndepot_ins s -> as_everc s' = as_everc s ->
  arep_instance segs E s' m -> arep_regioninfo segs E s m -> arep_region_mem segs E s m -> arep_thread segs E s' m ->
  arep_secondary segs E s' m -> arep_chunks segs s m -> arep_batches segs s m -> arep_depot (DepotR segs E) s m ->
  arep_globals segs E s m -> arep_shadow_but segs E blo bhi s' m -> AREPX s' m blo bhi.
Proof.
  intros s s' m blo bhi. destruct s, s'; cbn. intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.
  intros RA RB RC RD' RE RF RG RH RI RJ.
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD'|]. split; [exact RE|]. split; [exact RF|].
  split; [destruct RG as [RG1 RG2]; split; eapply arep_batch_list_indep; eassumption|]. split; [exact RH|]. split; [exact RI| exact RJ].
Qed.


(* [comment removed for export] *)
Section SEC.
Variables (s : astate) (m m' : mem) (lo mb msz need : Z).
#[warnings="-notation-for-abbreviation"] Notation s' := (sec_st s mb msz need).
#[warnings="-notation-for-abbreviation"] Notation n := (n_chunks s).
#[warnings="-notation-for-abbreviation"] Notation SS := (as_sec_stats s).

(* [comment removed for export] *)
Definition FPWsec (z : Z) : Prop :=
  lo <= z \/ (INST + 112 <= z < INST + 129) \/ (INST + 136 <= z < INST + 684) \/ (INST + 704 <= z < INST + 720)
  \/ (T + kThrStats + 72 <= z < T + kThrStats + 88) \/ (mb <= z < mb + msz)
  \/ (kShadowBase + mb / 8 <= z < kShadowBase + mb / 8 + msz / 8) \/ (PA <= z < PA + 8 * kChunksBlockCount).

Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWsec z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis REP : AREP s m.
Hypothesis WF : AWf E [] [] s.
Hypothesis BS : blocks_sep E s.
Hypothesis Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.
Hypothesis IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Hypothesis IMG_LO : 0x10000 <= fst (ae_img E).
Hypothesis IMG_LOW : forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
(* [comment removed for export] *)
Hypothesis IMG_INST : forall r, In r (List.tl (arep_img_ranges E) ++ depot_static E) -> fst r + snd r <= INST \/ INST + 3632 <= fst r.
Hypothesis AK : exists mo, AKern E s mo.
Hypothesis TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.
(* [comment removed for export] *)
Hypothesis D0RES : In (ae_depot_nodes E, kDepotNodeBlockBytes) (ae_reserved E) /\ In (ae_store_blk E, kStoreBlockBytes) (ae_reserved E).
(* [comment removed for export] *)
Hypothesis NEED : 0x10000 < need /\ need mod 8 = 0.
Hypothesis MSZ : msz = round_up need 4096 + 4096.
Hypothesis MB : mb mod 4096 = 0 /\ 0 < mb.
Hypothesis APP : app_mem mb msz /\ mb + msz <= alloc_ceiling /\ img_sep E mb msz.
Hypothesis RSV : forall rr, In rr (ae_reserved E) -> mb + msz <= fst rr \/ fst rr + snd rr <= mb.
Hypothesis KRF : ranges_free (known_ranges E s) mb msz = true.
(* [comment removed for export] *)
Hypothesis NC_nres : RW m' (INST + kInsNReserved) [C8 (zw (as_ptr_committed s')); C8 (zw (n + 1)); C1 (zb 0)].
Hypothesis NC_stats : RW m' (INST + kInsSecStats)
  [C8 (zw (ss_n_allocs SS + 1)); C8 (zw (ss_n_frees SS)); C8 (zw (ss_cur SS + msz)); C8 (zw (Z.max (ss_max SS) (ss_cur SS + msz)))].
Hypothesis NC_bsl : exists bsl', u64arr segs m' (INST + kInsSecStats + 32) bsl' /\ length bsl' = 64%nat.
Hypothesis NC_mutex : RW m' (INST + kInsSecMutex) [C4 (zw 0)].
Hypothesis NC_glob : RW m' (INST + kInsGlobalStats + 16) [C8 (zw (as_glob_allocated s + msz)); C8 (zw (as_glob_mapped s + msz))].
Hypothesis NC_thr : RW m' (T + kThrStats + 72) [C8 (zw (ts_mmaps (as_ts s) + 1)); C8 (zw (ts_mmaped (as_ts s) + msz))].
Hypothesis NC_ptr : exists junk', u64arr segs m' PA (map (fun c => zw (sc_map_beg c)) (as_sec s ++ [mkSec mb msz need]) ++ junk')
                                 /\ (length (as_sec s) + 1 + length junk' = Z.to_nat kChunksBlockCount)%nat.
Hypothesis NC_hdr : RW m' mb [C8 (zw mb); C8 (zw msz); C8 (zw need); C8 (zw n)].
Hypothesis NC_body : wr_at segs m' mb msz.
Hypothesis NC_sh : RW m' (kShadowBase + mb / 8) [CB 512%nat (repeat (zb kAsanHeapLeftRedzoneMagic) 512%nat)].

(* [comment removed for export] *)
Lemma msz_facts : need + 4096 <= msz /\ msz mod 4096 = 0 /\ msz <= need + 8192 /\ mb mod 8 = 0 /\ msz mod 8 = 0.
Proof.
  clear -NEED MSZ MB. destruct NEED as [N1 N8]. destruct MB as [M4 _]. subst msz. unfold round_up.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma newmap_apart : forall a, mb <= a < mb + msz ->
     ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
  /\ ~ (PA <= a < PA + 0x800000)
  /\ ~ (T <= a < T + 4096)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall b len, (In b (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len))
  /\ ~ (kLowAppEnd <= a < kHighMemBeg)
  /\ (forall r, In r (arep_img_ranges E ++ depot_static E) -> ~ (fst r <= a < fst r + snd r)).
Proof.
  intros a Ha. pose proof WF as (WE & _). 
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & _).
  assert (RS : forall b l, In (b, l) (ae_reserved E) -> ~ (b <= a < b + l)).
  { intros b l IN R. pose proof (RSV _ IN) as X. cbn [fst snd] in X. clear -X R Ha. lia. }
  (* [comment removed for export] *)
  assert (KR : forall b l, In (b, l) (known_ranges E s) -> ~ (b <= a < b + l /\ 0 < l)).
  { intros b l IN [R Hl]. unfold ranges_free in KRF. rewrite forallb_forall in KRF.
    pose proof (KRF (b, l) IN) as X. cbn [fst snd] in X. unfold iv_disjoint in X. apply Bool.orb_true_iff in X. destruct X as [X|X]; apply Z.leb_le in X; clear -X R Ha Hl; lia. }
  split; [exact (RS _ _ E7)|]. split; [exact (RS _ _ E8)|]. split; [exact (RS _ _ E13)|].
  split.
  { intros sc Hsc R. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & _).
    apply (KR (sc_map_beg sc) (sc_map_size sc)); [| split; [exact R| exact POS]].
    unfold known_ranges. apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists sc. auto. }
  split.
  { intros b len [[[<-|Hb] ->]|[[<-|Hb] ->]].
    - exact (RS _ _ (proj1 D0RES)).
    - intros R. apply (KR b kDepotNodeBlockBytes); [| split; [exact R| unfold kDepotNodeBlockBytes; lia]].
      unfold known_ranges. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists b. auto.
    - exact (RS _ _ (proj2 D0RES)).
    - intros R. apply (KR b kStoreBlockBytes); [| split; [exact R| unfold kStoreBlockBytes; lia]].
      unfold known_ranges. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists b. auto. }
  split.
  { destruct APP as (AM & _). unfold app_mem in AM. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. clear -AM Ha. lia. }
  intros r Hr R. destruct APP as (_ & _ & IS). unfold img_sep in IS. pose proof (IMG_IN r Hr) as [I1 I2]. clear -IS I1 I2 R Ha. lia.
Qed.


(* [comment removed for export] *)
Lemma win_band : forall z, kShadowBase + mb / 8 <= z < kShadowBase + mb / 8 + msz / 8 -> kLowAppEnd < z < kHighMemBeg.
Proof.
  intros z Hz. destruct APP as (AM & CE & _). pose proof alloc_ceiling_range as CR. destruct MB as [_ POS].
  unfold app_mem in AM. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. unfold kShadowBase in *. clear -Hz AM CE CR POS. lia.
Qed.
Lemma Sh_granule_range : forall x v, Sh E s x = Some v -> 0 <= x < 2^47.
Proof.
  intros x v Hx. pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hx.
  destruct (in_some_region_map E s x) eqn:RM.
  - pose proof (region_map_in_space E [] [] s x WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
    unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
  - destruct (in_some_sec_map s x) eqn:SM.
    + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2].
      apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
      unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
    + cbn [orb] in Hx. destruct (sh_default_dom E x && negb (sh_excluded E x)) eqn:C; [|discriminate].
      apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
      * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
        rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
      * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
        rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_fp : forall a, arep_fp E (DepotFP E) s a ->
  ~ (T <= a < T + 4096) -> ~ (INST <= a < INST + 3632) -> ~ (PA <= a < PA + 0x800000) -> ~ (mb <= a < mb + msz) ->
  ~ (kShadowBase + mb / 8 <= a < kShadowBase + mb / 8 + msz / 8) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NI NP NM NW. pose proof (fp_range E s WF BS IMG_IN IMG_LO a Ha) as BC. pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BC CR; lia|]. unfold FPWsec. unfold kThrStats, kChunksBlockCount in *. clear -NT NI NP NM NW BC LO. lia.
Qed.

(* [comment removed for export] *)
Lemma INST_img : 0x10000 <= INST /\ INST + 3632 <= 0x603000 /\ fst (ae_img E) <= INST /\ INST + 3632 <= fst (ae_img E) + snd (ae_img E).
Proof.
  pose proof (IMG_LOW (INST, 3632) ltac:(apply in_app_iff; left; left; reflexivity)) as [A B].
  pose proof (IMG_IN (INST, 3632) ltac:(apply in_app_iff; left; left; reflexivity)) as [C D]. cbn [fst snd] in *. auto.
Qed.

(* [comment removed for export] *)
Lemma AGimg1 : forall a, in_ranges (List.tl (arep_img_ranges E)) a -> m' (wa a) = m (wa a).
Proof.
  intros a (r & Hr & R). pose proof INST_img as (I1 & I2 & I3 & I4). pose proof Tpl as [[T1 T2] T3].
  assert (Hr' : In r (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; right; exact Hr).
  pose proof (IMG_LOW r Hr') as [L1 L2]. pose proof (IMG_IN r Hr') as [L3 L4].
  pose proof (IMG_INST r ltac:(apply in_app_iff; left; exact Hr)) as SEP.
  pose proof (proj1 WF) as WE.
  pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
  unfold img_sep in E33.
  apply AG_fp; [left; exists r; split; [right; exact Hr| exact R] | clear -R L1 L2 T1 T2; lia | clear -R SEP; lia | clear -R L3 L4 E33; lia | |].
  - intros M. destruct (newmap_apart a M) as (_ & _ & _ & _ & _ & _ & NIM'). exact (NIM' r Hr' R).
  - intros W. pose proof (win_band a W) as X. rewrite kLowAppEnd_val in X. clear -X L1 L2 R. lia.
Qed.


(* [comment removed for export] *)
Lemma AG_resv : forall a, arep_fp E (DepotFP E) s a -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 -> m' (wa a) = m (wa a).
Proof.
  intros a Ha R. pose proof INST_img as (I1 & I2 & _). pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  rewrite kHighMemBeg_val in E2.
  apply AG_fp; [exact Ha| | clear -R I1 I2 E2; lia| clear -R E20; lia| |].
  - intros HT. destruct (Tpage_apart E s WF Tpl AK TDN a HT) as (NR & _). exact (NR R).
  - intros M. destruct (newmap_apart a M) as (NR & _). exact (NR R).
  - intros W. pose proof (win_band a W) as X. rewrite kHighMemBeg_val in X. clear -X R E2. lia.
Qed.
Lemma space_resv : forall a, SB <= a < SB + kSpaceSize + 0x1000 -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000.
Proof. intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). clear -Ha E3 E4. lia. Qed.

Lemma AGri : forall a, ae_region_info E <= a < ae_region_info E + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_resv; [right; left; exact Ha|]. apply space_resv. unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha. lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_resv; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]|].
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E [] [] s a WF RM) as SP. apply space_resv. unfold kSpaceSize in *. clear -SP. lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. apply AG_resv; [do 7 right; left; exists b; split; [exact Hb| exact Ha]|].
  pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E [] s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [J1 J2].
  assert (CS : class_size kBatchClass = 8192) by reflexivity.
  apply space_resv. unfold kBatchCap, kSpaceSize, kRegionSize in *. clear -Ha J1 J2 CS. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_secmap : forall a sc, arep_fp E (DepotFP E) s a -> In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc -> m' (wa a) = m (wa a).
Proof.
  intros a sc Ha Hsc R. pose proof INST_img as (I1 & I2 & I3 & I4). pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & _).
  pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & _ & _ & _ & SR).
  pose proof (SR _ E29) as XI. pose proof (SR _ E8) as XP. cbn [fst snd] in XP.
  apply AG_fp; [exact Ha| | destruct (ae_img E); cbn [fst snd] in *; clear -R XI I3 I4; lia| clear -R XP; lia| |].
  - intros HT. destruct (Tpage_apart E s WF Tpl AK TDN a HT) as (_ & _ & NS & _). exact (NS sc Hsc R).
  - intros M. destruct (newmap_apart a M) as (_ & _ & _ & NS & _). exact (NS sc Hsc R).
  - intros W. pose proof (win_band a W) as X. unfold app_mem in AM. clear -X R AM. lia.
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE.
  apply (AG_secmap a sc); [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| exact Hsc| unfold kPageSize in GE; clear -Ha GE; lia].
Qed.
Lemma AGcm : forall a cb cm, as_chunks s !! cb = Some cm -> chunk_meta_fp cm a -> m' (wa a) = m (wa a).
Proof.
  intros a cb cm Hcm Ha.
  pose proof (chunk_meta_in_block E [] [] s cb cm a WF Hcm Ha) as [BL BU].
  destruct (block_where E [] [] s cb cm WF Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
  - apply AG_resv; [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]|]. apply space_resv. clear -BL BU J1 J2. lia.
  - apply (AG_secmap a sc); [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]| exact Hsc| unfold kPageSize in *; clear -BL BU L1 L2; lia].
Qed.


(* [comment removed for export] *)
Hypothesis DN0 : ae_depot_nodes E + kDepotNodeBlockBytes <= PA \/ PA + kPtrArrayLen <= ae_depot_nodes E.

Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof INST_img as (I1 & I2 & I3 & I4). pose proof Tpl as [[T1 T2] T3]. destruct AK as [mo K].
  pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & E32 & E33 & _).
  assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - (* [comment removed for export] *)
    assert (Hr' : In r (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hr).
    pose proof (IMG_LOW r Hr') as [L1 L2]. pose proof (IMG_IN r Hr') as [L3 L4].
    pose proof (IMG_INST r ltac:(apply in_app_iff; right; exact Hr)) as SEP. unfold img_sep in E33.
    apply AG_fp; [exact FPa| clear -R L1 L2 T1 T2; lia| clear -R SEP; lia| clear -R L3 L4 E33; lia| |].
    + intros M. destruct (newmap_apart a M) as (_ & _ & _ & _ & _ & _ & NIM). exact (NIM r Hr' R).
    + intros W. pose proof (win_band a W) as X. rewrite kLowAppEnd_val in X. clear -X L1 L2 R. lia.
  - (* [comment removed for export] *)
    pose proof (BS b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). unfold img_sep in BI.
    apply AG_fp; [exact FPa| | clear -R BI I3 I4; lia| | |].
    + intros HT. destruct (Tpage_apart E s WF Tpl (ex_intro _ mo K) TDN a HT) as (_ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
    + destruct Hb as [<-|Hb]; [unfold kPtrArrayLen in DN0; clear -R DN0; lia|].
      destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E8) as X. cbn [fst snd] in X. clear -R X. lia.
    + intros M. destruct (newmap_apart a M) as (_ & _ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
    + intros W. pose proof (win_band a W) as X. unfold app_mem in AM. clear -X R AM. lia.
  - (* [comment removed for export] *)
    pose proof (BS b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). unfold img_sep in BI.
    apply AG_fp; [exact FPa| | clear -R BI I3 I4; lia| | |].
    + intros HT. destruct (Tpage_apart E s WF Tpl (ex_intro _ mo K) TDN a HT) as (_ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
    + destruct Hb as [<-|Hb].
      * pose proof (ak_store_sep _ _ _ K) as (_ & _ & _ & _ & X). unfold kPtrArrayLen, kStoreBlockBytes in *. clear -R X. lia.
      * destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E8) as X. cbn [fst snd] in X. clear -R X. lia.
    + intros M. destruct (newmap_apart a M) as (_ & _ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
    + intros W. pose proof (win_band a W) as X. unfold app_mem in AM. clear -X R AM. lia.
Qed.

(* [comment removed for export] *)
Lemma AGsh_out : forall g v, Sh E s (8 * g) = Some v -> (8 * g + 8 <= mb \/ mb + msz <= 8 * g) ->
  m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg OUT. pose proof (Sh_granule_range _ _ Hg) as GR. pose proof INST_img as (I1 & I2 & _). pose proof msz_facts as (_ & _ & _ & MB8 & MS8).
  pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & _).
  assert (BAND : kLowAppEnd < kShadowBase + g < kHighMemBeg) by (rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia).
  apply AG_fp; [do 9 right; exists g, v; split; [reflexivity| exact Hg]| | rewrite kLowAppEnd_val in BAND; clear -BAND I1 I2; lia
               | unfold app_mem in E16; clear -BAND E16; lia| |].
  - intros HT. destruct (Tpage_apart E s WF Tpl AK TDN _ HT) as (_ & _ & _ & _ & NBAND & _). apply NBAND. clear -BAND. lia.
  - intros M. destruct (newmap_apart _ M) as (_ & _ & _ & _ & _ & NB & _). apply NB. clear -BAND. lia.
  - intros W. unfold kShadowBase in *. clear -W OUT MB8 MS8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma AGthr_cells : forall A k, T <= A -> A + k <= T + 4096 ->
  (A + k <= T + kThrStats + 72 \/ T + kThrStats + 88 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR. pose proof INST_img as (I1 & I2 & _).
  pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  assert (HT : T <= z < T + 4096) by (clear -Hz H0 H1; lia).
  apply AG; [clear -Hz H0 H1 T1 T3 CR; lia|]. unfold FPWsec. intros [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
  - clear -X HT T3 LO. lia.
  - clear -X HT I1 I2 T2. lia.
  - clear -X HT I1 I2 T2. lia.
  - clear -X HT I1 I2 T2. lia.
  - clear -X Hz H2. lia.
  - destruct (newmap_apart z X) as (_ & _ & NT & _). exact (NT HT).
  - pose proof (win_band z X) as B. unfold app_mem in E14. clear -B HT E14. lia.
  - unfold kChunksBlockCount in X. clear -X HT E23. lia.
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.


(* [comment removed for export] *)
Lemma existsb_app' : forall {X} (f : X -> bool) l1 l2, existsb f (l1 ++ l2) = existsb f l1 || existsb f l2.
Proof. intros X f l1 l2. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH, Bool.orb_assoc. reflexivity. Qed.

Lemma sec_in_region_map : forall x, in_some_region_map E s' x = in_some_region_map E s x.
Proof. intros x. unfold in_some_region_map, region_of, get_region. rewrite sec_regions. reflexivity. Qed.
Lemma sec_in_sec_map : forall x, in_some_sec_map s' x = in_some_sec_map s x || ((mb <=? x) && (x <? mb + msz)).
Proof. intros x. unfold in_some_sec_map. rewrite sec_sec, existsb_app'. cbn [existsb sc_map_beg sc_map_size]. rewrite Bool.orb_false_r. reflexivity. Qed.
Lemma sec_find_chunk : forall x, find_chunk s' x = find_chunk s x.
Proof. intros x. unfold find_chunk. rewrite sec_chunks. reflexivity. Qed.

Lemma Sh_sec_out : forall x, (x < mb \/ mb + msz <= x) -> Sh E s' x = Sh E s x.
Proof.
  intros x Hx. unfold Sh. rewrite sec_in_region_map, sec_in_sec_map, sec_find_chunk.
  replace ((mb <=? x) && (x <? mb + msz)) with false; [rewrite Bool.orb_false_r; reflexivity|].
  symmetry. apply Bool.andb_false_iff. destruct Hx; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Lemma find_chunk_newmap : forall x, mb <= x < mb + msz -> find_chunk s x = None.
Proof.
  intros x Hx. destruct (find_chunk s x) as [cm|] eqn:FC; [exfalso| reflexivity].
  destruct (find_chunk_some s x cm FC) as (cb & Hcm & R).
  assert (SPAN : blk_hi s cm = cm_alloc_beg cm + block_span cm) by (unfold blk_hi, block_span; destruct (cm_prim cm); lia).
  destruct (newmap_apart x Hx) as (NR & _ & _ & NS & _).
  destruct (block_where E [] [] s cb cm WF Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)]; unfold blk_lo in *.
  - apply NR. apply space_resv. clear -R SPAN J1 J2. lia.
  - apply (NS sc Hsc). unfold kPageSize in L1. clear -R SPAN L1 L2. lia.
Qed.
Lemma Sh_sec_new : forall x, mb <= x < mb + msz -> Sh E s' x = Some kAsanHeapLeftRedzoneMagic.
Proof.
  intros x Hx. unfold Sh. rewrite sec_in_sec_map, sec_find_chunk, (find_chunk_newmap x Hx).
  replace ((mb <=? x) && (x <? mb + msz)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  rewrite !Bool.orb_true_r. reflexivity.
Qed.


Hypothesis NCH : n_chunks s < kChunksBlockCount.

(* [comment removed for export] *)
Lemma AGinst : forall A k, INST <= A -> A + k <= INST + 3632 ->
  (A + k <= INST + 112 \/ (INST + 129 <= A /\ A + k <= INST + 136) \/ (INST + 684 <= A /\ A + k <= INST + 704) \/ INST + 720 <= A) ->
  agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR. pose proof INST_img as (I1 & I2 & I3 & I4).
  pose proof (proj1 WF) as WE.
  pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
  unfold img_sep in E33.
  assert (HI : INST <= z < INST + 3632) by (clear -Hz H0 H1; lia).
  apply AG; [clear -HI I1 I2 CR; lia|]. unfold FPWsec. intros [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
  - clear -X HI I2 CR LO. lia.
  - clear -X Hz H2. lia.
  - clear -X Hz H2. lia.
  - clear -X Hz H2. lia.
  - clear -X HI I1 I2 T2. unfold kThrStats in X. lia.
  - destruct (newmap_apart z X) as (_ & _ & _ & _ & _ & _ & NIM). apply (NIM (INST, 3632)); [apply in_app_iff; left; left; reflexivity| exact HI].
  - pose proof (win_band z X) as B. rewrite kLowAppEnd_val in B. clear -B HI I2. lia.
  - unfold kChunksBlockCount in X. clear -X HI I3 I4 E33. lia.
Qed.
Ltac ins_ag := apply AGinst; unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined in *; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia.

Lemma repA_sec : arep_instance segs E s' m'.
Proof.
  pose proof REP as (RA & _). destruct RA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold arep_instance. rewrite sec_n_chunks, sec_stats, sec_glob_allocated, sec_glob_mapped, sec_gq, gq_bytes_sec.
  cbn [ss_n_allocs ss_n_frees ss_cur ss_max].
  split; [eapply rw_cells_agree'; [| exact A1]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A2]; ins_ag|].
  split; [exact NC_nres|]. split; [exact NC_stats|]. split; [exact NC_bsl|]. split; [exact NC_mutex|]. split; [exact NC_glob|].
  split; [eapply rw_cells_agree'; [| exact A8]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A9]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A10]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A11]; ins_ag|].
  eapply rw_cells_agree'; [| exact A12]; ins_ag.
Qed.

(* [comment removed for export] *)
Lemma repD_sec : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  unfold arep_thread. rewrite sec_tq, sec_cache_allocated, sec_cache_mapped, sec_ts, tq_bytes_sec.
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D3]; thr_ag|].
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). unfold percls_cells. rewrite !sec_get_cache, sec_cache_inited. unfold kNumClasses in Hc'.
    split.
    - eapply rw_cells_agree'; [| exact X1]. unfold percls_cells. thr_ag.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag. }
  split; [eapply rw_cells_agree'; [| exact D5]; thr_ag|].
  split.
  { (* [comment removed for export] *)
    apply u64arr_of_cells.
    - destruct D6 as [_ W6]. eapply wr_at_transport; [| exact WM]. unfold tstats_words in *. rewrite length_map in *. cbn [length] in *. exact W6.
    - apply rh_split with (cs1 := [C8 (zw (ts_mmaps (as_ts s) + 1))]) in NC_thr as [N9 N10]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in N10.
      intros i w Hi.
      Ltac oldw D6 i := eapply rw_cells_agree'; [| exact (u64arr_cell segs _ _ _ i _ D6 eq_refl)]; thr_ag.
      do 9 (destruct i as [|i]; [cbn in Hi; injection Hi as <-; oldw D6 0%nat || oldw D6 1%nat || oldw D6 2%nat || oldw D6 3%nat || oldw D6 4%nat || oldw D6 5%nat || oldw D6 6%nat || oldw D6 7%nat || oldw D6 8%nat |]).
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 9) with (T + kThrStats + 72) by lia; exact N9|].
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 10) with (T + kThrStats + 72 + 8) by lia; exact N10|].
      do 3 (destruct i as [|i]; [cbn in Hi; injection Hi as <-; oldw D6 11%nat || oldw D6 12%nat || oldw D6 13%nat |]).
      destruct i; cbn in Hi; discriminate. }
  split.
  { replace (ts_by_size (ts_on_mmap msz (as_ts s))) with (ts_by_size (as_ts s)) by reflexivity.
    eapply u64arr_agree; [| exact D7]. rewrite length_map, length_ziota. thr_ag. }
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.


(* [comment removed for export] *)
Lemma repE_sec : arep_secondary segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & RE & _). destruct RE as [E1 E2].
  pose proof WF as (_ & _ & _ & _ & _ & (S1 & S2 & _) & _).
  unfold arep_secondary. rewrite sec_ptr, sec_sec. split.
  - right. split.
    + unfold kChunksBlockCount in *. destruct S1 as [[P0 _]|P1]; [rewrite P0 in *| rewrite P1 in *].
      * replace (n_chunks s =? 0) with true by (symmetry; apply Z.eqb_eq; clear -S2 NCH; unfold n_chunks in *; lia). reflexivity.
      * replace (n_chunks s =? 16384) with false by (symmetry; apply Z.eqb_neq; clear -NCH; lia). reflexivity.
    + destruct NC_ptr as (junk' & U & L). exists junk'. split; [exact U|]. rewrite length_app. cbn [length]. clear -L. lia.
  - intros i c Hi.
    destruct (Nat.lt_ge_cases i (length (as_sec s))) as [LT|GE].
    + rewrite nth_error_app1 in Hi by exact LT. destruct (E2 i c Hi) as [X1 X2].
      pose proof (nth_error_In _ _ Hi) as Hc.
      split; [| eapply wr_at_transport; [exact X2| exact WM]].
      eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGsec x c Hc). clear -Hx. lia.
    + rewrite nth_error_app2 in Hi by exact GE.
      destruct (i - length (as_sec s))%nat as [|k] eqn:D; [| destruct k; cbn in Hi; discriminate].
      cbn in Hi. injection Hi as <-. cbn [sc_map_beg sc_map_size sc_needed].
      replace (Z.of_nat i) with (n_chunks s) by (unfold n_chunks; clear -GE D; lia).
      split; [exact NC_hdr| exact NC_body].
Qed.

(* [comment removed for export] *)
Ltac zconsts Hx := unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined, kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats,
  kThrStats, kThrUnwinding, kRegSize, kBatchCap, kChunksBlockCount, kIaPageSizeOff in Hx |- *.
Ltac ag AG ARM := let Hx := fresh "Hx" in intros x Hx; cbn -[Z.add Z.mul Z.sub Z.of_nat Z.to_nat free_array region_beg region_of get_region Z.pow] in Hx; apply AG; ARM Hx.
Ltac agN1 AG k := ag AG ltac:(fun Hx => eexists; split; [eapply nth_error_In with (n := k); reflexivity| cbn [fst snd length asan_flags_bytes]; zconsts Hx; lia]).
Lemma repI_sec : arep_globals segs E s m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & RI' & _).
  destruct RI' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18). unfold arep_globals.
  split; [eapply u8arr_agree; [| exact I1]; agN1 AGimg1 0%nat|].
  split; [eapply rw_cells_agree'; [| exact I2]; agN1 AGimg1 1%nat|].
  split; [eapply rw_cells_agree'; [| exact I3]; agN1 AGimg1 2%nat|].
  split; [eapply rw_cells_agree'; [| exact I4]; agN1 AGimg1 3%nat|].
  split; [eapply rw_cells_agree'; [| exact I5]; agN1 AGimg1 4%nat|].
  split; [eapply rw_cells_agree'; [| exact I6]; agN1 AGimg1 5%nat|].
  split; [eapply rw_cells_agree'; [| exact I7]; agN1 AGimg1 6%nat|].
  split; [eapply rw_cells_agree'; [| exact I8]; agN1 AGimg1 7%nat|].
  split; [eapply rw_cells_agree'; [| exact I9]; agN1 AGimg1 8%nat|].
  split; [eapply rw_cells_agree'; [| exact I10]; agN1 AGimg1 9%nat|].
  split; [eapply rw_cells_agree'; [| exact I11]; agN1 AGimg1 10%nat|].
  split; [eapply rw_cells_agree'; [| exact I12]; agN1 AGimg1 11%nat|].
  split; [eapply rw_cells_agree'; [| exact I13]; agN1 AGimg1 12%nat|].
  split; [eapply u64arr_agree; [| exact I14]; agN1 AGimg1 13%nat|].
  split; [eapply rw_cells_agree'; [| exact I15]; agN1 AGimg1 14%nat|].
  split; [intros Hia; eapply rw_cells_agree'; [| exact (I16 Hia)]; agN1 AGimg1 15%nat|].
  split.
  { eapply u8arr_agree; [| exact I17]. intros x Hx. rewrite zeros_ia_len in Hx.
    apply AGimg1. eexists; split; [eapply nth_error_In with (n := 15%nat); reflexivity| cbn [fst snd]; zconsts Hx; clear -Hx; lia]. }
  eapply wr_at_transport; [exact I18| exact WM].
Qed.

(* [comment removed for export] *)
Lemma repJ_sec : arep_shadow_but segs E (mb + 4096) (mb + msz) s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RJ). pose proof msz_facts as (M1 & M2 & M3 & MB8 & MS8).
  intros g v Hg OUT.
  destruct (Z_lt_le_dec (8 * g) mb) as [LTm|GEm]; [| destruct (Z_lt_le_dec (8 * g) (mb + msz)) as [IN|GE2]].
  - rewrite (Sh_sec_out (8 * g) (or_introl LTm)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia.
    apply (AGsh_out g v Hg). left. clear -LTm MB8. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    rewrite (Sh_sec_new (8 * g) (conj GEm IN)) in Hg. injection Hg as <-.
    replace (kShadowBase + g) with (kShadowBase + mb / 8 + (g - mb / 8)) by lia.
    apply (CB_byte segs m' (kShadowBase + mb / 8) 512%nat (zb kAsanHeapLeftRedzoneMagic) (g - mb / 8) NC_sh).
    clear -GEm IN OUT M1 MB8. Z.div_mod_to_equations. lia.
  - rewrite (Sh_sec_out (8 * g) (or_intror GE2)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia.
    apply (AGsh_out g v Hg). right. exact GE2.
Qed.

Theorem ARepX_sec : AREPX s' m' (mb + 4096) (mb + msz).
Proof.
  pose proof REP as (RA & RB & RC & _ & RE & RF & RG & RH & RI & RJ).
  apply (ARepX_sec_xfer s s' m'); try (unfold sec_st, sec_commit; destruct (n_chunks _ =? _); destruct s; reflexivity).
  - exact repA_sec.
  - exact (frameB' segs E s m m' AGri RB).
  - exact (frameC' segs E s m m' WM AGfa RC).
  - exact repD_sec.
  - exact repE_sec.
  - exact (frameF' segs s m m' AGcm RF).
  - exact (frameG' segs s m m' AGbat RG).
  - exact (frameH' segs E s m m' WM AGdep RH).
  - exact repI_sec.
  - exact repJ_sec.
Qed.
End SEC.
End RSX.
End RC__1.

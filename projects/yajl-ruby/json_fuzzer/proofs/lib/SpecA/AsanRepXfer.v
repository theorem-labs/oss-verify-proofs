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
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHit AsanRepX AsanRepCa AsanRepSec AsanRepRefill AsanRepEnq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RQX.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation INST := (ae_instance E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).

Definition qx_st (s : astate) (tq' gq' : list batch) : astate := upd_tq (fun _ => tq') (upd_gq (fun _ => gq') s).

(* [comment removed for export] *)
Definition FPWq (s : astate) (lo : Z) (z : Z) : Prop :=
     lo <= z
  \/ (INST + kInsQMutex <= z < INST + kInsQMutex + 4)
  \/ (INST + kInsQGlobal <= z < INST + kInsQGlobal + 32)
  \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (exists b, In b (as_tq s ++ as_gq s) /\ b_addr b <= z < b_addr b + 8192).

(* [comment removed for export] *)
Section WFS.
Variables (P : list Z) (s : astate).
Hypothesis WF : AWf E P [] s.
Hypothesis RENV : renv_ok E s.
Hypothesis IMG_INST : forall r, In r (List.tl (arep_img_ranges E) ++ depot_static E) -> fst r + snd r <= INST \/ INST + 3632 <= fst r.

Let BS : blocks_sep E s. Proof. exact (proj1 RENV). Qed.
Let Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling. Proof. exact (proj1 (proj2 RENV)). Qed.
Let IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Proof. exact (proj1 (proj2 (proj2 RENV))). Qed.
Let IMG_LO : 0x10000 <= fst (ae_img E). Proof. exact (proj1 (proj2 (proj2 (proj2 RENV)))). Qed.
Let IMG_LOW : forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 RENV))))). Qed.
Let AK : exists mo, AKern E s mo. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV))))))). Qed.
Let TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV)))))))). Qed.
Let DN0 : ae_depot_nodes E + kDepotNodeBlockBytes <= PA \/ PA + kPtrArrayLen <= ae_depot_nodes E.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV)))))))). Qed.

Lemma fp_range : forall a, arep_fp E (DepotFP E) s a -> 0 <= a < alloc_ceiling.
Proof.
  intros a Ha. split; [| exact (fp_below_ceiling E (DepotFP E) P [] IMG_IN (DepotFP_where E) s a WF BS Ha)].
  destruct (fp_locate E (DepotFP E) P [] IMG_IN (DepotFP_where E) s a WF BS Ha) as [X|[[X _]|[X _]]].
  - destruct X as (r0 & Hr & R). pose proof (IMG_IN r0 Hr). clear -R H IMG_LO. lia.
  - pose proof (sh_band_below_ceiling a X). rewrite kLowAppEnd_val in *. clear -H. lia.
  - unfold app_addr in X. rewrite kHighMemBeg_val in X. clear -X. lia.
Qed.
Lemma INST_img : 0x10000 <= INST /\ INST + 3632 <= 0x603000 /\ fst (ae_img E) <= INST /\ INST + 3632 <= fst (ae_img E) + snd (ae_img E).
Proof.
  pose proof (IMG_LOW (INST, 3632) ltac:(apply in_app_iff; left; left; reflexivity)) as [A B].
  pose proof (IMG_IN (INST, 3632) ltac:(apply in_app_iff; left; left; reflexivity)) as [C D]. cbn [fst snd] in *. auto.
Qed.
Lemma Tpage_apart : forall a, T <= a < T + 4096 ->
     ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
  /\ ~ (ae_ptr_array E <= a < ae_ptr_array E + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall b0 len, (In b0 (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b0 (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b0 <= a < b0 + len))
  /\ ~ (kLowAppEnd < a < kHighMemBeg) /\ ~ (0x10000 <= a < 0x603000).
Proof.
  intros a Ha. destruct AK as [mo K]. pose proof WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & S3 & _).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  split; [clear -Ha E19; lia|]. split; [clear -Ha E23; lia|]. split.
  { intros sc Hsc. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  split.
  { intros b0 len H. destruct H as [[[<-|Hb0] ->]|[[<-|Hb0] ->]].
    - clear -Ha TDN. lia.
    - destruct (ak_blocks_sep _ _ _ K b0 kDepotNodeBlockBytes (or_introl (conj Hb0 eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia.
    - pose proof (ak_store_sep _ _ _ K) as (_ & _ & X & _). unfold kPageSize, kStoreBlockBytes in *. clear -Ha X. lia.
    - destruct (ak_blocks_sep _ _ _ K b0 kStoreBlockBytes (or_intror (conj Hb0 eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  unfold app_mem in E14. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. pose proof Tpl as [[T1 T2] T3]. clear -Ha E14 T1 T2 T3. split; lia.
Qed.
Lemma CS24 : class_size kBatchClass = 8192. Proof. reflexivity. Qed.
Lemma bat_range : forall b0, In b0 (as_tq s ++ as_gq s) ->
  SB + kBatchClass * kRegionSize <= b_addr b0 /\ b_addr b0 + 8192 <= SB + kBatchClass * kRegionSize + rg_mapped_user (region_of s kBatchClass) /\ carved E s kBatchClass (b_addr b0).
Proof.
  intros b0 Hb0. pose proof WF as (WE & [_ WR] & _ & _ & (WQ1 & _) & _).
  destruct (WQ1 b0 Hb0) as [(CV & _) _]. pose proof CV as (k & Hk & Hab & Hk1).
  destruct (WR kBatchClass ltac:(unfold kBatchClass, kLargestClassID; lia)) as (Q1 & _). cbv zeta in Q1. unfold region_of in *.
  rewrite CS24 in *. unfold region_beg in Hab. split; [| split; [| exact CV]]; rewrite Hab; clear -Hk Hk1 Q1; nia.
Qed.
Lemma bat_facts : forall b0 a, In b0 (as_tq s ++ as_gq s) -> b_addr b0 <= a < b_addr b0 + 8192 ->
  0 <= a < alloc_ceiling /\ ~ (kLowAppEnd <= a < kHighMemBeg) /\ ~ (T <= a < T + 4096)
  /\ (forall x, In x (arep_img_ranges E ++ depot_static E) -> ~ (fst x <= a < fst x + snd x))
  /\ ~ (PA <= a < PA + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall bb len, (In bb (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In bb (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (bb <= a < bb + len))
  /\ ~ (RI <= a < RI + kRegSize * kNumClasses)
  /\ (forall c', 0 <= c' < kNumClasses -> ~ (free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c'))).
Proof.
  intros b0 a Hb0 Ha. pose proof (bat_range b0 Hb0) as (R1 & R2 & _).
  pose proof WF as (WE & [WR0 WR] & _ & _ & _ & (_ & _ & S3 & _) & _).
  pose proof alloc_ceiling_range as CR. destruct AK as [mo K].
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  destruct (WR kBatchClass ltac:(unfold kBatchClass, kLargestClassID; lia)) as (Q1 & _ & Q3 & _). cbv zeta in Q1, Q3.
  pose proof (RG_any E P [] s WF) as RG.
  rewrite kHighMemBeg_val in E2. rewrite kLowAppEnd_val, kHighMemBeg_val. unfold kBatchClass, kRegionSize, kFreeArrayOffset, kSpaceSize, kResvLen in *.
  assert (SP : ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 /\ SB <= a < SB + 2^37) by (clear -Ha R1 R2 Q1 Q3 E3 E4; lia).
  destruct SP as [SP1 SP2].
  split; [clear -Ha R1 E2 E3 E5 SP1; lia|]. split; [clear -SP2 E2 E3; lia|]. split; [clear -SP1 E19; lia|]. split.
  { intros x Hx Rx. pose proof (IMG_LOW x Hx) as [L1 L2]. clear -SP2 E2 E3 Rx L2. lia. }
  split; [clear -SP1 E20; lia|]. split.
  { intros sc Hsc Rs. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ E7) as X. cbn [fst snd] in X. clear -SP1 Rs X. lia. }
  split.
  { pose proof (BS (ae_depot_nodes E) kDepotNodeBlockBytes (or_introl (conj (or_introl eq_refl) eq_refl))) as (_ & _ & DNR & _).
    pose proof (ak_store_sep _ _ _ K) as (SBR & _).
    intros bb len [[[<-|Hbb] ->]|[[<-|Hbb] ->]].
    - clear -SP1 DNR. lia.
    - destruct (ak_blocks_sep _ _ _ K bb kDepotNodeBlockBytes (or_introl (conj Hbb eq_refl))) as (_ & _ & _ & BR & _). unfold kResvLen in BR. clear -SP1 BR. lia.
    - unfold kResvLen, kStoreBlockBytes in *. clear -SP1 SBR. lia.
    - destruct (ak_blocks_sep _ _ _ K bb kStoreBlockBytes (or_intror (conj Hbb eq_refl))) as (_ & _ & _ & BR & _). unfold kResvLen, kStoreBlockBytes in *. clear -SP1 BR. lia. }
  split; [unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize; clear -SP2; lia|].
  intros c' Hc' Rf. unfold kNumClasses in Hc'. pose proof (RG c' Hc') as [_ [G3 G4]]. unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *.
  clear -Ha R1 R2 Q1 Q3 Hc' G3 G4 Rf. lia.
Qed.
Lemma bat_vs_chunk : forall b0 cb' cm' a, In b0 (as_tq s ++ as_gq s) -> as_chunks s !! cb' = Some cm' -> chunk_meta_fp cm' a ->
  ~ (b_addr b0 <= a < b_addr b0 + 8192).
Proof.
  intros b0 cb' cm' a Hb0 H' FPa R. pose proof WF as (WE & WR & _ & _ & WQ & _).
  pose proof (chunk_meta_in_block E P [] s cb' cm' a WF H' FPa) as [B1 B2].
  destruct (batch_block E [] s b0 WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb0)) as (CV & _ & _ & NCB).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  destruct (block_where E P [] s cb' cm' WF H') as [(J1 & J2 & c & Hc & PR & CVc & _ & _ & SP)|(sc & Hsc & _ & L1 & L2)]; unfold blk_lo in *.
  - destruct (carved_blocks_disjoint E s c (cm_alloc_beg cm') kBatchClass (b_addr b0) Hc HB24 WR CVc CV) as [[_ EQ]|D].
    + apply NCB. exists cb', cm'. split; [exact H'| exact EQ].
    + rewrite CS24 in D. clear -B1 B2 R D SP. lia.
  - destruct (bat_facts b0 a Hb0 R) as (_ & _ & _ & _ & _ & NS & _). apply (NS sc Hsc). unfold kPageSize in L1. clear -B1 B2 L1 L2. lia.
Qed.

Lemma bat_vs_bat : forall b1 b2 a, In b1 (as_tq s ++ as_gq s) -> In b2 (as_tq s ++ as_gq s) -> b_addr b1 <> b_addr b2 ->
  b_addr b1 <= a < b_addr b1 + 8192 -> ~ (b_addr b2 <= a < b_addr b2 + 8192).
Proof.
  intros b1 b2 a H1 H2 NE R1 R2. pose proof WF as (WE & WR & _).
  pose proof (bat_range b1 H1) as (_ & _ & C1). pose proof (bat_range b2 H2) as (_ & _ & C2).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  destruct (carved_blocks_disjoint E s kBatchClass (b_addr b1) kBatchClass (b_addr b2) HB24 HB24 WR C1 C2) as [[_ EQ]|D]; [exact (NE EQ)|].
  rewrite CS24 in D. clear -R1 R2 D. lia.
Qed.

(* [comment removed for export] *)
Section QX.
Variables (m m' : mem) (lo : Z) (tq' gq' : list batch).
#[warnings="-notation-for-abbreviation"] Notation s' := (qx_st s tq' gq').
Hypothesis REP : AREP s m.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWq s lo z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
(* [comment removed for export] *)
Hypothesis NC_qm : RW m' (INST + kInsQMutex) [C4 (zw 0)].
Hypothesis NC_qg : RW m' (INST + kInsQGlobal) [C8 (zw (qcount gq')); C8 (zw (list_first gq')); C8 (zw (list_last gq')); C8 (zw (qbytes gq'))].
Hypothesis NC_qc : RW m' (T + kThrQCache) [C8 (zw (qcount tq')); C8 (zw (list_first tq')); C8 (zw (list_last tq')); C8 (zw (qbytes tq'))].
Hypothesis BLt : arep_batch_list segs s' tq' m'.
Hypothesis BLg : arep_batch_list segs s' gq' m'.

(* [comment removed for export] *)
Lemma qx_tq : as_tq s' = tq'. Proof. destruct s; reflexivity. Qed.
Lemma qx_gq : as_gq s' = gq'. Proof. destruct s; reflexivity. Qed.
Lemma qx_tq_bytes : tq_bytes s' = qbytes tq'. Proof. destruct s; reflexivity. Qed.
Lemma qx_gq_bytes : gq_bytes s' = qbytes gq'. Proof. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Lemma AG_fp : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) -> ~ (INST <= a < INST + 3632) ->
  (forall b, In b (as_tq s ++ as_gq s) -> ~ (b_addr b <= a < b_addr b + 8192)) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NI NB. pose proof (fp_range a Ha) as BC'. pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BC' CR; lia|]. unfold FPWq. intros [X|[X|[X|[X|(b & Hb & X)]]]].
  - clear -X BC' LO. lia.
  - unfold kInsQMutex in X. clear -X NI. lia.
  - unfold kInsQGlobal in X. clear -X NI. lia.
  - unfold kThrQCache in X. clear -X NT. lia.
  - exact (NB b Hb X).
Qed.

Lemma AGimg1 : forall a, in_ranges (List.tl (arep_img_ranges E)) a -> m' (wa a) = m (wa a).
Proof.
  intros a (r & Hr & R). pose proof INST_img as (I1 & I2 & I3 & I4). pose proof Tpl as [[T1 T2] T3].
  assert (Hr' : In r (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; right; exact Hr).
  pose proof (IMG_LOW r Hr') as [L1 L2]. pose proof (IMG_INST r ltac:(apply in_app_iff; left; exact Hr)) as SEP.
  apply AG_fp; [left; exists r; split; [right; exact Hr| exact R] | clear -R L1 L2 T1 T2; lia | clear -R SEP; lia |].
  intros b Hb Rb. destruct (bat_facts b a Hb Rb) as (_ & _ & _ & NI & _). exact (NI r Hr' R).
Qed.
(* [comment removed for export] *)
Lemma AG_resv : forall a, arep_fp E (DepotFP E) s a -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 ->
  (forall b, In b (as_tq s ++ as_gq s) -> ~ (b_addr b <= a < b_addr b + 8192)) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha R NB. pose proof INST_img as (I1 & I2 & _). pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  rewrite kHighMemBeg_val in E2.
  apply AG_fp; [exact Ha| | clear -R I1 I2 E2; lia| exact NB].
  intros HT. destruct (Tpage_apart a HT) as (NR & _). exact (NR R).
Qed.
Lemma space_resv : forall a, SB <= a < SB + kSpaceSize + 0x1000 -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000.
Proof. intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). clear -Ha E3 E4. lia. Qed.
Lemma AGri : forall a, RI <= a < RI + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_resv; [right; left; exact Ha| | intros b Hb Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & _ & _ & NR & _); exact (NR Ha)].
  apply space_resv. unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha. lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_resv; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| | intros b Hb Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & _ & _ & _ & NF); exact (NF c' Hc Ha)].
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E P [] s a WF RM) as SP. apply space_resv. unfold kSpaceSize in *. clear -SP. lia.
Qed.
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. unfold kChunksBlockCount in Ha. pose proof INST_img as (I1 & I2 & I3 & I4). pose proof (proj1 WF) as WE.
  pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
  unfold img_sep in E33.
  apply AG_fp; [do 4 right; left; unfold kChunksBlockCount; exact Ha| | | intros b Hb Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & NP & _); apply NP; clear -Ha; lia].
  - intros HT. destruct (Tpage_apart a HT) as (_ & NP & _). clear -Ha NP. lia.
  - clear -Ha I3 I4 E33. lia.
Qed.
Lemma AG_secmap : forall a sc, arep_fp E (DepotFP E) s a -> In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc -> m' (wa a) = m (wa a).
Proof.
  intros a sc Ha Hsc R. pose proof INST_img as (I1 & I2 & I3 & I4). pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & _).
  pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & _ & _ & _ & SR).
  pose proof (SR _ E29) as XI.
  apply AG_fp; [exact Ha| | destruct (ae_img E); cbn [fst snd] in *; clear -R XI I3 I4; lia|].
  - intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). exact (NS sc Hsc R).
  - intros b Hb Rb. destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & NS & _). exact (NS sc Hsc R).
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
  pose proof (chunk_meta_in_block E P [] s cb cm a WF Hcm Ha) as [BL BU].
  destruct (block_where E P [] s cb cm WF Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
  - apply AG_resv; [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]| | intros b Hb; exact (bat_vs_chunk b cb cm a Hb Hcm Ha)].
    apply space_resv. clear -BL BU J1 J2. lia.
  - apply (AG_secmap a sc); [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]| exact Hsc| unfold kPageSize in *; clear -BL BU L1 L2; lia].
Qed.
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof INST_img as (I1 & I2 & I3 & I4). pose proof Tpl as [[T1 T2] T3]. destruct AK as [mo K].
  pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & E32 & E33 & _).
  assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - assert (Hr' : In r (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hr).
    pose proof (IMG_LOW r Hr') as [L1 L2]. pose proof (IMG_INST r ltac:(apply in_app_iff; right; exact Hr)) as SEP.
    apply AG_fp; [exact FPa| clear -R L1 L2 T1 T2; lia| clear -R SEP; lia|].
    intros b Hb Rb. destruct (bat_facts b a Hb Rb) as (_ & _ & _ & NI & _). exact (NI r Hr' R).
  - pose proof (BS b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). unfold img_sep in BI.
    apply AG_fp; [exact FPa| | clear -R BI I3 I4; lia|].
    + intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
    + intros b0 Hb0 Rb. destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
  - pose proof (BS b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). unfold img_sep in BI.
    apply AG_fp; [exact FPa| | clear -R BI I3 I4; lia|].
    + intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
    + intros b0 Hb0 Rb. destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
Qed.
Lemma AGsh : forall g v, Sh E s (8 * g) = Some v -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg. pose proof (AsanRepSec.Sh_granule_range segs E s) as SGR || idtac.
  assert (GR : 0 <= 8 * g < 2^47).
  { pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hg.
    destruct (in_some_region_map E s (8 * g)) eqn:RM.
    - pose proof (region_map_in_space E P [] s (8 * g) WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
      unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
    - destruct (in_some_sec_map s (8 * g)) eqn:SM.
      + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb0). apply andb_true_iff in Hb0 as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
        unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
      + cbn [orb] in Hg. destruct (sh_default_dom E (8 * g) && negb (sh_excluded E (8 * g))) eqn:C; [|discriminate].
        apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
        * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
          rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
        * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
          rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia. }
  assert (BAND : kLowAppEnd < kShadowBase + g < kHighMemBeg) by (rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia).
  pose proof INST_img as (I1 & I2 & _).
  apply AG_fp; [do 9 right; exists g, v; split; [reflexivity| exact Hg]| | rewrite kLowAppEnd_val in BAND; clear -BAND I1 I2; lia|].
  - intros HT. destruct (Tpage_apart _ HT) as (_ & _ & _ & _ & NBAND & _). apply NBAND. exact BAND.
  - intros b Hb Rb. destruct (bat_facts b _ Hb Rb) as (_ & NB & _). apply NB. clear -BAND. lia.
Qed.
(* [comment removed for export] *)
Lemma AGthr_cells : forall A k, T <= A -> A + k <= T + 4096 -> (A + k <= T + kThrQCache \/ T + kThrQCache + 32 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR. pose proof INST_img as (I1 & I2 & _).
  assert (HT : T <= z < T + 4096) by (clear -Hz H0 H1; lia).
  apply AG; [clear -HT T1 T3 CR; lia|]. unfold FPWq. intros [X|[X|[X|[X|(b & Hb & X)]]]].
  - clear -X HT T3 LO. lia.
  - unfold kInsQMutex in X. clear -X HT I1 I2 T2. lia.
  - unfold kInsQGlobal in X. clear -X HT I1 I2 T2. lia.
  - clear -X Hz H2. lia.
  - destruct (bat_facts b z Hb X) as (_ & _ & NT & _). exact (NT HT).
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.
(* [comment removed for export] *)
Lemma AGinst : forall A k, INST <= A -> A + k <= INST + 3632 ->
  (A + k <= INST + kInsQMutex \/ (INST + kInsQMutex + 4 <= A /\ A + k <= INST + kInsQGlobal) \/ INST + kInsQGlobal + 32 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR. pose proof INST_img as (I1 & I2 & I3 & I4).
  assert (HI : INST <= z < INST + 3632) by (clear -Hz H0 H1; lia).
  apply AG; [clear -HI I1 I2 CR; lia|]. unfold FPWq. intros [X|[X|[X|[X|(b & Hb & X)]]]].
  - clear -X HI I2 CR LO. lia.
  - unfold kInsQMutex, kInsQGlobal in *. clear -X Hz H2. lia.
  - unfold kInsQMutex, kInsQGlobal in *. clear -X Hz H2. lia.
  - unfold kThrQCache in X. clear -X HI I1 I2 T2. lia.
  - destruct (bat_facts b z Hb X) as (_ & _ & _ & NI & _). apply (NI (INST, 3632)); [apply in_app_iff; left; left; reflexivity| exact HI].
Qed.
Ltac ins_ag := apply AGinst; unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined in *; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia.

(* [comment removed for export] *)
Lemma repA_qx : arep_instance segs E s' m'.
Proof.
  pose proof REP as (RA & _). destruct RA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold arep_instance. rewrite qx_gq, qx_gq_bytes.
  replace (as_ptr_committed s') with (as_ptr_committed s) by (destruct s; reflexivity).
  replace (n_chunks s') with (n_chunks s) by (destruct s; reflexivity).
  replace (as_sec_stats s') with (as_sec_stats s) by (destruct s; reflexivity).
  replace (as_glob_allocated s') with (as_glob_allocated s) by (destruct s; reflexivity).
  replace (as_glob_mapped s') with (as_glob_mapped s) by (destruct s; reflexivity).
  split; [eapply rw_cells_agree'; [| exact A1]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A2]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A3]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A4]; ins_ag|].
  split; [destruct A5 as (bsl & U & L); exists bsl; split; [| exact L]; eapply u64arr_agree; [| exact U]; rewrite L; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A6]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A7]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A8]; ins_ag|].
  split; [exact NC_qm|]. split; [exact NC_qg|].
  split; [eapply rw_cells_agree'; [| exact A11]; ins_ag|].
  eapply rw_cells_agree'; [| exact A12]; ins_ag.
Qed.

(* [comment removed for export] *)
Lemma repD_qx : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  unfold arep_thread. rewrite qx_tq_bytes, qx_tq.
  replace (as_cache_allocated s') with (as_cache_allocated s) by (destruct s; reflexivity).
  replace (as_cache_mapped s') with (as_cache_mapped s) by (destruct s; reflexivity).
  replace (as_ts s') with (as_ts s) by (destruct s; reflexivity).
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [exact NC_qc|].
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). unfold percls_cells in *.
    replace (get_cache s' c') with (get_cache s c') by (destruct s; reflexivity). replace (as_cache_inited s') with (as_cache_inited s) by (destruct s; reflexivity).
    unfold kNumClasses in Hc'. split.
    - eapply rw_cells_agree'; [| exact X1]. thr_ag.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag. }
  split; [eapply rw_cells_agree'; [| exact D5]; thr_ag|].
  split; [eapply u64arr_agree; [| exact D6]; unfold tstats_words; rewrite length_map; cbn [length]; thr_ag|].
  split; [eapply u64arr_agree; [| exact D7]; rewrite length_map, length_ziota; thr_ag|].
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.

(* [comment removed for export] *)
Ltac zconsts Hx := unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined, kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats,
  kThrStats, kThrUnwinding, kRegSize, kBatchCap, kChunksBlockCount, kIaPageSizeOff in Hx |- *.
Ltac ag AG ARM := let Hx := fresh "Hx" in intros x Hx; cbn -[Z.add Z.mul Z.sub Z.of_nat Z.to_nat free_array region_beg region_of get_region Z.pow] in Hx; apply AG; ARM Hx.
Ltac agN1 AG k := ag AG ltac:(fun Hx => eexists; split; [eapply nth_error_In with (n := k); reflexivity| cbn [fst snd length asan_flags_bytes]; zconsts Hx; lia]).
Lemma repI_qx : arep_globals segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & RI' & _).
  destruct RI' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18). unfold arep_globals.
  replace (as_ia_inited s') with (as_ia_inited s) by (destruct s; reflexivity).
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
Theorem ARep_q_xfer : AREP s' m'.
Proof.
  pose proof REP as (RA & RB & RC & RD & RE & RF & RG & RH & RI & RJ).
  split; [exact repA_qx|].
  split; [apply (frameB' segs E s' m m' AGri); destruct s; exact RB|].
  split; [apply (frameC' segs E s' m m' WM); [intros a c Hc Ha; apply (AGfa a c Hc); destruct s; exact Ha| destruct s; exact RC]|].
  split; [exact repD_qx|].
  split; [apply (frameE' segs E s' m m' WM); [exact AGptr| intros a sc Hsc; apply AGsec; destruct s; exact Hsc| destruct s; exact RE]|].
  split; [apply (frameF' segs s' m m'); [intros a cb cm Hcm; apply (AGcm a cb cm); destruct s; exact Hcm| destruct s; exact RF]|].
  split; [split; [rewrite qx_tq; exact BLt| rewrite qx_gq; exact BLg]|].
  split; [apply (frameH' segs E s' m m' WM); [intros a Ha; apply AGdep; destruct s; exact Ha| destruct s; exact RH]|].
  split; [exact repI_qx|].
  apply (frameJ' segs E s' m m'); [intros g v Hg; apply (AGsh g v); destruct s; exact Hg| destruct s; exact RJ].
Qed.
End QX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section X3.
Variables (m m' : mem) (lo : Z).
#[warnings="-notation-for-abbreviation"] Notation tq := (as_tq s).
#[warnings="-notation-for-abbreviation"] Notation gq := (as_gq s).
Definition FPWx (z : Z) : Prop :=
     lo <= z
  \/ (INST + kInsQMutex <= z < INST + kInsQMutex + 4)
  \/ (INST + kInsQGlobal <= z < INST + kInsQGlobal + 32)
  \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (gq <> [] /\ list_last gq <= z < list_last gq + 8).
Hypothesis TQ : tq <> [].
Hypothesis REP : AREP s m.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWx z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis NC_qm : RW m' (INST + kInsQMutex) [C4 (zw 0)].
Hypothesis NC_qg : RW m' (INST + kInsQGlobal)
  [C8 (zw (qcount gq + qcount tq)); C8 (zw (match gq with [] => list_first tq | _ => list_first gq end)); C8 (zw (list_last tq)); C8 (zw (gq_bytes s + tq_bytes s))].
Hypothesis NC_qc : RW m' (T + kThrQCache) [C8 (zw 0); C8 (zw 0); C8 (zw 0); C8 (zw 0)].
Hypothesis NC_last : forall l0 b0, gq = l0 ++ [b0] -> RW m' (b_addr b0) [C8 (zw (list_first tq))].

Lemma list_last_snoc' : forall l0 b0, list_last (l0 ++ [b0]) = b_addr b0.
Proof. intros l0 b0. unfold list_last. rewrite last_last. destruct (l0 ++ [b0]) eqn:EL; [| reflexivity]. destruct l0; discriminate. Qed.
Lemma list_last_app : forall l1 l2, l2 <> [] -> list_last (l1 ++ l2) = list_last l2.
Proof.
  intros l1 l2 NE.
  assert (X : exists l0 b0, l2 = l0 ++ [b0]).
  { destruct l2 as [|b l2'] using rev_ind; [exfalso; exact (NE eq_refl)| exists l2', b; reflexivity]. }
  destruct X as (l0 & b0 & ->). rewrite app_assoc, !list_last_snoc'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma AGbat3 : forall a b, In b (tq ++ gq) -> b_addr b <= a < b_addr b + 8192 -> ~ (gq <> [] /\ list_last gq <= a < list_last gq + 8) -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha NL. destruct (bat_facts b a Hb Ha) as (BC & _ & NT & NI & _). pose proof alloc_ceiling_range as CR. pose proof INST_img as (I1 & I2 & _).
  assert (NIN : ~ (INST <= a < INST + 3632)) by (intros X; apply (NI (INST, 3632)); [apply in_app_iff; left; left; reflexivity| exact X]).
  apply AG; [clear -BC CR; lia|]. unfold FPWx. intros [X|[X|[X|[X|X]]]].
  - clear -X BC LO. lia.
  - unfold kInsQMutex in X. clear -X NIN. lia.
  - unfold kInsQGlobal in X. clear -X NIN. lia.
  - unfold kThrQCache in X. clear -X NT. lia.
  - exact (NL X).
Qed.

(* [comment removed for export] *)
Fixpoint bln (l : list batch) (n : Z) (mm : mem) : Prop :=
  match l with
  | [] => True
  | b :: rest => arep_batch segs s b (match rest with [] => n | b' :: _ => b_addr b' end) mm /\ bln rest n mm
  end.
Lemma bln_0 : forall sx l mm, bln l 0 mm <-> arep_batch_list segs sx l mm.
Proof. intros sx l mm. induction l as [|b l IH]; cbn; [tauto|]. rewrite IH. destruct l; tauto. Qed.
Lemma bln_app : forall l1 l2 n mm, l2 <> [] -> bln l1 (list_first l2) mm -> bln l2 n mm -> bln (l1 ++ l2) n mm.
Proof.
  induction l1 as [|b l1 IH]; intros l2 n mm NE H1 H2; [exact H2|]. cbn [bln app] in H1 |- *. destruct H1 as [HB H1].
  split; [| exact (IH l2 n mm NE H1 H2)]. destruct l1 as [|b1 l1']; [| exact HB]. cbn [app]. destruct l2; [exfalso; exact (NE eq_refl)| exact HB].
Qed.

Lemma NDall : List.NoDup (map b_addr (tq ++ gq)).
Proof. pose proof WF as (_ & _ & _ & _ & (_ & _ & ND & _) & _). unfold all_batches in ND. rewrite app_nil_r in ND. exact ND. Qed.

Lemma last_gq : gq <> [] -> exists l1 b1, gq = l1 ++ [b1].
Proof. intros NE. destruct gq as [|bb gg] using rev_ind; [exfalso; exact (NE eq_refl)| exists gg, bb; reflexivity]. Qed.
Lemma last_gq_distinct : forall l1 b1 b0, gq = l1 ++ [b1] -> In b0 tq \/ In b0 l1 -> b_addr b0 <> b_addr b1.
Proof.
  intros l1 b1 b0 E1 Hb0. pose proof NDall as ND. rewrite E1, app_assoc in ND.
  apply (nodup_map_sep b_addr (tq ++ l1) b1 [] b0 ND). rewrite app_nil_r. apply in_app_iff. exact Hb0.
Qed.

(* [comment removed for export] *)
Lemma bln_tq : bln tq 0 m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & [RG1 _] & _). apply (bln_0 s) in RG1.
  assert (K : forall l0, (forall b0, In b0 l0 -> In b0 tq) -> bln l0 0 m -> bln l0 0 m').
  { induction l0 as [|b0 l0 IH]; intros SUB H; [exact I|]. destruct H as [[X1 (junk & X2 & L)] H2].
    pose proof (SUB b0 ltac:(left; reflexivity)) as Hb0. assert (Hb0' : In b0 (tq ++ gq)) by (apply in_app_iff; left; exact Hb0).
    pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
    assert (NL : forall a, b_addr b0 <= a < b_addr b0 + 8192 -> ~ (gq <> [] /\ list_last gq <= a < list_last gq + 8)).
    { intros a Ha [NE R]. destruct (last_gq NE) as (l1 & b1 & E1). rewrite E1, list_last_snoc' in R.
      assert (Hb1 : In b1 (tq ++ gq)) by (apply in_app_iff; right; rewrite E1; apply in_app_iff; right; left; reflexivity).
      apply (bat_vs_bat b0 b1 a Hb0' Hb1 (last_gq_distinct l1 b1 b0 E1 (or_introl Hb0)) Ha). clear -R. lia. }
    split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]]. split.
    - eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros x Hx.
      apply (AGbat3 x b0 Hb0' ltac:(clear -Hx; lia) (NL x ltac:(clear -Hx; lia))).
    - exists junk. split; [| exact L]. eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map. intros x Hx.
      apply (AGbat3 x b0 Hb0' ltac:(clear -Hx L'; lia) (NL x ltac:(clear -Hx L'; lia))). }
  exact (K tq (fun b0 H => H) RG1).
Qed.

(* [comment removed for export] *)
Lemma bln_gq : bln gq (list_first tq) m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & [_ RG2] & _). apply (bln_0 s) in RG2.
  assert (CASE : gq = [] \/ exists l1 b1, gq = l1 ++ [b1]).
  { generalize gq. intros l. induction l as [|bb gg _] using rev_ind; [left; reflexivity| right; exists gg, bb; reflexivity]. }
  destruct CASE as [EG|(l1 & b1 & EG)]; [rewrite EG; exact I|]. rewrite EG in RG2 |- *.
  assert (Hb1 : In b1 (tq ++ gq)) by (apply in_app_iff; right; rewrite EG; apply in_app_iff; right; left; reflexivity).
  assert (K : forall l0, (forall b0, In b0 l0 -> In b0 l1) -> bln (l0 ++ [b1]) 0 m -> bln (l0 ++ [b1]) (list_first tq) m').
  { induction l0 as [|b0 l0 IH]; intros SUB H.
    - (* [comment removed for export] *)
      cbn [bln app] in H |- *. destruct H as [[X1 (junk & X2 & L)] _]. split; [| exact I].
      pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
      split.
      + apply rh_split with (cs1 := [C8 (zw 0)]) in X1. destruct X1 as [_ X1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in X1.
        apply (rh_join_at segs m' _ (b_addr b1 + 8) [C8 (zw (list_first tq))]); [exact (NC_last l1 b1 EG)| | cbn; lia].
        eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros x Hx.
        apply (AGbat3 x b1 Hb1 ltac:(clear -Hx; lia)). intros [_ R]. rewrite EG, list_last_snoc' in R. clear -Hx R. lia.
      + exists junk. split; [| exact L]. eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map. intros x Hx.
        apply (AGbat3 x b1 Hb1 ltac:(clear -Hx L'; lia)). intros [_ R]. rewrite EG, list_last_snoc' in R. clear -Hx R. lia.
    - (* [comment removed for export] *)
      cbn [bln app] in H |- *. destruct H as [[X1 (junk & X2 & L)] H2].
      pose proof (SUB b0 ltac:(left; reflexivity)) as Hb0. assert (Hb0' : In b0 (tq ++ gq)) by (apply in_app_iff; right; rewrite EG; apply in_app_iff; left; exact Hb0).
      pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
      assert (NL : forall a, b_addr b0 <= a < b_addr b0 + 8192 -> ~ (gq <> [] /\ list_last gq <= a < list_last gq + 8)).
      { intros a Ha [_ R]. rewrite EG, list_last_snoc' in R.
        apply (bat_vs_bat b0 b1 a Hb0' Hb1 (last_gq_distinct l1 b1 b0 EG (or_intror Hb0)) Ha). clear -R. lia. }
      split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]].
      replace (match l0 ++ [b1] with [] => list_first tq | b' :: _ => b_addr b' end) with (match l0 ++ [b1] with [] => 0 | b' :: _ => b_addr b' end) by (destruct l0; reflexivity).
      split.
      + eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros x Hx.
        apply (AGbat3 x b0 Hb0' ltac:(clear -Hx; lia) (NL x ltac:(clear -Hx; lia))).
      + exists junk. split; [| exact L]. eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map. intros x Hx.
        apply (AGbat3 x b0 Hb0' ltac:(clear -Hx L'; lia) (NL x ltac:(clear -Hx L'; lia))). }
  exact (K l1 (fun b0 H => H) RG2).
Qed.

Theorem ARep_after_xfer : AREP (qx_st s [] (gq ++ tq)) m'.
Proof.
  apply (ARep_q_xfer m m' lo [] (gq ++ tq) REP WM); [| exact LO| exact NC_qm| | exact NC_qc| exact I|].
  - intros z Hz NF. apply AG; [exact Hz|]. intros X. apply NF. unfold FPWq. unfold FPWx in X.
    destruct X as [X|[X|[X|[X|[NE X]]]]]; [left; exact X| right; left; exact X| do 2 right; left; exact X| do 3 right; left; exact X|].
    do 4 right. destruct (last_gq NE) as (l1 & b1 & E1). exists b1. rewrite E1, list_last_snoc' in X.
    split; [apply in_app_iff; right; rewrite E1; apply in_app_iff; right; left; reflexivity| clear -X; lia].
  - unfold qcount in NC_qg |- *. rewrite length_app, Nat2Z.inj_add, qbytes_app, (list_last_app gq tq TQ).
    replace (list_first (gq ++ tq)) with (match gq with [] => list_first tq | _ :: _ => list_first gq end) by (destruct gq; reflexivity).
    unfold gq_bytes, tq_bytes in NC_qg. exact NC_qg.
  - apply (proj1 (bln_0 (qx_st s [] (gq ++ tq)) (gq ++ tq) m')). apply (bln_app gq tq 0 m' TQ bln_gq bln_tq).
Qed.
End X3.
End WFS.
End RQX.
End RC__1.

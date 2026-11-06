(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf2 AsanWf3 AsanWf4.
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
Variable P : list Z.
Variable D : list batch.
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ranges_free_In : forall l a n b m, ranges_free l a n = true -> In (b, m) l -> a + n <= b \/ b + m <= a.
Proof.
  intros l a n b m H Hin. unfold ranges_free in H. rewrite forallb_forall in H. specialize (H _ Hin). cbn in H.
  unfold iv_disjoint in H. apply Bool.orb_prop in H as [H|H]; [left|right]; apply Z.leb_le in H; exact H.
Qed.

Lemma wf_chunk_mono_sec : forall s s' cb cm,
  as_regions s' = as_regions s -> as_cache s' = as_cache s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  (forall sc, In sc (as_sec s) -> In sc (as_sec s')) ->
  wf_chunk E P D s cb cm -> wf_chunk E P D s' cb cm.
Proof.
  intros s s' cb cm HR HC HT HG HS (A & B & C & D0 & E0).
  unfold wf_chunk, carved, in_free, in_cache, is_batch, all_batches, region_of, get_region, get_cache in *.
  rewrite HR, HC, HT, HG. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [|exact E0].
  destruct (cm_prim cm); [exact D0|]. destruct D0 as (D1 & sc & Hsc & X). split; [exact D1|]. exists sc. split; [apply HS; exact Hsc| exact X].
Qed.

Lemma map_size_facts : forall n, map_size n mod kPageSize = 0 /\ needed n + kPageSize <= map_size n /\ 2 * kPageSize <= map_size n.
Proof.
  intros n. unfold map_size. pose proof (round_up_mod (needed n) kPageSize ltac:(unfold kPageSize; lia)).
  pose proof (round_up_ge (needed n) kPageSize ltac:(unfold kPageSize; lia)).
  pose proof (needed_ge n). pose proof (rz_size_pos n). pose proof (req_geom n).
  split; [|split; [lia|]].
  - rewrite <- Z.add_mod_idemp_r by (unfold kPageSize; lia). rewrite Z.mod_same by (unfold kPageSize; lia). rewrite Z.add_0_r. exact H.
  - assert (needed n >= 1).
    { unfold needed, needed1. pose proof (rounded_ge n). destruct (from_primary n); lia. }
    assert (kPageSize <= round_up (needed n) kPageSize).
    { pose proof (Z.mod_pos_bound (round_up (needed n) kPageSize) kPageSize ltac:(unfold kPageSize; lia)).
      apply Z.mod_divide in H as [q Hq]; [|unfold kPageSize; lia]. unfold kPageSize in *. nia. }
    lia.
Qed.

(* [comment removed for export] *)
Definition sec_fresh (s : astate) (r msz : Z) : Prop :=
  r mod kPageSize = 0 /\ app_mem r msz /\ r + msz <= alloc_ceiling
  /\ (r + msz <= SB \/ SB + kSpaceSize <= r)
  /\ (forall sc, In sc (as_sec s) -> r + msz <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= r)
  /\ (forall x, In x (ae_reserved E) -> r + msz <= fst x \/ fst x + snd x <= r).

Lemma sec_fresh_of_grant : forall s r msz, AWF s -> 0 < msz ->
  r mod kPageSize = 0 -> ranges_free (known_ranges E s) r msz = true -> app_mem r msz -> r + msz <= alloc_ceiling ->
  sec_fresh s r msz.
Proof.
  intros s r msz WF POS AL RF HB HE. destruct WF as ((W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & _) & _).
  unfold known_ranges in RF.
  split; [exact AL|]. split; [exact HB|]. split; [exact HE|]. split; [|split].
  - pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; left; exact W7)). unfold kSpaceSize in *. lia.
  - intros sc Hsc. apply (ranges_free_In _ _ _ _ _ RF). apply in_app_iff; right. apply in_app_iff; left. apply in_map_iff. exists sc; auto.
  - intros [b k] Hx. cbn [fst snd]. apply (ranges_free_In _ _ _ _ _ RF). apply in_app_iff; left; exact Hx.
Qed.

(* [comment removed for export] *)
Lemma sec_fresh_untracked : forall s r msz a, AWF s -> sec_fresh s r msz -> r + kPageSize <= a -> a + 8 < r + msz ->
  untracked D s a /\ as_chunks s !! a = None.
Proof.
  intros s r msz a WF (AL & HB & HE & OUT & DISJ & FSJ) LO HI.
  pose proof WF as X. destruct X as (WE & WR & WC & WCH & WQ & WS & WD).
  assert (NCB : forall cb cm, as_chunks s !! cb = Some cm -> cm_alloc_beg cm <> a /\ cb <> a).
  { intros cb cm Hcm. pose proof (chunk_beg_loc E P D s cb cm WF Hcm) as LOC.
    destruct WCH as [K1 _]. destruct (K1 cb cm Hcm) as (_ & B & _ & D0 & _).
    destruct (cm_prim cm) as [c|].
    - destruct LOC as (Hc & CV & L1 & L2). pose proof (carved_in_space E s c _ Hc WR CV) as [I1 I2].
      pose proof (class_size_mod c Hc) as [_ SZ]. unfold kRegionSize, kSpaceSize, kPageSize in *. split; lia.
    - destruct LOC as (sc & Hsc & L1 & L2 & _). pose proof (DISJ sc Hsc) as DJ.
      destruct D0 as (_ & sc' & Hsc' & Hab & Hms & _). pose proof (DISJ sc' Hsc') as DJ'.
      pose proof (map_size_facts (cm_n cm)) as (_ & _ & M2). rewrite <- Hms in M2.
      unfold kPageSize in *. split; lia. }
  split; [split|].
  - intros (cb & cm & Hcm & Ha). exact (proj1 (NCB cb cm Hcm) Ha).
  - intros (b & Hb & Hba). destruct (batch_block E D s b WQ Hb) as (CV & _).
    pose proof (carved_in_space E s kBatchClass _ ltac:(unfold kBatchClass, kLargestClassID; lia) WR CV) as [I1 I2].
    rewrite Hba in I1, I2. unfold kRegionSize, kSpaceSize, kPageSize, kBatchClass in *.
    pose proof (class_size_mod 24 ltac:(unfold kBatchClass, kLargestClassID; lia)) as [_ SZ]. lia.
  - destruct (as_chunks s !! a) as [cm|] eqn:H; [|reflexivity]. exfalso. exact (proj2 (NCB a cm H) eq_refl).
Qed.

Lemma wf_quarantine_same : forall s s',
  as_regions s' = as_regions s -> as_cache s' = as_cache s -> as_chunks s' = as_chunks s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  wf_quarantine E D s -> wf_quarantine E D s'.
Proof.
  intros s s' HR HC HK HT HG W.
  unfold wf_quarantine, wf_batch, wf_dbatch, all_batches, carved, in_free, in_cache, is_chunk_block, chunk_used_size, tq_bytes, gq_bytes,
    region_of, get_region, get_cache in *.
  rewrite HR, HC, HK, HT, HG. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sec_alloc_spec : forall s0 n,
  AWF s0 -> n_chunks s0 < kChunksBlockCount ->
  hoare (fun s => s = s0) (sec_alloc E (needed n))
    (fun s' r => match r with
       | None => s' = s0
       | Some ab => AWF s' /\ as_regions s' = as_regions s0 /\ as_cache s' = as_cache s0 /\ as_cache_inited s' = as_cache_inited s0
                    /\ as_chunks s' = as_chunks s0 /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0 /\ as_keys s' = as_keys s0
                    /\ exists r, ab = r + kPageSize /\ as_sec s' = as_sec s0 ++ [mkSec r (map_size n) (needed n)] /\ sec_fresh s0 r (map_size n)
       end).
Proof.
  intros s0 n WF ROOM. unfold sec_alloc.
  change (round_up (needed n) kPageSize + kPageSize) with (map_size n).
  pose proof (map_size_facts n) as (MSM & MSG & MS2).
  eapply hoare_bind; [apply (call_mmap_anon_frame E (fun s => s = s0))|].
  intros r. apply hoare_pre. intros s1 (-> & GR). destruct r as [mb|]; [|apply hoare_ret; auto].
  destruct (GR mb eq_refl) as (AL & POS & CEIL & RF & HB & NP1 & NP2 & HE). clear GR.
  assert (SF : sec_fresh s0 mb (map_size n)) by (apply sec_fresh_of_grant; [exact WF| unfold kPageSize in *; lia| assumption..]).
  apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->).
  set (s1 := upd_ts _ s0).
  apply hoare_get_bind. intros s ->.
  assert (NC1 : n_chunks s1 = n_chunks s0) by reflexivity.
  unfold acheck. replace (n_chunks s1 <? 2 ^ 20) with true by (symmetry; apply Z.ltb_lt; rewrite NC1; unfold kChunksBlockCount in ROOM; lia).
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s1); auto|]. intros []. apply hoare_pre. intros s ->.
  pose proof WF as X. destruct X as (WE & WR & WC & WCH & WQ & (S1 & S2 & S3 & S4 & S5) & WD).
  eapply hoare_bind with (Q := fun s2 _ => exists pc, s2 = upd_ptr_committed pc s1 /\ n_chunks s0 + 1 <= pc /\ (pc = 0 /\ as_sec s0 = [] \/ pc = kChunksBlockCount)).
  { destruct (n_chunks s1 =? as_ptr_committed s1) eqn:EQ.
    - apply Z.eqb_eq in EQ. rewrite NC1 in EQ. change (as_ptr_committed s1) with (as_ptr_committed s0) in EQ.
      eapply hoare_bind; [apply (call_mmap_fixed_frame (fun s => s = s1))|].
      intros ok. apply hoare_pre. intros s ->. destruct ok; [|apply hoare_spin].
      apply hoare_upd. intros s ->. exists (as_ptr_committed s0 + kChunksBlockCount).
      split; [reflexivity|]. unfold kChunksBlockCount in *. destruct S1 as [[S1a S1b]|S1a]; [|lia]. split; [lia|]. right. lia.
    - apply Z.eqb_neq in EQ. rewrite NC1 in EQ. change (as_ptr_committed s1) with (as_ptr_committed s0) in EQ.
      apply hoare_ret. intros s ->. exists (as_ptr_committed s0). split; [subst s1; destruct s0; reflexivity|].
      destruct S1 as [[S1a S1b]|S1a].
      + exfalso. apply EQ. rewrite S1a. unfold n_chunks. rewrite S1b. reflexivity.
      + split; [lia|]. right; exact S1a. }
  intros []. apply hoare_pre. intros s2 (pc & -> & PC1 & PC2).
  apply hoare_upd_bind. apply hoare_ret. intros s' (s & -> & ->).
  set (sc := mkSec mb (map_size n) (needed n)).
  set (s' := upd_glob _ _ _).
  assert (HS' : as_sec s' = as_sec s0 ++ [sc]) by reflexivity.
  assert (HR' : as_regions s' = as_regions s0) by reflexivity.
  assert (HC' : as_cache s' = as_cache s0) by reflexivity.
  assert (HK' : as_chunks s' = as_chunks s0) by reflexivity.
  assert (HT' : as_tq s' = as_tq s0) by reflexivity.
  assert (HG' : as_gq s' = as_gq s0) by reflexivity.
  assert (HP' : as_ptr_committed s' = pc) by reflexivity.
  destruct SF as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (WF' : AWF s').
  { split; [exact WE|]. split; [eapply wf_regions_same; [exact HR'| exact WR]|].
    split; [eapply wf_cache_same; [exact HR'| exact HC'| reflexivity| exact WC]|].
    split.
    { destruct WCH as [K1 K2]. split; [| rewrite HK'; exact K2].
      intros cb cm H. rewrite HK' in H. eapply wf_chunk_mono_sec; [exact HR'| exact HC'| exact HT'| exact HG'| | exact (K1 _ _ H)].
      intros sc0 Hsc0. rewrite HS'. apply in_app_iff. left; exact Hsc0. }
    split; [eapply wf_quarantine_same; [exact HR'| exact HC'| exact HK'| exact HT'| exact HG'| exact WQ]|].
    split; [|exact WD].
    unfold wf_secondary. rewrite HP', HS'. unfold n_chunks. rewrite HS', length_app. cbn [length].
    split; [destruct PC2 as [[-> ->] | ->]; [left; split; [reflexivity|]; cbn; unfold n_chunks in PC1; cbn in PC1; exfalso; lia| right; reflexivity]|].
    split; [unfold n_chunks in PC1; lia|].
    split.
    { intros sc0 Hsc0. apply in_app_iff in Hsc0 as [Hsc0|[<-|[]]]; [exact (S3 sc0 Hsc0)|].
      subst sc; cbn. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [lia|]. split; [exact MSM|]. split; [exact F4| exact F6]. }
    split.
    { rewrite map_app. cbn. apply NoDup_app; [exact S4| constructor; [intros []| constructor]|].
      intros a Ha [<-|[]]. apply in_map_iff in Ha as (sc0 & Hmb & Hsc0). destruct (F5 sc0 Hsc0) as [X|X].
      - subst sc; cbn in X. lia.
      - destruct (S3 sc0 Hsc0) as (_ & _ & _ & SZ0 & _). subst sc; cbn in X. rewrite Hmb in X. lia. }
    intros a b Ha Hb NE. apply in_app_iff in Ha as [Ha|[<-|[]]]; apply in_app_iff in Hb as [Hb|[<-|[]]].
    - exact (S5 a b Ha Hb NE).
    - subst sc; cbn. destruct (F5 a Ha); lia.
    - subst sc; cbn. destruct (F5 b Hb); lia.
    - exfalso; exact (NE eq_refl). }
  split; [exact WF'|]. split; [exact HR'|]. split; [exact HC'|]. split; [reflexivity|]. split; [exact HK'|]. split; [exact HT'|]. split; [exact HG'|]. split; [reflexivity|].
  exists mb. split; [reflexivity|]. split; [exact HS'|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5| exact F6].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma untracked_frame : forall s s' a, as_chunks s' = as_chunks s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  untracked D s a -> untracked D s' a.
Proof.
  intros s s' a HK HT HG U. unfold untracked, is_chunk_block, is_batch, all_batches in *. rewrite HK, HT, HG. exact U.
Qed.

Lemma amalloc_core_sec_spec : forall s0 key n,
  depot_ok E s0 key -> 0 <= n < 2^40 -> from_primary n = false -> AWF s0 -> malloc_pre s0 n ->
  hoare (fun s => s = s0) (amalloc_core E key n)
    (fun s' r => AWF s' /\ depot_n_ids E s' <= depot_n_ids E s0 + 1 /\
       match r with
       | None => as_chunks s' = as_chunks s0 /\ as_sec s' = as_sec s0
       | Some p => exists ab id mb, p = ab + rz_size n /\ 1 <= id /\ ab = mb + kPageSize
                   /\ as_chunks s0 !! (p - kChunkHeaderSize) = None
                   /\ as_chunks s' = <[p - kChunkHeaderSize := new_chunk ab n id]> (as_chunks s0)
                   /\ as_sec s' = as_sec s0 ++ [mkSec mb (map_size n) (needed n)] /\ p mod 16 = 0
       end).
Proof.
  intros s0 key n HK Hn PR WF PRE. unfold malloc_pre in PRE. rewrite PR in PRE.
  unfold amalloc_core. rewrite PR.
  unfold acheck. replace (n <? 2 ^ 40) with true by (symmetry; apply Z.ltb_lt; lia).
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s0); auto|]. intros [].
  apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->). set (s0' := upd_nprimc _ _ s0).
  assert (WF0' : AWF s0') by (eapply AWf_same_core; [| exact WF]; unfold same_core; repeat split; reflexivity).
  change (as_chunks s0) with (as_chunks s0'). change (as_sec s0) with (as_sec s0').
  eapply hoare_bind; [apply (sec_alloc_spec s0' n WF0' PRE)|].
  intros r. destruct r as [ab|].
  2:{ apply hoare_pre. intros s1 ->. apply hoare_upd_bind. apply hoare_ret. intros s' (s & -> & ->).
      split; [eapply AWf_same_core; [apply same_core_upd_oom| exact WF0']|]. split; [unfold depot_n_ids; cbn; lia|]. split; reflexivity. }
  apply hoare_pre. intros s1 (WF1 & HR1 & HC1 & HI1 & HK1 & HT1 & HG1 & HKy1 & (mb & -> & HS1 & SF)).
  assert (HK1' : depot_ok E s1 key) by (unfold depot_ok, depot_n_ids in *; rewrite HKy1; exact HK).
  pose proof (map_size_facts n) as (MSM & MSG & MS2). pose proof (rz_size_pos n) as RP. pose proof (needed_ge n) as NG.
  pose proof (req_geom n) as (G1 & G2 & G3 & G4 & G5).
  (* [comment removed for export] *)
  destruct (sec_fresh_untracked s0' mb (map_size n) (mb + kPageSize) WF0' SF ltac:(lia) ltac:(unfold kPageSize in *; lia)) as [U0 _].
  destruct (sec_fresh_untracked s0' mb (map_size n) (mb + kPageSize + rz_size n - kChunkHeaderSize) WF0' SF
              ltac:(unfold kChunkHeaderSize; lia) ltac:(unfold kPageSize, kChunkHeaderSize in *; lia)) as [_ NONE0].
  eapply hoare_bind; [apply (depot_put_wf E P D s1 key HK1' WF1)|].
  intros id. apply hoare_pre. intros s2 (WF2 & (SR & SC & SI & SK & ST & SG & SS & SP) & ID & NID).
  set (ab := mb + kPageSize) in *.
  set (cb := ab + rz_size n - kChunkHeaderSize) in *.
  assert (NONE : as_chunks s2 !! cb = None) by (rewrite SK, HK1; exact NONE0).
  apply hoare_get_bind. intros s ->. rewrite NONE.
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s2); auto|]. intros []. apply hoare_pre. intros s ->.
  apply hoare_upd_bind. apply hoare_pre. intros s3 (s & -> & ->).
  set (cm := mkCM ab (rz_log n) (req n) None (CAllocated id)).
  set (s3 := upd_dead _ (upd_chunks _ s2)).
  assert (U2 : untracked D s2 ab).
  { eapply untracked_frame; [| | | exact U0]; [rewrite SK, HK1| rewrite ST, HT1| rewrite SG, HG1]; reflexivity. }
  assert (WCM : wf_chunk E P D s2 cb cm).
  { unfold wf_chunk. subst cm; cbn [cm_n cm_prim cm_state cm_rz_log cm_alloc_beg].
    split; [unfold cm_chunk_beg, cm_user_beg; cbn [cm_rz_log cm_alloc_beg]; subst cb; unfold rz_size; reflexivity|].
    split; [clear -G5 Hn; unfold req in *; lia|]. split; [symmetry; exact G1|]. split; [|exact ID].
    split; [rewrite G3; exact PR|]. exists (mkSec mb (map_size n) (needed n)). cbn.
    split; [rewrite SS, HS1; apply in_app_iff; right; left; reflexivity|].
    split; [reflexivity|]. split; [unfold map_size; rewrite G4; reflexivity| symmetry; exact G4]. }
  assert (WF3 : AWF s3).
  { subst s3. apply AWf_register_chunk; [exact WF2| exact NONE| exact WCM| exact U2]. }
  eapply hoare_bind; [apply (poison_zero_frame (fun s => s = s3)); reflexivity|]. intros [].
  apply hoare_pre. intros s ->.
  apply hoare_upd_bind. apply hoare_ret. intros s' (s & -> & ->).
  split; [eapply AWf_same_core; [apply same_core_upd_ts| exact WF3]|].
  split; [unfold depot_n_ids in *; cbn; rewrite HKy1 in NID; cbn in NID; lia|].
  exists ab, id, mb. split; [reflexivity|]. split; [exact ID|]. split; [reflexivity|].
  change (ab + rz_size n - kChunkHeaderSize) with cb.
  split; [exact NONE0|].
  split; [cbn; rewrite SK, HK1; unfold new_chunk; rewrite PR; reflexivity|].
  split; [cbn; rewrite SS, HS1; reflexivity|].
  destruct SF as (F1 & _). subst ab. unfold kPageSize in *. pose proof (rz_size_mod16 n) as RM.
  apply Z.mod_divide in F1; [|lia]. destruct F1 as [q Hq]. apply Z.mod_divide in RM; [|lia]. destruct RM as [q' Hq'].
  apply Z.mod_divide; [lia|]. exists (q * 256 + 256 + q'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem amalloc_spec : forall s0 key n,
  depot_ok E s0 key -> 0 <= n < 2^40 -> AWF s0 -> malloc_pre s0 n ->
  hoare (fun s => s = s0) (amalloc E key n)
    (fun s' r => AWF s' /\ depot_n_ids E s' <= depot_n_ids E s0 + 1 /\
       match r with
       | None => as_chunks s' = as_chunks s0
       | Some p => p mod 16 = 0 /\ as_chunks s0 !! (p - kChunkHeaderSize) = None
                   /\ exists ab id, 1 <= id /\ p = ab + rz_size n
                        /\ as_chunks s' = <[p - kChunkHeaderSize := new_chunk ab n id]> (as_chunks s0)
       end).
Proof.
  intros s0 key n HK Hn WF PRE. unfold amalloc. destruct (from_primary n) eqn:PR.
  - eapply hoare_conseq; [apply (amalloc_core_prim_spec E P D s0 key n HK ltac:(lia) PR WF PRE)| auto|].
    cbn beta. intros s [p|] (W & N & X); (split; [exact W|]); (split; [exact N|]); [| exact X].
    destruct X as (ab & id & A & B & C & D0 & _ & M). split; [exact M|]. split; [exact C|]. exists ab, id. auto.
  - eapply hoare_conseq; [apply (amalloc_core_sec_spec s0 key n HK Hn PR WF PRE)| auto|].
    cbn beta. intros s [p|] (W & N & X); (split; [exact W|]); (split; [exact N|]); [| exact (proj1 X)].
    destruct X as (ab & id & mb & A & B & _ & C & D0 & _ & M). split; [exact M|]. split; [exact C|]. exists ab, id. auto.
Qed.

End WF.
End RC__1.

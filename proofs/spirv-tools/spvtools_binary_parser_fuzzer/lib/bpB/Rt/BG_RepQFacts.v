(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BG_RepQ.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma carved_rangeQ : forall st XC XB c a, WFQ st XC XB -> carved st c a ->
  region_beg st c <= a /\ a + class_size c <= region_beg st c + kFreeArrayOffset /\ 0 < class_size c <= 65536.
Proof.
  intros st XC XB c a W (Hc & Hsz & H0 & Hm & Hle). pose proof (WFQ_region st XC XB c W Hc) as RO.
  pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_bound _ _ RO). pose proof (class_size_table_facts c Hc).
  unfold kUserMapSize in *. lia.
Qed.
Lemma carved_sepQ : forall st XC XB c a c' a', WFQ st XC XB -> carved st c a -> carved st c' a' ->
  (c = c' /\ a = a') \/ a + class_size c <= a' \/ a' + class_size c' <= a.
Proof.
  intros st XC XB c a c' a' W Ca Ca'.
  pose proof (carved_rangeQ st XC XB c a W Ca) as (R1 & R2 & R3). pose proof (carved_rangeQ st XC XB c' a' W Ca') as (R1' & R2' & R3').
  destruct Ca as (Hc & Hsz & H0 & Hm & Hle). destruct Ca' as (Hc' & Hsz' & H0' & Hm' & Hle').
  destruct (Z.eq_dec c c') as [<-|Hne].
  - destruct (Z.eq_dec a a') as [<-|Hna]; [left; auto| right].
    destruct (proj1 (Z.mod_divide (a - region_beg st c) (class_size c) Hsz) Hm) as [q Hq].
    destruct (proj1 (Z.mod_divide (a' - region_beg st c) (class_size c) Hsz) Hm') as [q' Hq'].
    assert (q <> q') by (intros ->; lia).
    destruct (Z.lt_ge_cases q q'); nia.
  - right. unfold kFreeArrayOffset in *.
    destruct (regions_disjoint st c c' ltac:(lia) ltac:(lia) Hne); lia.
Qed.
Lemma carved_of_elemQ : forall st XC XB c cp, WFQ st XC XB -> 0 <= c < kNumClasses ->
  0 <= cp -> Z.shiftl cp kCompactPtrScale < rg_allocated_user (get_region st c) ->
  class_size c <> 0 -> Z.shiftl cp kCompactPtrScale mod class_size c = 0 ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st XC XB c cp W Hc A B C D. rewrite shiftl4 in *. rewrite compact_to_addr_eq. unfold carved.
  replace (region_beg st c + cp * 16 - region_beg st c) with (cp * 16) by lia.
  pose proof (class_size_table_facts c Hc) as T. pose proof (ro_alloc_mod _ _ (WFQ_region st XC XB c W Hc) C) as AM.
  repeat split; try lia. apply mult_below; lia.
Qed.
Lemma carved_freeQ : forall st XC XB c cp, WFQ st XC XB -> 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st XC XB c cp W Hc Hin. pose proof (ro_fa_elems _ _ (WFQ_region st XC XB c W Hc) cp Hin) as (A & B & C & D).
  eapply carved_of_elemQ; eassumption.
Qed.
Lemma carved_cacheQ : forall st XC XB c cp, WFQ st XC XB -> 0 <= c < kNumClasses -> In cp (pc_chunks (get_pc st c)) ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st XC XB c cp W Hc Hin. pose proof (co_elems _ _ (WFQ_cache st XC XB c W Hc) cp Hin) as (A & B & C & D).
  eapply carved_of_elemQ; eassumption.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section FactsQ.
  Variable s : ast.
  Variables XC XB : list Z.
  Hypothesis OKQ : placed_ok s /\ WFQ (a_st s) XC XB.
  Let st := a_st s.
  Let W : WFQ st XC XB. Proof. exact (proj2 OKQ). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKQ). Qed.

  Lemma carved_in_spaceQ : forall c a, carved st c a ->
    a_sb s <= a /\ a + class_size c <= a_sb s + kSpaceSize /\ 0 < class_size c.
  Proof.
    intros c a C. pose proof (carved_rangeQ st XC XB c a W C) as (R1 & R2 & R3). destruct C as (Hc & _).
    pose proof (region_in_space st c Hc) as [S1 S2]. unfold a_sb, kFreeArrayOffset in *. unfold st in *. lia.
  Qed.

  Lemma chunk_geomQ : forall ch, In ch (chunk_list st) ->
    let u := ch_user_beg ch in let a := ch_alloc_beg ch in let n := ch_used ch in
    16 <= ch_rz ch /\ u = a + ch_rz ch /\ 1 <= n /\ a + ch_rz ch + round_up n 8 <= ch_end ch /\ n <= round_up n 8 < n + 8 /\ round_up n 8 = 8 * nsh n
    /\ (if ch_primary ch then carved st (ch_class ch) a /\ ch_end ch = a + class_size (ch_class ch)
        else exists h, In h (as_sec st) /\ sc_map_beg h = a - kPageSize /\ ch_end ch = sc_map_beg h + sc_map_size h).
  Proof.
    intros ch Hin. pose proof (WFQ_chunk st XC XB ch W Hin) as CO.
    destruct CO as (U1 & U2 & U3 & U4 & REST).
    pose proof (rz_size_facts (ch_used ch)) as RZ.
    change (rz_size (ch_used ch)) with (rq_rz (compute_req (ch_used ch))) in RZ. rewrite <- U3 in RZ. destruct RZ as (RZ1 & RZ2 & _).
    assert (NS : round_up (ch_used ch) 8 = 8 * nsh (ch_used ch) /\ ch_used ch <= round_up (ch_used ch) 8 < ch_used ch + 8).
    { unfold nsh, round_up. Z.div_mod_to_equations. lia. }
    assert (RD : rq_rounded (compute_req (ch_used ch)) = round_up (Z.max (ch_used ch) 8) 8 /\ round_up (ch_used ch) 8 <= round_up (Z.max (ch_used ch) 8) 8).
    { split; [reflexivity|]. unfold round_up. Z.div_mod_to_equations. nia. }
    assert (ND : rq_needed (compute_req (ch_used ch)) = rq_rounded (compute_req (ch_used ch)) + ch_rz ch + (if rq_primary (compute_req (ch_used ch)) then 0 else ch_rz ch)).
    { rewrite U3. unfold compute_req. cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.eqb]. destruct (round_up (Z.max (ch_used ch) 8) 8 + rz_size (ch_used ch) <=? kMaxSize); cbn; lia. }
    repeat split; try lia.
    - destruct (ch_primary ch) eqn:E.
      + destruct REST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite P1 in ND. unfold ch_end. rewrite E. lia.
      + destruct REST as (P1 & P2 & i & h & Hi & Hb & Hsz & Hms). rewrite P1 in ND. unfold ch_end. rewrite E.
        unfold round_up in *. unfold kPageSize in *. Z.div_mod_to_equations. nia.
    - destruct (ch_primary ch) eqn:E.
      + destruct REST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). split; [| unfold ch_end; rewrite E; reflexivity].
        unfold carved. pose proof (class_size_table_facts (ch_class ch)).
        assert (HC : 0 <= ch_class ch < kNumClasses).
        { rewrite P3. unfold class_of_addr. pose proof (Z.land_ones (Z.shiftr (ch_alloc_beg ch - as_space_beg st) kRegionSizeLog) 5).
          change (Z.ones 5) with 31 in H0. rewrite H0; [| lia]. unfold kNumClasses. apply Z.mod_pos_bound. lia. }
        repeat split; try lia. intros Z0. rewrite Z0 in P8. rewrite ND, P1 in P8. unfold round_up in P8. Z.div_mod_to_equations. nia.
      + destruct REST as (P1 & P2 & i & h & Hi & Hb & Hsz & Hms). exists h. split; [eapply nth_error_In; eauto|]. split; [exact Hb|].
        unfold ch_end. rewrite E. rewrite Hms, Hsz, Hb. unfold kPageSize. lia.
  Qed.

  Lemma batch_carvedQ : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> carved st kBatchClass (qb_addr b) /\ qb_count b = zlen (qb_chunks b) /\ 1 <= qb_count b <= kBatchCount.
  Proof.
    intros b Hb. pose proof (WFQ_batch st XC XB b W Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & _).
    split; [| split; [exact B1| exact B2]]. unfold carved. change (class_size kBatchClass) with 8192 in *.
    unfold kBatchClass, kNumClasses in *. repeat split; try lia.
  Qed.

  Lemma afoot_aobjQ : forall a, afoot s a -> aobj s a \/ (ASHADOW_BASE <= a < AHI_LO).
  Proof.
    intros a AF.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    destruct AF as [H|H|H|H|c Hc H|c Hc H|c cp Hc Hin H|H|h Hh H|ch Hch H|ch Hch H|ch Hch Hq H|b Hb H
                   |c Hc H|c Hc H|c cp Hc Hin H|ch Hch H|ch Hch H|ch Hch Hq H|ch Hch Hp H|b Hb H].
    all: unfold aobj, astatic; unfold a_ri, a_cache, RB, FA, a_sb in *.
    all: unfold AINST, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AIAINST,
      AHOOKS, ADYING, AREALMEMSET, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, OI_MISMATCH, OT_UNWINDING, kPageSize, kSpaceSize, kPtrArrayReserve,
      kBatchSize, kNumClasses, AIMG_LO, AIMG_TOP, AFS_SIZE, AHI_LO in *.
    all: acb.
    - left. right; right; right; right; right. lia.
    - left. right; right; right; right; right. lia.
    - left. lia.
    - left. left. lia.
    -   left. left. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_fa_bound _ _ RO). pose proof (ro_fa_le _ _ RO).
      pose proof (ro_numfreed _ _ RO). pose proof (region_in_space st c Hc). rewrite free_array_base_eq in H.
      unfold kFreeArrayOffset, kFreeArraySize, kSpaceSize, zlen in *. unfold st in *. lia.
    -   left. left. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO). pose proof (ro_alloc_nonneg _ _ RO).
      pose proof (region_in_space st c Hc). unfold kFreeArrayOffset, kUserMapSize, kSpaceSize in *. unfold st in *. lia.
    -   left. left.
      assert (C : carved st c (compact_to_addr st c cp)) by (destruct Hin; [eapply (carved_freeQ st XC XB)| eapply (carved_cacheQ st XC XB)]; eassumption).
      pose proof (carved_in_spaceQ c _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
    -   left. right; left. pose proof W as WW. destruct WW as (_ & _ & _ & _ & _ & _ & Wn & Wr & _). unfold kChunksBlockCount in *.
      assert (0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia). unfold st in *. lia.
    -   left. do 4 right. left. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _). lia.
    -   left. pose proof (chunk_geomQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      destruct (ch_primary ch).
      + left. destruct G7 as [C E]. pose proof (carved_in_spaceQ _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
      + do 4 right. left. destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _).
        lia.
    -   left. pose proof (chunk_geomQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      destruct (ch_primary ch).
      + left. destruct G7 as [C E]. pose proof (carved_in_spaceQ _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
      + do 4 right. left. destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _). lia.
    -   left. pose proof (chunk_geomQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      destruct (ch_primary ch).
      + left. destruct G7 as [C E]. pose proof (carved_in_spaceQ _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
      + do 4 right. left. destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _). lia.
    -   left. left. pose proof (batch_carvedQ b Hb) as (C & _). pose proof (carved_in_spaceQ _ _ C).
      change (class_size kBatchClass) with 8192 in *. unfold a_sb, kSpaceSize in *. unfold st in *. lia.
    -   right. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_fa_bound _ _ RO). pose proof (ro_fa_le _ _ RO).
      pose proof (ro_numfreed _ _ RO). pose proof (region_in_space st c Hc).
      rewrite free_array_base_eq in H. unfold kFreeArrayOffset, kFreeArraySize, kSpaceSize, zlen in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    -   right. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO). pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO).
      pose proof (region_in_space st c Hc). unfold kFreeArrayOffset, kUserMapSize, kSpaceSize in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    -   right. assert (C : carved st c (compact_to_addr st c cp)) by (destruct Hin; [eapply (carved_freeQ st XC XB)| eapply (carved_cacheQ st XC XB)]; eassumption).
      pose proof (carved_in_spaceQ c _ C) as (A1 & A2 & A3). pose proof (class_size_table_facts c Hc) as T. unfold a_sb, kSpaceSize in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    -   right. pose proof (chunk_geomQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (R : 0 <= ch_alloc_beg ch /\ ch_end ch <= aceil).
      { destruct (ch_primary ch).
        - destruct G7 as [C E]. pose proof (carved_in_spaceQ _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
        - destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0. lia. } eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    -   right. pose proof (chunk_geomQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (R : 0 <= ch_alloc_beg ch /\ ch_end ch <= aceil).
      { destruct (ch_primary ch).
        - destruct G7 as [C E]. pose proof (carved_in_spaceQ _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
        - destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0. lia. } eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    -   right. pose proof (chunk_geomQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (R : 0 <= ch_alloc_beg ch /\ ch_end ch <= aceil).
      { destruct (ch_primary ch).
        - destruct G7 as [C E]. pose proof (carved_in_spaceQ _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
        - destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0. lia. } eapply sh_range_in; [| | | exact H]; unfold nsh in *; Z.div_mod_to_equations; lia.
    -   right. pose proof (chunk_geomQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). rewrite Hp in G7.
      destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0.
      eapply sh_range_in; [| | | exact H]; unfold AHI_LO in *; lia.
    -   right. pose proof (batch_carvedQ b Hb) as (C & _). pose proof (carved_in_spaceQ _ _ C). change (class_size kBatchClass) with 8192 in *.
      unfold a_sb, kSpaceSize in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; unfold AHI_LO in *; Z.div_mod_to_equations; lia.
  Qed.

  Lemma aobj_rangeQ : forall a, aobj s a -> aband a \/ (AIMG_LO <= a < AIMG_TOP /\ astatic a).
  Proof.
    intros a H. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    unfold aobj in H. unfold aband. unfold kSpaceSize, kPageSize, kPtrArrayReserve in *.
    destruct H as [H|[H|[H|[H|[(h0 & Hsc & H)|H]]]]].
    - left; unfold a_sb in *; unfold st in *. clear - H S2 S3. aunf. lia.
    - left; clear - H P2. aunf. lia.
    - left; clear - H T2. aunf. lia.
    - left; clear - H X2. aunf. lia.
    - pose proof (SEC h0 Hsc) as (_ & G0 & G & _). left. clear - H G0. aunf. lia.
    - right. exact H.
  Qed.

  Theorem stack_not_afootQ : forall a, aceil <= a -> ~ afoot s a.
  Proof.
    intros a Ha AF. acb. destruct (afoot_aobjQ a AF) as [H|H].
    - apply aobj_rangeQ in H. unfold aband, AIMG_LO, AIMG_TOP, ALOWSH_LO in H. lia.
    - unfold AHI_LO in H. lia.
  Qed.

  Let ND : List.NoDup ((seg_free s) ++ (seg_inuse s) ++ (seg_batch s)).
  Proof. rewrite <- (carved_addr_list_eq s). exact (NoDup_app_l _ _ (WFQ_carved _ _ _ W)). Qed.

  Lemma in_seg_freeQ : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) -> In (compact_to_addr st c cp) (seg_free s).
  Proof.
    intros c cp Hc Hin. unfold seg_free. apply in_flat_map. exists c. split.
    - apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. unfold kNumClasses in Hc. lia.
    - apply in_app_iff. destruct Hin as [Hin|Hin]; [left|right]; apply in_map_iff; eauto.
  Qed.
  Lemma in_seg_inuseQ : forall ch, In ch (chunk_list st) -> ch_primary ch = true -> In (ch_alloc_beg ch) (seg_inuse s).
  Proof. intros ch Hin Hp. unfold seg_inuse. apply in_map_iff. exists ch. split; [reflexivity|]. apply filter_In. auto. Qed.
  Lemma in_seg_batchQ : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In (qb_addr b) (seg_batch s).
  Proof. intros b Hb. unfold seg_batch. apply in_map_iff. eauto. Qed.

  Lemma batch_not_freeQ : forall b c cp, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) -> qb_addr b <> compact_to_addr st c cp.
  Proof.
    intros b c cp Hb Hc Hin E. eapply (NoDup_app_disjoint (seg_free s) ((seg_inuse s) ++ (seg_batch s)) (qb_addr b) ND).
    - rewrite E. apply in_seg_freeQ; assumption.
    - apply in_app_iff. right. apply in_seg_batchQ; assumption.
  Qed.
  Lemma inuse_not_batchQ : forall ch b, In ch (chunk_list st) -> ch_primary ch = true ->
    In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> ch_alloc_beg ch <> qb_addr b.
  Proof.
    intros ch b Hch Hp Hb E. eapply (NoDup_app_disjoint (seg_inuse s) (seg_batch s) (qb_addr b)); [eapply NoDup_app_r; exact ND| |].
    - rewrite <- E. apply in_seg_inuseQ; assumption.
    - apply in_seg_batchQ; assumption.
  Qed.
  Lemma inuse_injQ : forall ch ch', In ch (chunk_list st) -> In ch' (chunk_list st) -> ch_primary ch = true -> ch_primary ch' = true ->
    ch_alloc_beg ch = ch_alloc_beg ch' -> ch = ch'.
  Proof.
    intros ch ch' H1 H2 P1 P2 E. eapply (NoDup_map_inj ch_alloc_beg (List.filter ch_primary (chunk_list st))).
    - eapply NoDup_app_l. eapply NoDup_app_r. exact ND.
    - apply filter_In; auto. - apply filter_In; auto. - exact E.
  Qed.

  Lemma records_sepQ : forall ch ch', In ch (chunk_list st) -> In ch' (chunk_list st) ->
    ch = ch' \/ ch_end ch <= ch_lo ch' \/ ch_end ch' <= ch_lo ch.
  Proof.
    intros ch ch' H1 H2.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geomQ ch H1) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (chunk_geomQ ch' H2) as (G1' & G2' & G3' & G4' & G5' & G6' & G7').
    unfold ch_lo. destruct (ch_primary ch) eqn:E1; destruct (ch_primary ch') eqn:E2.
    - destruct G7 as [C EE]. destruct G7' as [C' EE'].
      destruct (carved_sepQ st XC XB _ _ _ _ W C C') as [[EC EA]|D]; [left; apply inuse_injQ; auto| right; clear - D EE EE'; try acb; lia].
    - right. destruct G7 as [C EE]. destruct G7' as (h & Hh & Hb & He).
      pose proof (carved_in_spaceQ _ _ C) as CS. pose proof (SEC h Hh) as (_ & _ & _ & _ & D & _).
      unfold st in CS. clear - CS D EE Hb He; try acb. unfold disj, a_sb, kSpaceSize, kPageSize in *. lia.
    - right. destruct G7' as [C EE]. destruct G7 as (h & Hh & Hb & He).
      pose proof (carved_in_spaceQ _ _ C) as CS. pose proof (SEC h Hh) as (_ & _ & _ & _ & D & _).
      unfold st in CS. clear - CS D EE Hb He; try acb. unfold disj, a_sb, kSpaceSize, kPageSize in *. lia.
    - destruct G7 as (h & Hh & Hb & He). destruct G7' as (h' & Hh' & Hb' & He').
      destruct (Z.eq_dec (sc_map_beg h) (sc_map_beg h')) as [EQ|NE].
      + left. destruct W as (_ & _ & CO & INJ & _). apply INJ; auto.
        pose proof (CO ch H1) as (_ & _ & R3 & _ & REST). rewrite E1 in REST. destruct REST as (NP & _).
        pose proof (CO ch' H2) as (_ & _ & R3' & _ & REST'). rewrite E2 in REST'. destruct REST' as (NP' & _).
        rewrite G2, G2', R3, R3', (secondary_rz _ NP), (secondary_rz _ NP'). clear - Hb Hb' EQ; try acb. unfold kPageSize in *. lia.
      + right. pose proof (SEC2 h h' Hh Hh' NE) as D. pose proof (SEC h Hh) as (_ & _ & _ & SZ & _). pose proof (SEC h' Hh') as (_ & _ & _ & SZ' & _).
        clear - D Hb He Hb' He' SZ SZ'; try acb. unfold disj, kPageSize in *. lia.
  Qed.
End FactsQ.

End HCW.

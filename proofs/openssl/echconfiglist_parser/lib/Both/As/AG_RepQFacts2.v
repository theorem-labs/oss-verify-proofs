(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AsDepotInv AG_Malloc2 AG_RepQ AG_RepQFacts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FactsQ2.
  Context {HCEIL : HeapCeil}.
  Variable s : ast.
  Variables XC XB : list Z.
  Hypothesis OKQ : placed_ok s /\ WFQ (a_st s) XC XB.
  Let st := a_st s.
  Let W : WFQ st XC XB. Proof. exact (proj2 OKQ). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKQ). Qed.

  Lemma ext_factsQ : forall ch, In ch (chunk_list st) ->
    AIMG_TOP <= ch_lo ch /\ ch_end ch <= aceil /\ ch_lo ch <= ch_alloc_beg ch
    /\ (ch_primary ch = true -> carved st (ch_class ch) (ch_alloc_beg ch) /\ ch_end ch = ch_alloc_beg ch + class_size (ch_class ch)
                                /\ a_sb s <= ch_alloc_beg ch /\ ch_end ch <= a_sb s + kSpaceSize)
    /\ (ch_primary ch = false -> exists h, In h (as_sec st) /\ ch_lo ch = sc_map_beg h /\ ch_end ch = sc_map_beg h + sc_map_size h
                                 /\ ch_alloc_beg ch = sc_map_beg h + kPageSize).
  Proof.
    intros ch Hch. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geomQ s XC XB OKQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    unfold ch_lo. destruct (ch_primary ch) eqn:E.
    - destruct G7 as [C EE]. pose proof (carved_in_spaceQ s XC XB OKQ _ _ C) as (CS1 & CS2 & CS3). unfold st in *. unfold a_sb in *.
      split; [unfold AHI_LO, AIMG_TOP in *; lia|]. split; [(first [clear - S3 P1 EE CS2; lia | lia])|]. split; [lia|]. split; [| intros; congruence].
      intros _. split; [exact C|]. split; [exact EE|]. lia.
    - destruct G7 as (h & Hh & Hb & He). pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & _). unfold kPageSize in *.
      pose proof (aapp_above_image _ _ Q2) as Q2'.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; congruence|].
      intros _. exists h. repeat split; auto; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ext_bandQ : forall ch, In ch (chunk_list st) -> aapp (ch_lo ch) (ch_end ch - ch_lo ch).
  Proof.
    intros ch Hch. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geomQ s XC XB OKQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    unfold ch_lo. destruct (ch_primary ch) eqn:E.
    - destruct G7 as [C EE]. pose proof (carved_in_spaceQ s XC XB OKQ _ _ C) as (CS1 & CS2 & CS3). unfold st in *. unfold a_sb in *.
      right. unfold kSpaceSize, kPageSize in *. split; lia.
    - destruct G7 as (h & Hh & Hb & He). pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & _). unfold kPageSize in *.
      rewrite <- Hb, He. replace (sc_map_beg h + sc_map_size h - sc_map_beg h) with (sc_map_size h) by lia. exact Q2.
  Qed.


  Lemma chunk_alignQ : forall ch, In ch (chunk_list st) ->
    ch_alloc_beg ch mod 16 = 0 /\ ch_rz ch mod 16 = 0 /\ ch_user_beg ch mod 16 = 0 /\ ch_end ch mod 8 = 0 /\ ch_lo ch mod 8 = 0.
  Proof.
    intros ch Hch. pose proof PL as (S1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof (chunk_geomQ s XC XB OKQ ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof (WFQ_chunk st XC XB ch W Hch) as (_ & _ & R3 & _).
    pose proof (rz_size_facts (ch_used ch)) as (_ & RZ & _). change (rz_size (ch_used ch)) with (rq_rz (compute_req (ch_used ch))) in RZ.
    rewrite <- R3 in RZ.
    assert (AB : ch_alloc_beg ch mod 16 = 0 /\ ch_end ch mod 8 = 0 /\ ch_lo ch mod 8 = 0).
    { unfold ch_lo. destruct (ch_primary ch) eqn:E.
      - destruct G7 as [C EE]. destruct C as (Hc & Hsz & H0 & Hm & Hle). pose proof (class_size_table_facts (ch_class ch) Hc) as (_ & CS & _).
        rewrite region_beg_eq in *. unfold a_sb in S1. unfold st in *. rewrite EE.
        set (sz := class_size (ch_class ch)) in *. set (ab := ch_alloc_beg ch) in *. set (sb := as_space_beg (a_st s)) in *.
        clear - S1 Hsz Hm CS; try acb. Z.div_mod_to_equations. (first [clear - S1 Hsz Hm CS H H0 H4 H5 H9 H10 H14 H19 H20 H21 H22 H23 H24; nia | nia]).
      - destruct G7 as (h & Hh & Hb & He). pose proof (SEC h Hh) as (Q1 & _). unfold kPageSize in *.
        unfold ch_end. rewrite E. unfold round_up, kPageSize. set (ab := ch_alloc_beg ch) in *.
        set (k := (rq_needed (compute_req (ch_used ch)) + 4096 - 1) / 4096). clearbody k. rewrite Hb in Q1. clear - Q1; try acb.
        assert (Hab : exists q, ab = 4096 * q + 4096). { exists ((ab - 4096) / 4096). Z.div_mod_to_equations. lia. }
        destruct Hab as [q ->]. clear Q1.
        split; [| split]; Z.div_mod_to_equations; lia. }
    destruct AB as (AB1 & AB2 & AB3). rewrite G2. repeat split; auto. clear - AB1 RZ; try acb. Z.div_mod_to_equations. nia.
  Qed.


  Ltac mod8s := first [ reflexivity | assumption | lia
                      | apply mod8_add; mod8s | apply mod8_sub; mod8s | apply mod8_mul_r; mod8s | apply mod8_mul_l; mod8s
                      | eapply (mod8_of 16); [reflexivity| lia| assumption]
                      | eapply (mod8_of 32); [reflexivity| lia| assumption]
                      | eapply (mod8_of 65536); [reflexivity| lia| assumption]
                      | eapply (mod8_of 4096); [reflexivity| lia| assumption]
                      | eapply (mod8_of 8192); [reflexivity| lia| assumption]
                      | eapply (mod8_of 262144); [reflexivity| lia| assumption] ].

  Lemma farray_in_spaceQ : forall c, 0 <= c < kNumClasses ->
    a_sb s <= FA s c /\ FA s c + rg_mapped_free_array (get_region st c) <= a_sb s + kSpaceSize /\ FA s c mod 8 = 0
    /\ 0 <= rg_mapped_free_array (get_region st c) /\ rg_mapped_free_array (get_region st c) mod 8 = 0.
  Proof.
    intros c Hc. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_fa_bound _ _ RO). pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_mod _ _ RO) as FM.
    pose proof (ro_numfreed _ _ RO). pose proof (region_in_space st c Hc). pose proof PL as (S1 & _).
    unfold FA. rewrite free_array_base_eq, region_beg_eq in *. unfold a_sb, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kSpaceSize, zlen in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *. set (f := rg_mapped_free_array _) in *. clearbody f.
    repeat split; mod8s.
  Qed.

  Lemma tail_in_spaceQ : forall c, 0 <= c < kNumClasses ->
    a_sb s <= RB s c + rg_allocated_user (get_region st c) /\ RB s c + rg_mapped_user (get_region st c) <= a_sb s + kSpaceSize
    /\ (RB s c + rg_allocated_user (get_region st c)) mod 8 = 0 /\ rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c)
    /\ (rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c)) mod 8 = 0.
  Proof.
    intros c Hc. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO). pose proof (ro_alloc_nonneg _ _ RO).
    pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_mod _ _ RO) as MM. pose proof (ro_alloc_mod _ _ RO) as AM. pose proof (ro_empty _ _ RO) as EM.
    pose proof (class_size_table_facts c Hc) as (_ & CS & _). pose proof (region_in_space st c Hc). pose proof PL as (S1 & _).
    unfold RB. rewrite region_beg_eq in *. unfold a_sb, kFreeArrayOffset, kUserMapSize, kSpaceSize in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *. set (al := rg_allocated_user _) in *. set (mu := rg_mapped_user _) in *.
    set (sz := class_size c) in *. clearbody al mu sz.
    assert (AM8 : al mod 8 = 0).
    { destruct (Z.eq_dec sz 0) as [E0|NZ].
      - specialize (EM E0). replace al with 0 by lia. reflexivity.
      - specialize (AM NZ). eapply (mod8_of sz); [| exact NZ| exact AM]. eapply (mod8_of 32); [reflexivity| lia| exact CS]. }
    assert (MM8 : mu mod 8 = 0) by (eapply (mod8_of 262144); [reflexivity| lia| exact MM]).
    repeat split; mod8s.
  Qed.

  Lemma freech_in_spaceQ : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    a_sb s <= compact_to_addr st c cp /\ compact_to_addr st c cp + class_size c <= a_sb s + kSpaceSize
    /\ compact_to_addr st c cp mod 8 = 0 /\ 0 < class_size c /\ class_size c mod 8 = 0.
  Proof.
    intros c cp Hc Hin.
    assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply (carved_freeQ st XC XB)| apply (carved_cacheQ st XC XB)]; assumption).
    pose proof (carved_in_spaceQ s XC XB OKQ _ _ C') as (CS1 & CS2 & CS3). pose proof (class_size_table_facts c Hc) as (_ & CS & _). pose proof PL as (S1 & _).
    rewrite compact_to_addr_eq, region_beg_eq in *. unfold a_sb in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *. set (sz := class_size c) in *. clearbody sz.
    assert (SZ8 : sz mod 8 = 0) by (eapply (mod8_of 32); [reflexivity| lia| exact CS]).
    repeat split; mod8s.
  Qed.

  Lemma batch_in_spaceQ : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
    a_sb s <= qb_addr b /\ qb_addr b + kBatchSize <= a_sb s + kSpaceSize /\ qb_addr b mod 8 = 0.
  Proof.
    intros b Hb. pose proof (batch_carvedQ s XC XB OKQ b Hb) as (C' & _). pose proof (carved_in_spaceQ s XC XB OKQ _ _ C') as (CS1 & CS2 & CS3).
    change (class_size kBatchClass) with 8192 in *. pose proof PL as (S1 & _).
    destruct C' as (_ & _ & C0 & C1 & _). rewrite region_beg_eq in C0, C1. change (class_size kBatchClass) with 8192 in C1.
    unfold a_sb, kBatchSize, kBatchClass in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *.
    split; [lia|]. split; [lia|].
    assert (E : qb_addr b = (qb_addr b - (sb + 24 * 2^32)) + sb + 24 * 2^32) by lia.
    rewrite E. mod8s.
  Qed.

  Section RecQ.
  Variable ch0 : chunk.
  Hypothesis H0 : In ch0 (chunk_list st).
  Let lo0 := ch_lo ch0.
  Let hi0 := ch_end ch0.

  (* [comment removed for export] *)
  Lemma record_extQ : AIMG_TOP <= lo0 /\ hi0 <= aceil /\ lo0 <= ch_alloc_beg ch0 /\ lo0 mod 8 = 0 /\ hi0 mod 8 = 0
    /\ ch_alloc_beg ch0 + ch_rz ch0 = ch_user_beg ch0 /\ ch_user_beg ch0 + round_up (ch_used ch0) 8 <= hi0 /\ 16 <= ch_rz ch0 /\ 1 <= ch_used ch0.
  Proof.
    pose proof (ext_factsQ ch0 H0) as (X1 & X2 & X3 & _). pose proof (chunk_alignQ ch0 H0) as (A1 & A2 & A3 & A4 & A5).
    pose proof (chunk_geomQ s XC XB OKQ ch0 H0) as (G1 & G2 & G3 & G4 & _). subst lo0 hi0. repeat split; try assumption; lia.
  Qed.
  Lemma record_bandQ : aapp lo0 (hi0 - lo0).
  Proof. exact (ext_bandQ ch0 H0). Qed.

  (* [comment removed for export] *)
  Lemma record_primary_spaceQ : ch_primary ch0 = true -> a_sb s <= lo0 /\ hi0 <= a_sb s + kSpaceSize.
  Proof. intros P. pose proof (ext_factsQ ch0 H0) as (_ & _ & _ & XP & _). destruct (XP P) as (_ & _ & B1 & B2). subst lo0 hi0. unfold ch_lo. rewrite P. lia. Qed.
  Lemma record_secondary_mapQ : ch_primary ch0 = false ->
    exists h, In h (as_sec st) /\ lo0 = sc_map_beg h /\ hi0 = sc_map_beg h + sc_map_size h /\ ch_alloc_beg ch0 = sc_map_beg h + kPageSize.
  Proof. intros P. pose proof (ext_factsQ ch0 H0) as (_ & _ & _ & _ & XS). exact (XS P). Qed.

  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  (* [comment removed for export] *)
  Lemma record_vs_spaceQ : ch_primary ch0 = false -> a_sb s + kSpaceSize + kPageSize <= lo0 \/ hi0 <= a_sb s.
  Proof.
    intros P. placed. destruct (record_secondary_mapQ P) as (h & Hh & L & E & _). pose proof (SEC h Hh) as (_ & _ & _ & _ & D & _).
    subst lo0 hi0. rewrite L, E. clear - D; try acb. unfold disj in D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma farray_vs_recordQ : forall c, 0 <= c < kNumClasses ->
    FA s c + rg_mapped_free_array (get_region st c) <= lo0 \/ hi0 <= FA s c.
  Proof.
    intros c Hc. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_fa_bound _ _ RO) as FB.
    pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold FA. rewrite free_array_base_eq.
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_factsQ ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      pose proof (carved_rangeQ st XC XB _ _ W C) as (CR1 & CR2 & CR3). subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (Z.eq_dec c (ch_class ch0)) as [->|NE].
      + right. unfold st in *. clear - EE CR2; try acb. lia.
      + destruct C as (Hc0 & _). destruct (regions_disjoint st c (ch_class ch0) ltac:(hci; lia) ltac:(hci; lia) NE) as [D|D];
          unfold st in *; clear - EE CR1 CR2 D FB; try acb; unfold kFreeArrayOffset, kFreeArraySize in *; lia.
    - destruct (record_vs_spaceQ E) as [D|D]; unfold a_sb, st in *; clear - D RS1 RS2 FB; try acb; unfold kFreeArrayOffset, kFreeArraySize, kSpaceSize, kPageSize in *; lia.
  Qed.

  Lemma tail_vs_recordQ : forall c, 0 <= c < kNumClasses ->
    RB s c + rg_mapped_user (get_region st c) <= lo0 \/ hi0 <= RB s c + rg_allocated_user (get_region st c).
  Proof.
    intros c Hc. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO) as MB. pose proof (ro_alloc_nonneg _ _ RO) as AN.
    pose proof (ro_alloc_le _ _ RO) as AL.
    pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold RB.
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_factsQ ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      pose proof (carved_rangeQ st XC XB _ _ W C) as (CR1 & CR2 & CR3). subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (Z.eq_dec c (ch_class ch0)) as [->|NE].
      + right. destruct C as (_ & _ & _ & _ & CL). unfold st in *. clear - EE CL; try acb. lia.
      + destruct C as (Hc0 & _). destruct (regions_disjoint st c (ch_class ch0) ltac:(hci; lia) ltac:(hci; lia) NE) as [D|D];
          unfold st in *; clear - EE CR1 CR2 D MB AN AL; try acb; unfold kFreeArrayOffset, kUserMapSize in *; lia.
    - destruct (record_vs_spaceQ E) as [D|D]; unfold a_sb, st in *; clear - D RS1 RS2 MB AN AL; try acb; unfold kFreeArrayOffset, kUserMapSize, kSpaceSize, kPageSize in *; lia.
  Qed.

  Lemma rinfo_vs_recordQ : a_ri s + kPageSize <= lo0 \/ hi0 <= a_ri s.
  Proof.
    unfold a_ri. destruct (ch_primary ch0) eqn:E.
    - right. exact (proj2 (record_primary_spaceQ E)).
    - destruct (record_vs_spaceQ E) as [D|D]; unfold kSpaceSize, kPageSize in *; lia.
  Qed.

  Lemma freech_vs_recordQ : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    compact_to_addr st c cp + class_size c <= lo0 \/ hi0 <= compact_to_addr st c cp.
  Proof.
    intros c cp Hc Hin.
    assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply (carved_freeQ st XC XB)| apply (carved_cacheQ st XC XB)]; assumption).
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_factsQ ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (carved_sepQ st XC XB _ _ _ _ W C C') as [[EC EA]|D].
      + exfalso. eapply (inuse_not_freeQ s XC XB OKQ ch0 c cp); eauto.
      + clear - EE D; try acb. lia.
    - pose proof (carved_in_spaceQ s XC XB OKQ _ _ C') as (CS1 & CS2 & _).
      destruct (record_vs_spaceQ E) as [D|D]; unfold st in *; clear - D CS1 CS2; try acb; unfold kPageSize in *; lia.
  Qed.

  Lemma batch_vs_recordQ : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
    qb_addr b + kBatchSize <= lo0 \/ hi0 <= qb_addr b.
  Proof.
    intros b Hb. pose proof (batch_carvedQ s XC XB OKQ b Hb) as (C' & _).
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_factsQ ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (carved_sepQ st XC XB _ _ _ _ W C C') as [[EC EA]|D].
      + exfalso. eapply (inuse_not_batchQ s XC XB OKQ ch0 b); eauto.
      + change (class_size kBatchClass) with kBatchSize in D. clear - EE D; try acb. lia.
    - pose proof (carved_in_spaceQ s XC XB OKQ _ _ C') as (CS1 & CS2 & _). change (class_size kBatchClass) with kBatchSize in CS2.
      destruct (record_vs_spaceQ E) as [D|D]; unfold st in *; clear - D CS1 CS2; try acb; unfold kPageSize in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sechdr_vs_primary_recordQ : forall h, In h (as_sec st) -> ch_primary ch0 = true ->
    sc_map_beg h + kPageSize <= lo0 \/ hi0 <= sc_map_beg h.
  Proof.
    intros h Hh P. placed. pose proof (SEC h Hh) as (_ & _ & _ & Q4 & Q & _). destruct (record_primary_spaceQ P) as [B1 B2].
    clear - Q4 Q B1 B2; try acb. unfold disj, kPageSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma record_vs_recordQ : forall ch, In ch (chunk_list st) -> ch <> ch0 -> ch_end ch <= lo0 \/ hi0 <= ch_lo ch.
  Proof. intros ch Hch NE. destruct (records_sepQ s XC XB OKQ ch ch0 Hch H0) as [E|[D|D]]; [congruence| left; exact D| right; exact D]. Qed.


  End RecQ.

  Section CarvedSlotQ.
  Variables (c0 : Z) (A0 : Z).
  Hypothesis CV : carved st c0 A0.
  Let sz0 := class_size c0.

  Lemma carved_vs_farrayQ : forall c, 0 <= c < kNumClasses ->
    FA s c + rg_mapped_free_array (get_region st c) <= A0 \/ A0 + sz0 <= FA s c.
  Proof.
    intros c Hc. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_fa_bound _ _ RO) as FB. pose proof (ro_alloc_le _ _ RO) as AL. pose proof (ro_mapped_bound _ _ RO) as MB.
    pose proof (carved_rangeQ st XC XB _ _ W CV) as (CR1 & CR2 & CR3). destruct CV as (Hc0 & _ & _ & _ & CL). subst sz0. unfold FA. rewrite free_array_base_eq.
    destruct (Z.eq_dec c c0) as [->|NE].
    - right. unfold st in *. unfold kFreeArrayOffset, kUserMapSize in *. lia.
    - destruct (regions_disjoint st c c0 ltac:(lia) ltac:(unfold kNumClasses in Hc0; lia) NE) as [D|D];
        unfold st in *; unfold kFreeArrayOffset, kFreeArraySize, kUserMapSize in *; lia.
  Qed.

  Lemma carved_vs_tailQ : forall c, 0 <= c < kNumClasses ->
    RB s c + rg_mapped_user (get_region st c) <= A0 \/ A0 + sz0 <= RB s c + rg_allocated_user (get_region st c).
  Proof.
    intros c Hc. pose proof (WFQ_region st XC XB c W Hc) as RO. pose proof (ro_alloc_nonneg _ _ RO) as AN. pose proof (ro_alloc_le _ _ RO) as AL. pose proof (ro_mapped_bound _ _ RO) as MB.
    pose proof (carved_rangeQ st XC XB _ _ W CV) as (CR1 & CR2 & CR3). destruct CV as (Hc0 & _ & _ & _ & CL). subst sz0. unfold RB.
    destruct (Z.eq_dec c c0) as [->|NE].
    - right. unfold st in *. lia.
    - destruct (regions_disjoint st c c0 ltac:(lia) ltac:(unfold kNumClasses in Hc0; lia) NE) as [D|D];
        unfold st in *; unfold kFreeArrayOffset, kUserMapSize in *; lia.
  Qed.

  Lemma carved_vs_rinfoQ : A0 + sz0 <= a_ri s.
  Proof. pose proof (carved_in_spaceQ s XC XB OKQ _ _ CV) as (CS1 & CS2 & _). unfold a_ri. subst sz0. unfold st in *. lia. Qed.

  Lemma carved_vs_threadQ : a_thr s + kPageSize <= A0 \/ A0 + sz0 <= a_thr s.
  Proof.
    pose proof (carved_in_spaceQ s XC XB OKQ _ _ CV) as (CS1 & CS2 & _). pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_ctxQ : a_ctx s + 160 <= A0 \/ A0 + sz0 <= a_ctx s.
  Proof.
    pose proof (carved_in_spaceQ s XC XB OKQ _ _ CV) as (CS1 & CS2 & _). pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D3 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_paQ : a_pa s + kPtrArrayReserve <= A0 \/ A0 + sz0 <= a_pa s.
  Proof.
    pose proof (carved_in_spaceQ s XC XB OKQ _ _ CV) as (CS1 & CS2 & _). pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_secQ : forall sc, In sc (as_sec st) -> sc_map_beg sc + sc_map_size sc <= A0 \/ A0 + sz0 <= sc_map_beg sc.
  Proof.
    intros sc Hsc. pose proof (carved_in_spaceQ s XC XB OKQ _ _ CV) as (CS1 & CS2 & _).
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof (SEC sc Hsc) as (_ & _ & _ & _ & D & _). subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_depotQ : forall d, depot_placed s d ->
    (d_nb d + 16 * 65536 <= A0 \/ A0 + sz0 <= d_nb d) /\ (d_sb d + 8 * 131072 <= A0 \/ A0 + sz0 <= d_sb d).
  Proof.
    intros d DPL. pose proof (carved_in_spaceQ s XC XB OKQ _ _ CV) as (CS1 & CS2 & _). destruct DPL as (_ & _ & G3 & G4 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma carved_vs_freechQ : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    compact_to_addr st c cp <> A0 ->
    compact_to_addr st c cp + class_size c <= A0 \/ A0 + sz0 <= compact_to_addr st c cp.
  Proof.
    intros c cp Hc Hin NE.
    assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply (carved_freeQ st XC XB)| apply (carved_cacheQ st XC XB)]; assumption).
    destruct (carved_sepQ st XC XB _ _ _ _ W CV C') as [[_ E]|D]; [exfalso; exact (NE (eq_sym E))| subst sz0; lia].
  Qed.
  Lemma carved_vs_batchQ : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> qb_addr b <> A0 ->
    qb_addr b + kBatchSize <= A0 \/ A0 + sz0 <= qb_addr b.
  Proof.
    intros b Hb NE. pose proof (batch_carvedQ s XC XB OKQ b Hb) as (C' & _).
    destruct (carved_sepQ st XC XB _ _ _ _ W CV C') as [[_ E]|D]; [exfalso; exact (NE (eq_sym E))|].
    change (class_size kBatchClass) with kBatchSize in D. subst sz0. lia.
  Qed.
  End CarvedSlotQ.
End FactsQ2.

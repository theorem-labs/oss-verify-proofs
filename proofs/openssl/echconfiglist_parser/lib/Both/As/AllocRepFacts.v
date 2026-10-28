(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition aobj (s : ast) (a : Z) : Prop :=
     (a_sb s <= a < a_sb s + kSpaceSize + kPageSize)
  \/ (a_pa s <= a < a_pa s + kPtrArrayReserve)
  \/ (a_thr s <= a < a_thr s + kPageSize)
  \/ (a_ctx s + 8 <= a < a_ctx s + 160)
  \/ (exists sc, In sc (as_sec (a_st s)) /\ sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc)
  \/ (AIMG_LO <= a < AIMG_TOP /\ astatic a).

Lemma secondary_rz : forall n, rq_primary (compute_req n) = false -> rq_rz (compute_req n) = 2048.
Proof.
  intros n H. unfold compute_req in *. cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.eqb Z.ltb] in *.
  unfold rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog, round_up, kMaxSize in *.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end; cbn; try reflexivity; exfalso; revert H; cbn -[Z.add Z.mul Z.max Z.leb Z.div].
  all: repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end.
  all: intros E; apply Z.leb_gt in E.
  all: match type of E with context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in E end.
  all: Z.div_mod_to_equations; lia.
Qed.
End HCW.

Section Facts.
  Context {HCEIL : HeapCeil}.
  Variable s : ast.
  Hypothesis OK : ast_ok s.
  Let st := a_st s.
  Let W : WF st. Proof. exact (proj2 OK). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.

  (* [comment removed for export] *)
  Lemma carved_in_space : forall c a, carved st c a ->
    a_sb s <= a /\ a + class_size c <= a_sb s + kSpaceSize /\ 0 < class_size c.
  Proof.
    intros c a C. pose proof (carved_range st c a W C) as (R1 & R2 & R3). destruct C as (Hc & _).
    pose proof (region_in_space st c Hc) as [S1 S2]. unfold a_sb, kFreeArrayOffset in *. unfold st in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma chunk_geom : forall ch, In ch (chunk_list st) ->
    let u := ch_user_beg ch in let a := ch_alloc_beg ch in let n := ch_used ch in
    16 <= ch_rz ch /\ u = a + ch_rz ch /\ 1 <= n /\ a + ch_rz ch + round_up n 8 <= ch_end ch /\ n <= round_up n 8 < n + 8 /\ round_up n 8 = 8 * nsh n
    /\ (if ch_primary ch then carved st (ch_class ch) a /\ ch_end ch = a + class_size (ch_class ch)
        else exists h, In h (as_sec st) /\ sc_map_beg h = a - kPageSize /\ ch_end ch = sc_map_beg h + sc_map_size h).
  Proof.
    intros ch Hin. pose proof (WF_chunk st ch W Hin) as CO.
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
        repeat split; try (first [clear - HC P6 P5 P7; lia | lia]). intros Z0. rewrite Z0 in P8. rewrite ND, P1 in P8. unfold round_up in P8. Z.div_mod_to_equations. nia.
      + destruct REST as (P1 & P2 & i & h & Hi & Hb & Hsz & Hms). exists h. split; [eapply nth_error_In; eauto|]. split; [exact Hb|].
        unfold ch_end. rewrite E. rewrite Hms, Hsz, Hb. unfold kPageSize. lia.
  Qed.

  Lemma sh_lo : forall x, 0 <= x -> ASHADOW_BASE <= sh x.
  Proof. intros x Hx. unfold sh. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_hi : forall x k, 0 <= k -> x + 8 * k <= aceil -> sh x + k <= AHI_LO.
  Proof. intros x k Hk H. acb. unfold sh, ASHADOW_BASE, AHI_LO in *. Z.div_mod_to_equations. lia. Qed.

  Lemma sh_range_in : forall X k a, 0 <= X -> 0 <= k -> X + 8 * k <= aceil ->
    sh X <= a < sh X + k -> ASHADOW_BASE <= a < AHI_LO.
  Proof. intros X k a HX Hk HB [H1 H2]. pose proof (sh_lo X HX). acb. pose proof (sh_hi X k Hk HB). lia. Qed.

  Lemma batch_carved : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> carved st kBatchClass (qb_addr b) /\ qb_count b = zlen (qb_chunks b) /\ 1 <= qb_count b <= kBatchCount.
  Proof.
    intros b Hb. pose proof (WF_batch st b W Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & _).
    split; [| split; [exact B1| exact B2]]. unfold carved. change (class_size kBatchClass) with 8192 in *.
    unfold kBatchClass, kNumClasses in *. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma afoot_aobj : forall a, afoot s a -> aobj s a \/ (ASHADOW_BASE <= a < AHI_LO).
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
    - (* [comment removed for export] *) left. left. pose proof (WF_region st c W Hc) as RO. pose proof (ro_fa_bound _ _ RO). pose proof (ro_fa_le _ _ RO).
      pose proof (ro_numfreed _ _ RO). pose proof (region_in_space st c Hc). rewrite free_array_base_eq in H.
      unfold kFreeArrayOffset, kFreeArraySize, kSpaceSize, zlen in *. unfold st in *. lia.
    - (* [comment removed for export] *) left. left. pose proof (WF_region st c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO). pose proof (ro_alloc_nonneg _ _ RO).
      pose proof (region_in_space st c Hc). unfold kFreeArrayOffset, kUserMapSize, kSpaceSize in *. unfold st in *. lia.
    - (* [comment removed for export] *) left. left.
      assert (C : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
      pose proof (carved_in_space c _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
    - (* [comment removed for export] *) left. right; left. pose proof W as WW. destruct WW as (_ & _ & _ & _ & _ & _ & Wn & Wr & _). unfold kChunksBlockCount in *.
      assert (0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia). unfold st in *. lia.
    - (* [comment removed for export] *) left. do 4 right. left. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _). lia.
    - (* [comment removed for export] *) left. pose proof (chunk_geom ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      destruct (ch_primary ch).
      + left. destruct G7 as [C E]. pose proof (carved_in_space _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
      + do 4 right. left. destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _).
        lia.
    - (* [comment removed for export] *) left. pose proof (chunk_geom ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      destruct (ch_primary ch).
      + left. destruct G7 as [C E]. pose proof (carved_in_space _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
      + do 4 right. left. destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _). lia.
    - (* [comment removed for export] *) left. pose proof (chunk_geom ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      destruct (ch_primary ch).
      + left. destruct G7 as [C E]. pose proof (carved_in_space _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
      + do 4 right. left. destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. exists h. split; [exact Hh|]. pose proof (SEC h Hh) as (_ & _ & _ & G & _). lia.
    - (* [comment removed for export] *) left. left. pose proof (batch_carved b Hb) as (C & _). pose proof (carved_in_space _ _ C).
      change (class_size kBatchClass) with 8192 in *. unfold a_sb, kSpaceSize in *. unfold st in *. lia.
    - (* [comment removed for export] *) right. pose proof (WF_region st c W Hc) as RO. pose proof (ro_fa_bound _ _ RO). pose proof (ro_fa_le _ _ RO).
      pose proof (ro_numfreed _ _ RO). pose proof (region_in_space st c Hc).
      rewrite free_array_base_eq in H. unfold kFreeArrayOffset, kFreeArraySize, kSpaceSize, zlen in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *) right. pose proof (WF_region st c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO). pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO).
      pose proof (region_in_space st c Hc). unfold kFreeArrayOffset, kUserMapSize, kSpaceSize in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *) right. assert (C : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
      pose proof (carved_in_space c _ C) as (A1 & A2 & A3). pose proof (class_size_table_facts c Hc) as T. unfold a_sb, kSpaceSize in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *) right. pose proof (chunk_geom ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (R : 0 <= ch_alloc_beg ch /\ ch_end ch <= aceil).
      { destruct (ch_primary ch).
        - destruct G7 as [C E]. pose proof (carved_in_space _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
        - destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0. lia. } eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *) right. pose proof (chunk_geom ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (R : 0 <= ch_alloc_beg ch /\ ch_end ch <= aceil).
      { destruct (ch_primary ch).
        - destruct G7 as [C E]. pose proof (carved_in_space _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
        - destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0. lia. } eapply sh_range_in; [| | | exact H]; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *) right. pose proof (chunk_geom ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (R : 0 <= ch_alloc_beg ch /\ ch_end ch <= aceil).
      { destruct (ch_primary ch).
        - destruct G7 as [C E]. pose proof (carved_in_space _ _ C). unfold a_sb, kSpaceSize in *. unfold st in *. lia.
        - destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0. lia. } eapply sh_range_in; [| | | exact H]; unfold nsh in *; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *) right. pose proof (chunk_geom ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). rewrite Hp in G7.
      destruct G7 as (h & Hh & Hb & He). unfold kPageSize in Hb. pose proof (SEC h Hh) as (_ & G0 & G & G' & _). apply aapp_above_image in G0. unfold AIMG_TOP in G0.
      eapply sh_range_in; [| | | exact H]; unfold AHI_LO in *; lia.
    - (* [comment removed for export] *) right. pose proof (batch_carved b Hb) as (C & _). pose proof (carved_in_space _ _ C). change (class_size kBatchClass) with 8192 in *.
      unfold a_sb, kSpaceSize in *. unfold st in *.
      eapply sh_range_in; [| | | exact H]; unfold AHI_LO in *; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Definition aband (a : Z) : Prop := (4096 <= a < AIMG_LO) \/ (AIMG_TOP <= a < ALOWSH_LO) \/ (AHI_LO <= a < aceil).
  Lemma aobj_range : forall a, aobj s a -> aband a \/ (AIMG_LO <= a < AIMG_TOP /\ astatic a).
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

  Theorem stack_not_afoot : forall a, aceil <= a -> ~ afoot s a.
  Proof.
    intros a Ha AF. acb. destruct (afoot_aobj a AF) as [H|H].
    - apply aobj_range in H. unfold aband, AIMG_LO, AIMG_TOP, ALOWSH_LO in H. lia.
    - unfold AHI_LO in H. lia.
  Qed.

  Theorem image_not_afoot : forall a, ARW_LO <= a < AIMG_TOP -> ~ astatic a -> ~ afoot s a.
  Proof.
    intros a Ha Hn AF. destruct (afoot_aobj a AF) as [H|H].
    - apply aobj_range in H. destruct H as [H|[_ H]]; [unfold aband, AHI_LO, AIMG_LO, AIMG_TOP, ARW_LO in *; lia| exact (Hn H)].
    - unfold ASHADOW_BASE, AIMG_TOP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fakestack_not_afoot : forall a, a_fsb s <= a < a_fsb s + AFS_SIZE -> ~ afoot s a.
  Proof.
    intros a Ha AF. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    destruct (afoot_aobj a AF) as [H|H].
    - unfold aobj in H.
      destruct H as [H|[H|[H|[H|[(h0 & Hsc & H)|[H _]]]]]].
      + clear - Ha H D6; try acb. unfold disj, a_sb in *. lia.
      + clear - Ha H D7; try acb. unfold disj in *. lia.
      + clear - Ha H D8; try acb. unfold disj in *. lia.
      + clear - Ha H D9; try acb. unfold disj in *. lia.
      + pose proof (SEC h0 Hsc) as (_ & _ & _ & _ & _ & _ & _ & _ & G). clear - Ha H G; try acb. unfold disj in *. lia.
      + clear - Ha H F1. aunf. lia.
    - clear - Ha H F1. aunf. unfold ASHADOW_BASE in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma NoDup_app_disjoint : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
    inversion ND; subst. destruct H1 as [->|H1].
    - apply H3. apply in_app_iff. right. exact H2.
    - eapply IH; eauto.
  Qed.
  Lemma NoDup_app_l : forall (l1 l2 : list Z), List.NoDup (l1 ++ l2) -> List.NoDup l1.
  Proof. induction l1; intros l2 ND; [constructor|]. inversion ND; subst. constructor; [| eapply IHl1; eauto]. intros Hin. apply H1. apply in_app_iff. left. exact Hin. Qed.
  Lemma NoDup_app_r : forall (l1 l2 : list Z), List.NoDup (l1 ++ l2) -> List.NoDup l2.
  Proof. induction l1; intros l2 ND; [exact ND|]. inversion ND; subst. eapply IHl1; eauto. Qed.
  Lemma NoDup_map_inj : forall (f : chunk -> Z) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
  Proof.
    induction l as [|z l IH]; intros x y ND Hx Hy E; [destruct Hx|].
    cbn in ND. inversion ND; subst. destruct Hx as [->|Hx], Hy as [->|Hy]; [reflexivity| | | eapply IH; eauto].
    - exfalso. apply H1. rewrite E. apply in_map_iff. eauto.
    - exfalso. apply H1. rewrite <- E. apply in_map_iff. eauto.
  Qed.

  (* [comment removed for export] *)
  Definition seg_free : list Z :=
    List.flat_map (fun c => map (compact_to_addr st c) (rg_free_array (get_region st c)) ++ map (compact_to_addr st c) (pc_chunks (get_pc st c)))
             (map Z.of_nat (seq 0 32)).
  Definition seg_inuse : list Z := map ch_alloc_beg (List.filter ch_primary (chunk_list st)).
  Definition seg_batch : list Z := map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st)).
  Lemma carved_addr_list_eq : carved_addr_list st = seg_free ++ seg_inuse ++ seg_batch.
  Proof. reflexivity. Qed.
  Let ND : List.NoDup (seg_free ++ seg_inuse ++ seg_batch).
  Proof. rewrite <- carved_addr_list_eq. destruct W as (_ & H & _). exact H. Qed.

  Lemma in_seg_free : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) -> In (compact_to_addr st c cp) seg_free.
  Proof.
    intros c cp Hc Hin. unfold seg_free. apply in_flat_map. exists c. split.
    - apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. unfold kNumClasses in Hc. lia.
    - apply in_app_iff. destruct Hin as [Hin|Hin]; [left|right]; apply in_map_iff; eauto.
  Qed.
  Lemma in_seg_inuse : forall ch, In ch (chunk_list st) -> ch_primary ch = true -> In (ch_alloc_beg ch) seg_inuse.
  Proof. intros ch Hin Hp. unfold seg_inuse. apply in_map_iff. exists ch. split; [reflexivity|]. apply filter_In. auto. Qed.
  Lemma in_seg_batch : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In (qb_addr b) seg_batch.
  Proof. intros b Hb. unfold seg_batch. apply in_map_iff. eauto. Qed.

  Lemma inuse_not_free : forall ch c cp, In ch (chunk_list st) -> ch_primary ch = true -> 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) -> ch_alloc_beg ch <> compact_to_addr st c cp.
  Proof.
    intros ch c cp Hch Hp Hc Hin E. eapply (NoDup_app_disjoint seg_free (seg_inuse ++ seg_batch) (ch_alloc_beg ch) ND).
    - rewrite E. apply in_seg_free; assumption.
    - apply in_app_iff. left. apply in_seg_inuse; assumption.
  Qed.
  Lemma batch_not_free : forall b c cp, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) -> qb_addr b <> compact_to_addr st c cp.
  Proof.
    intros b c cp Hb Hc Hin E. eapply (NoDup_app_disjoint seg_free (seg_inuse ++ seg_batch) (qb_addr b) ND).
    - rewrite E. apply in_seg_free; assumption.
    - apply in_app_iff. right. apply in_seg_batch; assumption.
  Qed.
  Lemma inuse_not_batch : forall ch b, In ch (chunk_list st) -> ch_primary ch = true ->
    In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> ch_alloc_beg ch <> qb_addr b.
  Proof.
    intros ch b Hch Hp Hb E. eapply (NoDup_app_disjoint seg_inuse seg_batch (qb_addr b)); [eapply NoDup_app_r; exact ND| |].
    - rewrite <- E. apply in_seg_inuse; assumption.
    - apply in_seg_batch; assumption.
  Qed.
  Lemma inuse_inj : forall ch ch', In ch (chunk_list st) -> In ch' (chunk_list st) -> ch_primary ch = true -> ch_primary ch' = true ->
    ch_alloc_beg ch = ch_alloc_beg ch' -> ch = ch'.
  Proof.
    intros ch ch' H1 H2 P1 P2 E. eapply (NoDup_map_inj ch_alloc_beg (List.filter ch_primary (chunk_list st))).
    - eapply NoDup_app_l. eapply NoDup_app_r. exact ND.
    - apply filter_In; auto. - apply filter_In; auto. - exact E.
  Qed.

  (* [comment removed for export] *)
  Definition ch_lo (ch : chunk) : Z := if ch_primary ch then ch_alloc_beg ch else ch_alloc_beg ch - kPageSize.

  Lemma records_sep : forall ch ch', In ch (chunk_list st) -> In ch' (chunk_list st) ->
    ch = ch' \/ ch_end ch <= ch_lo ch' \/ ch_end ch' <= ch_lo ch.
  Proof.
    intros ch ch' H1 H2.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geom ch H1) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (chunk_geom ch' H2) as (G1' & G2' & G3' & G4' & G5' & G6' & G7').
    unfold ch_lo. destruct (ch_primary ch) eqn:E1; destruct (ch_primary ch') eqn:E2.
    - destruct G7 as [C EE]. destruct G7' as [C' EE'].
      destruct (carved_sep st _ _ _ _ W C C') as [[EC EA]|D]; [left; apply inuse_inj; auto| right; clear - D EE EE'; try acb; lia].
    - right. destruct G7 as [C EE]. destruct G7' as (h & Hh & Hb & He).
      pose proof (carved_in_space _ _ C) as CS. pose proof (SEC h Hh) as (_ & _ & _ & _ & D & _).
      unfold st in CS. clear - CS D EE Hb He; try acb. unfold disj, a_sb, kSpaceSize, kPageSize in *. lia.
    - right. destruct G7' as [C EE]. destruct G7 as (h & Hh & Hb & He).
      pose proof (carved_in_space _ _ C) as CS. pose proof (SEC h Hh) as (_ & _ & _ & _ & D & _).
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
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ClientView.
  Context {HCEIL : HeapCeil}.
  Variable s : ast.
  Hypothesis OK : ast_ok s.
  Let st := a_st s.
  Let W : WF st. Proof. exact (proj2 OK). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.

  (* [comment removed for export] *)
  Lemma ext_facts : forall ch, In ch (chunk_list st) ->
    AIMG_TOP <= ch_lo ch /\ ch_end ch <= aceil /\ ch_lo ch <= ch_alloc_beg ch
    /\ (ch_primary ch = true -> carved st (ch_class ch) (ch_alloc_beg ch) /\ ch_end ch = ch_alloc_beg ch + class_size (ch_class ch)
                                /\ a_sb s <= ch_alloc_beg ch /\ ch_end ch <= a_sb s + kSpaceSize)
    /\ (ch_primary ch = false -> exists h, In h (as_sec st) /\ ch_lo ch = sc_map_beg h /\ ch_end ch = sc_map_beg h + sc_map_size h
                                 /\ ch_alloc_beg ch = sc_map_beg h + kPageSize).
  Proof.
    intros ch Hch. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    unfold ch_lo. destruct (ch_primary ch) eqn:E.
    - destruct G7 as [C EE]. pose proof (carved_in_space s OK _ _ C) as (CS1 & CS2 & CS3). unfold st in *. unfold a_sb in *.
      split; [unfold AHI_LO, AIMG_TOP in *; (first [clear - CS1 S2; lia | lia])|]. split; [(first [clear - CS2 EE T1 S3; lia | lia])|]. split; [lia|]. split; [| intros; congruence].
      intros _. split; [exact C|]. split; [exact EE|]. (first [clear - CS2 CS1 EE; lia | lia]).
    - destruct G7 as (h & Hh & Hb & He). pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & _). unfold kPageSize in *.
      pose proof (aapp_above_image _ _ Q2) as Q2'.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; congruence|].
      intros _. exists h. repeat split; auto; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ext_band : forall ch, In ch (chunk_list st) -> aapp (ch_lo ch) (ch_end ch - ch_lo ch).
  Proof.
    intros ch Hch. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    unfold ch_lo. destruct (ch_primary ch) eqn:E.
    - destruct G7 as [C EE]. pose proof (carved_in_space s OK _ _ C) as (CS1 & CS2 & CS3). unfold st in *. unfold a_sb in *.
      right. unfold kSpaceSize, kPageSize in *. split; lia.
    - destruct G7 as (h & Hh & Hb & He). pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & _). unfold kPageSize in *.
      rewrite <- Hb, He. replace (sc_map_beg h + sc_map_size h - sc_map_beg h) with (sc_map_size h) by lia. exact Q2.
  Qed.

  (* [comment removed for export] *)
  Inductive apiece : Z -> Z -> Prop :=
  | ap_thread : apiece (a_thr s) (a_thr s + kPageSize)
  | ap_ctx    : apiece (a_ctx s + 8) (a_ctx s + 12)
  | ap_ctx2   : apiece (a_ctx s + 152) (a_ctx s + 160)
  | ap_rinfo  : apiece (a_ri s) (a_ri s + kPageSize)
  | ap_ptrarr : apiece (a_pa s) (a_pa s + kPtrArrayReserve)
  | ap_farray : forall c, 0 <= c < kNumClasses -> apiece (FA s c) (FA s c + rg_mapped_free_array (get_region st c))
  | ap_tail   : forall c, 0 <= c < kNumClasses ->
                apiece (RB s c + rg_allocated_user (get_region st c)) (RB s c + rg_mapped_user (get_region st c))
  | ap_freech : forall c cp, 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
                apiece (compact_to_addr st c cp) (compact_to_addr st c cp + class_size c)
  | ap_sechdr : forall h, In h (as_sec st) -> apiece (sc_map_beg h) (sc_map_beg h + kPageSize)
  | ap_chleft : forall ch, In ch (chunk_list st) -> apiece (ch_lo ch) (ch_user_beg ch)
  | ap_chright8 : forall ch, In ch (chunk_list st) -> apiece (ch_user_beg ch + round_up (ch_used ch) 8) (ch_end ch)
  | ap_chquar : forall ch, In ch (chunk_list st) -> ch_state ch = CQuarantine ->
                apiece (ch_user_beg ch) (ch_user_beg ch + round_up (ch_used ch) 8)
  | ap_batch  : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> apiece (qb_addr b) (qb_addr b + kBatchSize).

  (* [comment removed for export] *)
  Lemma apiece_block_sep : forall ch0 lo hi, In ch0 (chunk_list st) -> ch_state ch0 = CAllocated -> apiece lo hi ->
    hi <= ch_user_beg ch0 \/ ch_user_beg ch0 + round_up (ch_used ch0) 8 <= lo.
  Proof.
    intros ch0 lo hi H0 A0 P.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geom s OK ch0 H0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof (ext_facts ch0 H0) as (X01 & X02 & X03 & XP & XS).
    (* [comment removed for export] *)
    destruct P as [ | | | | |c Hc|c Hc|c cp Hc Hin|h Hh|ch Hch|ch Hch|ch Hch Hq|b Hb].
    - (* [comment removed for export] *) destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). unfold st in *. clear - G1 G2 G4 B1 B2 D2; try acb. unfold disj, kSpaceSize, kPageSize in *. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & _ & _ & Q & _).
        clear - G1 G2 G4 L0 E0 A0' Q X03; try acb. unfold disj, kPageSize in *. lia.
    - (* [comment removed for export] *) destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). unfold st in *. clear - G1 G2 G4 B1 B2 D3; try acb. unfold disj, kSpaceSize, kPageSize in *. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & _ & _ & _ & Q & _).
        clear - G1 G2 G4 L0 E0 A0' Q X03; try acb. unfold disj, kPageSize in *. lia.
    - (* [comment removed for export] *) destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). unfold st in *. clear - G1 G2 G4 B1 B2 D3; try acb. unfold disj, kSpaceSize, kPageSize in *. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & _ & _ & _ & Q & _).
        clear - G1 G2 G4 L0 E0 A0' Q X03; try acb. unfold disj, kPageSize in *. lia.
    - (* [comment removed for export] *) destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). clear - G1 G2 G4 B1 B2; try acb. unfold a_ri, kSpaceSize, kPageSize in *. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & Q & _).
        clear - G1 G2 G4 L0 E0 A0' Q X03; try acb. unfold disj, a_ri, kSpaceSize, kPageSize in *. lia.
    - (* [comment removed for export] *) destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). unfold st in *. clear - G1 G2 G4 B1 B2 D1; try acb. unfold disj, kSpaceSize, kPageSize in *. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & _ & Q & _).
        clear - G1 G2 G4 L0 E0 A0' Q X03; try acb. unfold disj, kPageSize in *. lia.
    - (* [comment removed for export] *) pose proof (WF_region st c W Hc) as RO. pose proof (ro_fa_bound _ _ RO) as FB.
      pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold FA in *. rewrite free_array_base_eq in *.
      destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). pose proof (carved_range st _ _ W C) as (CR1 & CR2 & CR3).
        destruct (Z.eq_dec c (ch_class ch0)) as [->|NE].
        * right. unfold st in *. clear - G1 G2 G4 EE CR2; try acb. lia.
        * destruct C as (Hc0 & _). destruct (regions_disjoint st c (ch_class ch0) ltac:(hci; lia) ltac:(hci; lia) NE) as [D|D];
          unfold st in *; clear - G1 G2 G4 EE CR1 CR2 D FB; try acb; unfold RB, kFreeArrayOffset, kFreeArraySize in *; lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & Q & _).
        unfold st in *. clear - G1 G2 G4 L0 E0 A0' Q X03 RS1 RS2 FB; try acb. unfold disj, a_sb, RB, kFreeArrayOffset, kFreeArraySize, kSpaceSize, kPageSize in *. lia.
    - (* [comment removed for export] *) pose proof (WF_region st c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO) as MB. pose proof (ro_alloc_nonneg _ _ RO) as AN.
      pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold RB in *.
      destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). pose proof (carved_range st _ _ W C) as (CR1 & CR2 & CR3).
        destruct (Z.eq_dec c (ch_class ch0)) as [->|NE].
        * right. destruct C as (_ & _ & _ & _ & CL). unfold st in *. clear - G1 G2 G4 EE CL; try acb. lia.
        * destruct C as (Hc0 & _). destruct (regions_disjoint st c (ch_class ch0) ltac:(hci; lia) ltac:(hci; lia) NE) as [D|D];
          unfold st in *; clear - G1 G2 G4 EE CR1 CR2 D MB AN; try acb; unfold kFreeArrayOffset, kUserMapSize in *; lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & Q & _).
        unfold st in *. clear - G1 G2 G4 L0 E0 A0' Q X03 RS1 RS2 MB AN; try acb. unfold disj, a_sb, kFreeArrayOffset, kUserMapSize, kSpaceSize, kPageSize in *. lia.
    - (* [comment removed for export] *)
      assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
      destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2).
        destruct (carved_sep st _ _ _ _ W C C') as [[EC EA]|D].
        * exfalso. eapply (inuse_not_free s OK ch0 c cp); eauto.
        * clear - G1 G2 G4 EE D; try acb. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & Q & _).
        pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & _).
        unfold st in *. clear - G1 G2 G4 L0 E0 A0' Q X03 CS1 CS2; try acb. unfold disj, a_sb, kSpaceSize, kPageSize in *. lia.
    - (* [comment removed for export] *) pose proof (SEC h Hh) as (_ & _ & _ & Q4 & Q & _).
      destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2). unfold st in *. clear - G1 G2 G4 B1 B2 Q4 Q; try acb. unfold disj, kSpaceSize, kPageSize in *. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0').
        destruct (Z.eq_dec (sc_map_beg h) (sc_map_beg h0)) as [EQ|NE].
        * left. clear - G1 G2 A0' EQ; try acb. unfold kPageSize in *. lia.
        * pose proof (SEC2 h h0 Hh Hh0 NE) as D. clear - G1 G2 G4 L0 E0 A0' D Q4 X03; try acb. unfold disj, kPageSize in *. lia.
    - (* [comment removed for export] *) pose proof (chunk_geom s OK ch Hch) as (G1' & G2' & G3' & G4' & G5' & _).
      pose proof (ext_facts ch Hch) as (_ & _ & X3' & _).
      destruct (records_sep s OK ch0 ch H0 Hch) as [<-|[D|D]]; [left; lia| |]; clear - G1 G2 G3 G4 G5 G1' G2' G3' G4' G5' X3' X03 D; try acb; lia.
    - (* [comment removed for export] *) pose proof (chunk_geom s OK ch Hch) as (G1' & G2' & G3' & G4' & G5' & _).
      pose proof (ext_facts ch Hch) as (_ & _ & X3' & _).
      destruct (records_sep s OK ch0 ch H0 Hch) as [<-|[D|D]]; [right; lia| |]; clear - G1 G2 G3 G4 G5 G1' G2' G3' G4' G5' X3' X03 D; try acb; lia.
    - (* [comment removed for export] *) pose proof (chunk_geom s OK ch Hch) as (G1' & G2' & G3' & G4' & G5' & _).
      pose proof (ext_facts ch Hch) as (_ & _ & X3' & _).
      destruct (records_sep s OK ch0 ch H0 Hch) as [<-|[D|D]]; [congruence| |]; clear - G1 G2 G3 G4 G5 G1' G2' G3' G4' G5' X3' X03 D; try acb; lia.
    - (* [comment removed for export] *) pose proof (batch_carved s OK b Hb) as (C' & _).
      destruct (ch_primary ch0) eqn:E.
      + destruct (XP eq_refl) as (C & EE & B1 & B2).
        destruct (carved_sep st _ _ _ _ W C C') as [[EC EA]|D].
        * exfalso. eapply (inuse_not_batch s OK ch0 b); eauto.
        * change (class_size kBatchClass) with kBatchSize in D. clear - G1 G2 G4 EE D; try acb. lia.
      + destruct (XS eq_refl) as (h0 & Hh0 & L0 & E0 & A0'). pose proof (SEC h0 Hh0) as (_ & _ & _ & _ & Q & _).
        pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & _). change (class_size kBatchClass) with kBatchSize in CS2.
        unfold st in *. clear - G1 G2 G4 L0 E0 A0' Q X03 CS1 CS2; try acb. unfold disj, a_sb, kSpaceSize, kPageSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma chunk_align : forall ch, In ch (chunk_list st) ->
    ch_alloc_beg ch mod 16 = 0 /\ ch_rz ch mod 16 = 0 /\ ch_user_beg ch mod 16 = 0 /\ ch_end ch mod 8 = 0 /\ ch_lo ch mod 8 = 0.
  Proof.
    intros ch Hch. pose proof PL as (S1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof (WF_chunk st ch W Hch) as (_ & _ & R3 & _).
    pose proof (rz_size_facts (ch_used ch)) as (_ & RZ & _). change (rz_size (ch_used ch)) with (rq_rz (compute_req (ch_used ch))) in RZ.
    rewrite <- R3 in RZ.
    assert (AB : ch_alloc_beg ch mod 16 = 0 /\ ch_end ch mod 8 = 0 /\ ch_lo ch mod 8 = 0).
    { unfold ch_lo. destruct (ch_primary ch) eqn:E.
      - destruct G7 as [C EE]. destruct C as (Hc & Hsz & H0 & Hm & Hle). pose proof (class_size_table_facts (ch_class ch) Hc) as (_ & CS & _).
        rewrite region_beg_eq in *. unfold a_sb in S1. unfold st in *. rewrite EE.
        set (sz := class_size (ch_class ch)) in *. set (ab := ch_alloc_beg ch) in *. set (sb := as_space_beg (a_st s)) in *.
        clear - S1 Hsz Hm CS; try acb. Z.div_mod_to_equations. (first [clear - H24 H23 H19 H14 H10 H9 H5 H4 H0 H CS Hm S1; nia | nia]).
      - destruct G7 as (h & Hh & Hb & He). pose proof (SEC h Hh) as (Q1 & _). unfold kPageSize in *.
        unfold ch_end. rewrite E. unfold round_up, kPageSize. set (ab := ch_alloc_beg ch) in *.
        set (k := (rq_needed (compute_req (ch_used ch)) + 4096 - 1) / 4096). clearbody k. rewrite Hb in Q1. clear - Q1; try acb.
        assert (Hab : exists q, ab = 4096 * q + 4096). { exists ((ab - 4096) / 4096). Z.div_mod_to_equations. lia. }
        destruct Hab as [q ->]. clear Q1.
        split; [| split]; Z.div_mod_to_equations; lia. }
    destruct AB as (AB1 & AB2 & AB3). rewrite G2. repeat split; auto. clear - AB1 RZ; try acb. Z.div_mod_to_equations. nia.
  Qed.

  (* [comment removed for export] *)
  Inductive spiece : Z -> Z -> Prop :=
  | sp_farray : forall c, 0 <= c < kNumClasses -> spiece (FA s c) (FA s c + rg_mapped_free_array (get_region st c))
  | sp_tail   : forall c, 0 <= c < kNumClasses ->
                spiece (RB s c + rg_allocated_user (get_region st c)) (RB s c + rg_mapped_user (get_region st c))
  | sp_freech : forall c cp, 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
                spiece (compact_to_addr st c cp) (compact_to_addr st c cp + class_size c)
  | sp_chleft : forall ch, In ch (chunk_list st) -> spiece (ch_alloc_beg ch) (ch_user_beg ch)
  | sp_chright8 : forall ch, In ch (chunk_list st) -> spiece (ch_user_beg ch + round_up (ch_used ch) 8) (ch_end ch)
  | sp_chquar : forall ch, In ch (chunk_list st) -> ch_state ch = CQuarantine ->
                spiece (ch_user_beg ch) (ch_user_beg ch + round_up (ch_used ch) 8)
  | sp_sechdr : forall ch, In ch (chunk_list st) -> ch_primary ch = false -> spiece (ch_alloc_beg ch - kPageSize) (ch_alloc_beg ch)
  | sp_batch  : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> spiece (qb_addr b) (qb_addr b + kBatchSize).

  Lemma spiece_block_sep : forall ch0 lo hi, In ch0 (chunk_list st) -> ch_state ch0 = CAllocated -> spiece lo hi ->
    hi <= ch_user_beg ch0 \/ ch_user_beg ch0 + round_up (ch_used ch0) 8 <= lo.
  Proof.
    intros ch0 lo hi H0 A0 P.
    destruct P as [c Hc|c Hc|c cp Hc Hin|ch Hch|ch Hch|ch Hch Hq|ch Hch Hp|b Hb].
    - exact (apiece_block_sep ch0 _ _ H0 A0 (ap_farray c Hc)).
    - exact (apiece_block_sep ch0 _ _ H0 A0 (ap_tail c Hc)).
    - exact (apiece_block_sep ch0 _ _ H0 A0 (ap_freech c cp Hc Hin)).
    - destruct (apiece_block_sep ch0 _ _ H0 A0 (ap_chleft ch Hch)) as [HH|HH]; [left; exact HH| right].
      pose proof (ext_facts ch Hch) as (_ & _ & X3 & _). lia.
    - exact (apiece_block_sep ch0 _ _ H0 A0 (ap_chright8 ch Hch)).
    - exact (apiece_block_sep ch0 _ _ H0 A0 (ap_chquar ch Hch Hq)).
    - destruct (apiece_block_sep ch0 _ _ H0 A0 (ap_chleft ch Hch)) as [HH|HH].
      + left. pose proof (chunk_geom s OK ch Hch) as (G1' & G2' & _). lia.
      + right. unfold ch_lo in HH. rewrite Hp in HH. exact HH.
    - exact (apiece_block_sep ch0 _ _ H0 A0 (ap_batch b Hb)).
  Qed.

  (* [comment removed for export] *)
  Lemma mod8_add : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
  Proof. intros a b Ha Hb. Z.div_mod_to_equations. lia. Qed.
  Lemma mod8_sub : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a - b) mod 8 = 0.
  Proof. intros a b Ha Hb. Z.div_mod_to_equations. lia. Qed.
  Lemma mod8_of : forall k x, k mod 8 = 0 -> k <> 0 -> x mod k = 0 -> x mod 8 = 0.
  Proof. intros k x Hk Hnz Hx. Z.div_mod_to_equations. nia. Qed.
  Lemma mod8_mul_r : forall a b, b mod 8 = 0 -> (a * b) mod 8 = 0.
  Proof. intros a b Hb. Z.div_mod_to_equations. nia. Qed.
  Lemma mod8_mul_l : forall a b, a mod 8 = 0 -> (a * b) mod 8 = 0.
  Proof. intros a b Ha. Z.div_mod_to_equations. nia. Qed.
  Ltac mod8 := first [ reflexivity | assumption
                     | apply mod8_add; mod8 | apply mod8_sub; mod8 | apply mod8_mul_r; mod8 | apply mod8_mul_l; mod8
                     | eapply (mod8_of 16); [reflexivity| lia| assumption]
                     | eapply (mod8_of 65536); [reflexivity| lia| assumption]
                     | eapply (mod8_of 4096); [reflexivity| lia| assumption]
                     | eapply (mod8_of 262144); [reflexivity| lia| assumption]
                     | eapply (mod8_of (2^32)); [reflexivity| lia| assumption] ].

  Lemma spiece_bounds : forall lo hi, spiece lo hi -> 0 <= lo /\ lo <= hi /\ hi <= aceil /\ lo mod 8 = 0 /\ hi mod 8 = 0.
  Proof.
    intros lo hi P. pose proof PL as (S1 & S2 & S3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    acb. unfold a_sb in *. unfold kNumClasses, kPageSize in *.
    destruct P as [c Hc|c Hc|c cp Hc Hin|ch Hch|ch Hch|ch Hch Hq|ch Hch Hp|b Hb].
    - pose proof (WF_region st c W Hc) as RO. pose proof (ro_fa_bound _ _ RO) as FB. pose proof (ro_fa_mod _ _ RO) as FM.
      pose proof (ro_fa_le _ _ RO) as FL. pose proof (ro_numfreed _ _ RO) as NF.
      pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold FA. rewrite free_array_base_eq, region_beg_eq in *.
      unfold kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kSpaceSize, AHI_LO, zlen in *. unfold st in *.
      set (sb := as_space_beg (a_st s)) in *. set (f := rg_mapped_free_array _) in *. clearbody f.
      split; [lia|]. split; [lia|]. split; [lia|]. split; mod8.
    - pose proof (WF_region st c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO) as MB. pose proof (ro_alloc_nonneg _ _ RO) as AN.
      pose proof (ro_alloc_le _ _ RO) as AL. pose proof (ro_mapped_mod _ _ RO) as MM. pose proof (ro_alloc_mod _ _ RO) as AM.
      pose proof (ro_empty _ _ RO) as EM. pose proof (class_size_table_facts c Hc) as (_ & CS & _).
      pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold RB. rewrite region_beg_eq in *.
      unfold kFreeArrayOffset, kUserMapSize, kSpaceSize, AHI_LO in *. unfold st in *.
      set (sb := as_space_beg (a_st s)) in *. set (al := rg_allocated_user _) in *. set (mu := rg_mapped_user _) in *.
      set (sz := class_size c) in *. clearbody al mu sz.
      assert (AM8 : al mod 8 = 0).
      { destruct (Z.eq_dec sz 0) as [E0|NZ].
        - specialize (EM E0). replace al with 0 by (first [clear - EM AL AN; lia | lia]). reflexivity.
        - specialize (AM NZ). eapply (mod8_of sz); [| exact NZ| exact AM]. eapply (mod8_of 32); [reflexivity| lia| exact CS]. }
      split; [(first [clear - RS1 AN S2; lia | lia])|]. split; [lia|]. split; [(first [clear - RS2 MB S3; lia | lia])|]. split; mod8.
    - assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
      pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & CS3). pose proof (class_size_table_facts c Hc) as (_ & CS & _).
      rewrite compact_to_addr_eq, region_beg_eq in *.
      unfold kSpaceSize, AHI_LO, a_sb in *. unfold st in *.
      set (sb := as_space_beg (a_st s)) in *. set (sz := class_size c) in *. clearbody sz.
      assert (sz mod 8 = 0) by (eapply (mod8_of 32); [reflexivity| lia| exact CS]).
      split; [lia|]. split; [lia|]. split; [lia|]. split; mod8.
    - pose proof (ext_facts ch Hch) as (X1 & X2 & X3 & _). pose proof (chunk_align ch Hch) as (A1 & A2 & A3 & A4 & A5).
      pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _). acb. unfold AHI_LO, AIMG_TOP in *.
      assert (ch_alloc_beg ch mod 8 = 0) by (eapply (mod8_of 16); [reflexivity| lia| exact A1]).
      assert (ch_user_beg ch mod 8 = 0) by (eapply (mod8_of 16); [reflexivity| lia| exact A3]).
      split; [lia|]. split; [lia|]. split; [lia|]. split; assumption.
    - pose proof (ext_facts ch Hch) as (X1 & X2 & X3 & _). pose proof (chunk_align ch Hch) as (A1 & A2 & A3 & A4 & A5).
      pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _). acb. unfold AHI_LO, AIMG_TOP in *.
      assert (ch_user_beg ch mod 8 = 0) by (eapply (mod8_of 16); [reflexivity| lia| exact A3]).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact A4]. rewrite G6. mod8.
    - pose proof (ext_facts ch Hch) as (X1 & X2 & X3 & _). pose proof (chunk_align ch Hch) as (A1 & A2 & A3 & A4 & A5).
      pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _). acb. unfold AHI_LO, AIMG_TOP in *.
      assert (ch_user_beg ch mod 8 = 0) by (eapply (mod8_of 16); [reflexivity| lia| exact A3]).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [assumption|]. rewrite G6. mod8.
    - pose proof (ext_facts ch Hch) as (X1 & X2 & X3 & _ & XS). pose proof (chunk_align ch Hch) as (A1 & A2 & A3 & A4 & A5).
      pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _). acb. unfold AHI_LO, AIMG_TOP in *.
      unfold ch_lo in *. rewrite Hp in *. unfold kPageSize in *.
      assert (ch_alloc_beg ch mod 8 = 0) by (eapply (mod8_of 16); [reflexivity| lia| exact A1]).
      split; [lia|]. split; [lia|]. split; [lia|]. split; assumption.
    - pose proof (batch_carved s OK b Hb) as (C' & _). pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & CS3).
      change (class_size kBatchClass) with 8192 in *.
      destruct C' as (_ & _ & C0 & C1 & _). rewrite region_beg_eq in C0, C1. change (class_size kBatchClass) with 8192 in C1.
      unfold kSpaceSize, AHI_LO, a_sb, kBatchSize, kBatchClass in *. unfold st in *.
      set (sb := as_space_beg (a_st s)) in *.
      assert (E : qb_addr b = (qb_addr b - (sb + 24 * 2^32)) + sb + 24 * 2^32) by lia.
      assert (M : qb_addr b mod 8 = 0).
      { rewrite E. apply mod8_add; [apply mod8_add; [| mod8]| mod8]. eapply (mod8_of 8192); [reflexivity| lia| exact C1]. }
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact M| apply mod8_add; [exact M| reflexivity]].
  Qed.

  (* [comment removed for export] *)
  Lemma apiece_noshadow : forall lo hi, apiece lo hi -> hi <= ALOWSH_LO \/ AHI_LO <= lo.
  Proof.
    intros lo hi P. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    destruct P as [ | | | | |c Hc|c Hc|c cp Hc Hin|h Hh|ch Hch|ch Hch|ch Hch Hq|b Hb].
    - clear - T2. unfold kPageSize in *. aunf. lia.
    - clear - X2. aunf. lia.
    - clear - X2. aunf. lia.
    - right. unfold a_ri, a_sb, kSpaceSize in *. unfold st in *. lia.
    - clear - P2. aunf. lia.
    - right. pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold FA. rewrite free_array_base_eq. unfold a_sb, kFreeArrayOffset in *. unfold st in *. (first [clear - RS1 S2; lia | lia]).
    - right. pose proof (region_in_space st c Hc) as [RS1 RS2]. pose proof (ro_alloc_nonneg _ _ (WF_region st c W Hc)). unfold RB, a_sb in *. unfold st in *. (first [clear - H RS1 S2; lia | lia]).
    - right. assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
      pose proof (carved_in_space s OK _ _ C') as (CS1 & _). unfold a_sb in *. unfold st in *. (first [clear - CS1 S2; lia | lia]).
    - pose proof (SEC h Hh) as (_ & Q & _ & Q4 & _). clear - Q Q4. unfold kPageSize in *. aunf. lia.
    - pose proof (ext_facts ch Hch) as (E1 & _ & E3 & _). pose proof (ext_band ch Hch) as EB. pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _).
      clear - E3 EB G1 G2 G3 G4 G5. aunf. lia.
    - pose proof (ext_facts ch Hch) as (E1 & _ & E3 & _). pose proof (ext_band ch Hch) as EB. pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _).
      clear - E3 EB G1 G2 G3 G4 G5. aunf. lia.
    - pose proof (ext_facts ch Hch) as (E1 & _ & E3 & _). pose proof (ext_band ch Hch) as EB. pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _).
      clear - E3 EB G1 G2 G3 G4 G5. aunf. lia.
    - right. pose proof (batch_carved s OK b Hb) as (C' & _). pose proof (carved_in_space s OK _ _ C') as (CS1 & _). unfold a_sb in *. unfold st in *. (first [clear - CS1 S2; lia | lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma afoot_cases : forall a, afoot s a ->
       (exists lo hi, apiece lo hi /\ lo <= a < hi)
    \/ (exists ch, In ch (chunk_list st) /\ ch_user_beg ch + ch_used ch <= a < ch_end ch)
    \/ (AIMG_LO <= a < AIMG_TOP /\ astatic a)
    \/ (exists lo hi, spiece lo hi /\ sh lo <= a < sh lo + (hi - lo) / 8).
  Proof.
    intros a AF.
    destruct AF as [H|H|H|H|c Hc H|c Hc H|c cp Hc Hin H|H|h Hh H|ch Hch H|ch Hch H|ch Hch Hq H|b Hb H
                   |c Hc H|c Hc H|c cp Hc Hin H|ch Hch H|ch Hch H|ch Hch Hq H|ch Hch Hp H|b Hb H].
    - do 2 right; left. unfold astatic. unfold AINST, OI_MISMATCH, AIMG_LO, AIMG_TOP in *. split; [lia| left; lia].   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      do 2 right; left. unfold astatic. unfold aflags_range in H. unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS,
        AIAINIT, AIAINST, AHOOKS, ADYING, AREALMEMSET, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_LO, AIMG_TOP, AINST, OI_MISMATCH in *.
      clear - H.
      repeat (destruct H as [H|H]);
        (split; [lia| let rec pick := lazymatch goal with |- _ \/ _ => first [ left; (lia_guard; (first [clear - H; lia | lia])) | right; pick ] | |- _ => lia end in pick]).
    - left. destruct H as [H|[H|H]].
      + exists (a_thr s), (a_thr s + kPageSize). split; [constructor|]. unfold OT_UNWINDING, kPageSize in *. lia.
      + exists (a_ctx s + 8), (a_ctx s + 12). split; [constructor| lia].
      + exists (a_ctx s + 152), (a_ctx s + 160). split; [constructor| lia].
    - left. do 2 eexists. split; [apply ap_rinfo| exact H].
    - left. do 2 eexists. split; [apply (ap_farray c Hc)| exact H].
    - left. do 2 eexists. split; [apply (ap_tail c Hc)| exact H].
    - left. do 2 eexists. split; [apply (ap_freech c cp Hc Hin)| exact H].
    - left. exists (a_pa s), (a_pa s + kPtrArrayReserve). split; [constructor|].
      pose proof W as WW. destruct WW as (_ & _ & _ & _ & _ & _ & Wn & Wr & _). unfold kChunksBlockCount, kPtrArrayReserve in *. unfold st in *. lia.
    - left. do 2 eexists. split; [apply (ap_sechdr h Hh)| exact H].
    - left. do 2 eexists. split; [apply (ap_chleft ch Hch)|]. pose proof (ext_facts ch Hch) as (_ & _ & X3 & _). lia.
    - right; left. exists ch. auto.
    - left. do 2 eexists. split; [apply (ap_chquar ch Hch Hq)|]. pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _). lia.
    - left. do 2 eexists. split; [apply (ap_batch b Hb)| exact H].
    - do 3 right. do 2 eexists. split; [apply (sp_farray c Hc)|]. replace (FA s c + _ - FA s c) with (rg_mapped_free_array (get_region st c)) by lia. exact H.
    - do 3 right. do 2 eexists. split; [apply (sp_tail c Hc)|].
      replace (RB s c + _ - _) with (rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c)) by lia. exact H.
    - do 3 right. do 2 eexists. split; [apply (sp_freech c cp Hc Hin)|]. replace (_ + class_size c - _) with (class_size c) by lia. exact H.
    - do 3 right. do 2 eexists. split; [apply (sp_chleft ch Hch)|]. pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & _).
      replace (ch_user_beg ch - ch_alloc_beg ch) with (ch_rz ch) by lia. exact H.
    - do 3 right. do 2 eexists. split; [apply (sp_chright8 ch Hch)| exact H].
    - do 3 right. do 2 eexists. split; [apply (sp_chquar ch Hch Hq)|]. pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
      replace (ch_user_beg ch + round_up (ch_used ch) 8 - ch_user_beg ch) with (8 * nsh (ch_used ch)) by lia.
      rewrite Z.mul_comm, Z.div_mul by lia. exact H.
    - do 3 right. do 2 eexists. split; [apply (sp_sechdr ch Hch Hp)|].
      replace (ch_alloc_beg ch - (ch_alloc_beg ch - kPageSize)) with kPageSize by lia. change (kPageSize / 8) with 512. exact H.
    - do 3 right. do 2 eexists. split; [apply (sp_batch b Hb)|]. replace (qb_addr b + kBatchSize - qb_addr b) with kBatchSize by lia. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma alb_In : forall A n, In (A, n) (alb s) ->
    exists ch, In ch (chunk_list st) /\ ch_state ch = CAllocated /\ ch_user_beg ch = A /\ ch_used ch = n.
  Proof.
    intros A n H. unfold alb in H. apply in_map_iff in H. destruct H as (ch & E & Hin). apply filter_In in Hin. destruct Hin as [Hin AL].
    exists ch. injection E as E1 E2. unfold is_alloc in AL. destruct (ch_state ch); [| discriminate]. unfold st. auto.
  Qed.

  Lemma sh_mono : forall x y, x <= y -> sh x <= sh y.
  Proof. intros x y H. unfold sh. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_diff8 : forall lo hi, lo mod 8 = 0 -> sh lo + (hi - lo) / 8 = sh hi.
  Proof. intros lo hi H. unfold sh. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_add8 : forall x k, x mod 8 = 0 -> sh (x + 8 * k) = sh x + k.
  Proof. intros x k H. unfold sh. Z.div_mod_to_equations. lia. Qed.

  Theorem block_not_afoot_thm : forall LB m A n a, ARHEAP s LB m -> In (A, n) LB -> A <= a < A + n -> ~ afoot s a.
  Proof.
    intros LB m A n a (HA & ND & EQ) Hin Ha AF. apply EQ in Hin. destruct (alb_In _ _ Hin) as (ch0 & H0 & A0 & U0 & N0). subst A n.
    pose proof (chunk_geom s OK ch0 H0) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts ch0 H0) as (X1 & X2 & X3 & _).
    destruct (afoot_cases a AF) as [(lo & hi & P & R)|[(ch & Hch & R)|[[R _]|(lo & hi & P & R)]]].
    - destruct (apiece_block_sep ch0 lo hi H0 A0 P); lia.
    - pose proof (chunk_geom s OK ch Hch) as (G1' & G2' & G3' & G4' & G5' & _). pose proof (ext_facts ch Hch) as (_ & _ & X3' & _).
      destruct (records_sep s OK ch0 ch H0 Hch) as [<-|[D|D]]; lia.
    - unfold AIMG_TOP, AHI_LO in *. lia.
    - pose proof (spiece_bounds lo hi P) as (B1 & B2 & B3 & B4 & B5).
      pose proof (sh_hi lo ((hi - lo) / 8) ltac:(hci; Z.div_mod_to_equations; lia) ltac:(hci; Z.div_mod_to_equations; lia)).
      pose proof (sh_lo lo B1). pose proof (ext_band ch0 H0) as EB.
      clear - H H1 EB R Ha G1 G2 G3 G4 G5 X3. aunf. unfold ASHADOW_BASE in *. lia.
  Qed.

  Theorem block_shadow_not_afoot_thm : forall LB m A n a, ARHEAP s LB m -> In (A, n) LB -> sh A <= a < sh A + nsh n -> ~ afoot s a.
  Proof.
    intros LB m A n a (HA & ND & EQ) Hin Ha AF. apply EQ in Hin. destruct (alb_In _ _ Hin) as (ch0 & H0 & A0 & U0 & N0). subst A n.
    pose proof (chunk_geom s OK ch0 H0) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts ch0 H0) as (X1 & X2 & X3 & _).
    pose proof (chunk_align ch0 H0) as (_ & _ & AL & _).
    assert (U8 : ch_user_beg ch0 mod 8 = 0) by (eapply (mod8_of 16); [reflexivity| lia| exact AL]).
    pose proof (sh_hi (ch_user_beg ch0) (nsh (ch_used ch0)) ltac:(hci; lia) ltac:(hci; lia)) as SH1.
    pose proof (sh_lo (ch_user_beg ch0) ltac:(hci; unfold AIMG_TOP in *; lia)) as SH0.
    destruct (afoot_cases a AF) as [(lo & hi & P & R)|[(ch & Hch & R)|[[R _]|(lo & hi & P & R)]]].
    - pose proof (apiece_noshadow lo hi P). unfold ALOWSH_LO, ASHADOW_BASE in *. lia.
    - pose proof (chunk_geom s OK ch Hch) as (G1' & G2' & G3' & _). pose proof (ext_facts ch Hch) as (X1' & _ & X3' & _).
      pose proof (ext_band ch Hch) as EB. clear - G1' G2' G3' X3' EB R Ha SH0 SH1. aunf. unfold ASHADOW_BASE in *. lia.
    - unfold AIMG_TOP, ASHADOW_BASE in *. lia.
    - pose proof (spiece_bounds lo hi P) as (B1 & B2 & B3 & B4 & B5). rewrite (sh_diff8 lo hi B4) in R.
      destruct (spiece_block_sep ch0 lo hi H0 A0 P) as [D|D].
      + pose proof (sh_mono _ _ D). lia.
      + rewrite G6 in D. pose proof (sh_mono _ _ D) as M. rewrite (sh_add8 _ _ U8) in M. lia.
  Qed.

  Theorem ARHEAP_block_range_thm : forall LB m A n, ARHEAP s LB m -> In (A, n) LB -> arblock_range A n.
  Proof.
    intros LB m A n (HA & ND & EQ) Hin. apply EQ in Hin. destruct (alb_In _ _ Hin) as (ch0 & H0 & A0 & U0 & N0). subst A n.
    pose proof (chunk_geom s OK ch0 H0) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts ch0 H0) as (X1 & X2 & X3 & _).
    pose proof (chunk_align ch0 H0) as (_ & _ & AL & _). pose proof (ext_band ch0 H0) as EB. unfold arblock_range.
    split; [lia|]. split; [exact AL|]. split; [lia|]. split; [lia|]. eapply aapp_sub; [exact EB| lia| lia].
  Qed.

  Theorem ARHEAP_blocks_disjoint_thm : forall LB m A1 n1 A2 n2, ARHEAP s LB m -> In (A1, n1) LB -> In (A2, n2) LB -> A1 <> A2 ->
    A1 + round_up n1 8 + 16 <= A2 \/ A2 + round_up n2 8 + 16 <= A1.
  Proof.
    intros LB m A1 n1 A2 n2 (HA & ND & EQ) H1 H2 NE. apply EQ in H1. apply EQ in H2.
    destruct (alb_In _ _ H1) as (ch1 & I1 & S1 & U1 & N1). destruct (alb_In _ _ H2) as (ch2 & I2 & S2 & U2 & N2). subst A1 n1 A2 n2.
    pose proof (chunk_geom s OK ch1 I1) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts ch1 I1) as (X1 & X2 & X3 & _).
    pose proof (chunk_geom s OK ch2 I2) as (G1' & G2' & G3' & G4' & G5' & G6' & _). pose proof (ext_facts ch2 I2) as (X1' & X2' & X3' & _).
    destruct (records_sep s OK ch1 ch2 I1 I2) as [<-|[D|D]]; [congruence| left; lia| right; lia].
  Qed.

  Theorem ARHEAP_frame_thm : forall LB m m' W0, ARHEAP s LB m -> munch W0 m m' -> wmono asegs m m' ->
    Forall (aclient_write_ok s LB) W0 -> ARHEAP s LB m'.
  Proof.
    intros LB m m' W0 HR MU WM FA. destruct HR as (HA & ND & EQ). split; [| split; [exact ND| exact EQ]].
    eapply AREP_frame; [exact HA| exact MU| exact WM|].
    unfold awin_ok. eapply Forall_impl; [| exact FA]. intros iv Hiv a Ha.
    destruct Hiv as [H|[(b & Hb & H1 & H2)|[(b & Hb & H1 & H2)|[(H1 & H2 & H3)|H]]]].
    - apply (stack_not_afoot s OK). lia.
    - destruct b as [A n]. eapply (block_not_afoot_thm LB m A n a); [split; [exact HA| split; assumption]| exact Hb| cbn in *; lia].
    - destruct b as [A n]. eapply (block_shadow_not_afoot_thm LB m A n a); [split; [exact HA| split; assumption]| exact Hb| cbn in *; lia].
    - apply (image_not_afoot s OK); [lia| apply H3; lia].
    - apply H. exact Ha.
  Qed.
End ClientView.
Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Theorem ARHEAP_block_range_ok : ARHEAP_block_range_stmt.
Proof. intros s LB m A n H Hin. eapply ARHEAP_block_range_thm; eauto. destruct H as [[OK _] _]. exact OK. Qed.
Theorem ARHEAP_blocks_disjoint_ok : ARHEAP_blocks_disjoint_stmt.
Proof. intros s LB m A1 n1 A2 n2 H. eapply ARHEAP_blocks_disjoint_thm; eauto. destruct H as [[OK _] _]. exact OK. Qed.
Theorem stack_not_afoot_ok : stack_not_afoot_stmt.
Proof. intros s m a H. apply stack_not_afoot. destruct H as [OK _]. exact OK. Qed.
Theorem block_not_afoot_ok : block_not_afoot_stmt.
Proof. intros s LB m A n a H. eapply block_not_afoot_thm; eauto. destruct H as [[OK _] _]. exact OK. Qed.
Theorem block_shadow_not_afoot_ok : block_shadow_not_afoot_stmt.
Proof. intros s LB m A n a H. eapply block_shadow_not_afoot_thm; eauto. destruct H as [[OK _] _]. exact OK. Qed.
Theorem image_not_afoot_ok : image_not_afoot_stmt.
Proof. intros s m a H. apply image_not_afoot. destruct H as [OK _]. exact OK. Qed.
Theorem ARHEAP_frame_ok : ARHEAP_frame_stmt.
Proof. intros s LB m m' W H. eapply ARHEAP_frame_thm; eauto. destruct H as [[OK _] _]. exact OK. Qed.

End HCW.


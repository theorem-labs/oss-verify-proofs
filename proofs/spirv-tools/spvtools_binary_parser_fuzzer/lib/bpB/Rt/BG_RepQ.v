(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition xb_ok (st : astate) (B : Z) : Prop := carved st (class_of_addr st B) B.

Definition xc_ok (st : astate) (m : Z) : Prop :=
  exists ch, find_chunk (as_chunks st) (m + kChunkHeaderSize) = Some ch /\ ch_state ch = CQuarantine.

Definition WFQ (st : astate) (XC XB : list Z) : Prop :=
     (forall c, 0 <= c < kNumClasses -> region_ok st c /\ cache_ok st c)
  /\ List.NoDup (carved_addr_list st ++ XB)
  /\ (forall ch, In ch (chunk_list st) -> chunk_ok st ch)
  /\ (forall ch ch', In ch (chunk_list st) -> In ch' (chunk_list st) -> ch_user_beg ch = ch_user_beg ch' -> ch = ch')
  /\ zlen (List.filter (fun ch => negb (ch_primary ch)) (chunk_list st)) = zlen (as_sec st)
  /\ List.NoDup (List.map sc_map_beg (as_sec st))
  /\ zlen (as_sec st) <= as_n_reserved st /\ (as_n_reserved st = 0 \/ as_n_reserved st = kChunksBlockCount)
  /\ qcache_ok st (as_tq st) /\ qcache_ok st (as_gq st)
  /\ List.NoDup (List.flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st)) ++ XC)
  /\ (forall ch, In ch (chunk_list st) -> ch_state ch = CQuarantine ->
        (exists b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) /\ In (ch_chunk_beg ch) (qb_chunks b))
        \/ In (ch_chunk_beg ch) XC)
  /\ rg_mapped_user (get_region st 0) = 0 /\ rg_mapped_user (get_region st 31) = 0
  /\ pc_count (get_pc st 0) = 0 /\ pc_count (get_pc st 31) = 0
  /\ length (as_regions st) = 32%nat /\ length (as_cache st) = 32%nat
  /\ as_qmax st = kQuarantineMaxSize /\ as_qmin st = kQuarantineMinSize /\ as_qcache st = kMaxCacheSize
  /\ (forall k x, PositiveMap.find k (as_chunks st) = Some x -> k = ckey (ch_user_beg x) /\ 0 < ch_user_beg x)
  /\ (forall m, In m XC -> xc_ok st m)
  /\ (forall B, In B XB -> xb_ok st B).

Definition qbounds (st : astate) : Prop :=
  qc_bytes (as_tq st) <= as_qcache st /\ qc_bytes (as_gq st) <= as_qmax st.

Lemma WF_WFQ : forall st, WF st <-> WFQ st [] [] /\ qbounds st.
Proof.
  intros st. unfold WF, WFQ, qbounds. rewrite !app_nil_r. split.
  - intros (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
    split; [| exact (conj W11 W12)].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|].
    split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|]. split; [exact W13|].
    split; [intros ch Hin Hq; left; exact (W14 ch Hin Hq)|].
    split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|]. split; [exact W19|]. split; [exact W20|].
    split; [exact W21|]. split; [exact W22|]. split; [exact W23|]. split; [exact W24|]. split; [intros m []| intros B []].
  - intros ((W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & _ & _) & B1 & B2).
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|].
    split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|]. split; [exact B1|]. split; [exact B2|]. split; [exact W13|].
    split; [intros ch Hin Hq; destruct (W14 ch Hin Hq) as [E|[]]; exact E|].
    split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|]. split; [exact W19|]. split; [exact W20|].
    split; [exact W21|]. split; [exact W22|]. split; [exact W23| exact W24].
Qed.

Lemma WFQ_region : forall st XC XB c, WFQ st XC XB -> 0 <= c < kNumClasses -> region_ok st c.
Proof. intros st XC XB c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WFQ_cache : forall st XC XB c, WFQ st XC XB -> 0 <= c < kNumClasses -> cache_ok st c.
Proof. intros st XC XB c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WFQ_chunk : forall st XC XB ch, WFQ st XC XB -> In ch (chunk_list st) -> chunk_ok st ch.
Proof. intros st XC XB ch W Hin. destruct W as (_ & _ & H & _). apply H, Hin. Qed.
Lemma WFQ_inj : forall st XC XB, WFQ st XC XB ->
  forall ch ch', In ch (chunk_list st) -> In ch' (chunk_list st) -> ch_user_beg ch = ch_user_beg ch' -> ch = ch'.
Proof. intros st XC XB W. destruct W as (_ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_carved : forall st XC XB, WFQ st XC XB -> List.NoDup (carved_addr_list st ++ XB).
Proof. intros st XC XB W. destruct W as (_ & H & _). exact H. Qed.
Lemma WFQ_tq : forall st XC XB, WFQ st XC XB -> qcache_ok st (as_tq st).
Proof. intros st XC XB W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_gq : forall st XC XB, WFQ st XC XB -> qcache_ok st (as_gq st).
Proof. intros st XC XB W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_batch : forall st XC XB b, WFQ st XC XB -> In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> batch_ok st b.
Proof.
  intros st XC XB b W Hin. apply in_app_iff in Hin as [Hin|Hin]; [apply (proj1 (WFQ_tq st XC XB W)) | apply (proj1 (WFQ_gq st XC XB W))]; exact Hin.
Qed.
Lemma WFQ_qnodup : forall st XC XB, WFQ st XC XB -> List.NoDup (flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st)) ++ XC).
Proof. intros st XC XB W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma WFQ_consts : forall st XC XB, WFQ st XC XB ->
  as_qmax st = kQuarantineMaxSize /\ as_qmin st = kQuarantineMinSize /\ as_qcache st = kMaxCacheSize.
Proof. intros st XC XB W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _). exact (conj H1 (conj H2 H3)). Qed.
Lemma WFQ_lens : forall st XC XB, WFQ st XC XB -> length (as_regions st) = 32%nat /\ length (as_cache st) = 32%nat.
Proof. intros st XC XB W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). exact (conj H1 H2). Qed.
Lemma WFQ_keys : forall st XC XB, WFQ st XC XB ->
  forall k x, PositiveMap.find k (as_chunks st) = Some x -> k = ckey (ch_user_beg x) /\ 0 < ch_user_beg x.
Proof. intros st XC XB W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_xc : forall st XC XB m, WFQ st XC XB -> In m XC -> xc_ok st m.
Proof. intros st XC XB m W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). apply H. Qed.
Lemma WFQ_xb : forall st XC XB B, WFQ st XC XB -> In B XB -> xb_ok st B.
Proof. intros st XC XB B W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). apply H. Qed.

Lemma WFQ_perm : forall st XC XC' XB XB', Permutation XC XC' -> Permutation XB XB' -> WFQ st XC XB -> WFQ st XC' XB'.
Proof.
  intros st XC XC' XB XB' PC PB W.
  destruct W as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
  split; [exact W1|]. split; [eapply Permutation_NoDup; [| exact W2]; apply Permutation_app_head; exact PB|].
  split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|].
  split; [eapply Permutation_NoDup; [| exact W11]; apply Permutation_app_head; exact PC|].
  split; [intros ch Hin Hq; destruct (W12 ch Hin Hq) as [E|E]; [left; exact E| right; eapply Permutation_in; [exact PC| exact E]]|].
  split; [exact W13|]. split; [exact W14|]. split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|].
  split; [exact W19|]. split; [exact W20|]. split; [exact W21|]. split; [exact W22|].
  split; [intros m Hm; apply W23; eapply Permutation_in; [apply Permutation_sym; exact PC| exact Hm]|].
  intros B HB. apply W24. eapply Permutation_in; [apply Permutation_sym; exact PB| exact HB].
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Definition ARmem (s : ast) (m : mem) : Prop :=
       inst_rep s m /\ flags_rep s m /\ thread_rep s m /\ sec_rep s m /\ ia_rep s m
    /\ (forall c, 0 <= c < kNumClasses -> region_rep s m c /\ pclass_rep s m c /\ region_shadow_rep s m c /\ region_junk_rep s m c)
    /\ (forall ch, In ch (chunk_list (a_st s)) -> chunk_rep m ch)
    /\ batches_rep m (qc_list (as_tq (a_st s))) /\ batches_rep m (qc_list (as_gq (a_st s))).

  Lemma AREP_split : forall s m, AREP s m <-> (placed_ok s /\ WF (a_st s)) /\ ARmem s m.
  Proof. intros s m. unfold AREP, ast_ok, ARmem. tauto. Qed.

  Definition AREPQ (s : ast) (XC XB : list Z) (m : mem) : Prop := placed_ok s /\ WFQ (a_st s) XC XB /\ ARmem s m.

  Lemma AREP_AREPQ : forall s m, AREP s m <-> AREPQ s [] [] m /\ qbounds (a_st s).
  Proof.
    intros s m. rewrite AREP_split. unfold AREPQ. rewrite (WF_WFQ (a_st s)). tauto.
  Qed.

  Lemma AREP_of_AREPQ : forall s m, AREPQ s [] [] m -> qbounds (a_st s) -> AREP s m.
  Proof. intros s m H B. exact (proj2 (AREP_AREPQ s m) (conj H B)). Qed.

  Lemma AREPQ_placed : forall s XC XB m, AREPQ s XC XB m -> placed_ok s.
  Proof. intros s XC XB m H. exact (proj1 H). Qed.
  Lemma AREPQ_WFQ : forall s XC XB m, AREPQ s XC XB m -> WFQ (a_st s) XC XB.
  Proof. intros s XC XB m H. exact (proj1 (proj2 H)). Qed.
  Lemma AREPQ_mem : forall s XC XB m, AREPQ s XC XB m -> ARmem s m.
  Proof. intros s XC XB m H. exact (proj2 (proj2 H)). Qed.
  Lemma AREPQ_perm : forall s XC XC' XB XB' m, Permutation XC XC' -> Permutation XB XB' -> AREPQ s XC XB m -> AREPQ s XC' XB' m.
  Proof. intros s XC XC' XB XB' m PC PB (P & W & M). split; [exact P|]. split; [exact (WFQ_perm _ _ _ _ _ PC PB W)| exact M]. Qed.

  Section FrameQ.
    Variable s : ast.
    Variables XC XB : list Z.
    Variables m m' : mem.
    Variable P : Z -> Prop.
    Hypothesis AG : agree_on P m m'.
    Hypothesis WM : wmono asegs m m'.
    Hypothesis W : WFQ (a_st s) XC XB.

    Ltac tr_cells H := eapply (rw_cells_transport_pt P m m' AG WM); [exact H|];
                       cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat].
    Ltac tr_junk H := eapply (junk_transport_pt P m m' AG WM); [exact H|].
    Ltac tr_u32 H := eapply (u32arr_transport_pt P m m' AG WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
    Ltac tr_u64 H := eapply (u64arr_transport_pt P m m' AG WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
    Ltac tr_poi H := eapply (poisoned_transport_pt P m m' AG WM); [exact H|].
    Ltac af C := intros ? ?; eapply C; eauto; unfold OI_MISMATCH, OT_UNWINDING, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX,
                 OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER, OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, CACHE_STATS, PCLASS_SIZE, REGIONINFO_SIZE,
                 kNumClasses, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; try lia.

    Lemma region_rep_frameQ : forall c, 0 <= c < kNumClasses ->
      (forall a, a_ri s <= a < a_ri s + kPageSize -> P a) ->
      (forall a, FA s c <= a < FA s c + rg_mapped_free_array (get_region (a_st s) c) -> P a) ->
      (forall a, RB s c + rg_allocated_user (get_region (a_st s) c) <= a < RB s c + rg_mapped_user (get_region (a_st s) c) -> P a) ->
      region_rep s m c -> region_rep s m' c.
    Proof.
      intros c Hc HP1 HP2 HP3 H. pose proof (WFQ_region _ _ _ c W Hc) as RO.
      destruct H as (R1 & J1 & R2 & J2 & U & J3 & J4). unfold region_rep.
      pose proof (ro_numfreed _ _ RO) as N1. pose proof (ro_fa_le _ _ RO) as N2. pose proof (ro_alloc_nonneg _ _ RO) as N3.
      pose proof (ro_alloc_le _ _ RO) as N4. unfold zlen in N1.
      split; [tr_cells R1; af HP1|].
      split; [tr_junk J1; af HP1|].
      split; [tr_cells R2; af HP1|].
      split; [tr_junk J2; af HP1|].
      split; [tr_u32 U; af HP2|].
      split; [tr_junk J3; af HP2|].
      tr_junk J4; af HP3.
    Qed.

    Lemma pclass_rep_frameQ : forall c, 0 <= c < kNumClasses ->
      (forall a, a_cache s + PCLASS_SIZE * c <= a < a_cache s + PCLASS_SIZE * c + PCLASS_SIZE -> P a) ->
      pclass_rep s m c -> pclass_rep s m' c.
    Proof.
      intros c Hc HP H. pose proof (WFQ_cache _ _ _ c W Hc) as CO.
      destruct H as (P1 & P2 & U & J). unfold pclass_rep.
      pose proof (co_count _ _ CO) as N1. unfold zlen in N1.
      assert (N2 : 0 <= pc_count (get_pc (a_st s) c) <= 16).
      { pose proof (co_bound _ _ CO) as B. pose proof (class_size_table_facts c Hc) as T.
        destruct (as_cache_inited (a_st s)); lia. }
      split; [tr_cells P1; af HP|].
      split; [tr_cells P2; af HP|].
      split; [tr_u32 U; af HP|].
      tr_junk J; af HP.
    Qed.

    Lemma sec_rep_frameQ :
      (forall a, a_pa s <= a < a_pa s + 8 * as_n_reserved (a_st s) -> P a) ->
      (forall h a, In h (as_sec (a_st s)) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> P a) ->
      sec_rep s m -> sec_rep s m'.
    Proof.
      intros HP1 HP2 (U & J & H). unfold sec_rep.
      destruct W as (_ & _ & _ & _ & Wn & _ & Wres & _).
      assert (N0 : 0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia).
      split; [tr_u64 U; unfold zlen in *; af HP1|].
      split; [tr_junk J; unfold zlen in *; af HP1|].
      intros i h Hi. destruct (H i h Hi) as [C1 J1]. pose proof (nth_error_In _ _ Hi) as IN.
      split; [tr_cells C1; af HP2| tr_junk J1; af HP2].
    Qed.

    Lemma region_shadow_rep_frameQ : forall c, 0 <= c < kNumClasses ->
      (forall cp a, In cp (rg_free_array (get_region (a_st s) c)) \/ In cp (pc_chunks (get_pc (a_st s) c)) ->
                    sh (compact_to_addr (a_st s) c cp) <= a < sh (compact_to_addr (a_st s) c cp) + class_size c / 8 -> P a) ->
      (forall a, sh (RB s c + rg_allocated_user (get_region (a_st s) c)) <= a
                 < sh (RB s c + rg_allocated_user (get_region (a_st s) c)) + (rg_mapped_user (get_region (a_st s) c) - rg_allocated_user (get_region (a_st s) c)) / 8 -> P a) ->
      (forall a, sh (FA s c) <= a < sh (FA s c) + rg_mapped_free_array (get_region (a_st s) c) / 8 -> P a) ->
      region_shadow_rep s m c -> region_shadow_rep s m' c.
    Proof.
      intros c Hc HP1 HP2 HP3 (H1 & H2 & H3 & H4). pose proof (WFQ_region _ _ _ c W Hc) as RO. pose proof (class_size_table_facts c Hc) as CS.
      pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO). pose proof (ro_fa_le _ _ RO). pose proof (ro_numfreed _ _ RO).
      unfold zlen in *. unfold region_shadow_rep.
      split; [| split; [| split]].
      - intros cp Hin. specialize (H1 cp Hin). tr_poi H1. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af (HP1 cp).
      - intros cp Hin. specialize (H2 cp Hin). tr_poi H2. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af (HP1 cp).
      - tr_poi H3. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af HP2.
      - tr_poi H4. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af HP3.
    Qed.

    Lemma chunk_rep_frameQ : forall ch, In ch (chunk_list (a_st s)) -> (forall a, achunk_range ch a -> P a) -> chunk_rep m ch -> chunk_rep m' ch.
    Proof.
      intros ch Hin HP H. pose proof (WFQ_chunk _ _ _ ch W Hin) as CO. unfold achunk_range in HP.
      destruct CO as (U1 & U2 & U3 & U4 & _).
      pose proof (rz_size_facts (ch_used ch)) as RZ. rewrite <- (eq_refl : rq_rz (compute_req (ch_used ch)) = rz_size (ch_used ch)) in RZ.
      rewrite <- U3 in RZ. destruct RZ as (RZ1 & RZ2 & _).
      destruct H as ((b1 & actx & HD & Hb1 & Hb1') & LC & ST & JR & PL & PR & PH). unfold chunk_rep.
      assert (NS : 0 <= nsh (ch_used ch) /\ 8 * nsh (ch_used ch) = round_up (ch_used ch) 8 /\ ch_used ch <= round_up (ch_used ch) 8 < ch_used ch + 8).
      { unfold nsh, round_up. Z.div_mod_to_equations. lia. }
      split.
      { exists b1, actx. split; [|split; [exact Hb1| exact Hb1']]. tr_cells HD. unfold kChunkHeaderSize. intros ? ?; eapply HP; left; lia. }
      split.
      { destruct LC as [LC|[LC1 LC2]]; [left; exact LC| right]. split; [tr_cells LC1; intros ? ?; eapply HP; left; lia| tr_junk LC2; intros ? ?; eapply HP; left; lia]. }
      split.
      { destruct (ch_state ch) eqn:E.
        - destruct ST as [ST1 ST2]. split; eapply wr_at_transport; eauto.
        - destruct ST as [ST1 ST2]. split; [tr_junk ST1; intros ? ?; eapply HP; do 2 right; left; split; [first [exact E | reflexivity]| lia]
                                            | tr_poi ST2; rewrite Z2Nat.id by lia; intros ? ?; eapply HP; do 5 right; left; split; [first [exact E | reflexivity]| lia]]. }
      split; [tr_junk JR; intros ? ?; eapply HP; right; left; lia|].
      split; [tr_poi PL; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); intros ? ?; eapply HP; do 3 right; left; lia|].
      split.
      { tr_poi PR. destruct (Z.le_gt_cases 0 ((ch_end ch - (ch_user_beg ch + round_up (ch_used ch) 8)) / 8)).
        - rewrite Z2Nat.id by lia. intros ? ?; eapply HP; do 4 right; left; lia.
        - rewrite (Z2Nat.nonpos _) by lia. intros a Ha. cbn in Ha. lia. }
      destruct (ch_primary ch) eqn:E; [exact I|]. tr_poi PH. intros ? ?; eapply HP. do 6 right. split; [reflexivity| lia].
    Qed.
  End FrameQ.

  Theorem AREPQ_frame_pt : forall s XC XB m m',
    AREPQ s XC XB m -> agree_on (afoot s) m m' -> wmono asegs m m' -> AREPQ s XC XB m'.
  Proof.
    intros s XC XB m m' H AG WM.
    destruct H as (PL & W & I & F & T & SC & IA & RC & CH & BT & BG).
    split; [exact PL|]. split; [exact W|].
    split; [apply (inst_rep_frame s m m' _ AG WM (af_inst s) I)|].
    split; [apply (flags_rep_frame s m m' _ AG WM (af_flags s) F)|].
    split; [apply (thread_rep_frame s m m' _ AG WM (af_thread s) T)|].
    split; [apply (sec_rep_frameQ s XC XB m m' _ AG WM W (af_ptrarr s) (fun h a Hh Ha => af_sechdr s a h Hh Ha) SC)|].
    split; [apply (ia_rep_frame s m m' _ AG WM); [intros a Ha; eapply af_flags; do 13 right; left; exact Ha| exact IA]|].
    split.
    { intros c Hc. destruct (RC c Hc) as (R1 & R2 & R3 & R4).
      split; [apply (region_rep_frameQ s XC XB m m' _ AG WM W c Hc (af_rinfo s) (fun a Ha => af_farray s a c Hc Ha) (fun a Ha => af_tail s a c Hc Ha) R1)|].
      split.
      { apply (pclass_rep_frameQ s XC XB m m' _ AG WM W c Hc); [| exact R2]. intros a Ha. apply af_thread. left.
        unfold a_cache, OT_CACHE, PCLASS_SIZE, OT_UNWINDING, kNumClasses in *. lia. }
      split; [apply (region_shadow_rep_frameQ s XC XB m m' _ AG WM W c Hc (fun cp a Hin Ha => af_sh_freech s a c cp Hc Hin Ha) (fun a Ha => af_sh_tail s a c Hc Ha) (fun a Ha => af_sh_farray s a c Hc Ha) R3)
            | apply (region_junk_rep_frame s m m' _ AG WM c Hc (fun cp a Hin Ha => af_freech s a c cp Hc Hin Ha) R4)]. }
    split.
    { intros ch Hin. apply (chunk_rep_frameQ s XC XB m m' _ AG WM W ch Hin); [| exact (CH ch Hin)].
      intros a Ha. destruct Ha as [Ha|[Ha|[[Q Ha]|[Ha|[Ha|[[Q Ha]|[NP Ha]]]]]]].
      - eapply af_chleft; eauto. - eapply af_chright; eauto. - eapply af_chquar; eauto. - eapply af_sh_chleft; eauto.
      - eapply af_sh_chright; eauto. - eapply af_sh_chquar; eauto. - eapply af_sh_sechdr; eauto. }
    assert (BOK : forall b, In b (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s))) ->
              0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)).
    { intros b Hb. pose proof (WFQ_batch _ _ _ b W Hb) as (B1 & B2 & _). unfold kBatchSize, kBatchCount in *. lia. }
    split.
    - eapply (batches_rep_transport (afoot s) m m'); [exact AG| exact WM| | | exact BT].
      + intros b a Hb Hr. destruct Hr as [Hr|Hr]; [eapply af_batch| eapply af_sh_batch]; eauto; apply in_app_iff; left; exact Hb.
      + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
    - eapply (batches_rep_transport (afoot s) m m'); [exact AG| exact WM| | | exact BG].
      + intros b a Hb Hr. destruct Hr as [Hr|Hr]; [eapply af_batch| eapply af_sh_batch]; eauto; apply in_app_iff; right; exact Hb.
      + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
  Qed.

  Theorem AREPQ_frame : forall s XC XB W m m',
    AREPQ s XC XB m -> munch W m m' -> wmono asegs m m' -> awin_ok s W -> AREPQ s XC XB m'.
  Proof. intros s XC XB W m m' H MU WM AW. eapply AREPQ_frame_pt; [exact H| eapply awin_agree; eauto| exact WM]. Qed.

End HCW.

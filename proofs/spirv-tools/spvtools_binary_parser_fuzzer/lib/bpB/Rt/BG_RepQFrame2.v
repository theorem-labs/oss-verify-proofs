(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BecLazy2 BG_RepQ.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition afootX {HCEIL : HeapCeil} (s : ast) (a : Z) : Prop :=
  afoot s a \/ exists ch, In ch (chunk_list (a_st s)) /\ ch_state ch = CAllocated
                /\ (ch_user_beg ch <= a < ch_user_beg ch + ch_used ch \/ sh (ch_user_beg ch) <= a < sh (ch_user_beg ch) + nsh (ch_used ch)).
Definition achunk_rangeX {HCEIL : HeapCeil} (ch : chunk) (a : Z) : Prop :=
  achunk_range ch a \/ (ch_state ch = CAllocated /\ (ch_user_beg ch <= a < ch_user_beg ch + ch_used ch \/ sh (ch_user_beg ch) <= a < sh (ch_user_beg ch) + nsh (ch_used ch))).

Section HCW.
  Context {HCEIL : HeapCeil}.

Section TransportAg.
  Variable P : Z -> Prop.
  Variables m m' : mem.
  Hypothesis AG : agree_on P m m'.

  Lemma wview_ag : forall a, P a -> 0 <= a < 2^64 -> wview asegs m' (wa a) = wview asegs m (wa a).
  Proof. intros a Ha Hr. apply wview_pointwise. exact (AG a Ha Hr). Qed.
  Lemma wr_at_transport_ag : forall A n, wr_at asegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at asegs m' A n.
  Proof.
    intros A n (Ha & Hn & H) HR. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    rewrite (wview_ag (A + i)); [exact (H i Hi)| apply HR; lia| lia].
  Qed.
  Lemma bytes_at_transport_ag : forall A bs,
    bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
  Proof.
    intros A bs (Ha & Hl & H) HR. split; [lia|]. split; [lia|].
    intros i Hi. unfold mrd. rewrite AG; [apply H; exact Hi| apply HR; lia| lia].
  Qed.
  Lemma stk_transport_ag : forall lo hi, stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
  Proof.
    intros lo hi (H1 & H2 & H) HR. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (H a Ha) as [Hw (b & Hb)]. split; [rewrite (wview_ag a); [exact Hw| apply HR; lia| lia]|]. exists b.
    unfold mrd in *. rewrite AG; [exact Hb| apply HR; lia| lia].
  Qed.
  Lemma junk_transport_ag : forall lo n, junk m lo n -> (forall a, lo <= a < lo + n -> P a) -> junk m' lo n.
  Proof. intros lo n J HR Hn. eapply stk_transport_ag; [apply J; exact Hn| exact HR]. Qed.
  Lemma rw_cells_transport_ag : forall A cs,
    rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] HR. split; [split; [exact Hwf|]| eapply wr_at_transport_ag; [exact Hw| exact HR]].
    eapply bytes_at_transport_ag; [exact Hb|]. rewrite cells_bytes_length by assumption. exact HR.
  Qed.
  Lemma u32arr_transport_ag : forall A ws,
    u32arr asegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HR. split.
    - eapply bytes_at_transport_ag; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HR. lia.
    - eapply wr_at_transport_ag; [exact Hw|]. intros a Ha. apply HR. lia.
  Qed.
  Lemma u8arr_transport_ag : forall A bs,
    u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr asegs m' A bs.
  Proof.
    intros A bs [Hb Hw] HR. split; [eapply bytes_at_transport_ag; [exact Hb| exact HR]| eapply wr_at_transport_ag; [exact Hw| exact HR]].
  Qed.
  Lemma u64arr_transport_ag : forall A ws,
    u64arr asegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HR. split.
    - eapply bytes_at_transport_ag; [exact Hb|]. rewrite u64s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HR. lia.
    - eapply wr_at_transport_ag; [exact Hw|]. intros a Ha. apply HR. lia.
  Qed.
  Lemma SHAD_transport_ag : forall A sbs,
    SHAD m A sbs -> (forall a, sh A <= a < sh A + Z.of_nat (length sbs) -> P a) -> SHAD m' A sbs.
  Proof.
    intros A sbs (A0 & HA & [Hb Hw]) HR. split; [exact A0|]. split; [exact HA|].
    split; [eapply bytes_at_transport_ag; eauto| eapply wr_at_transport_ag; eauto].
  Qed.
  Lemma poisoned_transport_ag : forall A k v,
    poisoned m A k v -> (forall a, sh A <= a < sh A + Z.of_nat k -> P a) -> poisoned m' A k v.
  Proof.
    intros A k v H HR. eapply SHAD_transport_ag; [exact H|]. unfold poison_bytes. rewrite repeat_length. exact HR.
  Qed.
End TransportAg.

Lemma batches_rep_transport_ag : forall P m m' l,
  agree_on P m m' ->
  (forall b a, In b l -> (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
  (forall b, In b l -> 0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)) ->
  batches_rep m l -> batches_rep m' l.
Proof.
  intros P m m' l AG HP HC. induction l as [|b l IH]; [exact (fun x => x)|].
  cbn [batches_rep hd map]. intros (HB & HR). split; [| apply IH; [intros; eapply HP; [right; eassumption| eassumption] | intros; apply HC; right; assumption | exact HR]].
  destruct HB as (B1 & B2 & B3 & B4). pose proof (HC b (or_introl eq_refl)) as (C1 & C2 & C3).
  unfold zlen in C3. unfold kBatchSize in *.
  split; [|split; [|split]].
  - eapply (rw_cells_transport_ag P m m' AG); [exact B1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. eapply HP; [left; reflexivity| left; lia].
  - eapply (u64arr_transport_ag P m m' AG); [exact B2|]. unfold wlist. rewrite length_map. intros a Ha. eapply HP; [left; reflexivity| left; lia].
  - eapply (junk_transport_ag P m m' AG); [exact B3|]. intros a Ha. unfold kBatchSize in Ha. eapply HP; [left; reflexivity| left; lia].
  - eapply (poisoned_transport_ag P m m' AG); [exact B4|]. intros a Ha. unfold kBatchSize in Ha. eapply HP; [left; reflexivity| ]. right.
    change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. lia.
Qed.

Section FrameAg.
  Variable s : ast.
  Variables m m' : mem.
  Variable P : Z -> Prop.
  Hypothesis AG : agree_on P m m'.

  Ltac tr_cells H := eapply (rw_cells_transport_ag P m m' AG); [exact H|];
                     cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat].
  Ltac tr_junk H := eapply (junk_transport_ag P m m' AG); [exact H|].
  Ltac tr_u32 H := eapply (u32arr_transport_ag P m m' AG); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
  Ltac tr_u64 H := eapply (u64arr_transport_ag P m m' AG); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
  Ltac tr_poi H := eapply (poisoned_transport_ag P m m' AG); [exact H|].
  Ltac af C := intros ? ?; eapply C; eauto; unfold OI_MISMATCH, OT_UNWINDING, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX,
               OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER, OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, CACHE_STATS, PCLASS_SIZE, REGIONINFO_SIZE,
               kNumClasses, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; try lia.

  Ltac pick n := lazymatch n with O => left | S ?k => right; pick k end.

  Definition aflags_range (a : Z) : Prop :=
    (AFLAGS + 44 <= a < AFLAGS + 89) \/ (ACFLAGS + 34 <= a < ACFLAGS + 261) \/ (ASHBASE_CELL <= a < ASHBASE_CELL + 8)
    \/ (AHIGHMEMEND <= a < AHIGHMEMEND + 24) \/ (ACANPOISON <= a < ACANPOISON + 1) \/ (AINITED <= a < AINITED + 1)
    \/ (ACTXSIZE <= a < ACTXSIZE + 4) \/ (ATSDINIT <= a < ATSDINIT + 8) \/ (AALLOCFLAGS <= a < AALLOCFLAGS + 3)
    \/ (AIAINIT <= a < AIAINIT + 4) \/ (AHOOKS <= a < AHOOKS + 80) \/ (ADYING <= a < ADYING + 4)
    \/ (AREALMEMSET <= a < AREALMEMSET + 8) \/ (AIAINST <= a < AIAINST + 0x81030)
    \/ (AGOT_LO <= a < AGOT_LO + 120) \/ (APAGESZ <= a < APAGESZ + 8) \/ (ASECNAME <= a < ASECNAME + 8)
    \/ (APRIMNAME <= a < APRIMNAME + 8) \/ (ATLSSLOT <= a < ATLSSLOT + 8) \/ (ATSD <= a < ATSD + 8)
    \/ (ALSANDIS <= a < ALSANDIS + 4) \/ (AGOT2 <= a < AGOT2 + 8).

  Ltac trf HP H n := tr_cells H; intros ? ?; eapply HP; unfold aflags_range; pick n;
                  unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS,
                         ADYING, AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2 in *; lia.
  Lemma flags_rep_frame_ag : (forall a, aflags_range a -> P a) -> flags_rep s m -> flags_rep s m'.
  Proof.
    intros HP H. destruct H as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    unfold flags_rep.
    split; [trf HP F1 0%nat|]. split; [trf HP F2 0%nat|]. split; [trf HP F3 0%nat|]. split; [trf HP F4 0%nat|].
    split; [trf HP F5 1%nat|]. split; [trf HP F6 1%nat|]. split; [trf HP F7 1%nat|]. split; [trf HP F8 1%nat|].
    split; [trf HP F9 2%nat|]. split; [trf HP F10 3%nat|]. split; [trf HP F11 4%nat|]. split; [trf HP F12 5%nat|]. split; [trf HP F13 6%nat|]. split; [trf HP F14 7%nat|].
    split; [trf HP F15 8%nat|]. split; [trf HP F16 9%nat|]. split; [trf HP F17 10%nat|]. split; [trf HP F18 11%nat|]. split; [trf HP F19 12%nat|].
    split; [eapply (rw_cells_transport_ag P m m' AG); [exact F20|]; change (Z.of_nat _) with 120;
           intros ? ?; eapply HP; unfold aflags_range; pick 14%nat; unfold AGOT_LO in *; lia|].
    split; [trf HP F21 15%nat|]. split; [trf HP F22 16%nat|].
    split; [tr_cells F23; intros ? ?; eapply HP; unfold aflags_range; pick 17%nat; unfold APRIMNAME in *; lia|].
    split; [tr_cells F24; intros ? ?; eapply HP; unfold aflags_range; pick 18%nat; unfold ATLSSLOT in *; lia|].
    split; [tr_cells F25; intros ? ?; eapply HP; unfold aflags_range; pick 19%nat; unfold ATSD in *; lia|].
    split; [tr_cells F26; intros ? ?; eapply HP; unfold aflags_range; pick 20%nat; unfold ALSANDIS in *; lia|].
    tr_cells F27; intros ? ?; eapply HP; unfold aflags_range; do 21 right; unfold AGOT2 in *; lia.
  Qed.

  Hypothesis OK : ast_ok s.
  Let W : WF (a_st s).
  Proof. exact (proj2 OK). Qed.

  Definition athread_range (a : Z) : Prop :=
    (a_thr s <= a < a_thr s + OT_UNWINDING + 1) \/ (a_ctx s + 8 <= a < a_ctx s + 12) \/ (a_ctx s + 152 <= a < a_ctx s + 160).

  Lemma ia_rep_frame_ag : (forall a, AIAINST <= a < AIAINST + 0x81030 -> P a) -> ia_rep s m -> ia_rep s m'.
  Proof.
    intros HP. unfold ia_rep. destruct (as_internal_init (a_st s)).
    - intros (C1 & C2 & C3).
      split; [eapply (u8arr_transport_ag P m m' AG); [exact C1|]; rewrite repeat_length, Z2Nat.id by lia;
             intros ? ?; eapply HP; unfold AIAINST in *; lia|].
      split; [tr_cells C2; intros ? ?; eapply HP; unfold AIAINST in *; lia|].
      eapply (u8arr_transport_ag P m m' AG); [exact C3|]. rewrite repeat_length, Z2Nat.id by lia.
      intros ? ?; eapply HP; unfold AIAINST in *; lia.
    - intros C. eapply (u8arr_transport_ag P m m' AG); [exact C|]. rewrite repeat_length, Z2Nat.id by lia.
      intros ? ?; eapply HP; lia.
  Qed.

  Lemma region_junk_rep_frame_ag : forall c, 0 <= c < kNumClasses ->
    (forall cp a, In cp (rg_free_array (get_region (a_st s) c)) \/ In cp (pc_chunks (get_pc (a_st s) c)) ->
                  compact_to_addr (a_st s) c cp <= a < compact_to_addr (a_st s) c cp + class_size c -> P a) ->
    region_junk_rep s m c -> region_junk_rep s m' c.
  Proof.
    intros c Hc HP (H1 & H2). unfold region_junk_rep. split.
    - intros cp Hin. specialize (H1 cp Hin). tr_junk H1. af (HP cp).
    - intros cp Hin. specialize (H2 cp Hin). tr_junk H2. af (HP cp).
  Qed.

End FrameAg.

Section FrameQAg.
    Variable s : ast.
    Variables XC XB : list Z.
    Variables m m' : mem.
    Variable P : Z -> Prop.
    Hypothesis AG : agree_on P m m'.
    Hypothesis W : WFQ (a_st s) XC XB.

    Ltac tr_cells H := eapply (rw_cells_transport_ag P m m' AG); [exact H|];
                       cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat].
    Ltac tr_junk H := eapply (junk_transport_ag P m m' AG); [exact H|].
    Ltac tr_u32 H := eapply (u32arr_transport_ag P m m' AG); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
    Ltac tr_u64 H := eapply (u64arr_transport_ag P m m' AG); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
    Ltac tr_poi H := eapply (poisoned_transport_ag P m m' AG); [exact H|].
    Ltac af C := intros ? ?; eapply C; eauto; unfold OI_MISMATCH, OT_UNWINDING, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX,
                 OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER, OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, CACHE_STATS, PCLASS_SIZE, REGIONINFO_SIZE,
                 kNumClasses, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; try lia.

    Lemma region_rep_frameQ_ag : forall c, 0 <= c < kNumClasses ->
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

    Lemma pclass_rep_frameQ_ag : forall c, 0 <= c < kNumClasses ->
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

    Lemma region_shadow_rep_frameQ_ag : forall c, 0 <= c < kNumClasses ->
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

    Lemma chunk_rep_frameQ_ag : forall ch, In ch (chunk_list (a_st s)) -> (forall a, achunk_rangeX ch a -> P a) -> chunk_rep m ch -> chunk_rep m' ch.
    Proof.
      intros ch Hin HPX H. pose proof (WFQ_chunk _ _ _ ch W Hin) as CO.
      assert (HP : forall a, achunk_range ch a -> P a) by (intros a Ha; apply HPX; left; exact Ha). unfold achunk_range in HP.
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
        - destruct ST as [ST1 ST2]. split; [eapply (wr_at_transport_ag P m m' AG); [exact ST1|]| eapply (wr_at_transport_ag P m m' AG); [exact ST2|]];
            intros a Ha; apply HPX; right; (split; [exact E|]); [left| right]; exact Ha.
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

End FrameQAg.

End HCW.

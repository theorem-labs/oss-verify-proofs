(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepFacts2 BsDepotInv BW_MallocBase BW_IAInit BllocWalkKit BG_MallocModel BG_WFHit BG_Malloc BG_Malloc2 BG_FreeModel BG_WFFree BG_Free1 BG_FreeFacts BG_RepQ.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition lb_remove (U : Z) (LB : list (Z * Z)) : list (Z * Z) := List.filter (fun b => negb (fst b =? U)) LB.

Lemma lb_remove_In : forall U LB b, In b (lb_remove U LB) <-> In b LB /\ fst b <> U.
Proof.
  intros U LB b. unfold lb_remove. rewrite filter_In, Bool.negb_true_iff, Z.eqb_neq. tauto.
Qed.
Lemma lb_remove_nodup : forall U LB, List.NoDup LB -> List.NoDup (lb_remove U LB).
Proof. intros U LB ND. unfold lb_remove. apply NoDup_filter. exact ND. Qed.

Lemma poisoned_of_u8arr : forall m A k v, 0 <= A -> A mod 8 = 0 -> u8arr asegs m (sh A) (repeat (b8 v) k) -> poisoned m A k v.
Proof. intros m A k v H0 H8 U8. split; [exact H0|]. split; [exact H8|]. exact U8. Qed.

Lemma junk_of_rw_cells : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> junk m A n.
Proof. intros m A cs n RC E POS. rewrite <- E. exact (stk_of_rw_cells asegs _ _ _ RC). Qed.

Section FreePost.
  Variables (s : ast) (ch : chunk) (m m' : mem) (P : Z -> Prop).
  Variables (tq' : qcache) (cache' : list pclass) (L' S' : list (word * word)) (AL' : Z).
  Variables (b1 actx idv : Z) (bs : list byte).
  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.

  Definition free_st' : astate :=
    mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) cache' (as_n_reserved st) (as_sec st)
            (PositiveMap.add (ckey U) (qch ch) (as_chunks st)) tq' (as_gq st) true (as_maps st) (as_shadow st) (as_env st)
            (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
  Let st' := free_st'.
  Definition free_s' : ast := mkAst free_st' (a_thr s) (a_ctx s) (a_fsb s) L' S' (a_Zr s) AL' (a_top s) (a_bot s).
  Let s' := free_s'.

  Hypothesis R : AREP s m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).
  Variables (XC XB : list Z).
  Hypothesis WF' : WFQ st' XC XB.
  Hypothesis AG : agree_on P m m'.
  Hypothesis WM : wmono asegs m m'.

  Hypothesis B1 : 0 <= b1 < 256 /\ b1 mod 128 = 17.
  Hypothesis HDR' : rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)].
  Hypothesis UW' : rw_cells asegs m' U [C8 (wz idv)].
  Hypothesis SHF' : u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
  Hypothesis FLG' : rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)].
  Hypothesis IA' : ia_after m'.
  Hypothesis TST' : stk asegs m' (TH + 2800) (TH + 3168).
  Hypothesis UNW' : rw_cells asegs m' (TH + 3168) [C1 (b8 0)].
  Hypothesis CST' : junk m' (TH + 2768) 32.
  Hypothesis TQ' : rw_cells asegs m' (TH + OT_TQ)
      [C8 (wz (zlen (qc_list tq'))); C8 (wz (hd 0 (map qb_addr (qc_list tq')))); C8 (wz (last (map qb_addr (qc_list tq')) 0)); C8 (wz (qc_bytes tq'))].

  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].

  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Lemma free_okQ : placed_ok s' /\ WFQ (a_st s') XC XB. Proof. split; [exact PL| exact WF']. Qed.
  Let OK' := free_okQ.

  Lemma free_cl : forall y, In y (chunk_list st') <-> y = qch ch \/ (In y (chunk_list st) /\ ch_user_beg y <> U).
  Proof. intros y. exact (free_chunks_in st ch WFs CHIN y). Qed.

  Lemma free_old_in : forall y, In y (chunk_list st) -> y <> ch -> In y (chunk_list st').
  Proof.
    intros y Hy NE. apply free_cl. right. split; [exact Hy|]. intros E. apply NE.
    destruct WFs as (_ & _ & _ & INJ & _). exact (INJ y ch Hy CHIN E).
  Qed.

  Let PURE := free_pure s m ch R CHIN UHI.
  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ 7241728 <= ch_lo ch /\ ch_end ch <= aceil
            /\ ch_lo ch mod 8 = 0 /\ ch_end ch mod 8 = 0 /\ ch_alloc_beg ch + ch_rz ch = U /\ 16 <= ch_rz ch /\ ch_lo ch <= ch_alloc_beg ch.
  Proof.
    pose proof (record_ext s OK ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    pose proof (record_band s OK ch CHIN) as RB. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RB. unfold AHI_LO in UHI.
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 RB UHI. subst U size. pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; lia)) as [UE _]. unfold AHI_LO, AIMG_TOP in *. repeat split; try assumption; lia.
  Qed.

  Let BND : 4096 <= TH /\ TH + 4096 <= aceil /\ 7241728 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 7241728 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 7241744 <= U /\ U + round_up size 8 <= aceil /\ 1 <= size /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size
            /\ 2148356096 <= sh U /\ sh U + nsh size <= 0x10007fff8000 /\ U mod 16 = 0 /\ (sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U) /\ (U + round_up size 8 <= 2147446784 \/ 17594333495296 <= U - 16) /\ (ch_end ch <= 2147446784 \/ 17594333495296 <= ch_lo ch).
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & _).
    pose proof PL as (_ & _ & _ & P1 & P2 & P3 & _). apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia].
    pose proof (record_band s OK ch CHIN) as RBB. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RBB.
    clear - RBB Z1 Z2 Z3 Z4 Z5 Z6 Y1 Y2 Y4 Y5 X1 X2 P2 P3.
    subst U size TH CTX sb. unfold AHI_LO, AIMG_TOP, kSpaceSize, kPageSize, kPtrArrayReserve in *.
    assert (SH : 2148356096 <= sh (ch_user_beg ch) /\ sh (ch_user_beg ch) + nsh (ch_used ch) <= 0x10007fff8000
                 /\ (sh (ch_user_beg ch) + nsh (ch_used ch) <= ch_user_beg ch - 16 \/ ch_user_beg ch + round_up (ch_used ch) 8 <= sh (ch_user_beg ch))
                 /\ (ch_user_beg ch + round_up (ch_used ch) 8 <= 2147446784 \/ 17594333495296 <= ch_user_beg ch - 16)).
    { acb. clear - Z2 Z3 Z6 Z1 ACEILB. destruct Z2 as (ZA & _ & ZB). unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in ZA, ZB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    repeat match goal with |- _ /\ _ => split end; try lia.
  Qed.

  Ltac trc H Z K := eapply (rw_cells_transport_pt P m m' AG WM); [exact H|];
                    cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length repeat map];
                    let Ha := fresh in intros ? Ha; apply Z; clear - Ha K; lia.
  Ltac trj H Z K := eapply (junk_transport_pt P m m' AG WM); [exact H|]; let Ha := fresh in intros ? Ha; apply Z; clear - Ha K; lia.

  Lemma inst_after : (forall a, AINST <= a < AINST + OI_MISMATCH + 4 -> P a) -> inst_rep s' m'.
  Proof.
    intros ZI. pose proof R as RR; destruct RR as (_ & INST & _). apply (inst_rep_frame s' m m' P AG WM ZI). exact INST.
  Qed.

  Ltac pick n := lazymatch n with O => try left | S ?k => right; pick k end.
  Lemma flags_after :
    (forall a, aflags_range a -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> P a) -> flags_rep s' m'.
  Proof.
    intros ZF. pose proof R as RR; destruct RR as (_ & _ & FL & _).
    destruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    unfold flags_rep. change (a_ctx s') with (a_ctx s). change (as_internal_init (a_st s')) with true.
    Ltac trf ZF H n := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
                    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length repeat map];
                    let Ha := fresh in intros ? Ha; eapply ZF; [ unfold aflags_range; pick n | |]; clear - Ha;
                    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS,
                           ADYING, AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2 in Ha |- *; lia.
    split; [trf ZF F1 0%nat|]. split; [trf ZF F2 0%nat|]. split; [trf ZF F3 0%nat|]. split; [trf ZF F4 0%nat|].
    split; [trf ZF F5 1%nat|]. split; [trf ZF F6 1%nat|]. split; [trf ZF F7 1%nat|]. split; [trf ZF F8 1%nat|].
    split; [trf ZF F9 2%nat|]. split; [trf ZF F10 3%nat|]. split; [trf ZF F11 4%nat|]. split; [trf ZF F12 5%nat|]. split; [trf ZF F13 6%nat|].
    split; [trf ZF F14 7%nat|]. split; [trf ZF F15 8%nat|].
    split. {   exact FLG'. }
    split; [trf ZF F17 10%nat|]. split; [trf ZF F18 11%nat|]. split; [trf ZF F19 12%nat|].
    split. { eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F20|]. change (Z.of_nat _) with 120. intros a0 Ha0.
             eapply ZF; [unfold aflags_range; pick 14%nat| |]; clear - Ha0; unfold AGOT_LO, AIAINIT, AIAINST in Ha0 |- *; lia. }
    split; [trf ZF F21 15%nat|]. split; [trf ZF F22 16%nat|]. split; [trf ZF F23 17%nat|].
    split; [trf ZF F24 18%nat|]. split; [trf ZF F25 19%nat|]. split; [trf ZF F26 20%nat|]. trf ZF F27 21%nat.
  Qed.

  Lemma sec_after :
    (forall a, a_pa s <= a < a_pa s + kPtrArrayReserve -> P a) ->
    (forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> P a) -> sec_rep s' m'.
  Proof.
    intros ZPA ZSEC. pose proof R as RR; destruct RR as (_ & _ & _ & _ & SEC0 & _).
    apply (sec_rep_frameQ s' XC XB m m' P AG WM WF'); [| exact ZSEC| exact SEC0].
    intros a Ha. apply ZPA. change (a_pa s') with (a_pa s) in Ha. change (as_n_reserved (a_st s')) with (as_n_reserved st) in Ha.
    destruct WFs as (_ & _ & _ & _ & _ & _ & Wn & Wr & _). clear - Ha Wn Wr. unfold kChunksBlockCount, kPtrArrayReserve in Ha, Wr |- *.
    assert (0 <= zlen (as_sec st)) by (unfold zlen; lia). lia.
  Qed.

  Lemma thread_after :
    (forall a, TH <= a < TH + OT_TQ -> P a) -> (forall a, TH + OT_TQ + 32 <= a < TH + OT_CACHE -> P a) ->
    (forall a, CTX + 8 <= a < CTX + 12 -> P a) -> (forall a, CTX + 152 <= a < CTX + 160 -> P a) -> thread_rep s' m'.
  Proof.
    intros ZT1 ZT2 ZC1 ZC2. pose proof BND as B. pose proof R as RR; destruct RR as (_ & _ & _ & THR & _).
    destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_ctx s') with CTX. change (a_thr s') with TH. change (a_top s') with (a_top s). change (a_bot s') with (a_bot s).
    change (a_cache s') with (a_cache s). change (as_tq (a_st s')) with tq'.
    fold TH CTX in T1, T2, T2b, T2c, T2d, T3, T4, J1, J2, J3, T5. unfold a_cache, OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS in *.
    split; [trc T1 ZT1 AG|]. split; [trc T2 ZC1 AG|]. split; [trc T2b ZC2 AG|]. split; [trc T2c ZT1 AG|].
    split; [trc T2d ZT1 AG|]. split; [trc T3 ZT1 AG|]. split; [exact TQ'|].
    split; [trj J1 ZT2 AG|].
    split; [fold TH; replace (TH + 208 + 2560) with (TH + 2768) by (clear - AG; lia); exact CST'|].
    split; [intros _; replace (TH + 2800 + (3168 - 2800)) with (TH + 3168) by (clear - AG; lia); exact TST'| exact UNW'].
  Qed.

  Lemma region_after : forall c0, 0 <= c0 < kNumClasses ->
    (forall a, a_ri s <= a < a_ri s + kPageSize -> P a) ->
    (forall a, FA s c0 <= a < FA s c0 + rg_mapped_free_array (get_region st c0) -> P a) ->
    (forall a, RB s c0 + rg_allocated_user (get_region st c0) <= a < RB s c0 + rg_mapped_user (get_region st c0) -> P a) ->
    region_rep s' m' c0.
  Proof.
    intros c0 Hc0 Z1 Z2 Z3. pose proof R as RR; destruct RR as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL c0 Hc0) as (RG & _).
    exact (region_rep_frameQ s' XC XB m m' P AG WM WF' c0 Hc0 Z1 Z2 Z3 RG).
  Qed.

  Lemma pclass_after : forall c0, 0 <= c0 < kNumClasses -> get_pc st' c0 = get_pc st c0 ->
    (forall a, a_cache s + PCLASS_SIZE * c0 <= a < a_cache s + PCLASS_SIZE * c0 + PCLASS_SIZE -> P a) -> pclass_rep s' m' c0.
  Proof.
    intros c0 Hc0 E ZP. pose proof R as RR; destruct RR as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL c0 Hc0) as (_ & PC & _).
    unfold pclass_rep. change (a_st s') with st'. rewrite E. change (as_cache_inited st') with (as_cache_inited st). change (a_cache s') with (a_cache s).
    exact (pclass_rep_frame s m m' P AG WM OK c0 Hc0 ZP PC).
  Qed.
  Lemma region_shadow_after : forall c0, 0 <= c0 < kNumClasses ->
    (forall cp, In cp (pc_chunks (get_pc st' c0)) -> In cp (pc_chunks (get_pc st c0))) ->
    (forall cp a, In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st' c0)) ->
                  sh (compact_to_addr st c0 cp) <= a < sh (compact_to_addr st c0 cp) + class_size c0 / 8 -> P a) ->
    (forall a, sh (RB s c0 + rg_allocated_user (get_region st c0)) <= a
               < sh (RB s c0 + rg_allocated_user (get_region st c0)) + (rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8 -> P a) ->
    (forall a, sh (FA s c0) <= a < sh (FA s c0) + rg_mapped_free_array (get_region st c0) / 8 -> P a) ->
    region_shadow_rep s' m' c0.
  Proof.
    intros c0 Hc0 SUB Z1 Z2 Z3. pose proof R as RR; destruct RR as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL c0 Hc0) as (_ & _ & RSH & _).
    apply (region_shadow_rep_frameQ s' XC XB m m' P AG WM WF' c0 Hc0 Z1 Z2 Z3).
    unfold region_shadow_rep in RSH |- *. change (a_st s') with st'. change (get_region st' c0) with (get_region st c0).
    replace (compact_to_addr st' c0) with (compact_to_addr st c0) by reflexivity. change (RB s' c0) with (RB s c0). change (FA s' c0) with (FA s c0).
    destruct RSH as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [| split; [exact H3| exact H4]].
    intros cp Hin. apply H2. apply SUB. exact Hin.
  Qed.
  Lemma region_junk_after : forall c0, 0 <= c0 < kNumClasses ->
    (forall cp, In cp (pc_chunks (get_pc st' c0)) -> In cp (pc_chunks (get_pc st c0))) ->
    (forall cp a, In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st' c0)) ->
                  compact_to_addr st c0 cp <= a < compact_to_addr st c0 cp + class_size c0 -> P a) ->
    region_junk_rep s' m' c0.
  Proof.
    intros c0 Hc0 SUB Z1. pose proof R as RR; destruct RR as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL c0 Hc0) as (_ & _ & _ & RJ).
    apply (region_junk_rep_frame s' m m' P AG WM c0 Hc0 Z1).
    unfold region_junk_rep in RJ |- *. change (a_st s') with st'. change (get_region st' c0) with (get_region st c0).
    replace (compact_to_addr st' c0) with (compact_to_addr st c0) by reflexivity.
    destruct RJ as [H1 H2]. split; [exact H1|]. intros cp Hin. apply H2. apply SUB. exact Hin.
  Qed.

  Lemma new_chunk_rep :
    (forall a, ch_lo ch <= a < ch_end ch -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> P a) ->
    (forall a, sh (ch_lo ch) <= a < sh (ch_end ch) -> ~ (sh U <= a < sh U + nsh size) -> P a) ->
    chunk_rep m' (qch ch).
  Proof.
    intros ZA ZS. pose proof BND as B. pose proof EXT as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
    pose proof R as RR; destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _). pose proof (CHR ch CHIN) as ((b1o & actxo & HD & _) & LC & STI & JR & PLf & PR & PH).
    rewrite ALLOC in STI. destruct STI as [WRU WRS]. fold U in HD, LC, WRU, WRS, JR, PLf, PR, PH. fold size in HD, WRU, WRS, JR, PR.
    assert (SHL : sh (ch_lo ch) <= sh (ch_alloc_beg ch) /\ sh (ch_alloc_beg ch) + ch_rz ch / 8 <= sh U
                  /\ sh U + nsh size = sh (U + round_up size 8) /\ sh (U + round_up size 8) + (ch_end ch - (U + round_up size 8)) / 8 <= sh (ch_end ch)).
    { pose proof (chunk_align s OK ch CHIN) as (A1 & A2 & A3 & _). fold U in A3.
      clear - B E1 E2 E6 E7 E8 E9 E10 A1 A2 A3. unfold sh. repeat split; Z.div_mod_to_equations; lia. }
    unfold chunk_rep. cbn [ch_state ch_user_beg ch_used ch_alloc_beg ch_rz ch_class qch]. fold U size.
    replace (ch_end (qch ch)) with (ch_end ch) by reflexivity. replace (ch_primary (qch ch)) with (ch_primary ch) by reflexivity.
    split.
    { exists b1, actx. split; [| exact B1]. unfold kChunkHeaderSize. replace (U - 16) with (U + -16) by (clear - AG; lia). exact HDR'. }
    split.
    { destruct (Z.eq_dec (ch_rz ch) 16) as [E16|N16]; [left; exact E16| right].
      destruct LC as [LC|[LC1 LC2]]; [exfalso; exact (N16 LC)|]. unfold kChunkHeaderSize in *.
      pose proof (chunk_align s OK ch CHIN) as (_ & RZ16 & _).
      assert (RZ32 : 32 <= ch_rz ch) by (clear - N16 RZ16 E9; Z.div_mod_to_equations; lia).
      pose proof (conj B (conj E1 (conj E3 (conj E8 (conj E10 RZ32))))) as K.
      split; [trc LC1 ZA K| trj LC2 ZA K]. }
    split.
    { split.
      -
        intros POS.
        destruct (Z.le_gt_cases size 8) as [LE|GT].
        + pose proof (stk_of_rw_cells asegs _ _ _ UW') as SK. cbn [cells_size csize Nat.add] in SK.
          destruct (stk_split asegs _ _ (U + size) _ SK ltac:(clear - LE POS; lia)) as [SK1 _]. exact SK1.
        + pose proof (stk_of_rw_cells asegs _ _ _ UW') as SK. cbn [cells_size csize Nat.add] in SK.
          apply (rw_cells_CB_split asegs _ _ _ 8%nat) in BLK; [| clear - GT; lia]. destruct BLK as [_ BLK2].
          eapply (rw_cells_transport_pt P m m' AG WM) in BLK2.
          2:{ cbn [cells_size csize Nat.add]. intros a Ha. apply ZA; clear - Ha GT B E1 E2; lia. }
          pose proof (stk_of_rw_cells asegs _ _ _ BLK2) as SK2. cbn [cells_size csize Nat.add] in SK2.
          replace (U + Z.of_nat 8 + Z.of_nat (Z.to_nat size - 8 + 0)) with (U + size) in SK2 by (clear - GT; lia).
          eapply stk_merge; [exact SK| exact SK2| clear - GT; lia].
      - apply poisoned_of_u8arr; [clear - B; lia| clear - B; Z.div_mod_to_equations; lia| exact SHF']. }
    split.
    {
      intros POS. pose proof (stk_of_rw_cells asegs _ _ _ UW') as SKW. cbn [cells_size csize Nat.add] in SKW.
      assert (SKR : stk asegs m' (Z.max (U + 8) (U + size)) (ch_end ch)).
      { destruct (Z.lt_ge_cases (Z.max (U + 8) (U + size)) (ch_end ch)) as [LT|GE].
        - pose proof (junk_stk' _ _ _ JR ltac:(clear - B; lia) ltac:(clear - B E5; acb; lia) ltac:(clear - B E2; lia)) as SK0.
          replace (U + size + (ch_end ch - (U + size))) with (ch_end ch) in SK0 by (clear - AG; lia).
          destruct (stk_split asegs _ _ (Z.max (U + 8) (U + size)) _ SK0 ltac:(clear - LT B; lia)) as [_ SK1].
          eapply (stk_transport_pt P m m' AG WM); [exact SK1|]. intros a Ha. apply ZA; clear - Ha B E1 E2 E3; lia.
        - split; [clear - B; lia|]. split; [clear - B E5; acb; lia|]. intros a Ha. exfalso. clear - Ha GE. lia. }
      replace (U + size + (ch_end ch - (U + size))) with (ch_end ch) by (clear - AG; lia).
      destruct (Z.le_gt_cases 8 size) as [LE|GT].
      - replace (Z.max (U + 8) (U + size)) with (U + size) in SKR by (clear - LE; lia). exact SKR.
      - replace (Z.max (U + 8) (U + size)) with (U + 8) in SKR by (clear - GT; lia).
        destruct (stk_split asegs _ _ (U + size) _ SKW ltac:(clear - GT B; lia)) as [_ SKW2].
        eapply stk_merge; [exact SKW2| exact SKR| clear - GT E3; lia]. }
    assert (NN : 0 <= (ch_end ch - (U + round_up size 8)) / 8) by (clear - EXT; Z.div_mod_to_equations; lia).
    split.
    { eapply (poisoned_transport_pt P m m' AG WM); [exact PLf|]. rewrite Z2Nat.id by (clear - E9; Z.div_mod_to_equations; lia).
      intros a Ha. apply ZS; clear - Ha SHL B NN; lia. }
    split.
    { eapply (poisoned_transport_pt P m m' AG WM); [exact PR|]. rewrite Z2Nat.id by exact NN.
      intros a Ha. apply ZS; clear - Ha SHL B NN E9; first [lia | Z.div_mod_to_equations; lia]. }
    destruct (ch_primary ch) eqn:PRIM; [exact I|].
    eapply (poisoned_transport_pt P m m' AG WM); [exact PH|]. change (Z.of_nat 512) with 512.
    assert (SP : sh (ch_lo ch) = sh (ch_alloc_beg ch - kPageSize) /\ sh (ch_alloc_beg ch - kPageSize) + 512 = sh (ch_alloc_beg ch)).
    { unfold ch_lo. rewrite PRIM. pose proof (chunk_align s OK ch CHIN) as (A1 & _). unfold ch_lo in E6. rewrite PRIM in E6.
      clear - A1 E6. unfold sh, kPageSize in *. split; Z.div_mod_to_equations; lia. }
    intros a Ha. apply ZS; clear - Ha SP SHL B NN E9; first [lia | Z.div_mod_to_equations; lia].
  Qed.

  Lemma old_chunk_rep : forall x, In x (chunk_list st) -> x <> ch ->
    (forall a, ch_lo x <= a < ch_end x -> P a) ->
    (forall lo' k a, ch_lo x <= lo' -> lo' + 8 * k <= ch_end x -> lo' mod 8 = 0 -> 0 <= k -> sh lo' <= a < sh lo' + k -> P a) ->
    chunk_rep m' x.
  Proof.
    intros x Hx NE APP SHW. pose proof R as RR; destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _).
    pose proof (record_ext s OK x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    apply (chunk_rep_frame s m m' P AG WM OK x Hx); [| exact (CHR x Hx)].
    pose proof (chunk_align s OK x Hx) as (A1 & A2 & A3 & A4 & A5).
    assert (AL8 : ch_alloc_beg x mod 8 = 0 /\ ch_user_beg x mod 8 = 0 /\ 8 * (ch_rz x / 8) = ch_rz x)
      by (clear - A1 A2 A3; Z.div_mod_to_equations; lia).
    clear A1 A2 A3. destruct AL8 as (A1 & A3 & RZ8).
    assert (NS : 8 * nsh (ch_used x) = round_up (ch_used x) 8 /\ ch_used x <= round_up (ch_used x) 8 /\ (round_up (ch_used x) 8) mod 8 = 0)
      by (unfold nsh, round_up; clear - X9; Z.div_mod_to_equations; lia).
    acb.
    intros a Ha. destruct Ha as [Ha|[Ha|[[Q Ha]|[Ha|[Ha|[[Q Ha]|[NP Ha]]]]]]].
    - apply APP. clear - Ha X3 X6 X7 X9 NS. lia.
    - apply APP. clear - Ha X3 X6 X8 X9. lia.
    - apply APP. clear - Ha X3 X6 X7 X8 NS. lia.
    - apply (SHW (ch_alloc_beg x) (ch_rz x / 8) a); clear - Ha X3 X6 X7 X8 X9 NS A1 RZ8; lia.
    - apply (SHW (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) a);
        clear - Ha X3 X5 X6 X7 X8 X9 NS A3; try lia; Z.div_mod_to_equations; lia.
    - apply (SHW (ch_user_beg x) (nsh (ch_used x)) a); clear - Ha X3 X6 X7 X8 X9 NS A3; try lia; unfold nsh; Z.div_mod_to_equations; lia.
    - unfold ch_lo in *. rewrite NP in *. apply (SHW (ch_alloc_beg x - kPageSize) 512 a); unfold kPageSize in *; clear - Ha X3 X6 X7 X8 X9 NS A1;
        try lia; Z.div_mod_to_equations; lia.
  Qed.
  Lemma chunks_after :
    (forall a, ch_lo ch <= a < ch_end ch -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> P a) ->
    (forall a, sh (ch_lo ch) <= a < sh (ch_end ch) -> ~ (sh U <= a < sh U + nsh size) -> P a) ->
    (forall x a, In x (chunk_list st) -> x <> ch -> ch_lo x <= a < ch_end x -> P a) ->
    (forall x lo' k a, In x (chunk_list st) -> x <> ch -> ch_lo x <= lo' -> lo' + 8 * k <= ch_end x -> lo' mod 8 = 0 -> 0 <= k ->
                       sh lo' <= a < sh lo' + k -> P a) ->
    forall y, In y (chunk_list (a_st s')) -> chunk_rep m' y.
  Proof.
    intros ZA ZS APP SHW y Hy. change (a_st s') with st' in Hy. apply free_cl in Hy. destruct Hy as [->|[Hy NEU]].
    - exact (new_chunk_rep ZA ZS).
    - assert (NE : y <> ch) by (intros ->; exact (NEU eq_refl)).
      apply (old_chunk_rep y Hy NE); [intros a Ha; exact (APP y a Hy NE Ha)| intros lo' k a; apply (SHW y lo' k a Hy NE)].
  Qed.

  Lemma batch_after : forall b nx, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> batch_rep m b nx ->
    (forall a, qb_addr b <= a < qb_addr b + kBatchSize -> P a) -> (forall a, sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8 -> P a) ->
    batch_rep m' b nx.
  Proof.
    intros b nx Hb BR Z1 Z2. pose proof (WF_batch _ b WFs Hb) as (Cb1 & Cb2 & _). unfold zlen in Cb1.
    pose proof (conj Cb1 Cb2) as K. unfold batch_rep in BR |- *. unfold kBatchSize, kBatchCount in *. destruct BR as (Q1 & Q2 & Q3 & Q4).
    split; [trc Q1 Z1 K|].
    split; [eapply (u64arr_transport_pt P m m' AG WM); [exact Q2|]; unfold wlist; rewrite length_map; intros a Ha; apply Z1; clear - Ha K; lia|].
    split; [trj Q3 Z1 K|].
    eapply (poisoned_transport_pt P m m' AG WM); [exact Q4|]. change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024.
    intros a Ha. apply Z2. change (8192 / 8) with 1024. exact Ha.
  Qed.
  Lemma batches_after_list : forall l, (forall b, In b l -> In b (qc_list (as_tq st) ++ qc_list (as_gq st))) -> batches_rep m l ->
    (forall b a, In b l -> qb_addr b <= a < qb_addr b + kBatchSize -> P a) ->
    (forall b a, In b l -> sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8 -> P a) ->
    batches_rep m' l.
  Proof.
    intros l. induction l as [|b l IH]; intros SUB BR Z1 Z2; [exact I|]. cbn [batches_rep] in BR |- *. destruct BR as [Hb Hl].
    split; [apply (batch_after b _ (SUB b (or_introl eq_refl)) Hb); intros a Ha; [apply (Z1 b a)| apply (Z2 b a)]; try (left; reflexivity); exact Ha|].
    apply IH; [intros b0 H0; apply SUB; right; exact H0| exact Hl| intros b0 a H0; apply Z1; right; exact H0| intros b0 a H0; apply Z2; right; exact H0].
  Qed.
End FreePost.
End HCW.

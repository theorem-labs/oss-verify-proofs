(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2
     AllocWalkKit AW_LargeAlloc1 AW_Efs AG_Malloc AG_WFHit AG_RefillModel AS_Refill1 AS_Rta AG_RepQ AG_RepQFacts AG_RepQFacts2
     AG_MallocModel AG_RecycleModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma class_slots_count : forall st XC XB c, WFQ st XC XB -> 0 <= c < kNumClasses -> class_size c <> 0 ->
  class_size c * (zlen (rg_free_array (get_region st c)) + zlen (pc_chunks (get_pc st c))) <= rg_allocated_user (get_region st c).
Proof.
  intros st XC XB c W Hc NZ. pose proof (WFQ_region st _ _ c W Hc) as RO. pose proof (WFQ_cache st _ _ c W Hc) as CO.
  pose proof (class_size_table_facts c ltac:(unfold kNumClasses in Hc; lia)) as (T1 & T2 & _).
  assert (POS : 0 < class_size c) by lia.
  assert (AMOD : rg_allocated_user (get_region st c) mod class_size c = 0) by (apply (ro_alloc_mod _ _ RO); exact NZ).
  assert (A0 : 0 <= rg_allocated_user (get_region st c)) by (apply (ro_alloc_nonneg _ _ RO)).
  set (l := rg_free_array (get_region st c) ++ pc_chunks (get_pc st c)).
  (* [comment removed for export] *)
  assert (ND : List.NoDup l).
  { pose proof (WFQ_carved st _ _ W) as ND. apply NoDup_app_l in ND. unfold carved_addr_list in ND. apply NoDup_app_l in ND.
    assert (INc : In c (map Z.of_nat (seq 0 32))) by (apply classes_in; unfold kNumClasses in Hc; lia).
    apply in_split in INc. destruct INc as (l1 & l2 & EL). rewrite EL, flat_map_app in ND. cbn [flat_map] in ND.
    apply NoDup_app_r in ND. apply NoDup_app_l in ND. rewrite <- map_app in ND. fold l in ND.
    exact (NoDup_map_inv _ _ ND). }
  set (csz := class_size c) in *. set (au := rg_allocated_user (get_region st c)) in *.
  assert (EL : forall x, In x l -> 0 <= x /\ x * 16 < au /\ (x * 16) mod csz = 0).
  { intros x Hx. unfold l in Hx. apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
    - destruct (ro_fa_elems _ _ RO x Hx) as (E1 & E2 & _ & E4). rewrite shiftl4 in E2, E4. fold csz au in E2, E4 |- *. repeat split; assumption.
    - destruct (co_elems _ _ CO x Hx) as (E1 & E2 & _ & E4). rewrite shiftl4 in E2, E4. fold csz au in E2, E4 |- *. repeat split; assumption. }
  assert (X : zlen l <= au / csz).
  { apply (nodup_slots_length (fun cp => cp * 16 / csz)); [exact ND| apply Z.div_pos; lia| |].
    - intros x Hx. destruct (EL x Hx) as (E1 & E2 & E4).
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      pose proof (mult_below csz (x * 16) au POS E4 AMOD E2). Z.div_mod_to_equations. nia.
    - intros x y Hx Hy E. destruct (EL x Hx) as (_ & _ & Ex). destruct (EL y Hy) as (_ & _ & Ey). Z.div_mod_to_equations. nia. }
  unfold l in X. rewrite zlen_app in X. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cd_state (st : astate) (c p : Z) (drained : bool) : astate := push_state (if drained then rta_state st c else st) c p.

Section CDState.
  Variables (st : astate) (XC XB : list Z) (c p : Z) (drained : bool).
  Let pc := get_pc st c.
  Let r := get_region st c.
  Let mc := max_count c.
  Let n := mc / 2.
  Let k := if drained then n else 0.
  Let cnt := pc_count pc. Let chunks := pc_chunks pc.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let mfa' := if drained then rta_mfa nf n mfa else mfa.
  Let stX := if drained then rta_state st c else st.
  Let st' := cd_state st c p drained.
  Hypothesis W : WFQ st XC (p :: XB).
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis INIT : as_cache_inited st = true.
  Hypothesis EC : class_of_addr st p = c.
  (* [comment removed for export] *)
  Hypothesis DR : if drained then cnt = mc else cnt < mc.
  Hypothesis FROOM : efs_new (nf + n) <= kFreeArraySize.

  Let LENC : length (as_cache st) = 32%nat. Proof. exact (proj2 (WFQ_lens st _ _ W)). Qed.
  Let LENR : length (as_regions st) = 32%nat. Proof. exact (proj1 (WFQ_lens st _ _ W)). Qed.
  Let T : 0 <= class_size c <= 65536 /\ class_size c mod 32 = 0 /\ (1 <= c -> 32 <= class_size c)
          /\ 0 <= max_count c <= 16 /\ (1 <= c -> 2 <= max_count c) /\ max_count c mod 2 = 0.
  Proof. apply class_size_table_facts. unfold kNumClasses in HC. lia. Qed.

  Lemma cd_stX : WFQ stX XC (p :: XB) /\ class_of_addr stX p = c /\ as_cache_inited stX = true /\ addr_to_compact stX c p = addr_to_compact st c p
    /\ get_pc stX c = mkPC (cnt - k) (skipn (Z.to_nat k) chunks) /\ (forall c0, 0 <= c0 -> c0 <> c -> get_pc stX c0 = get_pc st c0)
    /\ get_region stX c = mkRegion mu au (nf + k) (firstn (Z.to_nat k) chunks ++ fl) mfa' /\ (forall c0, 0 <= c0 -> c0 <> c -> get_region stX c0 = get_region st c0)
    /\ as_maps stX = (if mfa <? mfa' then [mkMap (free_array_base st c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false] else []) ++ as_maps st
    /\ as_space_beg stX = as_space_beg st /\ as_ptr_array stX = as_ptr_array st /\ as_sec stX = as_sec st /\ as_chunks stX = as_chunks st
    /\ as_tq stX = as_tq st /\ as_gq stX = as_gq st /\ as_n_reserved stX = as_n_reserved st /\ as_internal_init stX = as_internal_init st
    /\ as_qmax stX = as_qmax st /\ as_qmin stX = as_qmin st /\ as_qcache stX = as_qcache st /\ length (as_cache stX) = 32%nat
    /\ pc_count (get_pc stX c) + 1 <= max_count c.
  Proof.
    pose proof T as (_ & _ & _ & T4 & T5 & T6). specialize (T5 ltac:(clear - HC; lia)).
    pose proof (co_count _ _ (WFQ_cache st _ _ c W ltac:(clear - HC; unfold kNumClasses in *; lia))) as CC. fold pc cnt chunks in CC.
    unfold stX, k, mfa'. destruct drained.
    - pose proof (rta_facts st _ _ c W HC DR) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11). fold pc chunks r mc n nf mfa in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11.
      pose proof (rta_same st _ _ c W HC) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11).
      split; [exact (WFQ_rta st _ _ c W HC INIT DR FROOM)|].
      split; [rewrite S10; exact EC|]. split; [unfold rta_state; cbn [as_cache_inited]; exact INIT|].
      split; [unfold addr_to_compact; rewrite S7; reflexivity|].
      split; [rewrite (rta_pc_c st _ _ c W HC); unfold rta_pc; fold pc mc n cnt chunks; reflexivity|].
      split; [intros c0 H0 H1; exact (rta_pc_o st _ _ c W HC c0 H0 H1)|].
      split; [rewrite (rta_region_c st _ _ c W HC); unfold rta_region; fold r pc mc n chunks nf mfa au mu fl; reflexivity|].
      split; [intros c0 H0 H1; exact (rta_region_o st _ _ c W HC c0 H0 H1)|].
      split.
      { unfold rta_state. cbn [as_maps]. unfold rta_maps. fold r pc mc n nf mfa. unfold rta_mfa.
        destruct (Z.leb_spec (4 * (nf + n)) mfa) as [LE|GT]; [rewrite Z.ltb_irrefl; reflexivity|].
        replace (mfa <? efs_new (nf + n)) with true; [reflexivity|]. symmetry. apply Z.ltb_lt. revert Q7 Q8. unfold rta_mfa.
        replace (4 * (nf + n) <=? mfa) with false by (symmetry; apply Z.leb_gt; exact GT). clear - GT. intros. lia. }
      assert (PC1 : pc_count (get_pc (rta_state st c) c) + 1 <= max_count c).
      { rewrite (rta_pc_c st _ _ c W HC). unfold rta_pc. cbn [pc_count]. fold pc mc n cnt. clear - DR Q4 Q5; lia. }
      unfold rta_state in PC1 |- *. cbn in PC1 |- *. rewrite length_upd_nth. repeat split; try reflexivity; try exact LENC; exact PC1.
    - rewrite Z.ltb_irrefl, Z.add_0_r, Z.sub_0_r. cbn [Z.to_nat skipn firstn app]. split; [exact W|].
      repeat split; try reflexivity; try assumption.
      + unfold cnt, chunks, pc. destruct (get_pc st c); reflexivity.
      + unfold mu, au, nf, fl, mfa, r. destruct (get_region st c); reflexivity.
      + fold pc cnt. clear - DR; lia.
  Qed.

  Lemma WFQ_cd_state : WFQ st' XC XB.
  Proof.
    pose proof cd_stX as (X1 & X2 & X3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X22).
    unfold st', cd_state. fold stX. exact (WFQ_push stX _ _ c p X1 X2 X3 X22).
  Qed.

  Lemma cd_state_fields :
       get_pc st' c = mkPC (cnt - k + 1) (addr_to_compact st c p :: skipn (Z.to_nat k) chunks) /\ (forall c0, 0 <= c0 -> c0 <> c -> get_pc st' c0 = get_pc st c0)
    /\ get_region st' c = mkRegion mu au (nf + k) (firstn (Z.to_nat k) chunks ++ fl) mfa' /\ (forall c0, 0 <= c0 -> c0 <> c -> get_region st' c0 = get_region st c0)
    /\ as_maps st' = (if mfa <? mfa' then [mkMap (free_array_base st c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false] else []) ++ as_maps st
    /\ as_space_beg st' = as_space_beg st /\ as_ptr_array st' = as_ptr_array st /\ as_sec st' = as_sec st /\ as_chunks st' = as_chunks st
    /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st /\ as_n_reserved st' = as_n_reserved st /\ as_cache_inited st' = true /\ as_internal_init st' = as_internal_init st
    /\ as_qmax st' = as_qmax st /\ as_qmin st' = as_qmin st /\ as_qcache st' = as_qcache st.
  Proof.
    pose proof cd_stX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22).
    unfold st', cd_state. fold stX. unfold push_state, set_pc, get_pc, get_region in *. cbn.
    assert (IDX : (zidx c < length (as_cache stX))%nat) by (rewrite X21; unfold zidx; unfold kNumClasses in HC; clear - HC; lia).
    split; [rewrite znth_upd_nth_eq by exact IDX; rewrite X4; unfold get_pc in X5; rewrite X5; reflexivity|].
    split; [intros c0 H0 H1; rewrite znth_upd_nth_neq by (unfold zidx; clear - H0 H1 HC; lia); exact (X6 c0 H0 H1)|].
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_state_eval : forall stA, same_but_shadow stA st ->
    (drained = true -> mfa < 4 * (nf + n) ->
       Z.land (free_array_base st c + mfa) 7 = 0 /\ addr_is_in_mem (free_array_base st c + mfa) = true
       /\ Z.land (efs_new (nf + n) - mfa) 7 = 0 /\ addr_is_in_mem (free_array_base st c + mfa + (efs_new (nf + n) - mfa) - 8) = true) ->
    exists stA' ev, cache_dealloc stA c p = Some (stA', ev) /\ same_but_shadow stA' st'.
  Proof.
    intros stA SBS GEO. unfold st', cd_state. destruct drained.
    - destruct (cache_dealloc_eval_drain stA st c p SBS HC INIT LENC LENR DR FROOM ltac:(cbv zeta; intros GT; exact (GEO eq_refl GT))) as (stA' & ev & E & SB).
      exists stA', ev. exact (conj E SB).
    - destruct (cache_dealloc_eval_push stA st c p SBS HC INIT LENC LENR ltac:(exact DR)) as (stA' & E & SB). exists stA', []. exact (conj E SB).
  Qed.
End CDState.

Section CDCells.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m : mem) (XC XB : list Z) (c : Z).
  Hypothesis RQ : AREPQ s XC XB m.
  Hypothesis HC : 1 <= c <= 30.
  Let st := a_st s.
  Let T := a_thr s.
  Let CA := a_cache s.
  Let P := CA + PCLASS_SIZE * c.
  Let RI := a_ri s + REGIONINFO_SIZE * c.
  Let r := get_region st c.
  Let pc := get_pc st c.
  Hypothesis INIT : as_cache_inited st = true.

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st XC XB. Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let MEM : ARmem s m. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
  Let RO : region_ok st c. Proof. exact (WFQ_region st _ _ c WQ ltac:(clear - HC; unfold kNumClasses; lia)). Qed.
  Let CO : cache_ok st c. Proof. exact (WFQ_cache st _ _ c WQ ltac:(clear - HC; unfold kNumClasses; lia)). Qed.
  Let CT : 32 <= class_size c <= 65536 /\ class_size c mod 32 = 0 /\ 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
  Proof. clear - HC. pose proof (class_size_table_facts c ltac:(lia)) as (X1 & X2 & X3 & X4 & X5 & X6). repeat split; try lia. Qed.

  (* [comment removed for export] *)
  Lemma cd_pure :
       0 <= rg_num_freed r /\ 4 * rg_num_freed r <= rg_mapped_free_array r <= kFreeArraySize
    /\ rg_mapped_free_array r mod kFreeArrayMapSize = 0
    /\ 0 <= rg_allocated_user r <= rg_mapped_user r /\ rg_mapped_user r + kUserMapSize <= kFreeArrayOffset
    /\ rg_mapped_user r mod kUserMapSize = 0
    /\ length (rg_free_array r) = Z.to_nat (rg_num_freed r)
    /\ pc_count pc = zlen (pc_chunks pc) /\ 0 <= pc_count pc <= max_count c
    /\ 32 <= class_size c <= 65536 /\ 2 <= max_count c <= 16.
  Proof.
    clear MEM.
    pose proof (ro_alloc_nonneg _ _ RO) as X1. pose proof (ro_alloc_le _ _ RO) as X2. pose proof (ro_mapped_mod _ _ RO) as X3. pose proof (ro_mapped_bound _ _ RO) as X4.
    pose proof (ro_numfreed _ _ RO) as NF. pose proof (ro_fa_le _ _ RO) as X5. pose proof (ro_fa_mod _ _ RO) as X6. pose proof (ro_fa_bound _ _ RO) as X7.
    pose proof (co_count _ _ CO) as CC. pose proof (co_bound _ _ CO) as CB. fold st in X1, X2, X3, X4, X5, X6, X7, NF, CC, CB. fold r in X1, X2, X3, X4, X5, X6, X7, NF.
    fold pc in CC, CB. rewrite INIT in CB. pose proof CT as (C1 & C2 & C3 & C4).
    assert (LEN : length (rg_free_array r) = Z.to_nat (rg_num_freed r)) by (rewrite NF; unfold zlen; clear; lia).
    assert (NF0 : 0 <= rg_num_freed r) by (rewrite NF; unfold zlen; clear; lia).
    assert (CC0 : 0 <= pc_count pc) by (rewrite CC; unfold zlen; clear; lia).
    clear - X1 X2 X3 X4 X5 X6 X7 LEN NF0 CC CB CC0 C1 C3. repeat split; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_cells_of_arepq :
    exists (q0 q1 q2 q3 : word),
       rw_cells asegs m P [C4 (wz (pc_count pc)); C4 (wz (max_count c))]
    /\ rw_cells asegs m (P + 8) [C8 (wz (class_size c))]
    /\ u32arr asegs m (P + 16) (wlist (rev (pc_chunks pc)))
    /\ stk asegs m (P + 16 + 4 * pc_count pc) (P + 80)
    /\ rw_cells asegs m (T + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs m (T + 2800) (T + 3168)
    /\ rw_cells asegs m RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (rg_num_freed r)); C8 (wz (rg_mapped_free_array r));
                            C8 (wz (rg_allocated_user r)); C8 (wz 0); C8 (wz (rg_mapped_user r)); C8 (wz 0)]
    /\ stk asegs m (RI + 64) (RI + 68) /\ rw_cells asegs m (RI + 68) [C1 (b8 0)] /\ stk asegs m (RI + 69) (RI + 128)
    /\ u32arr asegs m (FA s c) (wlist (rev (rg_free_array r)))
    /\ stk asegs m (FA s c + 4 * rg_num_freed r) (FA s c + rg_mapped_free_array r)
    /\ stk asegs m (RB s c + rg_allocated_user r) (RB s c + rg_mapped_user r)
    /\ RENV (wz ATP) ATSD (a_ctx s) T (a_sb s) (a_ri s) m.
  Proof.
    pose proof MEM as (INST & FL & THR & SEC & IA & CL & CH & BT & BG).
    assert (Hc' : 0 <= c < kNumClasses) by (clear - HC; unfold kNumClasses; lia).
    destruct (CL c Hc') as (RG & PC & RSH & RJ).
    pose proof cd_pure as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10).
    pose proof PL as (S1 & S2 & S3 & P1' & P2' & P3 & T1 & T2 & T3 & _).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia].
    assert (RS : a_sb s <= RB s c /\ RB s c + 2^32 <= a_sb s + kSpaceSize /\ FA s c = RB s c + kFreeArrayOffset).
    { unfold RB, FA. rewrite free_array_base_eq. pose proof (region_in_space st c ltac:(clear - HC; lia)) as RS'. fold st. change (as_space_beg st) with (a_sb s) in RS'. clear - RS'. lia. }
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kFreeArraySize, kFreeArrayOffset, kUserMapSize in *.
    (* [comment removed for export] *)
    destruct PC as (Q1 & Q2 & QU & QJ). fold st CA P pc in Q1, Q2, QU, QJ. rewrite INIT in Q1, Q2.
    replace (negb (c =? 0)) with true in Q1, Q2 by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; clear - HC; lia). cbn [andb] in Q1, Q2.
    (* [comment removed for export] *)
    destruct THR as (Tc & Ttid & Tthr & Tstk & T40 & Tsw & Ttq & Jtq & Jcs & Jst & Tunw). fold T CA in Tc, Tstk, T40, Tsw, Ttq, Jtq, Jcs, Jst, Tunw.
    unfold OT_CACHE, CACHE_STATS, OT_STATS, OT_UNWINDING, OT_TQ, PCLASS_SIZE, REGIONINFO_SIZE in *.
    assert (ECA : CA = T + 208) by reflexivity.
    pose proof (junk_stk' _ _ _ Jcs ltac:(clear - T2 ECA; lia) ltac:(clear - T2 ECA ACEILB; lia) ltac:(clear; lia)) as SCS.
    destruct (stk_cells _ _ _ SCS ltac:(clear; lia)) as [js JS]. replace (CA + 2560 + (2800 - 208 - 2560) - (CA + 2560)) with 32 in JS by (clear; lia).
    change (Z.to_nat 32) with 32%nat in JS.
    apply (rw_cells_split_CB asegs _ _ [] 32 js [] [8;8;8;8]%nat) in JS; [| reflexivity]. cbn [mk_CB_cells app] in JS.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS) as [w0 JS0].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS0. destruct JS0 as [K0 JS1]. cbn [cells_size csize Nat.add] in JS1.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS1) as [w1 JS1'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS1'. destruct JS1' as [K1 JS2]. cbn [cells_size csize Nat.add] in JS2.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS2) as [w2 JS2'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS2'. destruct JS2' as [K2 JS3]. cbn [cells_size csize Nat.add] in JS3.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS3) as [w3 K3].
    exists w0, w1, w2, w3.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact QU|].
    split. { replace (P + 80) with (P + 16 + 4 * pc_count pc + (64 - 4 * pc_count pc)) by (clear; lia).
             apply junk_stk'; [exact QJ| subst P CA T; clear - T2 U9 HC ECA; lia| subst P CA T; clear - T2 U9 U10 HC ECA ACEILB; lia| clear - U9 U10; lia]. }
    split. { replace (T + 2768) with (CA + 2560) by (clear - ECA; lia).
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add]. exact K3. }
    split. { replace (T + 3168) with (T + 2800 + (3168 - 2800)) by (clear; lia). apply junk_stk'; [exact Jst| subst T; clear - T2; lia| subst T; clear - T2 ACEILB; lia| clear; lia]. }
    (* [comment removed for export] *)
    destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7). fold st in G1, G2, G3, G4, G5, G6, G7. fold r in G1, G2, G3, G4, G5, G6, G7. fold RI in G1, G2, G3, G4.
    assert (ERI : RI = a_sb s + 137438953472 + 128 * c) by (subst RI; unfold a_ri, kSpaceSize; clear; lia).
    split; [exact G1|].
    split. { replace (RI + 68) with (RI + 64 + 4) by (clear; lia). apply junk_stk'; [exact G2| clear - ERI S2 HC; lia| clear - ERI S3 HC ACEILB; lia| clear; lia]. }
    split; [exact G3|].
    split. { replace (RI + 128) with (RI + 69 + 59) by (clear; lia). apply junk_stk'; [exact G4| clear - ERI S2 HC; lia| clear - ERI S3 HC ACEILB; lia| clear; lia]. }
    split; [exact G5|].
    split. { replace (FA s c + rg_mapped_free_array r) with (FA s c + 4 * rg_num_freed r + (rg_mapped_free_array r - 4 * rg_num_freed r)) by (clear; lia).
             apply junk_stk'; [exact G6| clear - RS S2 U1; lia| clear - RS S3 U1 U2 ACEILB; lia| clear - U2; lia]. }
    split. { replace (RB s c + rg_mapped_user r) with (RB s c + rg_allocated_user r + (rg_mapped_user r - rg_allocated_user r)) by (clear; lia).
             apply junk_stk'; [exact G7| clear - RS S2 U4; lia| clear - RS S3 U4 U5 ACEILB; lia| clear - U4; lia]. }
    (* [comment removed for export] *)
    destruct INST as (A1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A9).
    destruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    pose proof A1 as A1'.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in A1. destruct A1 as [ISB A2]. cbn [cells_size csize Nat.add length] in A2.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in A2. destruct A2 as [IRI A3]. cbn [cells_size csize Nat.add length] in A3.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in A3. destruct A3 as [PMH _].
    unfold AINST, OI_SPACEBEG, AFLAGS, ACFLAGS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT,
           AALLOCFLAGS, AHOOKS, AREALMEMSET, AMEMSET, AGOT_LO, APAGESZ, ASECNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2 in *.
    cbn [Z.of_nat Z.add Pos.add Nat.add] in IRI, PMH.
    constructor.
    - constructor; assumption.
    - exact ISB.
    - exact IRI.
    - exact PMH.
  Qed.
End CDCells.

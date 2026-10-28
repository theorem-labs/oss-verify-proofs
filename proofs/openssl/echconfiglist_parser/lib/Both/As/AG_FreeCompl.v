(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel LazyRestrict.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AsDepotHash AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_Put1 AW_Enqueue1 AW_Enqueue2 AS_Free1 AS_Refill1
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_WriteSet AG_MallocCold AG_MallocTop
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section HCW.
  Context {HCEIL : HeapCeil}.

Section FreeCompl.
  Variables (s : ast) (m : mem) (d : depot) (lo spv : Z) (ch : chunk) (s' : ast).

  Let st := a_st s.
  Let TH := a_thr s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  Let lcount := qb_count lb.
  Let c := kBatchClass.
  Let CA := TH + 208.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let chunks2 := firstn (Z.to_nat n) fl1.
  Let cp2 := hd 0 chunks2.
  Let B2 := compact_to_addr st2 c cp2.
  Let cp1 := hd 0 (pc_chunks (get_pc st c)).
  Let B1 := compact_to_addr st c cp1.
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo spv TH U size d.
  Let Wa : list ivl := [(lo, spv + -2208); (TH + OT_TQ + 24, TH + OT_TQ + 32); (LA + 8, LA + 24); (LA + 24 + 8 * lcount, LA + 32 + 8 * lcount)].
  Let WR : list ivl := (lo, spv) :: (TH + 3168, TH + 3169) :: rf_W lo spv P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  (* [comment removed for export] *)
  Let INW (iv : ivl) : Prop := forall a, fst iv <= a < snd iv -> awrit s s' d lo spv a.

  Hypothesis R : AREP s m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis DPL : depot_placed s d.
  Hypothesis HI : lo + 2944 <= spv.

  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HC24 : 0 <= c < kNumClasses. Proof. unfold c, kBatchClass, kNumClasses. lia. Qed.
  Let HC : 1 <= c <= 30. Proof. unfold c, kBatchClass. lia. Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  (* [comment removed for export] *)
  Let BND : 4096 <= TH /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ sb mod 65536 = 0
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384 /\ c = 24.
  Proof.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & _).
    assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia].
    clear - Y1 Y2 Y3 T2 E1 E2. unfold TH, sb, P, CA, RI, a_ri, c. unfold a_sb in *.
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kBatchClass in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Local Ltac inw := unfold INW; cbn [fst snd]; intros aa Haa.
  Local Ltac awstk := inw; left.
  Local Ltac awthr := inw; right; left; unfold kPageSize; fold TH.
  Local Ltac awsp := inw; right; right; left; unfold kSpaceSize, kPageSize; fold sb.
  Local Ltac awsh := inw; right; right; right; left; unfold kSpaceSize, kPageSize; fold sb.

  (* [comment removed for export] *)
  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ U mod 8 = 0 /\ 1 <= size
            /\ round_up size 8 = 8 * nsh size /\ AIMG_TOP <= ch_lo ch /\ ch_end ch <= aceil.
  Proof.
    pose proof (record_ext s OKs ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (chunk_geom s OKs ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (chunk_align s OKs ch CHIN) as (_ & _ & A3 & _).
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 A3. subst U size. repeat split; try assumption; lia.
  Qed.
  Lemma rec_zone : forall X Y, ch_lo ch <= X -> Y <= ch_end ch -> INW (X, Y).
  Proof.
    intros X Y H1 H2 a Ha. cbn [fst snd] in Ha. destruct (ch_primary ch) eqn:E.
    - pose proof (record_primary_space s OKs ch CHIN E) as [Q1 Q2]. right; right; left. unfold kPageSize. clear - Q1 Q2 H1 H2 Ha. lia.
    - destruct (record_secondary_map s OKs ch CHIN E) as (h & Hh & L0 & E0 & _). do 5 right; left. exists h. split; [left; exact Hh|].
      left. clear - L0 E0 H1 H2 Ha. lia.
  Qed.
  Lemma rec_zone_sh : forall X k, ch_lo ch <= X -> X mod 8 = 0 -> 0 <= k -> X + 8 * k <= ch_end ch -> INW (sh X, sh X + k).
  Proof.
    intros X k H1 M8 Hk H2 a Ha. cbn [fst snd] in Ha. pose proof EXT as (_ & _ & _ & _ & _ & _ & E7 & E8). destruct (ch_primary ch) eqn:E.
    - pose proof (record_primary_space s OKs ch CHIN E) as [Q1 Q2]. right; right; right; left.
      clear - Q1 Q2 H1 H2 M8 Hk Ha E7. unfold sh, ASHADOW_BASE, kSpaceSize, kPageSize, AIMG_TOP in *. Z.div_mod_to_equations. lia.
    - destruct (record_secondary_map s OKs ch CHIN E) as (h & Hh & L0 & E0 & _). do 5 right; left. exists h. split; [left; exact Hh|].
      right. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
      pose proof (SEC h Hh) as (A1 & _). clear - L0 E0 H1 H2 M8 Hk Ha A1 E7. unfold sh, ASHADOW_BASE, kPageSize, AIMG_TOP in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma depot_compl : Forall INW (depot_W d).
  Proof.
    unfold depot_W. constructor; [inw; do 6 right; left; right; left; clear - Haa; lia|].
    constructor; [inw; do 6 right; left; right; left; clear - Haa; lia|].
    constructor; [inw; do 7 right; left; clear - Haa; lia|].
    constructor; [inw; do 7 right; right; clear - Haa; lia|].
    constructor.
  Qed.

  (* [comment removed for export] *)
  Lemma head_compl : Forall INW Wh.
  Proof.
    pose proof BND as B0. pose proof EXT as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    unfold Wh, free_head_W. apply Forall_app. split; [| exact depot_compl].
    constructor; [awstk; exact Haa|].
    constructor; [awthr; clear - B0 Haa; lia|].
    constructor; [inw; do 6 right; left; right; right; left; exact Haa|].
    constructor; [inw; do 6 right; left; right; right; right; exact Haa|].
    constructor; [apply rec_zone; [clear - E1; lia| clear - E3; lia]|].
    constructor; [apply rec_zone; [clear - E1; lia| clear - E3; lia]|].
    constructor; [awthr; clear - B0 Haa; lia|].
    constructor; [| constructor].
    apply rec_zone_sh; [clear - E1; lia| exact E4| unfold nsh; clear - E5; Z.div_mod_to_equations; lia| rewrite <- E6; exact E2].
  Qed.

  (* [comment removed for export] *)
  Lemma last_batch_sp : l <> [] -> sb <= LA /\ LA + 8192 <= sb + kSpaceSize /\ 1 <= lcount <= kBatchCount.
  Proof.
    intros NE. pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & INlb & _ & CB & _).
    fold st tq l lb LA lcount in INlb, CB.
    pose proof (batch_carved s OKs lb INlb) as (CV & _). pose proof (carved_in_space s OKs _ _ CV) as (CS1 & CS2 & _). fold st LA in CS1, CS2.
    change (class_size kBatchClass) with 8192 in CS2. change (a_sb s) with sb in CS1, CS2. split; [exact CS1|]. split; [exact CS2| exact CB].
  Qed.

  (* [comment removed for export] *)
  Lemma app_compl : l <> [] -> lcount < kBatchCount -> Forall INW Wa.
  Proof.
    intros NE LT. pose proof BND as B0. pose proof (last_batch_sp NE) as (CS1 & CS2 & CB). unfold Wa.
    constructor; [awstk; clear - Haa HI; lia|].
    constructor; [awthr; unfold OT_TQ in *; clear - B0 Haa; lia|].
    constructor; [awsp; clear - CS1 CS2 Haa; unfold kSpaceSize in *; lia|].
    constructor; [awsp; clear - CS1 CS2 CB LT Haa; unfold kSpaceSize, kBatchCount in *; lia|].
    constructor.
  Qed.

  (* [comment removed for export] *)
  Lemma new_compl : forall B, sb <= B /\ B + kBatchSize <= sb + kSpaceSize -> Forall INW (enq_new_W lo spv TH B LA).
  Proof.
    intros B [BS1 BS2]. pose proof BND as B0.
    assert (LAX : LA = 0 \/ (sb <= LA /\ LA + 8192 <= sb + kSpaceSize)).
    { assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]).
      destruct D as [EL|NE]; [left; unfold LA, lb; rewrite EL; reflexivity| right].
      pose proof (last_batch_sp NE) as (CS1 & CS2 & _). exact (conj CS1 CS2). }
    unfold enq_new_W.
    constructor; [awstk; clear - Haa HI; lia|].
    constructor; [awthr; clear - B0 Haa; lia|].
    constructor; [awthr; clear - B0 Haa; lia|].
    constructor; [awsp; clear - BS1 BS2 Haa; unfold kSpaceSize, kBatchSize in *; lia|].
    constructor; [awthr; clear - B0 Haa; lia|].
    constructor; [| constructor].
    awsp. clear - LAX Haa. unfold kSpaceSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hit_slot_sp : pc_count (get_pc st c) <> 0 -> sb <= B1 /\ B1 + kBatchSize <= sb + kSpaceSize.
  Proof.
    intros HIT. pose proof BND as B0.
    assert (HIN : In cp1 (pc_chunks (get_pc st c))).
    { pose proof (co_count _ _ (WF_cache st c WFs HC24)) as CC. unfold cp1. destruct (pc_chunks (get_pc st c)) as [|x q]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
    pose proof (WF_region st c WFs HC24) as RO.
    pose proof (ro_alloc_le _ _ RO) as W2. pose proof (ro_mapped_bound _ _ RO) as W3. fold st r in W2, W3. fold au mu in W2, W3.
    destruct (co_elems _ _ (WF_cache st c WFs HC24) cp1 HIN) as (E1 & E2 & _).
    unfold kCompactPtrScale in E2. rewrite Z.shiftl_mul_pow2 in E2 by (clear; lia). change (2 ^ 4) with 16 in E2. fold st r in E2. fold au in E2.
    change (class_size c) with 8192 in E2.
    unfold kUserMapSize, kFreeArrayOffset in W3.
    unfold B1. rewrite compact_to_addr_eq. change (region_beg st c) with (RB s c).
    destruct B0 as (_ & _ & _ & _ & _ & _ & _ & ERB & _ & C24). rewrite ERB, C24. unfold kBatchSize, kSpaceSize.
    clear - E1 E2 W2 W3. lia.
  Qed.

  (* [comment removed for export] *)
  Section RefillCompl.
    Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.

    Let RF := rf_facts st c WFs HC ROOM.
    Let BR : 0 <= au <= mu /\ mu <= mu' /\ mu' + 262144 <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' <= 536870912 /\ 1 <= n <= nf1 /\ au <= au' <= mu' /\ 0 <= nnew
             /\ zlen fl1 = nf1 /\ au' = au + nnew * 8192.
    Proof.
      pose proof RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & _).
      pose proof (WF_region st c WFs HC24) as RO.
      pose proof (ro_alloc_nonneg _ _ RO) as W1. pose proof (ro_alloc_le _ _ RO) as W2. pose proof (ro_mapped_bound _ _ RO) as W3.
      pose proof (ro_fa_le _ _ RO) as W4. pose proof (ro_fa_bound _ _ RO) as W5. pose proof (ro_numfreed _ _ RO) as W6.
      fold st r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q11, Q12, W1, W2, W3, W4, W5, W6. fold nf mfa au mu fl n in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q11, Q12, W1, W2, W3, W4, W5, W6.
      fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q11, Q12. change (class_size c) with 8192 in Q5. unfold zlen in W6.
      unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
      assert (N1 : n = 1) by reflexivity.
      clear - W1 W2 W3 W4 W5 W6 Q1 Q2 Q3 Q5 Q6 Q7 Q12 ROOM N1. repeat split; lia.
    Qed.
    Let ALN : (RB s c + mu) mod 8 = 0 /\ (FA s c + mfa) mod 8 = 0 /\ au mod 16 = 0.
    Proof.
      pose proof (WF_region st c WFs HC24) as RO.
      pose proof (ro_fa_mod _ _ RO) as W7. pose proof (ro_alloc_mod _ _ RO ltac:(change (class_size c) with 8192; lia)) as W8. pose proof (ro_mapped_mod _ _ RO) as W9.
      fold st r in W7, W8, W9. fold mfa au mu in W7, W8, W9. change (class_size c) with 8192 in W8.
      destruct BND as (_ & _ & _ & SB64 & _ & _ & _ & ERB & EFA & C24).
      unfold kUserMapSize, kFreeArrayMapSize in *. clear - SB64 ERB EFA C24 W7 W8 W9.
      destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
      destruct (proj1 (Z.mod_divide mfa 262144 ltac:(lia)) W7) as [f Hf].
      destruct (proj1 (Z.mod_divide mu 262144 ltac:(lia)) W9) as [u Hu].
      destruct (proj1 (Z.mod_divide au 8192 ltac:(lia)) W8) as [q Hq].
      rewrite EFA, ERB, C24.
      split; [| split].
      - apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * 24 + 32768 * u). lia.
      - apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * 24 + 469762048 + 32768 * f). lia.
      - apply Z.mod_divide; [lia|]. exists (512 * q). lia.
    Qed.

    Lemma refill_compl : Forall INW WR.
    Proof.
      pose proof BND as B0. pose proof BR as BQ. pose proof ALN as (M1 & M2 & M3).
      unfold WR, rf_W.
      constructor; [awstk; exact Haa|].
      constructor; [awthr; clear - B0 Haa; lia|].
      constructor; [awstk; exact Haa|].
      constructor; [awthr; clear - B0 Haa; lia|].
      constructor; [awthr; clear - B0 Haa; lia|].
      do 5 (constructor; [awsp; clear - B0 Haa; lia|]).
      constructor; [awsp; clear - B0 BQ Haa; lia|].
      constructor; [awsp; clear - B0 BQ Haa; lia|].
      constructor; [awsh; unfold sh, ASHADOW_BASE in *; clear - B0 BQ M2 Haa; Z.div_mod_to_equations; lia|].
      constructor; [awsh; unfold sh, ASHADOW_BASE in *; clear - B0 BQ M1 Haa; Z.div_mod_to_equations; lia|].
      constructor; [awthr; clear - B0 Haa; lia|].
      eapply Forall_impl; [| apply icW_inside]. intros [x y] (I1 & I2 & I3). cbn [fst snd] in I1, I2, I3. awthr; clear - B0 I1 I2 I3 Haa; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma refill_slot_sp : sb <= B2 /\ B2 + kBatchSize <= sb + kSpaceSize.
    Proof.
      pose proof BND as B0. pose proof BR as BQ. pose proof ALN as (M1 & M2 & M3).
      pose proof RF as (Q1 & Q2 & _). fold st r in Q1, Q2. fold nf mfa au mu fl n in Q1, Q2. fold mu' nnew nf1 fl1 in Q1, Q2.
      pose proof (WF_region st c WFs HC24) as RO. pose proof (ro_fa_elems _ _ RO) as W10. fold st r in W10. fold au fl in W10. change (class_size c) with 8192 in W10.
      assert (HIN : In cp2 fl1).
      { assert (L : length chunks2 = Z.to_nat n) by (unfold chunks2; rewrite length_firstn; unfold zlen in Q2; clear - Q1 Q2 BQ; lia).
        unfold cp2. rewrite <- (firstn_skipn (Z.to_nat n) fl1). fold chunks2. apply in_or_app. left.
        destruct chunks2 as [|x q] eqn:E; [exfalso; cbn in L; clear - L BQ; lia| left; reflexivity]. }
      assert (CP : 0 <= cp2 /\ cp2 * 16 + 8192 <= au' + 8192).
      { unfold fl1, rf_fl1 in HIN. fold n nnew in HIN. change (class_size c) with 8192 in HIN. apply in_app_or in HIN. destruct HIN as [HIN|HIN].
        - apply in_carve_asc in HIN. destruct HIN as (j & Hj & ->). rewrite Z2Nat.id in Hj by (clear - BQ; lia).
          unfold kCompactPtrScale. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 4) with 16.
          destruct BQ as (BQ1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & EAU). rewrite EAU.
          clear - Hj BQ1 M3. Z.div_mod_to_equations. lia.
        - destruct (W10 cp2 HIN) as (A1 & A2 & _). unfold kCompactPtrScale in A2. rewrite Z.shiftl_mul_pow2 in A2 by (clear; lia). change (2 ^ 4) with 16 in A2.
          clear - A1 A2 BQ. lia. }
      unfold B2. rewrite compact_to_addr_eq. change (region_beg st2 c) with (region_beg st c). change (region_beg st c) with (RB s c).
      destruct B0 as (_ & _ & _ & _ & _ & _ & _ & ERB & _ & C24). rewrite ERB, C24. unfold kBatchSize, kSpaceSize.
      clear - CP BQ. lia.
    Qed.
  End RefillCompl.
End FreeCompl.
End HCW.

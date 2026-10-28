(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BazyRestrict.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BsDepotInv BsDepotHash BW_DepotFrame BW_MallocBase BW_AllocBase BW_IAInit BW_Put1 BW_Enqueue1 BW_Enqueue2 BS_Free1 BS_Refill1 BG_MallocModel BG_WFHit BG_Malloc BG_Malloc2 BG_RefillModel BG_Refill1 BG_Refill2 BG_Frame BG_MallocCold BG_MallocTop BG_FreeModel BG_WFFree BG_Free1 BG_FreeFacts BG_Free2 BG_Free3 BG_Free5.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Section FreeFrame.
  Variables (s : ast) (m : mem) (LB : list (Z * Z)) (d : depot) (lo spv : Z) (ch : chunk).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let FSB := a_fsb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
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
  Let LB' := lb_remove U LB.

  Let Wh : list ivl := free_head_W lo spv TH U size d.
  Let Wa : list ivl := [(lo, spv + -2208); (TH + OT_TQ + 24, TH + OT_TQ + 32); (LA + 8, LA + 24); (LA + 24 + 8 * lcount, LA + 32 + 8 * lcount)].
  Let WR : list ivl := (lo, spv) :: (TH + 3168, TH + 3169) :: rf_W lo spv P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 32768).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2912 <= spv.

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HLB : forall b, In b LB -> In b (alb s). Proof. intros b Hb. exact (proj1 (proj2 (proj2 HR) b) Hb). Qed.
  Let HLB' : forall b, In b LB' -> In b (alb s). Proof. intros b Hb. apply lb_remove_In in Hb. exact (HLB b (proj1 Hb)). Qed.
  Let SPc : aceil <= spv. Proof. lia. Qed.
  Let HC24 : 0 <= c < kNumClasses. Proof. unfold c, kBatchClass, kNumClasses. lia. Qed.
  Let HC : 1 <= c <= 30. Proof. unfold c, kBatchClass. lia. Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  Let BND : 4096 <= TH /\ TH + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ sb mod 65536 = 0
            /\ 7241728 <= FSB /\ FSB + 11571200 <= aceil /\ (sb + 137438953472 + 4096 <= FSB \/ FSB + 11571200 <= sb) /\ (TH + 4096 <= FSB \/ FSB + 11571200 <= TH)
            /\ 7241728 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7241728 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384 /\ c = 24.
  Proof.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in F1; [| unfold AFS_SIZE; clear; lia]. apply aapp_env in G10; [| clear; lia]. apply aapp_env in G12; [| clear; lia].
    clear - Y1 Y2 Y3 T1 T2 T3 F1 F2 D6 D8 G10 G11 G12 G13 E1 E2. unfold TH, sb, FSB, P, CA, RI, a_ri, c. unfold a_sb, disj in *.
    acb. unfold AHI_LO, kSpaceSize, kPageSize, AFS_SIZE, kBatchClass in *. repeat split; lia.
  Qed.

  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ 7241728 <= ch_lo ch /\ ch_end ch <= aceil
            /\ ch_lo ch mod 8 = 0 /\ U mod 16 = 0 /\ 1 <= size /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size.
  Proof.
    pose proof (record_ext s OKs ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (chunk_geom s OKs ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (chunk_align s OKs ch CHIN) as (_ & _ & A3 & _).
    pose proof (record_band s OKs ch CHIN) as RB'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RB'. unfold AHI_LO in UHI.
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 A3 RB' UHI. subst U size. pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; lia)) as [UE _]. unfold AHI_LO, AIMG_TOP in *. repeat split; try assumption; lia.
  Qed.
  Lemma rec_vs_fsb : FSB + AFS_SIZE <= ch_lo ch \/ ch_end ch <= FSB.
  Proof.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D6 & _ & _ & _ & SEC & _).
    destruct (ch_primary ch) eqn:E.
    - pose proof (record_primary_space s OKs ch CHIN E) as [Q1 Q2]. subst FSB. clear - Q1 Q2 D6. unfold disj, kSpaceSize, kPageSize in *. lia.
    - destruct (record_secondary_map s OKs ch CHIN E) as (h & Hh & L0 & E0 & _). pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & _ & _ & _ & D).
      subst FSB. clear - L0 E0 D. unfold disj in *. lia.
  Qed.
  Lemma bsep_rec : forall A nn, In (A, nn) LB' -> bsep A nn (ch_lo ch) (ch_end ch).
  Proof.
    intros A nn Hin. apply lb_remove_In in Hin. destruct Hin as [Hin NEU]. cbn [fst] in NEU.
    destruct (alb_In s A nn (HLB _ Hin)) as (chA & HA & _ & EA & EN).
    assert (NE : chA <> ch) by (intros ->; apply NEU; symmetry; exact EA).
    pose proof (record_vs_record s OKs ch CHIN chA HA NE) as D.
    pose proof (record_ext s OKs chA HA) as (_ & _ & X3 & _ & _ & X6 & X7 & X8 & _). rewrite EA in X6, X7. rewrite EN in X7.
    unfold bsep. clear - D X3 X6 X7 X8. lia.
  Qed.

  Lemma head_frame : Forall (fun iv : ivl => apriv s LB' spv (fst iv) (snd iv)) Wh.
  Proof.
    pose proof BND as B0. pose proof EXT as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10). pose proof rec_vs_fsb as RF0.
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). destruct DFS as [FN FB].
    unfold Wh, free_head_W, depot_W.
    constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB' HLB'); exact LO|].
    constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB' HLB'); [| | | exact SPc]; unfold kPageSize; clear - B0; lia|].
    constructor; [cbn [fst snd]; apply (apriv_static s OKs LB' HLB'); [| exact SPc|]; unfold AIAINIT, AIMG_TOP; clear; lia|].
    constructor; [cbn [fst snd]; apply (apriv_static s OKs LB' HLB'); [| exact SPc|]; unfold AIAINST, AIMG_TOP; clear; lia|].
    constructor.
    { cbn [fst snd]. apply (apriv_app s OKs LB' HLB'); [apply (arng_sub _ _ _ _ (arng_of_aapp _ _ UHI)); [clear - E1; zlets; lia| clear - E8 E9; zlets; lia]| clear - E1 E3 E5 SPc; zlets; lia| |].
      - intros A nn Hin. apply (bsep_mono s A nn (ch_lo ch) (ch_end ch)); [clear - E1; zlets; lia| clear - E3; zlets; lia| exact (bsep_rec A nn Hin)].
      - clear - RF0 E1 E3. zlets. lia. }
    constructor.
    { cbn [fst snd]. apply (apriv_app s OKs LB' HLB'); [apply (arng_sub _ _ _ _ (arng_of_aapp _ _ UHI)); [clear - E1; zlets; lia| clear - E8 E9 E10; zlets; lia]| clear - E3 E5 SPc; zlets; lia| |].
      - intros A nn Hin. apply (bsep_mono s A nn (ch_lo ch) (ch_end ch)); [clear - E1; zlets; lia| clear - E3; zlets; lia| exact (bsep_rec A nn Hin)].
      - clear - RF0 E1 E3. zlets. lia. }
    constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB' HLB'); [| | | exact SPc]; unfold kPageSize; clear - B0; lia|].
    constructor.
    { cbn [fst snd]. replace (nsh size) with ((U + round_up size 8 - U) / 8) by (clear - E10; Z.div_mod_to_equations; lia).
      apply (apriv_shadow s OKs LB' HLB'); [apply (arng_sub _ _ _ _ (arng_of_aapp _ _ UHI)); [clear - E1; zlets; lia| clear - E1; zlets; lia]| clear - E8 E9; lia| clear - E7; Z.div_mod_to_equations; lia| exact SPc| |].
      - intros A nn Hin. apply (bsep_mono s A nn (ch_lo ch) (ch_end ch)); [clear - E1; zlets; lia| exact E2| exact (bsep_rec A nn Hin)].
      - clear - RF0 E1 E2. zlets. lia. }
    destruct (apriv_depot_statics s OKs LB' HLB' spv SPc) as [A1 A2].
    destruct (apriv_depot_blocks s OKs LB' HLB' spv (d_nb d) (d_sb d) G10 G12 G3 G4 G9 FN FB SPc) as [A3 A4].
    repeat constructor; cbn [fst snd]; assumption.
  Qed.

  Lemma app_frame : l <> [] -> lcount < kBatchCount -> Forall (fun iv : ivl => apriv s LB' spv (fst iv) (snd iv)) Wa.
  Proof.
    intros NE LT. pose proof BND as B0.
    pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & INlb & _ & CB & _ & LA1 & LA2 & _).
    fold st tq l lb LA lcount in INlb, CB, LA1, LA2.
    pose proof (batch_carved s OKs lb INlb) as (CV & _). pose proof (carved_in_space s OKs _ _ CV) as (CS1 & CS2 & _). fold st LA in CS1, CS2.
    change (class_size kBatchClass) with 8192 in CS2. change (a_sb s) with sb in CS1, CS2.
    unfold Wa.
    constructor; [cbn [fst snd]; apply (apriv_mono s LB' spv lo spv); [clear; lia| clear - HI; lia| apply (apriv_stack s OKs LB' HLB'); exact LO]|].
    constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB' HLB'); [| | | exact SPc]; unfold OT_TQ, kPageSize; clear - B0; lia|].
    constructor.
    { cbn [fst snd]. apply (apriv_app s OKs LB' HLB'); [apply arng_hi; [clear - LA1; lia| clear - LA2; unfold kBatchSize in *; lia]| clear - LA2 SPc; unfold kBatchSize in *; lia| |].
      - intros A nn Hin. apply (bsep_mono s A nn LA (LA + kBatchSize)); [clear; lia| unfold kBatchSize; clear; lia| exact (bsep_apiece s OKs LB' HLB' _ _ (ap_batch s lb INlb) A nn Hin)].
      - clear - CS1 CS2 B0. zlets. unfold kSpaceSize, AFS_SIZE in *. lia. }
    constructor.
    { cbn [fst snd]. apply (apriv_app s OKs LB' HLB'); [apply arng_hi; [clear - LA1 CB; lia| clear - LA2 LT; unfold kBatchSize, kBatchCount in *; lia]| clear - LA2 LT SPc; unfold kBatchSize, kBatchCount in *; lia| |].
      - intros A nn Hin. apply (bsep_mono s A nn LA (LA + kBatchSize)); [clear - CB; lia| unfold kBatchSize, kBatchCount in *; clear - LT; lia| exact (bsep_apiece s OKs LB' HLB' _ _ (ap_batch s lb INlb) A nn Hin)].
      - clear - CS1 CS2 B0 CB LT. zlets. unfold kSpaceSize, AFS_SIZE, kBatchCount in *. lia. }
    constructor.
  Qed.

  Lemma new_frame : forall B, need_new tq = true -> apriv s LB' spv B (B + kBatchSize) ->
    Forall (fun iv : ivl => apriv s LB' spv (fst iv) (snd iv)) (enq_new_W lo spv TH B LA).
  Proof.
    intros B NN BP. pose proof BND as B0.
    unfold enq_new_W.
    constructor; [cbn [fst snd]; apply (apriv_mono s LB' spv lo spv); [clear; lia| clear - HI; lia| apply (apriv_stack s OKs LB' HLB'); exact LO]|].
    constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB' HLB'); [| | | exact SPc]; unfold kPageSize; clear - B0; lia|].
    constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB' HLB'); [| | | exact SPc]; unfold kPageSize; clear - B0; lia|].
    constructor; [cbn [fst snd]; apply (apriv_mono s LB' spv B (B + kBatchSize)); [clear; lia| unfold kBatchSize; clear; lia| exact BP]|].
    constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB' HLB'); [| | | exact SPc]; unfold kPageSize; clear - B0; lia|].
    constructor; [cbn [fst snd]| constructor].
    assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]).
    destruct D as [EL|NE].
    - replace LA with 0 by (unfold LA, lb; rewrite EL; reflexivity). apply (apriv_static s OKs LB' HLB'); [unfold AIMG_TOP; clear; lia| exact SPc| clear; lia].
    - pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & INlb & _ & _ & _ & LA1 & LA2 & _). fold st tq l lb LA in INlb, LA1, LA2.
      pose proof (batch_carved s OKs lb INlb) as (CV & _). pose proof (carved_in_space s OKs _ _ CV) as (CS1 & CS2 & _). fold st LA in CS1, CS2.
      change (class_size kBatchClass) with 8192 in CS2. change (a_sb s) with sb in CS1, CS2.
      apply (apriv_app s OKs LB' HLB'); [apply arng_hi; [clear - LA1; lia| clear - LA2; unfold kBatchSize in *; lia]| clear - LA2 SPc; unfold kBatchSize in *; lia| |].
      + intros A nn Hin. apply (bsep_mono s A nn LA (LA + kBatchSize)); [clear; lia| unfold kBatchSize; clear; lia| exact (bsep_apiece s OKs LB' HLB' _ _ (ap_batch s lb INlb) A nn Hin)].
      + clear - CS1 CS2 B0. zlets. unfold kSpaceSize, AFS_SIZE in *. lia.
  Qed.

  Lemma hit_slot : pc_count (get_pc st c) <> 0 -> apriv s LB' spv B1 (B1 + kBatchSize).
  Proof.
    intros HIT.
    assert (HIN : In cp1 (pc_chunks (get_pc st c))).
    { pose proof (co_count _ _ (WF_cache st c WFs HC24)) as CC. unfold cp1. destruct (pc_chunks (get_pc st c)) as [|x q]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
    change kBatchSize with (class_size c). exact (apriv_freech s OKs LB' HLB' spv c cp1 HC24 (or_intror HIN) SPc).
  Qed.

  Section RefillFrame.
    Hypothesis MISS : pc_count (get_pc st c) = 0.
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
      destruct BND as (_ & _ & _ & _ & SB64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & EFA & C24).
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

    Ltac thr B0 B1 := apply (apriv_thread s OKs LB' HLB'); [| | | assumption]; cbn [fst snd]; unfold kPageSize; clear - B0 B1; lia.
    Lemma refill_frame : Forall (fun iv : ivl => apriv s LB' spv (fst iv) (snd iv)) WR.
    Proof.
      pose proof BND as B0. pose proof BR as BQ. pose proof ALN as (M1 & M2 & M3). pose proof SPc as SP0.
      unfold WR, rf_W.
      constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB' HLB'); exact LO|].
      constructor; [cbn [fst snd]; thr B0 B0|].
      constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB' HLB'); exact LO|].
      constructor; [cbn [fst snd]; thr B0 B0|].
      constructor; [cbn [fst snd]; thr B0 B0|].
      do 5 (constructor; [cbn [fst snd]; apply (apriv_rinfo s OKs LB' HLB'); [| | |assumption]; unfold a_ri, kSpaceSize, kPageSize; clear - B0; zlets; unfold a_sb in *; lia|]).
      constructor. { cbn [fst snd]. apply (apriv_region_hi s OKs LB' HLB' _ c); [exact HC24| | | |assumption]; change (rg_allocated_user (get_region (a_st s) c)) with au; unfold kRegionSize; clear - B0 BQ; lia. }
      constructor. { cbn [fst snd]. apply (apriv_region_hi s OKs LB' HLB' _ c); [exact HC24| | | |assumption]; change (rg_allocated_user (get_region (a_st s) c)) with au; unfold kRegionSize; clear - B0 BQ; lia. }
      constructor. { cbn [fst snd]. replace ((mfa' - mfa) / 8) with ((FA s c + mfa' - (FA s c + mfa)) / 8) by (f_equal; clear; lia).
                     apply (apriv_region_hi_sh s OKs LB' HLB' _ c); [exact HC24| | | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize; clear - B0 BQ M2; lia. }
      constructor. { cbn [fst snd]. replace ((mu' - mu) / 8) with ((RB s c + mu' - (RB s c + mu)) / 8) by (f_equal; clear; lia).
                     apply (apriv_region_hi_sh s OKs LB' HLB' _ c); [exact HC24| | | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize; clear - B0 BQ M1; lia. }
      constructor; [cbn [fst snd]; thr B0 B0|].
      eapply Forall_impl; [| apply icW_inside]. intros [x y] (I1 & I2 & I3). cbn [fst snd] in I1, I2, I3 |- *. pose proof (conj I1 (conj I2 I3)) as II. thr B0 II.
    Qed.

    Lemma refill_slot : apriv s LB' spv B2 (B2 + kBatchSize) /\ apriv s LB' spv (sh B2) (sh B2 + kBatchSize / 8).
    Proof.
      pose proof BND as B0. pose proof BR as BQ. pose proof ALN as (M1 & M2 & M3). pose proof SPc as SP0.
      pose proof RF as (Q1 & Q2 & _). fold st r in Q1, Q2. fold nf mfa au mu fl n in Q1, Q2. fold mu' nnew nf1 fl1 in Q1, Q2.
      assert (HIN : In cp2 fl1).
      { assert (L : length chunks2 = Z.to_nat n) by (unfold chunks2; rewrite length_firstn; unfold zlen in Q2; clear - Q1 Q2 BQ; lia).
        unfold cp2. rewrite <- (firstn_skipn (Z.to_nat n) fl1). fold chunks2. apply in_or_app. left.
        destruct chunks2 as [|x q] eqn:E; [exfalso; cbn in L; clear - L BQ; lia| left; reflexivity]. }
      unfold fl1, rf_fl1 in HIN. fold n nnew in HIN. change (class_size c) with 8192 in HIN. apply in_app_or in HIN. destruct HIN as [HIN|HIN].
      -   apply in_carve_asc in HIN. destruct HIN as (j & Hj & Ecp).
        assert (EAB : B2 = RB s c + au + j * 8192).
        { unfold B2. rewrite compact_to_addr_eq. change (region_beg st2 c) with (region_beg st c). change (region_beg st c) with (RB s c). rewrite Ecp.
          replace (au + (0 + j) * 8192) with (((au + j * 8192) / 16) * 16) by (clear - M3 Hj; Z.div_mod_to_equations; lia).
          rewrite shiftr4_mul16. clear - M3 Hj. Z.div_mod_to_equations. lia. }
        rewrite Z2Nat.id in Hj by (clear - BQ; lia).
        assert (ABR : RB s c + au <= B2 /\ B2 + 8192 <= RB s c + au' /\ B2 mod 8 = 0).
        { rewrite EAB. destruct BQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EAU). rewrite EAU. clear - Hj M3 B0. split; [lia|]. split; [nia|]. Z.div_mod_to_equations. lia. }
        split.
        + apply (apriv_region_hi s OKs LB' HLB' _ c); [exact HC24| | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize, kBatchSize; clear - B0 BQ ABR; lia.
        + replace (kBatchSize / 8) with ((B2 + 8192 - B2) / 8) by (unfold kBatchSize; f_equal; clear; lia).
          apply (apriv_region_hi_sh s OKs LB' HLB' _ c); [exact HC24| | | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize; clear - B0 BQ ABR; lia.
      -
        assert (EB : B2 = compact_to_addr st c cp2) by reflexivity.
        rewrite EB. change kBatchSize with (class_size c). split.
        + exact (apriv_freech s OKs LB' HLB' spv c cp2 HC24 (or_introl HIN) SPc).
        + exact (apriv_freech_sh s OKs LB' HLB' spv c cp2 HC24 (or_introl HIN) SPc).
    Qed.
  End RefillFrame.
End FreeFrame.
End HCW.

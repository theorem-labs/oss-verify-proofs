(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_LargeAlloc1 AW_InitCache AW_IAInit AW_FreePre
     AW_Refill AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AS_Free3 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_ColdModel AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 AG_MallocCold
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_Free7 AG_Free8 SecLazy AG_FreeModel2 AG_Free3 AG_Free5 AG_RepQ AS_Free4 AW_Enqueue2 AG_WriteSet
     AW_PutR1 AW_EnqueueR1 AW_EnqueueR2 AW_PutR2 AS_FreeR1 AS_FreeR2 AS_FreeR3 AS_FreeR4 AG_FreeR3 AG_FreeMid.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).


Section FreeAppMidR.
  Context {HCEIL : HeapCeil}.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Variables (sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (ch : chunk) (bs sbs : list byte).
  Variables (T : list Z) (rest : list word) (RF : mem -> Prop).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  Let lcount := qb_count lb.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let tq' := tq_app tq (ch_chunk_beg ch) size.
  Let lb' := mkQB LA (qb_size lb + size) (lcount + 1) (qb_chunks lb ++ [ch_chunk_beg ch]).
  Let s' := free_s' s ch tq' (as_cache st) (a_L s) (a_S s) (a_AL s).
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let Wa : list ivl := [(lo, bv_unsigned sp + -2288); (TH + OT_TQ + 24, TH + OT_TQ + 32); (LA + 8, LA + 24); (LA + 24 + 8 * lcount, LA + 32 + 8 * lcount)].
  Let W : list ivl := Wh ++ Wa.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -2208).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3024 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis NR : (1 <= length T <= 30)%nat. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis LR : length rest = (255 - length T)%nat.
  Hypothesis RFT : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 -> disjoint_from W0 (bv_unsigned sp + -2208) 2208 ->
                   disjoint_from W0 (TH + 3168) 1 -> disjoint_from W0 AIAINIT 4 -> disjoint_from W0 AIAINST 0x81030 -> RF m1.
  Hypothesis RFE : forall m0, RF m0 ->
       rw_cells asegs m0 (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m0 (bv_unsigned sp + -2136 + 16) (map wz T ++ rest).
  Hypothesis RFX : forall m0, RF m0 ->
       rw_cells asegs m0 (TH + 3168) [C1 (b8 0)] /\ rw_cells asegs m0 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m0.
  Hypothesis RFP : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 ->
      (forall a, bv_unsigned sp + -2208 <= a < bv_unsigned sp -> outside W0 a) -> outside W0 (TH + 3168) ->
      (forall a, AIAINIT <= a < AIAINIT + 4 -> outside W0 a) -> (forall a, AIAINST <= a < AIAINST + 0x81030 -> outside W0 a) -> RF m1.
  Hypothesis RF0 : RF m.
  (* [comment removed for export] *)
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : l <> [] /\ lcount < kBatchCount.
  (* [comment removed for export] *)

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. destruct RR as (_ & _ & FL & _).
    destruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ 12599296 <= ch_lo ch /\ ch_end ch <= aceil
            /\ ch_lo ch mod 8 = 0 /\ ch_end ch mod 8 = 0 /\ ch_alloc_beg ch + ch_rz ch = U /\ 16 <= ch_rz ch /\ ch_lo ch <= ch_alloc_beg ch.
  Proof.
    pose proof (record_ext s OK ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    pose proof (record_band s OK ch CHIN) as RB'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RB'. unfold AHI_LO in UHI.
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 RB' UHI. subst U size. pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; lia)) as [UE _]. unfold AHI_LO, AIMG_TOP in *. repeat split; try assumption; lia.
  Qed.
  Let LAST := free_last_cells s m ch d R CHIN DPL (proj1 NN).

  (* [comment removed for export] *)
  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12599296 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 12599296 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 12599312 <= U /\ U + round_up size 8 <= aceil /\ 1 <= size /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size
            /\ 0x10007fff8000 <= LA /\ LA + 8192 <= aceil /\ 1 <= lcount <= 1020
            /\ 2148314624 <= sh U /\ sh U + nsh size <= 0x10007fff8000 /\ U mod 16 = 0 /\ lo + 3024 <= bv_unsigned sp.   (* [comment removed for export] *)
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & _).
    pose proof LAST as (_ & _ & _ & _ & _ & CNB & _ & L1 & L2 & _).
    pose proof PL as (_ & _ & _ & P1 & P2 & P3 & _). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4).
    pose proof (proj2 NN) as NN2.
    apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia]. apply aapp_env in N1; [| clear; lia]. apply aapp_env in N3; [| clear; lia].
    clear - Z1 Z2 Z3 Z4 Z5 Z6 Y1 Y2 Y4 Y5 X1 X2 CNB L1 L2 P2 P3 N1 N2 N3 N4 LO NN2 HI.
    subst U size LA lcount lb l tq TH CTX sb st. unfold AHI_LO, AIMG_TOP, kSpaceSize, kPageSize, kPtrArrayReserve, kBatchSize, kBatchCount in *.
    destruct Z2 as (ZA & _ & ZB). unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in ZA, ZB.   (* [comment removed for export] *)
    assert (SH : 2148314624 <= sh (ch_user_beg ch) /\ sh (ch_user_beg ch) + nsh (ch_used ch) <= 0x10007fff8000).
    { acb. clear - ZA Z3 Z6 Z1 ACEILB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    clear ZA. repeat match goal with |- _ /\ _ => split end; try lia.
  Qed.

  (* [comment removed for export] *)
  Definition free_app_gmidR : machine_state -> Prop := fun ms' =>
    exists (b1 actx : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
       ms' = MS (enq_regsR sp gp tp s7 s8 s9 s10 s11 U size TH kMaxCacheSize t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x19b46c) fc None m' (seg_rom asegs)
    /\ free_common_midR sp cs0 cs2 cs3 cs4 cs5 s6 m m' W lo U size b1 actx TH T d RF
    /\ ARHEAPQ s' [] [] (lb_remove U LB) m'
    /\ DEPOT asegs d' m'
    /\ (exists stX ev0 ev2, am_free_full st U = free_tail_m U size stX ev0 ev2 /\ same_but_shadow stX (a_st s') /\ syscalls_of ev0 = []).

  Theorem free_arep_app_midR :
    evt asegs free_app_gmidR
      (MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp x3 x4 x5 cs0 (wz U) (wz AINST) (wz U) (wz 0) (wz 0)
               (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) x12 x13 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 x14 x15 x16 x17)
          F (Z_to_bv 64 0x196ae8) fc None m (seg_rom asegs)).
  Proof.
    pose proof BND as B.
    destruct (free_cells s m ch R CHIN ALLOC UHI) as (b1 & actx & q0 & q1 & q2 & q3 & HDR & Hb1 & ACR & TST & UNW & QC & TQ & QST & INST & IEN).
    pose proof LAST as (LBc & LCHK & LJ & INlb & CNT & CNB & K1 & LA1 & LA2 & LA16 & LAT & LAU & LAD1 & LAD2 & _ & _ & LSZ & QR & HD0).
    fold st tq l lb LA lcount TH U size in LBc, LCHK, LJ, CNT, CNB, LA1, LA2, LA16, LAT, LAU, LAD1, LAD2, LSZ, QR, HD0, TQ.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    pose proof (free_plu s m ch d R CHIN DPL) as PLU.
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof SHB as [[_ [_ SHu]] SBS].
    (* [comment removed for export] *)
    assert (UB : exists ub, rw_cells asegs m U [CB 8 ub]).
    { pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _). pose proof (CHR ch CHIN) as (_ & _ & STI & JR & _).
      rewrite ALLOC in STI. fold U size in JR. pose proof EXT as (_ & _ & E3 & _ & E5 & _).
      pose proof (stk_of_rw_cells asegs _ _ _ BLK) as SK. cbn [cells_size csize Nat.add] in SK.
      replace (U + Z.of_nat (Z.to_nat size + 0)) with (U + size) in SK by (clear - B; lia).
      destruct (Z.le_gt_cases 8 size) as [LE|GT].
      - destruct (stk_split asegs _ _ (U + 8) _ SK ltac:(clear - LE; lia)) as [SK1 _]. destruct (stk_cells _ _ _ SK1 ltac:(clear - LE; lia)) as [ub Hub].
        exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - LE; lia). exact Hub.
      - pose proof (junk_stk' _ _ _ JR ltac:(clear - B; lia) ltac:(clear - B E5; acb; lia) ltac:(clear - GT E3; lia)) as SJ.
        replace (U + size + (ch_end ch - (U + size))) with (ch_end ch) in SJ by (clear - GT; lia).
        destruct (stk_split asegs _ _ (U + 8) _ SJ ltac:(clear - GT E3 B; lia)) as [SJ1 _].
        pose proof (stk_merge asegs _ _ _ _ SK SJ1 ltac:(clear - GT B; lia)) as SK8.
        destruct (stk_cells _ _ _ SK8 ltac:(clear - GT; lia)) as [ub Hub]. exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - GT; lia). exact Hub. }
    destruct UB as [ub UB].
    eapply evt_mono.
    { eapply (@free_append_midR _ sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m lo d
                ATSD CTX TH (a_top s) (a_bot s) sb U size b1 actx ub kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize sbs
                k (hd 0 (map qb_addr l)) LA (qc_bytes tq) T rest RF) with (lsize := qb_size lb) (lcount := lcount) (lchunks := qb_chunks lb).
      - exact LO.
      - exact HI.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _ & pX2 & pX3 & _). fold TH in pT1, pT2, pT3. fold CTX in pX2, pX3.
        unfold kPageSize in pT1, pT2, pT3. split; [clear; lia|]. split; [clear; lia|]. split; [exact pX2|]. split; [exact pX3|]. split; [exact pT2|]. split; [exact pT3|].
        clear - pT1. zlets. Z.div_mod_to_equations. lia.
      - constructor. unfold kSpaceSize. clear - X4 X5 Y6. zlets. unfold kSpaceSize in *. lia.
      - constructor. unfold disj, kSpaceSize, kPageSize in G1, G2, G3, G4, G5, G6. fold TH in G1, G2. fold sb in G3, G4. fold CTX in G5, G6.
        pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & dN1 & _ & dN3 & _).   (* [comment removed for export] *)
        repeat match goal with |- _ /\ _ => split end; try exact dN1; try exact dN3; clear - G1 G2 G3 G4 G5 G6 B; zlets; unfold kSpaceSize; lia.
      - constructor. exact PLU.
      - constructor. clear - V1 V2. zlets. unfold kPageSize in V1. lia.
      - exact DLO.
      - exact DCAP.
      - constructor. clear - Z1 Z2 Z3 Z4 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - clear - Z1 QSZ. zlets. lia.
      - exact Hb1.
      - exact ACR.
      - clear - QSZ. zlets. unfold kMaxCacheSize, kQuarantineMaxSize, kQuarantineMinSize in *. lia.
      - exact SBS.
      - pose proof (batches_len_bound s m R) as BL. clear - K3 BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - exact NR.
      - exact TRNG.
      - exact LR.
      - exact RFT.
      - exact RFE.
      - rewrite TP. exact IEN.
      - exact MI.
      - exact ST.
      - exact RF0.
      - exact DEP.
      - exact HDR.
      - exact UB.
      - exact TST.
      - exact QC.
      - exact SHu.
      - exact TQ.
      - exact K1.
      - constructor. clear - LA1 LA2 LA16 LAT. zlets. unfold kBatchSize, AHI_LO in *. repeat split; lia.
      - constructor. unfold kBatchSize. exact (conj LAU (conj LAD1 LAD2)).
      - clear - CNT CNB NN. zlets. unfold kBatchCount in *. zlets. lia.
      - exact LBc.
      - exact LCHK.
      - unfold kBatchSize. replace (LA + 8192) with (LA + kBatchSize) by reflexivity. exact LJ. }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & FC & TQ4 & LB4 & LCHK4 & LJ4).
    pose proof FC as (MU & WM & MI' & ST' & PFR' & RF' & HDR' & UW' & TST' & DEP' & SHF').
    destruct (RFX _ RF') as (UNW' & FLG' & IA').
    unfold free_app_gmidR. exists b1, actx. do 15 eexists. split; [unfold kMaxCacheSize; reflexivity|]. split; [exact FC|].
    split.
    { split; [| split; [apply lb_remove_nodup; exact (proj1 (proj2 HR))|]].
      - eapply (AG_FreeR3.arepq_after_app sp m s LB d lo ch bs sbs T rest HR CHIN ALLOC DPL LO HI NR LR BLK NN UHI m' b1 actx MU WM Hb1 HDR' UW' TST' UNW' FLG' IA' SHF' TQ4 LB4 LCHK4).
        unfold kBatchSize. exact LJ4.
      - intros b. destruct HR as (_ & ND & LBs). rewrite lb_remove_In, LBs. unfold alb. change (a_st s') with (free_st' s ch tq' (as_cache st)). rewrite !in_map_iff. split.
        + intros ((x & E & Hx) & NEU). apply filter_In in Hx. destruct Hx as [Hx AX]. exists x. split; [exact E|]. apply filter_In. split; [| exact AX].
          apply (free_old_in s ch m tq' (as_cache st) R CHIN x Hx). intros ->. apply NEU. rewrite <- E. reflexivity.
        + intros (x & E & Hx). apply filter_In in Hx. destruct Hx as [Hx AX]. apply (free_cl s ch m tq' (as_cache st) R CHIN) in Hx.
          destruct Hx as [->|[Hx NEU]]; [cbn in AX; discriminate AX|].
          split; [exists x; split; [exact E| apply filter_In; split; [exact Hx| exact AX]]|]. rewrite <- E. cbn [fst]. exact NEU. }
    split; [exact DEP'|].
    (* [comment removed for export] *)
    pose proof PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QMx & _ & QCx & _).
    assert (NNf : need_new tq = false) by exact (need_new_false tq (proj1 NN) (proj2 NN)).
    assert (IM : forall a, U - 16 <= a -> a + 1 <= U + round_up size 8 -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply (aim_of_aapp _ _ a UHI); clear - Ha Hb; zlets; lia. }   (* [comment removed for export] *)
    destruct (am_free_app_gen st ch (free_find st ch WFs CHIN) ALLOC ltac:(rewrite QMx, QCx; unfold kMaxCacheSize; clear - QSZ; lia)
                ltac:(change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); clear - B; Z.div_mod_to_equations; lia)
                ltac:(apply IM; clear - B; zlets; unfold AHI_LO; lia)
                ltac:(apply IM; clear - B; zlets; unfold AHI_LO; lia) NNf) as (stX & ev0 & E & SBX & SC).
    exists stX, ev0, []. split; [exact E|]. split; [exact SBX| exact SC].
  Qed.
End FreeAppMidR.

(* [comment removed for export] *)
Section FreeNewHitMidR.
  Context {HCEIL : HeapCeil}.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Variables (sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (ch : chunk) (bs sbs : list byte).
  Variables (T : list Z) (rest : list word) (RF : mem -> Prop).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  Let pc := get_pc st kBatchClass.
  Let cnt := pc_count pc.
  Let chunks := pc_chunks pc.
  Let cp := hd 0 chunks.
  Let B := compact_to_addr st kBatchClass cp.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st) (zidx kBatchClass) (mkPC (cnt - 1) (tl chunks)).
  Let s' := free_s' s ch tq' cache' (a_L s) (a_S s) (a_AL s).
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let Wn : list ivl := enq_newR_W lo (bv_unsigned sp) TH B LA.
  Let W : list ivl := Wh ++ Wn.
  Let Wf : list ivl := Wh ++ enq_new_W lo (bv_unsigned sp) TH B LA.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -2208).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3024 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis NR : (1 <= length T <= 30)%nat. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis LR : length rest = (255 - length T)%nat.
  Hypothesis RFT : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 -> disjoint_from W0 (bv_unsigned sp + -2208) 2208 ->
                   disjoint_from W0 (TH + 3168) 1 -> disjoint_from W0 AIAINIT 4 -> disjoint_from W0 AIAINST 0x81030 -> RF m1.
  Hypothesis RFE : forall m0, RF m0 ->
       rw_cells asegs m0 (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m0 (bv_unsigned sp + -2136 + 16) (map wz T ++ rest).
  Hypothesis RFX : forall m0, RF m0 ->
       rw_cells asegs m0 (TH + 3168) [C1 (b8 0)] /\ rw_cells asegs m0 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m0.
  Hypothesis RFP : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 ->
      (forall a, bv_unsigned sp + -2208 <= a < bv_unsigned sp -> outside W0 a) -> outside W0 (TH + 3168) ->
      (forall a, AIAINIT <= a < AIAINIT + 4 -> outside W0 a) -> (forall a, AIAINST <= a < AIAINST + 0x81030 -> outside W0 a) -> RF m1.
  Hypothesis RF0 : RF m.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : need_new tq = true.
  Hypothesis HIT : cnt <> 0.
  (* [comment removed for export] *)

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. destruct RR as (_ & _ & FL & _).
    destruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let HC24 : 0 <= kBatchClass < kNumClasses. Proof. unfold kBatchClass, kNumClasses. lia. Qed.
  Let PCS : pc_chunks (get_pc st kBatchClass) = cp :: tl chunks.
  Proof.
    pose proof (co_count _ _ (WF_cache st kBatchClass WFs HC24)) as C1. fold pc cnt chunks in C1.
    unfold cp. fold pc. fold chunks. destruct chunks as [|x r] eqn:E; [| reflexivity]. exfalso. apply HIT. rewrite C1. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition free_newhit_gmidR : machine_state -> Prop := fun ms' =>
    exists (b1 actx : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
       ms' = MS (enq_regsR sp gp tp s7 s8 s9 s10 s11 U size TH kMaxCacheSize t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x19b46c) fc None m' (seg_rom asegs)
    /\ free_common_midR sp cs0 cs2 cs3 cs4 cs5 s6 m m' W lo U size b1 actx TH T d RF
    /\ ARHEAPQ s' [] [] (lb_remove U LB) m'
    /\ DEPOT asegs d' m'
    /\ (exists stX ev0 ev2, am_free_full st U = free_tail_m U size stX ev0 ev2 /\ same_but_shadow stX (a_st s') /\ syscalls_of ev0 = []).

  Theorem free_arep_newhit_midR :
    evt asegs free_newhit_gmidR
      (MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp x3 x4 x5 cs0 (wz U) (wz AINST) (wz U) (wz 0) (wz 0)
               (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) x12 x13 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 x14 x15 x16 x17)
          F (Z_to_bv 64 0x196ae8) fc None m (seg_rom asegs)).
  Proof.
    destruct (free_cells s m ch R CHIN ALLOC UHI) as (b1 & actx & q0 & q1 & q2 & q3 & HDR & Hb1 & ACR & TST & UNW & QC & TQ & QST & INST & IEN).
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    pose proof (free_plu s m ch d R CHIN DPL) as PLU.
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof SHB as [[_ [_ SHu]] SBS].
    (* [comment removed for export] *)
    destruct (hit_cells_of_arep s m R kBatchClass ltac:(unfold kBatchClass, kNumClasses; (first [clear - R UHI CHIN; lia | lia])) HIT)
      as (j0 & j1 & j2 & j3 & PC1 & PC2 & PC3 & PC4 & QST' & BJ & _ & _ & _ & CC & CR & CPS & AB1 & AB2 & INI).
    cbv zeta in PC1, PC2, PC3, PC4, BJ, CC, CR, CPS, AB1, AB2. fold st pc cnt chunks cp in PC1, PC2, PC3, PC4, BJ, CC, CR, CPS, AB1, AB2.
    assert (EB : B = sb + kBatchClass * 2 ^ 32 + cp * 16) by (unfold B, sb, a_sb; rewrite compact_to_addr_eq, region_beg_eq; reflexivity).
    assert (EP : a_cache s + 80 * kBatchClass = TH + 2128) by (unfold a_cache, OT_CACHE, kBatchClass; zlets; lia).
    rewrite EP in PC1, PC2, PC3, PC4. rewrite <- EB in BJ, AB1, AB2. change (class_size kBatchClass) with 8192 in PC2, BJ, AB2.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in PC1. destruct PC1 as [PC1 _].
    pose proof (co_bound _ _ (WF_cache st kBatchClass WFs HC24)) as CB2. fold pc cnt in CB2.
    (* [comment removed for export] *)
    pose proof (carved_cache st kBatchClass cp WFs HC24 ltac:(rewrite PCS; left; reflexivity)) as CVB. fold B in CVB.
    pose proof (carved_vs_thread s OK _ _ CVB) as BT. pose proof (carved_vs_depot s OK _ _ CVB d DPL) as [BD1 BD2].
    pose proof (freech_vs_record s OK ch CHIN kBatchClass cp HC24 ltac:(right; rewrite PCS; left; reflexivity)) as BU.
    pose proof (record_ext s OK ch CHIN) as (E1 & E2 & E3 & _ & _ & E6 & E7 & E8 & _). change (class_size kBatchClass) with 8192 in BT, BD1, BD2, BU.
    (* [comment removed for export] *)
    assert (UB : exists ub, rw_cells asegs m U [CB 8 ub]).
    { pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _). pose proof (CHR ch CHIN) as (_ & _ & STI & JR & _).
      rewrite ALLOC in STI. fold U size in JR.
      pose proof (stk_of_rw_cells asegs _ _ _ BLK) as SK. cbn [cells_size csize Nat.add] in SK.
      replace (U + Z.of_nat (Z.to_nat size + 0)) with (U + size) in SK by (clear - Z1; zlets; lia).
      destruct (Z.le_gt_cases 8 size) as [LE|GT].
      - destruct (stk_split asegs _ _ (U + 8) _ SK ltac:(clear - LE; lia)) as [SK1 _]. destruct (stk_cells _ _ _ SK1 ltac:(clear - LE; lia)) as [ub Hub].
        exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - LE; lia). exact Hub.
      - pose proof (junk_stk' _ _ _ JR ltac:(clear - Z1 Z2; zlets; destruct Z2 as (_ & _ & ZT); unfold AIMG_TOP in ZT; lia) ltac:(clear - E2 E7 Z1 Z5; zlets; acb; lia) ltac:(clear - GT E7 Z5 Z6; zlets; lia)) as SJ.
        replace (U + size + (ch_end ch - (U + size))) with (ch_end ch) in SJ by (clear - GT; lia).
        destruct (stk_split asegs _ _ (U + 8) _ SJ ltac:(clear - GT E7 Z1 Z5 Z6; zlets; lia)) as [SJ1 _].
        pose proof (stk_merge asegs _ _ _ _ SK SJ1 ltac:(clear - GT Z1; zlets; lia)) as SK8.
        destruct (stk_cells _ _ _ SK8 ltac:(clear - GT; lia)) as [ub Hub]. exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - GT; lia). exact Hub. }
    destruct UB as [ub UB].
    eapply evt_mono.
    { eapply (@free_newhit_midR _ sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m lo d
                ATSD CTX TH (a_top s) (a_bot s) sb U size b1 actx ub kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize sbs
                k (hd 0 (map qb_addr l)) LA (qc_bytes tq) T rest RF) with (cnt := cnt) (chunks := chunks) (B := B) (j0 := j0) (j1 := j1) (j2 := j2) (j3 := j3).
      - exact LO.
      - exact HI.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _ & pX2 & pX3 & _). fold TH in pT1, pT2, pT3. fold CTX in pX2, pX3.
        unfold kPageSize in pT1, pT2, pT3. split; [clear; lia|]. split; [clear; lia|]. split; [exact pX2|]. split; [exact pX3|]. split; [exact pT2|]. split; [exact pT3|].
        clear - pT1. zlets. Z.div_mod_to_equations. lia.
      - constructor. clear - X4 X5 Y6. zlets. unfold kSpaceSize in *. lia.
      - constructor. repeat match goal with |- _ /\ _ => split end; try exact G10; try exact G12;   (* [comment removed for export] *)
          clear - G1 G2 G3 G4 G5 G6; zlets; unfold a_sb, kSpaceSize, kPageSize, disj in *; lia.
      - constructor. exact PLU.
      - constructor. clear - V1 V2. unfold kPageSize in V1. lia.
      - exact DLO.
      - exact DCAP.
      - constructor. clear - Z1 Z2 Z3 Z4 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - clear - Z1 QSZ. zlets. lia.
      - exact Hb1.
      - exact ACR.
      - clear - QSZ. zlets. unfold kMaxCacheSize, kQuarantineMaxSize, kQuarantineMinSize in *. lia.
      - exact SBS.
      - pose proof (batches_len_bound s m R) as BL. clear - K3 BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - exact NR.
      - exact TRNG.
      - exact LR.
      - exact RFT.
      - exact RFE.
      - rewrite TP. exact IEN.
      - exact MI.
      - exact ST.
      - exact RF0.
      - exact DEP.
      - exact HDR.
      - exact UB.
      - exact TST.
      - exact QC.
      - exact SHu.
      - exact TQ.
      - constructor. clear - X1 X2 X3. zlets. repeat split; assumption.
      - exact CC.
      - clear - CC CB2 HIT INI. zlets. rewrite INI in CB2. change (max_count kBatchClass) with 2 in CB2. unfold zlen in *. lia.
      - exact CPS.
      - exact EB.
      - constructor. clear - AB1 AB2 X1 X2 BT. zlets. unfold a_sb, AHI_LO, kBatchSize, kSpaceSize, kPageSize in *. lia.
      - constructor. clear - BU BD1 BD2 E1 E3 E6 E7 E8 Z1 Z5 Z6. zlets. unfold kBatchSize in *. lia.
      - (* [comment removed for export] *)
        intros NZ. assert (NE : l <> []) by (intros EL; apply NZ; unfold k; rewrite EL; reflexivity).
        pose proof (free_last_cells s m ch d R CHIN DPL NE) as (LBc & _ & _ & INlb & CNT' & CB' & _ & LA1 & LA2 & _ & LAT & LAU & LAD1 & LAD2 & _).
        pose proof (need_new_true_full tq NN NE) as FULL. fold l lb in FULL.
        pose proof (carved_vs_batch s OK _ _ CVB lb INlb ltac:(hci; apply (batch_not_free s OK lb kBatchClass cp INlb HC24); right; rewrite PCS; left; reflexivity)) as BL.
        change (class_size kBatchClass) with kBatchSize in BL. fold st tq l lb LA in LBc, LA1, LA2, LAT, LAU, LAD1, LAD2, BL, CB', FULL |- *.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_; _])) in LBc. destruct LBc as [LB1 LB23]. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in LB23. destruct LB23 as [_ LB3].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LB3.
        replace (qb_count lb) with kBatchCount in LB3 by (clear - CB' FULL; lia).
        split; [split; [exact LB1| replace (LA + 16) with (LA + 8 + 8) by (clear; lia); exact LB3]|].
        clear - LA1 LA2 LAT LAU LAD1 LAD2 BL. zlets. unfold kBatchSize, AHI_LO in *. repeat split; lia.
      - intros K0'. assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]).
        destruct D as [EL|NE]; [unfold LA, lb; rewrite EL; reflexivity|].
        exfalso. pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & _ & _ & _ & K1 & _). clear - K0' K1. zlets. lia.
      - exact PC1.
      - replace (TH + 2136) with (TH + 2128 + 8) by (clear; lia). exact PC2.
      - replace (TH + 2144) with (TH + 2128 + 16) by (clear; lia). exact PC3.
      - replace (TH + 2144) with (TH + 2128 + 16) by (clear; lia). replace (TH + 2208) with (TH + 2128 + 80) by (clear; lia). exact PC4.
      - replace (TH + 2768) with (TH + 208 + 2560) by (clear; lia). exact QST'.
      - exact INST.
      - exact BJ. }
    intros ms' PO.
    destruct PO as (j2' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & FC & TQ4 & LA4 & NB4 & NBJ4 & PC14 & PC34 & PC44 & ST4).
    pose proof FC as (MU & WM & MI' & ST' & PFR' & RF' & HDR' & UW' & TST' & DEP' & SHF').
    destruct (RFX _ RF') as (UNW' & FLG' & IA').
    assert (SUBW : sub_fp W Wf).
    { unfold W, Wf, Wn, enq_newR_W, enq_new_W. intros x Hx. apply outside_app in Hx. destruct Hx as [H1 H2]. apply outside_app. split; [exact H1|].
      cbn [outside] in H2 |- *. destruct H2 as (A1 & A2). split; [clear - A1; lia| exact A2]. }
    unfold free_newhit_gmidR. exists b1, actx. do 15 eexists. split; [unfold kMaxCacheSize; reflexivity|]. split; [exact FC|].
    assert (W0 : WF (set_internal_init st)) by (eapply WF_ext; [ .. | exact WFs]; reflexivity).
    pose proof (WFQ_free_new (set_internal_init st) ch W0 CHIN ALLOC cp (tl chunks) PCS) as WQ'.
    split.
    { split; [| split; [apply lb_remove_nodup; exact (proj1 (proj2 HR))|]].
      - exact (arepq_after_new s m m' d lo (bv_unsigned sp) ch bs cp (tl chunks) (a_L s) (a_S s) (a_AL s) b1 actx _ j0 j1 j2' j3
                 R CHIN ALLOC UHI DPL LO PCS BLK (munch_agree _ _ _ (munch_weaken _ _ _ _ SUBW MU)) WM Hb1 HDR' UW' TST' UNW' FLG' IA' SHF' TQ4 LA4 NB4 NBJ4 PC14 PC34 PC44 ST4 WQ').
      - intros b. destruct HR as (_ & ND & LBs). rewrite lb_remove_In, LBs. unfold alb. change (a_st s') with (free_st' s ch tq' cache'). rewrite !in_map_iff. split.
        + intros ((x & E & Hx) & NEU). apply filter_In in Hx. destruct Hx as [Hx AX]. exists x. split; [exact E|]. apply filter_In. split; [| exact AX].
          apply (free_old_in s ch m tq' cache' R CHIN x Hx). intros ->. apply NEU. rewrite <- E. reflexivity.
        + intros (x & E & Hx). apply filter_In in Hx. destruct Hx as [Hx AX]. apply (free_cl s ch m tq' cache' R CHIN) in Hx.
          destruct Hx as [->|[Hx NEU]]; [cbn in AX; discriminate AX|].
          split; [exists x; split; [exact E| apply filter_In; split; [exact Hx| exact AX]]|]. rewrite <- E. cbn [fst]. exact NEU. }
    split; [exact DEP'|].
    (* [comment removed for export] *)
    assert (IM : forall a, U - 16 <= a -> a + 1 <= U + round_up size 8 -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply (aim_of_aapp _ _ a UHI); clear - Ha Hb; zlets; lia. }   (* [comment removed for export] *)
    pose proof (carved_in_space s OK _ _ CVB) as (S1 & _). fold st B in S1.
    destruct (am_free_newhit_gen st ch (free_find st ch WFs CHIN) ALLOC ltac:(rewrite Q1, Q3; unfold kMaxCacheSize; clear - QSZ; lia)
                ltac:(change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); clear - Z4; zlets; Z.div_mod_to_equations; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5; zlets; unfold AHI_LO in *; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5 Z6; zlets; unfold AHI_LO in *; lia)
                cp (tl chunks) NN PCS HIT ltac:(clear - S1 X1; zlets; unfold a_sb, AHI_LO in *; lia)) as (stX & ev0 & E & SBX & SC).
    exists stX, ev0, []. split; [exact E|]. split; [exact SBX| exact SC].
  Qed.
End FreeNewHitMidR.

(* [comment removed for export] *)
Section FreeRefillMidR.
  Context {HCEIL : HeapCeil}.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Variables (sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (ch : chunk) (bs sbs : list byte).
  Variables (T : list Z) (rest : list word) (RF : mem -> Prop).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  (* [comment removed for export] *)
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
  Let cp := hd 0 chunks2.
  Let B := compact_to_addr st2 c cp.
  (* [comment removed for export] *)
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let L2 : list (word * word) :=
    if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
    else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s).
  Let S2 : list (word * word) :=
    (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
    ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Let AL' := a_AL s.   (* [comment removed for export] *)
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) AL' (a_top s) (a_bot s).
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st2) (zidx c) (mkPC (n - 1) (tl chunks2)).
  Let sF := free_s' sR ch tq' cache' L2 S2 AL'.
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let WR : list ivl := (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wn : list ivl := enq_new_W lo (bv_unsigned sp) TH B LA.
  Let WfR : list ivl := rf_W lo (bv_unsigned sp + -2352) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wf : list ivl := rf_W lo (bv_unsigned sp + -2272) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let WnR : list ivl := enq_newR_W lo (bv_unsigned sp) TH B LA.
  Definition fr_WR : list ivl := WR ++ (Wh ++ Wn).

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -2208).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3024 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis NR : (1 <= length T <= 30)%nat. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis LR : length rest = (255 - length T)%nat.
  Hypothesis RFT : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 -> disjoint_from W0 (bv_unsigned sp + -2208) 2208 ->
                   disjoint_from W0 (TH + 3168) 1 -> disjoint_from W0 AIAINIT 4 -> disjoint_from W0 AIAINST 0x81030 -> RF m1.
  Hypothesis RFE : forall m0, RF m0 ->
       rw_cells asegs m0 (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m0 (bv_unsigned sp + -2136 + 16) (map wz T ++ rest).
  Hypothesis RFX : forall m0, RF m0 ->
       rw_cells asegs m0 (TH + 3168) [C1 (b8 0)] /\ rw_cells asegs m0 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m0.
  Hypothesis RFP : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 ->
      (forall a, bv_unsigned sp + -2208 <= a < bv_unsigned sp -> outside W0 a) -> outside W0 (TH + 3168) ->
      (forall a, AIAINIT <= a < AIAINIT + 4 -> outside W0 a) -> (forall a, AIAINST <= a < AIAINST + 0x81030 -> outside W0 a) -> RF m1.
  Hypothesis RF0 : RF m.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : need_new tq = true.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.   (* [comment removed for export] *)
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp x3 x4 x5 cs0 (wz U) (wz AINST) (wz U) (wz 0) (wz 0)
             (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) x12 x13 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 x14 x15 x16 x17) F (Z_to_bv 64 0x196ae8) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_refill_gmidR (msF' : machine_state) (mo' : Model) : Prop :=
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       lzok asegs (a_L sF) (a_S sF) (a_Zr sF) (mkCfg msF' mo')
    /\ restrict (a_L sF) (a_S sF) msF'
       = MS (enq_regsR sp gp tp s7 s8 s9 s10 s11 U size TH kMaxCacheSize t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x19b46c) fc None m' (seg_rom asegs)
    /\ ARHEAPQ sF [] [] (lb_remove U LB) m' /\ awin_vis sF m' /\ flagsx_rep m' /\ AMODELX sF mo'
    /\ nonvm_same mo mo' /\ avmx s sF mo mo'                                                       (* [comment removed for export] *)
    /\ DEPOT asegs d' m' /\ depot_placed sF d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -2288)
    /\ rw_cells asegs m' (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH)
    /\ RF m'
    /\ munch fr_WR m m' /\ wmono asegs m m'
    /\ (exists stX ev0 ev2, am_free_full st U = free_tail_m U size stX ev0 ev2 /\ same_but_shadow stX (a_st sF) /\ syscalls_of ev0 = []).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HC : 1 <= c <= 30. Proof. unfold c, kBatchClass. lia. Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. destruct RR as (_ & _ & FL & _).
    destruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let RPURE := refill_pure s m c R HC MISS.
  Let RFF := rf_facts st c WFs HC ROOM.
  Let PCc := rfd_pc_c st c WFs HC ROOM.

  Theorem free_arep_refill_midR :
    (forall msF' mo', free_refill_gmidR msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    assert (SUBf : sub_fp WfR Wf).
    { unfold WfR, Wf, rf_W. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (A1 & A2). split; [clear - A1; lia| exact A2]. }
    assert (SUBn : sub_fp WnR Wn).
    { unfold WnR, Wn, enq_newR_W, enq_new_W. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (A1 & A2). split; [clear - A1; lia| exact A2]. }
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK].
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof (proj1 (proj2 HR)) as ND. pose proof (proj2 (proj2 HR)) as LBs.
    (* [comment removed for export] *)
    destruct (free_cells s m ch R CHIN ALLOC UHI) as (b1 & actx & q0 & q1 & q2 & q3 & HDR & Hb1 & ACR & TST & UNW & QC & TQ & QST & INST & IEN).
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    pose proof (free_plu s m ch d R CHIN DPL) as PLU.
    pose proof SHB as [[_ [_ SHu]] SBS].
    pose proof RPURE as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    fold st in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10. fold r in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10.
    fold nf mfa au mu fl in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10.
    destruct (refill_cells_of_arep s m c R HC MISS) as (p0 & p1 & p2 & p3 & PC1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REN).
    unfold a_cache, OT_CACHE, PCLASS_SIZE in PC1. fold st TH in PC1. fold CA in PC1. fold P in PC1.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in PC1. destruct PC1 as [PC1 _].
    assert (BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ sb mod 65536 = 0 /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ aceil <= lo /\ lo + 3024 <= bv_unsigned sp
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384 /\ c = 24).
    { assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
      assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
      clear - Y1 Y2 Y3 Y4 Y5 X1 X2 X3 LO HI E1 E2. zlets. unfold a_ri, a_sb, AHI_LO, kSpaceSize, kPageSize, kBatchClass in *. repeat split; lia. }
    assert (BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ mu <= mu' <= mu + 262144 /\ mfa <= mfa' <= mfa + 262144 /\ n = 1).
    { pose proof RFF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
      pose proof (rf_mfa_delta st c WFs HC ROOM) as FD.
      fold st r in F7, F12, FD. fold nf mfa au mu fl n in F7, F12, FD. fold mu' mfa' in F7, F12, FD.
      unfold kFreeArraySize, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *. clear - U1 U2 U4 U5 F7 F12 FD. repeat split; first [lia | reflexivity]. }
    (* [comment removed for export] *)
    assert (UB : exists ub, rw_cells asegs m U [CB 8 ub]).
    { pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _). pose proof (CHR ch CHIN) as (_ & _ & STI & JR & _).
      rewrite ALLOC in STI. fold U size in JR.
      pose proof (record_ext s OKs ch CHIN) as (E1 & E2 & E3 & _ & _ & E6 & E7 & E8 & _).
      pose proof (stk_of_rw_cells asegs _ _ _ BLK) as SK. cbn [cells_size csize Nat.add] in SK.
      replace (U + Z.of_nat (Z.to_nat size + 0)) with (U + size) in SK by (clear - Z1; zlets; lia).
      destruct (Z.le_gt_cases 8 size) as [LE|GT].
      - destruct (stk_split asegs _ _ (U + 8) _ SK ltac:(clear - LE; lia)) as [SK1 _]. destruct (stk_cells _ _ _ SK1 ltac:(clear - LE; lia)) as [ub Hub].
        exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - LE; lia). exact Hub.
      - pose proof (junk_stk' _ _ _ JR ltac:(clear - Z1 Z2; zlets; destruct Z2 as (_ & _ & ZT); unfold AIMG_TOP in ZT; lia) ltac:(clear - E2 E7 Z1 Z5; zlets; acb; lia) ltac:(clear - GT E7 Z5 Z6; zlets; lia)) as SJ.
        replace (U + size + (ch_end ch - (U + size))) with (ch_end ch) in SJ by (clear - GT; lia).
        destruct (stk_split asegs _ _ (U + 8) _ SJ ltac:(clear - GT E7 Z1 Z5 Z6; zlets; lia)) as [SJ1 _].
        pose proof (stk_merge asegs _ _ _ _ SK SJ1 ltac:(clear - GT Z1; zlets; lia)) as SK8.
        destruct (stk_cells _ _ _ SK8 ltac:(clear - GT; lia)) as [ub Hub]. exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - GT; lia). exact Hub. }
    destruct UB as [ub UB].
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
    { eapply (@free_head_refillR _ sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m lo d
                ATSD CTX TH (a_top s) (a_bot s) sb U size b1 actx ub kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize sbs
                k (hd 0 (map qb_addr l)) LA (qc_bytes tq) T rest RF).
      - exact LO.
      - exact HI.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _ & pX2 & pX3 & _). fold TH in pT1, pT2, pT3. fold CTX in pX2, pX3.
        unfold kPageSize in pT1, pT2, pT3. split; [clear; lia|]. split; [clear; lia|]. split; [exact pX2|]. split; [exact pX3|]. split; [exact pT2|]. split; [exact pT3|].
        clear - pT1. zlets. Z.div_mod_to_equations. lia.
      - constructor. clear - X4 X5 Y6. zlets. unfold kSpaceSize in *. lia.
      - constructor. repeat match goal with |- _ /\ _ => split end; try exact G10; try exact G12;   (* [comment removed for export] *)
          clear - G1 G2 G3 G4 G5 G6; zlets; unfold a_sb, kSpaceSize, kPageSize, disj in *; lia.
      - constructor. exact PLU.
      - constructor. clear - V1 V2. unfold kPageSize in V1. lia.
      - exact DLO.
      - exact DCAP.
      - constructor. clear - Z1 Z2 Z3 Z4 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - clear - Z1 QSZ. zlets. lia.
      - exact Hb1.
      - exact ACR.
      - clear - QSZ. zlets. unfold kMaxCacheSize, kQuarantineMaxSize, kQuarantineMinSize in *. lia.
      - exact SBS.
      - pose proof (batches_len_bound s m R) as BL. clear - BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - constructor. clear - X1 X2 X3. zlets. repeat split; assumption.
      - exact NR.
      - exact TRNG.
      - exact LR.
      - exact RFT.
      - exact RFE.
      - rewrite TP. exact IEN.
      - exact MI.
      - exact ST.
      - exact RF0.
      - exact DEP.
      - exact HDR.
      - exact UB.
      - exact TST.
      - exact QC.
      - exact SHu.
      - exact TQ.
      - replace (TH + 2128) with P by (clear - BND; lia). exact PC1.
      - (* [comment removed for export] *)
        intros NZ. assert (NE : l <> []) by (intros EL; apply NZ; unfold k; rewrite EL; reflexivity).
        pose proof (free_last_cells s m ch d R CHIN DPL NE) as (LBc & _ & _ & INlb & CNT' & CB' & _ & LA1 & LA2 & _ & LAT & LAU & LAD1 & LAD2 & _).
        pose proof (need_new_true_full tq NN NE) as FULL. fold l lb in FULL.
        fold st tq l lb LA in LBc, LA1, LA2, LAT, LAU, LAD1, LAD2, CB', FULL |- *.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_; _])) in LBc. destruct LBc as [LB1 LB23]. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in LB23. destruct LB23 as [_ LB3].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LB3.
        replace (qb_count lb) with kBatchCount in LB3 by (clear - CB' FULL; lia).
        split; [split; [exact LB1| replace (LA + 16) with (LA + 8 + 8) by (clear; lia); exact LB3]|].
        clear - LA1 LA2 LAT LAU LAD1 LAD2. zlets. unfold kBatchSize, AHI_LO in *. repeat split; lia. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
    destruct PO1 as (t0_1 & t1_1 & t2_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & jke & m1 & VIS1 & MU1 & WM1 & MI1 & ENV1 & ST1 & FR1 & PFR1 & RF1
                     & HDR1 & UW1 & TST1 & DEP1 & SHF1 & TQ1 & PC11 & LC1).
    destruct (RFX _ RF1) as (UNW1 & FLG1 & IA1).
    pose proof (munch_agree _ _ _ MU1) as AG1.
    (* [comment removed for export] *)
    destruct (refill_cells_at1 s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO MISS ROOM QSZ m1 MU1 WM1)
      as (q0' & q1' & q2' & q3' & PC1' & PCJ1 & FAM1 & QST1 & RIC1 & RIJ1 & EXH1 & RST1 & FARR1 & FAJ1 & USJ1 & I1 & I2 & I3 & _).
    (* [comment removed for export] *)
    assert (ZI : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) -> outside Wh a)
      by (intros a Ha N1 N2 N3 N4; exact (ZH_lo s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO QSZ a Ha N1 N2 N3 N4)).
    assert (ZC : forall a, CTX <= a < CTX + 160 -> outside Wh a).
    { intros a Ha. pose proof (rec_vs_ctx s m ch R CHIN) as RC. pose proof (record_ext s OKs ch CHIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
      pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & pX2 & _). pose proof (aapp_lit _ _ pX2) as BC. fold CTX in BC.   (* [comment removed for export] *)
      apply (ZH_hi s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO QSZ a);
        [clear - Ha Y4 Y5 BC| clear - Ha RC E3 E6 E7 E8 Z1 Z5 Z6| clear - Ha RC E3 E6 E7 E8 Z1 Z5 Z6| clear - Ha Y6| clear - Ha G5| clear - Ha G6];
        zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, disj, kPageSize in *; lia. }
    assert (REN1 : RENV tp ATSD CTX TH sb (a_ri s) m1).
    { rewrite TP. destruct REN as [SE I1' I2' I3']. open_senv SE.
      constructor; [constructor| exact I1| exact I2| exact I3].
      all: eapply (rw_cells_transport_pt _ _ _ AG1 WM1); [eassumption|]; unfold AGOT_VALS;
           cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length map];
           let Ha := fresh in intros ? Ha;
           first [ apply ZC; clear - Ha; zlets; lia
                 | apply ZI; unfold AIMG_TOP, AIAINIT, AIAINST, wz, ATP, ATSD, AGOT_VALS, AINST in *; rewrite ?unsigned_lit in Ha by (clear; lia); clear - Ha; lia ]. }
    (* [comment removed for export] *)
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof AMX1 as AMX1'. destruct AMX1' as [AM1 AK1].
    pose proof AM1 as AM1'. destruct AM1' as (AIL1 & ASV1 & AB1). destruct AIL1 as (_ & _ & _ & NOV1 & NW1 & NWA1). destruct AB1 as [AB1a AB1b].
    (* [comment removed for export] *)
    replace (wz (TH + 2128)) with (wz (TH + OT_CACHE + PCLASS_SIZE * c)) in VIS1 by (unfold OT_CACHE, PCLASS_SIZE, c, kBatchClass; f_equal; clear; lia).
    eapply (refill_sreach (a_L s) (a_S s) (a_Zr s) msF1 mo1 Q (wz 0x19b5cc) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0_1 t1_1 t2_1
              (wz (TH + OT_CACHE + PCLASS_SIZE * c)) (wz (TH + OT_CACHE)) (wz size) (wz AINST) a6_1 a7_1
              (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz size) (wz kMaxCacheSize) s7 s8 s9 s10 s11 t3_1 t4_1 t5_1 t6_1
              F fc m1 lo sb c (TH + OT_CACHE) TH CTX ATSD nf mfa au mu fl (as_cache_inited st)).
    { exact LO. }
    { rewrite unsigned_lit by (clear - SPR BND; acb; lia). clear - BND; lia. }
    { rewrite unsigned_lit by (clear - SPR BND; acb; lia). clear - SPT; lia. }
    { constructor. rewrite unsigned_lit by (clear - SPR BND; acb; lia). clear - SPA. Z.div_mod_to_equations. lia. }
    { exact HC. }
    { reflexivity. }
    { clear - X1 X2. zlets. split; assumption. }
    { constructor. exact X3. }
    { rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia. }
    { unfold ATSD, AIMG_TOP. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & pT2 & pT3 & _ & pX2 & pX3 & _). fold TH in pT2, pT3. fold CTX in pX2, pX3. unfold kPageSize in pT2, pT3.
      split; [clear; lia|]. split; [clear; lia|]. split; [exact pX2|]. split; [exact pX3|]. split; [exact pT2| exact pT3]. }
    { constructor. clear - Y3. zlets. Z.div_mod_to_equations. lia. }
    { constructor. unfold kSpaceSize. clear - X4 X5 Y6. zlets. unfold kSpaceSize in *. lia. }
    { unfold kFreeArraySize. clear - BR. lia. }
    { constructor. exact U3. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - BR. lia. }
    { constructor. exact U6. }
    { exact U7. }
    { exact OK1. }
    { exact VIS1. }
    { exact MI1. }
    { rewrite unsigned_lit by (clear - SPR BND; acb; lia). exact ST1. }
    { exact REN1. }
    { exact U8. }
    { exact PC1'. }
    { exact PCJ1. }
    { exact FAM1. }
    { exact QST1. }
    { exact TST1. }
    { exact RIC1. }
    { exact RIJ1. }
    { exact EXH1. }
    { exact RST1. }
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - BND; lia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - BND; lia).
    { exact FARR1. }
    { exact FAJ1. }
    { exact USJ1. }
    { intros a kk Ha. exact (ak_resf_hi s mo1 AK1 a kk Ha). }
    { intros a kk Ha Hk. apply (ak_prim s mo1 AK1 a kk c); [unfold kNumClasses; clear - HC; lia| exact Ha| unfold kRegionSize; exact Hk]. }
    { exact NW1. }
    { exact NWA1. }
    { exact NOV1. }
    { intros x Hx. apply (ak_zr_sb s mo1 AK1). unfold kSpaceSize, kPageSize. clear - Hx BND. unfold sb in *. lia. }
    { exact (ak_zrsh s mo1 AK1). }
    { exact (ak_lsh s mo1 AK1). }
    { intros x Hx. apply WM1. exact (AWV x Hx). }
    { unfold ABUDGET, aPhi in AB1b. change (a_st s) with st in AB1b. unfold COLD_COST in PROOM. unfold page_size in AB1b. clear - AB1a AB1b PROOM. lia. }   (* [comment removed for export] *)
    { exact U9. }
    { exact U10. }
    { exact (ak_atop s mo1 AK1). }
    cbv beta. intros msF2 mo2 RD.
    destruct RD as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & j0 & j1 & j2 & j3 & m2 & L' & S' & RD).
    lazy zeta in RD.
    destruct RD as (OK2 & VIS2 & EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG & MU2 & WM2 & MI2 & ST2 & PCN & FAM2 & CHA & CHJ
                    & RI2 & RIJ2 & EXH2 & RST2 & FARR2 & FAJ2 & USJ2 & POIu & POIf & QST2 & TST2).
    fold mu' nnew nf1 mfa' au' fl1 n in VIS2, EL, ES, VMN, EAG, MU2, PCN, CHA, CHJ, RI2, FARR2, FAJ2, USJ2, POIu, POIf.
    rewrite unsigned_lit in MU2, ST2 by (clear - SPR BND; acb; lia).
    subst L' S'. fold L2 in OK2, VIS2. fold S2 in OK2, VIS2.
    fold chunks2 in CHA.
    pose proof MU2 as MU2R. fold WfR in MU2R. apply (munch_weaken _ _ _ _ SUBf) in MU2. fold Wf in MU2.
    (* [comment removed for export] *)
    pose proof (after_refill_bundle s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3
                  MU1 WM1 MU2 WM2 MI MI2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1
                  b1 actx (d_putid d (depot_hash T)) (hd 0 (map qb_addr l)) (qc_bytes tq) HDR1 UW1 FLG1 IA1 SHF1 TQ1 LC1 INST) as ARB.
    destruct ARB as ((R2 & MIR' & WM0R' & AG0R' & FXR2) & (EB & A1 & A2 & BT & BUx & BD1 & BD2 & BPOS & BLA) & (N1 & CC & TK & CPS) & LAX
                     & BJ2 & HDR2 & UW2 & FLG2 & IA2 & SHF2 & TQ2 & LC2 & INST2 & PC12 & PC22 & PC32 & PC42 & UNW2).
    (* [comment removed for export] *)
    assert (HI80 : lo + 2944 <= bv_unsigned sp + -80) by (clear - HI; lia).
    assert (ZK : forall a, bv_unsigned sp + -2352 <= a -> outside WfR a).
    { intros a Ha. unfold WfR. replace (bv_unsigned sp + -2352) with (bv_unsigned sp + -80 + -2272) by (clear; lia).
      apply (ZR_stack s m d lo (bv_unsigned sp + -80) ch R DPL LO HI80 MISS ROOM a). clear - Ha. lia. }
    assert (AG2 : agree_on (outside WfR) m1 m2) by exact (munch_agree _ _ _ MU2R).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -2352)
              [CB 8 jke; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (wz size); C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x19b46c)])
      by (trp rw_cells_transport_pt AG2 WM2 FR1 ZK SPR).
    unfold put_frameR in PFR1.
    assert (PFR2 : rw_cells asegs m2 (bv_unsigned sp + -2288)
              [C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 s6; C8 cs5;
               C8 cs4; C8 cs3; C8 cs2; C8 (wz U); C8 cs0; C8 (wz 0x197a10)])
      by (trp rw_cells_transport_pt AG2 WM2 PFR1 ZK SPR).
    assert (RF2 : RF m2).
    { apply (RFP _ _ _ RF1 MU2R WM2).
      - intros a Ha. apply ZK. clear - Ha. lia.
      - unfold WfR. replace (bv_unsigned sp + -2352) with (bv_unsigned sp + -80 + -2272) by (clear; lia).
        apply (ZR_thr s m d lo (bv_unsigned sp + -80) ch R CHIN DPL LO MISS ROOM); clear - BND; lia.
      - intros a Ha. unfold WfR. replace (bv_unsigned sp + -2352) with (bv_unsigned sp + -80 + -2272) by (clear; lia).
        apply (ZR_lo s m d lo (bv_unsigned sp + -80) ch R DPL LO MISS ROOM). unfold AIAINIT, AIMG_TOP in *. clear - Ha. lia.
      - intros a Ha. unfold WfR. replace (bv_unsigned sp + -2352) with (bv_unsigned sp + -80 + -2272) by (clear; lia).
        apply (ZR_lo s m d lo (bv_unsigned sp + -80) ch R DPL LO MISS ROOM). unfold AIAINST, AIMG_TOP in *. clear - Ha. lia. }
    (* [comment removed for export] *)
    replace (wz (TH + OT_CACHE + PCLASS_SIZE * c)) with (wz (TH + 2128)) in VIS2 by (unfold OT_CACHE, PCLASS_SIZE, c, kBatchClass; f_equal; clear; lia).
    change (ret_pc (wz 0x19b5cc)) with (ret_pc (Z_to_bv 64 0x19b5cc)) in VIS2. rewrite (ret_pc_even 0x19b5cc) in VIS2 by (clear; lia).
    eapply (evt_sreach_lazy_at asegs L2 S2 (a_Zr s) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (@free_tail_refill_midR _ sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 F fc
                t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 (wz 0x19b5cc) m2
                lo jke RF U size TH kMaxCacheSize sb k (hd 0 (map qb_addr l)) LA (qc_bytes tq) n chunks2 B j0 j1 j2 j3).
      - exact LO.
      - exact HI.
      - constructor. exact SPT.
      - constructor. clear - Z1 Z2 Z3 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - constructor. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _). fold TH in pT1, pT2, pT3. unfold kPageSize in pT1, pT2, pT3.
        split; [exact pT2|]. split; [exact pT3|]. clear - pT1. zlets. Z.div_mod_to_equations. lia.
      - constructor. clear - X1 X2 X3. zlets. repeat split; assumption.
      - exact CC.
      - clear - N1. zlets. rewrite N1. clear. lia.
      - exact CPS.
      - exact EB.
      - constructor. split; [exact A1| split; [exact A2| exact BT]].
      - pose proof (batches_len_bound s m R) as BL. clear - BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - intros NZ. split; [exact (LC2 NZ)|].
        destruct LAX as [(_ & _ & KZ)|(_ & _ & L1 & L2' & L3 & L4 & _)]; [exfalso; exact (NZ KZ)|].
        split; [exact L1|]. split; [exact L2'|]. split; [exact L3|]. split; [exact (BLA NZ)| exact L4].
      - intros KZ. destruct LAX as [(_ & LA0 & _)|(_ & K1 & _)]; [exact LA0| exfalso; clear - KZ K1; zlets; lia].
      - exact RFT.
      - exact MI2.
      - exact ST2.
      - exact FR2.
      - exact TQ2.
      - exact PC12.
      - exact PC22.
      - exact PC32.
      - exact PC42.
      - exact QST2.
      - exact INST2.
      - exact BJ2.
      - exact PFR2.
      - exact RF2. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j2' & m3 & VIS3 & MU3 & WM3 & MI3 & ST3
                     & PFR3 & RF3 & TQ3 & LA3 & NB3 & NBJ3 & PC13 & PC33 & PC43 & STATS3).
    pose proof MU3 as MU3R. apply (munch_weaken _ _ _ _ SUBn) in MU3. fold Wn in MU3.
    (* [comment removed for export] *)
    pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3) as WM03.
    destruct (head_cells3 s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3
                MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3
                b1 actx (d_putid d (depot_hash T)) HDR2 UW2 FLG2 IA2 SHF2 UNW2) as (HDR3 & UW3 & FLG3 & IA3 & SHF3 & TST3 & UNW3 & DAV).
    pose proof (arepq_after_refill_new s m d lo (bv_unsigned sp) ch bs L2 S2 AL' R CHIN ALLOC UHI DPL LO MISS ROOM QSZ BLK m1 m2 j0 j1 j2 j3
                  MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3
                  b1 actx (d_putid d (depot_hash T)) j0 j1 j2' j3 Hb1 HDR3 UW3 TST3 UNW3 FLG3 IA3 SHF3 TQ3 LA3 NB3 NBJ3 PC13 PC33 PC43 STATS3 WM03) as AQ.
    apply K. unfold free_refill_gmidR.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3.
    split; [exact OK3|]. split; [exact VIS3|].
    split. { split; [exact AQ|]. split; [apply lb_remove_nodup; exact ND|].
             exact (alb_after_refill_new s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM QSZ m1 m2 j0 j1 j2 j3
                      MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 LB LBs). }
    split. { intros x Hx. apply (win3 s m d lo ch R DPL LO MISS ROOM m2 POIu POIf m3 WM3 (a_S s) x Hx). intros Hx'. apply WM03. exact (AWV x Hx'). }
    split. { exact (flagsx3 s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3 MU1 WM1 MU2 WM2
                      PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3 WM03 (FXR2 FXR)). }
    split. { assert (HAL : 0 <= a_AL s <= a_AL s) by (clear - AB1a; lia).   (* [comment removed for export] *)
             pose proof (amodelx_after_refill s mo1 mo2 c L2 S2 AL' AMX1 OKs HC ROOM (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK))
                           eq_refl eq_refl VMM VMR VML (nonvm_same_atop _ _ NVS) VMN EAG HAL) as AMX2.   (* [comment removed for export] *)
             exact (amodelx_free sR mo3 ch tq' cache' (AMODELX_mat sR mo2 mo3 AMX2 SBM3)). }
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat _ _ SBM1) (nonvm_same_trans _ _ _ NVS (nonvm_same_mat _ _ SBM3)))|].
    split. { apply avmx_same; [| reflexivity]. rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). reflexivity. }
    split. { assert (DEP2 : DEPOT asegs d' m2).
             { eapply (DEPOT_transport asegs d' m1 m2 _ DEP1 MU2 WM2). unfold d', depot_avoid. rewrite d_nb_put, d_sb_put.
               exact (ZR_depot s m d lo (bv_unsigned sp) ch R CHIN DPL LO MISS ROOM). }
             eapply (DEPOT_transport asegs d' m2 m3 _ DEP2 MU3 WM3). unfold d', depot_avoid. rewrite d_nb_put, d_sb_put. exact DAV. }
    split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split. { unfold depot_cov. unfold d'. rewrite d_nb_put, d_sb_put. intros x Hx.
             rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). exact (DCOV x Hx). }
    split; [exact MI3|]. split; [exact ST3|].
    split; [exact PFR3|]. split; [exact RF3|].
    split. { intros x Hx. unfold fr_WR in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2].
             pose proof (AG0R' (bv_unsigned x) Hx1 (bv_unsigned_in_range _ x)) as E1.
             pose proof (AGR3 s m d lo (bv_unsigned sp) ch m2 m3 MU3 (bv_unsigned x) Hx2 (bv_unsigned_in_range _ x)) as E2.
             unfold wa in E1, E2. rewrite Z_to_bv_bv_unsigned in E1, E2. rewrite E2. exact E1. }
    split; [exact WM03|].
    (* [comment removed for export] *)
    assert (IM : forall a, U - 16 <= a -> a + 1 <= U + round_up size 8 -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply (aim_of_aapp _ _ a UHI); clear - Ha Hb; zlets; lia. }   (* [comment removed for export] *)
    assert (HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0).
    { change (as_space_beg st) with sb. unfold kHighMemBeg, kHighMemEnd, kSpaceSize. clear - BND. acb. Z.div_mod_to_equations. lia. }
    destruct (am_free_refill_gen st ch (free_find st ch WFs CHIN) ALLOC ltac:(rewrite Q1, Q3; unfold kMaxCacheSize; clear - QSZ; lia)
                ltac:(change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); clear - Z4; zlets; Z.div_mod_to_equations; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5; zlets; unfold AHI_LO in *; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5 Z6; zlets; unfold AHI_LO in *; lia)
                cp (tl chunks2) WFs NN MISS ROOM HM TK BPOS) as (stX & ev0 & ev2 & E & SBS' & SC0).
    exists stX, ev0, ev2. split; [exact E|]. split; [| exact SC0].
    unfold free_new_state in SBS'. change (get_pc (refilled (set_internal_init st) kBatchClass) kBatchClass) with (get_pc st2 c) in SBS'.
    rewrite PCc in SBS'. cbn [pc_count refill_pc] in SBS'. exact SBS'.
  Qed.
End FreeRefillMidR.

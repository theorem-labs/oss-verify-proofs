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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AW_Drain AW_Put3 AS_Free1 AS_Free2 AS_Free3 AS_Free4 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_MallocCold AG_MallocTop
     AG_FreeModel AG_FreeModel2 AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free7 AG_Free8 AG_Free9 AG_Free
     AG_RepQ AG_RepQFacts AG_FreeMid AG_FreeTail AG_FreeT1 SecLazy AG_WriteSet AG_RecycleDefs AG_FreeNum AG_FreeCompl AG_FreeT2X.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_PutR1 AW_EnqueueR1 AW_EnqueueR2 AW_PutR2 AS_FreeR4 AG_FreeR3 AG_FreeMidR AG_FreeTailR AG_FreeT1R AG_FreeT2XR AG_FreeTop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section FreeGlueR.
  Context {HCEIL : HeapCeil}.
  Variables (sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (ch : chunk) (bs sbs : list byte).
  Variables (T : list Z) (rest : list word) (RF RFr : mem -> Prop).

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
  Let c := kBatchClass.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let LB' := lb_remove U LB.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 131072).
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -2208).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI0 : lo + 3280 <= bv_unsigned sp.   (* [comment removed for export] *)
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  (* [comment removed for export] *)
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
  Hypothesis RFW : forall m0, RF m0 -> RFr m0.
  Hypothesis RFrT : forall W0 m0 m1, RFr m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 -> disjoint_from W0 (bv_unsigned sp + -2208) 2208 -> RFr m1.
  Hypothesis RFrA : forall m0 m1, RFr m0 -> agree_on (fun a => bv_unsigned sp + -2208 <= a) m0 m1 -> RFr m1.
  (* [comment removed for export] *)
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize.
  (* [comment removed for export] *)
  Hypothesis INITQH : INITQ st.
  Hypothesis PINVH : PINV st.
  Hypothesis NALH : nalloc st <= LIVEB.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.   (* [comment removed for export] *)
  Hypothesis ROOM : rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp x3 x4 x5 cs0 (wz U) (wz AINST) (wz U) (wz 0) (wz 0)
             (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) x12 x13 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 x14 x15 x16 x17) F (Z_to_bv 64 0x196ae8) fc None m (seg_rom asegs).

  Let HI : lo + 3024 <= bv_unsigned sp. Proof. clear - HI0. lia. Qed.
  Let HI29 : lo + 2944 <= bv_unsigned sp. Proof. clear - HI0. lia. Qed.
  Let TPv : bv_unsigned tp = ATP. Proof. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). reflexivity. Qed.
  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8). Proof. exact (uhi_of_arep s m ch R CHIN). Qed.   (* [comment removed for export] *)
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Let HC24 : 0 <= c < kNumClasses. Proof. unfold c, kBatchClass, kNumClasses. lia. Qed.
  Let QSZ2 : size <= kQuarantineMaxSize /\ size < 2^32.
  Proof. split; [exact QSZ|]. unfold kQuarantineMaxSize in QSZ. clear - QSZ. lia. Qed.
  Let DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Proof. pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & G12 & G13). clear - G11 G13 LO. lia. Qed.
  (* [comment removed for export] *)
  Let ZHs : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
                      ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) -> outside (free_head_W lo (bv_unsigned sp) TH U size d) a.
  Proof. intros a Ha N1 N2 N3 N4. apply (ZH_lo s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO QSZ2 a); [clear - Ha; lia| assumption| assumption| assumption| assumption]. Qed.
  (* [comment removed for export] *)
  Let BT : TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH.
  Proof. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & pT2 & _). pose proof (akobj_lit _ _ pT2) as X. unfold kPageSize in X. exact X. Qed.
  (* [comment removed for export] *)
  Let QB : 0 <= qc_bytes tq <= kMaxCacheSize /\ 0 <= qc_bytes (as_gq st) <= kQuarantineMaxSize /\ 1 <= size.
  Proof.
    pose proof WFs as WW. destruct WW as (_ & _ & _ & _ & _ & _ & _ & _ & Wtq & Wgq & Wtqb & Wgqb & _ & _ & _ & _ & _ & _ & _ & _ & Wqmax & _ & Wqc & _).
    fold st in Wtq, Wgq, Wtqb, Wgqb, Wqmax, Wqc. fold tq in Wtq, Wtqb. rewrite Wqc in Wtqb. rewrite Wqmax in Wgqb.
    pose proof (qc_bytes_nonneg st tq WFs Wtq) as N1. pose proof (qc_bytes_nonneg st (as_gq st) WFs Wgq) as N2.
    pose proof (WF_chunk st ch WFs CHIN) as (C1 & _). fold size in C1.
    clear - Wtqb Wgqb N1 N2 C1. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Let TAILS : forall sm msF2 mo2,
    free_midsR sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo ch T RFr sm msF2 mo2 ->
    as_cache_inited (a_st sm) = true -> NUM (a_st sm) ->
    (forall msF' mo', free_gpostXR sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo ch T RFr msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF2 mo2).
  Proof.
    intros sm msF2 mo2 MIDS INI NM K. destruct (Z.le_gt_cases (qc_bytes (as_tq (a_st sm))) kMaxCacheSize) as [LEc|GTc].
    - exact (free_tail0R sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo Q s LB d lo ch T RFr LO HI sm msF2 mo2 MIDS LEc K).
    - destruct (Z.le_gt_cases (qc_bytes (as_gq (a_st sm)) + qc_bytes (as_tq (a_st sm))) kQuarantineMaxSize) as [LE|GT2].
      + exact (free_tail1R sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo Q s LB d lo ch T RFr HR LO HI SPT RFrT sm msF2 mo2 MIDS GTc LE K).
      + exact (free_tail2R sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo Q s LB d lo ch T RFr HR DPL DFS LO HI0 RFrA SPT SPA TPv sm msF2 mo2 MIDS GTc GT2 INI NM K).
  Qed.

  (* [comment removed for export] *)
  Let MIDS_OF : forall (tq' : qcache) (cache' : list pclass) (W : list ivl) msF2 mo2 (b1 actx : Z)
                       (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem),
    let s' := free_s' s ch tq' cache' (a_L s) (a_S s) (a_AL s) in
    qc_list tq' <> [] -> 0 <= qc_bytes tq' <= kMaxCacheSize + kQuarantineMaxSize + kBatchSize ->
    lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF2 mo2) -> same_but_materialized mo mo2 ->
    restrict (a_L s) (a_S s) msF2
      = MS (enq_regsR sp gp tp s7 s8 s9 s10 s11 U size TH kMaxCacheSize t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x19b46c) fc None m2 (seg_rom asegs) ->
    free_common_midR sp cs0 cs2 cs3 cs4 cs5 s6 m m2 W lo U size b1 actx TH T d RF ->
    ARHEAPQ s' [] [] LB' m2 ->
    (exists stX ev0 ev2, am_free_full st U = free_tail_m U size stX ev0 ev2 /\ same_but_shadow stX (a_st s') /\ syscalls_of ev0 = []) ->
    flagsx_rep m2 -> amframe s LB' (bv_unsigned sp) m m2 -> acompl s s' d lo (bv_unsigned sp) m m2 ->
    free_midsR sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo ch T RFr s' msF2 mo2.
  Proof.
    intros tq' cache' W msF2 mo2 b1 actx t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 s' TNE TQB OK2 SBM VIS2 FC HQ MODEL FX2 AMF2 ACM2.
    destruct FC as (MU & WM2 & MI2 & ST2 & PFR & RF2 & HDR' & UW' & TST' & DEP' & SHF').
    pose proof QB as (_ & (GQ0 & GQ1) & _). destruct AX as [AWV FXR].
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [subst s'; cbn [a_AL free_s']; unfold FREE_COST, COLD_COST; clear; lia|].
    split; [exact TNE|]. split; [exact TQB|]. split; [subst s'; cbn [a_st free_s' free_st' as_gq]; exact (conj GQ0 GQ1)|].
    split; [exact OK2|]. split; [exact VIS2|]. split; [exact HQ|].
    split; [intros x Hx; apply WM2; exact (AWV x Hx)|]. split; [exact FX2|].
    split; [exact (amodelx_free s mo2 ch _ _ (AMODELX_mat s mo mo2 AMX SBM))|].
    split; [exact (nonvm_same_mat mo mo2 SBM)|].
    split; [exact DEP'|].
    split; [subst s'; unfold depot_placed; cbn [a_thr a_sb a_ctx a_pa a_st free_s']; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split; [unfold depot_cov; unfold d'; rewrite d_nb_put, d_sb_put; intros x Hx; rewrite (same_but_materialized_vmmaps mo mo2 SBM); exact (DCOV x Hx)|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact PFR|]. split; [exact (RFW _ RF2)|]. split; [exact AMF2|]. split; [exact WM2|].
    split; [exact ACM2|].
    split; [apply avmx_same; [rewrite (same_but_materialized_vmmaps mo mo2 SBM); reflexivity| reflexivity]|].
    exact MODEL.
  Qed.

  Theorem free_arepR :
    (forall msF' mo', free_gpostXR sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo ch T RFr msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. pose proof AX as [AWV FXR]. pose proof QB as ((TQ0 & TQ1) & (GQ0 & GQ1) & SZ1).
    pose proof (free_pure s m ch R CHIN UHI) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    destruct (need_new tq) eqn:NNq.
    - destruct (Z.eq_dec (pc_count (get_pc st c)) 0) as [MISS|HIT].
      + (* [comment removed for export] *)
        eapply (free_arep_refill_midR sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m msF mo Q s LB d lo ch bs sbs T rest RF
                  HR CHIN ALLOC UHI AX AMX DEP DPL DCOV MI ST LO HI SPA SPT TP DLO DCAP NR TRNG LR RFT RFE RFX RFP RF0 BLK SHB QSZ2 NNq MISS PROOM ROOM OK VISE).
        intros msF2 mo2 PO.
        destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & OK2 & VIS2 & HQ & AWV2 & FX2 & AMX2
                        & NVS2 & AVX2 & DEP2 & DPL2 & DCOV2 & MI2 & ST2 & PFR & RF2 & MU2 & WM2 & MODEL).
        assert (HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0).
        { pose proof PL as (pY1 & pY2 & pY3 & _). unfold a_sb in pY1, pY2, pY3. fold st in pY1, pY2, pY3.
          unfold kHighMemBeg, kHighMemEnd, kSpaceSize, kPageSize, AHI_LO in *. clear - pY1 pY2 pY3. acb. Z.div_mod_to_equations. lia. }
        (* [comment removed for export] *)
        lazymatch type of HQ with ARHEAPQ ?sx0 _ _ _ _ =>
          set (sx := sx0) in *;
          apply (TAILS sx msF2 mo2); [| reflexivity| exact (NUM_regions (a_st sx) (refilled st c) eq_refl (NUM_refilled st WFs PINVH NALH MISS ROOM HM))| exact K];
          assert (ACM2 : acompl s sx d lo (bv_unsigned sp) m m2)
            by (apply (acompl_of_munchF s sx d lo (bv_unsigned sp) _ m m2 MU2); unfold fr_W; apply Forall_app; split;
                [exact (refill_compl s m d lo (bv_unsigned sp) ch sx R ROOM)|
                 apply Forall_app; split; [exact (head_compl s m d lo (bv_unsigned sp) ch sx R CHIN)|
                                           exact (new_compl s m d lo (bv_unsigned sp) ch sx R CHIN DPL _ (refill_slot_sp s m ch R ROOM))]]) end.
        exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [subst sx; cbn [a_AL free_s']; unfold FREE_COST; clear; lia|].
        split; [subst sx; cbn -[Z.add]; intros E; apply app_eq_nil in E; destruct E as [_ E]; discriminate E|].
        split; [subst sx; cbn -[Z.add Z.mul Z.le kBatchSize kQuarantineMaxSize kMaxCacheSize]; clear - TQ0 TQ1 QSZ SZ1; zlets; unfold kBatchSize, kQuarantineMaxSize, kMaxCacheSize in *; lia|].
        split; [subst sx; cbn -[Z.le kQuarantineMaxSize]; clear - GQ0 GQ1; zlets; lia|].
        split; [exact OK2|]. split; [exact VIS2|]. split; [exact HQ|]. split; [exact AWV2|]. split; [exact FX2|]. split; [exact AMX2|].
        split; [exact NVS2|].
        split; [exact DEP2|]. split; [exact DPL2|]. split; [exact DCOV2|]. split; [exact MI2|]. split; [exact ST2|].
        split; [exact PFR|]. split; [exact (RFW _ RF2)|].
        split. { apply (amframe_of_munch s LB' (bv_unsigned sp) _ m m2 MU2). unfold fr_W. apply Forall_app. split.
                 * exact (refill_frame s m LB d lo (bv_unsigned sp) ch HR DPL LO HI29 ROOM).
                 * apply Forall_app. split; [exact (head_frame s m LB d lo (bv_unsigned sp) ch HR CHIN UHI DPL DFS LO HI29)|].
                   apply (new_frame s m LB d lo (bv_unsigned sp) ch HR CHIN DPL LO HI29 _ NNq). exact (proj1 (refill_slot s m LB d lo (bv_unsigned sp) ch HR DPL LO HI29 ROOM)). }
        split; [exact WM2|]. split; [exact ACM2|]. split; [exact AVX2| exact MODEL].
      + (* [comment removed for export] *)
        eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
        { exact (free_arep_newhit_midR sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m s LB d lo ch bs sbs T rest RF
                   HR CHIN ALLOC UHI DEP DPL MI ST LO HI SPA SPT TP DLO DCAP NR TRNG LR RFT RFE RFX RF0 BLK SHB QSZ2 NNq HIT). }
        cbv beta. intros msF2 mo2 OK2 SBM _ PO.
        destruct PO as (b1 & actx & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & VIS2 & FC & HQ & DEP2 & MODEL).
        pose proof FC as (MU & WM2 & _).
        lazymatch type of HQ with ARHEAPQ ?sx _ _ _ _ =>
          apply (TAILS sx msF2 mo2); [| exact (inited_of_count st c (WF_cache st c WFs HC24) HIT)| exact (NUM_regions (a_st sx) st eq_refl (proj2 PINVH))| exact K];
          assert (ACM2 : acompl s sx d lo (bv_unsigned sp) m m2)
            by (apply (acompl_of_munchF s sx d lo (bv_unsigned sp) _ m m2 MU); apply Forall_app; split; [exact (head_compl s m d lo (bv_unsigned sp) ch sx R CHIN)|];
                pose proof (new_compl s m d lo (bv_unsigned sp) ch sx R CHIN DPL _ (hit_slot_sp s m ch R HIT)) as FC'; unfold enq_newR_W; unfold enq_new_W in FC';
                apply Forall_cons; [cbn [fst snd]; intros a Ha; apply (Forall_inv FC'); cbn [fst snd]; clear - Ha; lia| exact (Forall_inv_tail FC')]) end.
        eapply (MIDS_OF _ _ _ msF2 mo2 b1 actx t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2); try eassumption.
        * cbn -[Z.add]. intros E. apply app_eq_nil in E. destruct E as [_ E]. discriminate E.
        * cbn -[Z.add Z.mul Z.le kBatchSize kQuarantineMaxSize kMaxCacheSize]. clear - TQ0 TQ1 QSZ SZ1. zlets. unfold kBatchSize, kQuarantineMaxSize, kMaxCacheSize in *. lia.
        * (* [comment removed for export] *)
          apply (flagsx_transport _ m m2 (munch_agree _ _ _ MU) WM2); [| exact FXR]. intros a Ha N1 N2 N3 N4. apply outside_app. split; [exact (ZHs a Ha N1 N2 N3 N4)|].
          unfold enq_newR_W. cbn [outside].
          assert (LAX : LA = 0 \/ 0x10007fff8000 <= LA).
          { assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]).
            destruct D as [EL|NE]; [left; unfold LA, lb; rewrite EL; reflexivity| right].
            pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & _ & _ & _ & _ & LA1 & _). unfold AHI_LO in LA1. exact LA1. }
          assert (CPIN : In (hd 0 (pc_chunks (get_pc st c))) (pc_chunks (get_pc st c))).
          { pose proof (co_count _ _ (WF_cache st c WFs HC24)) as CC.
            destruct (pc_chunks (get_pc st c)) as [|x q]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
          pose proof (carved_in_space s OKs _ _ (carved_cache st c _ WFs HC24 CPIN)) as (CS1 & _).
          pose proof BT as BT'. unfold AIMG_TOP in Ha. clear - Ha LAX CS1 Y1 X1 LO BT'. acb. zlets. unfold a_sb, AHI_LO in *. repeat split; try exact I; lia.
        * apply (amframe_of_munch s LB' (bv_unsigned sp) _ m m2 MU). apply Forall_app.
          split; [exact (head_frame s m LB d lo (bv_unsigned sp) ch HR CHIN UHI DPL DFS LO HI29)|].
          pose proof (new_frame s m LB d lo (bv_unsigned sp) ch HR CHIN DPL LO HI29 _ NNq (hit_slot s m LB lo (bv_unsigned sp) ch HR LO HI29 HIT)) as FW.
          unfold enq_newR_W. unfold enq_new_W in FW. apply Forall_cons; [| exact (Forall_inv_tail FW)].
          cbn [fst snd]. pose proof (Forall_inv FW) as FW1. cbn [fst snd] in FW1.
          apply (apriv_mono s LB' (bv_unsigned sp) lo (bv_unsigned sp + -2208)); [first [clear; lia| clear - HI; lia] | first [clear; lia| clear - HI; lia] | exact FW1].
    - (* [comment removed for export] *)
      destruct (need_new_false_inv tq NNq) as [NE LT]. fold l lb lcount in NE, LT |- *.
      eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
      { exact (free_arep_app_midR sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m s LB d lo ch bs sbs T rest RF
                 HR CHIN ALLOC UHI DEP DPL MI ST LO HI SPA SPT TP DLO DCAP NR TRNG LR RFT RFE RFX RF0 BLK SHB QSZ2 (conj NE LT)). }
      cbv beta. intros msF2 mo2 OK2 SBM _ PO.
      destruct PO as (b1 & actx & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & VIS2 & FC & HQ & DEP2 & MODEL).
      pose proof FC as (MU & WM2 & _).
      lazymatch type of HQ with ARHEAPQ ?sx _ _ _ _ =>
        apply (TAILS sx msF2 mo2); [| exact (inited_of_tq st INITQH NE)| exact (NUM_regions (a_st sx) st eq_refl (proj2 PINVH))| exact K];
        assert (ACM2 : acompl s sx d lo (bv_unsigned sp) m m2)
          by (apply (acompl_of_munchF s sx d lo (bv_unsigned sp) _ m m2 MU); apply Forall_app; split; [exact (head_compl s m d lo (bv_unsigned sp) ch sx R CHIN)|];
              pose proof (app_compl s m d lo (bv_unsigned sp) ch sx R CHIN DPL NE LT) as FC';
              apply Forall_cons; [cbn [fst snd]; intros a Ha; apply (Forall_inv FC'); cbn [fst snd]; clear - Ha; lia| exact (Forall_inv_tail FC')]) end.
      eapply (MIDS_OF _ _ _ msF2 mo2 b1 actx t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2); try eassumption.
      * cbn -[Z.add]. intros E. apply app_eq_nil in E. destruct E as [_ E]. discriminate E.
      * cbn -[Z.add Z.mul Z.le kBatchSize kQuarantineMaxSize kMaxCacheSize]. clear - TQ0 TQ1 QSZ SZ1. zlets. unfold kBatchSize, kQuarantineMaxSize, kMaxCacheSize in *. lia.
      * apply (flagsx_transport _ m m2 (munch_agree _ _ _ MU) WM2); [| exact FXR]. intros a Ha N1 N2 N3 N4. apply outside_app. split; [exact (ZHs a Ha N1 N2 N3 N4)|].
        pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & _ & _ & CB & _ & LA1 & _). fold st tq l lb LA lcount in LA1, CB.
        pose proof BT as BT'. cbn [outside]. unfold AIMG_TOP in Ha. clear - Ha LA1 CB Y1 LO BT'. acb. zlets. unfold AHI_LO, OT_TQ in *. repeat split; try exact I; lia.
      * apply (amframe_of_munch s LB' (bv_unsigned sp) _ m m2 MU). apply Forall_app.
        split; [exact (head_frame s m LB d lo (bv_unsigned sp) ch HR CHIN UHI DPL DFS LO HI29)|].
        pose proof (app_frame s m LB d lo (bv_unsigned sp) ch HR CHIN DPL LO HI29 NE LT) as FW.
        apply Forall_cons; [| exact (Forall_inv_tail FW)].
        cbn [fst snd]. pose proof (Forall_inv FW) as FW1. cbn [fst snd] in FW1.
        apply (apriv_mono s LB' (bv_unsigned sp) lo (bv_unsigned sp + -2208)); [first [clear; lia| clear - HI; lia] | first [clear; lia| clear - HI; lia] | exact FW1].
  Qed.
End FreeGlueR.

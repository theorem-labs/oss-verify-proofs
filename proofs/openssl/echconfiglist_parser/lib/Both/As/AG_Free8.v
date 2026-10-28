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
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_Free7 SecLazy.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

(* [comment removed for export] *)
Ltac trp lem AG WM H Z B :=
  eapply (lem _ _ _ AG WM); [exact H|];
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
  let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; lia.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma amodelx_free : forall s mo ch tq' cache',
  AMODELX s mo -> AMODELX (free_s' s ch tq' cache' (a_L s) (a_S s) (a_AL s)) mo.
Proof. intros s mo ch tq' cache' A. exact A. Qed.
End HCW.

Section FreeRefillGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

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
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
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
  Definition fr_W : list ivl := WR ++ (Wh ++ Wn).

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
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : need_new tq = true.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.   (* [comment removed for export] *)
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf184) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition free_refill_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       lzok asegs (a_L sF) (a_S sF) (a_Zr sF) (mkCfg msF' mo')
    /\ restrict (a_L sF) (a_S sF) msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP sF (lb_remove U LB) m' /\ awin_vis sF m' /\ flagsx_rep m' /\ AMODELX sF mo'
    /\ DEPOT asegs d' m' /\ depot_placed sF d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch fr_W m m' /\ wmono asegs m m'
    /\ (exists st'' ev, am_free_full st U = Some (st'', ev) /\ same_but_shadow st'' (a_st sF)).

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
  Let RF := rf_facts st c WFs HC ROOM.
  Let PCc := rfd_pc_c st c WFs HC ROOM.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  Theorem free_arep_refill :
    (forall msF' mo', free_refill_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
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
            /\ sb mod 65536 = 0 /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ aceil <= lo /\ lo + 2944 <= bv_unsigned sp
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384 /\ c = 24).
    { assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
      assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
      clear - Y1 Y2 Y3 Y4 Y5 X1 X2 X3 LO HI E1 E2. zlets. unfold a_ri, a_sb, AHI_LO, kSpaceSize, kPageSize, kBatchClass in *. repeat split; lia. }
    assert (BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ mu <= mu' <= mu + 262144 /\ mfa <= mfa' <= mfa + 262144 /\ n = 1).
    { pose proof RF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
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
    { eapply (@free_head_refill _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo d (as_internal_init st)
                ATSD CTX TH (a_top s) (a_bot s) CH sb U size b1 actx ub kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize sbs
                k (hd 0 (map qb_addr l)) LA (qc_bytes tq)).
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
      - exact FCH.
      - exact Ha0.
      - constructor. clear - Z1 Z2 Z3 Z4 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - clear - Z1 QSZ. zlets. lia.
      - exact Hb1.
      - exact ACR.
      - clear - QSZ. zlets. unfold kMaxCacheSize, kQuarantineMaxSize, kQuarantineMinSize in *. lia.
      - exact SBS.
      - pose proof (batches_len_bound s m R) as BL. clear - BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - constructor. clear - X1 X2 X3. zlets. repeat split; assumption.
      - rewrite TP. exact IEN.
      - exact MI.
      - exact ST.
      - exact UNW.
      - exact FLG4.
      - exact IAX.
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
    destruct PO1 as (t0_1 & t1_1 & t2_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & jk & jke & rest & m1 & VIS1 & MU1 & WM1 & MI1 & ENV1 & ST1 & FR1 & PFR1 & ESO1 & TRB1 & LR & TFB1 & F41
                     & TRNG & NR1 & HDR1 & UW1 & TST1 & UNW1 & FLG1 & IA1 & DEP1 & SHF1 & TQ1 & PC11 & LC1).
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
    eapply (refill_sreach (a_L s) (a_S s) (a_Zr s) msF1 mo1 Q (wz 0x19b5cc) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0_1 t1_1 t2_1
              (wz (TH + OT_CACHE + PCLASS_SIZE * c)) (wz (TH + OT_CACHE)) (wz size) (wz AINST) a6_1 a7_1
              (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz size) (wz kMaxCacheSize) s7 s8 s9 s10 s11 t3_1 t4_1 t5_1 t6_1
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
    (* [comment removed for export] *)
    pose proof (after_refill_bundle s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3
                  MU1 WM1 MU2 WM2 MI MI2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1
                  b1 actx (d_putid d (depot_hash T)) (hd 0 (map qb_addr l)) (qc_bytes tq) HDR1 UW1 FLG1 IA1 SHF1 TQ1 LC1 INST) as ARB.
    destruct ARB as ((R2 & MIR' & WM0R' & AG0R' & FXR2) & (EB & A1 & A2 & BT & BUx & BD1 & BD2 & BPOS & BLA) & (N1 & CC & TK & CPS) & LAX
                     & BJ2 & HDR2 & UW2 & FLG2 & IA2 & SHF2 & TQ2 & LC2 & INST2 & PC12 & PC22 & PC32 & PC42 & UNW2).
    (* [comment removed for export] *)
    assert (ZK : forall a, bv_unsigned sp + -2272 <= a ->
                 outside (rf_W lo (bv_unsigned sp + -2272) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a)
      by (intros a Ha; exact (ZR_stack s m d lo (bv_unsigned sp) ch R DPL LO HI MISS ROOM a Ha)).
    assert (AG2 : agree_on (outside (rf_W lo (bv_unsigned sp + -2272) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu')) m1 m2) by exact (munch_agree _ _ _ MU2).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -2272)
              [CB 8 jke; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (wz size); C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x19b46c)])
      by (trp rw_cells_transport_pt AG2 WM2 FR1 ZK SPR).
    unfold put_frame in PFR1.
    assert (PFR2 : rw_cells asegs m2 (bv_unsigned sp + -2208)
              [C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
               C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (wz 1); C8 (wz 0x1bf2bc); C8 (wz U); C8 sp; C8 (wz 0x1bf32c)])
      by (trp rw_cells_transport_pt AG2 WM2 PFR1 ZK SPR).
    assert (ESO2 : rw_cells asegs m2 (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))])
      by (trp rw_cells_transport_pt AG2 WM2 ESO1 ZK SPR).
    assert (TRB2 : u64arr asegs m2 (bv_unsigned sp + -2128 + 16) (map wz T ++ rest)).
    { eapply (u64arr_transport_pt _ _ _ AG2 WM2); [exact TRB1|]. intros a Ha. apply ZK. clear - Ha. lia. }
    assert (TFB2 : rw_cells asegs m2 (bv_unsigned sp + -72) [C8 sp]) by (trp rw_cells_transport_pt AG2 WM2 TFB1 ZK SPR).
    assert (F42 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (trp rw_cells_transport_pt AG2 WM2 F41 ZK SPR).
    (* [comment removed for export] *)
    replace (wz (TH + OT_CACHE + PCLASS_SIZE * c)) with (wz (TH + 2128)) in VIS2 by (unfold OT_CACHE, PCLASS_SIZE, c, kBatchClass; f_equal; clear; lia).
    change (ret_pc (wz 0x19b5cc)) with (ret_pc (Z_to_bv 64 0x19b5cc)) in VIS2. rewrite (ret_pc_even 0x19b5cc) in VIS2 by (clear; lia).
    eapply (evt_sreach_lazy_at asegs L2 S2 (a_Zr s) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (@free_tail_refill _ sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc
                t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 (wz 0x19b5cc) m2
                lo T rest jk jke U size TH kMaxCacheSize sb k (hd 0 (map qb_addr l)) LA (qc_bytes tq) n chunks2 B j0 j1 j2 j3).
      - exact LO.
      - exact HI.
      - constructor. exact SPT.
      - constructor. clear - Z1 Z2 Z3 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - clear - Z1 QSZ. zlets. lia.
      - constructor. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _). fold TH in pT1, pT2, pT3. unfold kPageSize in pT1, pT2, pT3.
        split; [exact pT2|]. split; [exact pT3|]. clear - pT1. zlets. Z.div_mod_to_equations. lia.
      - constructor. clear - X1 X2 X3. zlets. repeat split; assumption.
      - exact CC.
      - clear - N1. zlets. rewrite N1. clear. lia.
      - exact CPS.
      - exact EB.
      - constructor. split; [exact A1| split; [exact A2| exact BT]].
      - pose proof (batches_len_bound s m R) as BL. clear - BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - split; [exact K4| exact NOD].
      - unfold kMaxCacheSize. clear. lia.
      - intros NZ. split; [exact (LC2 NZ)|].
        destruct LAX as [(_ & _ & KZ)|(_ & _ & L1 & L2' & L3 & L4 & _)]; [exfalso; exact (NZ KZ)|].
        split; [exact L1|]. split; [exact L2'|]. split; [exact L3|]. split; [exact (BLA NZ)| exact L4].
      - intros KZ. destruct LAX as [(_ & LA0 & _)|(_ & K1 & _)]; [exact LA0| exfalso; clear - KZ K1; zlets; lia].
      - exact LR.
      - exact NR1.
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
      - exact ESO2.
      - exact TRB2.
      - exact TFB2.
      - exact F42. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (j2' & m3 & RET & MU3 & WM3 & MI3 & TQ3 & LA3 & NB3 & NBJ3 & PC13 & PC33 & PC43 & STATS3).
    destruct RET as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & VIS3 & ST3).
    (* [comment removed for export] *)
    pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3) as WM03.
    destruct (head_cells3 s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3
                MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3
                b1 actx (d_putid d (depot_hash T)) HDR2 UW2 FLG2 IA2 SHF2 UNW2) as (HDR3 & UW3 & FLG3 & IA3 & SHF3 & TST3 & UNW3 & DAV).
    pose proof (arheap_after_refill_new s m d lo (bv_unsigned sp) ch bs L2 S2 AL' R CHIN ALLOC UHI DPL LO MISS ROOM NOD QSZ BLK m1 m2 j0 j1 j2 j3
                  MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3
                  LB b1 actx (d_putid d (depot_hash T)) j0 j1 j2' j3 ND LBs Hb1 HDR3 UW3 TST3 UNW3 FLG3 IA3 SHF3 TQ3 LA3 NB3 NBJ3 PC13 PC33 PC43 STATS3 WM03) as AH.
    apply K. unfold free_refill_gpost.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3.
    split; [exact OK3|]. split; [exact VIS3|]. split; [exact AH|].
    split. { intros x Hx. apply (win3 s m d lo ch R DPL LO MISS ROOM m2 POIu POIf m3 WM3 (a_S s) x Hx). intros Hx'. apply WM03. exact (AWV x Hx'). }
    split. { exact (flagsx3 s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3 MU1 WM1 MU2 WM2
                      PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3 WM03 (FXR2 FXR)). }
    split. { assert (HAL : 0 <= a_AL s <= a_AL s) by (clear - AB1a; lia).   (* [comment removed for export] *)
             pose proof (amodelx_after_refill s mo1 mo2 c L2 S2 AL' AMX1 OKs HC ROOM (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK))
                           eq_refl eq_refl VMM VMR VML (nonvm_same_atop _ _ NVS) VMN EAG HAL) as AMX2.   (* [comment removed for export] *)
             exact (amodelx_free sR mo3 ch tq' cache' (AMODELX_mat sR mo2 mo3 AMX2 SBM3)). }
    split. { assert (DEP2 : DEPOT asegs d' m2).
             { eapply (DEPOT_transport asegs d' m1 m2 _ DEP1 MU2 WM2). unfold d', depot_avoid. rewrite d_nb_put, d_sb_put.
               exact (ZR_depot s m d lo (bv_unsigned sp) ch R CHIN DPL LO MISS ROOM). }
             eapply (DEPOT_transport asegs d' m2 m3 _ DEP2 MU3 WM3). unfold d', depot_avoid. rewrite d_nb_put, d_sb_put. exact DAV. }
    split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split. { unfold depot_cov. unfold d'. rewrite d_nb_put, d_sb_put. intros x Hx.
             rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). exact (DCOV x Hx). }
    split; [exact MI3|]. split; [exact ST3|].
    split. { intros x Hx. unfold fr_W in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2].
             pose proof (AG0R' (bv_unsigned x) Hx1 (bv_unsigned_in_range _ x)) as E1.
             pose proof (AGR3 s m d lo (bv_unsigned sp) ch m2 m3 MU3 (bv_unsigned x) Hx2 (bv_unsigned_in_range _ x)) as E2.
             unfold wa in E1, E2. rewrite Z_to_bv_bv_unsigned in E1, E2. rewrite E2. exact E1. }
    split; [exact WM03|].
    (* [comment removed for export] *)
    assert (IM : forall a, U - 16 <= a -> a + 1 <= U + round_up size 8 -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply (aim_of_aapp _ _ a UHI); clear - Ha Hb; zlets; lia. }   (* [comment removed for export] *)
    assert (HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0).
    { change (as_space_beg st) with sb. unfold kHighMemBeg, kHighMemEnd, kSpaceSize. clear - BND. acb. Z.div_mod_to_equations. lia. }
    destruct (am_free_refill st ch (free_find st ch WFs CHIN) ALLOC ltac:(rewrite Q1, Q3; unfold kMaxCacheSize; clear - QSZ; lia)
                ltac:(change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); clear - Z4; zlets; Z.div_mod_to_equations; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5; zlets; unfold AHI_LO in *; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5 Z6; zlets; unfold AHI_LO in *; lia)
                cp (tl chunks2) WFs NN MISS ROOM HM TK BPOS ltac:(rewrite Q3; exact NOD)) as (st'' & ev & E & SBS').
    exists st'', ev. split; [exact E|].
    unfold free_new_state in SBS'. change (get_pc (refilled (set_internal_init st) kBatchClass) kBatchClass) with (get_pc st2 c) in SBS'.
    rewrite PCc in SBS'. cbn [pc_count refill_pc] in SBS'. exact SBS'.
  Qed.
End FreeRefillGlue.

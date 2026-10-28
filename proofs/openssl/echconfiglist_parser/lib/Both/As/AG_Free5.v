(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AsDepotHash AsUnwind CidBits AW_AllocBase AW_MallocBase AW_IAInit AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_RepQ.
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

Lemma need_new_true_full : forall t, need_new t = true -> qc_list t <> [] -> kBatchCount <= qb_count (last (qc_list t) (mkQB 0 0 0 [])).
Proof. intros t. unfold need_new. destruct (qc_list t) as [|b r]; intros NN NE; [exfalso; exact (NE eq_refl)| apply Z.leb_le; exact NN]. Qed.

Section FreeNewHit.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
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
  Let pc := get_pc st kBatchClass.
  Let cnt := pc_count pc.
  Let chunks := pc_chunks pc.
  Let cp := hd 0 chunks.
  Let B := compact_to_addr st kBatchClass cp.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st) (zidx kBatchClass) (mkPC (cnt - 1) (tl chunks)).
  Let s' := free_s' s ch tq' cache' (a_L s) (a_S s) (a_AL s).
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let Wn : list ivl := enq_new_W lo (bv_unsigned sp) TH B LA.
  Let W : list ivl := Wh ++ Wn.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
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
  Hypothesis HIT : cnt <> 0.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.

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
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  (* [comment removed for export] *)
  Lemma free_newhit_model : exists st'' ev, am_free_full st U = Some (st'', ev) /\ same_but_shadow st'' (a_st s') /\ syscalls_of ev = [].
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _ & _ & _ & _ & _ & _ & X1 & _ & _ & _ & _ & _ & _ & QM & _ & QC & _).
    assert (IM : forall a, U - 16 <= a -> a + 1 <= U + round_up size 8 -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply (aim_of_aapp _ _ a UHI); clear - Ha Hb; zlets; lia. }   (* [comment removed for export] *)
    pose proof (carved_in_space s OK _ _ (carved_cache st kBatchClass cp WFs HC24 ltac:(rewrite PCS; left; reflexivity))) as (S1 & _). fold st B in S1.
    destruct (am_free_newhit st ch (free_find st ch WFs CHIN) ALLOC ltac:(rewrite QM, QC; unfold kMaxCacheSize; clear - QSZ; lia)
                ltac:(change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); clear - Z4; zlets; Z.div_mod_to_equations; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5; zlets; unfold AHI_LO in *; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5 Z6; zlets; unfold AHI_LO in *; lia)
                cp (tl chunks) NN PCS HIT ltac:(clear - S1 X1; zlets; unfold a_sb, AHI_LO in *; lia) ltac:(rewrite QC; exact NOD)) as (st'' & ev & E & SBS & SC).
    exists st'', ev. split; [exact E|]. split; [exact SBS| exact SC].
  Qed.

  (* [comment removed for export] *)
  Definition free_newhit_gpost : machine_state -> Prop := fun ms' =>
    exists m', free_ret_post sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc lo m' ms'
      /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ ARHEAP s' (lb_remove U LB) m' /\ DEPOT asegs d' m'.

  Theorem free_arep_newhit :
    evt asegs free_newhit_gpost
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bf184) fc None m (seg_rom asegs)).
  Proof.
    destruct (free_cells s m ch R CHIN ALLOC UHI) as (b1 & actx & q0 & q1 & q2 & q3 & HDR & Hb1 & ACR & TST & UNW & QC & TQ & QST & INST & IEN).
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    pose proof (free_plu s m ch d R CHIN DPL) as PLU.
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof SHB as [[_ [_ SHu]] SBS].
    (* [comment removed for export] *)
    destruct (hit_cells_of_arep s m R kBatchClass ltac:(unfold kBatchClass, kNumClasses; lia) HIT)
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
    { eapply (@free_newhit _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo d (as_internal_init st)
                ATSD CTX TH (a_top s) (a_bot s) CH sb U size b1 actx ub kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize sbs
                k (hd 0 (map qb_addr l)) LA (qc_bytes tq)) with (cnt := cnt) (chunks := chunks) (B := B) (j0 := j0) (j1 := j1) (j2 := j2) (j3 := j3).
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
      - pose proof (batches_len_bound s m R) as BL. clear - K3 BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - exact K4.
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
      - exact NOD.
      - exact PC1.
      - replace (TH + 2136) with (TH + 2128 + 8) by (clear; lia). exact PC2.
      - replace (TH + 2144) with (TH + 2128 + 16) by (clear; lia). exact PC3.
      - replace (TH + 2144) with (TH + 2128 + 16) by (clear; lia). replace (TH + 2208) with (TH + 2128 + 80) by (clear; lia). exact PC4.
      - replace (TH + 2768) with (TH + 208 + 2560) by (clear; lia). exact QST'.
      - exact INST.
      - exact BJ. }
    intros ms' PO.
    destruct PO as (j2' & m' & RET & FC & TQ4 & LA4 & NB4 & NBJ4 & PC14 & PC34 & PC44 & ST4).
    destruct FC as (MU & WM & MI' & ST' & HDR' & UW' & TST' & UNW' & FLG' & IA' & DEP' & SHF' & _ & _).
    exists m'. split; [exact RET|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split; [| exact DEP'].
    assert (W0 : WF (set_internal_init st)) by (eapply WF_ext; [ .. | exact WFs]; reflexivity).
    pose proof (WF_free_new (set_internal_init st) ch W0 CHIN ALLOC cp (tl chunks) PCS ltac:(change (as_qcache (set_internal_init st)) with (as_qcache st); rewrite Q3; exact NOD)) as WF'.
    pose proof (WFQ_free_new (set_internal_init st) ch W0 CHIN ALLOC cp (tl chunks) PCS) as WQ'.
    destruct HR as (_ & ND & LBs).
    eapply (arheap_after_new s m m' d lo (bv_unsigned sp) ch bs cp (tl chunks) (a_L s) (a_S s) (a_AL s) b1 actx _ j0 j1 j2' j3
              R CHIN ALLOC UHI DPL LO PCS BLK (munch_agree _ _ _ MU) WM Hb1 HDR' UW' TST' UNW' FLG' IA' SHF' TQ4 LA4 NB4 NBJ4 PC14 PC34 PC44 ST4 WQ' LB WF' ND LBs).
  Qed.
End FreeNewHit.
End HCW.

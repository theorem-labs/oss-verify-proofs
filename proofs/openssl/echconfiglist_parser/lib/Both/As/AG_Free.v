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
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AS_Free3 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_MallocCold AG_MallocTop
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_Free7 AG_Free8 AG_Free9 SecLazy.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition FREE_COST : Z := 0.   (* [comment removed for export] *)

Lemma need_new_false_inv : forall t, need_new t = false -> qc_list t <> [] /\ qb_count (last (qc_list t) (mkQB 0 0 0 [])) < kBatchCount.
Proof.
  intros t. unfold need_new. destruct (qc_list t) as [|b q] eqn:E; intros H; [discriminate H|].
  split; [discriminate| apply Z.leb_gt in H; exact H].
Qed.

(* [comment removed for export] *)
Lemma flagsx_transport : forall (P : Z -> Prop) ma mb, agree_on P ma mb -> wmono asegs ma mb ->
  (forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
             ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) -> P a) ->
  flagsx_rep ma -> flagsx_rep mb.
Proof.
  intros P ma mb AG WM ZT FX.
  destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIAINIT, AIAINST, AIMG_TOP in *.
  Ltac trz AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
    let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; lia.
  split; [trz AG WM FXa ZT|]. split; [trz AG WM FXb ZT|]. split; [exists g; trz AG WM FXc ZT|]. split; [trz AG WM FXd ZT|]. exists bb; trz AG WM FXe ZT.
Qed.
End HCW.

Section FreeGlue.
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
  Let lcount := qb_count lb.
  Let c := kBatchClass.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 131072).
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  (* [comment removed for export] *)
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.   (* [comment removed for export] *)
  Hypothesis ROOM : rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf184) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition free_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ as_sec (a_st s') = as_sec (a_st s) /\ a_AL s - FREE_COST <= a_AL s'
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP s' (lb_remove U LB) m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo'
    /\ DEPOT asegs d' m' /\ depot_placed s' d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ amframe s (lb_remove U LB) (bv_unsigned sp) m m' /\ wmono asegs m m'
    /\ (exists st'' ev, am_free_full st U = Some (st'', ev) /\ same_but_shadow st'' (a_st s')).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
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

  Theorem free_arep_fast :
    (forall msF' mo', free_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. destruct AX as [AWV FXR].
    pose proof (free_pure s m ch R CHIN UHI) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    destruct (need_new tq) eqn:NNq.
    - destruct (Z.eq_dec (pc_count (get_pc st c)) 0) as [MISS|HIT].
      + (* [comment removed for export] *)
        eapply (free_arep_refill ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo CH ch bs sbs
                  HR CHIN ALLOC UHI (conj AWV FXR) AMX DEP DPL DCOV MI ST LO HI SPA SPT TP DLO DCAP FCH Ha0 BLK SHB QSZ2 NNq MISS NOD PROOM ROOM OK VISE).
        intros msF' mo' PO.
        destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & OK' & VIS' & HR' & AWV' & FX' & AMX'
                        & DEP' & DPL' & DCOV' & MI' & ST' & MU' & WM' & MODEL).
        apply K. unfold free_gpost. lazymatch type of HR' with ARHEAP ?sx _ _ => exists sx end. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [cbn [a_AL free_s']; unfold FREE_COST; clear; lia|].
        split; [exact OK'|]. split; [exact VIS'|]. split; [exact HR'|]. split; [exact AWV'|]. split; [exact FX'|]. split; [exact AMX'|].
        split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DCOV'|]. split; [exact MI'|]. split; [exact ST'|].
        split; [| split; [exact WM'| exact MODEL]].
        apply (amframe_of_munch s (lb_remove U LB) (bv_unsigned sp) _ m m' MU'). unfold fr_W. apply Forall_app. split.
        * exact (refill_frame s m LB d lo (bv_unsigned sp) ch HR DPL LO HI ROOM).
        * apply Forall_app. split; [exact (head_frame s m LB d lo (bv_unsigned sp) ch HR CHIN UHI DPL DFS LO HI)|].
          apply (new_frame s m LB d lo (bv_unsigned sp) ch HR CHIN DPL LO HI _ NNq). exact (proj1 (refill_slot s m LB d lo (bv_unsigned sp) ch HR DPL LO HI ROOM)).
      + (* [comment removed for export] *)
        eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
        { exact (free_arep_newhit ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB d lo CH ch bs sbs
                   HR CHIN ALLOC UHI DEP DPL MI ST LO HI SPA SPT TP DLO DCAP FCH Ha0 BLK SHB QSZ2 NNq HIT NOD). }
        cbv beta. intros msF' mo' OK' SBM _ PO.
        destruct PO as (m' & RET & MU' & WM' & MI' & HR' & DEP').
        destruct RET as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & VIS' & ST').
        apply K. unfold free_gpost. lazymatch type of HR' with ARHEAP ?sx _ _ => exists sx end. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [cbn [a_AL free_s']; unfold FREE_COST, COLD_COST; clear; lia|].
        split; [exact OK'|]. split; [exact VIS'|]. split; [exact HR'|].
        split; [intros x Hx; apply WM'; exact (AWV x Hx)|].
        split. { apply (flagsx_transport _ m m' (munch_agree _ _ _ MU') WM'); [| exact FXR]. intros a Ha N1 N2 N3 N4. apply outside_app. split; [exact (ZHs a Ha N1 N2 N3 N4)|].
                 unfold enq_new_W. cbn [outside].
                 assert (LAX : LA = 0 \/ 0x10007fff8000 <= LA).
                 { assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]).
                   destruct D as [EL|NE]; [left; unfold LA, lb; rewrite EL; reflexivity| right].
                   pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & _ & _ & _ & _ & LA1 & _). unfold AHI_LO in LA1. exact LA1. }
                 assert (CPIN : In (hd 0 (pc_chunks (get_pc st c))) (pc_chunks (get_pc st c))).
                 { pose proof (co_count _ _ (WF_cache st c WFs HC24)) as CC.
                   destruct (pc_chunks (get_pc st c)) as [|x q]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
                 pose proof (carved_in_space s OKs _ _ (carved_cache st c _ WFs HC24 CPIN)) as (CS1 & _).
                 pose proof PL as (_ & _ & _ & _ & _ & _ & _ & pT2 & _). pose proof (akobj_lit _ _ pT2) as BT. unfold kPageSize in BT. fold TH in BT.   (* [comment removed for export] *)
                 unfold AIMG_TOP in Ha. clear - Ha LAX CS1 Y1 X1 LO BT. acb. zlets. unfold a_sb, AHI_LO in *. repeat split; try exact I; lia. }
        split; [exact (amodelx_free s mo' ch _ _ (AMODELX_mat s mo mo' AMX SBM))|].
        split; [exact DEP'|].
        split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
        split; [unfold depot_cov; unfold d'; rewrite d_nb_put, d_sb_put; intros x Hx; rewrite (same_but_materialized_vmmaps mo mo' SBM); exact (DCOV x Hx)|].
        split; [exact MI'|]. split; [exact ST'|].
        split. { apply (amframe_of_munch s (lb_remove U LB) (bv_unsigned sp) _ m m' MU'). apply Forall_app.
                 split; [exact (head_frame s m LB d lo (bv_unsigned sp) ch HR CHIN UHI DPL DFS LO HI)|].
                 apply (new_frame s m LB d lo (bv_unsigned sp) ch HR CHIN DPL LO HI _ NNq). exact (hit_slot s m LB lo (bv_unsigned sp) ch HR LO HI HIT). }
        split; [exact WM'|].
        destruct (free_newhit_model ra sp s0 m s LB d lo CH ch bs HR CHIN ALLOC UHI QSZ2 NNq HIT NOD) as (st'' & ev & E1 & E2 & _).
        exists st'', ev. split; [exact E1| exact E2].
    - (* [comment removed for export] *)
      destruct (need_new_false_inv tq NNq) as [NE LT]. fold l lb lcount in NE, LT |- *.
      eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
      { exact (free_arep_app ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB d lo CH ch bs sbs
                 HR CHIN ALLOC DEP DPL MI ST LO HI SPA SPT TP DLO DCAP FCH Ha0 BLK SHB QSZ2 (conj NE LT) ltac:(clear - NOD; zlets; unfold kBatchSize in *; lia) UHI). }
      cbv beta. intros msF' mo' OK' SBM _ PO.
      destruct PO as (m' & RET & MU' & WM' & MI' & HR' & DEP').
      destruct RET as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & VIS' & ST').
      apply K. unfold free_gpost. lazymatch type of HR' with ARHEAP ?sx _ _ => exists sx end. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [cbn [a_AL free_s']; unfold FREE_COST, COLD_COST; clear; lia|].
      split; [exact OK'|]. split; [exact VIS'|]. split; [exact HR'|].
      split; [intros x Hx; apply WM'; exact (AWV x Hx)|].
      split. { apply (flagsx_transport _ m m' (munch_agree _ _ _ MU') WM'); [| exact FXR]. intros a Ha N1 N2 N3 N4. apply outside_app. split; [exact (ZHs a Ha N1 N2 N3 N4)|].
               pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & _ & _ & CB & _ & LA1 & _). fold st tq l lb LA lcount in LA1, CB.
               pose proof PL as (_ & _ & _ & _ & _ & _ & _ & pT2 & _). pose proof (akobj_lit _ _ pT2) as BT. unfold kPageSize in BT. fold TH in BT.   (* [comment removed for export] *)
               cbn [outside]. unfold AIMG_TOP in Ha. clear - Ha LA1 CB Y1 LO BT. acb. zlets. unfold AHI_LO, OT_TQ in *. repeat split; try exact I; lia. }
      split; [exact (amodelx_free s mo' ch _ _ (AMODELX_mat s mo mo' AMX SBM))|].
      split; [exact DEP'|].
      split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
      split; [unfold depot_cov; unfold d'; rewrite d_nb_put, d_sb_put; intros x Hx; rewrite (same_but_materialized_vmmaps mo mo' SBM); exact (DCOV x Hx)|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { apply (amframe_of_munch s (lb_remove U LB) (bv_unsigned sp) _ m m' MU'). apply Forall_app.
               split; [exact (head_frame s m LB d lo (bv_unsigned sp) ch HR CHIN UHI DPL DFS LO HI)|].
               exact (app_frame s m LB d lo (bv_unsigned sp) ch HR CHIN DPL LO HI NE LT). }
      split; [exact WM'|].
      destruct (free_app_model sp m s LB d lo ch HR CHIN ALLOC DPL LO HI QSZ2 (conj NE LT) ltac:(clear - NOD; zlets; unfold kBatchSize in *; lia) UHI) as (st'' & ev & E1 & E2 & _).
      exists st'', ev. split; [exact E1| exact E2].
  Qed.
End FreeGlue.

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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsConst.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_ReallocPre AW_ReallocMid AW_ReallocRet
     AG_WFHit AG_MallocModel AG_RefillModel AG_ColdModel AG_Malloc AG_Malloc2 AG_WriteSet AG_Frame AG_MallocAll
     AS_Refill1 AG_Refill1 AG_Refill2 AG_Refill3 AG_MallocCold AG_MallocTop AG_Free1 AG_Free2 AG_Free6 AG_Free7 AG_Free AG_FreeModel
     AG_RecycleDefs AG_ComplFrame AG_FreeTail AG_FreeTailR AG_FreeTopR AG_ReallocF2 AG_ReallocCold AG_ReallocMid SecLazy AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section HCW.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Lemma d_put_twice : forall d h n, 0 <= d_ids d -> d_put (d_put d h n) h n = d_put d h n.
  Proof.
    intros d h n H. unfold d_put. destruct (d_find d h =? 0) eqn:E; [| rewrite E; reflexivity].
    replace (d_find (d_insert d h n) h =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq.
    unfold d_find, d_insert. cbn [d_hash d_chain]. rewrite Z.eqb_refl. cbn [find_hash]. rewrite Z.eqb_refl, Z.eqb_refl. lia.
  Qed.
  Lemma lb_remove_cons_ne : forall (U n P0 : Z) LB, U <> P0 -> lb_remove P0 ((U, n) :: LB) = (U, n) :: lb_remove P0 LB.
  Proof. intros U n P0 LB NE. unfold lb_remove. cbn [List.filter fst negb]. replace (U =? P0) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. Qed.
End HCW.

Section ReallocGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).
  Variables (och : chunk) (bs sbs : list byte).

  Let st := a_st s.
  Let TH := a_thr s.
  Let sb := a_sb s.
  Let rz := rz_size size.
  Let needed := round_up (Z.max size 8) 8 + rz.
  Let c := class_id needed.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf8f0 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let P0 := ch_user_beg och.
  Let old := ch_used och.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 131072).
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3280 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis DCAP2 : d_ids d' + 1 < 65536 /\ d_frames d' + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz P0.
  Hypothesis Ha1 : a1 = wz size.
  Hypothesis CHIN0 : In och (chunk_list st).
  Hypothesis ALLOC0 : ch_state och = CAllocated.
  Hypothesis OLDSZ : old <= 64512.
  Hypothesis SZB : size <= 64512.
  Hypothesis BLK0 : rw_cells asegs m P0 [CB (Z.to_nat old) bs].
  Hypothesis SHB0 : SHAD m P0 sbs /\ Z.of_nat (length sbs) = nsh old.
  Hypothesis AC : ACONST m.
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.
  Hypothesis ROOM : rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis MIDQ : forall (sM : ast) (UM : Z) (stM : astate) (mM : mem),
    ARHEAP sM ((UM, size) :: LB) mM ->
    (forall kaddr, exists st'' ev, am_malloc_k st size kaddr = Some (UM, st'', ev) /\ same_but_shadow st'' stM) ->
    a_st sM = set_internal_init stM ->
    INITQ (a_st sM) /\ PINV (a_st sM) /\ nalloc (a_st sM) <= LIVEB /\ pusage (a_st sM) + COLD_COST <= B_PRIM
    /\ rg_mapped_user (get_region (a_st sM) kBatchClass) + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf7b4) fc None m (seg_rom asegs).

  Definition realloc_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (U : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec st))
    /\ a_AL s - FREE_COST <= a_AL s'
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz U) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP s' ((U, size) :: lb_remove P0 LB) m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo' /\ nonvm_same mo mo'
    /\ DEPOT asegs d' m' /\ depot_placed s' d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ amframe s (lb_remove P0 LB) (bv_unsigned sp) m m' /\ avis s s' m m'
    /\ acompl s s' d lo (bv_unsigned sp) m m' /\ avmx s s' mo mo'
    /\ rw_cells asegs m' U [CB (Z.to_nat size) (firstn (Z.to_nat (Z.min size old)) bs ++ skipn (Z.to_nat (Z.min size old)) junk)] /\ length junk = Z.to_nat size
    /\ addressable m' U size
    /\ U <> P0
    /\ (exists stM st2 ev2, (forall kaddr, exists st1 ev1, am_malloc_k st size kaddr = Some (U, st1, ev1) /\ same_but_shadow st1 stM)
                         /\ (WF (set_internal_init stM) /\ INITQ (set_internal_init stM) /\ PINV (set_internal_init stM) /\ nalloc (set_internal_init stM) <= LIVEB)
                         /\ am_free_full (set_internal_init stM) P0 = Some (st2, ev2) /\ same_but_shadow st2 (a_st s')).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HLB : forall b, In b LB -> In b (alb s). Proof. intros b Hb. exact (proj1 (proj2 (proj2 HR) b) Hb). Qed.
  Let INLB : In (P0, old) LB.
  Proof. apply (proj2 (proj2 (proj2 HR) (P0, old))). unfold alb. apply in_map_iff. exists och. split; [reflexivity|]. apply filter_In. split; [exact CHIN0|]. unfold is_alloc. rewrite ALLOC0. reflexivity. Qed.
  Let O1 : 1 <= old. Proof. exact (proj1 (free_pure s m och R CHIN0 (uhi_of_arep s m och R CHIN0))). Qed.
  Let DIDS : 0 <= d_ids d. Proof. pose proof (wf_ids d (proj1 DEP)) as W1. clear - W1. lia. Qed.

  Theorem realloc_arep :
    (forall msF' mo', realloc_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    apply (realloc_arep_mid ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo size CH och bs sbs
             HR AX AMX DEP DPL DFS DCOV MI ST LO ltac:(clear - HI; lia) SPA SPT SZ TP DCAP FCH Ha0 Ha1 CHIN0 ALLOC0 OLDSZ SZB BLK0 SHB0 AC PROOM ROOM OK VISE).
    intros sM UM stM msF2 mo2 PO.
    destruct PO as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & cfu & jk & jr1 & jr2 & junk & rest & m2
                    & Ethr & Ectx & Efsb & Ezr & Etop & Ebot & Esb & Epa & Esec & Eal & Est & OK2 & VIS2 & HR2 & AWV2 & FX2 & AMX2 & NV2 & DEP2 & DPL2 & DCOV2
                    & MI2 & ST2 & AMF2 & WM2 & ACM2 & AVX2 & BLK & LJ & ADDR & MODEL & RFR2 & OBLK2 & OSH2 & FLG2 & IA2 & TRNG & NRT & LR).
    change (length rest = (255 - length T)%nat) in LR. change (Forall (fun x => 0 <= x < 2^64) T) in TRNG. change ((1 <= length T <= 30)%nat) in NRT.
    change (rframes sp ra s0 s1 s2 s3 s4 s5 s6 T rest jk jr1 jr2 cfu P0 size m2) in RFR2. change (DEPOT asegs d' m2) in DEP2. change (depot_placed sM d') in DPL2. change (depot_cov d' mo2) in DCOV2.
    destruct (MIDQ sM UM stM m2 HR2 MODEL Est) as (IQ2 & PI2 & NAL2 & PROOM2 & ROOM2).
    (* [comment removed for export] *)
    pose proof (proj1 HR2) as R2. pose proof (proj1 R2) as OK2s. pose proof (proj2 OK2s) as WF2.
    destruct (alb_In sM P0 old (proj1 (proj2 (proj2 HR2) (P0, old)) (or_intror INLB))) as (x & XIN & XAL & XU & XN).
    assert (UNW2 : rw_cells asegs m2 (a_thr sM + 3168) [C1 (b8 0)]).
    { destruct R2 as (_ & _ & _ & THR & _). destruct THR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U0). exact U0. }
    pose proof (ARHEAP_block_range_thm sM OK2s ((UM, size) :: LB) m2 UM size HR2 (or_introl eq_refl)) as UR.
    assert (NEQ : UM <> P0).
    { intros E. pose proof (proj1 (proj2 HR2)) as ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E.
      destruct (alb_In sM UM size (proj1 (proj2 (proj2 HR2) (UM, size)) (or_introl eq_refl))) as (y & YIN & YAL & YU & YN).
      pose proof (proj1 (chunk_list_find _ x (WF_keys _ WF2)) XIN) as FX. pose proof (proj1 (chunk_list_find _ y (WF_keys _ WF2)) YIN) as FY.
      rewrite XU in FX. rewrite YU, E in FY. rewrite FX in FY. injection FY as EXY. subst y. rewrite <- YN, XN. exact INLB. }
    (* [comment removed for export] *)
    set (RFr := fun mx : mem => rframes sp ra s0 s1 s2 s3 s4 s5 s6 T rest jk jr1 jr2 cfu P0 size mx).
    set (RF := fun mx : mem => RFr mx /\ rw_cells asegs mx (a_thr sM + 3168) [C1 (b8 0)] /\ rw_cells asegs mx AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after mx).
    assert (SPR : 0 <= bv_unsigned sp < 2^64) by (pose proof (bv_unsigned_in_range _ sp) as X; change (bv_modulus 64) with (2^64) in X; exact X).
    assert (LTB : (length (map wz T ++ rest) = 255)%nat) by (rewrite length_app, length_map, LR; clear - NRT; lia).
    assert (RFrT : forall W0 m0 m1, RFr m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 -> disjoint_from W0 (bv_unsigned sp + -2208) 2208 -> RFr m1).
    { intros W0 m0 m1 H MU0 WM0 D0. subst RFr. cbv beta in H |- *. unfold rframes in H |- *. destruct H as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      Ltac dsub D0 := eapply disjoint_from_sub; [exact D0| lia| lia].
      split; [eapply rw_cells_transport; [exact C1| exact MU0| exact WM0| cbn [cells_size csize Nat.add]; dsub D0]|].
      split; [eapply rw_cells_transport; [exact C2| exact MU0| exact WM0| cbn [cells_size csize Nat.add]; dsub D0]|].
      split; [eapply rw_cells_transport; [exact C3| exact MU0| exact WM0| cbn [cells_size csize Nat.add]; dsub D0]|].
      split; [eapply rw_cells_transport; [exact C4| exact MU0| exact WM0| cbn [cells_size csize Nat.add]; dsub D0]|].
      split; [eapply u64arr_transport; [exact C5| exact MU0| exact WM0| rewrite LTB; clear - D0 NRT; dsub D0]|].
      split; [eapply rw_cells_transport; [exact C6| exact MU0| exact WM0| cbn [cells_size csize Nat.add]; dsub D0]|].
      eapply rw_cells_transport; [exact C7| exact MU0| exact WM0| cbn [cells_size csize Nat.add]; dsub D0]. }
    assert (RFrA : forall m0 m1, RFr m0 -> agree_on (fun a => bv_unsigned sp + -2208 <= a) m0 m1 -> RFr m1).
    { intros m0 m1 H AG0. subst RFr. cbv beta in H |- *. unfold rframes in H |- *. destruct H as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      Ltac dpt := cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]; intros; lia.
      split; [eapply (rw_cells_pteq _ m0 m1 AG0); [exact C1| dpt]|]. split; [eapply (rw_cells_pteq _ m0 m1 AG0); [exact C2| dpt]|].
      split; [eapply (rw_cells_pteq _ m0 m1 AG0); [exact C3| dpt]|]. split; [eapply (rw_cells_pteq _ m0 m1 AG0); [exact C4| dpt]|].
      split; [eapply (u64arr_pteq _ m0 m1 AG0); [exact C5| rewrite LTB; intros; lia]|].
      split; [eapply (rw_cells_pteq _ m0 m1 AG0); [exact C6| dpt]| eapply (rw_cells_pteq _ m0 m1 AG0); [exact C7| dpt]]. }
    assert (RFT : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 -> disjoint_from W0 (bv_unsigned sp + -2208) 2208 ->
                  disjoint_from W0 (a_thr sM + 3168) 1 -> disjoint_from W0 AIAINIT 4 -> disjoint_from W0 AIAINST 0x81030 -> RF m1).
    { intros W0 m0 m1 (H1 & H2 & H3 & H4) MU0 WM0 D1 D2 D3 D4. subst RF. cbv beta. split; [exact (RFrT W0 m0 m1 H1 MU0 WM0 D1)|].
      split; [eapply rw_cells_transport; [exact H2| exact MU0| exact WM0| exact D2]|].
      split; [eapply rw_cells_transport; [exact H3| exact MU0| exact WM0| exact D3]|].
      exact (ia_if_transport true W0 m0 m1 H4 MU0 WM0 D4). }
    assert (RFP : forall W0 m0 m1, RF m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 ->
                  (forall a, bv_unsigned sp + -2208 <= a < bv_unsigned sp -> outside W0 a) -> outside W0 (a_thr sM + 3168) ->
                  (forall a, AIAINIT <= a < AIAINIT + 4 -> outside W0 a) -> (forall a, AIAINST <= a < AIAINST + 0x81030 -> outside W0 a) -> RF m1).
    { intros W0 m0 m1 (H1 & H2 & H3 & H4) MU0 WM0 Z1 Z2 Z3 Z4. pose proof (munch_agree _ _ _ MU0) as AG0. subst RF RFr. cbv beta in H1 |- *.
      split.
      { unfold rframes in H1 |- *. destruct H1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
        Ltac dpo Z1 := cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]; let Ha := fresh in intros ? Ha; apply Z1; clear - Ha; lia.
        split; [eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact C1| dpo Z1]|]. split; [eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact C2| dpo Z1]|].
        split; [eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact C3| dpo Z1]|]. split; [eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact C4| dpo Z1]|].
        split; [eapply (u64arr_transport_pt _ m0 m1 AG0 WM0); [exact C5| rewrite LTB; clear - Z1 NRT; intros a Ha; apply Z1; clear - Ha; lia]|].
        split; [eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact C6| dpo Z1]| eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact C7| dpo Z1]]. }
      split. { eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact H2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. intros a Ha. replace a with (a_thr sM + 3168) by (clear - Ha; lia). exact Z2. }
      split. { eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact H3|]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length]. intros a Ha. apply Z3. clear - Ha. lia. }
      unfold ia_after in H4 |- *. unfold AIAINST in Z4 |- *. destruct H4 as (I1 & I2 & I3).
      split; [| split].
      - eapply (u8arr_transport_pt _ m0 m1 AG0 WM0); [exact I1|]. rewrite repeat_length, Z2Nat.id by (clear; lia). intros a Ha. apply Z4. clear - Ha. lia.
      - eapply (rw_cells_transport_pt _ m0 m1 AG0 WM0); [exact I2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length]. intros a Ha. apply Z4. clear - Ha. lia.
      - eapply (u8arr_transport_pt _ m0 m1 AG0 WM0); [exact I3|]. rewrite repeat_length, Z2Nat.id by (clear; lia). intros a Ha. apply Z4. clear - Ha. lia. }
    eapply (free_arepR sp gp tp t0' t1' t2' a6' a7' t3' t4' t5' t6' (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz AINST) (wz (Z.min size old)) (wz UM)
              (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 F fc m2 msF2 mo2 Q sM ((UM, size) :: LB) d' lo x bs sbs T rest RF RFr
              HR2 XIN XAL (conj AWV2 FX2) AMX2 DEP2 DPL2).
    { rewrite Efsb. unfold d'. rewrite d_nb_put, d_sb_put. exact DFS. }
    { exact DCOV2. } { exact MI2. } { exact ST2. } { exact LO. } { exact HI. } { exact SPA. } { exact SPT. } { exact TP. } { exact DCAP2. }
    { exact NRT. } { exact TRNG. } { exact LR. }
    { exact RFT. }
    { intros m0 (H1 & _). subst RFr. cbv beta in H1. unfold rframes in H1. destruct H1 as (_ & _ & _ & C4 & C5 & _). exact (conj C4 C5). }
    { intros m0 (_ & H2 & H3 & H4). exact (conj H2 (conj H3 H4)). }
    { exact RFP. }
    { subst RF RFr. cbv beta. split; [exact RFR2|]. split; [exact UNW2|]. exact (conj FLG2 IA2). }
    { intros m0 (H1 & _). exact H1. }
    { exact RFrT. } { exact RFrA. }
    { rewrite XU, XN. exact OBLK2. } { rewrite XU, XN. exact (conj OSH2 (proj2 SHB0)). }
    { rewrite XN. unfold kQuarantineMaxSize. clear - OLDSZ. lia. }
    { exact IQ2. } { exact PI2. } { exact NAL2. } { exact PROOM2. } { exact ROOM2. } { exact OK2. }
    { rewrite XU. exact VIS2. }
    intros msF3 mo3 PO3.
    destruct PO3 as (s' & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3
                    & E_thr & E_ctx & E_fsb & E_zr & E_top & E_bot & SUB & AL & OK3 & VIS3 & HR3 & AWV3 & FX3 & AMX3 & NV3 & DEP3 & DPL3 & DCOV3
                    & MI3 & ST3 & RFR3 & AMF3 & AVI3 & ACM3 & AVX3 & MODEL3).
    (* [comment removed for export] *)
    subst RFr. cbv beta in RFR3.
    eapply (evt_sreach_lazy_at asegs (a_L s') (a_S s') (a_Zr s') _ msF3 _ mo3 Q OK3 VIS3).
    { eapply (realloc_retF sp ra s0 s1 s2 s3 s4 s5 s6 gp tp s7 s8 s9 s10 s11 F fc lo T rest jk jr1 jr2 cfu P0 size UM); [clear - HI; lia| exact LR| exact NRT| | exact MI3| exact ST3| exact RFR3].
      destruct UR as (U1 & U2 & U3 & U4 & U5). unfold AIMG_TOP in U1. clear - U1 U3 U4. acb. lia. }
    cbv beta. intros msF4 mo4 OK4 SBM4 _ PO4. destruct PO4 as (v0 & v1 & v2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & VIS4 & ST4).
    (* [comment removed for export] *)
    apply K. unfold realloc_gpost.
    exists s', UM, v0, v1, v2, w1, w2, w3, w4, w5. exists w6, w7, v3, v4, v5, v6, junk, m3.
    split; [rewrite E_thr; exact Ethr|]. split; [rewrite E_ctx; exact Ectx|]. split; [rewrite E_fsb; exact Efsb|]. split; [rewrite E_zr; exact Ezr|].
    split; [rewrite E_top; exact Etop|]. split; [rewrite E_bot; exact Ebot|].
    split; [intros sc Hsc; rewrite <- Esec; exact (SUB sc Hsc)|].
    split; [rewrite <- Eal; exact AL|].
    split; [exact OK4|]. split; [exact VIS4|].
    split; [rewrite <- (lb_remove_cons_ne UM size P0 LB NEQ); rewrite <- XU; exact HR3|].
    split; [exact AWV3|]. split; [exact FX3|]. split; [exact (AMODELX_mat s' mo3 mo4 AMX3 SBM4)|].
    split; [exact (nonvm_same_trans _ _ _ NV2 (nonvm_same_trans _ _ _ NV3 (nonvm_same_mat _ _ SBM4)))|].
    split; [unfold d' in DEP3 |- *; rewrite (d_put_twice d (depot_hash T) nT DIDS) in DEP3; exact DEP3|].
    split; [unfold d' in DPL3 |- *; rewrite (d_put_twice d (depot_hash T) nT DIDS) in DPL3; exact DPL3|].
    split; [unfold d' in DCOV3 |- *; rewrite (d_put_twice d (depot_hash T) nT DIDS) in DCOV3; exact (depot_cov_mat _ mo3 mo4 DCOV3 SBM4)|].
    split; [exact MI3|]. split; [exact ST4|].
    split.
    { (* [comment removed for export] *)
      apply (amframe_trans s (lb_remove P0 LB) (bv_unsigned sp) m m2 m3).
      - intros a Ha CL. apply (AMF2 a Ha). revert CL. unfold aclient. intros [C|[C|[(A & n & Hin & C)|[(A & n & Hin & C)|C]]]]; [left; exact C| right; left; exact C| | | do 4 right; exact C].
        + right; right; left. exists A, n. split; [exact (proj1 (proj1 (lb_remove_In P0 LB (A, n)) Hin))| exact C].
        + right; right; right; left. exists A, n. split; [exact (proj1 (proj1 (lb_remove_In P0 LB (A, n)) Hin))| exact C].
      - intros a Ha CL. apply (AMF3 a Ha). rewrite XU. rewrite (lb_remove_cons_ne UM size P0 LB NEQ). revert CL. unfold aclient. rewrite Efsb.
        intros [C|[C|[(A & n & Hin & C)|[(A & n & Hin & C)|C]]]]; [left; exact C| right; left; exact C| | | do 4 right; exact C].
        + right; right; left. exists A, n. split; [right; exact Hin| exact C].
        + right; right; right; left. exists A, n. split; [right; exact Hin| exact C]. }
    split; [exact (avis_trans s sM s' m m2 m3 ltac:(intros sc Hsc; rewrite <- Esec; exact Hsc) SUB (avis_of_wmono s sM m m2 WM2) AVI3)|].
    split; [exact (acompl_trans s sM s' d lo (bv_unsigned sp) m m2 m3 (conj Ethr (conj Esb Epa)) ltac:(intros sc Hsc; rewrite <- Esec; exact Hsc) ACM2 ltac:(unfold d' in ACM3; rewrite acompl_dput in ACM3; exact ACM3))|].
    split; [exact (avmx_trans s sM s' mo mo2 mo4 ltac:(intros sc Hsc; rewrite <- Esec; exact Hsc) SUB AVX2 (avmx_mat_r sM s' mo2 mo3 mo4 AVX3 SBM4))|].
    assert (AGc : agree_on (aclient sM (lb_remove (ch_user_beg x) ((UM, size) :: LB)) (bv_unsigned sp)) m2 m3) by (intros a Pa Ha; exact (AMF3 a Ha Pa)).
    assert (INU : In (UM, size) (lb_remove (ch_user_beg x) ((UM, size) :: LB))) by (rewrite XU, (lb_remove_cons_ne UM size P0 LB NEQ); left; reflexivity).
    split.
    { eapply (rw_cells_pteq _ m2 m3 AGc); [exact BLK|]. cbn [cells_size csize Nat.add Nat.mul]. rewrite Nat.add_0_r, Z2Nat.id by (clear - SZ; lia).
      intros a Ha. right; right; left. exists UM, size. exact (conj INU Ha). }
    split; [exact LJ|].
    split.
    { destruct ADDR as [Hn (A0 & A8 & U8)]. split; [exact Hn|]. split; [exact A0|]. split; [exact A8|].
      eapply (u8arr_pteq _ m2 m3 AGc); [exact U8|]. rewrite shadow_of_length by exact Hn.
      intros a Ha. right; right; right; left. exists UM, size. exact (conj INU Ha). }
    split; [exact NEQ|].
    destruct MODEL3 as (st2 & ev2 & MF & SB2). exists stM, st2, ev2. split; [exact MODEL|]. rewrite Est, XU in MF.
    split; [rewrite <- Est; exact (conj WF2 (conj IQ2 (conj PI2 NAL2)))|]. exact (conj MF SB2).
  Qed.
End ReallocGlue.

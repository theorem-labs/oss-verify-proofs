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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AW_Drain AW_Put3 AS_Free1 AS_Free2 AS_Free3 AS_Free4 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_MallocCold AG_MallocTop
     AG_FreeModel AG_FreeModel2 AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free9 AG_RepQ AG_RepQFacts AG_RepQFacts2
     AG_FreeMid AG_FreeTail SecLazy AG_WriteSet AG_RecycleDefs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_PutR1 AW_EnqueueR1 AW_PutR2 AW_PutR3 AG_FreeTail AG_FreeTailR AG_FreeT1.
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
(* [comment removed for export] *)

Lemma hd_app_hd : forall (d : Z) (l1 l2 : list Z), hd d (l1 ++ l2) = hd (hd d l2) l1.
Proof. intros d l1 l2. destruct l1; reflexivity. Qed.
Lemma last_app_nonnil : forall (d : Z) (l1 l2 : list Z), l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros d l1 l2 NE. induction l1 as [|x l1 IH]; [reflexivity|]. cbn [app]. destruct (l1 ++ l2) as [|y r] eqn:E.
  - apply app_eq_nil in E. destruct E as [_ E]. exfalso. exact (NE E).
  - change (last (x :: y :: r) d) with (last (y :: r) d). exact IH.
Qed.
Lemma map_nonnil {A B} : forall (f : A -> B) l, l <> [] -> map f l <> [].
Proof. intros f l NE. destruct l; [intros _; exact (NE eq_refl)| discriminate]. Qed.

Lemma WFQ_transfer : forall st, WFQ st [] [] -> WFQ (transfer_m st) [] [].
Proof.
  intros st WQ. pose proof WQ as WW.
  destruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys & Wxc & Wxb).
  unfold WFQ. rewrite !app_nil_r. rewrite app_nil_r in Wnd, Wndb.
  change (as_tq (transfer_m st)) with qcache0.
  change (as_gq (transfer_m st)) with (mkQC (qc_list (as_gq st) ++ qc_list (as_tq st)) (qc_bytes (as_gq st) + qc_bytes (as_tq st))).
  change (chunk_list (transfer_m st)) with (chunk_list st). change (as_sec (transfer_m st)) with (as_sec st).
  change (as_n_reserved (transfer_m st)) with (as_n_reserved st). change (as_regions (transfer_m st)) with (as_regions st).
  change (as_cache (transfer_m st)) with (as_cache st). change (as_chunks (transfer_m st)) with (as_chunks st).
  change (as_qmax (transfer_m st)) with (as_qmax st). change (as_qmin (transfer_m st)) with (as_qmin st). change (as_qcache (transfer_m st)) with (as_qcache st).
  cbn [qc_list qc_bytes qcache0]. cbn [app].
  split. { intros c Hc. destruct (Wrc c Hc) as [R0 C0]. split; [destruct R0; constructor; assumption| destruct C0; constructor; assumption]. }
  split. { apply (Permutation_NoDup (l := carved_addr_list st)); [| exact Wnd]. unfold carved_addr_list.
           apply Permutation_app; [apply Permutation_refl|]. apply Permutation_app; [apply Permutation_refl|].
           change (as_tq (transfer_m st)) with qcache0.
           change (as_gq (transfer_m st)) with (mkQC (qc_list (as_gq st) ++ qc_list (as_tq st)) (qc_bytes (as_gq st) + qc_bytes (as_tq st))).
           cbn [qc_list qcache0 app]. rewrite !map_app. apply Permutation_app_comm. }
  split; [exact Wch|]. split; [exact Winj|]. split; [exact Wsec|]. split; [exact Wsnd|]. split; [exact Wres1|]. split; [exact Wres2|].
  split; [split; [intros b []| reflexivity]|].
  split. { split.
           - cbn [qc_list]. intros b Hb. apply in_app_iff in Hb. apply (WFQ_batch st [] [] b WQ). apply in_app_iff. tauto.
           - cbn [qc_list qc_bytes]. rewrite fold_qb_app, (proj2 Wtq), (proj2 Wgq). lia. }
  split. { apply (Permutation_NoDup (l := flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st)))); [| exact Wndb].
           rewrite !flat_map_app'. apply Permutation_app_comm. }
  split. { intros y Hy Qy. destruct (Wq y Hy Qy) as [[b [Hb Hq]]|[]]. left. exists b. split; [| exact Hq]. apply in_app_iff in Hb. apply in_app_iff. tauto. }
  split; [exact Wm0|]. split; [exact Wm31|]. split; [exact Wpc0|]. split; [exact Wpc31|]. split; [exact WlenR|]. split; [exact WlenC|].
  split; [exact Wqmax|]. split; [exact Wqmin|]. split; [exact Wqc|]. split; [exact Wkeys|]. split; [intros q0 []| intros B0 []].
Qed.

Section FreeTail1R.
  Context {HCEIL : HeapCeil}.
  Variables (sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (ch : chunk).
  Variables (T : list Z) (RFr : mem -> Prop).

  Let st := a_st s.
  Let TH := a_thr s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let LB' := lb_remove U LB.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3024 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis RFrT : forall W0 m0 m1, RFr m0 -> munch W0 m0 m1 -> wmono asegs m0 m1 -> disjoint_from W0 (bv_unsigned sp + -2208) 2208 -> RFr m1.

  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  Theorem free_tail1R : forall sm msF2 mo2,
    free_midsR sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo ch T RFr sm msF2 mo2 ->
    kMaxCacheSize < qc_bytes (as_tq (a_st sm)) -> qc_bytes (as_gq (a_st sm)) + qc_bytes (as_tq (a_st sm)) <= kQuarantineMaxSize ->
    (forall msF' mo', free_gpostXR sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo ch T RFr msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF2 mo2).
  Proof.
    intros sm msF2 mo2 MID GT LE K.
    destruct MID as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & Ethr & Ectx & Efsb & Ezr & Etop & Ebot & Esb & Epa & Esec & Egq & HAL & TNE & TQB & GQB & OK2 & VIS2 & HQ & AWV & FX & AMX & NVS & DEP & DPL & DCOV & MI2 & ST2 & PFR & RF2 & AMF & WM & ACM & AVX & (stX & ev0 & ev2 & EM & SBS & SC0)).
    pose proof HQ as (RQ & ND & LBs).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL2. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ2. pose proof (conj PL2 WQ2 : placed_ok sm /\ WFQ (a_st sm) [] []) as OKQ2.
    pose proof (WFQ_consts _ _ _ WQ2) as (CQmax & CQmin & CQc).
    pose proof (AREPQ_mem _ _ _ _ RQ) as (INST & _ & _ & _ & _ & _ & _ & BT & BG).
    pose proof INST as (_ & _ & _ & _ & _ & _ & _ & QC & _ & QM & GQ & _). rewrite CQmax, CQmin, CQc in QC.
    pose proof (tq_cells_of_arepq sm [] [] m2 RQ) as TQ. rewrite Ethr in TQ.
    pose proof PL2 as (_ & SB2 & SB3 & _ & _ & _ & T1 & T2 & T3 & _). rewrite Ethr in T1, T2, T3.
    set (lt := qc_list (as_tq (a_st sm))) in *. set (lg := qc_list (as_gq (a_st sm))) in *.
    set (glb := last lg (mkQB 0 0 0 [])).
    assert (BA : forall b, In b (lt ++ lg) -> AHI_LO <= qb_addr b /\ qb_addr b + 8192 <= aceil /\ qb_addr b mod 8 = 0).
    { intros b Hb. pose proof (batch_in_spaceQ sm [] [] OKQ2 b Hb) as (P1 & P2 & P3). clear - P1 P2 P3 SB2 SB3. unfold kBatchSize, kSpaceSize, kPageSize in *. repeat split; try exact P3; lia. }
    assert (NGB : 0 <= zlen lg /\ kBatchSize * zlen lg <= qc_bytes (as_gq (a_st sm))).
    { split; [unfold zlen; clear; lia|]. apply (qc_len_bytes (a_st sm) [] [] (as_gq (a_st sm)) WQ2 (WFQ_gq _ _ _ WQ2)). intros b Hb. apply in_app_iff. right. exact Hb. }
    assert (NTB : 1 <= zlen lt /\ kBatchSize * zlen lt <= qc_bytes (as_tq (a_st sm))).
    { split; [subst lt; destruct (qc_list (as_tq (a_st sm))); [exfalso; exact (TNE eq_refl)| rewrite zlen_cons; unfold zlen; clear; lia]|].
      apply (qc_len_bytes (a_st sm) [] [] (as_tq (a_st sm)) WQ2 (WFQ_tq _ _ _ WQ2)). intros b Hb. apply in_app_iff. left. exact Hb. }
    assert (ADB : forall x, (x = 0 \/ exists b, In b (lt ++ lg) /\ x = qb_addr b) -> 0 <= x < 2^64 /\ x mod 8 = 0).
    { intros x [->|(b & Hb & ->)]; [clear; repeat split; reflexivity || lia|]. pose proof (BA b Hb) as (P1 & P2 & P3). clear - P1 P2 P3. acb. unfold AHI_LO in *. split; [lia| exact P3]. }
    assert (FGB : 0 <= hd 0 (map qb_addr lg) < 2^64 /\ hd 0 (map qb_addr lg) mod 8 = 0).
    { apply ADB. destruct (hd_addr_cases lg) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; right; exact Hb| exact E]]. }
    assert (LGB : 0 <= last (map qb_addr lg) 0 < 2^64 /\ last (map qb_addr lg) 0 mod 8 = 0).
    { apply ADB. destruct (last_addr_cases lg) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; right; exact Hb| exact E]]. }
    assert (FTB : 0 <= hd 0 (map qb_addr lt) < 2^64 /\ hd 0 (map qb_addr lt) mod 8 = 0).
    { apply ADB. destruct (hd_addr_cases lt) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; left; exact Hb| exact E]]. }
    assert (LTB : 0 <= last (map qb_addr lt) 0 < 2^64 /\ last (map qb_addr lt) 0 mod 8 = 0).
    { apply ADB. destruct (last_addr_cases lt) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; left; exact Hb| exact E]]. }
    (* [comment removed for export] *)
    assert (GLF : zlen lg <> 0 -> lg = removelast lg ++ [glb] /\ last (map qb_addr lg) 0 = qb_addr glb /\ In glb (qc_list (as_tq (a_st sm)) ++ qc_list (as_gq (a_st sm)))
                                 /\ batch_rep m2 glb 0 /\ carved (a_st sm) kBatchClass (qb_addr glb)).
    { intros NZ. assert (NE : lg <> []) by (intros E; apply NZ; rewrite E; reflexivity).
      assert (EL : lg = removelast lg ++ [glb]) by (subst glb; apply app_removelast_last; exact NE).
      assert (IN : In glb (qc_list (as_tq (a_st sm)) ++ qc_list (as_gq (a_st sm)))) by (apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity).
      split; [exact EL|]. split; [rewrite EL at 1; rewrite map_app; cbn [map]; rewrite last_app_nonnil by discriminate; reflexivity|].
      split; [exact IN|]. split; [rewrite EL in BG; exact (batches_rep_last m2 _ _ BG)|]. exact (proj1 (batch_carvedQ sm [] [] OKQ2 glb IN)). }
    assert (HI' : lo + 2576 <= bv_unsigned sp) by (clear - HI; lia).
    assert (THR : hidden (akobj (a_thr s) 4096 /\ a_thr s + 4096 <= aceil /\ a_thr s mod 16 = 0)).   (* [comment removed for export] *)
    { constructor. unfold kPageSize in T1, T2, T3. clear - T1 T2 T3. split; [exact T2|]. split; [exact T3|]. Z.div_mod_to_equations. lia. }
    eapply (evt_sreach_lazy_at asegs (a_L sm) (a_S sm) (a_Zr sm) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (@put_drain_norecR _ sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 F fc lo LO HI' SPT
                t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 U size (a_thr s) kMaxCacheSize
                (zlen lg) (hd 0 (map qb_addr lg)) (last (map qb_addr lg) 0) (qc_bytes (as_gq (a_st sm))) (qb_size glb) (qb_count glb)
                (zlen lt) (hd 0 (map qb_addr lt)) (last (map qb_addr lt) 0) (qc_bytes (as_tq (a_st sm))) kQuarantineMaxSize kQuarantineMinSize MI2 THR).
      - unfold kMaxCacheSize. clear. lia.
      - exact GT.
      - clear - NGB FGB LGB GQB. unfold kBatchSize, kQuarantineMaxSize in *. lia.
      - clear - NTB FTB LTB TQB. unfold kBatchSize, kQuarantineMaxSize, kMaxCacheSize in *. lia.
      - clear - GQB TQB. unfold kBatchSize, kQuarantineMaxSize, kMaxCacheSize in *. lia.
      - unfold kQuarantineMaxSize, kQuarantineMinSize. clear. lia.
      - intros NZ. destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG. pose proof (BA glb ltac:(apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity)) as (P1 & P2 & P3).
        pose proof (carved_vs_threadQ sm [] [] OKQ2 _ _ CV) as CT. change (class_size kBatchClass) with 8192 in CT. rewrite Ethr in CT.
        clear - P1 P2 P3 CT. unfold kPageSize, OT_TQ in *. repeat split; try exact P3; lia.
      - exact ST2.
      - exact PFR.
      - exact QM.
      - exact GQ.
      - intros NZ. destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG. exact (proj1 BR).
      - exact TQ.
      - exact QC.
      - exact LE. }
    cbv beta. intros msF' mo' OK' SBM _ PO.
    destruct PO as (m' & FRP & (m1 & DM & MU' & WM' & MI')).
    destruct FRP as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & VIS' & ST').
    pose proof DM as (MU1 & WM1 & MI1 & ST1 & QM' & GQ' & GL' & TQ' & QC').
    rewrite unsigned_lit in MU1 by (clear - HI LO SPT; acb; lia).
    (* [comment removed for export] *)
    assert (RF1 : RFr m1).
    { eapply (RFrT _ _ _ RF2 MU1 WM1); unfold drain_W; apply disjoint_from_app.
      - unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ. cbn [disjoint_from]. repeat match goal with |- _ /\ _ => split end; try exact I; clear - LO HI T3; try acb; unfold kPageSize in *; lia.
      - destruct (Z.eqb_spec (zlen lg) 0) as [Ez|NZ]; [exact I|]. destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG.
        pose proof (BA glb ltac:(apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity)) as (P1 & P2 & P3).
        cbn [disjoint_from]. split; [| exact I]. unfold AHI_LO in *. clear - P1 P2 LO HI; try acb; lia. }
    assert (RF' : RFr m').
    { eapply (RFrT _ _ _ RF1 MU' WM'); cbn [disjoint_from]; split; [| exact I]; clear - LO HI; try acb; lia. }
    assert (SPV : aceil + 48 <= bv_unsigned sp + -2288) by (clear - HI LO; lia).
    rewrite <- Ethr in MU1, TQ'.
    pose proof (arheap_after_transfer sm m2 m1 (bv_unsigned sp + -2288) RQ SPV TNE MU1 WM1 QM' GQ' GL' TQ' LB' HQ LE) as HR3.
    pose proof (flagsx_after_transfer sm m2 m1 _ RQ SPV MU1 WM1 FX) as FX1.
    pose proof (depot_after_transfer sm m2 m1 _ RQ SPV MU1 WM1 d' DPL DEP) as DEP1.
    assert (OK3 : ast_ok (transfer_s sm)) by exact (proj1 (proj1 HR3)).
    assert (OKs : ast_ok s) by exact (proj1 (proj1 HR)).
    assert (HLB' : forall b, In b LB' -> In b (alb s)) by (intros b Hb; apply lb_remove_In in Hb; exact (proj1 (proj2 (proj2 HR) b) (proj1 Hb))).
    assert (SPc : aceil <= bv_unsigned sp) by (clear - HI LO; lia).
    (* [comment removed for export] *)
    assert (APR : Forall (fun iv : ivl => apriv s LB' (bv_unsigned sp) (fst iv) (snd iv)) (drain_W (bv_unsigned sp + -2288) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg))).
    { unfold drain_W. rewrite Ethr. apply Forall_app. split.
      - constructor; [cbn [fst snd]; apply (apriv_mono s LB' (bv_unsigned sp) lo (bv_unsigned sp)); [clear - HI; lia| clear; lia| apply (apriv_stack s OKs LB' HLB'); exact LO]|].
        constructor; [cbn [fst snd]; apply (apriv_inst s OKs LB' HLB'); [unfold OI_QMUTEX; clear; lia| unfold OI_QMUTEX; clear; lia| exact SPc]|].
        constructor; [cbn [fst snd]; apply (apriv_inst s OKs LB' HLB'); [unfold OI_GQ; clear; lia| unfold OI_GQ; clear; lia| exact SPc]|].
        constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB' HLB'); [unfold OT_TQ; clear; lia| unfold OT_TQ, kPageSize; clear; lia| unfold OT_TQ; clear; lia| exact SPc]|].
        constructor.
      - destruct (Z.eqb_spec (zlen lg) 0) as [E|NZ]; [constructor|]. constructor; [cbn [fst snd]| constructor].
        destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG.
        assert (INs : In glb (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s)))) by (apply in_app_iff; right; rewrite <- Egq; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity).
        pose proof (BA glb ltac:(apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity)) as (P1 & P2 & P3).
        pose proof (batch_in_space s OKs glb INs) as (Q1 & Q2 & _).
        pose proof (proj1 OKs) as PLs. pose proof PLs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D6 & _).
        apply (apriv_app s OKs LB' HLB'); [apply arng_hi; [clear - P1; lia| clear - P2; lia]| clear - P2 SPc; lia| |].
        + intros A nn Hin. apply (bsep_mono s A nn (qb_addr glb) (qb_addr glb + kBatchSize)); [clear; lia| unfold kBatchSize; clear; lia| exact (bsep_apiece s OKs LB' HLB' _ _ (ap_batch s glb INs) A nn Hin)].
        + clear - Q1 Q2 D6. unfold disj, kSpaceSize, kPageSize, AFS_SIZE, kBatchSize in *. lia. }
    (* [comment removed for export] *)
    assert (HR' : ARHEAP (transfer_s sm) LB' m').
    { apply (ARHEAP_frame_thm (transfer_s sm) OK3 LB' m1 m' _ HR3 MU' WM'). constructor; [| constructor]. left. cbn [fst]. exact LO. }
    assert (FX' : flagsx_rep m').
    { apply (flagsx_transport5 (outside [(lo, bv_unsigned sp + -2208)]) m1 m' (munch_agree _ _ _ MU') WM'); [| exact FX1].
      intros a Ha. cbn [outside]. split; [| exact I]. clear - Ha LO. acb. unfold ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *. lia. }
    assert (DEP' : DEPOT asegs d' m').
    { apply (DEPOT_transport asegs d' m1 m' _ DEP1 MU' WM'). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4).
      unfold depot_avoid, avoids. cbn [d_nb d_sb d_put fst snd] in *. clear - LO N1 N2 N3 N4. acb. unfold AHI_LO in *.
      repeat split; (apply Forall_cons; [cbn [fst snd]; zlets; lia| apply Forall_nil]). }
    assert (AMF' : amframe s LB' (bv_unsigned sp) m m').
    { apply (amframe_trans s LB' (bv_unsigned sp) m m2 m' AMF). apply (amframe_trans s LB' (bv_unsigned sp) m2 m1 m').
      - exact (amframe_of_munch s LB' (bv_unsigned sp) _ m2 m1 MU1 APR).
      - apply (amframe_of_munch s LB' (bv_unsigned sp) _ m1 m' MU'). constructor; [| constructor]. cbn [fst snd].
        apply (apriv_mono s LB' (bv_unsigned sp) lo (bv_unsigned sp)); [clear; lia| clear - HI; lia| apply (apriv_stack s OKs LB' HLB'); exact LO]. }
    (* [comment removed for export] *)
    assert (CMP' : acompl sm (transfer_s sm) d lo (bv_unsigned sp) m2 m').
    { apply (acompl_of_munch sm (transfer_s sm) d lo (bv_unsigned sp) _ m2 m' (munch_app2 _ _ _ _ _ MU1 MU')).
      intros iv a Hiv Ha. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
      - unfold drain_W in Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
        + destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; unfold awrit, astatw; unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ, kPageSize in *.
          * left. clear - Ha HI. lia.
          * do 6 right. left. left. clear - Ha. lia.
          * do 6 right. left. left. clear - Ha. lia.
          * right. left. clear - Ha. lia.
        + destruct (Z.eqb_spec (zlen lg) 0) as [E|NZ]; [destruct Hiv|]. destruct Hiv as [<-|[]]. cbn [fst snd] in Ha.
          destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG in Ha.
          pose proof (batch_in_spaceQ sm [] [] OKQ2 glb IN) as (P1 & P2 & _).
          unfold awrit. right. right. left. clear - Ha P1 P2. unfold kBatchSize, kSpaceSize, kPageSize in *. lia.
      - destruct Hiv as [<-|[]]. cbn [fst snd] in Ha. unfold awrit. left. clear - Ha. lia. }
    apply K. unfold free_gpostXR.
    exists (transfer_s sm), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m'.
    split; [exact Ethr|]. split; [exact Ectx|]. split; [exact Efsb|]. split; [exact Ezr|]. split; [exact Etop|]. split; [exact Ebot|].
    split; [intros sc Hsc; rewrite <- Esec; exact Hsc|]. split; [exact HAL|].
    split; [exact OK'|]. split; [exact VIS'|].
    split; [exact HR'|].
    split; [exact (awin_vis_wmono sm m2 m' AWV (wmono_trans _ _ _ _ WM1 WM'))|]. split; [exact FX'|]. split; [exact (AMODELX_mat sm mo2 mo' AMX SBM)|].
    split; [exact (nonvm_same_trans _ _ _ NVS (nonvm_same_mat mo2 mo' SBM))|].
    split; [exact DEP'|]. split; [exact DPL|].
    split; [unfold depot_cov in DCOV |- *; intros x Hx; rewrite (same_but_materialized_vmmaps mo2 mo' SBM); exact (DCOV x Hx)|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact RF'|]. split; [exact AMF'|].
    split; [exact (avis_of_wmono s (transfer_s sm) m m' (wmono_trans _ _ _ _ WM (wmono_trans _ _ _ _ WM1 WM')))|].
    split. { apply (acompl_trans s sm (transfer_s sm) d lo (bv_unsigned sp) m m2 m' (conj Ethr (conj Esb Epa))); [| exact ACM| exact CMP'].
             intros sc Hsc. rewrite <- Esec. exact Hsc. }
    split. { apply (avmx_mat_r s (transfer_s sm) mo mo2 mo'); [| exact SBM]. intros x Hx. destruct (AVX x Hx) as [A1 A2]. split; [exact A1| exact A2]. }
    pose proof SBS as SBS0. unfold same_but_shadow in SBS0.
    destruct SBS0 as (_ & _ & _ & _ & _ & _ & _ & _ & Etq & Egq' & _ & _ & _ & Eqm & _ & Eqc).
    rewrite (free_tail_transfer U size stX ev0 ev2) in EM by (rewrite ?Etq, ?Egq', ?Eqc, ?Eqm, ?CQc, ?CQmax; first [exact GT| exact LE]).
    eexists (transfer_m stX), _. split; [exact EM|].
    clear - SBS. unfold same_but_shadow, transfer_m, set_gq, set_tq in *. cbn. destruct SBS as (? & ? & ? & ? & ? & ? & ? & ? & E9 & E10 & ? & ? & ? & ? & ? & ?). rewrite E9, E10. repeat split; assumption || reflexivity.
  Qed.
End FreeTail1R.

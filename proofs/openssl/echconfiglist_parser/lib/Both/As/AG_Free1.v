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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AsDepotInv
     AW_MallocBase AllocWalkKit AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_FreeModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma batches_rep_last : forall m l0 b, batches_rep m (l0 ++ [b]) -> batch_rep m b 0.
Proof.
  intros m l0 b. induction l0 as [|x l0 IH]; cbn [batches_rep app].
  - intros [H _]. cbn [map hd] in H. exact H.
  - intros [_ H]. exact (IH H).
Qed.
Lemma batches_rep_In : forall m l b, batches_rep m l -> In b l -> exists nx, batch_rep m b nx.
Proof.
  intros m l b. induction l as [|x l IH]; [intros _ []|]. cbn [batches_rep]. intros [H1 H2] [<-|Hin]; [eexists; exact H1| exact (IH H2 Hin)].
Qed.
Lemma last_map {A B} : forall (f : A -> B) l d, last (map f l) (f d) = f (last l d).
Proof. intros f l d. induction l as [|x l IH]; [reflexivity|]. cbn [map last]. rewrite IH. destruct l; reflexivity. Qed.

Lemma find_chunk_In : forall st u c, find_chunk (as_chunks st) u = Some c -> In c (chunk_list st).
Proof. intros st u c F. unfold find_chunk in F. destruct (u <=? 0); [discriminate|]. apply chunk_list_in_iff. eexists. exact F. Qed.

Lemma sum_used_nonneg : forall st qs, WF st ->
  0 <= fold_right (fun (q : Z) (acc : Z) => match find_chunk (as_chunks st) (q + kChunkHeaderSize) with Some c => ch_used c | None => 0 end + acc) 0 qs.
Proof.
  intros st qs W. induction qs as [|q qs IH]; cbn; [lia|]. destruct (find_chunk (as_chunks st) (q + kChunkHeaderSize)) as [c0|] eqn:F; [| lia].
  pose proof (WF_chunk st c0 W (find_chunk_In _ _ _ F)) as (C1 & _). lia.
Qed.
Lemma qc_bytes_nonneg : forall st q, WF st -> qcache_ok st q -> 0 <= qc_bytes q.
Proof.
  intros st q W [Q1 Q2]. rewrite Q2. assert (H : forall b, In b (qc_list q) -> 0 <= qb_size b).
  { intros b Hb. destruct (Q1 b Hb) as (_ & _ & _ & _ & _ & _ & _ & B8 & _). rewrite B8. pose proof (sum_used_nonneg st (qb_chunks b) W). unfold kBatchSize. lia. }
  clear - H. induction (qc_list q) as [|b r IH]; cbn; [lia|]. pose proof (H b (or_introl eq_refl)). assert (0 <= fold_right (fun b0 acc => qb_size b0 + acc) 0 r) by (apply IH; intros; apply H; right; assumption). lia.
Qed.

(* [comment removed for export] *)
Lemma uhi_of_arep : forall s m ch, AREP s m -> In ch (chunk_list (a_st s)) ->
  aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).
Proof.
  intros s m ch R CHIN. pose proof (proj1 R) as OK.
  pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_band s OK ch CHIN) as EB.
  assert (LO : ch_lo ch <= ch_alloc_beg ch) by (unfold ch_lo; destruct (ch_primary ch); unfold kPageSize; lia).
  apply (aapp_sub _ _ _ _ EB); clear - G1 G2 G4 LO; lia.
Qed.
(* [comment removed for export] *)
Lemma aim_of_aapp : forall X k x, aapp X k -> X <= x -> x + 1 <= X + k -> addr_is_in_mem x = true.
Proof.
  intros X k x H H1 H2. acb. unfold addr_is_in_mem, kHighMemBeg, kHighMemEnd, kLowMemEnd, kShadowOffset. apply orb_true_iff.
  unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in H.
  destruct H as [[A1 A2]|[A1 A2]]; [left| right]; apply andb_true_iff; split; apply Z.leb_le; lia.
Qed.

Section FreeCells.
  Variables (s : ast) (m : mem) (ch : chunk) (d : depot).
  Hypothesis R : AREP s m.
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
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis DPL : depot_placed s d.
  (* [comment removed for export] *)
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).

  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.

  (* [comment removed for export] *)
  Lemma free_pure :
       1 <= size /\ (aapp (U - 16) (16 + round_up size 8) /\ aapp U (round_up size 8) /\ AIMG_TOP + 16 <= U) /\ U + round_up size 8 <= aceil /\ U mod 16 = 0 /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size
    /\ 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)
    /\ AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil /\ sb mod 65536 = 0
    /\ (TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
    /\ kPageSize <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s
    /\ as_qmax st = kQuarantineMaxSize /\ as_qmin st = kQuarantineMinSize /\ as_qcache st = kMaxCacheSize
    /\ k = zlen l /\ 0 <= k /\ qc_bytes tq <= as_qcache st /\ 0 <= qc_bytes tq.
  Proof.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ext_facts s OK ch CHIN) as (E1 & E2 & E3 & _).
    pose proof (chunk_align s OK ch CHIN) as (A1 & A2 & A3 & _).
    pose proof WFs as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
    assert (QB0 : 0 <= qc_bytes tq) by (apply (qc_bytes_nonneg st); [exact WFs| exact Wtq]).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in X2; [| clear; lia].   (* [comment removed for export] *)
    subst U size k l tq lb LA TH CTX sb st. unfold a_sb in *. unfold disj, kSpaceSize, kPageSize in D2, D3, TCX. unfold AHI_LO in *.
    split; [exact G3|].
    split. { pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; lia)) as [UE _]. split; [exact UHI|]. split; [apply (aapp_sub _ _ _ _ UHI); clear - G3 G5; lia| unfold AIMG_TOP in *; clear - UE; lia]. }
    split; [clear - G2 G4 E2; lia|]. split; [exact A3|]. split; [clear - G5; lia|]. split; [exact G6|].
    split; [exact (proj1 T2)|]. split; [exact T3|]. split; [exact T1|]. split; [exact (proj1 X2)|]. split; [exact X3|]. split; [clear - TCX; lia|].
    split; [exact S2|]. split; [exact S3|]. split; [exact S1|]. split; [clear - D2; unfold kSpaceSize; lia|]. split; [clear - D3; unfold kSpaceSize; lia|].
    split; [clear - TCX; unfold kPageSize; lia|]. split; [clear - TCX; lia|].
    split; [exact Wqmax|]. split; [exact Wqmin|]. split; [exact Wqc|].
    split; [reflexivity|]. split; [unfold zlen; clear; lia|]. split; [exact Wtqb| exact QB0].
  Qed.

  (* [comment removed for export] *)
  Lemma rec_vs_thread : TH + kPageSize <= ch_lo ch \/ ch_end ch <= TH.
  Proof.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    destruct (ch_primary ch) eqn:E.
    - pose proof (record_primary_space s OK ch CHIN E) as [B1 B2]. subst TH. clear - B1 B2 D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - destruct (record_secondary_map s OK ch CHIN E) as (h & Hh & L0 & E0 & _). pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & _ & D & _).
      subst TH. clear - L0 E0 D. unfold disj, kPageSize in *. lia.
  Qed.
  Lemma rec_vs_ctx : CTX + 160 <= ch_lo ch \/ ch_end ch <= CTX.
  Proof.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    destruct (ch_primary ch) eqn:E.
    - pose proof (record_primary_space s OK ch CHIN E) as [B1 B2]. subst CTX. clear - B1 B2 D3. unfold disj, kSpaceSize, kPageSize in *. lia.
    - destruct (record_secondary_map s OK ch CHIN E) as (h & Hh & L0 & E0 & _). pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & _ & _ & D & _).
      subst CTX. clear - L0 E0 D. unfold disj, kPageSize in *. lia.
  Qed.
  Lemma rec_vs_depot : (d_nb d + 16 * 65536 <= ch_lo ch \/ ch_end ch <= d_nb d) /\ (d_sb d + 8 * 131072 <= ch_lo ch \/ ch_end ch <= d_sb d).
  Proof.
    destruct DPL as (_ & _ & G3 & G4 & _ & _ & _ & _ & GS & _).
    destruct (ch_primary ch) eqn:E.
    - pose proof (record_primary_space s OK ch CHIN E) as [B1 B2]. clear - B1 B2 G3 G4. unfold disj, kSpaceSize, kPageSize in *. lia.
    - destruct (record_secondary_map s OK ch CHIN E) as (h & Hh & L0 & E0 & _). destruct (GS h Hh) as [Da Db].
      clear - L0 E0 Da Db. unfold disj in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma free_plu : (TH + 4096 <= U - 16 \/ U + 8 <= TH) /\ (CTX + 160 <= U - 16 \/ U + 8 <= CTX)
                /\ (d_nb d + 16 * 65536 <= U - 16 \/ U + 8 <= d_nb d) /\ (d_sb d + 8 * 131072 <= U - 16 \/ U + 8 <= d_sb d).
  Proof.
    pose proof rec_vs_thread as RT. pose proof rec_vs_ctx as RC. pose proof rec_vs_depot as [RD1 RD2].
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts s OK ch CHIN) as (E1 & E2 & E3 & _).
    subst U TH CTX. unfold kPageSize in RT. clear - RT RC RD1 RD2 G1 G2 G3 G4 G5 G6 E3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma free_cells : exists (b1 actx : Z) (q0 q1 q2 q3 : word),
       rw_cells asegs m (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] /\ (0 <= b1 < 256 /\ (b1 mod 128 = 17 \/ b1 mod 128 = 65)) /\ 0 <= actx < 2^64
    /\ stk asegs m (TH + 2800) (TH + 3168) /\ rw_cells asegs m (TH + 3168) [C1 (b8 0)]
    /\ rw_cells asegs m (AINST + OI_QMAX) [C8 (wz kQuarantineMaxSize); C8 (wz kQuarantineMinSize); C8 (wz kMaxCacheSize)]
    /\ rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz (hd 0 (map qb_addr l))); C8 (wz LA); C8 (wz (qc_bytes tq))]
    /\ rw_cells asegs m (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3]
    /\ rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)]
    /\ IENV (wz ATP) ATSD CTX TH sb (a_top s) (a_bot s) m.
  Proof.
    pose proof (free_pure) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K1 & K2 & K3 & K4).
    pose proof R as RR. destruct RR as (OK' & INST & FL & THR & SEC & IA & CL & CH & BT & BG).
    (* [comment removed for export] *)
    destruct (CH ch CHIN) as ((b1 & actx & HD & Hb1 & Hb1') & _). rewrite ALLOC in HD. fold U size in HD. unfold kChunkHeaderSize in HD.
    replace (U - 16) with (U + -16) in HD by lia.
    unfold wz in HD at 3. rewrite <- (Z_to_bv_mod64 actx) in HD. fold (wz (actx mod 2^64)) in HD.
    (* [comment removed for export] *)
    destruct THR as (Tc & Ttid & Tthr & Tstk & T40 & Tsw & Ttq & Jtq & Jcs & Jst & Tunw). fold TH st tq in Ttq, Jcs, Jst, Tunw. fold l in Ttq.
    unfold a_cache in *. unfold OT_CACHE, CACHE_STATS, OT_STATS, OT_UNWINDING in *. fold TH in Jcs.
    acb. unfold AHI_LO in *.
    pose proof (junk_stk' _ _ _ Jcs ltac:(lia) ltac:(lia) ltac:(lia)) as SCS.
    destruct (stk_cells _ _ _ SCS ltac:(lia)) as [js JS]. replace (TH + 208 + 2560 + (2800 - 208 - 2560) - (TH + 208 + 2560)) with 32 in JS by lia.
    change (Z.to_nat 32) with 32%nat in JS.
    apply (rw_cells_split_CB asegs _ _ [] 32 js [] [8;8;8;8]%nat) in JS; [| reflexivity]. cbn [mk_CB_cells app] in JS.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS) as [w0 JS0].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS0. destruct JS0 as [Kw0 JS1]. cbn [cells_size csize Nat.add] in JS1.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS1) as [w1 JS1'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS1'. destruct JS1' as [Kw1 JS2]. cbn [cells_size csize Nat.add] in JS2.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS2) as [w2 JS2'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS2'. destruct JS2' as [Kw2 JS3]. cbn [cells_size csize Nat.add] in JS3.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS3) as [w3 Kw3].
    exists b1, (actx mod 2^64), w0, w1, w2, w3.
    split; [exact HD|]. split; [split; [exact Hb1| exact Hb1']|]. split; [apply Z.mod_pos_bound; lia|].
    split. { replace (TH + 3168) with (TH + 2800 + (3168 - 2800)) by lia. apply junk_stk'; [exact Jst| lia| lia| lia]. }
    split; [exact Tunw|].
    split. { destruct INST as (_ & _ & _ & _ & _ & _ & _ & A5 & _). fold st in A5. rewrite Q1, Q2, Q3 in A5. exact A5. }
    split. { subst LA lb k. rewrite <- (last_map qb_addr). cbn [qb_addr]. exact Ttq. }
    split. { replace (TH + 2768) with (TH + 208 + 2560) by lia.
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact Kw0|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact Kw1|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact Kw2|]. cbn [cells_size csize Nat.add]. exact Kw3. }
    split. { destruct INST as (A1 & _). apply (proj1 (rw_cells_app asegs _ _ [_] _)) in A1. destruct A1 as [A1 _]. exact A1. }
    apply ienv_of_arep. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma free_last_cells : l <> [] ->
       rw_cells asegs m LA [C8 (wz 0); C8 (wz (qb_size lb)); C8 (wz (qb_count lb))]
    /\ u64arr asegs m (LA + 24) (wlist (qb_chunks lb))
    /\ stk asegs m (LA + 24 + 8 * qb_count lb) (LA + kBatchSize)
    /\ In lb (qc_list (as_tq st) ++ qc_list (as_gq st))
    /\ qb_count lb = zlen (qb_chunks lb) /\ 1 <= qb_count lb <= kBatchCount /\ 1 <= k
    /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ LA mod 16 = 0 /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH)
    /\ (LA + kBatchSize <= U - 16 \/ U + 8 <= LA)
    /\ (d_nb d + 16 * 65536 <= LA \/ LA + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 131072 <= LA \/ LA + kBatchSize <= d_sb d)
    /\ sb + kBatchClass * 2^32 <= LA /\ LA + kBatchSize <= sb + kBatchClass * 2^32 + kFreeArrayOffset
    /\ kBatchSize <= qb_size lb /\ Forall (fun x => 0 <= x < 2^64) (qb_chunks lb) /\ hd 0 (map qb_addr l) <> 0.
  Proof.
    intros NE.
    pose proof R as RR. destruct RR as (OK' & INST & FL & THR & SEC & IA & CL & CH & BT & BG).
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SECp & SEC2 & TCX).
    pose proof (app_removelast_last (mkQB 0 0 0 []) NE) as EL. fold l lb in EL.
    assert (INlb : In lb (qc_list (as_tq st) ++ qc_list (as_gq st))) by (apply in_app_iff; left; fold tq l; rewrite EL; apply in_app_iff; right; left; reflexivity).
    fold st tq l in BT. rewrite EL in BT. pose proof (batches_rep_last m _ _ BT) as (B1 & B2 & B3 & B4). fold LA in B1, B2, B3, B4.
    pose proof (batch_carved s OK lb INlb) as (CV & CNT & CB). pose proof (carved_range st _ _ WFs CV) as (CR1 & CR2 & CR3).
    pose proof (carved_in_space s OK _ _ CV) as (CS1 & CS2 & CS3). fold st LA in CR1, CR2, CS1, CS2, CS3. rewrite region_beg_eq in CR1, CR2.
    change (class_size kBatchClass) with kBatchSize in CR2, CR3, CS2.
    pose proof (WF_batch st lb WFs INlb) as (_ & _ & _ & _ & BM & _ & _ & B8 & B9).
    pose proof (batch_vs_record s OK ch CHIN lb INlb) as BVR. fold LA in BVR.
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts s OK ch CHIN) as (E1 & E2 & E3 & _).
    destruct DPL as (_ & _ & DG3 & DG4 & _).
    assert (LA16 : LA mod 16 = 0).
    { fold st LA in BM. rewrite region_beg_eq in BM. change (class_size kBatchClass) with 8192 in BM. clear - BM S1. unfold a_sb in S1. subst LA lb l tq st.
      unfold kBatchClass in BM. Z.div_mod_to_equations. lia. }
    assert (HD0 : hd 0 (map qb_addr l) <> 0).
    { assert (EX0 : exists b0 r, l = b0 :: r) by (clear - NE; subst l; destruct (qc_list tq) as [|b0 r]; [exfalso; exact (NE eq_refl)| exists b0, r; reflexivity]).
      destruct EX0 as (b0 & r & EL0). rewrite EL0. cbn [map hd].
      assert (IN0 : In b0 (qc_list (as_tq st) ++ qc_list (as_gq st))) by (apply in_app_iff; left; fold tq; fold l; rewrite EL0; left; reflexivity).
      pose proof (batch_carved s OK b0 IN0) as (CV0 & _). pose proof (carved_in_space s OK _ _ CV0) as (C01 & _). clear - C01 S2. unfold AHI_LO in *. lia. }
    assert (QR : Forall (fun x => 0 <= x < 2^64) (qb_chunks lb)).
    { apply Forall_forall. intros x Hx. destruct (B9 x Hx) as [cx [Fx _]]. pose proof (find_chunk_In _ _ _ Fx) as INx.
      pose proof (ext_facts s OK cx INx) as (Ex1 & Ex2 & Ex3 & _). pose proof (chunk_geom s OK cx INx) as (Gx1 & Gx2 & Gx3 & Gx4 & Gx5 & _).
      unfold find_chunk in Fx. destruct (x + kChunkHeaderSize <=? 0) eqn:LE; [discriminate|]. apply Z.leb_gt in LE.
      destruct (WF_keys st WFs _ _ Fx) as [Kx Px]. unfold ckey in Kx. apply Z2Pos.inj_iff in Kx; [| exact LE| exact Px].
      unfold kChunkHeaderSize in Kx, LE. clear - Kx Ex1 Ex2 Ex3 Gx1 Gx2 Gx3 Gx4 Gx5 LE. acb. unfold AHI_LO, AIMG_TOP in *. lia. }
    subst LA lb l k tq U TH CTX sb size st. unfold a_sb, AHI_LO, disj, kSpaceSize, kPageSize, kBatchSize, kBatchCount, kFreeArrayOffset in *. acb.
    split; [exact B1|]. split; [exact B2|].
    split. { eapply junk_stk' in B3; [| clear - CS1 S2 CB; lia| clear - CS2 S3 CB ACEILB; lia| clear - CB; lia].
             match type of B3 with stk _ _ _ ?e => replace e with (qb_addr (last (qc_list (as_tq (a_st s))) {| qb_addr := 0; qb_size := 0; qb_count := 0; qb_chunks := [] |}) + 8192) in B3 by lia end.
             exact B3. }
    split; [exact INlb|]. split; [exact CNT|]. split; [exact CB|].
    split. { rewrite EL. unfold zlen. rewrite length_app. cbn [length]. clear. lia. }
    split; [clear - CS1 S2; lia|]. split; [clear - CS2 S3 ACEILB; lia|]. split; [exact LA16|].
    split; [clear - CS1 CS2 D2; lia|].
    split; [clear - BVR G1 G2 G3 G4 G5 G6 E3; lia|].
    split; [clear - CS1 CS2 DG3; lia|]. split; [clear - CS1 CS2 DG4; lia|].
    split; [clear - CR1; unfold kBatchClass in *; lia|]. split; [clear - CR2; unfold kBatchClass in *; lia|].
    split; [rewrite B8; pose proof (sum_used_nonneg (a_st s) (qb_chunks (last (qc_list (as_tq (a_st s))) {| qb_addr := 0; qb_size := 0; qb_count := 0; qb_chunks := [] |})) WFs); lia|].
    split; [exact QR| exact HD0].
  Qed.
End FreeCells.

End HCW.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AW_Drain AW_MergeBatches AW_Recycle AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_FreeModel AG_FreeModel2 AG_RepQ AG_RepQFacts AG_RepQFacts2 AG_FreeMid AG_FreeT1
     AG_RecycleModel AG_WriteSet AG_RecycleDefs SecLazy AllocTacX.
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
Lemma outside_bext_of : forall (L : list qbatch) a, (forall b, In b L -> ~ (qb_addr b <= a < qb_addr b + kBatchSize)) -> outside (map bext L) a.
Proof.
  intros L a H. induction L as [|b L IH]; [exact I|]. cbn [map outside bext]. split; [apply H; left; reflexivity| apply IH; intros b' Hb'; apply H; right; exact Hb'].
Qed.

(* [comment removed for export] *)
Lemma munch_app_re : forall (A B : list ivl) m1 m2 m3, munch A m1 m2 -> munch B m2 m3 -> munch (A ++ B) m1 m3.
Proof.
  intros A B m1 m2 m3 H1 H2. eapply munch_trans; [eapply munch_weaken; [| exact H1]| eapply munch_weaken; [| exact H2]];
    intros x Hx; apply outside_app in Hx; tauto.
Qed.

(* [comment removed for export] *)
Lemma rsplit_bsum : forall l qb qmin l2 b2 ex rp,
  rsplit (mkQC l qb) qmin = Some (mkQC l2 b2, ex, rp) -> qb = bsum l -> bsum (ex ++ rev rp) + b2 = qb /\ b2 = bsum l2.
Proof.
  intros l qb qmin l2 b2 ex rp R QB. unfold rsplit in R. cbn [qc_list qc_bytes] in R.
  destruct (qb <? zlen l * kBatchSize); [discriminate R|].
  destruct ((zlen l * kBatchSize <? qb) && (qb * 100 <? zlen l * kBatchSize * 200)).
  - destruct (merge_batches (mkQC l qb)) as [[[g' ex'] xb]|] eqn:MB; [| discriminate R]. destruct g' as [lF qbF]. cbn [qc_list qc_bytes] in R.
    destruct (pop_while (S (length lF)) lF qbF qmin []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R]. injection R as <- <- <- <-.
    pose proof (merge_batches_bsum _ _ _ _ _ _ MB) as (S1 & S2 & S3 & S4).
    pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & EL & ERP & EB & _). rewrite app_nil_r in ERP. subst rp' lF.
    assert (EX : bsum ex' = xb).
    { rewrite S3. clear - S4. induction ex' as [|b r IH]; [rewrite bsum_nil, zlen_nil'; lia|]. apply Forall_cons_iff in S4. destruct S4 as [E F].
      rewrite bsum_cons, zlen_cons', E, (IH F). lia. }
    rewrite bsum_app, rev_involutive, EX. rewrite bsum_app in S1. split; [clear - S1 S2 EB; lia| clear - S1 S2 EB QB; lia].
  - cbn [qc_list qc_bytes] in R. destruct (pop_while (S (length l)) l qb qmin []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R]. injection R as <- <- <- <-.
    pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & EL & ERP & EB & _). rewrite app_nil_r in ERP. subst rp'.
    cbn [app]. rewrite rev_involutive. rewrite EL, bsum_app in QB. split; [clear - EB QB; lia| clear - EB QB; lia].
Qed.
End HCW.

(* [comment removed for export] *)
Section BatchFacts.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (XC XB : list Z).
  Hypothesis OKQ : placed_ok s /\ WFQ (a_st s) XC XB.
  Let st := a_st s.

  Lemma bok_of_repQ : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> bok b.
  Proof.
    intros b Hb. pose proof OKQ as [PL WQ]. pose proof PL as (S1 & S2 & S3 & _). unfold a_sb in S1, S2, S3.
    pose proof (batch_in_spaceQ s XC XB OKQ b Hb) as (B1 & B2 & _). unfold a_sb in B1, B2.
    pose proof (batch_carvedQ s XC XB OKQ b Hb) as (CV & CNT & C1).
    pose proof (WFQ_batch _ _ _ b WQ Hb) as (_ & _ & _ & _ & _ & _ & _ & Q8 & Q9).
    pose proof aceil_range as ACR.
    unfold bok. split; [clear - S2 B1; lia|]. split; [clear - S3 B2; unfold kSpaceSize, kPageSize, kBatchSize in *; lia|].
    split. { destruct CV as (_ & _ & C0 & C2 & _). rewrite region_beg_eq in C0, C2. change (class_size kBatchClass) with 8192 in C2.
             replace (kBatchClass * 2 ^ 32) with 103079215104 in C0, C2 by reflexivity. fold st in S1.
             clear - S1 C0 C2. subst st. Z.div_mod_to_equations. lia. }
    split; [clear - C1; lia|]. split; [exact CNT|].
    split. { rewrite Q8. fold st.
             assert (S : 0 <= fold_right (fun (q0 : Z) (acc : Z) => match find_chunk (as_chunks st) (q0 + kChunkHeaderSize) with Some c => ch_used c | None => 0 end + acc) 0 (qb_chunks b)).
             { clear - WQ. induction (qb_chunks b) as [|q0 qs IH]; cbn; [lia|]. destruct (find_chunk (as_chunks st) (q0 + kChunkHeaderSize)) as [c0|] eqn:F; [| lia].
               pose proof (WFQ_chunk st XC XB c0 WQ (find_chunk_In _ _ _ F)) as (C1' & _). lia. }
             clear - S. lia. }
    apply Forall_forall. intros x Hx. destruct (Q9 x Hx) as (ch & F & _). fold st in F.
    pose proof (find_chunk_key st _ ch (WFQ_keys st XC XB WQ) F) as EK. pose proof (find_chunk_In _ _ _ F) as IN.
    pose proof (record_extQ s XC XB OKQ ch IN) as (X1 & X2 & X3 & _ & _ & X6 & X7 & X8 & X9).
    assert (RU : ch_used ch <= round_up (ch_used ch) 8) by (clear; unfold round_up; Z.div_mod_to_equations; lia).
    clear - EK X1 X2 X3 X6 X7 X8 X9 RU ACR. unfold kChunkHeaderSize, AIMG_TOP in *. lia.
  Qed.

  Lemma batches_PW : forall a b, In a (map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st))) -> In b (map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st))) ->
    a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a.
  Proof.
    intros a b Ha Hb NE. apply in_map_iff in Ha. destruct Ha as (ba & <- & Ha). apply in_map_iff in Hb. destruct Hb as (bb & <- & Hb).
    pose proof (batch_carvedQ s XC XB OKQ ba Ha) as (CV & _).
    pose proof (carved_vs_batchQ s XC XB OKQ kBatchClass (qb_addr ba) CV bb Hb ltac:(intros E; exact (NE (eq_sym E)))) as D.
    change (class_size kBatchClass) with kBatchSize in D. clear - D. lia.
  Qed.

  Lemma batches_nodupQ : List.NoDup (map qb_addr (qc_list (as_gq st) ++ qc_list (as_tq st))).
  Proof.
    pose proof (WFQ_carved _ _ _ (proj2 OKQ)) as ND. apply NoDup_app_l in ND. rewrite (carved_addr_list_eq s) in ND.
    apply NoDup_app_r in ND. apply NoDup_app_r in ND. unfold seg_batch in ND. fold st in ND. rewrite map_app in ND |- *.
    exact (Permutation_NoDup (Permutation_app_comm _ _) ND).
  Qed.

  Lemma qbytes_bsum : qc_bytes (as_gq st) = bsum (qc_list (as_gq st)) /\ qc_bytes (as_tq st) = bsum (qc_list (as_tq st)).
  Proof.
    assert (BS : forall l, fold_right (fun b acc => qb_size b + acc) 0 l = bsum l) by (intros l; induction l as [|x l IH]; [reflexivity|]; cbn [fold_right]; rewrite bsum_cons, IH; reflexivity).
    split; [rewrite (proj2 (WFQ_gq st XC XB (proj2 OKQ)))| rewrite (proj2 (WFQ_tq st XC XB (proj2 OKQ)))]; apply BS.
  Qed.
End BatchFacts.
Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma rec_pre_pure : forall s XC XB m, AREPQ s XC XB m ->
  let st := a_st s in let l := qc_list (as_gq st) ++ qc_list (as_tq st) in
     Forall bok l /\ List.NoDup (map qb_addr l)
  /\ (forall a b, In a (map qb_addr l) -> In b (map qb_addr l) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a)
  /\ qc_bytes (as_gq st) + qc_bytes (as_tq st) = bsum l.
Proof.
  intros s XC XB m RQ. pose proof (conj (AREPQ_placed _ _ _ _ RQ) (AREPQ_WFQ _ _ _ _ RQ)) as OKQ. cbv zeta.
  assert (SW : forall b, In b (qc_list (as_gq (a_st s)) ++ qc_list (as_tq (a_st s))) -> In b (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s))))
    by (intros b Hb; apply in_app_iff in Hb; apply in_app_iff; clear - Hb; tauto).
  assert (SWm : forall a, In a (map qb_addr (qc_list (as_gq (a_st s)) ++ qc_list (as_tq (a_st s)))) -> In a (map qb_addr (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s)))))
    by (intros a Ha; rewrite map_app in Ha |- *; apply in_app_iff in Ha; apply in_app_iff; clear - Ha; tauto).
  split; [apply Forall_forall; intros b Hb; exact (bok_of_repQ s XC XB OKQ b (SW b Hb))|].
  split; [exact (batches_nodupQ s XC XB OKQ)|].
  split; [intros a b Ha Hb NE; exact (batches_PW s XC XB OKQ a b (SWm a Ha) (SWm b Hb) NE)|].
  pose proof (qbytes_bsum s XC XB OKQ) as [E1 E2]. rewrite bsum_app, E1, E2. reflexivity.
Qed.

(* [comment removed for export] *)
Definition recentry_s (sm : ast) (l2F : list qbatch) (b2F : Z) : ast :=
  mkAst (set_gq (transfer_m (a_st sm)) (mkQC l2F b2F)) (a_thr sm) (a_ctx sm) (a_fsb sm) (a_L sm) (a_S sm) (a_Zr sm) (a_AL sm) (a_top sm) (a_bot sm).
End HCW.

Section RecEntryPost.
  Context {HCEIL : HeapCeil}.
  Variables (sm : ast) (m2 m4 : mem) (spv : Z).   (* [comment removed for export] *)
  Variables (l2F exF rpF : list qbatch) (b2F qmin : Z).
  Let st := a_st sm.
  Let TH := a_thr sm.
  Let CTX := a_ctx sm.
  Let sb := a_sb sm.
  Let lt := qc_list (as_tq st).
  Let lg := qc_list (as_gq st).
  Let ng := zlen lg.
  Let LG := last (map qb_addr lg) 0.
  Let bg := qc_bytes (as_gq st).
  Let bt := qc_bytes (as_tq st).
  Let l := lg ++ lt.
  Let T := exF ++ rev rpF.
  Let XC := flat_map qb_chunks T.
  Let XB := map qb_addr T.
  Let s4 := recentry_s sm l2F b2F.
  Let st4 := a_st s4.
  Let W : list ivl := drain_W spv (TH + OT_TQ) LG ng ++ rec_W spv l.
  Let P := outside W.

  Hypothesis RQ : AREPQ sm [] [] m2.
  Hypothesis SPV : aceil + 96 <= spv.
  Hypothesis TNE : lt <> [].
  Hypothesis AG : agree_on P m2 m4.
  Hypothesis WM : wmono asegs m2 m4.
  (* [comment removed for export] *)
  Hypothesis QM' : rw_cells asegs m4 (AINST + OI_QMUTEX) [C8 (wz 0)].
  Hypothesis GQ' : rw_cells asegs m4 (AINST + OI_GQ) [C8 (wz (zlen l2F)); C8 (wz (hd 0 (map qb_addr l2F))); C8 (wz (last (map qb_addr l2F) 0)); C8 (wz b2F)].
  Hypothesis TQ' : rw_cells asegs m4 (TH + OT_TQ) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Hypothesis BR' : batches_rep m4 l2F.

  Let PL : placed_ok sm. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st [] []. Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let OKQ : placed_ok sm /\ WFQ (a_st sm) [] []. Proof. exact (conj PL WQ). Qed.
  Let MEM : ARmem sm m2. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  (* [comment removed for export] *)
  Let INL : forall b, In b l -> In b (qc_list (as_tq st) ++ qc_list (as_gq st)).
  Proof. intros b Hb. unfold l, lg, lt in Hb. apply in_app_iff in Hb. apply in_app_iff. clear - Hb. tauto. Qed.

  (* [comment removed for export] *)
  Let BND : aceil + 96 <= spv /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12599296 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 12599296 <= a_pa sm /\ a_pa sm + 8388608 <= aceil
            /\ 0 <= LG /\ (ng <> 0 -> sb <= LG /\ LG + 8192 <= sb + 137438953472).
  Proof.
    placed. clear AG WM QM' GQ' TQ' BR'. fold TH CTX sb in T2, T3, X2, X3, S2, S3.
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in X2; [| clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia].
    assert (L0 : 0 <= LG /\ (ng <> 0 -> sb <= LG /\ LG + 8192 <= sb + 137438953472)).
    { assert (D : lg = [] \/ lg <> []) by (destruct lg; [left; reflexivity| right; discriminate]). destruct D as [EL|NE].
      - unfold LG, ng. rewrite EL. cbn. split; [apply Z.le_refl| intros C; exfalso; exact (C eq_refl)].
      - assert (IN : In (last lg (mkQB 0 0 0 [])) (qc_list (as_tq st) ++ qc_list (as_gq st))).
        { apply in_app_iff. right. fold lg. rewrite (app_removelast_last (mkQB 0 0 0 []) NE) at 2. apply in_app_iff. right. left. reflexivity. }
        assert (ELG : LG = qb_addr (last lg (mkQB 0 0 0 []))).
        { unfold LG. rewrite (app_removelast_last (mkQB 0 0 0 []) NE) at 1. rewrite map_app. cbn [map]. rewrite last_app_nonnil by discriminate. reflexivity. }
        pose proof (batch_in_spaceQ sm [] [] OKQ _ IN) as (B1 & B2 & _). fold sb in B1, B2. rewrite <- ELG in B1, B2. unfold kBatchSize, kSpaceSize, AHI_LO in B1, B2, S2.
        clear - B1 B2 S2. split; [lia| intros _; lia]. }
    unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. clear - SPV T2 T3 X2 X3 S2 S3 P2 P3 L0.
    repeat match goal with |- _ /\ _ => split end; try lia; exact (proj2 L0).
  Qed.
  Let BANDS : hidden ((TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa sm + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa sm)).
  Proof.
    clear AG WM QM' GQ' TQ' BR'. pose proof PL as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _). fold TH in T2. fold CTX in X2.
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    pose proof (aapp_lit _ _ P2) as L. unfold kPtrArrayReserve in L. exact L.
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).

  (* [comment removed for export] *)
  Let BSL : forall b, In b l -> sb <= qb_addr b /\ qb_addr b + kBatchSize <= sb + kSpaceSize /\ carved st kBatchClass (qb_addr b).
  Proof.
    clear AG WM QM' GQ' TQ' BR'. intros b Hb. pose proof (batch_in_spaceQ sm [] [] OKQ b (INL b Hb)) as (B1 & B2 & _). pose proof (batch_carvedQ sm [] [] OKQ b (INL b Hb)) as (CV & _).
    fold sb in B1, B2. split; [exact B1|]. split; [exact B2| exact CV].
  Qed.

  (* [comment removed for export] *)
  Lemma ZR_gen : forall a, a < aceil -> ~ (AINST + OI_QMUTEX <= a < AINST + OI_GQ + 32) -> ~ (TH + OT_TQ <= a < TH + OT_TQ + 32) ->
    (forall b, In b l -> ~ (qb_addr b <= a < qb_addr b + kBatchSize)) -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha N1 N2 N3. pose proof BND as (B1 & B2 & B3 & _ & _ & B6 & B7 & _ & _ & B10 & B11). unfold W. apply (proj2 (outside_app _ _ a)). split.
    - unfold drain_W. apply (proj2 (outside_app _ _ a)). split.
      + cbn [outside]. unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ in *. clear - Ha N1 N2 B1. repeat split; try exact I; lia.
      + destruct (Z.eqb_spec ng 0) as [E|NE]; [exact I|]. cbn [outside]. split; [| exact I].
        assert (D : lg = [] \/ lg <> []) by (destruct lg; [left; reflexivity| right; discriminate]). destruct D as [EL|NEL]; [exfalso; apply NE; unfold ng; rewrite EL; reflexivity|].
        assert (IN : In (last lg (mkQB 0 0 0 [])) l) by (unfold l; apply in_app_iff; left; rewrite (app_removelast_last (mkQB 0 0 0 []) NEL) at 2; apply in_app_iff; right; left; reflexivity).
        assert (ELG : LG = qb_addr (last lg (mkQB 0 0 0 []))).
        { unfold LG. rewrite (app_removelast_last (mkQB 0 0 0 []) NEL) at 1. rewrite map_app. cbn [map]. rewrite last_app_nonnil by discriminate. reflexivity. }
        specialize (N3 _ IN). rewrite <- ELG in N3. unfold kBatchSize in N3. clear - N3. lia.
    - unfold rec_W. cbn [outside]. unfold AINST, OI_QMUTEX, OI_GQ in *. split; [clear - Ha B1; lia|]. split; [clear - N1; lia|]. split; [clear - N1; lia|].
      apply outside_bext_of. exact N3.
  Qed.
  (* [comment removed for export] *)
  Let NB_out : forall a, (a < sb \/ sb + kSpaceSize <= a) -> forall b, In b l -> ~ (qb_addr b <= a < qb_addr b + kBatchSize).
  Proof. clear AG WM QM' GQ' TQ' BR'. intros a Ha b Hb. pose proof (BSL b Hb) as (B1 & B2 & _). clear - Ha B1 B2. lia. Qed.

  Lemma ZR_lo : forall a, 65536 <= a < AIMG_TOP -> ~ (AINST + OI_QMUTEX <= a < AINST + OI_GQ + 32) -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha N1. pose proof BND as (_ & B2 & _ & _ & _ & B6 & _). bands_as (BT & _). apply ZR_gen; [clear - Ha; acb; unfold AIMG_TOP in *; lia| exact N1| |].
    - clear - Ha B2 BT. unfold AIMG_TOP, OT_TQ in *. lia.
    - apply NB_out. left. clear - Ha B6. unfold AIMG_TOP in *. lia.
  Qed.
  Lemma ZR_static : forall a, astatic a -> ~ (AINST + OI_QMUTEX <= a < AINST + OI_GQ + 32) -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha N1. apply ZR_lo; [| exact N1]. clear - Ha. unfold astatic in Ha.
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP in *. lia.
  Qed.
  Lemma ZR_flags : forall a, aflags_range a -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha. apply ZR_lo; clear - Ha; unfold aflags_range in Ha;
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia.
  Qed.
  Lemma ZR_sh : forall a, a < AHI_LO -> ALOWSH_LO <= a -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha Hb. pose proof BND as (_ & B2 & _ & _ & _ & B6 & _). bands_as (BT & _).
    apply ZR_gen; [clear - Ha; acb; unfold AHI_LO in *; lia| clear - Hb; unfold ALOWSH_LO, AINST, OI_QMUTEX, OI_GQ in *; lia| clear - Ha Hb B2 BT; unfold AHI_LO, ALOWSH_LO, OT_TQ in *; lia|].
    apply NB_out. left. clear - Ha B6. unfold AHI_LO in *. lia.
  Qed.
  Lemma ZR_SH : forall lo' kk a, 0 <= lo' -> 0 <= kk -> lo' + 8 * kk <= aceil -> sh lo' <= a < sh lo' + kk -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros lo' kk a H0 Hk Hhi Ha. apply ZR_sh; clear - H0 Hk Hhi Ha; acb; unfold sh, ASHADOW_BASE, AHI_LO, ALOWSH_LO in *; Z.div_mod_to_equations; lia.
  Qed.
  Lemma ZR_thr : forall a, TH <= a < TH + 4096 -> ~ (TH + OT_TQ <= a < TH + OT_TQ + 32) -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha N2. pose proof BND as (_ & B2 & B3 & _). bands_as (BT & _).
    apply ZR_gen; [clear - Ha B3; lia| clear - Ha BT; unfold AINST, OI_QMUTEX, OI_GQ in *; lia| exact N2|].
    intros b Hb. pose proof (carved_vs_threadQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb)))) as CT. change (class_size kBatchClass) with 8192 in CT. fold TH in CT.
    clear - Ha CT. unfold kBatchSize, kPageSize in *. lia.
  Qed.
  Lemma ZR_ctx : forall a, CTX + 8 <= a < CTX + 160 -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha. pose proof BND as (_ & B2 & B3 & B4 & B5 & _). placed. fold TH CTX in TCX. destruct TCX as (TCX & _).
    apply ZR_gen; [clear - Ha B5; lia| clear - Ha B4; unfold AINST, OI_QMUTEX, OI_GQ in *; lia| clear - Ha TCX; unfold disj, kPageSize, OT_TQ in *; lia|].
    intros b Hb. pose proof (carved_vs_ctxQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb)))) as CT. change (class_size kBatchClass) with 8192 in CT. fold CTX in CT.
    clear - Ha CT. unfold kBatchSize in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZR_obj : forall X Y a, AIMG_TOP <= X -> Y <= aceil -> (TH + 4096 <= X \/ Y <= TH) -> (forall b, In b l -> qb_addr b + kBatchSize <= X \/ Y <= qb_addr b) ->
    X <= a < Y -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros X Y a H1 H2 H3 H4 Ha. apply ZR_gen; [clear - H2 Ha; lia| clear - H1 Ha; unfold AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia| clear - H3 Ha; unfold OT_TQ; lia|].
    intros b Hb. specialize (H4 b Hb). clear - H4 Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ZR_rinfo : forall a, a_ri sm <= a < a_ri sm + kPageSize -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    apply (ZR_obj (a_ri sm) (a_ri sm + kPageSize) a); [| | | | exact Ha].
    - unfold a_ri. fold sb. clear - B6. unfold AIMG_TOP, kSpaceSize. lia.
    - unfold a_ri. fold sb. clear - B7. unfold kSpaceSize, kPageSize. lia.
    - unfold a_ri. fold sb. clear - D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros b Hb. pose proof (carved_vs_rinfoQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb)))) as CR. change (class_size kBatchClass) with 8192 in CR. clear - CR. unfold kBatchSize. lia.
  Qed.
  Lemma ZR_pa : forall a, a_pa sm <= a < a_pa sm + kPtrArrayReserve -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha. pose proof BND as (_ & B2 & B3 & _ & _ & _ & _ & B8 & B9 & _). placed. fold TH in D4.
    apply (ZR_obj (a_pa sm) (a_pa sm + kPtrArrayReserve) a); [| | | | exact Ha].
    - clear - B8. unfold AIMG_TOP. lia.
    - clear - B9. unfold kPtrArrayReserve. lia.
    - clear - D4. unfold disj, kPtrArrayReserve, kPageSize in *. lia.
    - intros b Hb. pose proof (carved_vs_paQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb)))) as CR. change (class_size kBatchClass) with 8192 in CR. clear - CR. unfold kBatchSize. lia.
  Qed.
  Lemma ZR_sechdr : forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros h a Hh Ha. placed. pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). fold TH in Q7.
    apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
    apply (ZR_obj (sc_map_beg h) (sc_map_beg h + kPageSize) a); [| | | | exact Ha].
    - clear - Q2. unfold AIMG_TOP. lia.
    - clear - Q3 Q4. unfold kPageSize in *. lia.
    - clear - Q7 Q4. unfold disj, kPageSize in *. lia.
    - intros b Hb. pose proof (carved_vs_secQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb))) h Hh) as CR. change (class_size kBatchClass) with 8192 in CR. clear - CR Q4. unfold kPageSize, kBatchSize in *. lia.
  Qed.
  Lemma ZR_farray : forall c0 a, 0 <= c0 < kNumClasses -> FA sm c0 <= a < FA sm c0 + rg_mapped_free_array (get_region st c0) -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros c0 a Hc0 Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    pose proof (farray_in_spaceQ sm [] [] OKQ c0 Hc0) as (F1' & F2' & _). fold st sb in F1', F2'.
    apply (ZR_obj (FA sm c0) (FA sm c0 + rg_mapped_free_array (get_region st c0)) a); [| | | | exact Ha].
    - clear - F1' B6. unfold AIMG_TOP. lia.
    - clear - F2' B7. unfold kSpaceSize in *. lia.
    - clear - F1' F2' D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros b Hb. pose proof (carved_vs_farrayQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb))) c0 Hc0) as CR. change (class_size kBatchClass) with 8192 in CR. fold st in CR. clear - CR. unfold kBatchSize. lia.
  Qed.
  Lemma ZR_tail : forall c0 a, 0 <= c0 < kNumClasses ->
    RB sm c0 + rg_allocated_user (get_region st c0) <= a < RB sm c0 + rg_mapped_user (get_region st c0) -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros c0 a Hc0 Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    pose proof (tail_in_spaceQ sm [] [] OKQ c0 Hc0) as (F1' & F2' & _). fold st sb in F1', F2'.
    apply (ZR_obj (RB sm c0 + rg_allocated_user (get_region st c0)) (RB sm c0 + rg_mapped_user (get_region st c0)) a); [| | | | exact Ha].
    - clear - F1' B6. unfold AIMG_TOP. lia.
    - clear - F2' B7. unfold kSpaceSize in *. lia.
    - clear - F1' F2' D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros b Hb. pose proof (carved_vs_tailQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb))) c0 Hc0) as CR. change (class_size kBatchClass) with 8192 in CR. fold st in CR. clear - CR. unfold kBatchSize. lia.
  Qed.
  Lemma ZR_freech : forall c0 cp a, 0 <= c0 < kNumClasses -> In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
    compact_to_addr st c0 cp <= a < compact_to_addr st c0 cp + class_size c0 -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros c0 cp a Hc0 Hin Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    pose proof (freech_in_spaceQ sm [] [] OKQ c0 cp Hc0 Hin) as (F1' & F2' & _). fold st sb in F1', F2'.
    apply (ZR_obj (compact_to_addr st c0 cp) (compact_to_addr st c0 cp + class_size c0) a); [| | | | exact Ha].
    - clear - F1' B6. unfold AIMG_TOP. lia.
    - clear - F2' B7. unfold kSpaceSize in *. lia.
    - clear - F1' F2' D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros b Hb. pose proof (carved_vs_freechQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb))) c0 cp Hc0 Hin) as CR. change (class_size kBatchClass) with 8192 in CR. fold st in CR.
      assert (NEQ : compact_to_addr st c0 cp <> qb_addr b) by (intros E; exact (batch_not_freeQ sm [] [] OKQ b c0 cp (INL b Hb) Hc0 Hin (eq_sym E))).
      specialize (CR NEQ). clear - CR. unfold kBatchSize. lia.
  Qed.
  Lemma ZR_rec : forall x a, In x (chunk_list st) -> ch_lo x <= a < ch_end x -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros x a Hx Ha. pose proof BND as (_ & B2 & B3 & _). placed. fold TH sb in D2.
    pose proof (record_extQ sm [] [] OKQ x Hx) as (E1 & E2 & _).
    assert (XT : TH + 4096 <= ch_lo x \/ ch_end x <= TH).
    { destruct (ch_primary x) eqn:E.
      - pose proof (record_primary_spaceQ sm [] [] OKQ x Hx E) as [R1 R2]. fold sb in R1, R2. clear - R1 R2 D2. unfold disj, kSpaceSize, kPageSize in *. lia.
      - destruct (record_secondary_mapQ sm [] [] OKQ x Hx E) as (h & Hh & L0 & E0 & _). pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & _ & D & _). fold TH in D.
        clear - L0 E0 D. unfold disj, kPageSize in *. lia. }
    apply (ZR_obj (ch_lo x) (ch_end x) a); [exact E1| exact E2| exact XT| | exact Ha].
    intros b Hb. pose proof (batch_vs_recordQ sm [] [] OKQ x Hx b (INL b Hb)) as BR. clear - BR. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac trc H Z := eapply (rw_cells_transport_pt P m2 m4 AG WM); [exact H|];
                  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length repeat map]; intros ? ?; Z.
  Ltac trj H Z := eapply (junk_transport_pt P m2 m4 AG WM); [exact H|]; intros ? ?; Z.

  Lemma inst_rec_entry : inst_rep s4 m4.
  Proof.
    clear TQ' BR'.
    pose proof MEM as (INST & _). destruct INST as (A1 & J1 & A2 & J2 & A3 & J3 & J4 & A5 & J5 & A6 & A7 & J6 & A8 & J7 & A9).
    unfold inst_rep. change (a_sb s4) with (a_sb sm). change (a_ri s4) with (a_ri sm). change (a_pa s4) with (a_pa sm). change (a_st s4) with st4.
    change (as_n_reserved st4) with (as_n_reserved st). change (as_sec st4) with (as_sec st).
    change (as_qmax st4) with (as_qmax st). change (as_qmin st4) with (as_qmin st). change (as_qcache st4) with (as_qcache st).
    change (qc_list (as_gq st4)) with l2F. change (qc_bytes (as_gq st4)) with b2F.
    Ltac zi Ha := apply ZR_lo; clear - Ha; unfold AINST, AIMG_TOP, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX, OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER in *; lia.
    split; [trc A1 ltac:(zi H)|]. split; [trj J1 ltac:(zi H)|]. split; [trc A2 ltac:(zi H)|]. split; [trj J2 ltac:(zi H)|].
    split; [trc A3 ltac:(zi H)|]. split; [trj J3 ltac:(zi H)|]. split; [trj J4 ltac:(zi H)|]. split; [trc A5 ltac:(zi H)|]. split; [trj J5 ltac:(zi H)|].
    split; [exact QM'|]. split; [exact GQ'|].
    split; [trj J6 ltac:(zi H)|]. split; [trc A8 ltac:(zi H)|]. split; [trj J7 ltac:(zi H)| trc A9 ltac:(zi H)].
  Qed.

  Lemma thread_rec_entry : thread_rep s4 m4.
  Proof.
    clear QM' GQ' BR' TNE.
    pose proof MEM as (_ & _ & THR & _). destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_thr s4) with TH. change (a_ctx s4) with CTX. change (a_top s4) with (a_top sm). change (a_bot s4) with (a_bot sm).
    change (a_cache s4) with (a_cache sm). change (a_st s4) with st4. change (qc_list (as_tq st4)) with (@nil qbatch).
    change (qc_bytes (as_tq st4)) with 0. cbn [zlen length Z.of_nat map hd last].
    fold TH CTX in T1, T2, T2b, T2c, T2d, T3, J1, J3, T5.
    Ltac zt Ha := first [apply ZR_thr; clear - Ha; unfold OT_TQ, OT_CACHE, OT_SWITCHING, OT_STATS, OT_UNWINDING, CACHE_STATS, a_cache in *; lia | apply ZR_ctx; clear - Ha; lia].
    split; [trc T1 ltac:(zt H)|]. split; [trc T2 ltac:(zt H)|]. split; [trc T2b ltac:(zt H)|]. split; [trc T2c ltac:(zt H)|]. split; [trc T2d ltac:(zt H)|].
    split; [trc T3 ltac:(zt H)|]. split; [exact TQ'|]. split; [trj J1 ltac:(zt H)|].
    split; [trj J2 ltac:(unfold a_cache in *; fold TH in H; zt H)|]. split; [trj J3 ltac:(zt H)| trc T5 ltac:(zt H)].
  Qed.

  Lemma armem_rec_entry : ARmem s4 m4.
  Proof.
    pose proof MEM as (INST & FL & THR & SC & IA & RC & CH & BT & BG).
    split; [exact inst_rec_entry|].
    split; [exact (flags_rep_frame sm m2 m4 P AG WM ZR_flags FL)|].
    split; [exact thread_rec_entry|].
    split. { apply (sec_rep_frameQ sm [] [] m2 m4 P AG WM WQ); [| | exact SC].
             - intros a Ha. apply ZR_pa. pose proof WQ as (_ & _ & _ & _ & _ & _ & _ & RES & _). fold st in Ha.
               clear - Ha RES. unfold kPtrArrayReserve, kChunksBlockCount in *. lia.
             - intros h a Hh Ha. exact (ZR_sechdr h a Hh Ha). }
    split. { apply (ia_rep_frame sm m2 m4 P AG WM); [| exact IA]. intros a Ha. apply ZR_lo; clear - Ha; unfold AIAINST, AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia. }
    split. { intros c Hc. destruct (RC c Hc) as (R1 & R2 & R3 & R4).
             split; [exact (region_rep_frameQ sm [] [] m2 m4 P AG WM WQ c Hc ZR_rinfo (fun a Ha => ZR_farray c a Hc Ha) (fun a Ha => ZR_tail c a Hc Ha) R1)|].
             split. { apply (pclass_rep_frameQ sm [] [] m2 m4 P AG WM WQ c Hc); [| exact R2]. intros a Ha. apply ZR_thr; unfold a_cache, OT_CACHE, PCLASS_SIZE, OT_TQ, kNumClasses in *; fold TH in Ha; clear - Ha Hc; lia. }
             split; [| exact (region_junk_rep_frame sm m2 m4 P AG WM c Hc (fun cp a Hin Ha => ZR_freech c cp a Hc Hin Ha) R4)].
             apply (region_shadow_rep_frameQ sm [] [] m2 m4 P AG WM WQ c Hc); [| | | exact R3].
             - intros cp a Hin Ha. pose proof (freech_in_spaceQ sm [] [] OKQ c cp Hc Hin) as (F1' & F2' & _ & F4' & _). pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _). fold st sb in F1', F2'.
               pose proof (class_size_table_facts c Hc) as (_ & CS8 & _).
               apply (ZR_SH (compact_to_addr st c cp) (class_size c / 8) a); [| | | exact Ha]; clear - F1' F2' F4' B6 B7 CS8; zlets; unfold kSpaceSize in *; Z.div_mod_to_equations; lia.
             - intros a Ha. pose proof (tail_in_spaceQ sm [] [] OKQ c Hc) as (F1' & F2' & _ & F4' & F5'). pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _). fold st sb in F1', F2'.
               apply (ZR_SH (RB sm c + rg_allocated_user (get_region st c)) ((rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c)) / 8) a); [| | | exact Ha];
                 clear - F1' F2' F4' F5' B6 B7; zlets; unfold kSpaceSize in *; Z.div_mod_to_equations; lia.
             - intros a Ha. pose proof (farray_in_spaceQ sm [] [] OKQ c Hc) as (F1' & F2' & _ & F4' & F5'). pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _). fold st sb in F1', F2'.
               apply (ZR_SH (FA sm c) (rg_mapped_free_array (get_region st c) / 8) a); [| | | exact Ha]; clear - F1' F2' F4' F5' B6 B7; zlets; unfold kSpaceSize in *; Z.div_mod_to_equations; lia. }
    split. { intros x Hx. apply (chunk_rep_frameQ sm [] [] m2 m4 P AG WM WQ x Hx); [| exact (CH x Hx)].
             pose proof (record_extQ sm [] [] OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
             assert (RU : ch_used x <= round_up (ch_used x) 8) by (clear; unfold round_up; Z.div_mod_to_equations; lia).
             assert (NS : 0 <= nsh (ch_used x) /\ 8 * nsh (ch_used x) = round_up (ch_used x) 8) by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; lia).
             intros a [Ha|[Ha|[[_ Ha]|[Ha|[Ha|[[_ Ha]|[NP Ha]]]]]]].
             - apply (ZR_rec x a Hx). clear - Ha X3 X6 X7 X8 X9 RU. lia.
             - apply (ZR_rec x a Hx). clear - Ha X3 X6 X8 X9. lia.
             - apply (ZR_rec x a Hx). clear - Ha X3 X6 X7 X8 X9 RU. lia.
             - apply (ZR_SH (ch_alloc_beg x) (ch_rz x / 8) a); [| | | exact Ha]; clear - X1 X2 X3 X6 X7 X8 X9 RU; unfold AHI_LO, AIMG_TOP in *; Z.div_mod_to_equations; lia.
             - apply (ZR_SH (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) a); [| | | exact Ha];
                 clear - X1 X2 X3 X6 X7 X8 X9 RU; unfold AHI_LO, AIMG_TOP in *; Z.div_mod_to_equations; lia.
             - apply (ZR_SH (ch_user_beg x) (nsh (ch_used x)) a); [| | | exact Ha]; clear - X1 X2 X3 X6 X7 X8 X9 NS; unfold AHI_LO, AIMG_TOP in *; lia.
             - apply (ZR_SH (ch_alloc_beg x - kPageSize) 512 a); [| | | exact Ha]; unfold ch_lo in X1; rewrite NP in X1; clear - X1 X2 X6 X7 X8 X9 RU; unfold AHI_LO, AIMG_TOP, kPageSize in *; lia. }
    change (qc_list (as_tq (a_st s4))) with (@nil qbatch). change (qc_list (as_gq (a_st s4))) with l2F.
    split; [exact I| exact BR'].
  Qed.

  Lemma flagsx_rec_entry : flagsx_rep m2 -> flagsx_rep m4.
  Proof.
    clear QM' GQ' TQ' BR' TNE. intros FX. apply (flagsx_transport5 P m2 m4 AG WM); [| exact FX].
    intros a Ha. apply ZR_lo; clear - Ha; unfold ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia.
  Qed.
  Lemma depot_avoid_rec_entry : forall d, depot_placed sm d -> depot_avoid W d.
  Proof.
    clear AG WM QM' GQ' TQ' BR' TNE.
    intros d DPL. pose proof BND as (B1 & B2 & B3 & _ & _ & B6 & B7 & _ & _ & B10 & B11). pose proof DPL as (G1 & G2 & G3 & G4 & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4). fold TH in G1, G2. fold sb in G3, G4.
    apply aapp_env in N1; [| clear; lia]. apply aapp_env in N3; [| clear; lia]. bands_as (BT & _).
    unfold disj, kPageSize, kSpaceSize in G1, G2, G3, G4.
    assert (GB : forall b, In b l -> (d_nb d + 16 * 65536 <= qb_addr b \/ qb_addr b + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 131072 <= qb_addr b \/ qb_addr b + kBatchSize <= d_sb d)).
    { intros b Hb. pose proof (carved_vs_depotQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb))) d DPL) as CD. change (class_size kBatchClass) with 8192 in CD. unfold kBatchSize. exact CD. }
    unfold depot_avoid, avoids, W, drain_W, rec_W. acb.
    assert (LBB : forall b, In b l -> sb <= qb_addr b) by (intros b Hb; exact (proj1 (BSL b Hb))).
    assert (BX : forall Q : Z * Z -> Prop, (forall b, In b l -> Q (qb_addr b, qb_addr b + kBatchSize)) -> Forall Q (map bext l)).
    { intros Q H. clear - H. induction l as [|b L IH]; [apply Forall_nil|]. cbn [map]. apply Forall_cons; [exact (H b (or_introl eq_refl))| apply IH; intros b' Hb'; apply H; right; exact Hb']. }
    destruct (Z.eqb_spec ng 0) as [E|NE]; cbn [app].
    - clear B11. unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ in *. clear - B1 B2 B3 B6 B7 G1 G2 G3 G4 N1 N2 N3 N4 ACEILB BT GB BX LBB.
      repeat split; repeat (first [apply Forall_nil | apply BX; intros b Hb; pose proof (GB b Hb) as [Gn Gs]; pose proof (LBB b Hb) as Lb; cbn [fst snd]; unfold kBatchSize in *; lia | apply Forall_cons; [cbn [fst snd]; lia|]]).
    - specialize (B11 NE). unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ in *.
      assert (GL : (d_nb d + 16 * 65536 <= LG \/ LG + 8192 <= d_nb d) /\ (d_sb d + 8 * 131072 <= LG \/ LG + 8192 <= d_sb d)).
      { assert (D : lg = [] \/ lg <> []) by (destruct lg; [left; reflexivity| right; discriminate]). destruct D as [EL|NEL]; [exfalso; apply NE; unfold ng; rewrite EL; reflexivity|].
        assert (IN : In (last lg (mkQB 0 0 0 [])) l) by (unfold l; apply in_app_iff; left; rewrite (app_removelast_last (mkQB 0 0 0 []) NEL) at 2; apply in_app_iff; right; left; reflexivity).
        assert (ELG : LG = qb_addr (last lg (mkQB 0 0 0 []))).
        { unfold LG. rewrite (app_removelast_last (mkQB 0 0 0 []) NEL) at 1. rewrite map_app. cbn [map]. rewrite last_app_nonnil by discriminate. reflexivity. }
        rewrite ELG. unfold kBatchSize in GB. exact (GB _ IN). }
      clear - B1 B2 B3 B6 B7 G1 G2 G3 G4 N1 N2 N3 N4 ACEILB BT GB BX LBB GL B11.
      repeat split; repeat (first [apply Forall_nil | apply BX; intros b Hb; pose proof (GB b Hb) as [Gn Gs]; pose proof (LBB b Hb) as Lb; cbn [fst snd]; unfold kBatchSize in *; lia | apply Forall_cons; [cbn [fst snd]; lia|]]).
  Qed.

  (* [comment removed for export] *)
  Lemma rec_entry_T : (forall x, In x T -> In (qb_addr x) (map qb_addr l)) -> Forall (fun b => class_of_addr st4 (qb_addr b) = kBatchClass) T.
  Proof.
    clear AG WM QM' GQ' TQ' BR'. intros SUBT. apply Forall_forall. intros b Hb. pose proof (SUBT b Hb) as IN. apply in_map_iff in IN. destruct IN as (b0 & E & Hb0).
    rewrite <- E. change (class_of_addr st4 (qb_addr b0)) with (class_of_addr st (qb_addr b0)).
    destruct (WFQ_tq st [] [] WQ) as [OKT _]. destruct (WFQ_gq st [] [] WQ) as [OKG _].
    pose proof (INL b0 Hb0) as IN2. apply in_app_iff in IN2. destruct IN2 as [I|I]; [destruct (OKT b0 I) as (_ & _ & _ & X & _)| destruct (OKG b0 I) as (_ & _ & _ & X & _)]; exact X.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ZRW_thr : forall a, TH <= a < TH + 4096 -> outside (rec_W spv l) a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a Ha. pose proof BND as (B1 & B2 & B3 & _). bands_as (BT & _).
    unfold rec_W. cbn [outside]. unfold AINST, OI_QMUTEX, OI_GQ in *. split; [clear - Ha B1 B3; lia|]. split; [clear - Ha BT; lia|]. split; [clear - Ha BT; lia|].
    apply outside_bext_of. intros b Hb. pose proof (carved_vs_threadQ sm [] [] OKQ _ _ (proj2 (proj2 (BSL b Hb)))) as CT. change (class_size kBatchClass) with 8192 in CT. fold TH in CT.
    clear - Ha CT. unfold kBatchSize, kPageSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma W_awrit : forall d lo SP, lo + 96 <= spv -> spv <= SP -> forall iv a, In iv W -> fst iv <= a < snd iv -> awrit sm sm d lo SP a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros d lo SP L1 L2 iv a Hiv Ha. pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _ & _ & B10 & B11).
    assert (SL : forall b, In b l -> qb_addr b <= a < qb_addr b + kBatchSize -> awrit sm sm d lo SP a).
    { intros b Hb Hab. pose proof (BSL b Hb) as (S1 & S2 & _). unfold awrit. right. right. left. fold sb. clear - Hab S1 S2. unfold kBatchSize, kSpaceSize, kPageSize in *. lia. }
    unfold W in Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
    - unfold drain_W in Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
      + destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; unfold awrit, astatw; unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ, kPageSize in *.
        * left. clear - Ha L1 L2. lia.
        * do 6 right. left. left. clear - Ha. lia.
        * do 6 right. left. left. clear - Ha. lia.
        * right. left. fold TH. clear - Ha. lia.
      + destruct (Z.eqb_spec ng 0) as [E|NE]; [destruct Hiv|]. destruct Hiv as [<-|[]]. cbn [fst snd] in Ha.
        assert (D : lg = [] \/ lg <> []) by (destruct lg; [left; reflexivity| right; discriminate]). destruct D as [EL|NEL]; [exfalso; apply NE; unfold ng; rewrite EL; reflexivity|].
        assert (IN : In (last lg (mkQB 0 0 0 [])) l) by (unfold l; apply in_app_iff; left; rewrite (app_removelast_last (mkQB 0 0 0 []) NEL) at 2; apply in_app_iff; right; left; reflexivity).
        assert (ELG : LG = qb_addr (last lg (mkQB 0 0 0 []))).
        { unfold LG. rewrite (app_removelast_last (mkQB 0 0 0 []) NEL) at 1. rewrite map_app. cbn [map]. rewrite last_app_nonnil by discriminate. reflexivity. }
        apply (SL _ IN). rewrite <- ELG. clear - Ha. unfold kBatchSize. lia.
    - unfold rec_W in Hiv. destruct Hiv as [<-|[<-|[<-|Hiv]]]; cbn [fst snd] in Ha.
      + unfold awrit. left. clear - Ha L1 L2. lia.
      + unfold awrit, astatw. do 6 right. left. left. unfold AINST, OI_QMUTEX, OI_GQ in *. clear - Ha. lia.
      + unfold awrit, astatw. do 6 right. left. left. unfold AINST, OI_QMUTEX, OI_GQ in *. clear - Ha. lia.
      + apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb). cbn [bext fst snd] in Ha. exact (SL b Hb Ha).
  Qed.

  (* [comment removed for export] *)
  Lemma alive_outside : forall a, alive st a -> outside W a.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a (x & Hx & Ex & Ha). fold st in Hx.
    pose proof (record_extQ sm [] [] OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    assert (RU : ch_used x <= round_up (ch_used x) 8) by (clear; unfold round_up; Z.div_mod_to_equations; lia).
    assert (NS : 0 <= nsh (ch_used x) /\ 8 * nsh (ch_used x) = round_up (ch_used x) 8) by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; lia).
    destruct Ha as [Ha|Ha].
    - apply (ZR_rec x a Hx). clear - Ha X3 X6 X7 X8 RU. lia.
    - apply (ZR_SH (ch_user_beg x) (nsh (ch_used x)) a); [| | | exact Ha]; clear - X1 X2 X3 X6 X7 X8 X9 NS; unfold AHI_LO, AIMG_TOP in *; lia.
  Qed.
  Lemma alive_below : forall a, alive st4 a -> a < aceil.
  Proof.
    clear AG WM QM' GQ' TQ' BR'.
    intros a (x & Hx & Ex & Ha). change (chunk_list st4) with (chunk_list st) in Hx.
    pose proof (record_extQ sm [] [] OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    assert (RU : ch_used x <= round_up (ch_used x) 8) by (clear; unfold round_up; Z.div_mod_to_equations; lia).
    assert (NS : 0 <= nsh (ch_used x) /\ 8 * nsh (ch_used x) = round_up (ch_used x) 8) by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; lia).
    destruct Ha as [Ha|Ha].
    - clear - Ha X2 X7 RU. lia.
    - clear - Ha X1 X2 X3 X6 X7 X8 NS. acb. unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP in *. Z.div_mod_to_equations. lia.
  Qed.
  Lemma alive_agree : agree_on (alive st) m2 m4.
  Proof. clear QM' GQ' TQ' BR'. intros a Ha Hr. exact (AG a (alive_outside a Ha) Hr). Qed.

  (* [comment removed for export] *)
  Lemma NUM_rec_entry : NUM st -> NUM st4.
  Proof. clear. intros NM c Hc. exact (NM c Hc). Qed.
  Lemma awin_rec_entry : awin_vis sm m2 -> awin_vis s4 m4.
  Proof. clear QM' GQ' TQ' BR'. intros AWV. exact (awin_vis_wmono sm m2 m4 AWV WM). Qed.
  Lemma amodelx_rec_entry : forall mo, AMODELX sm mo -> AMODELX s4 mo.
  Proof. clear. intros mo H. exact H. Qed.
  Lemma depot_placed_rec_entry : forall d, depot_placed sm d -> depot_placed s4 d.
  Proof. clear. intros d H. exact H. Qed.
  (* [comment removed for export] *)
  Hypothesis RS : rsplit (mkQC l (bg + bt)) qmin = Some (mkQC l2F b2F, exF, rpF).
  Let WQT : WFQ (transfer_m st) [] []. Proof. exact (WFQ_transfer st WQ). Qed.
  (* [comment removed for export] *)
  Let RS' : rsplit (as_gq (transfer_m st)) qmin = Some (mkQC l2F b2F, exF, rpF). Proof. exact RS. Qed.
  Let PF := WFQ_pop (transfer_m st) qmin l2F exF rpF b2F WQT RS'.
  Lemma WQ4 : WFQ st4 XC XB.
  Proof. unfold st4, s4, recentry_s. cbn [a_st]. exact (proj1 PF). Qed.
  (* [comment removed for export] *)
  Lemma rec_entry_pop : (forall b, In b (l2F ++ T) -> In (qb_addr b) (map qb_addr l)) /\ Forall (batch_ok (transfer_m st)) l2F
    /\ b2F = bsum l2F /\ b2F <= qmin /\ List.NoDup (map qb_addr (l2F ++ T)).
  Proof. pose proof PF as (_ & P2 & P3 & _ & P5 & P6 & P7). repeat split; assumption. Qed.

  Theorem arepq_rec_entry : AREPQ s4 XC XB m4.
  Proof. split; [exact PL|]. split; [exact WQ4| exact armem_rec_entry]. Qed.

End RecEntryPost.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Packages.
  Context {HCEIL : HeapCeil}.
  Variables (sp : word) (lo : Z) (d' : depot) (LB' : list (Z * Z)).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3200 <= bv_unsigned sp.

  Theorem rec_pre_ok : forall (sm : ast) (m2 m1 : mem),
    let stm := a_st sm in let lt := qc_list (as_tq stm) in let lg := qc_list (as_gq stm) in
    ARHEAPQ sm [] [] LB' m2 -> lt <> [] ->
    munch (drain_W (bv_unsigned sp + -2208) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg)) m2 m1 -> wmono asegs m2 m1 ->
    (zlen lg <> 0 -> rw_cells asegs m1 (last (map qb_addr lg) 0)
                       [C8 (wz (hd 0 (map qb_addr lt))); C8 (wz (qb_size (last lg (mkQB 0 0 0 [])))); C8 (wz (qb_count (last lg (mkQB 0 0 0 []))))]) ->
       batches_rep m1 (lg ++ lt) /\ Forall bok (lg ++ lt) /\ List.NoDup (map qb_addr (lg ++ lt))
    /\ (forall a b, In a (map qb_addr (lg ++ lt)) -> In b (map qb_addr (lg ++ lt)) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a)
    /\ qc_bytes (as_gq stm) + qc_bytes (as_tq stm) = bsum (lg ++ lt).
  Proof.
    intros sm m2 m1. cbv zeta. intros HQ TNE MU1 WM1 GL1. pose proof HQ as (RQ & _).
    assert (SPV : aceil + 48 <= bv_unsigned sp + -2208) by (clear - LO HI; lia).
    split; [exact (batches_after_transfer sm m2 m1 (bv_unsigned sp + -2208) RQ SPV MU1 WM1 GL1)|].
    exact (rec_pre_pure sm [] [] m2 RQ).
  Qed.

  Theorem rec_entry_ok : forall (sm : ast) (m2 m1 m4 : mem) (mo4 : Model) (l2F exF rpF : list qbatch) (b2F : Z),
    let stm := a_st sm in let lt := qc_list (as_tq stm) in let lg := qc_list (as_gq stm) in let l := lg ++ lt in
    let Tb := exF ++ rev rpF in let s4 := recentry_s sm l2F b2F in
    ARHEAPQ sm [] [] LB' m2 -> lt <> [] -> as_cache_inited stm = true -> NUM stm ->
    0 <= qc_bytes (as_tq stm) <= kMaxCacheSize + kQuarantineMaxSize + kBatchSize -> 0 <= qc_bytes (as_gq stm) <= kQuarantineMaxSize ->
    awin_vis sm m2 -> flagsx_rep m2 -> AMODELX sm mo4 -> DEPOT asegs d' m2 -> depot_placed sm d' ->
    rsplit (mkQC l (qc_bytes (as_gq stm) + qc_bytes (as_tq stm))) kQuarantineMinSize = Some (mkQC l2F b2F, exF, rpF) ->
    munch (drain_W (bv_unsigned sp + -2208) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg)) m2 m1 -> wmono asegs m2 m1 ->
    (zlen lg <> 0 -> rw_cells asegs m1 (last (map qb_addr lg) 0)
                       [C8 (wz (hd 0 (map qb_addr lt))); C8 (wz (qb_size (last lg (mkQB 0 0 0 [])))); C8 (wz (qb_count (last lg (mkQB 0 0 0 []))))]) ->
    rw_cells asegs m1 (a_thr sm + OT_TQ) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    munch (rec_W (bv_unsigned sp + -2208) l) m1 m4 -> wmono asegs m1 m4 -> mem_inv asegs m4 ->
    rw_cells asegs m4 (AINST + OI_QMUTEX) [C8 (wz 0)] ->
    rw_cells asegs m4 (AINST + OI_GQ) [C8 (wz (zlen l2F)); C8 (wz (hd 0 (map qb_addr l2F))); C8 (wz (last (map qb_addr l2F) 0)); C8 (wz b2F)] ->
    batches_rep m4 l2F -> batches_rep m4 Tb -> Forall bok l2F -> Forall bok Tb ->
    (forall b, In b (l2F ++ Tb) -> In (qb_addr b) (map qb_addr l)) -> List.NoDup (map qb_addr (l2F ++ Tb)) -> b2F = bsum l2F ->
       AREPQ s4 (flat_map qb_chunks Tb) (map qb_addr Tb) m4 /\ NUM (a_st s4) /\ awin_vis s4 m4 /\ flagsx_rep m4 /\ AMODELX s4 mo4
    /\ DEPOT asegs d' m4 /\ depot_placed s4 d'
    /\ bsum Tb < 2^62 /\ Forall (fun b => class_of_addr (a_st s4) (qb_addr b) = kBatchClass) Tb
    /\ b2F <= kQuarantineMinSize /\ (forall a, alive (a_st s4) a -> a < aceil)
    /\ acompl sm sm d' lo (bv_unsigned sp) m2 m4 /\ agree_on (alive stm) m2 m4.
  Proof.
    intros sm m2 m1 m4 mo4 l2F exF rpF b2F. cbv zeta.
    intros HQ TNE INIT NM TQB GQB AWV FX AMX DEP DPL RS MU1 WM1 GL1 TQ1 MU4 WM4 MI4 QM4 GQ4 BR24 BRT4 OK24 OKT4 SUB4 ND4 B24.
    pose proof HQ as (RQ & _).
    set (spv := bv_unsigned sp + -2208) in *.
    set (lt := qc_list (as_tq (a_st sm))) in *. set (lg := qc_list (as_gq (a_st sm))) in *.
    assert (SPV : aceil + 96 <= spv) by (subst spv; clear - LO HI; lia).
    pose proof (munch_app_re _ _ _ _ _ MU1 MU4) as MU. pose proof (munch_agree _ _ _ MU) as AG. pose proof (wmono_trans _ _ _ _ WM1 WM4) as WM.
    (* [comment removed for export] *)
    assert (TQ4 : rw_cells asegs m4 (a_thr sm + OT_TQ) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply (rw_cells_transport_pt (outside (rec_W spv (lg ++ lt))) m1 m4 (munch_agree _ _ _ MU4) WM4); [exact TQ1|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros a Ha.
      apply (ZRW_thr sm m2 spv RQ SPV a). pose proof (AREPQ_placed _ _ _ _ RQ) as (_ & _ & _ & _ & _ & _ & T1 & _). clear - Ha T1. unfold OT_TQ, kPageSize in *. lia. }
    pose proof (rec_pre_pure sm [] [] m2 RQ) as (OKL & NDL & PW & QB). fold lt lg in OKL, NDL, PW, QB.
    pose proof (rsplit_bsum _ _ _ _ _ _ _ RS QB) as [BT1 BT2].
    split; [exact (arepq_rec_entry sm m2 m4 spv l2F exF rpF b2F kQuarantineMinSize RQ SPV AG WM QM4 GQ4 TQ4 BR24 RS)|].
    split; [exact (NUM_rec_entry sm l2F b2F NM)|].
    split; [exact (awin_rec_entry sm m2 m4 l2F b2F WM AWV)|].
    split; [exact (flagsx_rec_entry sm m2 m4 spv RQ SPV AG WM FX)|].
    split; [exact (amodelx_rec_entry sm l2F b2F mo4 AMX)|].
    split; [exact (DEPOT_transport asegs d' m2 m4 _ DEP MU WM (depot_avoid_rec_entry sm m2 spv RQ SPV d' DPL))|].
    split; [exact (depot_placed_rec_entry sm l2F b2F d' DPL)|].
    split. { pose proof (bsum_len l2F OK24) as BL. pose proof (zlen_nonneg l2F) as ZL. clear - BT1 BT2 BL ZL TQB GQB.
             unfold kBatchSize, kMaxCacheSize, kQuarantineMaxSize in *. lia. }
    split; [exact (rec_entry_T sm m2 l2F exF rpF b2F RQ (fun x Hx => SUB4 x ltac:(apply in_app_iff; right; exact Hx)))|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (rec_entry_pop sm m2 l2F exF rpF b2F kQuarantineMinSize RQ RS)))))|].
    split; [exact (alive_below sm m2 l2F b2F RQ)|].
    split; [| exact (alive_agree sm m2 m4 spv RQ SPV AG)].
    apply (acompl_of_munch sm sm d' lo (bv_unsigned sp) _ m2 m4 MU). apply (W_awrit sm m2 spv RQ SPV d' lo (bv_unsigned sp)); subst spv; clear - LO HI; lia.
  Qed.
End Packages.

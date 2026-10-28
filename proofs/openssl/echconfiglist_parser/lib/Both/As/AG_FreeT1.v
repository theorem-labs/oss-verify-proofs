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

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition transfer_s (sm : ast) : ast :=
  mkAst (transfer_m (a_st sm)) (a_thr sm) (a_ctx sm) (a_fsb sm) (a_L sm) (a_S sm) (a_Zr sm) (a_AL sm) (a_top sm) (a_bot sm).

(* [comment removed for export] *)
Fixpoint blist (m : mem) (l : list qbatch) (nx : Z) : Prop :=
  match l with
  | [] => True
  | b :: r => batch_rep m b (hd nx (map qb_addr r)) /\ blist m r nx
  end.
Lemma blist0 : forall m l, batches_rep m l <-> blist m l 0.
Proof. intros m l. induction l as [|b r IH]; cbn [batches_rep blist]; [tauto|]. rewrite IH. tauto. Qed.
Lemma blist_app : forall m l1 l2 nx, blist m (l1 ++ l2) nx <-> blist m l1 (hd nx (map qb_addr l2)) /\ blist m l2 nx.
Proof.
  intros m l1 l2 nx. induction l1 as [|b r IH]; cbn [blist app]; [tauto|]. rewrite map_app, hd_app_hd, IH. tauto.
Qed.
Lemma batch_rep_transport_pt : forall (P : Z -> Prop) m m' b nx, agree_on P m m' -> wmono asegs m m' ->
  0 <= qb_count b -> 24 + 8 * qb_count b <= kBatchSize -> qb_count b = zlen (qb_chunks b) ->
  (forall a, qb_addr b <= a < qb_addr b + kBatchSize -> P a) -> (forall a, sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8 -> P a) ->
  batch_rep m b nx -> batch_rep m' b nx.
Proof.
  intros P m m' b nx AG WM C1 C2 C3 Z1 Z2 (B1 & B2 & B3 & B4). unfold zlen in C3. unfold kBatchSize in *.
  split; [|split; [|split]].
  - eapply (rw_cells_transport_pt P m m' AG WM); [exact B1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply Z1. lia.
  - eapply (u64arr_transport_pt P m m' AG WM); [exact B2|]. unfold wlist. rewrite length_map. intros a Ha. apply Z1. lia.
  - eapply (junk_transport_pt P m m' AG WM); [exact B3|]. intros a Ha. apply Z1. unfold kBatchSize in Ha. lia.
  - eapply (poisoned_transport_pt P m m' AG WM); [exact B4|]. intros a Ha. apply Z2. unfold kBatchSize in Ha. change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. lia.
Qed.
Lemma blist_transport_pt : forall (P : Z -> Prop) m m' l nx, agree_on P m m' -> wmono asegs m m' ->
  (forall b, In b l -> 0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)) ->
  (forall b a, In b l -> (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
  blist m l nx -> blist m' l nx.
Proof.
  intros P m m' l nx AG WM HC HP. induction l as [|b r IH]; [exact (fun x => x)|]. cbn [blist]. intros [HB HR].
  pose proof (HC b (or_introl eq_refl)) as (C1 & C2 & C3).
  split; [| apply IH; [intros; apply HC; right; assumption| intros; eapply HP; [right; eassumption| eassumption]| exact HR]].
  apply (batch_rep_transport_pt P m m' b _ AG WM C1 C2 C3); [| | exact HB]; intros a Ha; eapply HP; [left; reflexivity| | left; reflexivity|]; [left| right]; exact Ha.
Qed.

(* [comment removed for export] *)
Lemma qc_len_bytes : forall st XC XB q, WFQ st XC XB -> qcache_ok st q -> (forall b, In b (qc_list q) -> In b (qc_list (as_tq st) ++ qc_list (as_gq st))) ->
  kBatchSize * zlen (qc_list q) <= qc_bytes q.
Proof.
  intros st XC XB q W [Q1 Q2] SUB. rewrite Q2.
  assert (H : forall b, In b (qc_list q) -> kBatchSize <= qb_size b).
  { intros b Hb. destruct (Q1 b Hb) as (_ & _ & _ & _ & _ & _ & _ & B8 & B9). rewrite B8.
    assert (S : 0 <= fold_right (fun (q0 : Z) (acc : Z) => match find_chunk (as_chunks st) (q0 + kChunkHeaderSize) with Some c => ch_used c | None => 0 end + acc) 0 (qb_chunks b)).
    { clear - W. induction (qb_chunks b) as [|q0 qs IH]; cbn; [lia|]. destruct (find_chunk (as_chunks st) (q0 + kChunkHeaderSize)) as [c0|] eqn:F; [| lia].
      pose proof (WFQ_chunk st XC XB c0 W (find_chunk_In _ _ _ F)) as (C1 & _). lia. }
    lia. }
  clear - H. induction (qc_list q) as [|b r IH]; [unfold zlen; cbn; lia|]. rewrite zlen_cons. cbn [fold_right].
  pose proof (H b (or_introl eq_refl)). assert (kBatchSize * zlen r <= fold_right (fun b0 acc => qb_size b0 + acc) 0 r) by (apply IH; intros; apply H; right; assumption).
  assert (0 <= zlen r) by (unfold zlen; lia). unfold kBatchSize in *. lia.
Qed.

(* [comment removed for export] *)
Lemma flagsx_transport5 : forall (P : Z -> Prop) ma mb, agree_on P ma mb -> wmono asegs ma mb ->
  (forall a, (ALIBCPGSZ <= a < ALIBCPGSZ + 8 \/ AGOT_SSP <= a < AGOT_SSP + 8 \/ ASSPGUARD <= a < ASSPGUARD + 8
              \/ ACFLAGS + 219 <= a < ACFLAGS + 220 \/ ACFLAGS + 244 <= a < ACFLAGS + 245) -> P a) ->
  flagsx_rep ma -> flagsx_rep mb.
Proof.
  intros P ma mb AG WM ZT FX.
  destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep.
  Ltac trz5 AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
    let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; lia.
  split; [trz5 AG WM FXa ZT|]. split; [trz5 AG WM FXb ZT|]. split; [exists g; trz5 AG WM FXc ZT|]. split; [trz5 AG WM FXd ZT|]. exists bb; trz5 AG WM FXe ZT.
Qed.
End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TransferPost.
  Context {HCEIL : HeapCeil}.
  Variables (sm : ast) (m2 m3 : mem) (spv : Z).   (* [comment removed for export] *)
  Let st := a_st sm.
  Let TH := a_thr sm.
  Let CTX := a_ctx sm.
  Let sb := a_sb sm.
  Let lt := qc_list (as_tq st).
  Let lg := qc_list (as_gq st).
  Let ng := zlen lg.
  Let fg := hd 0 (map qb_addr lg).
  Let LG := last (map qb_addr lg) 0.
  Let bg := qc_bytes (as_gq st).
  Let glb := last lg (mkQB 0 0 0 []).
  Let nt := zlen lt.
  Let ft := hd 0 (map qb_addr lt).
  Let LT := last (map qb_addr lt) 0.
  Let bt := qc_bytes (as_tq st).
  Let s3 := transfer_s sm.
  Let W : list ivl := drain_W spv (TH + OT_TQ) LG ng.
  Let P := outside W.

  Hypothesis RQ : AREPQ sm [] [] m2.
  Hypothesis SPV : aceil + 48 <= spv.
  Hypothesis TNE : lt <> [].
  Hypothesis MU : munch W m2 m3.
  Hypothesis WM : wmono asegs m2 m3.
  (* [comment removed for export] *)
  Hypothesis QM' : rw_cells asegs m3 (AINST + OI_QMUTEX) [C8 (wz 0)].
  Hypothesis GQ' : rw_cells asegs m3 (AINST + OI_GQ) [C8 (wz (ng + nt)); C8 (wz (if ng =? 0 then ft else fg)); C8 (wz LT); C8 (wz (bg + bt))].
  Hypothesis GL' : ng <> 0 -> rw_cells asegs m3 LG [C8 (wz ft); C8 (wz (qb_size glb)); C8 (wz (qb_count glb))].
  Hypothesis TQ' : rw_cells asegs m3 (TH + OT_TQ) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

  Let PL : placed_ok sm. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st [] []. Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let OKQ : placed_ok sm /\ WFQ (a_st sm) [] []. Proof. exact (conj PL WQ). Qed.
  Let MEM : ARmem sm m2. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
  Let AG : agree_on P m2 m3. Proof. exact (munch_agree _ _ _ MU). Qed.

  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  (* [comment removed for export] *)
  Let LGF : (lg = [] /\ ng = 0 /\ LG = 0)
            \/ (lg <> [] /\ ng <> 0 /\ lg = removelast lg ++ [glb] /\ LG = qb_addr glb /\ In glb (qc_list (as_tq st) ++ qc_list (as_gq st))
                /\ AHI_LO <= LG /\ LG + kBatchSize <= aceil /\ sb <= LG /\ LG + kBatchSize <= sb + kSpaceSize /\ carved st kBatchClass LG).
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    assert (D : lg = [] \/ lg <> []) by (destruct lg; [left; reflexivity| right; discriminate]).
    destruct D as [EL|NE].
    - left. split; [exact EL|]. unfold ng, LG. rewrite EL. split; reflexivity.
    - right. assert (EL : lg = removelast lg ++ [glb]) by (unfold glb; apply app_removelast_last; exact NE).
      assert (ELG : LG = qb_addr glb).
      { unfold LG. rewrite EL at 1. rewrite map_app. cbn [map]. rewrite last_app_nonnil by discriminate. reflexivity. }
      assert (IN : In glb (qc_list (as_tq st) ++ qc_list (as_gq st))) by (apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity).
      pose proof (batch_in_spaceQ sm [] [] OKQ glb IN) as (B1 & B2 & _). pose proof (batch_carvedQ sm [] [] OKQ glb IN) as (CV & _).
      pose proof PL as (_ & S2 & S3 & _). fold st sb in B1, B2, CV. rewrite <- ELG in B1, B2, CV.
      split; [exact NE|]. split; [unfold ng, zlen; intros E; apply NE; destruct lg; [reflexivity| cbn in E; lia]|].
      split; [exact EL|]. split; [exact ELG|]. split; [exact IN|].
      unfold kSpaceSize, kPageSize, kBatchSize in *. fold sb in S2, S3. clear - B1 B2 S2 S3 CV. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact CV].
  Qed.

  (* [comment removed for export] *)
  Let BND : aceil + 48 <= spv /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12599296 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 12599296 <= a_pa sm /\ a_pa sm + 8388608 <= aceil
            /\ 0 <= LG /\ (ng <> 0 -> 0x10007fff8000 <= LG /\ LG + 8192 <= aceil /\ (TH + 4096 <= LG \/ LG + 8192 <= TH) /\ (CTX + 160 <= LG \/ LG + 8192 <= CTX)).
  Proof.
    placed. clear AG MU WM QM' GQ' GL' TQ'. fold TH CTX sb in T2, T3, X2, X3, S2, S3.
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in X2; [| clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia].
    assert (L : 0 <= LG /\ (ng <> 0 -> 0x10007fff8000 <= LG /\ LG + 8192 <= aceil /\ (TH + 4096 <= LG \/ LG + 8192 <= TH) /\ (CTX + 160 <= LG \/ LG + 8192 <= CTX))).
    { destruct LGF as [(_ & NG0 & L0)|(_ & NGnz & _ & _ & _ & L1 & L2 & _ & _ & CV)].
      - rewrite L0. split; [apply Z.le_refl|]. intros NE. exfalso. exact (NE NG0).
      - pose proof (carved_vs_threadQ sm [] [] OKQ _ _ CV) as CT. pose proof (carved_vs_ctxQ sm [] [] OKQ _ _ CV) as CC.
        change (class_size kBatchClass) with 8192 in CT, CC. fold TH in CT. fold CTX in CC. unfold AHI_LO, kBatchSize, kPageSize in *.
        clear - L1 L2 CT CC. split; [lia|]. intros _. repeat split; lia. }
    unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. clear - SPV T2 T3 X2 X3 S2 S3 P2 P3 L.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact (proj2 L).
  Qed.
  (* [comment removed for export] *)
  Let BANDS : hidden ((TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa sm + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa sm)).
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'. pose proof PL as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _). fold TH in T2. fold CTX in X2.
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    pose proof (aapp_lit _ _ P2) as L. unfold kPtrArrayReserve in L. exact L.
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).

  (* [comment removed for export] *)
  Ltac wsplit := unfold W, drain_W; destruct (ng =? 0); cbn [outside app]; repeat split; try exact I.
  Lemma ZT_gen : forall a, a < aceil -> ~ (AINST + OI_QMUTEX <= a < AINST + OI_GQ + 32) -> ~ (TH + OT_TQ <= a < TH + OT_TQ + 32) ->
    (ng <> 0 -> ~ (LG <= a < LG + 8)) -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha N1 N2 N3. pose proof BND as BB. destruct (Z.eqb_spec ng 0) as [E|NE].
    - clear N3. unfold W, drain_W. rewrite (proj2 (Z.eqb_eq _ _) E). cbn [outside app]. unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ in *. clear - Ha N1 N2 BB. repeat split; try exact I; lia.
    - specialize (N3 NE). destruct BB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11). specialize (B11 NE).
      unfold W, drain_W. rewrite (proj2 (Z.eqb_neq _ _) NE). cbn [outside app]. unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ in *.
      clear - Ha N1 N2 N3 B1 B2 B3 B11. repeat split; try exact I; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ZT_lo : forall a, 65536 <= a < AIMG_TOP -> ~ (AINST + OI_QMUTEX <= a < AINST + OI_GQ + 32) -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha N1. pose proof BND as (_ & B2 & _). bands_as (BT & _). apply ZT_gen; [clear - Ha; acb; unfold AIMG_TOP in *; lia| exact N1| |];
      [| intros NE; destruct BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B11); destruct (B11 NE) as (L1 & _); clear - Ha L1; unfold AIMG_TOP in *; lia].
    clear - Ha B2 BT. unfold AIMG_TOP, OT_TQ in *. lia.
  Qed.
  Lemma ZT_static : forall a, astatic a -> ~ (AINST + OI_QMUTEX <= a < AINST + OI_GQ + 32) -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha N1. apply ZT_lo; [| exact N1]. clear - Ha. unfold astatic in Ha.
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP in *. lia.
  Qed.
  Lemma ZT_flags : forall a, aflags_range a -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha. apply ZT_lo; clear - Ha; unfold aflags_range in Ha;
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ZT_sh : forall a, a < AHI_LO -> ALOWSH_LO <= a -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha Hb. pose proof BND as (_ & B2 & _). bands_as (BT & _).
    apply ZT_gen; [clear - Ha; acb; unfold AHI_LO in *; lia| clear - Hb; unfold ALOWSH_LO, AINST, OI_QMUTEX, OI_GQ in *; lia| clear - Ha Hb B2 BT; unfold AHI_LO, ALOWSH_LO, OT_TQ in *; lia|].
    intros NE. destruct BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B11). destruct (B11 NE) as (L1 & _). clear - Ha L1. unfold AHI_LO in *. lia.
  Qed.
  Lemma ZT_SH : forall lo' kk a, 0 <= lo' -> 0 <= kk -> lo' + 8 * kk <= aceil -> sh lo' <= a < sh lo' + kk -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros lo' kk a H0 Hk Hhi Ha. apply ZT_sh; clear - H0 Hk Hhi Ha; acb; unfold sh, ASHADOW_BASE, AHI_LO, ALOWSH_LO in *; Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZT_hi : forall a, AHI_LO <= a < aceil -> ~ (TH + OT_TQ <= a < TH + OT_TQ + 32) -> (ng <> 0 -> ~ (LG <= a < LG + 8)) -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha N2 N3. apply ZT_gen; [clear - Ha; lia| clear - Ha; unfold AHI_LO, AINST, OI_QMUTEX, OI_GQ in *; lia| exact N2| exact N3].
  Qed.
  (* [comment removed for export] *)
  Lemma ZT_thr : forall a, TH <= a < TH + 4096 -> ~ (TH + OT_TQ <= a < TH + OT_TQ + 32) -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha N2. pose proof BND as (_ & B2 & B3 & _ & _ & _ & _ & _ & _ & _ & B11). bands_as (BT & _).
    apply ZT_gen; [clear - Ha B3; lia| clear - Ha BT; unfold AINST, OI_QMUTEX, OI_GQ in *; lia| exact N2|]. intros NE. destruct (B11 NE) as (_ & _ & L3 & _). clear - Ha L3. lia.
  Qed.
  Lemma ZT_ctx : forall a, CTX + 8 <= a < CTX + 160 -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha. pose proof BND as (_ & B2 & B3 & B4 & B5 & _ & _ & _ & _ & _ & B11). placed. fold TH CTX in TCX. destruct TCX as (TCX & _).
    apply ZT_gen; [clear - Ha B5; lia| clear - Ha B4; unfold AINST, OI_QMUTEX, OI_GQ in *; lia| clear - Ha TCX; unfold disj, kPageSize, OT_TQ in *; lia|].
    intros NE. destruct (B11 NE) as (_ & _ & _ & L4). clear - Ha L4. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZT_obj : forall X Y a, AIMG_TOP <= X -> Y <= aceil -> (TH + 4096 <= X \/ Y <= TH) -> (ng <> 0 -> LG + 8 <= X \/ Y <= LG) ->
    X <= a < Y -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros X Y a H1 H2 H3 H4 Ha. apply ZT_gen; [clear - H2 Ha; lia| clear - H1 Ha; unfold AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia| clear - H3 Ha; unfold OT_TQ; lia|].
    intros NE. specialize (H4 NE). clear - H4 Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ZT_rinfo : forall a, a_ri sm <= a < a_ri sm + kPageSize -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    apply (ZT_obj (a_ri sm) (a_ri sm + kPageSize) a); [| | | | exact Ha].
    - unfold a_ri. fold sb. clear - B6. unfold AIMG_TOP, kSpaceSize. lia.
    - unfold a_ri. fold sb. clear - B7. unfold kSpaceSize, kPageSize. lia.
    - unfold a_ri. fold sb. clear - D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & CV)]; [exfalso; exact (NE NG0)|].
      pose proof (carved_vs_rinfoQ sm [] [] OKQ _ _ CV) as CR. change (class_size kBatchClass) with 8192 in CR. clear - CR. lia.
  Qed.
  Lemma ZT_pa : forall a, a_pa sm <= a < a_pa sm + kPtrArrayReserve -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a Ha. pose proof BND as (_ & B2 & B3 & _ & _ & _ & _ & B8 & B9 & _). placed. fold TH in D4.
    apply (ZT_obj (a_pa sm) (a_pa sm + kPtrArrayReserve) a); [| | | | exact Ha].
    - clear - B8. unfold AIMG_TOP. lia.
    - clear - B9. unfold kPtrArrayReserve. lia.
    - clear - D4. unfold disj, kPtrArrayReserve, kPageSize in *. lia.
    - intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & CV)]; [exfalso; exact (NE NG0)|].
      pose proof (carved_vs_paQ sm [] [] OKQ _ _ CV) as CR. change (class_size kBatchClass) with 8192 in CR. clear - CR. lia.
  Qed.
  Lemma ZT_sechdr : forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros h a Hh Ha. placed. pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). fold TH in Q7.
    apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
    apply (ZT_obj (sc_map_beg h) (sc_map_beg h + kPageSize) a); [| | | | exact Ha].
    - clear - Q2. unfold AIMG_TOP. lia.
    - clear - Q3 Q4. unfold kPageSize in *. lia.
    - clear - Q7 Q4. unfold disj, kPageSize in *. lia.
    - intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & CV)]; [exfalso; exact (NE NG0)|].
      pose proof (carved_vs_secQ sm [] [] OKQ _ _ CV h Hh) as CR. change (class_size kBatchClass) with 8192 in CR. clear - CR Q4. unfold kPageSize in *. lia.
  Qed.
  Lemma ZT_farray : forall c0 a, 0 <= c0 < kNumClasses -> FA sm c0 <= a < FA sm c0 + rg_mapped_free_array (get_region st c0) -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros c0 a Hc0 Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    pose proof (farray_in_spaceQ sm [] [] OKQ c0 Hc0) as (F1' & F2' & _). fold st sb in F1', F2'.
    apply (ZT_obj (FA sm c0) (FA sm c0 + rg_mapped_free_array (get_region st c0)) a); [| | | | exact Ha].
    - clear - F1' B6. unfold AIMG_TOP. lia.
    - clear - F2' B7. unfold kSpaceSize in *. lia.
    - clear - F1' F2' D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & CV)]; [exfalso; exact (NE NG0)|].
      pose proof (carved_vs_farrayQ sm [] [] OKQ _ _ CV c0 Hc0) as CR. change (class_size kBatchClass) with 8192 in CR. fold st in CR. clear - CR. lia.
  Qed.
  Lemma ZT_tail : forall c0 a, 0 <= c0 < kNumClasses ->
    RB sm c0 + rg_allocated_user (get_region st c0) <= a < RB sm c0 + rg_mapped_user (get_region st c0) -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros c0 a Hc0 Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    pose proof (tail_in_spaceQ sm [] [] OKQ c0 Hc0) as (F1' & F2' & _). fold st sb in F1', F2'.
    apply (ZT_obj (RB sm c0 + rg_allocated_user (get_region st c0)) (RB sm c0 + rg_mapped_user (get_region st c0)) a); [| | | | exact Ha].
    - clear - F1' B6. unfold AIMG_TOP. lia.
    - clear - F2' B7. unfold kSpaceSize in *. lia.
    - clear - F1' F2' D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & CV)]; [exfalso; exact (NE NG0)|].
      pose proof (carved_vs_tailQ sm [] [] OKQ _ _ CV c0 Hc0) as CR. change (class_size kBatchClass) with 8192 in CR. fold st in CR. clear - CR. lia.
  Qed.
  Lemma ZT_freech : forall c0 cp a, 0 <= c0 < kNumClasses -> In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
    compact_to_addr st c0 cp <= a < compact_to_addr st c0 cp + class_size c0 -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros c0 cp a Hc0 Hin Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    pose proof (freech_in_spaceQ sm [] [] OKQ c0 cp Hc0 Hin) as (F1' & F2' & _). fold st sb in F1', F2'.
    apply (ZT_obj (compact_to_addr st c0 cp) (compact_to_addr st c0 cp + class_size c0) a); [| | | | exact Ha].
    - clear - F1' B6. unfold AIMG_TOP. lia.
    - clear - F2' B7. unfold kSpaceSize in *. lia.
    - clear - F1' F2' D2. unfold disj, kSpaceSize, kPageSize in *. lia.
    - intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & IN & _ & _ & _ & _ & CV)]; [exfalso; exact (NE NG0)|].
      pose proof (carved_vs_freechQ sm [] [] OKQ _ _ CV c0 cp Hc0 Hin) as CR. change (class_size kBatchClass) with 8192 in CR. fold st in CR.
      destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & ELG & _)]; [exfalso; exact (NE NG0)|].
      assert (NEQ : compact_to_addr st c0 cp <> LG) by (rewrite ELG; intros E; exact (batch_not_freeQ sm [] [] OKQ glb c0 cp IN Hc0 Hin (eq_sym E))).
      specialize (CR NEQ). clear - CR. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZT_rec : forall x a, In x (chunk_list st) -> ch_lo x <= a < ch_end x -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros x a Hx Ha. pose proof BND as (_ & B2 & B3 & _). placed. fold TH sb in D2.
    pose proof (record_extQ sm [] [] OKQ x Hx) as (E1 & E2 & _).
    assert (XT : TH + 4096 <= ch_lo x \/ ch_end x <= TH).
    { destruct (ch_primary x) eqn:E.
      - pose proof (record_primary_spaceQ sm [] [] OKQ x Hx E) as [R1 R2]. fold sb in R1, R2. clear - R1 R2 D2. unfold disj, kSpaceSize, kPageSize in *. lia.
      - destruct (record_secondary_mapQ sm [] [] OKQ x Hx E) as (h & Hh & L0 & E0 & _). pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & _ & D & _). fold TH in D.
        clear - L0 E0 D. unfold disj, kPageSize in *. lia. }
    apply (ZT_obj (ch_lo x) (ch_end x) a); [exact E1| exact E2| exact XT| | exact Ha].
    intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & ELG & IN & _)]; [exfalso; exact (NE NG0)|].
    pose proof (batch_vs_recordQ sm [] [] OKQ x Hx glb IN) as BR. rewrite <- ELG in BR. clear - BR. unfold kBatchSize in BR. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZT_batch : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> qb_addr b <> LG -> qb_addr b <= a < qb_addr b + kBatchSize -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros b a Hb NE Ha. pose proof BND as (_ & B2 & B3 & _ & _ & B6 & B7 & _). placed. fold TH sb in D2.
    pose proof (batch_in_spaceQ sm [] [] OKQ b Hb) as (P1' & P2' & _). fold st sb in P1', P2'.
    apply (ZT_obj (qb_addr b) (qb_addr b + kBatchSize) a); [| | | | exact Ha].
    - clear - P1' B6. unfold AIMG_TOP. lia.
    - clear - P2' B7. unfold kSpaceSize, kBatchSize in *. lia.
    - clear - P1' P2' D2. unfold disj, kSpaceSize, kPageSize, kBatchSize in *. lia.
    - intros NG. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & CV)]; [exfalso; exact (NG NG0)|].
      pose proof (carved_vs_batchQ sm [] [] OKQ _ _ CV b Hb NE) as CR. change (class_size kBatchClass) with 8192 in CR. clear - CR. unfold kBatchSize in *. lia.
  Qed.
  Lemma ZT_glb : forall a, ng <> 0 -> LG + 8 <= a < LG + kBatchSize -> outside W a.
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    intros a NE Ha. pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B11). destruct (B11 NE) as (L1 & L2 & L3 & _).
    apply (ZT_obj (LG + 8) (LG + kBatchSize) a); [clear - L1; unfold AIMG_TOP; lia| clear - L2; unfold kBatchSize; lia| clear - L3; unfold kBatchSize; lia| intros _; left; apply Z.le_refl| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Ltac trc H Z := eapply (rw_cells_transport_pt P m2 m3 AG WM); [exact H|];
                  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length repeat map]; intros ? ?; Z.
  Ltac trj H Z := eapply (junk_transport_pt P m2 m3 AG WM); [exact H|]; intros ? ?; Z.

  Lemma inst_after_transfer : inst_rep s3 m3.
  Proof.
    clear GL' TQ'.
    pose proof MEM as (INST & _). destruct INST as (A1 & J1 & A2 & J2 & A3 & J3 & J4 & A5 & J5 & A6 & A7 & J6 & A8 & J7 & A9).
    unfold inst_rep. change (a_sb s3) with (a_sb sm). change (a_ri s3) with (a_ri sm). change (a_pa s3) with (a_pa sm). change (a_st s3) with (transfer_m st).
    change (as_n_reserved (transfer_m st)) with (as_n_reserved st). change (as_sec (transfer_m st)) with (as_sec st).
    change (as_qmax (transfer_m st)) with (as_qmax st). change (as_qmin (transfer_m st)) with (as_qmin st). change (as_qcache (transfer_m st)) with (as_qcache st).
    change (qc_list (as_gq (transfer_m st))) with (lg ++ lt). change (qc_bytes (as_gq (transfer_m st))) with (bg + bt).
    Ltac zi Ha := apply ZT_lo; clear - Ha; unfold AINST, AIMG_TOP, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX, OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER in *; lia.
    split; [trc A1 ltac:(zi H)|]. split; [trj J1 ltac:(zi H)|]. split; [trc A2 ltac:(zi H)|]. split; [trj J2 ltac:(zi H)|].
    split; [trc A3 ltac:(zi H)|]. split; [trj J3 ltac:(zi H)|]. split; [trj J4 ltac:(zi H)|]. split; [trc A5 ltac:(zi H)|]. split; [trj J5 ltac:(zi H)|].
    split; [exact QM'|].
    split. { rewrite zlen_app. fold ng nt. rewrite map_app, hd_app_hd. fold ft.
             replace (hd ft (map qb_addr lg)) with (if ng =? 0 then ft else fg) by (unfold ng, fg, zlen; destruct lg; reflexivity).
             rewrite last_app_nonnil by (apply map_nonnil; exact TNE). fold LT. exact GQ'. }
    split; [trj J6 ltac:(zi H)|]. split; [trc A8 ltac:(zi H)|]. split; [trj J7 ltac:(zi H)| trc A9 ltac:(zi H)].
  Qed.

  Lemma thread_after_transfer : thread_rep s3 m3.
  Proof.
    clear QM' GQ' GL' TNE.
    pose proof MEM as (_ & _ & THR & _). destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_thr s3) with TH. change (a_ctx s3) with CTX. change (a_top s3) with (a_top sm). change (a_bot s3) with (a_bot sm).
    change (a_cache s3) with (a_cache sm). change (a_st s3) with (transfer_m st). change (qc_list (as_tq (transfer_m st))) with (@nil qbatch).
    change (qc_bytes (as_tq (transfer_m st))) with 0. cbn [zlen length Z.of_nat map hd last].
    fold TH CTX in T1, T2, T2b, T2c, T2d, T3, J1, J3, T5.
    Ltac zt Ha := first [apply ZT_thr; clear - Ha; unfold OT_TQ, OT_CACHE, OT_SWITCHING, OT_STATS, OT_UNWINDING, CACHE_STATS, a_cache in *; lia | apply ZT_ctx; clear - Ha; lia].
    split; [trc T1 ltac:(zt H)|]. split; [trc T2 ltac:(zt H)|]. split; [trc T2b ltac:(zt H)|]. split; [trc T2c ltac:(zt H)|]. split; [trc T2d ltac:(zt H)|].
    split; [trc T3 ltac:(zt H)|]. split; [exact TQ'|]. split; [trj J1 ltac:(zt H)|].
    split; [trj J2 ltac:(unfold a_cache in *; fold TH in H; zt H)|]. split; [trj J3 ltac:(zt H)| trc T5 ltac:(zt H)].
  Qed.

  Let NDB : List.NoDup (map qb_addr (lt ++ lg)).
  Proof.
    clear AG MU WM QM' GQ' GL' TQ'.
    pose proof (WFQ_carved _ _ _ WQ) as ND. rewrite app_nil_r, (carved_addr_list_eq sm) in ND.
    exact (NoDup_app_r _ _ (NoDup_app_r _ _ ND)).
  Qed.
  Let BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> 0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b).
  Proof. clear AG MU WM QM' GQ' GL' TQ'. intros b Hb. pose proof (WFQ_batch _ _ _ b WQ Hb) as (B1 & B2 & _). unfold kBatchSize, kBatchCount in *. lia. Qed.

  Lemma batches_after_transfer : batches_rep m3 (lg ++ lt).
  Proof.
    clear QM' GQ' TQ' TNE.
    pose proof MEM as (_ & _ & _ & _ & _ & _ & _ & BT & BG). fold st lt in BT. fold st lg in BG.
    apply (proj2 (blist0 m3 (lg ++ lt))). apply (proj2 (blist_app m3 lg lt 0)). fold ft. split.
    - (* [comment removed for export] *)
      destruct LGF as [(EL & _)|(NE & NG & EL & ELG & IN & _)]; [rewrite EL; exact I|].
      rewrite EL. apply (proj2 (blist_app m3 (removelast lg) [glb] ft)). cbn [map hd blist]. rewrite <- ELG.
      apply (proj1 (blist0 m2 lg)) in BG. rewrite EL in BG. apply (proj1 (blist_app m2 (removelast lg) [glb] 0)) in BG. cbn [map hd blist] in BG. rewrite <- ELG in BG.
      destruct BG as [B0 [Bl _]].
      assert (SUB : forall b, In b (removelast lg) -> In b (qc_list (as_tq st) ++ qc_list (as_gq st)) /\ qb_addr b <> LG).
      { intros b Hb. split; [apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; left; exact Hb|].
        rewrite map_app in NDB. apply NoDup_app_r in NDB. rewrite EL, map_app in NDB. cbn [map] in NDB. rewrite <- ELG in NDB.
        intros E. apply (NoDup_app_disjoint _ _ LG NDB); [| left; reflexivity]. rewrite <- E. apply in_map_iff. exists b. split; [reflexivity| exact Hb]. }
      split.
      + apply (blist_transport_pt P m2 m3 (removelast lg) LG AG WM); [intros b Hb; apply BOK; exact (proj1 (SUB b Hb))| | exact B0].
        intros b a Hb [Ha|Ha]; [apply (ZT_batch b a (proj1 (SUB b Hb)) (proj2 (SUB b Hb)) Ha)|].
        apply (ZT_SH (qb_addr b) 1024 a); [| | | exact Ha]; pose proof (batch_in_spaceQ sm [] [] OKQ b (proj1 (SUB b Hb))) as (P1' & P2' & _);
          pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _); fold sb in P1', P2'; clear - P1' P2' B6 B7; unfold kBatchSize, kSpaceSize in *; lia.
      + split; [| exact I]. pose proof (BOK glb IN) as (C1 & C2 & C3). destruct Bl as (Q1 & Q2 & Q3 & Q4). unfold batch_rep. rewrite <- ELG in Q2, Q3, Q4 |- *.
        pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B11). destruct (B11 NG) as (L1 & L2 & _). unfold zlen in C3. unfold kBatchSize in C2.
        split; [exact (GL' NG)|].
        split; [eapply (u64arr_transport_pt P m2 m3 AG WM); [exact Q2|]; unfold wlist; rewrite length_map; intros a Ha; apply (ZT_glb a NG); clear - Ha C1 C2 C3; unfold kBatchSize; lia|].
        split; [trj Q3 ltac:(apply (ZT_glb _ NG); clear - H C1 C2; unfold kBatchSize in *; lia)|].
        eapply (poisoned_transport_pt P m2 m3 AG WM); [exact Q4|]. intros a Ha. change (Z.of_nat (Z.to_nat (kBatchSize / 8))) with 1024 in Ha.
        apply (ZT_SH LG 1024 a); [| | | exact Ha]; clear - L1 L2; unfold AHI_LO in *; lia.
    - (* [comment removed for export] *)
      apply (proj1 (blist0 m3 lt)).
      assert (SUB : forall b, In b lt -> In b (qc_list (as_tq st) ++ qc_list (as_gq st)) /\ qb_addr b <> LG).
      { intros b Hb. split; [apply in_app_iff; left; exact Hb|].
        destruct LGF as [(_ & _ & L0)|(NE & NG & EL & ELG & IN & L1 & _)].
        - rewrite L0. pose proof (batch_in_spaceQ sm [] [] OKQ b ltac:(apply in_app_iff; left; exact Hb)) as (P1' & _). pose proof BND as (_ & _ & _ & _ & _ & B6 & _).
          fold sb in P1'. clear - P1' B6. lia.
        - intros E. rewrite map_app in NDB. apply (NoDup_app_disjoint _ _ LG NDB).
          + rewrite <- E. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
          + rewrite EL, map_app. cbn [map]. rewrite <- ELG. apply in_app_iff. right. left. reflexivity. }
      eapply (batches_rep_transport P m2 m3 lt AG WM); [| intros b Hb; apply BOK; exact (proj1 (SUB b Hb))| exact BT].
      intros b a Hb [Ha|Ha]; [apply (ZT_batch b a (proj1 (SUB b Hb)) (proj2 (SUB b Hb)) Ha)|].
      apply (ZT_SH (qb_addr b) 1024 a); [| | | exact Ha]; pose proof (batch_in_spaceQ sm [] [] OKQ b (proj1 (SUB b Hb))) as (P1' & P2' & _);
        pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _); fold sb in P1', P2'; clear - P1' P2' B6 B7; unfold kBatchSize, kSpaceSize in *; lia.
  Qed.

  Lemma armem_after_transfer : ARmem s3 m3.
  Proof.
    pose proof MEM as (INST & FL & THR & SC & IA & RC & CH & BT & BG).
    split; [exact inst_after_transfer|].
    split; [exact (flags_rep_frame sm m2 m3 P AG WM ZT_flags FL)|].
    split; [exact thread_after_transfer|].
    split. { apply (sec_rep_frameQ sm [] [] m2 m3 P AG WM WQ); [| | exact SC].
             - intros a Ha. apply ZT_pa. pose proof WQ as (_ & _ & _ & _ & _ & _ & _ & RES & _). fold st in Ha.
               clear - Ha RES. unfold kPtrArrayReserve, kChunksBlockCount in *. lia.
             - intros h a Hh Ha. exact (ZT_sechdr h a Hh Ha). }
    split. { apply (ia_rep_frame sm m2 m3 P AG WM); [| exact IA]. intros a Ha. apply ZT_lo; clear - Ha; unfold AIAINST, AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia. }
    split. { intros c Hc. destruct (RC c Hc) as (R1 & R2 & R3 & R4).
             split; [exact (region_rep_frameQ sm [] [] m2 m3 P AG WM WQ c Hc ZT_rinfo (fun a Ha => ZT_farray c a Hc Ha) (fun a Ha => ZT_tail c a Hc Ha) R1)|].
             split. { apply (pclass_rep_frameQ sm [] [] m2 m3 P AG WM WQ c Hc); [| exact R2]. intros a Ha. apply ZT_thr; unfold a_cache, OT_CACHE, PCLASS_SIZE, OT_TQ, kNumClasses in *; fold TH in Ha; clear - Ha Hc; lia. }
             split; [| exact (region_junk_rep_frame sm m2 m3 P AG WM c Hc (fun cp a Hin Ha => ZT_freech c cp a Hc Hin Ha) R4)].
             apply (region_shadow_rep_frameQ sm [] [] m2 m3 P AG WM WQ c Hc); [| | | exact R3].
             - intros cp a Hin Ha. pose proof (freech_in_spaceQ sm [] [] OKQ c cp Hc Hin) as (F1' & F2' & _ & F4' & _). pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _). fold st sb in F1', F2'.
               pose proof (class_size_table_facts c Hc) as (_ & CS8 & _).
               apply (ZT_SH (compact_to_addr st c cp) (class_size c / 8) a); [| | | exact Ha]; clear - F1' F2' F4' B6 B7 CS8; zlets; unfold kSpaceSize in *; Z.div_mod_to_equations; lia.
             - intros a Ha. pose proof (tail_in_spaceQ sm [] [] OKQ c Hc) as (F1' & F2' & _ & F4' & F5'). pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _). fold st sb in F1', F2'.
               apply (ZT_SH (RB sm c + rg_allocated_user (get_region st c)) ((rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c)) / 8) a); [| | | exact Ha];
                 clear - F1' F2' F4' F5' B6 B7; zlets; unfold kSpaceSize in *; Z.div_mod_to_equations; lia.
             - intros a Ha. pose proof (farray_in_spaceQ sm [] [] OKQ c Hc) as (F1' & F2' & _ & F4' & F5'). pose proof BND as (_ & _ & _ & _ & _ & B6 & B7 & _). fold st sb in F1', F2'.
               apply (ZT_SH (FA sm c) (rg_mapped_free_array (get_region st c) / 8) a); [| | | exact Ha]; clear - F1' F2' F4' F5' B6 B7; zlets; unfold kSpaceSize in *; Z.div_mod_to_equations; lia. }
    split. { intros x Hx. apply (chunk_rep_frameQ sm [] [] m2 m3 P AG WM WQ x Hx); [| exact (CH x Hx)].
             pose proof (record_extQ sm [] [] OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
             assert (RU : ch_used x <= round_up (ch_used x) 8) by (clear; unfold round_up; Z.div_mod_to_equations; lia).
             assert (NS : 0 <= nsh (ch_used x) /\ 8 * nsh (ch_used x) = round_up (ch_used x) 8) by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; lia).
             intros a [Ha|[Ha|[[_ Ha]|[Ha|[Ha|[[_ Ha]|[NP Ha]]]]]]].
             - apply (ZT_rec x a Hx). clear - Ha X3 X6 X7 X8 X9 RU. lia.
             - apply (ZT_rec x a Hx). clear - Ha X3 X6 X8 X9. lia.
             - apply (ZT_rec x a Hx). clear - Ha X3 X6 X7 X8 X9 RU. lia.
             - apply (ZT_SH (ch_alloc_beg x) (ch_rz x / 8) a); [| | | exact Ha]; clear - X1 X2 X3 X6 X7 X8 X9 RU; unfold AHI_LO, AIMG_TOP in *; Z.div_mod_to_equations; lia.
             - apply (ZT_SH (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) a); [| | | exact Ha];
                 clear - X1 X2 X3 X6 X7 X8 X9 RU; unfold AHI_LO, AIMG_TOP in *; Z.div_mod_to_equations; lia.
             - apply (ZT_SH (ch_user_beg x) (nsh (ch_used x)) a); [| | | exact Ha]; clear - X1 X2 X3 X6 X7 X8 X9 NS; unfold AHI_LO, AIMG_TOP in *; lia.
             - apply (ZT_SH (ch_alloc_beg x - kPageSize) 512 a); [| | | exact Ha]; unfold ch_lo in X1; rewrite NP in X1; clear - X1 X2 X6 X7 X8 X9 RU; unfold AHI_LO, AIMG_TOP, kPageSize in *; lia. }
    change (qc_list (as_tq (a_st s3))) with (@nil qbatch). change (qc_list (as_gq (a_st s3))) with (lg ++ lt).
    split; [exact I| exact batches_after_transfer].
  Qed.

  Lemma arepq_after_transfer : AREPQ s3 [] [] m3.
  Proof. split; [exact PL|]. split; [exact (WFQ_transfer st WQ)| exact armem_after_transfer]. Qed.
  Lemma arep_after_transfer : bg + bt <= kQuarantineMaxSize -> AREP s3 m3.
  Proof.
    intros LE. apply AREP_of_AREPQ; [exact arepq_after_transfer|]. pose proof (WFQ_consts _ _ _ WQ) as (C1 & _ & C3).
    split.
    - change (qc_bytes (as_tq (a_st s3))) with 0. change (as_qcache (a_st s3)) with (as_qcache st). rewrite C3. unfold kMaxCacheSize. clear; lia.
    - change (qc_bytes (as_gq (a_st s3))) with (bg + bt). change (as_qmax (a_st s3)) with (as_qmax st). rewrite C1. exact LE.
  Qed.
  Lemma arheap_after_transfer : forall LB, ARHEAPQ sm [] [] LB m2 -> bg + bt <= kQuarantineMaxSize -> ARHEAP s3 LB m3.
  Proof. intros LB (_ & ND & LBs) LE. split; [exact (arep_after_transfer LE)|]. split; [exact ND|]. exact LBs. Qed.

  (* [comment removed for export] *)
  Lemma flagsx_after_transfer : flagsx_rep m2 -> flagsx_rep m3.
  Proof.
    clear QM' GQ' GL' TQ' TNE.
    intros FX. destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep.
    Ltac trz H := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
      let Ha := fresh in intros ? Ha; apply ZT_lo; clear - Ha; unfold ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIMG_TOP, AINST, OI_QMUTEX, OI_GQ in *; lia.
    split; [trz FXa|]. split; [trz FXb|]. split; [exists g; trz FXc|]. split; [trz FXd|]. exists bb; trz FXe.
  Qed.
  Lemma depot_after_transfer : forall d, depot_placed sm d -> DEPOT asegs d m2 -> DEPOT asegs d m3.
  Proof.
    clear AG QM' GQ' GL' TQ' TNE.
    intros d DPL DEP. pose proof BND as (B1 & B2 & B3 & _ & _ & _ & _ & _ & _ & _ & B11). pose proof DPL as (G1 & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4). fold TH in G1. pose proof DPL as (_ & G2 & _). fold TH in G2.
    apply aapp_env in N1; [| clear; lia]. apply aapp_env in N3; [| clear; lia].   (* [comment removed for export] *)
    assert (GL : ng <> 0 -> (d_nb d + 16 * 65536 <= LG \/ LG + 8192 <= d_nb d) /\ (d_sb d + 8 * 131072 <= LG \/ LG + 8192 <= d_sb d)).
    { intros NE. destruct LGF as [(_ & NG0 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & CV)]; [exfalso; exact (NE NG0)|].
      pose proof (carved_vs_depotQ sm [] [] OKQ _ _ CV d DPL) as CD. change (class_size kBatchClass) with 8192 in CD. exact CD. }
    eapply (DEPOT_transport asegs d m2 m3 W DEP MU WM).
    unfold depot_avoid, avoids, W, drain_W. destruct (Z.eqb_spec ng 0) as [E|NE]; cbn [app].
    - clear GL B11. bands_as (BT & _). unfold AHI_LO, AINST, OI_QMUTEX, OI_GQ, OT_TQ, disj, kPageSize in *. acb. clear - B1 B2 B3 G1 G2 N1 N2 N3 N4 ACEILB BT.
      repeat split; repeat (first [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; lia|]]).
    - specialize (GL NE). specialize (B11 NE). bands_as (BT & _). unfold AHI_LO, AINST, OI_QMUTEX, OI_GQ, OT_TQ, disj, kPageSize in *. acb. clear - B1 B2 B3 G1 G2 N1 N2 N3 N4 ACEILB GL B11 BT.
      repeat split; repeat (first [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; lia|]]).
  Qed.
End TransferPost.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FreeTail1.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk).

  Let st := a_st s.
  Let TH := a_thr s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let LB' := lb_remove U LB.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.

  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  Lemma hd_addr_cases : forall l : list qbatch, hd 0 (map qb_addr l) = 0 \/ exists b, In b l /\ hd 0 (map qb_addr l) = qb_addr b.
  Proof. intros l. destruct l as [|b r]; [left; reflexivity| right; exists b; split; [left; reflexivity| reflexivity]]. Qed.
  Lemma last_In_qb : forall (l : list qbatch) d0, l <> [] -> In (last l d0) l.
  Proof. induction l as [|x r IH]; intros d0 NE; [exact (False_ind _ (NE eq_refl))|]. destruct r as [|y r]; [left; reflexivity|]. right. change (last (x :: y :: r) d0) with (last (y :: r) d0). apply (IH d0). discriminate. Qed.
  Lemma last_addr_cases : forall l : list qbatch, last (map qb_addr l) 0 = 0 \/ exists b, In b l /\ last (map qb_addr l) 0 = qb_addr b.
  Proof.
    intros l. assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]). destruct D as [->|NE]; [left; reflexivity| right].
    exists (last l (mkQB 0 0 0 [])). split; [apply last_In_qb; exact NE|].
    rewrite (app_removelast_last (mkQB 0 0 0 []) NE) at 1. rewrite map_app. cbn [map]. rewrite last_app_nonnil by discriminate. reflexivity.
  Qed.

  Theorem free_tail1 : forall sm msF2 mo2,
    free_mids ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo CH ch sm msF2 mo2 ->
    kMaxCacheSize < qc_bytes (as_tq (a_st sm)) -> qc_bytes (as_gq (a_st sm)) + qc_bytes (as_tq (a_st sm)) <= kQuarantineMaxSize ->
    (forall msF' mo', free_gpostX ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo CH ch msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF2 mo2).
  Proof.
    intros sm msF2 mo2 MID GT LE K.
    destruct MID as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jk & rest & m2 & Ethr & Ectx & Efsb & Ezr & Etop & Ebot & Esb & Epa & Esec & Egq & HAL & TNE & TQB & GQB & OK2 & VIS2 & HQ & AWV & FX & AMX & NVS & DEP & DPL & DCOV & MI2 & ST2 & PFR & ESO & TRB & LR & NR & TFB & F4 & AMF & WM & ACM & AVX & (stX & ev0 & ev2 & EM & SBS & SC0)).
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
    assert (HI' : lo + 2496 <= bv_unsigned sp) by (clear - HI; lia).
    assert (THR : hidden (akobj (a_thr s) 4096 /\ a_thr s + 4096 <= aceil /\ a_thr s mod 16 = 0)).   (* [comment removed for export] *)
    { constructor. unfold kPageSize in T1, T2, T3. clear - T1 T2 T3. split; [exact T2|]. split; [exact T3|]. Z.div_mod_to_equations. lia. }
    eapply (evt_sreach_lazy_at asegs (a_L sm) (a_S sm) (a_Zr sm) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (@put_drain_norec _ sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc lo T rest jk LO HI' SPT LR NR
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
      - exact ESO.
      - exact TRB.
      - exact TFB.
      - exact F4.
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
    assert (SPV : aceil + 48 <= bv_unsigned sp + -2208) by (clear - HI LO; lia).
    rewrite <- Ethr in MU1, TQ'.
    pose proof (arheap_after_transfer sm m2 m1 (bv_unsigned sp + -2208) RQ SPV TNE MU1 WM1 QM' GQ' GL' TQ' LB' HQ LE) as HR3.
    pose proof (flagsx_after_transfer sm m2 m1 _ RQ SPV MU1 WM1 FX) as FX1.
    pose proof (depot_after_transfer sm m2 m1 _ RQ SPV MU1 WM1 d' DPL DEP) as DEP1.
    assert (OK3 : ast_ok (transfer_s sm)) by exact (proj1 (proj1 HR3)).
    assert (OKs : ast_ok s) by exact (proj1 (proj1 HR)).
    assert (HLB' : forall b, In b LB' -> In b (alb s)) by (intros b Hb; apply lb_remove_In in Hb; exact (proj1 (proj2 (proj2 HR) b) (proj1 Hb))).
    assert (SPc : aceil <= bv_unsigned sp) by (clear - HI LO; lia).
    (* [comment removed for export] *)
    assert (APR : Forall (fun iv : ivl => apriv s LB' (bv_unsigned sp) (fst iv) (snd iv)) (drain_W (bv_unsigned sp + -2208) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg))).
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
    { apply (flagsx_transport5 (outside [(lo, bv_unsigned sp + -2128)]) m1 m' (munch_agree _ _ _ MU') WM'); [| exact FX1].
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
    apply K. unfold free_gpostX.
    exists (transfer_s sm), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m'.
    split; [exact Ethr|]. split; [exact Ectx|]. split; [exact Efsb|]. split; [exact Ezr|]. split; [exact Etop|]. split; [exact Ebot|].
    split; [intros sc Hsc; rewrite <- Esec; exact Hsc|]. split; [exact HAL|].
    split; [exact OK'|]. split; [exact VIS'|].
    split; [exact HR'|].
    split; [exact (awin_vis_wmono sm m2 m' AWV (wmono_trans _ _ _ _ WM1 WM'))|]. split; [exact FX'|]. split; [exact (AMODELX_mat sm mo2 mo' AMX SBM)|].
    split; [exact (nonvm_same_trans _ _ _ NVS (nonvm_same_mat mo2 mo' SBM))|].
    split; [exact DEP'|]. split; [exact DPL|].
    split; [unfold depot_cov in DCOV |- *; intros x Hx; rewrite (same_but_materialized_vmmaps mo2 mo' SBM); exact (DCOV x Hx)|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact AMF'|].
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
End FreeTail1.

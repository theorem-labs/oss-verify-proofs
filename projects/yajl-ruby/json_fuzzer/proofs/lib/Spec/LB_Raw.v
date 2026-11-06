(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ITree Nodes NodesMat Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl RawAlloc KInv KLink KStep
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_TF2 MI_WFree2 MI_WGroup MI_WSlot MI_WMalloc MI_WEnframe2 MI_Cnt MI_Sim MI_Contracts
  LB_Kernel LB_Embed LB_Tables LB_Inv LB_Sum LB_Bound LB_Tree LB_StmtA LB_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition bs (k : blk) : cptr * Z := (bslot k, bsize k).
Definition xs (xb : bptr * Z) : cptr * Z := (fst (fst xb), snd xb).

(* [comment removed for export] *)
Definition LRX (X : list (bptr * Z)) (c : Z) : Z := zcount (fun xb => negb (MMAP_THRESHOLD <=? snd xb) && (size_to_class (snd xb) =? c)) X.
Definition n63X (X : list (bptr * Z)) : Z := zcount (fun xb => MMAP_THRESHOLD <=? snd xb) X.
Definition R63X (X : list (bptr * Z)) : Z := zsum (map (fun xb => if MMAP_THRESHOLD <=? snd xb then round_up_pg (snd xb + IB + UNIT) + PGSZ else 0) X).  (* [comment removed for export] *)
Definition ROOMX (X : list (bptr * Z)) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LRX X (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63X X + 1 <= P 63)
  /\ zlen X + 1 <= P 0.   (* [comment removed for export] *)

Lemma zcount_map {A B} (f : A -> B) (p : B -> bool) l : zcount p (map f l) = zcount (fun x => p (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

Lemma LRX_eq X BL c : Permutation (map xs X) (map bs BL) -> LRX X c = LR BL c.
Proof.
  intros HP. unfold LRX, LR, isbig.
  transitivity (zcount (fun q : cptr * Z => negb (MMAP_THRESHOLD <=? snd q) && (size_to_class (snd q) =? c)) (map xs X)); [rewrite zcount_map; reflexivity|].
  rewrite (zcount_perm _ _ _ HP), zcount_map. reflexivity.
Qed.
Lemma n63X_eq X BL : Permutation (map xs X) (map bs BL) -> n63X X = n63 BL.
Proof.
  intros HP. unfold n63X, n63, isbig.
  transitivity (zcount (fun q : cptr * Z => MMAP_THRESHOLD <=? snd q) (map xs X)); [rewrite zcount_map; reflexivity|].
  rewrite (zcount_perm _ _ _ HP), zcount_map. reflexivity.
Qed.
Lemma R63X_eq X BL : Permutation (map xs X) (map bs BL) -> R63X X = R63 BL.
Proof.
  intros HP. unfold R63X, R63, isbig.
  transitivity (zsum (map (fun q : cptr * Z => if MMAP_THRESHOLD <=? snd q then round_up_pg (snd q + IB + UNIT) + PGSZ else 0) (map xs X))); [rewrite map_map; reflexivity|].
  rewrite (zsum_map_perm _ _ _ HP), map_map. reflexivity.
Qed.
Lemma zlenX_eq X BL : Permutation (map xs X) (map bs BL) -> zlen X = zlen BL.
Proof. intros HP. unfold zlen. rewrite <- (length_map xs X), <- (length_map bs BL). rewrite (Permutation_length HP). reflexivity. Qed.
Lemma ROOMX_eq X BL P n : Permutation (map xs X) (map bs BL) -> ROOMX X P n -> ROOM BL P n.
Proof.
  intros HP (R1 & R2 & R3). split; [rewrite <- (LRX_eq X BL _ HP); exact R1|].
  split; [rewrite <- (n63X_eq X BL HP); exact R2| rewrite <- (zlenX_eq X BL HP); exact R3].
Qed.

Lemma R63X_cons p n X : R63X ((p, n) :: X) = bigb n + R63X X.
Proof. unfold R63X, bigb. cbn [map snd]. rewrite zsum_cons. reflexivity. Qed.
Lemma R63X_nonneg X : 0 <= R63X X.
Proof.
  unfold R63X. apply zsum_map_nonneg. intros xb _. destruct (Z.leb_spec MMAP_THRESHOLD (snd xb)); [| lia].
  pose proof (round_up_pg_spec (snd xb + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT, PGSZ in *. lia.
Qed.
Lemma bigb_nonneg n : 0 <= bigb n.
Proof. unfold bigb. destruct (Z.leb_spec MMAP_THRESHOLD n); [| lia]. pose proof (round_up_pg_spec (n + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT, PGSZ in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LBUDGET : Z := 2 ^ 34.
(* [comment removed for export] *)
Definition live (mo : Model) : Z := vm_live_bytes (m_vmmaps mo).

(* [comment removed for export] *)
Definition QI (X : list (bptr * Z)) (P : Z -> Z) : assn PState := fun s mo =>
  (exists st L BL LS, strip st = ps_m s /\ INVL x0 st L BL LS /\ SINV x0 st BL /\ AQ st BL P
      /\ KL L (ps_brk s) mo /\ LI L mo /\ Permutation (map xs X) (map bs BL) /\ ld_live L = map bslot BL)
  /\ PHI P + R63X X <= LBUDGET.

Lemma QI_live X P s mo : QI X P s mo -> live mo <= LBUDGET.
Proof.
  intros [(st & L & BL & LS & _ & INV & SI & HAQ & HK & HL & HP & HLV) HB].
  pose proof (live_bound x0 st L BL LS P INV SI HAQ (ps_brk s) mo eq_refl HK HL) as LB.
  unfold ORPH in LB. cbn [x_orph x0] in LB. rewrite <- (R63X_eq X BL HP) in LB. unfold live, PGSZ in *. lia.
Qed.

Lemma QI_perm X Y P s mo : Permutation X Y -> QI X P s mo -> QI Y P s mo.
Proof.
  intros HXY [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP & HLV) HB]. split.
  - exists st, L, BL, LS. repeat (split; [assumption|]). split; [| exact HLV]. etransitivity; [| exact HP]. apply Permutation_map. apply Permutation_sym. exact HXY.
  - rewrite <- (zsum_map_perm _ _ _ HXY) || idtac. unfold R63X in *. rewrite (zsum_map_perm _ _ _ (Permutation_sym HXY)). exact HB.
Qed.

Lemma QI_fds X P s mo mo' : QI X P s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> m_vm_materialized mo' = [] -> QI X P s mo'.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP & HLV) HB] Hvm Hmi Hh Hmat. split; [| exact HB].
  exists st, L, BL, LS. repeat (split; [assumption|]). split; [| split; [| split; [exact HP| exact HLV]]].
  - destruct HK; constructor; try (rewrite Hvm); auto.
  - unfold LI in *. rewrite Hvm. exact HL.
Qed.

Lemma QI_minv X P s mo : QI X P s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(st & L & BL & LS & _ & _ & _ & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma QI_mat X P s mo : QI X P s mo -> m_vm_materialized mo = [].
Proof. intros [(st & L & BL & LS & _ & _ & _ & _ & HK & _) _]. exact (kl_mat _ _ _ HK). Qed.

Lemma QI_after_node X P s mo n rsp mo' evs :
  lazy_free_node n ->
  QI X P s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> QI X P s mo'.
Proof.
  intros Hlf HQ Hst Hvm. destruct (QI_minv _ _ _ _ HQ) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hlf Hmi Hh Hst) as [Hh' Hmi']. eapply QI_fds; eauto.
  exact (nstep_mat_nil _ _ _ _ _ Hst (QI_mat _ _ _ _ HQ)).
Qed.

(* [comment removed for export] *)
Lemma QI_other X P s s' mo : QI X P s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> QI X P s' mo.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP & HLV) HB] Hm Hb. split; [| exact HB].
  exists st, L, BL, LS. rewrite Hm, Hb. repeat (split; [assumption|]). exact HLV.
Qed.
Lemma QI_set_so X P s mo v : QI X P s mo -> QI X P (set_so_ps v s) mo.
Proof. intros H. eapply QI_other; [exact H| reflexivity| reflexivity]. Qed.
Lemma QI_set_fa X P s mo v : QI X P s mo -> QI X P (set_fa_ps v s) mo.
Proof. intros H. eapply QI_other; [exact H| reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma zsum_map_le' {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof. apply zsum_map_le. Qed.

Lemma CAP_mono P P' c : (forall c, P c <= P' c) -> CAP P c <= CAP P' c.
Proof.
  intros HP. unfold CAP, HOSTSTD.
  assert (zsum (map (fun c' => if bighost c' =? c then (CAP0 P c' + 32) / cmax c' else 0) guests)
          <= zsum (map (fun c' => if bighost c' =? c then (CAP0 P' c' + 32) / cmax c' else 0) guests)); [| assert (C0 : CAP0 P c <= CAP0 P' c) by (unfold CAP0; pose proof (HP 0); lia); lia].
  apply zsum_map_le. intros c' Hc'. destruct (bighost c' =? c); [| lia].
  assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia).
  pose proof (tab_basic_ok c' G) as (_ & CM & _). apply Z.div_le_mono; [lia|]. assert (C0 : CAP0 P c' <= CAP0 P' c') by (unfold CAP0; pose proof (HP 0); lia). lia.
Qed.
Lemma NCAP_mono P P' : (forall c, P c <= P' c) -> NCAP P <= NCAP P'.
Proof.
  intros HP. unfold NCAP, NG.
  assert (zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes) <= zsum (map (fun c => (CAP P' c + 32) / cmax c + 160) classes)); [| specialize (HP 63); lia].
  apply zsum_map_le. intros c Hc. apply In_classes in Hc. pose proof (tab_basic_ok c Hc) as (_ & CM & _).
  pose proof (CAP_mono P P' c HP). apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
Qed.
Lemma AQ_monoP st BL P P' : (forall c, P c <= P' c) -> AQ st BL P -> AQ st BL P'.
Proof.
  intros HP A. destruct A as [A1 A2 A3 A4 A5 A6]. constructor.
  - intros c Hc. specialize (A1 c Hc). specialize (HP c). lia.
  - intros c Hc. pose proof (CAP_mono P P' c HP). specialize (A2 c Hc). lia.
  - specialize (HP 63). lia.
  - pose proof (NCAP_mono P P' HP). lia.
  - intros c. specialize (A5 c). specialize (HP c). lia.
  - specialize (HP 0). lia.
Qed.
Lemma QI_monoP X P P' s mo : (forall c, P c <= P' c) -> PHI P' + R63X X <= LBUDGET -> QI X P s mo -> QI X P' s mo.
Proof.
  intros HP HB [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HPm) _]. split; [| exact HB].
  exists st, L, BL, LS. repeat (split; [assumption|]). split; [exact (AQ_monoP st BL P P' HP HAQ)|]. auto.
Qed.

Lemma QI_nodup X P s mo : QI X P s mo -> List.NoDup (map (fun xb => fst (fst xb)) X).
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP & HLV) _].
  pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND.
  assert (ND' : List.NoDup (map bslot BL)) by (apply NoDup_ListNoDup; exact ND).
  assert (E1 : map (fun xb : bptr * Z => fst (fst xb)) X = map fst (map xs X)) by (rewrite map_map; reflexivity).
  assert (E2 : map bslot BL = map fst (map bs BL)) by (rewrite map_map; reflexivity).
  rewrite E1. rewrite E2 in ND'. eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact HP| exact ND'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SINV_ctrl X st st1 BL : ctrl_eq st st1 -> SINV X st BL -> SINV X st1 BL.
Proof.
  intros CE S.
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (NC : ncarved st1 = ncarved st) by (unfold ncarved; rewrite (ce_metas _ _ CE); reflexivity).
  assert (AP : apages st1 = apages st).
  { unfold apages, regions_l, frontier. rewrite (ce_regions _ _ CE), (ce_ctx _ _ CE). reflexivity. }
  assert (SCL : forall s, slotcls st1 s = slotcls st s) by (intros s; unfold slotcls, cls; rewrite (ce_slots _ _ CE); destruct (s_slots st !! s) as [[? ?]|]; [rewrite MR1|]; reflexivity).
  assert (STD : forall x, stdg st1 x = stdg st x) by (intros x; unfold stdg, cls; rewrite !MR1; reflexivity).
  destruct S as [qb_cls qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor; rewrite ?(ce_slots _ _ CE), ?(ce_groups _ _ CE), ?(ce_metas _ _ CE), ?(ce_regions _ _ CE), ?(ce_ctx _ _ CE), ?NC, ?AP; auto.
  - intros k Hk. destruct (qb_cls k Hk) as (m0 & i0 & H0 & H1 & H2). exists m0, i0. rewrite !MR1. auto.
  - intros b m' ai Hg. rewrite !MR1. intros A1 A2. exact (qg_map _ _ _ Hg A1 A2).
  - intros b m' ai Hg. rewrite STD, !MR1. intros SG. destruct (qg_std _ _ _ Hg SG) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p' & i' & Hs' & E'). exists p', i'. rewrite (MR1 p'). auto.
  - intros c' Hc'. replace (nsc st1 c') with (nsc st c'); [apply qg_small; exact Hc'|].
    unfold nsc, gmetas, groups_l, cls. rewrite (ce_groups _ _ CE). apply zsum_map_ext. intros mb _. rewrite STD, MR1. reflexivity.
  - intros b m' ai Hg. rewrite !MR1. intros C63. exact (qg_63 _ _ _ Hg C63).
  - intros b m' ai p' i' Hg. rewrite !MR1. intros Z0 Hs'. exact (qg_host _ _ _ _ _ Hg Z0 Hs').
Qed.

Lemma bl_remove_perm k BL : In k BL -> List.NoDup (map bslot BL) ->
  Permutation (map bs BL) (bs k :: map bs (bl_remove (bslot k) BL)).
Proof.
  induction BL as [|k' BL IH]; intros Hin ND; [destruct Hin|]. cbn [map bl_remove].
  inversion ND as [|x l NI ND']; subst.
  destruct (aptr_eqb_spec (bslot k') (bslot k)) as [E|NE].
  - destruct Hin as [->|Hin]; [apply Permutation_refl|].
    exfalso. apply NI. rewrite E. apply in_map_iff. exists k. auto.
  - destruct Hin as [->|Hin]; [congruence|]. cbn [map]. etransitivity; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

Lemma INVL_nodup_slots X st L BL LS : INVL X st L BL LS -> List.NoDup (map bslot BL).
Proof. intros INV. apply NoDup_ListNoDup. exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

Definition GT : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_GT : frame_ok GT.
Proof. intros s s' mo mo' _ _ _ _. exact I. Qed.

Section RAWQ.
Hypothesis MQ : malloc_core_fq_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma free_simQ st L BL LS P c off n (o : unit) ans o' st' :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> In ((c, off), n) BL ->
  follow (prun pans0 pupd0 o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  SINV x0 st' (bl_remove c BL) /\ AQ st' (bl_remove c BL) P.
Proof.
  intros INV SI HAQ Hk Hf.
  pose proof (free_fq st L BL LS P c off n (PHI P + R63 BL) INV SI HAQ Hk ltac:(unfold PGSZ; lia)) as FQ.
  pose proof (ftree_prun pans0 pupd0 pans0_range _ L _ o (@fqtree_ftree _ _ _ _ _ _ FQ)) as PT.
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ (LS' & _ & S' & A')]. split; assumption.
Qed.

Theorem raw_free_L X P p n :
  mspec (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P).
Proof.
  unfold raw_free.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP & HLV) HB]].
  assert (Hin : In (fst p, n) (map bs BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n'] & Ebs & Hk). unfold bs in Ebs. cbn in Ebs.
  assert (Ec : c = fst p) by congruence. assert (En : n' = n) by congruence. subst n'.
  rewrite R63X_cons in HB. pose proof (bigb_nonneg n) as BBn.
  pose proof (R63X_eq _ _ HP) as R63E. rewrite R63X_cons in R63E.
  (* [comment removed for export] *)
  assert (QT : qtree LBUDGET L (cfree (ps_m s1) (Some (fst p))) (fun _ _ => True)).
  { rewrite <- E, <- Ec.
    eapply (qtree_of_full pans0 pupd0 pans0_range (RR := FREL)).
    - exact (free_fq st L BL LS P c off n LBUDGET INV SI HAQ Hk ltac:(unfold PGSZ; lia)).
    - exact (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)).
    - intros; exact I. }
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedL LBUDGET (cfree (ps_m s1) (Some (fst p))) (fun _ _ => True) GT L s1 frame_ok_GT QT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL| exact I]. }
  intros stc'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & CP & _ & HK' & HL' & _ & Hm & Hfa & Hso).
  apply mspec_upd'. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2).
  rewrite <- E, <- Ec in Hf, HL2.
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
  unfold FREL in SF. cbn in SF.
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (_ & _ & LIVE' & LS' & INV').
  destruct (free_simQ st L BL LS P c off n tt ans o' st' INV SI HAQ Hk FF) as [SI' HAQ'].
  rewrite HL2 in INV'.
  split; [| lia].
  exists st', (set_live (map bslot (bl_remove c BL)) L'), (bl_remove c BL), LS'. cbn [ps_m ps_brk set_m].
  split; [exact SF|]. split; [apply INVL_set_live; exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
  split; [apply KL_set_live; exact HK'|]. split; [unfold LI in *; rewrite gm_set_live, BB_set_live; exact HL'|]. split; [| reflexivity].
  pose proof (bl_remove_perm ((c, off), n) BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP. cbn [bs bslot bsize fst snd] in BP.
  apply (Permutation_cons_inv (l:=map xs X) (a:=bs ((c, off), n))). etransitivity; [| exact BP]. etransitivity; [| exact HP]. cbn [map xs fst snd]. unfold bs. cbn [bslot bsize fst snd]. rewrite Ec. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mallocK (n : Z) (x : mstate * option (aptr * Z)) : M (mstate * optr) :=
  let '(st1, r) := x in
  match r with
  | None => ret (st1, @None aptr)
  | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
  end.

Lemma malloc_unfold st n : malloc st n = sbind (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n) (mallocK n).
Proof. reflexivity. Qed.

Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st).
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Lemma malloc_fbnd8 st L BL LS P n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ -> fbnd8 B L (malloc st n).
Proof.
  intros INV SI HAQ Hn HR HB. rewrite malloc_unfold.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  eapply fbnd8_bind; [exact (MQ st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB)|].
  intros L1 [st1 [[g idx]|]] _; cbn [mallocK].
  - apply fbnd8_enframe_full. intros st' p. exact I.
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma malloc_simQ st L BL LS P n B (o : unit) ans o' st' r :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ ->
  follow (prun pans0 pupd0 o (malloc st n)) ans = Some (o', (st', r)) ->
  let t := cmalloc (strip st) n in
  let L' := lafter L t ans in
  exists rc, follow t ans = Some (strip st', rc) /\
    match r, rc with
    | None, None => (exists LS', INVL x0 st' L' BL LS') /\ SINV x0 st' BL /\ AQ st' BL P
    | Some pf, Some c => exists off LS', pf = aadd c (UNIT * off)
                         /\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ SINV x0 st' (((c, off), n) :: BL) /\ AQ st' (((c, off), n) :: BL) P
    | _, _ => False
    end.
Proof.
  intros INV SI HAQ Hn HR HB Hf. cbn zeta.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  assert (E1 : steq (prun pans0 pupd0 o (malloc st n)) (sbind (prun pans0 pupd0 o (malloc_core full_lay st0 n)) (fun x => prun pans0 pupd0 (fst x) (mallocK n (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].
  (* [comment removed for export] *)
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (@fqtree_ftree _ _ _ _ _ _ (MQ st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB))) as PTQ.
  pose proof (ptree_followk _ L _ ans PTQ FK) as CQ. unfold CORE_POSTQ in CQ. cbn [snd fst] in CQ.
  set (L1 := lafter L (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & CP).
  (* [comment removed for export] *)
  pose proof (malloc_core_ctrl pans0 pupd0 n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    specialize (CQ bg). fold c0 in CQ.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ ctrl_eq st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9; reflexivity| exact CE])).
    pose proof (ftree_prun pans0 pupd0 pans0_range _ L1 _ o1 EF) as PTE.
    cbn [mallocK fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Er & INV2 & SS2 & CE2)]. cbn [fst snd] in Er, INV2, SS2, CE2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    exists off, LS1. split; [reflexivity|]. split; [exact INV2|].
    destruct (CQ off Hg) as [S1 A1].
    split; [exact (SINV_ctrl x0 st1 st' _ CE2 S1)| exact (AQ_ctrl st1 st' _ P CE2 A1)].
  - destruct CP as (LS1 & INV1). cbn [mallocK fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity|].
    split; [exists LS1; exact INV1|]. exact CQ.
Qed.

Theorem raw_malloc_L X P n : 0 <= n ->
  mspec (fun s mo => QI X P s mo /\ ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => QI ((p, n) :: X) P s mo /\ n < 2 ^ 63
                        | None => QI X P s mo
                        end).
Proof.
  intros Hn. unfold raw_malloc.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> ([(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP & HLV) HB0] & HRX & HB)].
  pose proof (R63X_eq _ _ HP) as R63E. pose proof (ROOMX_eq X BL P n HP HRX) as HR.
  assert (HBB : PHI P + R63 BL + bigb n <= LBUDGET + 3 * PGSZ) by (unfold PGSZ; lia).
  (* [comment removed for export] *)
  assert (QT : qtree LBUDGET L (cmalloc (ps_m s1) n) (fun _ _ => True)).
  { rewrite <- E.
    eapply (qtree_of_full8 pans0 pupd0 pans0_range (RR := MREL)).
    - exact (malloc_INVL st L BL LS n INV Hn).
    - exact (malloc_fbnd8 st L BL LS P n LBUDGET INV SI HAQ Hn HR HBB).
    - exact (malloc_control pans0 pupd0 pans0_range st n tt).
    - intros; exact I. }
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedL LBUDGET (cmalloc (ps_m s1) n) (fun _ _ => True) GT L s1 frame_ok_GT QT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL| exact I]. }
  intros [stc' rc]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & CP & _ & HK' & HL' & _ & Hm & Hfa & Hso).
  eapply mspec_seq with (R := fun s mo => s = set_m stc' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2). rewrite <- E in Hf, HL2.
  pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
  destruct (malloc_simQ st L BL LS P n LBUDGET tt ans o' st' rf INV SI HAQ Hn HR HBB FF) as (rc2 & Hf2 & RES).
  rewrite Hf in Hf2. assert (Est : stc' = strip st') by congruence. assert (Erc : rc = rc2) by congruence. subst rc2.
  rewrite HL2 in RES.
  destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
  - destruct RES as (off & LS' & Epf & INV' & SI' & HAQ'). split.
    + split; [| rewrite R63X_cons; lia].
      exists st', (set_live (map bslot (((c, off), n) :: BL)) L'), (((c, off), n) :: BL), LS'. cbn [ps_m ps_brk set_m].
      split; [symmetry; exact Est|]. split; [apply INVL_set_live; exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
      split; [apply KL_set_live; exact HK'|]. split; [unfold LI in *; rewrite gm_set_live, BB_set_live; exact HL'|]. split; [| reflexivity].
      cbn [map xs bs fst snd]. unfold bs at 1. cbn [bslot bsize fst snd]. apply perm_skip. exact HP.
    + destruct (size_overflows n) eqn:Eov.
      * exfalso. rewrite (cmalloc_overflow _ _ Eov) in CP. inversion CP.
      * unfold size_overflows in Eov. apply Z.leb_gt in Eov. lia.
  - destruct RES as (INV' & SI' & HAQ'). split; [| lia].
    destruct INV' as [LS' INV'].
    exists st', (set_live (map bslot BL) L'), BL, LS'. cbn [ps_m ps_brk set_m].
    split; [symmetry; exact Est|]. split; [apply INVL_set_live; exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
    split; [apply KL_set_live; exact HK'|]. split; [unfold LI in *; rewrite gm_set_live, BB_set_live; exact HL'|]. split; [exact HP| reflexivity].
Qed.
End RAWQ.
End RC__1.

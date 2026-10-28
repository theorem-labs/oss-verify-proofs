(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit HxpGetState.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Model.
Context {ptr : Type}.
Implicit Types st : ap_st ptr.

(* [comment removed for export] *)
Definition ofree {A} (o : option ptr) (k : aprog ptr A) : aprog ptr A :=
  match o with Some q => AFree q k | None => k end.

(* [comment removed for export] *)
Definition ecd (i : nat) st : ap_st ptr :=
  if negb (Z.land (get_dflags i st) ERR_TXT_MALLOCED =? 0)
  then match get_data i st with Some _ => set_dflags i ERR_TXT_MALLOCED st | None => st end
  else set_dflags i 0 (set_data i None st).

Lemma err_clear_data_false_tree : forall i st, err_clear_data i false st = ARet (tt, ecd i st).
Proof.
  intros i st. unfold err_clear_data, ecd, abind, aget, amodify, aret. cbn [apbind fst snd].
  destruct (negb (Z.land (get_dflags i st) ERR_TXT_MALLOCED =? 0)); [|reflexivity].
  destruct (get_data i st); reflexivity.
Qed.

(* [comment removed for export] *)
Definition ecl_mid (i : nat) st : ap_st ptr := set_line i (-1) (set_buf i 0 (set_marks i 0 (ecd i st))).
Definition ecl_fin (i : nat) st : ap_st ptr := set_func i None (set_file i None (ecl_mid i st)).

Lemma apbind_ofree : forall {A B} (o : option ptr) (t : aprog ptr A) (k : A -> aprog ptr B),
  apbind (ofree o t) k = ofree o (apbind t k).
Proof. intros A B [q|] t k; reflexivity. Qed.

Lemma free_file_slot_tree : forall i st, free_file_slot i st = ofree (option_map fst (get_file i st)) (ARet (tt, set_file i None st)).
Proof.
  intros i st. unfold free_file_slot, abind, aget, afree_opt, afree, aret, amodify. cbn [apbind fst snd].
  destruct (get_file i st) as [[p n]|]; reflexivity.
Qed.
Lemma free_func_slot_tree : forall i st, free_func_slot i st = ofree (option_map fst (get_func i st)) (ARet (tt, set_func i None st)).
Proof.
  intros i st. unfold free_func_slot, abind, aget, afree_opt, afree, aret, amodify. cbn [apbind fst snd].
  destruct (get_func i st) as [[p n]|]; reflexivity.
Qed.

Lemma err_clear_false_tree : forall i st,
  err_clear i false st
  = ofree (option_map fst (get_file i (ecl_mid i st)))
      (ofree (option_map fst (get_func i (ecl_mid i st))) (ARet (tt, ecl_fin i st))).
Proof.
  intros i st. unfold err_clear, ecl_fin, ecl_mid. unfold abind. rewrite err_clear_data_false_tree. cbn [apbind fst snd].
  unfold amodify. cbn [apbind fst snd]. rewrite free_file_slot_tree, apbind_ofree. cbn [apbind fst snd].
  rewrite free_func_slot_tree. reflexivity.
Qed.

(* [comment removed for export] *)
Definition enew_top st : nat := ring_next (as_top st).
Definition enew_bot st : nat := if Nat.eqb (enew_top st) (as_bottom st) then ring_next (as_bottom st) else as_bottom st.
Definition enew_st1 st : ap_st ptr := set_bottom (enew_bot st) (set_top (enew_top st) st).

Lemma err_new_tree : forall st,
  err_new st = ofree (option_map fst (get_file (enew_top st) (ecl_mid (enew_top st) (enew_st1 st))))
                 (ofree (option_map fst (get_func (enew_top st) (ecl_mid (enew_top st) (enew_st1 st))))
                    (ARet (tt, ecl_fin (enew_top st) (enew_st1 st)))).
Proof.
  intros st. unfold err_new. unfold abind at 1. unfold aget. cbn [apbind fst snd]. unfold abind at 1. unfold amodify. cbn [apbind fst snd].
  rewrite err_clear_false_tree. reflexivity.
Qed.

(* [comment removed for export] *)
Definition eserr_fin (rs : rsite) st : ap_st ptr := set_buf (as_top st) (rs_code rs) (ecd (as_top st) st).
Lemma err_set_error_tree : forall rs st, err_set_error rs st = ARet (tt, eserr_fin rs st).
Proof.
  intros rs st. unfold err_set_error. unfold abind at 1. unfold aget. cbn [apbind fst snd]. unfold abind. rewrite err_clear_data_false_tree.
  cbn [apbind fst snd]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ecd_proj : forall i st,
  as_top (ecd i st) = as_top st /\ as_bottom (ecd i st) = as_bottom st /\ as_file (ecd i st) = as_file st /\ as_func (ecd i st) = as_func st
  /\ as_marks (ecd i st) = as_marks st /\ as_buf (ecd i st) = as_buf st /\ as_line (ecd i st) = as_line st /\ as_cnf (ecd i st) = as_cnf st.
Proof. intros i st. unfold ecd. destruct (negb _); [destruct (get_data i st)|]; repeat split; reflexivity. Qed.
End Model.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma NoDup_app_remove_l : forall {A} (l1 l2 l3 : list A), List.NoDup (l1 ++ l2 ++ l3) -> List.NoDup (l1 ++ l3).
Proof.
  intros A l1 l2 l3 H. induction l1 as [|x l1 IH]; cbn in *.
  - induction l2 as [|y l2 IH2]; cbn in *; [exact H|]. apply IH2. apply NoDup_cons_iff in H. tauto.
  - apply NoDup_cons_iff in H. destruct H as [Hx H]. constructor; [|apply IH; exact H].
    rewrite in_app_iff in *. intros [H1|H3]; apply Hx; rewrite in_app_iff; tauto.
Qed.

(* [comment removed for export] *)
Lemma ids_ok_perm : forall E (st st' : ap_st bptr),
  Permutation (st_blocks st') (st_blocks st) -> (as_top st' < ERR_NUM)%nat -> (as_bottom st' < ERR_NUM)%nat -> marks_sub st' st -> ids_ok E st -> ids_ok E st'.
Proof.
  intros E st st' HP T B MS (H & _ & _ & MK). unfold ids_ok, es_ids in *. split; [|split; [assumption|split; [assumption|eapply marks_ok_sub; [exact MS|exact MK]]]].
  eapply Permutation_NoDup; [|exact H].
  apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact HP.
Qed.

Lemma ids_ok_sub : forall E (st st' : ap_st bptr) pre,
  Permutation (pre ++ st_blocks st') (st_blocks st) -> (as_top st' < ERR_NUM)%nat -> (as_bottom st' < ERR_NUM)%nat -> marks_sub st' st -> ids_ok E st -> ids_ok E st'.
Proof.
  intros E st st' pre HP T B MS (H & _ & _ & MK). unfold ids_ok, es_ids in *. split; [|split; [assumption|split; [assumption|eapply marks_ok_sub; [exact MS|exact MK]]]].
  assert (H1 : List.NoDup (map fst pre ++ map fst (st_blocks st') ++ env_ids E)).
  { rewrite app_assoc, <- map_app. eapply Permutation_NoDup; [|exact H]. apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact HP. }
  exact (NoDup_app_remove_l [] (map fst pre) _ H1).
Qed.

Lemma ids_ok_same : forall E (st st' : ap_st bptr), st_blocks st' = st_blocks st -> (as_top st' < ERR_NUM)%nat -> (as_bottom st' < ERR_NUM)%nat ->
  marks_sub st' st -> ids_ok E st -> ids_ok E st'.
Proof.
  intros E st st' EQ T B MS (H & _ & _ & MK). unfold ids_ok, es_ids in *. rewrite EQ.
  split; [exact H|split; [assumption|split; [assumption|eapply marks_ok_sub; [exact MS|exact MK]]]].
Qed.

Lemma ids_ok_top : forall E (st : ap_st bptr), ids_ok E st -> (as_top st < ERR_NUM)%nat /\ (as_bottom st < ERR_NUM)%nat.
Proof. intros E st (_ & T & B & _). split; assumption. Qed.

(* [comment removed for export] *)
Lemma ids_ok0_perm : forall E (st st' : ap_st bptr),
  Permutation (st_blocks st') (st_blocks st) -> (as_top st' < ERR_NUM)%nat -> (as_bottom st' < ERR_NUM)%nat -> ids_ok0 E st -> ids_ok0 E st'.
Proof.
  intros E st st' HP T B (H & _ & _). unfold ids_ok0, es_ids in *. split; [|split; assumption]. eapply Permutation_NoDup; [|exact H].
  apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact HP.
Qed.
Lemma ids_ok0_sub : forall E (st st' : ap_st bptr) pre,
  Permutation (pre ++ st_blocks st') (st_blocks st) -> (as_top st' < ERR_NUM)%nat -> (as_bottom st' < ERR_NUM)%nat -> ids_ok0 E st -> ids_ok0 E st'.
Proof.
  intros E st st' pre HP T B (H & _ & _). unfold ids_ok0, es_ids in *. split; [|split; assumption].
  assert (H1 : List.NoDup (map fst pre ++ map fst (st_blocks st') ++ env_ids E)).
  { rewrite app_assoc, <- map_app. eapply Permutation_NoDup; [|exact H]. apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact HP. }
  exact (NoDup_app_remove_l [] (map fst pre) _ H1).
Qed.
Lemma ids_ok0_same : forall E (st st' : ap_st bptr), st_blocks st' = st_blocks st -> (as_top st' < ERR_NUM)%nat -> (as_bottom st' < ERR_NUM)%nat ->
  ids_ok0 E st -> ids_ok0 E st'.
Proof. intros E st st' EQ T B (H & _ & _). unfold ids_ok0, es_ids in *. rewrite EQ. split; [exact H|split; assumption]. Qed.

(* [comment removed for export] *)
Lemma marks_sub_ecd : forall i (st : ap_st bptr), marks_sub (ecd i st) st.
Proof. intros i st. apply marks_sub_eq. exact (proj1 (proj2 (proj2 (proj2 (proj2 (ecd_proj i st)))))). Qed.
Lemma marks_sub_ecl_fin : forall i (st : ap_st bptr), marks_sub (ecl_fin i st) st.
Proof.
  intros i st. apply (marks_sub_set0 _ _ i). unfold ecl_fin, ecl_mid. cbn [as_marks set_func set_file set_line set_buf set_marks].
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (ecd_proj i st)))))). reflexivity.
Qed.
Lemma marks_sub_eserr_fin : forall rs (st : ap_st bptr), marks_sub (eserr_fin rs st) st.
Proof. intros rs st. apply marks_sub_eq. unfold eserr_fin. cbn [as_marks set_buf]. exact (proj1 (proj2 (proj2 (proj2 (proj2 (ecd_proj _ st)))))). Qed.
Lemma marks_sub_enew_st1 : forall st : ap_st bptr, marks_sub (enew_st1 st) st.
Proof. intros st. apply marks_sub_eq. reflexivity. Qed.
Lemma marks_ok_set_marks : forall sg (st : ap_st bptr) i v, mark_ok sg v -> marks_ok sg st -> marks_ok sg (set_marks i v st).
Proof.
  intros sg st i v Hv H. unfold marks_ok in *. cbn [as_marks set_marks]. apply Forall_forall. intros k Hk.
  destruct (in_lset_or _ _ _ _ Hk) as [->|Hin]; [exact Hv|]. exact (proj1 (Forall_forall _ _) H k Hin).
Qed.

Lemma st_blocks_ecd : forall i (st : ap_st bptr), (i < length (as_data st))%nat ->
  Permutation (st_blocks (ecd i st)) (st_blocks st) \/ Permutation (optb (get_data i st) ++ st_blocks (ecd i st)) (st_blocks st).
Proof.
  intros i st Hi. unfold ecd. destruct (negb _).
  - destruct (get_data i st); [rewrite st_blocks_set_dflags|]; left; apply Permutation_refl.
  - right. rewrite st_blocks_set_dflags. pose proof (st_blocks_set_data i None st Hi) as P. cbn [optb app] in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma badr_cons : forall q A n OW p, badr ((q, A, n) :: OW) p = if bptr_eqb q p then A else badr OW p.
Proof. intros. reflexivity. Qed.

Lemma badr_remove_other : forall OW p q, p <> q -> badr (lb_remove q OW) p = badr OW p.
Proof.
  intros OW p q Hpq. induction OW as [|[[r A] n] OW IH]; [reflexivity|].
  rewrite lb_remove_cons. cbn [blk_id fst snd]. destruct (bptr_eqb r q) eqn:E.
  - cbn [badr blk_id blk_addr fst snd]. rewrite IH. apply bptr_eqb_eq in E. subst r. rewrite (bptr_eqb_neq q p ltac:(congruence)). reflexivity.
  - cbn [badr blk_id blk_addr fst snd]. rewrite IH. reflexivity.
Qed.

Lemma badr_in : forall OW p A n, List.NoDup (map blk_id OW) -> In (p, A, n) OW -> badr OW p = A.
Proof.
  induction OW as [|[[r A'] n'] OW IH]; intros p A n ND HIn; [destruct HIn|].
  cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  cbn [badr blk_id blk_addr fst snd]. destruct HIn as [E|HIn].
  - injection E as -> -> ->. rewrite bptr_eqb_refl. reflexivity.
  - destruct (bptr_eqb r p) eqn:E.
    + exfalso. apply bptr_eqb_eq in E. subst r. apply NI. change p with (blk_id (p, A, n)). apply in_map. exact HIn.
    + eapply IH; eassumption.
Qed.

(* [comment removed for export] *)
Lemma blk_bounds : forall s L m p A n, RHEAP s L m -> In (p, A, n) L ->
  0 < A /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x355000 <= A) /\ A mod 16 = 0.
Proof. intros s L m p A n HEAP HIn. pose proof (LH_block_range _ _ _ _ HEAP HIn) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd] in *. lia. Qed.

Lemma blk_disjoint : forall s L m p A n q A' n', RHEAP s L m -> In (p, A, n) L -> In (q, A', n') L -> p <> q ->
  A + n <= A' \/ A' + n' <= A.
Proof.
  intros s L m p A n q A' n' HEAP H1 H2 Hpq. pose proof (LH_disjoint _ _ _ _ _ HEAP H1 H2 ltac:(cbn; exact Hpq)) as D. cbn [blk_addr blk_size fst snd] in D. exact D.
Qed.

(* [comment removed for export] *)
Lemma optb_ok_nth : forall OW (l : list (option (bptr * Z))) i p n,
  Forall (optb_ok OW) l -> nth i l None = Some (p, n) -> In (p, badr OW p, n) OW /\ 0 < badr OW p.
Proof.
  intros OW l i p n HF Hn. assert (HIn : In (Some (p, n)) l) by (rewrite <- Hn; apply nth_In; destruct (Nat.lt_ge_cases i (length l)) as [L|L]; [exact L|]; rewrite (nth_overflow l None L) in Hn; discriminate).
  apply Forall_forall with (x := Some (p, n)) in HF; [|exact HIn]. exact HF.
Qed.

(* [comment removed for export] *)
Lemma fm_in : forall (l : list (option (bptr * Z))) i p n, nth i l None = Some (p, n) -> In (p, n) (fm l).
Proof.
  induction l as [|x l IH]; intros [|i] p n H; cbn in H; try discriminate.
  - subst x. cbn. left. reflexivity.
  - rewrite fm_cons. apply in_app_iff. right. eapply IH. exact H.
Qed.

Lemma es_ids_file : forall (st : ap_st bptr) i p n, get_file i st = Some (p, n) -> In p (es_ids st).
Proof. intros st i p n H. unfold es_ids, st_blocks. rewrite !map_app, !in_app_iff. left. change p with (fst (p, n)). apply in_map. eapply fm_in. exact H. Qed.
Lemma es_ids_func : forall (st : ap_st bptr) i p n, get_func i st = Some (p, n) -> In p (es_ids st).
Proof. intros st i p n H. unfold es_ids, st_blocks. rewrite !map_app, !in_app_iff. right; left. change p with (fst (p, n)). apply in_map. eapply fm_in. exact H. Qed.
Lemma es_ids_data : forall (st : ap_st bptr) i p n, get_data i st = Some (p, n) -> In p (es_ids st).
Proof. intros st i p n H. unfold es_ids, st_blocks. rewrite !map_app, !in_app_iff. right; right; left. change p with (fst (p, n)). apply in_map. eapply fm_in. exact H. Qed.

(* [comment removed for export] *)
Lemma ids_ok_not_env : forall E (st : ap_st bptr) p, ids_ok E st -> In p (es_ids st) -> ~ In p (env_ids E).
Proof.
  intros E st p (H & _ & _) Hp He. induction (es_ids st) as [|x l IH]; [destruct Hp|].
  cbn in H. apply NoDup_cons_iff in H. destruct H as [Hx H]. destruct Hp as [->|Hp]; [apply Hx; apply in_app_iff; right; exact He|]. apply IH; assumption.
Qed.

Lemma env_ids_unfold : forall E, env_ids E = [p_es E; p_mk E; p_sa E; p_nd E; p_xl E].
Proof. intros. reflexivity. Qed.

End WithCeiling0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record esg : Type := mkG { g_fl : list word; g_ma : list word; g_bu : list word; g_da : list word; g_ds : list word; g_df : list word; g_fi : list word; g_li : list word; g_fu : list word; g_top : Z; g_bot : Z }.
Definition set_g_fl (l : list word) (g : esg) : esg := mkG l (g_ma g) (g_bu g) (g_da g) (g_ds g) (g_df g) (g_fi g) (g_li g) (g_fu g) (g_top g) (g_bot g).
Definition set_g_ma (l : list word) (g : esg) : esg := mkG (g_fl g) l (g_bu g) (g_da g) (g_ds g) (g_df g) (g_fi g) (g_li g) (g_fu g) (g_top g) (g_bot g).
Definition set_g_bu (l : list word) (g : esg) : esg := mkG (g_fl g) (g_ma g) l (g_da g) (g_ds g) (g_df g) (g_fi g) (g_li g) (g_fu g) (g_top g) (g_bot g).
Definition set_g_da (l : list word) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) l (g_ds g) (g_df g) (g_fi g) (g_li g) (g_fu g) (g_top g) (g_bot g).
Definition set_g_ds (l : list word) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) (g_da g) l (g_df g) (g_fi g) (g_li g) (g_fu g) (g_top g) (g_bot g).
Definition set_g_df (l : list word) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) (g_da g) (g_ds g) l (g_fi g) (g_li g) (g_fu g) (g_top g) (g_bot g).
Definition set_g_fi (l : list word) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) (g_da g) (g_ds g) (g_df g) l (g_li g) (g_fu g) (g_top g) (g_bot g).
Definition set_g_li (l : list word) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) (g_da g) (g_ds g) (g_df g) (g_fi g) l (g_fu g) (g_top g) (g_bot g).
Definition set_g_fu (l : list word) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) (g_da g) (g_ds g) (g_df g) (g_fi g) (g_li g) l (g_top g) (g_bot g).
Definition set_g_top (t : Z) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) (g_da g) (g_ds g) (g_df g) (g_fi g) (g_li g) (g_fu g) t (g_bot g).
Definition set_g_bot (b : Z) (g : esg) : esg := mkG (g_fl g) (g_ma g) (g_bu g) (g_da g) (g_ds g) (g_df g) (g_fi g) (g_li g) (g_fu g) (g_top g) b.

Section EsRaw. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition es_raw (m : mem) (A : Z) (g : esg) : Prop :=
  u32arr ctusegs m (A + ESO_FLAGS) (g_fl g)
  /\ u32arr ctusegs m (A + ESO_MARKS) (g_ma g)
  /\ u64arr ctusegs m (A + ESO_BUFFER) (g_bu g)
  /\ u64arr ctusegs m (A + ESO_DATA) (g_da g)
  /\ u64arr ctusegs m (A + ESO_DSIZE) (g_ds g)
  /\ u32arr ctusegs m (A + ESO_DFLAGS) (g_df g)
  /\ u64arr ctusegs m (A + ESO_FILE) (g_fi g)
  /\ u32arr ctusegs m (A + ESO_LINE) (g_li g)
  /\ u64arr ctusegs m (A + ESO_FUNC) (g_fu g)
  /\ rw_cells ctusegs m (A + ESO_TOP) [C4 (wz (g_top g)); C4 (wz (g_bot g))].
Definition g_len (g : esg) : Prop := length (g_fl g) = ERR_NUM /\ length (g_ma g) = ERR_NUM /\ length (g_bu g) = ERR_NUM /\ length (g_da g) = ERR_NUM /\ length (g_ds g) = ERR_NUM /\ length (g_df g) = ERR_NUM /\ length (g_fi g) = ERR_NUM /\ length (g_li g) = ERR_NUM /\ length (g_fu g) = ERR_NUM.
Definition g_of (st : ap_st bptr) (adr : bptr -> Z) : esg :=
  mkG (wl (repeat 0 ERR_NUM)) (wl (as_marks st)) (wl (as_buf st)) (wl (map (optr adr) (as_data st))) (wl (map osize (as_data st)))
      (wl (as_dflags st)) (wl (map (optr adr) (as_file st))) (wl (as_line st)) (wl (map (optr adr) (as_func st)))
      (Z.of_nat (as_top st)) (Z.of_nat (as_bottom st)).

Lemma es_at_raw : forall m A st adr, es_at m A st adr <-> es_raw m A (g_of st adr).
Proof. intros. unfold es_at, es_raw, g_of. cbn -[u32arr u64arr rw_cells wl Z.add map optr osize repeat ERR_NUM Z.of_nat]. tauto. Qed.

Lemma g_len_of : forall st adr, es_shape st -> g_len (g_of st adr).
Proof.
  intros st adr (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold g_len, g_of. cbn -[wl map repeat ERR_NUM length].
  unfold wl. rewrite !length_map, ?repeat_length. repeat split; first [assumption | reflexivity].
Qed.

Local Ltac eso := unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ERR_NUM in *.

(* [comment removed for export] *)
Lemma nth_error_wl : forall l i d, (i < length l)%nat -> nth_error (wl l) i = Some (wz (nth i l d)).
Proof. intros l i d Hi. unfold wl. rewrite nth_error_map. rewrite (nth_error_nth' l d Hi). reflexivity. Qed.
Lemma nth_error_len : forall (l : list word) i, (i < length l)%nat -> exists w, nth_error l i = Some w /\ nth i l (wz 0) = w.
Proof. intros l i Hi. exists (nth i l (wz 0)). split; [apply nth_error_nth'; exact Hi|reflexivity]. Qed.

Lemma es_raw_bound : forall m A g, es_raw m A g -> 0 <= A /\ A + 904 <= 2^64.
Proof.
  intros m A g H. destruct H as (Hfl & _ & _ & _ & _ & _ & _ & _ & _ & HT). pose proof (rw_cells_bound _ _ _ _ HT) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (u32arr_bound _ _ _ _ Hfl) as B0. eso. lia.
Qed.

Lemma es_rd_fl : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_FLAGS + 4 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 4 = Some (le4 (nth i (g_fl g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_fl g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_FLAGS) (g_fl g) (Z.of_nat i)); [exact Hfl | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_ma : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_MARKS + 4 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 4 = Some (le4 (nth i (g_ma g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_ma g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_MARKS) (g_ma g) (Z.of_nat i)); [exact Hma | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_bu : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_BUFFER + 8 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 8 = Some (le8 (nth i (g_bu g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_bu g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_BUFFER) (g_bu g) (Z.of_nat i)); [exact Hbu | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_da : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DATA + 8 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 8 = Some (le8 (nth i (g_da g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_da g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_DATA) (g_da g) (Z.of_nat i)); [exact Hda | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_ds : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DSIZE + 8 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 8 = Some (le8 (nth i (g_ds g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_ds g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_DSIZE) (g_ds g) (Z.of_nat i)); [exact Hds | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_df : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DFLAGS + 4 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 4 = Some (le4 (nth i (g_df g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_df g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_DFLAGS) (g_df g) (Z.of_nat i)); [exact Hdf | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_fi : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_FILE + 8 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 8 = Some (le8 (nth i (g_fi g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_fi g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_FILE) (g_fi g) (Z.of_nat i)); [exact Hfi | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_li : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_LINE + 4 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 4 = Some (le4 (nth i (g_li g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_li g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_LINE) (g_li g) (Z.of_nat i)); [exact Hli | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_fu : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_FUNC + 8 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 8 = Some (le8 (nth i (g_fu g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_fu g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_FUNC) (g_fu g) (Z.of_nat i)); [exact Hfu | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_top : forall m A g a, es_raw m A g -> a = wa (A + 896) -> ov_read_bytes ctusegs m a 4 = Some (le4 (wz (g_top g))).
Proof.
  intros m A g a H ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). eso.
  apply (rw_cells_read_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 0%nat (C4 (wz (g_top g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia].
Qed.
Lemma es_rd_bot : forall m A g a, es_raw m A g -> a = wa (A + 900) -> ov_read_bytes ctusegs m a 4 = Some (le4 (wz (g_bot g))).
Proof.
  intros m A g a H ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). eso.
  apply (rw_cells_read_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 4%nat (C4 (wz (g_bot g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia].
Qed.

Lemma es_wr_fl : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_FLAGS + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_FLAGS + 4 * Z.of_nat i)) (le4 v)) A (set_g_fl (upd (g_fl g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_FLAGS) (g_fl g) (Z.of_nat i)); [exact Hfl | lia | reflexivity]. }
  unfold es_raw, set_g_fl. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_FLAGS) (g_fl g) (Z.of_nat i) v Hfl ltac:(lia)). }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_ma : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_MARKS + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_MARKS + 4 * Z.of_nat i)) (le4 v)) A (set_g_ma (upd (g_ma g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_MARKS) (g_ma g) (Z.of_nat i)); [exact Hma | lia | reflexivity]. }
  unfold es_raw, set_g_ma. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_MARKS) (g_ma g) (Z.of_nat i) v Hma ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_bu : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_BUFFER + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_BUFFER + 8 * Z.of_nat i)) (le8 v)) A (set_g_bu (upd (g_bu g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_BUFFER) (g_bu g) (Z.of_nat i)); [exact Hbu | lia | reflexivity]. }
  unfold es_raw, set_g_bu. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_BUFFER) (g_bu g) (Z.of_nat i) v Hbu ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_da : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_DATA + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_DATA + 8 * Z.of_nat i)) (le8 v)) A (set_g_da (upd (g_da g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_DATA) (g_da g) (Z.of_nat i)); [exact Hda | lia | reflexivity]. }
  unfold es_raw, set_g_da. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_DATA) (g_da g) (Z.of_nat i) v Hda ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_ds : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_DSIZE + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_DSIZE + 8 * Z.of_nat i)) (le8 v)) A (set_g_ds (upd (g_ds g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_DSIZE) (g_ds g) (Z.of_nat i)); [exact Hds | lia | reflexivity]. }
  unfold es_raw, set_g_ds. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_DSIZE) (g_ds g) (Z.of_nat i) v Hds ltac:(lia)). }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_df : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_DFLAGS + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_DFLAGS + 4 * Z.of_nat i)) (le4 v)) A (set_g_df (upd (g_df g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_DFLAGS) (g_df g) (Z.of_nat i)); [exact Hdf | lia | reflexivity]. }
  unfold es_raw, set_g_df. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_DFLAGS) (g_df g) (Z.of_nat i) v Hdf ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_fi : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_FILE + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_FILE + 8 * Z.of_nat i)) (le8 v)) A (set_g_fi (upd (g_fi g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_FILE) (g_fi g) (Z.of_nat i)); [exact Hfi | lia | reflexivity]. }
  unfold es_raw, set_g_fi. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_FILE) (g_fi g) (Z.of_nat i) v Hfi ltac:(lia)). }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_li : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_LINE + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_LINE + 4 * Z.of_nat i)) (le4 v)) A (set_g_li (upd (g_li g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_LINE) (g_li g) (Z.of_nat i)); [exact Hli | lia | reflexivity]. }
  unfold es_raw, set_g_li. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_LINE) (g_li g) (Z.of_nat i) v Hli ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_fu : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctusegs m (wa (A + ESO_FUNC + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_FUNC + 8 * Z.of_nat i)) (le8 v)) A (set_g_fu (upd (g_fu g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_FUNC) (g_fu g) (Z.of_nat i)); [exact Hfu | lia | reflexivity]. }
  unfold es_raw, set_g_fu. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_FUNC) (g_fu g) (Z.of_nat i) v Hfu ltac:(lia)). }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_top : forall m A g (t : Z), es_raw m A g -> g_len g ->
  store_ok ctusegs m (wa (A + 896)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + 896)) (le4 (wz t))) A (set_g_top t g).
Proof.
  intros m A g t H HL. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { apply (rw_cells_store_ok_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 0%nat (C4 (wz (g_top g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia]. }
  unfold es_raw, set_g_top. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  pose proof (rw_cells_write _ m (A + 896) _ 0%nat _ (C4 (wz t)) HT eq_refl eq_refl I) as W. cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in W.
  replace (A + 896 + Z.of_nat 0) with (A + 896) in W by lia. exact W.
Qed.

Lemma es_wr_bot : forall m A g (t : Z), es_raw m A g -> g_len g ->
  store_ok ctusegs m (wa (A + 900)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + 900)) (le4 (wz t))) A (set_g_bot t g).
Proof.
  intros m A g t H HL. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { apply (rw_cells_store_ok_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 4%nat (C4 (wz (g_bot g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia]. }
  unfold es_raw, set_g_bot. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  pose proof (rw_cells_write _ m (A + 896) _ 4%nat _ (C4 (wz t)) HT eq_refl eq_refl I) as W. cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in W.
  replace (A + 896 + Z.of_nat 4) with (A + 900) in W by lia. exact W.
Qed.

Lemma es_raw_transport : forall W m m' A g, es_raw m A g -> g_len g -> munch W m m' -> wmono ctusegs m m' ->
  disjoint_from W A 904 -> es_raw m' A g.
Proof.
  intros W m m' A g H HL MU WM HD. unfold es_raw in *. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  assert (D : forall a n, A <= a -> a + n <= A + 904 -> disjoint_from W a n).
  { intros a n Ha Hn. clear - HD Ha Hn. induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct HD as [HD1 HD2]. split; [lia | apply IH; exact HD2]. }
  split. { eapply u32arr_transport; [exact Hfl | exact MU | exact WM | apply D; lia]. }
  split. { eapply u32arr_transport; [exact Hma | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hbu | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hda | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hds | exact MU | exact WM | apply D; lia]. }
  split. { eapply u32arr_transport; [exact Hdf | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hfi | exact MU | exact WM | apply D; lia]. }
  split. { eapply u32arr_transport; [exact Hli | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hfu | exact MU | exact WM | apply D; lia]. }
  eapply rw_cells_transport; [exact HT | exact MU | exact WM | apply D; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_raw_agree : forall P m m' A g, es_raw m A g -> g_len g -> agree_on P m m' -> (forall a, A <= a < A + 904 -> P a) -> es_raw m' A g.
Proof.
  intros P m m' A g H HL AG HP. unfold es_raw in *. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply u32arr_agree; [exact AG | exact Hfl | intros a Ha; apply HP; lia]. }
  split. { eapply u32arr_agree; [exact AG | exact Hma | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hbu | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hda | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hds | intros a Ha; apply HP; lia]. }
  split. { eapply u32arr_agree; [exact AG | exact Hdf | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hfi | intros a Ha; apply HP; lia]. }
  split. { eapply u32arr_agree; [exact AG | exact Hli | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hfu | intros a Ha; apply HP; lia]. }
  eapply rw_cells_agree; [exact AG | exact HT | intros a Ha; apply HP; cbn [cells_size csize Nat.add] in Ha; lia].
Qed.

End EsRaw.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rest. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ap_rest (m : mem) (OW : list block) (E : ap_env) (bo : Z * Z) (cnf : option (bptr * bptr * bptr)) : Prop :=
  ap_env_ok E OW /\ ap_img m /\ ap_statics_fixed m E /\ ap_statics_cnf m OW (e_stage E) cnf /\ tl_chain m E /\ exlock_free m E
  /\ bio_out_rep m E (fst bo) (snd bo).

Lemma ap_state_split : forall st m OW E bo, ap_state st m OW E bo <-> ap_rest m OW E bo (as_cnf st) /\ err_rep m E OW st.
Proof. intros. unfold ap_state, ap_rest. tauto. Qed.

(* [comment removed for export] *)
Definition cnf_rblocks (OW : list block) (cnf : option (bptr * bptr * bptr)) : list block :=
  match cnf with
  | Some (lk, lh, bk) => [(lk, badr OW lk, SZ_OBJ_LOCK); (lh, badr OW lh, SZ_ADDED); (bk, badr OW bk, SZ_ADDED_BUCKETS)]
  | None => []
  end.
Definition rest_blocks (OW : list block) (E : ap_env) (cnf : option (bptr * bptr * bptr)) : list block :=
  [(p_mk E, e_mk E, 72); (p_sa E, e_sa E, 32); (p_nd E, e_nd E, 128); (p_xl E, e_xl E, MUTEX_SIZE)]
  ++ cnf_rblocks OW cnf.

Lemma rest_blocks_OW : forall m OW E bo cnf b, ap_rest m OW E bo cnf -> In b (rest_blocks OW E cnf) -> In b OW.
Proof.
  intros m OW E bo cnf b (HE & _ & _ & HC & _) Hb. destruct (env_in E OW HE) as (IES & IMK & ISA & IND & IXL).
  unfold rest_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
  - cbn [In] in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption.
  - destruct cnf as [[[lk lh] bk]|]; cbn [cnf_rblocks In] in Hb; [|destruct Hb].
    cbn [ap_statics_cnf] in HC. destruct HC as (_ & _ & _ & _ & _ & _ & I1 & I2 & I3 & _).
    destruct Hb as [<-|[<-|[<-|[]]]]; assumption.
Qed.

Lemma rest_ids : forall OW E cnf,
  map blk_id (rest_blocks OW E cnf) = [p_mk E; p_sa E; p_nd E; p_xl E] ++ map fst (cnf_blocks cnf).
Proof. intros OW E [[[lk lh] bk]|]; reflexivity. Qed.

Local Ltac static_iv lo hi :=
  intros a Ha; apply (lib_addr_static _ a lo hi); [unfold LIBW_HX; cbn; tauto|];
  cbn [cells_size csize cells_size Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
  unfold TL_MASTER_ONCE8, TL_MASTER_KEY8, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE2, AP_DC_EXLOCK, AP_DC_EXMETH_BIO, AP_DC_CONF_DIAG,
    OI_STOPPED, OI_BASE_ONCE, OI_OPTSDONE, AP_IN_INIT_KEY, AP_OPTSDONE_LOCK, TCB_TSD, AP_TSD_DC_SLOT, TSD_MK_SLOT, AP_TSD_USED, AP_TSD_INIT_SLOT,
    CR_GOT_MALLOC, CR_GOT_FREE, CR_MEMSET_FUNC, CR_MALLOC_IMPL, CR_REALLOC_IMPL, CR_FREE_IMPL, CR_NO_CUSTOMIZE, AP_CONFIG_ONCE, AP_OBJ_ONCE, AP_OBJ_LOCK,
    AP_OBJ_ADDED, AP_CONF_METH, AP_CANCELBUF, OI_BASE_INITED, OI_DO_CLEANUP, AP_OPENSSL_CONFIGURED in Ha; lia.
Local Ltac block_iv HIn :=
  intros a Ha; eapply lib_addr_block; [exact HIn|];
  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ length repeat c8s c4s zeros4 map mutex_free_cells sa_cells bio_null_cells bio_cells lhash_cells] in Ha;
  unfold BIO_SIZE, ES_SIZE, MUTEX_SIZE, SZ_OBJ_LOCK, SZ_ADDED, SZ_ADDED_BUCKETS, OFF_MK_SA in *; lia.

Lemma lib_addr_nil : forall RB a, lib_addr [] a -> lib_addr RB a.
Proof. intros RB a [H|(b & Hb & _)]; [left; exact H|destruct Hb]. Qed.

Theorem rest_agree : forall m m' OW E bo cnf,
  ap_rest m OW E bo cnf -> agree_on (lib_addr (rest_blocks OW E cnf)) m m' -> ap_rest m' OW E bo cnf.
Proof.
  intros m m' OW E bo cnf (HE & HI & HS & HC & HT & HX & HB) AG.
  assert (AG0 : agree_on (lib_addr []) m m') by (eapply agree_on_mono; [exact AG|apply lib_addr_nil]).
  assert (RB : forall b, In b [(p_mk E, e_mk E, 72); (p_sa E, e_sa E, 32); (p_nd E, e_nd E, 128); (p_xl E, e_xl E, MUTEX_SIZE)] ->
               In b (rest_blocks OW E cnf)) by (intros b Hb; unfold rest_blocks; apply in_app_iff; left; exact Hb).
  split; [exact HE|]. split; [eapply (ap_img_agree []); [exact HI|exact AG0]|]. split; [eapply (ap_statics_fixed_agree []); [exact HS|exact AG0]|].
  split.
  { destruct cnf as [[[lk lh] bk]|]; cbn [ap_statics_cnf] in *.
    - destruct HC as (S1 & S2 & S3 & S4 & S5 & S6 & I1 & I2 & I3 & M1 & M2 & M3).
      assert (J1 : In (lk, badr OW lk, SZ_OBJ_LOCK) (rest_blocks OW E (Some (lk, lh, bk)))) by (unfold rest_blocks; apply in_app_iff; right; cbn; tauto).
      assert (J2 : In (lh, badr OW lh, SZ_ADDED) (rest_blocks OW E (Some (lk, lh, bk)))) by (unfold rest_blocks; apply in_app_iff; right; cbn; tauto).
      assert (J3 : In (bk, badr OW bk, SZ_ADDED_BUCKETS) (rest_blocks OW E (Some (lk, lh, bk)))) by (unfold rest_blocks; apply in_app_iff; right; cbn; tauto).
      split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S5|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0x354150 0x3545b0|].
      split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
      split; [eapply rw_cells_agree; [exact AG|exact M1|]; block_iv J1|].
      split; [eapply rw_cells_agree; [exact AG|exact M2|]; block_iv J2|].
      eapply rw_cells_agree; [exact AG|exact M3|]; block_iv J3.
    - destruct HC as (S1 & S2 & S3 & S4 & S5 & S6).
      split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0x3306d0 0x333158|].
      split; [eapply rw_cells_agree; [exact AG|exact S5|]; static_iv 0x3306d0 0x333158|].
      eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0x354150 0x3545b0. }
  assert (IMK : In (p_mk E, e_mk E, 72) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  assert (ISA : In (p_sa E, e_sa E, 32) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  assert (IND : In (p_nd E, e_nd E, 128) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  assert (IXL : In (p_xl E, e_xl E, MUTEX_SIZE) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  split.
  { destruct HT as (T1 & (pad & T2) & T3).
    split; [eapply ro_cells_agree; [exact AG|exact T1|]; block_iv IMK|].
    split; [exists pad; eapply ro_cells_agree; [exact AG|exact T2|]; block_iv ISA|].
    eapply ro_cells_agree; [exact AG|exact T3|]; block_iv IND. }
  split; [eapply rw_cells_agree; [exact AG|exact HX|]; block_iv IXL|].
  exact I.
Qed.

Lemma rest_of_munch : forall W m m' OW E bo cnf,
  ap_rest m OW E bo cnf -> munch W m m' -> wmono ctusegs m m' ->
  (forall a, lib_addr (rest_blocks OW E cnf) a -> outside W a) -> ap_rest m' OW E bo cnf.
Proof.
  intros W m m' OW E bo cnf HR MU WM HW. eapply rest_agree; [exact HR|].
  eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. exact HW.
Qed.

Lemma rest_of_heap_pres : forall L SP m m' OW E bo cnf,
  ap_rest m OW E bo cnf -> rheap_pres L SP m m' -> (forall b, In b (rest_blocks OW E cnf) -> In b L) -> ap_rest m' OW E bo cnf.
Proof.
  intros L SP m m' OW E bo cnf HR HP HL. eapply rest_agree; [exact HR|].
  intros a Ha Hl. apply (HP a Ha). eapply lib_addr_rclient; [exact HL|exact Hl].
Qed.

(* [comment removed for export] *)
Lemma rest_addr_cases : forall OW E cnf a,
  lib_addr (rest_blocks OW E cnf) a ->
  (0x2c2e98 <= a < 0x355000) \/ (exists b, In b (rest_blocks OW E cnf) /\ blk_addr b <= a < blk_addr b + blk_size b).
Proof.
  intros OW E cnf a [H|(b & Hb & Hr)]; [left|right; exists b; auto].
  unfold LIBW_HX in H. cbn [rin_ivs fst snd] in H. lia.
Qed.

Lemma rest_outside_stack : forall s L m OW E bo cnf lo x y a,
  ap_rest m OW E bo cnf -> RHEAP s L m -> (forall b, In b OW -> In b L) ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= x ->
  lib_addr (rest_blocks OW E cnf) a -> ~ (x <= a < y).
Proof.
  intros s L m OW E bo cnf lo x y a HR HEAP HL CEIL GLO Hx Ha.
  destruct (rest_addr_cases _ _ _ _ Ha) as [Hs|([[p A] n] & Hb & Hr)]; [unfold GLOBALS_TOP in GLO; lia|].
  cbn [blk_addr blk_size fst snd] in Hr.
  pose proof (blk_bounds s L m p A n HEAP (HL _ (rest_blocks_OW _ _ _ _ _ _ HR Hb))) as (B1 & B2 & B3 & B4 & B5). lia.
Qed.

Lemma rest_outside_block : forall s L m OW E bo cnf p0 A0 n0 a,
  ap_rest m OW E bo cnf -> RHEAP s L m -> (forall b, In b OW -> In b L) ->
  In (p0, A0, n0) L -> ~ In p0 (map blk_id (rest_blocks OW E cnf)) ->
  lib_addr (rest_blocks OW E cnf) a -> ~ (A0 <= a < A0 + n0).
Proof.
  intros s L m OW E bo cnf p0 A0 n0 a HR HEAP HL H0 Hni Ha.
  pose proof (blk_bounds s L m p0 A0 n0 HEAP H0) as (B1 & B2 & B3 & B4 & B5).
  destruct (rest_addr_cases _ _ _ _ Ha) as [Hs|([[p A] n] & Hb & Hr)]; [lia|].
  cbn [blk_addr blk_size fst snd] in Hr.
  assert (Hp : p0 <> p) by (intros ->; apply Hni; change p with (blk_id (p, A, n)); apply in_map; exact Hb).
  pose proof (blk_disjoint s L m p0 A0 n0 p A n HEAP H0 (HL _ (rest_blocks_OW _ _ _ _ _ _ HR Hb)) Hp) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma NoDup_app_disjoint : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H1; [destruct H1|]. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [Hy ND].
  destruct H1 as [->|H1]; [intros H2; apply Hy; apply in_app_iff; right; exact H2|]. apply IH; assumption.
Qed.

Lemma cnf_ids_in_es_ids : forall (st : ap_st bptr) q, In q (map fst (cnf_blocks (as_cnf st))) -> In q (es_ids st).
Proof. intros st q H. unfold es_ids, st_blocks. rewrite !map_app, !in_app_iff. right; right; right. exact H. Qed.

Lemma es_not_rest : forall st m OW E bo, ap_state st m OW E bo -> ids_ok E st -> ~ In (p_es E) (map blk_id (rest_blocks OW E (as_cnf st))).
Proof.
  intros st m OW E bo AS IDS H. rewrite rest_ids in H. apply in_app_iff in H.
  pose proof (env_ids_nodup _ _ _ _ _ AS) as ND. rewrite env_ids_unfold in ND.
  destruct H as [H|H].
  - cbn [In] in H.
    repeat match goal with H : List.NoDup (_ :: _) |- _ => apply NoDup_cons_iff in H; destruct H as [? H] end.
    cbn [In] in *. intuition congruence.
  - apply cnf_ids_in_es_ids in H. destruct IDS as (IDS & _ & _).
    exact (NoDup_app_disjoint _ _ _ IDS H ltac:(rewrite env_ids_unfold; cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma ffd_not_rest : forall (st : ap_st bptr) E OW p,
  ids_ok E st -> In p (map fst (fm (as_file st) ++ fm (as_func st) ++ fm (as_data st))) ->
  ~ In p (map blk_id (rest_blocks OW E (as_cnf st))).
Proof.
  intros st E OW p (IDS & _ & _) Hp H. rewrite rest_ids in H.
  unfold es_ids, st_blocks in IDS. rewrite !map_app in IDS. rewrite !map_app in Hp.
  set (a := map fst (fm (as_file st))) in *. set (b := map fst (fm (as_func st))) in *. set (c := map fst (fm (as_data st))) in *.
  set (d := map fst (cnf_blocks (as_cnf st))) in *. set (e := env_ids E) in *.
  assert (EQ : (a ++ b ++ c ++ d) ++ e = (a ++ b ++ c) ++ (d ++ e)) by (rewrite <- !app_assoc; reflexivity).
  rewrite EQ in IDS. pose proof (NoDup_app_disjoint _ _ _ IDS Hp) as NI. apply NI. apply in_app_iff.
  apply in_app_iff in H. destruct H as [H|H]; [right|left; exact H].
  subst e. rewrite env_ids_unfold. cbn [In] in *. tauto.
Qed.

Lemma data_not_rest : forall (st : ap_st bptr) E OW i p n, ids_ok E st -> get_data i st = Some (p, n) -> ~ In p (map blk_id (rest_blocks OW E (as_cnf st))).
Proof. intros st E OW i p n IDS H. eapply ffd_not_rest; [exact IDS|]. rewrite !map_app, !in_app_iff. right; right. change p with (fst (p, n)). apply in_map. eapply fm_in. exact H. Qed.
Lemma file_not_rest : forall (st : ap_st bptr) E OW i p n, ids_ok E st -> get_file i st = Some (p, n) -> ~ In p (map blk_id (rest_blocks OW E (as_cnf st))).
Proof. intros st E OW i p n IDS H. eapply ffd_not_rest; [exact IDS|]. rewrite !map_app, !in_app_iff. left. change p with (fst (p, n)). apply in_map. eapply fm_in. exact H. Qed.
Lemma func_not_rest : forall (st : ap_st bptr) E OW i p n, ids_ok E st -> get_func i st = Some (p, n) -> ~ In p (map blk_id (rest_blocks OW E (as_cnf st))).
Proof. intros st E OW i p n IDS H. eapply ffd_not_rest; [exact IDS|]. rewrite !map_app, !in_app_iff. right; left. change p with (fst (p, n)). apply in_map. eapply fm_in. exact H. Qed.

End Rest.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Calls. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma lib_addr_where : forall s L m OW a, RHEAP s L m -> (forall b, In b OW -> In b L) -> lib_addr OW a ->
  (2895512 <= a < 3491248 /\ ~ (3354968 <= a < 3355026)) \/ (a < alloc_ceiling /\ (a < 0x10000 \/ 0x355000 <= a)).
Proof.
  intros s L m OW a HEAP HL [H|([[p A] n] & Hb & Hr)].
  - left. unfold LIBW_HX in H. cbn [rin_ivs fst snd] in H. lia.
  - right. cbn [blk_addr blk_size fst snd] in Hr. pose proof (blk_bounds s L m p A n HEAP (HL _ Hb)) as (B1 & B2 & B3 & B4 & B5). lia.
Qed.

(* [comment removed for export] *)
Lemma ap_state_of_munch : forall st m m' OW E bo s L W lo,
  ap_state st m OW E bo -> RHEAP s L m -> (forall b, In b OW -> In b L) ->
  munch W m m' -> wmono ctusegs m m' -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  Forall (fun iv => lo <= fst iv \/ iv = (3355012, 3355016)) W ->
  ap_state st m' OW E bo.
Proof.
  intros st m m' OW E bo s L W lo AS HEAP HL MU WM CEIL GLO HW. eapply ap_state_agree; [exact AS|].
  eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros a Ha.
  pose proof (lib_addr_where s L m OW a HEAP HL Ha) as C. unfold GLOBALS_TOP in GLO. clear - C CEIL GLO HW.
  induction W as [|[x y] W IH]; cbn; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
  split; [|apply IH; exact H2]. cbn [fst] in H1. destruct H1 as [H1|H1]; [lia|]. injection H1 as -> ->. lia.
Qed.

Lemma W_ok_errno : forall LB, rclient_write_ok LB (3355012, 3355016).
Proof. intros LB. right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. Qed.

(* [comment removed for export] *)
Lemma get_state_call : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (s : PState) (L OW : list block)
    (E : ap_env) (st : ap_st bptr) (bo : Z * Z) (errv : word) (v : Z),
  ap_state st m OW E bo -> RHEAP s L m -> (forall b, In b OW -> In b L) ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 1024 ->
  bv_unsigned sp mod 16 = 0 -> rw_cells ctusegs m 3355012 [C4 errv] -> mem_inv ctusegs m -> tp = wz RMallocRep.RATP ->
  (v = 0 \/ v = 1) -> a0 = wz v ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (e_es E)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (3355012, 3355016)] m m'
               /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
               /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ rw_cells ctusegs m' 3355012 [C4 errv'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xe8a88) fc None m (seg_rom ctusegs)).
Proof.
  intros. pose proof (ossl_err_get_state_int_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s L OW E st bo errv v) as G.
  unfold LX_ERRNO, GET_STATE_STACK, OSSL_ERR_GET_STATE_INT, RMallocRep.RATP in G. change (3355176 - 164) with 3355012 in G. change (3355012 + 4) with 3355016 in G.
  apply G; assumption.
Qed.
End Calls.

Section StateFacts. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Lemma ap_state_es : forall st m OW E bo, ap_state st m OW E bo ->
  es_raw m (e_es E) (g_of st (badr OW)) /\ g_len (g_of st (badr OW)) /\ es_shape st
  /\ In (p_es E, e_es E, ES_SIZE) OW /\ 0 < e_es E /\ e_es E + ES_SIZE < 2^63 /\ e_es E mod 16 = 0
  /\ Forall (optb_ok OW) (as_file st) /\ Forall (optb_ok OW) (as_func st) /\ Forall (optb_ok OW) (as_data st).
Proof.
  intros st m OW E bo (HE & _ & _ & _ & _ & _ & _ & (SH & EAT & F1 & F2 & F3)).
  pose proof HE as (HF & ND & HP). destruct (env_in E OW HE) as (IES & _).
  unfold env_blocks in HP. apply Forall_cons_iff in HP as [PES _]. cbn [blk_addr blk_size fst snd] in PES.
  split; [apply es_at_raw; exact EAT|]. split; [apply g_len_of; exact SH|]. split; [exact SH|]. split; [exact IES|].
  split; [lia|]. split; [lia|]. split; [lia|]. repeat split; assumption.
Qed.
End StateFacts.

Section Segments. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Definition seg_iv (OW : list block) (lo SP : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= SP) \/ iv = (3355012, 3355016) \/ (exists p A n, In (p, A, n) OW /\ A <= fst iv /\ snd iv <= A + n).

Lemma seg_outside : forall W x, Forall (fun iv : Z * Z => ~ (fst iv <= x < snd iv)) W -> outside W x.
Proof. induction W as [|[a b] W IH]; intros x H; cbn; [exact I|]. apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [lia|apply IH; exact H2]. Qed.

Lemma seg_close : forall s OW LB W m m' lo SP B,
  RHEAP s (OW ++ LB) m -> rauxv_ok m B -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= SP <= B ->
  munch W m m' -> wmono ctusegs m m' -> Forall (seg_iv OW lo SP) W ->
  RHEAP s (OW ++ LB) m' /\ rauxv_ok m' B /\ lx_pres LB SP LIBW_AP m m'.
Proof.
  intros s OW LB W m m' lo SP B HEAP AUX CEIL GLO SPB MU WM HW. unfold GLOBALS_TOP in GLO.
  pose proof (LH_nodup _ _ _ HEAP) as ND.
  assert (BLK : forall p A n, In (p, A, n) OW -> 0 < A /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x355000 <= A) /\ A mod 16 = 0).
  { intros p A n H. eapply blk_bounds; [exact HEAP|]. apply in_app_iff. left. exact H. }
  split; [|split].
  - eapply LH_frame; [exact HEAP|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(p & A & n & H & H1 & H2)]]; cbn [fst snd] in *.
    + apply W_ok_stack. cbn. lia.
    + injection H as -> ->. apply W_ok_errno.
    + eapply (W_ok_block _ (p, A, n)); [apply in_app_iff; left; exact H|cbn; lia|cbn; lia].
  - eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(p & A & n & H & H1 & H2)]]; cbn [fst snd] in *.
    + unfold RAUXV_CELL. lia.
    + injection H as -> ->. unfold RAUXV_CELL. lia.
    + pose proof (BLK _ _ _ H). unfold RAUXV_CELL. lia.
  - eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HX Hc]. apply seg_outside. eapply Forall_impl; [|exact HW].
    intros [x y] [H|[H|(p & A & n & H & H1 & H2)]]; cbn [fst snd] in *.
    + destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| |lia].
      destruct b as [[q A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
      pose proof (blk_bounds _ _ _ q A' n' HEAP ltac:(apply in_app_iff; right; exact Hb)). lia.
    + injection H as -> ->. destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| |unfold ralloc_static, RMallocRep.RERRNO in Hc; lia].
      destruct b as [[q A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
      pose proof (blk_bounds _ _ _ q A' n' HEAP ltac:(apply in_app_iff; right; exact Hb)). lia.
    + pose proof (BLK _ _ _ H) as HB. destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| |lia].
      destruct b as [[q A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
      assert (Hpq : p <> q).
      { intros ->. rewrite map_app in ND. eapply (NoDup_app_disjoint _ _ q ND); [change q with (blk_id (q, A, n)); apply in_map; exact H|].
        change q with (blk_id (q, A', n')). apply in_map. exact Hb. }
      pose proof (blk_disjoint _ _ _ p A n q A' n' HEAP ltac:(apply in_app_iff; left; exact H) ltac:(apply in_app_iff; right; exact Hb) Hpq). lia.
Qed.
End Segments.

Section FreeOpt. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Definition lofree {X} (o : option bptr) (k : lprog X) : lprog X := match o with Some q => LFree q k | None => k end.
Lemma ap_embed_ofree : forall {A} (o : option bptr) (t : aprog bptr A), ap_embed (ofree o t) = lofree o (ap_embed t).
Proof. intros A [q|] t; reflexivity. Qed.

Definition lremove (od : option (bptr * Z)) (L : list block) : list block := match od with Some (q, _) => lb_remove q L | None => L end.

(* [comment removed for export] *)
Definition ofree_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (L' : list block) (lo B : Z) (errv : word) (m : mem)
    (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
    /\ rheap_pres L' (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' L' m'.

Hypothesis HF : rfree_stmt.

(* [comment removed for export] *)
Lemma CRYPTO_free_opt_walk : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (od : option (bptr * Z)) (adr : bptr -> Z) (lo B : Z) (errv : word)
    (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
  RHEAP s L m -> match od with Some (q, n) => In (q, adr q, n) L | None => True end ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_FREE_STACK ->
  rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
  crypto_statics m -> a0 = wz (optr adr od) ->
  (forall s' ms', ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lremove od L) lo B errv m s' ms' ->
                  implM ctusegs (interp k) s' Q ms') ->
  implM ctusegs (interp (lofree (option_map fst od) k)) s Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_FREE) fc None m (seg_rom ctusegs)).
Proof.
  intros until Q. intros HEAP HIN AUX SPB ST CEIL GLO LO ERR MI TP CS HA0 K.
  destruct od as [[q n]|]; cbn [option_map fst lofree optr lremove] in *; [|unfold CRYPTO_FREE_STACK, RFREE_STACK in LO].
  - eapply (CRYPTO_free_walk HF) with (A := adr q) (n := n); eassumption.
  - (* [comment removed for export] *)
    subst tp. eapply implM_evt.
    { eapply (CRYPTO_free_null_spec ra sp gp (wz RATP)); [exact ST|exact GLO|unfold CRYPTO_FREE_STACK, RFREE_STACK in LO; lia|exact MI|exact CS|exact HA0]. }
    intros ms' PO. destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST').
    apply K. unfold ofree_post.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold GLOBALS_TOP in GLO.
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m'. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rw_cells_transport; [exact ERR|exact MU|exact WM|]. unfold LX_ERRNO, RMallocRep.RATP. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|constructor]. }
    split. { eapply heap_pres_of_munch; [exact MU|exact WM|]. intros a Ha Hc. cbn. split; [|exact I].
             apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia|lia|].
             pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & B3 & _). lia. }
    split; [reflexivity|]. split; [reflexivity|].
    eapply LH_frame; [exact HEAP|exact MU|exact WM|]. constructor; [apply W_ok_stack; cbn; lia|constructor].
Qed.
End FreeOpt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Surgery. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

(* [comment removed for export] *)
Lemma g_of_set_top : forall t st adr, g_of (set_top t st) adr = set_g_top (Z.of_nat t) (g_of st adr). Proof. reflexivity. Qed.
Lemma g_of_set_bottom : forall b st adr, g_of (set_bottom b st) adr = set_g_bot (Z.of_nat b) (g_of st adr). Proof. reflexivity. Qed.
Lemma g_of_set_marks : forall i z st adr, g_of (set_marks i z st) adr = set_g_ma (upd (g_ma (g_of st adr)) i (wz z)) (g_of st adr).
Proof. intros. unfold g_of, set_g_ma, set_marks. cbn -[wl lset upd map optr osize repeat ERR_NUM Z.of_nat]. rewrite wl_lset. reflexivity. Qed.
Lemma g_of_set_buf : forall i z st adr, g_of (set_buf i z st) adr = set_g_bu (upd (g_bu (g_of st adr)) i (wz z)) (g_of st adr).
Proof. intros. unfold g_of, set_g_bu, set_buf. cbn -[wl lset upd map optr osize repeat ERR_NUM Z.of_nat]. rewrite wl_lset. reflexivity. Qed.
Lemma g_of_set_line : forall i z st adr, g_of (set_line i z st) adr = set_g_li (upd (g_li (g_of st adr)) i (wz z)) (g_of st adr).
Proof. intros. unfold g_of, set_g_li, set_line. cbn -[wl lset upd map optr osize repeat ERR_NUM Z.of_nat]. rewrite wl_lset. reflexivity. Qed.
Lemma g_of_set_dflags : forall i z st adr, g_of (set_dflags i z st) adr = set_g_df (upd (g_df (g_of st adr)) i (wz z)) (g_of st adr).
Proof. intros. unfold g_of, set_g_df, set_dflags. cbn -[wl lset upd map optr osize repeat ERR_NUM Z.of_nat]. rewrite wl_lset. reflexivity. Qed.
Lemma g_of_set_file : forall i o st adr, g_of (set_file i o st) adr = set_g_fi (upd (g_fi (g_of st adr)) i (wz (optr adr o))) (g_of st adr).
Proof. intros. unfold g_of, set_g_fi, set_file. cbn -[wl lset upd map optr osize repeat ERR_NUM Z.of_nat]. rewrite map_lset, wl_lset. reflexivity. Qed.
Lemma g_of_set_func : forall i o st adr, g_of (set_func i o st) adr = set_g_fu (upd (g_fu (g_of st adr)) i (wz (optr adr o))) (g_of st adr).
Proof. intros. unfold g_of, set_g_fu, set_func. cbn -[wl lset upd map optr osize repeat ERR_NUM Z.of_nat]. rewrite map_lset, wl_lset. reflexivity. Qed.
Lemma g_of_set_data : forall i o st adr,
  g_of (set_data i o st) adr = set_g_ds (upd (g_ds (g_of st adr)) i (wz (osize o))) (set_g_da (upd (g_da (g_of st adr)) i (wz (optr adr o))) (g_of st adr)).
Proof. intros. unfold g_of, set_g_da, set_g_ds, set_data. cbn -[wl lset upd map optr osize repeat ERR_NUM Z.of_nat]. rewrite !map_lset, !wl_lset. reflexivity. Qed.

(* [comment removed for export] *)
Lemma upd_nth_error_same : forall {X} (l : list X) i v, nth_error l i = Some v -> upd l i v = l.
Proof. induction l as [|x l IH]; intros [|i] v H; cbn in *; try discriminate; [congruence|]. rewrite (IH i v H). reflexivity. Qed.
Lemma upd_zeros : forall n i, (i < n)%nat -> upd (wl (repeat 0 n)) i (wz 0) = wl (repeat 0 n).
Proof. intros n i Hi. apply upd_nth_error_same. unfold wl. rewrite nth_error_map, (nth_error_nth' _ 0) by (rewrite repeat_length; exact Hi). rewrite nth_repeat. reflexivity. Qed.

(* [comment removed for export] *)
Lemma g_len_set : forall g,
  g_len g ->
  (forall l, length l = ERR_NUM -> g_len (set_g_fl l g)) /\ (forall l, length l = ERR_NUM -> g_len (set_g_ma l g))
  /\ (forall l, length l = ERR_NUM -> g_len (set_g_bu l g)) /\ (forall l, length l = ERR_NUM -> g_len (set_g_da l g))
  /\ (forall l, length l = ERR_NUM -> g_len (set_g_ds l g)) /\ (forall l, length l = ERR_NUM -> g_len (set_g_df l g))
  /\ (forall l, length l = ERR_NUM -> g_len (set_g_fi l g)) /\ (forall l, length l = ERR_NUM -> g_len (set_g_li l g))
  /\ (forall l, length l = ERR_NUM -> g_len (set_g_fu l g)) /\ (forall t, g_len (set_g_top t g)) /\ (forall b, g_len (set_g_bot b g)).
Proof. intros g (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). unfold g_len; cbn. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma g_of_adr_ext : forall st (adr adr' : bptr -> Z),
  (forall p n, In (Some (p, n)) (as_file st) -> adr p = adr' p) ->
  (forall p n, In (Some (p, n)) (as_func st) -> adr p = adr' p) ->
  (forall p n, In (Some (p, n)) (as_data st) -> adr p = adr' p) ->
  g_of st adr = g_of st adr'.
Proof.
  intros st adr adr' HF HN HD. unfold g_of.
  assert (M : forall l, (forall p n, In (Some (p, n)) l -> adr p = adr' p) -> map (optr adr) l = map (optr adr') l).
  { intros l Hl. apply map_ext_in. intros [[p n]|] Hin; cbn; [apply (Hl p n Hin)|reflexivity]. }
  rewrite (M _ HF), (M _ HN), (M _ HD). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma optb_ok_remove : forall OW q (l : list (option (bptr * Z))),
  Forall (optb_ok OW) l -> (forall p n, In (Some (p, n)) l -> p <> q) -> Forall (optb_ok (lb_remove q OW)) l.
Proof.
  intros OW q l H Hq. apply Forall_forall. intros [[p n]|] Hin; cbn; [|exact I].
  pose proof (proj1 (Forall_forall _ _) H _ Hin) as [I P]. cbn in I, P. pose proof (Hq p n Hin) as NE.
  rewrite (badr_remove_other OW p q NE). split; [|exact P]. apply lb_remove_In. split; [exact I|cbn; exact NE].
Qed.
Lemma optb_ok_cons : forall OW q A0 n0 (l : list (option (bptr * Z))),
  Forall (optb_ok OW) l -> (forall p n, In (Some (p, n)) l -> p <> q) -> Forall (optb_ok ((q, A0, n0) :: OW)) l.
Proof.
  intros OW q A0 n0 l H Hq. apply Forall_forall. intros [[p n]|] Hin; cbn -[badr]; [|exact I].
  pose proof (proj1 (Forall_forall _ _) H _ Hin) as [I P]. cbn in I, P. pose proof (Hq p n Hin) as NE.
  rewrite badr_cons, (bptr_eqb_neq q p ltac:(congruence)). split; [right; exact I|exact P].
Qed.
(* [comment removed for export] *)
Lemma optb_ok_lset_none : forall OW (l : list (option (bptr * Z))) i, Forall (optb_ok OW) l -> Forall (optb_ok OW) (lset l i None).
Proof. induction l as [|x l IH]; intros [|i] H; cbn; [constructor|constructor| |]; apply Forall_cons_iff in H as [H1 H2]; constructor; auto. exact I. Qed.
Lemma optb_ok_lset_some : forall OW (l : list (option (bptr * Z))) i p n,
  Forall (optb_ok OW) l -> In (p, badr OW p, n) OW -> 0 < badr OW p -> Forall (optb_ok OW) (lset l i (Some (p, n))).
Proof. induction l as [|x l IH]; intros [|i] p n H HI HP; cbn; [constructor|constructor| |]; apply Forall_cons_iff in H as [H1 H2]; constructor; auto. cbn. auto. Qed.

Lemma in_lset : forall {X} (l : list X) i v x, In x (lset l i v) -> x = v \/ In x l.
Proof. induction l as [|y l IH]; intros [|i] v x H; cbn in *; [tauto|tauto| |]. destruct H as [<-|H]; [left; reflexivity|right; right; exact H]. destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH _ _ _ H); [left; assumption|right; right; assumption]. Qed.

(* [comment removed for export] *)
Lemma NoDup_lb_remove : forall q OW, List.NoDup (map blk_id OW) -> List.NoDup (map blk_id (lb_remove q OW)).
Proof.
  intros q OW. induction OW as [|b OW IH]; intros ND; [constructor|]. rewrite lb_remove_cons. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct (bptr_eqb (blk_id b) q); [apply IH; exact ND|]. cbn [map]. constructor; [|apply IH; exact ND].
  intros H. apply NI. apply in_map_iff in H. destruct H as (b' & <- & Hb'). apply in_map. eapply lb_remove_incl. exact Hb'.
Qed.

Lemma rest_OW_remove : forall m OW E bo cnf q,
  ap_rest m OW E bo cnf -> ~ In q (map blk_id (rest_blocks OW E cnf)) -> q <> p_es E -> ap_rest m (lb_remove q OW) E bo cnf.
Proof.
  intros m OW E bo cnf q (HE & HI & HS & HC & HT & HX & HB) Hq Hqe. rewrite rest_ids in Hq. rewrite in_app_iff in Hq. cbn [In] in Hq.
  split.
  { destruct HE as (HF & ND & HP). split; [|split; [apply NoDup_lb_remove; exact ND|exact HP]].
    unfold env_blocks in *. repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
    repeat (apply Forall_cons; [apply lb_remove_In; split; [assumption|cbn; intros EQ; first [exact (Hqe (eq_sym EQ)) | apply Hq; left; tauto]]|]). apply Forall_nil. }
  split; [exact HI|]. split; [exact HS|]. split; [|split; [exact HT|split; [exact HX|exact HB]]].
  destruct cnf as [[[lk lh] bk]|]; cbn [ap_statics_cnf cnf_blocks map fst] in *; [|exact HC].
  destruct HC as (S1 & S2 & S3 & S4 & S5 & S6 & I1 & I2 & I3 & M1 & M2 & M3).
  assert (N1 : lk <> q) by (intros EQ; apply Hq; right; rewrite EQ; cbn; tauto). assert (N2 : lh <> q) by (intros EQ; apply Hq; right; rewrite EQ; cbn; tauto).
  assert (N3 : bk <> q) by (intros EQ; apply Hq; right; rewrite EQ; cbn; tauto).
  rewrite !(badr_remove_other OW lk q N1), !(badr_remove_other OW lh q N2), !(badr_remove_other OW bk q N3).
  repeat (split; [assumption|]). split; [apply lb_remove_In; split; [exact I1|cbn; exact N1]|].
  split; [apply lb_remove_In; split; [exact I2|cbn; exact N2]|]. split; [apply lb_remove_In; split; [exact I3|cbn; exact N3]|].
  split; [exact M1|]. split; [exact M2|exact M3].
Qed.

Lemma rest_OW_cons : forall m OW E bo cnf q A0 n0,
  ap_rest m OW E bo cnf -> ~ In q (map blk_id OW) -> 0 < A0 -> A0 + n0 < 2^63 -> A0 mod 16 = 0 -> ap_rest m ((q, A0, n0) :: OW) E bo cnf.
Proof.
  intros m OW E bo cnf q A0 n0 (HE & HI & HS & HC & HT & HX & HB) Hq HA Hn H16.
  assert (NEQ : forall p A n, In (p, A, n) OW -> bptr_eqb q p = false).
  { intros p A n H. apply bptr_eqb_neq. intros ->. apply Hq. change p with (blk_id (p, A, n)). apply in_map. exact H. }
  split.
  { destruct HE as (HF & ND & HP). split; [|split; [cbn [map blk_id fst snd]; constructor; [exact Hq|exact ND]|exact HP]].
    eapply Forall_impl; [|exact HF]. intros b Hb. right. exact Hb. }
  split; [exact HI|]. split; [exact HS|]. split; [|split; [exact HT|split; [exact HX|exact HB]]].
  destruct cnf as [[[lk lh] bk]|]; cbn [ap_statics_cnf] in *; [|exact HC].
  destruct HC as (S1 & S2 & S3 & S4 & S5 & S6 & I1 & I2 & I3 & M1 & M2 & M3).
  rewrite !badr_cons, (NEQ _ _ _ I1), (NEQ _ _ _ I2), (NEQ _ _ _ I3).
  repeat (split; [assumption|]). split; [right; exact I1|]. split; [right; exact I2|]. split; [right; exact I3|].
  split; [exact M1|]. split; [exact M2|exact M3].
Qed.

(* [comment removed for export] *)
Lemma ap_state_join : forall st m OW E bo,
  ap_rest m OW E bo (as_cnf st) -> es_shape st -> es_raw m (e_es E) (g_of st (badr OW)) ->
  Forall (optb_ok OW) (as_file st) -> Forall (optb_ok OW) (as_func st) -> Forall (optb_ok OW) (as_data st) ->
  ap_state st m OW E bo.
Proof. intros st m OW E bo HR SH ES F1 F2 F3. apply ap_state_split. split; [exact HR|]. split; [exact SH|]. split; [apply es_at_raw; exact ES|]. auto. Qed.

(* [comment removed for export] *)
Lemma es_shape_setters : forall st i,
  es_shape st ->
  es_shape (set_top i st) /\ es_shape (set_bottom i st)
  /\ (forall v, es_shape (set_file i v st)) /\ (forall v, es_shape (set_func i v st)) /\ (forall v, es_shape (set_data i v st))
  /\ (forall v, es_shape (set_marks i v st)) /\ (forall v, es_shape (set_buf i v st)) /\ (forall v, es_shape (set_line i v st))
  /\ (forall v, es_shape (set_dflags i v st)).
Proof.
  intros st i SH. pose proof (es_shape_set st i SH) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  split; [apply A8|]. split; [apply A9|]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|exact A7].
Qed.
End Surgery.

Section Seg2. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Lemma nth_wl_optr : forall adr (l : list (option (bptr * Z))) i, nth i (wl (map (optr adr) l)) (wz 0) = wz (optr adr (nth i l None)).
Proof. intros adr l i. unfold wl. rewrite map_map. change (wz 0) with ((fun x => wz (optr adr x)) None). apply map_nth. Qed.
Lemma nth_wl : forall (l : list Z) i, nth i (wl l) (wz 0) = wz (nth i l 0).
Proof. intros l i. unfold wl. change (wz 0) with ((fun x => wz x) 0). apply map_nth. Qed.

(* [comment removed for export] *)
Lemma rest_of_seg : forall s L W mb mc OW E bo st lo,
  ap_state st mb OW E bo \/ ap_rest mb OW E bo (as_cnf st) -> ids_ok E st -> (exists m0, ap_state st m0 OW E bo) ->
  RHEAP s L mb -> (forall b, In b OW -> In b L) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  munch W mb mc -> wmono ctusegs mb mc ->
  Forall (fun iv => lo <= fst iv \/ (fst iv = e_es E /\ snd iv <= e_es E + ES_SIZE)
                    \/ (exists i p n, get_data i st = Some (p, n) /\ fst iv = badr OW p /\ snd iv <= badr OW p + n)) W ->
  ap_rest mc OW E bo (as_cnf st).
Proof.
  intros s L W mb mc OW E bo st lo HR IDS [m0 AS0] HEAP HL CEIL GLO MU WM HW.
  assert (AR : ap_rest mb OW E bo (as_cnf st)) by (destruct HR as [H|H]; [apply ap_state_split in H; exact (proj1 H)|exact H]).
  eapply rest_of_munch; [exact AR|exact MU|exact WM|]. intros a Ha. apply seg_outside. eapply Forall_impl; [|exact HW].
  intros [x y] [H|[[-> Hy]|(i & p & n & Hd & -> & Hy)]]; cbn [fst snd] in *.
  - eapply (rest_outside_stack s L mb); eassumption.
  - intros Hin. eapply (rest_outside_block s L mb OW E bo (as_cnf st) (p_es E) (e_es E) ES_SIZE a); try eassumption.
    + apply HL. destruct AS0 as (HE & _). destruct (env_in E OW HE) as (IES & _). exact IES.
    + eapply es_not_rest; [exact AS0|exact IDS].
    + lia.
  - intros Hin. destruct (ap_state_es _ _ _ _ _ AS0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    destruct (optb_ok_nth OW _ i p n OD Hd) as [HIn _].
    eapply (rest_outside_block s L mb OW E bo (as_cnf st) p (badr OW p) n a); try eassumption.
    + apply HL. exact HIn.
    + eapply data_not_rest; [exact IDS|exact Hd].
    + lia.
Qed.
End Seg2.

Section Seg3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

Lemma lremove_keep : forall od L (b : block), In b L -> (forall q n, od = Some (q, n) -> blk_id b <> q) -> In b (lremove od L).
Proof. intros [[q n]|] L b Hb Hq; cbn; [|exact Hb]. apply lb_remove_In. split; [exact Hb|]. eapply Hq. reflexivity. Qed.
Lemma lremove_incl : forall od L (b : block), In b (lremove od L) -> In b L.
Proof. intros [[q n]|] L b Hb; cbn in Hb; [eapply lb_remove_incl; exact Hb|exact Hb]. Qed.
Lemma lremove_app : forall od OW LB, List.NoDup (map blk_id (OW ++ LB)) -> (forall q n, od = Some (q, n) -> In q (map blk_id OW)) ->
  lremove od (OW ++ LB) = lremove od OW ++ LB.
Proof. intros [[q n]|] OW LB ND Hq; cbn; [|reflexivity]. apply lb_remove_app_l; [exact ND|]. eapply Hq. reflexivity. Qed.
Lemma lremove_nodup : forall od OW, List.NoDup (map blk_id OW) -> List.NoDup (map blk_id (lremove od OW)).
Proof. intros [[q n]|] OW ND; cbn; [apply NoDup_lb_remove; exact ND|exact ND]. Qed.
Lemma badr_lremove : forall od OW p, (forall q n, od = Some (q, n) -> p <> q) -> badr (lremove od OW) p = badr OW p.
Proof. intros [[q n]|] OW p H; cbn; [|reflexivity]. apply badr_remove_other. eapply H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ids_es_ne : forall E st q, ids_ok E st -> In q (es_ids st) -> q <> p_es E.
Proof. intros E st q IDS Hq ->. apply (ids_ok_not_env E st (p_es E) IDS Hq). rewrite env_ids_unfold. cbn. tauto. Qed.

Lemma ids_file_func_ne : forall E st i j qf nf qn nn, ids_ok E st -> get_file i st = Some (qf, nf) -> get_func j st = Some (qn, nn) -> qf <> qn.
Proof.
  intros E st i j qf nf qn nn (ND & _ & _) HF HN. unfold es_ids, st_blocks in ND. rewrite !map_app in ND.
  set (a := map fst (fm (as_file st))) in ND. set (b := map fst (fm (as_func st))) in ND.
  set (c := map fst (fm (as_data st))) in ND. set (d := map fst (cnf_blocks (as_cnf st))) in ND. set (e := env_ids E) in ND.
  assert (EQ : (a ++ b ++ c ++ d) ++ e = a ++ (b ++ c ++ d ++ e)) by (rewrite <- !app_assoc; reflexivity). rewrite EQ in ND.
  intros ->. eapply (NoDup_app_disjoint _ _ qn ND).
  - subst a. change qn with (fst (qn, nf)). apply in_map. eapply fm_in. exact HF.
  - apply in_app_iff. left. subst b. change qn with (fst (qn, nn)). apply in_map. eapply fm_in. exact HN.
Qed.

(* [comment removed for export] *)
Lemma lb_client_ne : forall OW LB q (b : block), List.NoDup (map blk_id (OW ++ LB)) -> In q (map blk_id OW) -> In b LB -> blk_id b <> q.
Proof.
  intros OW LB q b ND Hq Hb EQ. rewrite map_app in ND. eapply (NoDup_app_disjoint _ _ q ND Hq). rewrite <- EQ. apply in_map. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma rest_of_seg' : forall s L W mb mc OW E bo cnf lo,
  ap_rest mb OW E bo cnf -> RHEAP s L mb -> (forall b, In b (rest_blocks OW E cnf) -> In b L) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  munch W mb mc -> wmono ctusegs mb mc ->
  Forall (fun iv => lo <= fst iv \/ (exists p A n, In (p, A, n) L /\ ~ In p (map blk_id (rest_blocks OW E cnf)) /\ A <= fst iv /\ snd iv <= A + n)) W ->
  ap_rest mc OW E bo cnf.
Proof.
  intros s L W mb mc OW E bo cnf lo AR HEAP HL CEIL GLO MU WM HW.
  eapply rest_agree; [exact AR|]. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros a Ha. apply seg_outside.
  eapply Forall_impl; [|exact HW]. intros [x y] [H|(p & A & n & HIn & Hni & H1 & H2)]; cbn [fst snd] in *.
  - destruct (rest_addr_cases _ _ _ _ Ha) as [Hs|([[p A] n] & Hb & Hr)]; [unfold GLOBALS_TOP in GLO; lia|].
    cbn [blk_addr blk_size fst snd] in Hr. pose proof (blk_bounds s L mb p A n HEAP (HL _ Hb)) as (B1 & B2 & B3 & B4 & B5). lia.
  - intros Hin. pose proof (blk_bounds s L mb p A n HEAP HIn) as (B1 & B2 & B3 & B4 & B5).
    destruct (rest_addr_cases _ _ _ _ Ha) as [Hs|([[p' A'] n'] & Hb & Hr)]; [lia|].
    cbn [blk_addr blk_size fst snd] in Hr.
    assert (Hp : p <> p') by (intros ->; apply Hni; change p' with (blk_id (p', A', n')); apply in_map; exact Hb).
    pose proof (blk_disjoint s L mb p A n p' A' n' HEAP HIn (HL _ Hb) Hp) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma rest_blocks_lremove : forall OW E cnf od L,
  (forall b, In b (rest_blocks OW E cnf) -> In b L) ->
  (forall q n, od = Some (q, n) -> ~ In q (map blk_id (rest_blocks OW E cnf))) ->
  forall b, In b (rest_blocks OW E cnf) -> In b (lremove od L).
Proof.
  intros OW E cnf od L HL Hod b Hb. apply lremove_keep; [apply HL; exact Hb|].
  intros q n Hq EQ. apply (Hod q n Hq). rewrite <- EQ. apply in_map. exact Hb.
Qed.
End Seg3.

Section Finish. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

Lemma rest_lremove : forall m OW E bo cnf od,
  ap_rest m OW E bo cnf -> (forall q n, od = Some (q, n) -> ~ In q (map blk_id (rest_blocks OW E cnf)) /\ q <> p_es E) ->
  ap_rest m (lremove od OW) E bo cnf.
Proof. intros m OW E bo cnf [[q n]|] AR H; cbn; [|exact AR]. destruct (H q n eq_refl) as [H1 H2]. apply rest_OW_remove; assumption. Qed.

Lemma optb_ok_lremove : forall OW od (l : list (option (bptr * Z))),
  Forall (optb_ok OW) l -> (forall p n q k, In (Some (p, n)) l -> od = Some (q, k) -> p <> q) -> Forall (optb_ok (lremove od OW)) l.
Proof. intros OW [[q k]|] l H Hq; cbn; [|exact H]. apply optb_ok_remove; [exact H|]. intros p n Hin. eapply Hq; [exact Hin|reflexivity]. Qed.

Lemma fm_in' : forall (l : list (option (bptr * Z))) p n, In (Some (p, n)) l -> In (p, n) (fm l).
Proof. induction l as [|x l IH]; intros p n H; [destruct H|]. rewrite fm_cons. apply in_app_iff. destruct H as [->|H]; [left; cbn; tauto|right; apply IH; exact H]. Qed.

Lemma es_ids_in : forall st p n,
  (In (Some (p, n)) (as_file st) \/ In (Some (p, n)) (as_func st) \/ In (Some (p, n)) (as_data st)) -> In p (es_ids st).
Proof.
  intros st p n H. unfold es_ids, st_blocks. rewrite !map_app, !in_app_iff. change p with (fst (p, n)).
  destruct H as [H|[H|H]]; [left|right; left|right; right; left]; apply in_map; apply fm_in'; exact H.
Qed.

(* [comment removed for export] *)
Lemma ids_pre_disjoint : forall E st st' pre p,
  ids_ok E st -> Permutation (pre ++ st_blocks st') (st_blocks st) -> In p (es_ids st') -> ~ In p (map fst pre).
Proof.
  intros E st st' pre p (ND & _ & _) HP Hp Hpre. unfold es_ids in *.
  assert (ND' : List.NoDup (map fst pre ++ (map fst (st_blocks st') ++ env_ids E))).
  { rewrite app_assoc, <- map_app. eapply Permutation_NoDup; [|exact ND]. apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact HP. }
  eapply (NoDup_app_disjoint _ _ p ND' Hpre). apply in_app_iff. left. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma st_blocks_ecl_fin : forall i st, es_shape st -> (i < ERR_NUM)%nat ->
  exists pre, Permutation ((optb (get_file i st) ++ optb (get_func i st) ++ pre) ++ st_blocks (ecl_fin i st)) (st_blocks st)
              /\ (pre = [] \/ pre = optb (get_data i st)).
Proof.
  intros i st SH Hi. pose proof SH as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof (ecd_proj i st) as (_ & _ & PF & PN & _ & _ & _ & _).
  assert (LF : (i < length (as_file (ecl_mid i st)))%nat) by (unfold ecl_mid; cbn [as_file set_line set_buf set_marks]; rewrite PF, L5; exact Hi).
  assert (LN : (i < length (as_func (set_file i None (ecl_mid i st))))%nat) by (unfold ecl_mid; cbn [as_func set_file set_line set_buf set_marks]; rewrite PN, L7; exact Hi).
  pose proof (st_blocks_set_func i None (set_file i None (ecl_mid i st)) LN) as P1. cbn [optb app] in P1.
  pose proof (st_blocks_set_file i None (ecl_mid i st) LF) as P2. cbn [optb] in P2. rewrite app_nil_l in P2 || idtac.
  assert (GF : get_file i (ecl_mid i st) = get_file i st) by (unfold get_file, ecl_mid; cbn [as_file set_line set_buf set_marks]; rewrite PF; reflexivity).
  assert (GN : get_func i (set_file i None (ecl_mid i st)) = get_func i st) by (unfold get_func, ecl_mid; cbn [as_func set_file set_line set_buf set_marks]; rewrite PN; reflexivity).
  rewrite GF in P2. rewrite GN in P1.
  assert (EM : st_blocks (ecl_mid i st) = st_blocks (ecd i st)) by (unfold ecl_mid; rewrite st_blocks_set_line, st_blocks_set_buf, st_blocks_set_marks; reflexivity).
  rewrite EM in P2.
  destruct (st_blocks_ecd i st ltac:(rewrite L3; exact Hi)) as [P3|P3].
  - exists []. split; [|left; reflexivity]. rewrite app_nil_r. unfold ecl_fin.
    rewrite <- app_assoc. eapply Permutation_trans; [|exact P3]. eapply Permutation_trans; [|exact P2]. apply Permutation_app_head. exact P1.
  - exists (optb (get_data i st)). split; [|right; reflexivity]. unfold ecl_fin.
    eapply Permutation_trans; [|exact P3].
    set (Fb := optb (get_file i st)). set (Nb := optb (get_func i st)). set (Db := optb (get_data i st)). set (SB := st_blocks _).
    replace ((Fb ++ Nb ++ Db) ++ SB) with ((Fb ++ Nb) ++ Db ++ SB) by (rewrite <- !app_assoc; reflexivity).
    eapply Permutation_trans; [apply Permutation_app_swap_app|]. rewrite <- app_assoc.
    apply Permutation_app_head. eapply Permutation_trans; [|exact P2]. apply Permutation_app_head. exact P1.
Qed.
End Finish.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DataCells. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

Lemma data_cells_of_munch : forall s L W mb mc OW st lo,
  data_cells mb OW st -> (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) L) -> RHEAP s L mb ->
  alloc_ceiling <= lo -> munch W mb mc -> wmono ctusegs mb mc ->
  Forall (fun iv => lo <= fst iv \/ iv = (3355012, 3355016)
                    \/ (exists p A n, In (p, A, n) L /\ (forall i q k, get_data i st = Some (q, k) -> q <> p) /\ A <= fst iv /\ snd iv <= A + n)) W ->
  data_cells mc OW st.
Proof.
  intros s L W mb mc OW st lo [DC DF] HD HEAP CEIL MU WM HW. split; [|exact DF]. intros i q k Hd.
  destruct (DC i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. exists junk.
  pose proof (HD i q k Hd) as HIn'.
  pose proof (blk_bounds s L mb q (badr OW q) k HEAP HIn') as (B1 & B2 & B3 & B4 & B5).
  eapply rw_cells_transport; [exact HC|exact MU|exact WM|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
  clear HC MU WM DC. induction W as [|[x y] W IH]; cbn; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2]. split; [|apply IH; exact H2].
  cbn [fst snd] in H1. destruct H1 as [H1|[H1|(p & A & n & HInp & Hne & HA & Hy)]]; [lia|injection H1 as -> ->; lia|].
  pose proof (blk_disjoint s L mb q (badr OW q) k p A n HEAP HIn' HInp ltac:(intros ->; exact (Hne i p k Hd eq_refl))) as D. lia.
Qed.

Lemma data_cells_heap_pres : forall L' SP m m' OW st,
  data_cells m OW st -> rheap_pres L' SP m m' -> (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) L') -> data_cells m' OW st.
Proof.
  intros L' SP m m' OW st [DC DF] HP HL. split; [|exact DF]. intros i q k Hd. destruct (DC i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. exists junk.
  eapply rw_cells_agree; [apply (agree_of_heap_pres _ _ _ _ HP)|exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia.
  right. right. exists (q, badr OW q, k). split; [eapply HL; exact Hd|]. cbn. lia.
Qed.

Lemma data_cells_OW : forall m OW OW' st,
  data_cells m OW st -> (forall i q k, get_data i st = Some (q, k) -> badr OW' q = badr OW q) -> data_cells m OW' st.
Proof. intros m OW OW' st [DC DF] HB. split; [|exact DF]. intros i q k Hd. rewrite (HB i q k Hd). exact (DC i q k Hd). Qed.

Lemma data_cells_sub : forall m OW st st',
  data_cells m OW st -> (forall i q k, get_data i st' = Some (q, k) -> exists j, get_data j st = Some (q, k)) -> dflags_ok st' -> data_cells m OW st'.
Proof. intros m OW st st' [DC DF] HS DF'. split; [|exact DF']. intros i q k Hd. destruct (HS i q k Hd) as [j Hj]. exact (DC j q k Hj). Qed.

Lemma data_cells_dflags : forall m OW st, data_cells m OW st -> dflags_ok st.
Proof. intros m OW st [_ DF]. exact DF. Qed.

(* [comment removed for export] *)
Lemma dflags_ok_ecd : forall i st, (i < length (as_data st))%nat -> length (as_dflags st) = length (as_data st) -> dflags_ok st -> dflags_ok (ecd i st).
Proof.
  intros i st Hi HL DF j Hj. unfold ecd in *.
  destruct (Z.eqb_spec (Z.land (get_dflags i st) ERR_TXT_MALLOCED) 0) as [E0|E0]; cbn [negb] in *.
  - unfold get_data, get_dflags in *. cbn [as_data as_dflags set_dflags set_data] in *.
    destruct (Nat.eq_dec j i) as [->|NE]; [rewrite nth_lset_same by lia; reflexivity|].
    rewrite nth_lset_other by congruence. rewrite nth_lset_other in Hj by congruence. exact (DF j Hj).
  - destruct (get_data i st) as [[pd nd]|] eqn:GD.
    + unfold get_data, get_dflags in *. cbn [as_data as_dflags set_dflags] in *.
      destruct (Nat.eq_dec j i) as [->|NE]; [rewrite GD in Hj; discriminate|]. rewrite nth_lset_other by congruence. exact (DF j Hj).
    + exfalso. exact (E0 (DF i GD)).
Qed.

Lemma dflags_ok_same : forall st st', as_data st' = as_data st -> as_dflags st' = as_dflags st -> dflags_ok st -> dflags_ok st'.
Proof. intros st st' ED EF DF j Hj. unfold get_data, get_dflags in *. rewrite ED, EF in *. exact (DF j Hj). Qed.

(* [comment removed for export] *)
Lemma get_data_lset_none : forall (l : list (option (bptr * Z))) i j q k,
  nth j (lset l i None) None = Some (q, k) -> nth j l None = Some (q, k).
Proof. induction l as [|x l IH]; intros [|i] [|j] q k H; cbn in *; try discriminate; try exact H. eapply IH. exact H. Qed.

Lemma get_data_ecd : forall i st j q k, get_data j (ecd i st) = Some (q, k) -> get_data j st = Some (q, k).
Proof.
  intros i st j q k H. unfold ecd in H. destruct (negb _); [destruct (get_data i st); [|exact H]|].
  - unfold get_data in H |- *. cbn [as_data set_dflags] in H. exact H.
  - unfold get_data in H |- *. cbn [as_data set_dflags set_data] in H. eapply get_data_lset_none. exact H.
Qed.

(* [comment removed for export] *)
Lemma badr_size_unique : forall OW p A n A' n', List.NoDup (map blk_id OW) -> In (p, A, n) OW -> In (p, A', n') OW -> A = A' /\ n = n'.
Proof. intros OW p A n A' n' ND H1 H2. pose proof (nodup_id_inj OW _ _ ND H1 H2 eq_refl) as EQ. injection EQ as <- <-. split; reflexivity. Qed.
End DataCells.

Section MoreIds. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.
Lemma ids_file_data_ne : forall E st i j qf nf q k, ids_ok E st -> get_file i st = Some (qf, nf) -> get_data j st = Some (q, k) -> qf <> q.
Proof.
  intros E st i j qf nf q k (ND & _ & _) HF HD. unfold es_ids, st_blocks in ND. rewrite !map_app in ND.
  set (a := map fst (fm (as_file st))) in ND. set (b := map fst (fm (as_func st))) in ND.
  set (c := map fst (fm (as_data st))) in ND. set (d := map fst (cnf_blocks (as_cnf st))) in ND. set (e := env_ids E) in ND.
  assert (EQ : (a ++ b ++ c ++ d) ++ e = a ++ (b ++ c ++ d ++ e)) by (rewrite <- !app_assoc; reflexivity). rewrite EQ in ND.
  intros ->. eapply (NoDup_app_disjoint _ _ q ND).
  - subst a. change q with (fst (q, nf)). apply in_map. eapply fm_in. exact HF.
  - rewrite !in_app_iff. right; left. subst c. change q with (fst (q, k)). apply in_map. eapply fm_in. exact HD.
Qed.
Lemma ids_func_data_ne : forall E st i j qn nn q k, ids_ok E st -> get_func i st = Some (qn, nn) -> get_data j st = Some (q, k) -> qn <> q.
Proof.
  intros E st i j qn nn q k (ND & _ & _) HN HD. unfold es_ids, st_blocks in ND. rewrite !map_app in ND.
  set (a := map fst (fm (as_file st))) in ND. set (b := map fst (fm (as_func st))) in ND.
  set (c := map fst (fm (as_data st))) in ND. set (d := map fst (cnf_blocks (as_cnf st))) in ND. set (e := env_ids E) in ND.
  assert (EQ : (a ++ b ++ c ++ d) ++ e = (a ++ b) ++ (c ++ d ++ e)) by (rewrite <- !app_assoc; reflexivity). rewrite EQ in ND.
  intros ->. eapply (NoDup_app_disjoint _ _ q ND).
  - apply in_app_iff. right. subst b. change q with (fst (q, nn)). apply in_map. eapply fm_in. exact HN.
  - rewrite !in_app_iff. left. subst c. change q with (fst (q, k)). apply in_map. eapply fm_in. exact HD.
Qed.
Lemma ids_data_es_ne : forall E st j q k, ids_ok E st -> get_data j st = Some (q, k) -> q <> p_es E.
Proof. intros E st j q k IDS HD. eapply ids_es_ne; [exact IDS|eapply es_ids_data; exact HD]. Qed.
End MoreIds.

Section Dflags. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Lemma es_rd_df1 : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DFLAGS + 4 * Z.of_nat i) ->
  ov_read_bytes ctusegs m a 1 = Some (le1 (nth i (g_df g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (_ & _ & _ & _ & _ & [Hb _] & _). unfold g_len, ERR_NUM in *.
  destruct (nth_error_len (g_df g) i ltac:(lia)) as (w & Hw & <-).
  destruct (u32s_split _ _ _ Hw) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * Z.of_nat i) with (Z.of_nat (4 * i)) by lia.
  rewrite (bytes_at_ov_read ctusegs m (A + ESO_DFLAGS) (u32s (g_df g)) (4 * i) 1 Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  unfold le4, le1. cbn [Z_to_le_bytes firstn app]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land1_mod : forall x k, 0 < k -> Z.land (x mod 2 ^ k) 1 = Z.land x 1.
Proof.
  intros x k Hk. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit 1 n) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite !andb_false_r. reflexivity.
Qed.
Lemma dflag_bit : forall f, Z.land (bv_unsigned (Z_to_bv 64 f) mod 2 ^ 8) 1 = Z.land f ERR_TXT_MALLOCED.
Proof.
  intros f. unfold ERR_TXT_MALLOCED. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (land1_mod _ 8), (land1_mod _ 64) by lia. reflexivity.
Qed.
Lemma land_malloced_mask : forall f, Z.land (Z.land f ERR_TXT_MALLOCED) 18446744073709551615 = Z.land f ERR_TXT_MALLOCED.
Proof.
  intros f. unfold ERR_TXT_MALLOCED. change 1 with (Z.ones 1). rewrite (Z.land_ones f 1) by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (Z.mod_pos_bound f (2 ^ 1) ltac:(lia)). lia.
Qed.
Lemma land_malloced_range : forall f, 0 <= Z.land f ERR_TXT_MALLOCED <= 1.
Proof.
  intros f. unfold ERR_TXT_MALLOCED. replace (Z.land f 1) with (f mod 2 ^ 1) by (symmetry; change 1 with (Z.ones 1) at 1; apply Z.land_ones; lia).
  pose proof (Z.mod_pos_bound f (2 ^ 1) ltac:(lia)). lia.
Qed.
End Dflags.

Section DataStore. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.
(* [comment removed for export] *)
Lemma data_cells_store1 : forall s L mc m' OW st lo x y pd D nd junk',
  data_cells mc OW st -> (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) L) ->
  In (pd, D, nd) L -> 1 <= nd -> RHEAP s L mc -> alloc_ceiling <= lo -> lo <= x ->
  munch [(x, y); (D, D + 1)] mc m' -> wmono ctusegs mc m' ->
  rw_cells ctusegs m' D [CB (Z.to_nat nd) junk'] ->
  data_cells m' OW st.
Proof.
  intros s L mc m' OW st lo x y pd D nd junk' [DC DF] HD HIn Hnd HEAP CEIL Hx MU WM HC'. split; [|exact DF]. intros i q k Hd.
  destruct (DC i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. pose proof (HD i q k Hd) as HInq.
  pose proof (LH_nodup _ _ _ HEAP) as ND.
  destruct (bptr_eqb q pd) eqn:E.
  - apply bptr_eqb_eq in E. subst q. destruct (badr_size_unique L pd (badr OW pd) k D nd ND HInq HIn) as [-> ->]. exists junk'. exact HC'.
  - assert (NE : q <> pd) by (intros ->; rewrite bptr_eqb_refl in E; discriminate).
    exists junk. pose proof (blk_bounds s L mc q (badr OW q) k HEAP HInq) as (B1 & B2 & B3 & B4 & B5).
    pose proof (blk_disjoint s L mc q (badr OW q) k pd D nd HEAP HInq HIn NE) as DJ.
    eapply rw_cells_transport; [exact HC|exact MU|exact WM|]. cbn [cells_size csize Nat.add disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    split; [lia|]. split; [lia|exact I].
Qed.
End DataStore.

Section ErrPack. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma land_shift_small_0 : forall a b k, 0 <= k -> 0 <= b < 2 ^ k -> Z.land (a * 2 ^ k) b = 0.
Proof.
  intros a b k Hk Hb. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [L|L].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit b n) with false; [apply andb_false_r|]. symmetry.
    destruct (Z.eq_dec b 0) as [->|Hb0]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    pose proof (proj1 (Z.log2_lt_pow2 b k ltac:(lia)) ltac:(lia)). lia.
Qed.

Lemma err_pack_val : forall lib reason, 0 <= lib < 256 -> 0 <= reason < 8388608 ->
  ERR_PACK lib reason = lib * 2 ^ 23 + reason.
Proof.
  intros lib reason Hl Hr. unfold ERR_PACK.
  change 255 with (Z.ones 8). change 8388607 with (Z.ones 23). rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite <- Z.lxor_lor by (apply land_shift_small_0; lia). symmetry. apply Z.add_nocarry_lxor. apply land_shift_small_0; lia.
Qed.

Lemma err_pack_range : forall lib reason, 0 <= lib < 256 -> 0 <= reason < 8388608 -> 0 <= ERR_PACK lib reason < 2 ^ 31.
Proof. intros. rewrite err_pack_val by lia. lia. Qed.

(* [comment removed for export] *)
Lemma err_pack_bits : forall lib reason, 0 <= lib < 256 -> 0 <= reason < 8388608 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 lib)) 56))) 33)))
        (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 reason)) 41))) 41)))
  = ERR_PACK lib reason.
Proof.
  intros lib reason Hl Hr. rewrite (unsigned_lit lib), (unsigned_lit reason) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (lib * 2 ^ 56)), (unsigned_lit (reason * 2 ^ 41)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (lib * 2 ^ 56 / 2 ^ 33) with (lib * 2 ^ 23) by (symmetry; replace (2 ^ 56) with (2 ^ 23 * 2 ^ 33) by reflexivity; rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite Z.div_mul by lia. rewrite !unsigned_lit by lia.
  rewrite err_pack_val by lia. rewrite <- Z.lxor_lor by (apply land_shift_small_0; lia). symmetry. apply Z.add_nocarry_lxor. apply land_shift_small_0; lia.
Qed.

(* [comment removed for export] *)
Lemma zext32_shifts : forall x, 0 <= x < 2 ^ 32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32 = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.
End ErrPack.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kept. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition kept (K : list block) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> in_block K a -> m' (wa a) = m (wa a).
Lemma kept_refl : forall K m, kept K m m. Proof. intros K m a _ _. reflexivity. Qed.
Lemma kept_trans : forall K m1 m2 m3, kept K m1 m2 -> kept K m2 m3 -> kept K m1 m3.
Proof. intros K m1 m2 m3 H1 H2 a Ha Hb. rewrite (H2 a Ha Hb). apply H1; assumption. Qed.

Lemma kept_of_heap_pres : forall K L' SP m m', rheap_pres L' SP m m' -> (forall b, In b K -> In b L') -> kept K m m'.
Proof.
  intros K L' SP m m' HP HK a Ha (b & Hb & Hr). apply (HP a Ha). right. right. exists b. split; [apply HK; exact Hb|exact Hr].
Qed.

Lemma kept_of_munch : forall s L W mb mc K lo,
  RHEAP s L mb -> (forall b, In b K -> In b L) -> alloc_ceiling <= lo -> munch W mb mc ->
  Forall (fun iv => lo <= fst iv \/ iv = (3355012, 3355016)
                    \/ (exists p A n, In (p, A, n) L /\ ~ In p (map blk_id K) /\ A <= fst iv /\ snd iv <= A + n)) W ->
  kept K mb mc.
Proof.
  intros s L W mb mc K lo HEAP HK CEIL MU HW a Ha (b & Hb & Hr). apply MU. unfold wa. rewrite unsigned_lit by lia.
  destruct b as [[q A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
  pose proof (blk_bounds s L mb q A' n' HEAP (HK _ Hb)) as (B1 & B2 & B3 & B4 & B5).
  apply seg_outside. eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(p & A & n & HIn & Hni & HA & Hy)]]; cbn [fst snd] in *.
  - lia.
  - injection H as -> ->. lia.
  - assert (Hpq : p <> q) by (intros ->; apply Hni; change q with (blk_id (q, A', n')); apply in_map; exact Hb).
    pose proof (blk_disjoint s L mb p A n q A' n' HEAP HIn (HK _ Hb) Hpq). lia.
Qed.

Lemma K_lremove : forall K L od, (forall b, In b K -> In b L) -> (forall q n, od = Some (q, n) -> ~ In q (map blk_id K)) ->
  forall b, In b K -> In b (lremove od L).
Proof.
  intros K L od HK Hod b Hb. apply lremove_keep; [apply HK; exact Hb|]. intros q n Hq EQ. apply (Hod q n Hq). rewrite <- EQ. apply in_map. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma K_not_es : forall K (st : ap_st bptr) E, (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
  forall q, In q (es_ids st) -> ~ In q (map blk_id K).
Proof. intros K st E HK q Hq Hin. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). apply (HK b Hb). apply in_app_iff. left. exact Hq. Qed.
Lemma K_not_env : forall K (st : ap_st bptr) E, (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
  forall q, In q (env_ids E) -> ~ In q (map blk_id K).
Proof. intros K st E HK q Hq Hin. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). apply (HK b Hb). apply in_app_iff. right. exact Hq. Qed.
End Kept.

Section Kept2. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma es_ids_sub_perm : forall (st st' : ap_st bptr) pre q,
  Permutation (pre ++ st_blocks st') (st_blocks st) -> In q (es_ids st') -> In q (es_ids st).
Proof.
  intros st st' pre q HP Hq. unfold es_ids in *. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb).
  apply in_map. eapply Permutation_in; [exact HP|]. apply in_app_iff. right. exact Hb.
Qed.
End Kept2.

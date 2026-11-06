(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim APrimSpec2 APrimLem APrimPop APrimRefill APrimQ APrimDealloc APrimCover ASec ASecD AQuar AQuarM
                        AHeap F_quar_E AQuarR AQuarP F_quar_As F_quar_R F_quar_DR F_quar_D F_quar_P.
Import ListNotations.
Open Scope Z_scope.

Definition sum_cs (hs : list (Z * Z)) : Z := fold_right (fun cv acc => class_size (fst cv) + acc) 0 hs.
Lemma sum_cs_cons : forall x l, sum_cs (x :: l) = class_size (fst x) + sum_cs l. Proof. reflexivity. Qed.
Lemma sum_cs_app : forall l1 l2, sum_cs (l1 ++ l2) = sum_cs l1 + sum_cs l2.
Proof. induction l1 as [|x l1 IH]; intros l2; [reflexivity|]. rewrite <- app_comm_cons, !sum_cs_cons, IH. lia. Qed.
Lemma sum_cs_perm : forall l1 l2, Permutation l1 l2 -> sum_cs l1 = sum_cs l2.
Proof. induction 1; rewrite ?sum_cs_cons; lia. Qed.

Lemma remove_at_perm : forall (l : list schunk) (i : nat) (c : schunk), nth_error l i = Some c -> Permutation l (c :: remove_at l i).
Proof.
  intros l i c NTH. pose proof (nth_error_lt _ _ _ NTH) as Hi.
  destruct l as [|x0 l0] using rev_ind; [cbn in Hi; lia|]. clear IHl0. rewrite remove_at_snoc. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.eqb_spec i (length l0)) as [->|NE].
  - rewrite nth_error_app2, Nat.sub_diag in NTH by lia. cbn in NTH. injection NTH as ->. apply Permutation_sym. apply Permutation_cons_append.
  - rewrite nth_error_app1 in NTH by lia.
    rewrite <- (firstn_skipn i l0) at 1. rewrite (skipn_cons_nth l0 i c NTH). rewrite <- app_assoc. cbn [app].
    apply Permutation_sym. apply Permutation_cons_app. apply Permutation_app_head. apply Permutation_cons_append.
Qed.

Section PCOV.
Variable c : Z.
Hypothesis Hc : 1 <= c <= 31.

#[using="Hc"] Lemma refill_cover_cls : forall k, pclass_wf c k -> p_cnt k = 0 ->
  (forall x, In x (cls_free k) -> In x (cls_free (refill k c)))
  /\ (forall x, 0 <= x -> p_au k <= 16 * x -> 16 * x + class_size c <= p_au (refill k c) -> (16 * x) mod class_size c = 0 -> In x (cls_free (refill k c))).
Proof.
  intros k WF C0. pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CM.
  pose proof WF as (Lnf & Lcnt & _ & _ & _ & _ & AU & _ & _ & AUS & _).
  assert (CH : p_chunks k = []) by (destruct (p_chunks k); [reflexivity| cbn [length] in Lcnt; lia]).
  assert (FR : forall x, In x (cls_free (refill k c)) <-> In x (p_fa (gfa_pre k c (max_count c / 2)))).
  { intros x. unfold refill, get_from_allocator, cls_free. cbn [p_fa p_chunks]. rewrite firstn_skipn. tauto. }
  assert (AUR : p_au (refill k c) = p_au (gfa_pre k c (max_count c / 2))) by reflexivity.
  split.
  - intros x Hx. apply FR. unfold cls_free in Hx. rewrite CH, app_nil_r in Hx. unfold gfa_pre. destruct (p_nf k <? max_count c / 2); [| exact Hx].
    unfold populate. cbn [p_fa]. apply in_app_iff. left. exact Hx.
  - intros x X0 XA XB XM. apply FR. rewrite AUR in XB. unfold gfa_pre in *. destruct (p_nf k <? max_count c / 2); [| exfalso; clear - XA XB CS; lia].
    unfold populate in *. cbn [p_fa p_au] in *. apply in_app_iff. right. apply in_carve.
    set (newc := pop_new k c (max_count c / 2 - p_nf k)) in *.
    assert (N0 : 0 <= newc) by (destruct (Z_lt_le_dec newc 0) as [NEG|]; [exfalso; clear - NEG XA XB CS; nia| assumption]).
    exists (Z.to_nat ((16 * x - p_au k) / class_size c)).
    assert (DV : 16 * x - p_au k = class_size c * ((16 * x - p_au k) / class_size c)).
    { apply Z_div_exact_full_2; [clear - CS; lia|]. rewrite Zminus_mod, XM, AUS. reflexivity. }
    assert (Q0 : 0 <= (16 * x - p_au k) / class_size c) by (apply Z.div_pos; clear - XA CS; lia).
    split.
    + apply Z2Nat.inj_lt; [exact Q0| exact N0|]. clear - DV XB CS Q0 N0. nia.
    + rewrite Z2Nat.id by exact Q0. replace (p_au k + (16 * x - p_au k) / class_size c * class_size c) with (x * 16) by (clear - DV; lia).
      rewrite Z_div_mult by lia. reflexivity.
Qed.

End PCOV.

Lemma cover_ext : forall P P' hs, (forall c, 1 <= c <= 31 -> get_cls P' c = get_cls P c) -> cover P hs -> cover P' hs.
Proof. intros P P' hs EX CV c v Hc V0 V1 V2. rewrite (EX c Hc) in *. exact (CV c v Hc V0 V1 V2). Qed.

Lemma get_cls_set_eq : forall cls ini ca cm c k c', length cls = 32%nat -> 1 <= c <= 31 -> 1 <= c' <= 31 ->
  get_cls (mkPRIM (set_nth (Z.to_nat c) k cls) ini ca cm) c' = if c' =? c then k else nth (Z.to_nat c') cls pclass0.
Proof.
  intros cls ini ca cm c k c' LEN Hc Hc'. destruct (Z.eqb_spec c' c) as [->|NE].
  - apply get_cls_set_same; [exact LEN| lia].
  - rewrite get_cls_set_other by lia. reflexivity.
Qed.

Lemma refill_cnt : forall c k, 1 <= c <= 31 -> p_cnt (refill k c) = max_count c / 2 /\ 1 <= max_count c / 2.
Proof.
  intros c k Hc. split; [unfold refill, get_from_allocator; reflexivity|].
  pose proof (max_count_range c Hc) as (R & M). clear - R M. Z.div_mod_to_equations. lia.
Qed.

Lemma cache_alloc_cls_refill : forall c k, 1 <= c <= 31 -> p_cnt k = 0 -> cache_alloc_cls k c = cache_alloc_cls (refill k c) c.
Proof.
  intros c k Hc C0. destruct (refill_cnt c k Hc) as [RC R1]. unfold cache_alloc_cls at 1 2. rewrite C0. cbn [Z.eqb].
  replace (p_cnt (refill k c) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma cover_refill_prim : forall P hs c, 1 <= c <= 31 -> length (pr_cls P) = 32%nat ->
  pclass_wf c (get_cls P c) -> p_cnt (get_cls P c) = 0 -> cover P hs -> cover (refill_prim P c) hs.
Proof.
  intros P hs c Hc LEN WF C0 CV. destruct (refill_cover_cls c Hc (get_cls P c) WF C0) as [F1 F2].
  assert (EC : forall c', 1 <= c' <= 31 -> get_cls (refill_prim P c) c' = if c' =? c then refill (get_cls P c) c else get_cls P c').
  { intros c' Hc'. unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *. apply get_cls_set_eq; assumption. }
  pose proof WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AUS & _).
  apply (cover_grow P (refill_prim P c) hs c CV); [| | | exact AUS| exact Hc].
  - intros c' NE. destruct (Z_le_gt_dec 1 c') as [L1|G1]; [destruct (Z_le_gt_dec c' 31) as [L2|G2]|].
    + rewrite (EC c' ltac:(lia)). replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
    + unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *. rewrite get_cls_set_other by lia. reflexivity.
    + unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
      destruct (Z_lt_le_dec c' 0) as [NEG|POS]; [| rewrite get_cls_set_other by lia; reflexivity].
      unfold get_cls. cbn [pr_cls]. replace (Z.to_nat c') with (Z.to_nat 0) by lia. apply nth_set_nth_other. lia.
  - rewrite (EC c Hc), Z.eqb_refl. exact F1.
  - rewrite (EC c Hc), Z.eqb_refl. exact F2.
Qed.

Lemma get_cls_set_off : forall cls ini ca cm c k c', 1 <= c <= 31 -> c' <> c ->
  get_cls (mkPRIM (set_nth (Z.to_nat c) k cls) ini ca cm) c' = nth (Z.to_nat c') cls pclass0.
Proof.
  intros cls ini ca cm c k c' Hc NE. unfold get_cls. cbn [pr_cls]. destruct (Z_lt_le_dec c' 0) as [NEG|POS].
  - replace (Z.to_nat c') with 0%nat by lia. apply nth_set_nth_other. lia.
  - apply nth_set_nth_other. lia.
Qed.

Definition pre_pop (P : prim) (c : Z) : prim := if p_cnt (get_cls P c) =? 0 then refill_prim P c else P.
Lemma enq_P1_eq : forall P, enq_P1 P = pre_pop P K_BCLASS. Proof. reflexivity. Qed.

Lemma pre_pop_facts : forall P c, 1 <= c <= 31 -> length (pr_cls P) = 32%nat -> pclass_wf c (get_cls P c) ->
  (p_cnt (get_cls P c) = 0 -> refill_budget c (get_cls P c)) ->
  let P1 := pre_pop P c in
  pclass_wf c (get_cls P1 c) /\ 0 < p_cnt (get_cls P1 c) /\ length (pr_cls P1) = 32%nat
  /\ (forall c', c' <> c -> get_cls P1 c' = get_cls P c')
  /\ cache_alloc_cls (get_cls P c) c = cache_alloc_cls (get_cls P1 c) c /\ pr_calloc P1 = pr_calloc P
  /\ get_cls P1 c = (if p_cnt (get_cls P c) =? 0 then refill (get_cls P c) c else get_cls P c).
Proof.
  intros P c Hc LEN WF BUD. unfold pre_pop. cbv zeta. destruct (Z.eqb_spec (p_cnt (get_cls P c)) 0) as [C0|CN].
  - destruct (BUD C0) as [B1 B2]. pose proof (refill_wf c (get_cls P c) Hc WF B1 B2 C0) as WF1. destruct (refill_cnt c (get_cls P c) Hc) as [RC R1].
    assert (EK : get_cls (refill_prim P c) c = refill (get_cls P c) c).
    { unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
    rewrite EK. split; [exact WF1|]. split; [lia|].
    split; [unfold refill_prim; cbv zeta; cbn [pr_cls]; rewrite set_nth_length; exact LEN|].
    split; [intros c' NE; unfold refill_prim; cbv zeta; destruct P as [cls ini ca cm]; cbn [pr_cls pr_calloc pr_cmapped]; apply get_cls_set_off; assumption|].
    split; [exact (cache_alloc_cls_refill c (get_cls P c) Hc C0)|]. split; reflexivity.
  - pose proof WF as (_ & _ & CNT & _). split; [exact WF|]. split; [lia|]. split; [exact LEN|].
    split; [intros; reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.
Lemma pre_pop_cover : forall P c hs, 1 <= c <= 31 -> length (pr_cls P) = 32%nat -> pclass_wf c (get_cls P c) -> cover P hs -> cover (pre_pop P c) hs.
Proof.
  intros P c hs Hc LEN WF CV. unfold pre_pop. destruct (Z.eqb_spec (p_cnt (get_cls P c)) 0) as [C0|CN]; [| exact CV].
  exact (cover_refill_prim P hs c Hc LEN WF C0 CV).
Qed.

Lemma cover_cache_alloc : forall P c hs, 1 <= c <= 31 -> length (pr_cls P) = 32%nat -> pclass_wf c (get_cls P c) ->
  (p_cnt (get_cls P c) = 0 -> refill_budget c (get_cls P c)) -> cover P hs ->
  cover (fst (cache_alloc P c)) ((c, snd (cache_alloc P c)) :: hs)
  /\ pr_calloc (fst (cache_alloc P c)) = pr_calloc P + class_size c
  /\ length (pr_cls (fst (cache_alloc P c))) = 32%nat.
Proof.
  intros P c hs Hc LEN WF BUD CV. destruct (pre_pop_facts P c Hc LEN WF BUD) as (WF1 & CP1 & LEN1 & OTH1 & EQ1 & _). pose proof (pre_pop_cover P c hs Hc LEN WF CV) as CV1.
  set (P1 := pre_pop P c) in *. set (k1 := get_cls P1 c) in *.
  pose proof WF1 as (_ & Lcnt & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). apply NoDup_ListNoDup in ND.
  assert (EP : get_cls (fst (cache_alloc P c)) c = fst (cache_alloc_cls k1 c) /\ snd (cache_alloc P c) = snd (cache_alloc_cls k1 c)
               /\ (forall c', c' <> c -> get_cls (fst (cache_alloc P c)) c' = get_cls P c')
               /\ pr_calloc (fst (cache_alloc P c)) = pr_calloc P + class_size c /\ length (pr_cls (fst (cache_alloc P c))) = 32%nat).
  { unfold cache_alloc. rewrite EQ1. destruct (cache_alloc_cls k1 c) as [kp v]. cbn [fst snd]. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
    split; [apply get_cls_set_same; [exact LEN| lia]|]. split; [reflexivity|]. split; [intros c' NE; apply get_cls_set_off; assumption|].
    split; [reflexivity| rewrite set_nth_length; exact LEN]. }
  destruct EP as (EK & EV & OTH & CAL & LEN'). split; [| split; [exact CAL| exact LEN']]. rewrite EV.
  apply (cover_pop P1 (fst (cache_alloc P c)) hs c _ CV1).
  - intros c' NE. rewrite (OTH c' NE), (OTH1 c' NE). reflexivity.
  - rewrite EK. pose proof (cache_pop_free k1 c 0 Lcnt CP1 ND) as (_ & _ & AU). exact AU.
  - intros x. rewrite EK. pose proof (cache_pop_free k1 c x Lcnt CP1 ND) as (_ & FR & _). exact FR.
Qed.

Lemma cover_cache_dealloc : forall P hs c v, 1 <= c <= 31 -> length (pr_cls P) = 32%nat ->
  cover P ((c, v) :: hs) -> ~ In (c, v) hs ->
  cover (cache_dealloc P c v) hs /\ pr_calloc (cache_dealloc P c v) = pr_calloc P - class_size c
  /\ length (pr_cls (cache_dealloc P c v)) = 32%nat.
Proof.
  intros P hs c v Hc LEN CV NI.
  assert (EK : get_cls (cache_dealloc P c v) c = cache_dealloc_cls (get_cls P c) c v).
  { unfold cache_dealloc. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
  split; [| split; [reflexivity| unfold cache_dealloc; cbn [pr_cls]; rewrite set_nth_length; exact LEN]].
  pose proof (cover_push P (cache_dealloc P c v) ((c, v) :: hs) c v CV) as CP.
  cbn [List.remove] in CP. destruct (cv_eq_dec (c, v) (c, v)) as [_|NE]; [| contradiction]. rewrite (notin_remove cv_eq_dec hs (c, v) NI) in CP.
  apply CP.
  - intros c' NE. exact (get_cls_cdealloc_other P c v c' Hc NE).
  - rewrite EK. apply cache_push_au.
  - intros x. rewrite EK. apply cache_push_free.
Qed.

Section FOLD.
Context {HC : HasCeiling}.
Variable AL : alayout.

Definition pinv (X : pstate) (hs : list (Z * Z)) (secs : list schunk) : Prop :=
  length (pr_cls (fst X)) = 32%nat
  /\ held_ok (fst X) hs /\ cover (fst X) hs /\ pr_calloc (fst X) = sum_cs hs
  /\ chunks_sep (se_chunks (snd X)) /\ Forall (chunk_ok AL) (se_chunks (snd X)) /\ Permutation (se_chunks (snd X)) secs.

#[using="Type"] Lemma held_ok_perm' : forall P h1 h2, Permutation h1 h2 -> held_ok P h1 -> held_ok P h2.
Proof. intros P h1 h2 PM [ND FH]. split; [eapply Permutation_NoDup; eassumption| eapply Permutation_Forall; eassumption]. Qed.

#[using="Type"] Lemma pinv_perm : forall X hs hs' secs secs', Permutation hs hs' -> Permutation secs secs' -> pinv X hs secs -> pinv X hs' secs'.
Proof.
  intros X hs hs' secs secs' PH PS (LEN & HO & CV & CA & SEP & COK & PSE). unfold pinv.
  split; [exact LEN|]. split; [exact (held_ok_perm' _ _ _ PH HO)|].
  split; [apply (cover_incl _ hs hs' CV); intros x Hx; eapply Permutation_in; eassumption|].
  split; [rewrite CA; exact (sum_cs_perm _ _ PH)|]. split; [exact SEP|]. split; [exact COK|]. exact (Permutation_trans PSE PS).
Qed.

#[using="Type"] Lemma pinv_prim : forall X ch c v hs secs, qc_kind ch = QPrim c v -> pinv X ((c, v) :: hs) secs -> pinv (recycle1 X ch) hs secs.
Proof.
  intros X ch c v hs secs EK (LEN & HO & CV & CA & SEP & COK & PSE). unfold recycle1. rewrite EK. unfold pinv. cbn [fst snd].
  pose proof HO as [ND FH]. apply Forall_cons_iff in FH as [(Hc & _) _]. cbn [fst] in Hc. apply NoDup_cons_iff in ND as [NI _].
  destruct (cover_cache_dealloc (fst X) hs c v Hc LEN CV NI) as (CV' & CA' & LEN').
  split; [exact LEN'|]. split; [exact (held_ok_cdealloc (fst X) [] hs c v LEN Hc HO)|]. split; [exact CV'|].
  split; [rewrite CA', CA, sum_cs_cons; cbn [fst]; lia|]. split; [exact SEP|]. split; [exact COK| exact PSE].
Qed.

#[using="Type"] Lemma pinv_sec : forall X ch sc hs secs, qc_kind ch = QSec sc -> pinv X hs (sc :: secs) -> pinv (recycle1 X ch) hs secs.
Proof.
  intros X ch sc hs secs EK (LEN & HO & CV & CA & SEP & COK & PSE). unfold recycle1. rewrite EK. unfold pinv. cbn [fst snd sec_dealloc se_chunks].
  assert (IN : In sc (se_chunks (snd X))) by (eapply Permutation_in; [apply Permutation_sym; exact PSE| left; reflexivity]).
  assert (POS : Forall (fun c => 0 < sc_msize c) (se_chunks (snd X))).
  { eapply Forall_impl; [| exact COK]. intros d CK. pose proof (chunk_ok_msize AL d CK) as [M1 _]. lia. }
  pose proof (sc_index_nth (se_chunks (snd X)) sc SEP POS IN) as NTH. pose proof (nth_error_lt _ _ _ NTH) as LT.
  split; [exact LEN|]. split; [exact HO|]. split; [exact CV|]. split; [exact CA|].
  split; [exact (chunks_sep_remove_at _ _ LT SEP)|].
  split; [apply Forall_forall; intros d Hd; exact (proj1 (Forall_forall _ _) COK d (remove_at_In _ _ d LT Hd))|].
  pose proof (remove_at_perm _ _ _ NTH) as RP. apply (Permutation_cons_inv (a := sc)).
  eapply Permutation_trans; [apply Permutation_sym; exact RP| exact PSE].
Qed.

#[using="Type"] Lemma pinv_chunks : forall chs X hs secs,
  pinv X (flat_map prim_of chs ++ hs) (flat_map sec_of chs ++ secs) -> pinv (recycle_chunks X chs) hs secs.
Proof.
  induction chs as [|ch chs IH]; intros X hs secs PI; [exact PI|]. cbn [recycle_chunks flat_map] in *. apply IH.
  destruct (qc_kind ch) as [c v|sc] eqn:EK; unfold prim_of, sec_of in PI; rewrite EK in PI; cbn [app] in PI.
  - exact (pinv_prim X ch c v _ _ EK PI).
  - exact (pinv_sec X ch sc _ _ EK PI).
Qed.

#[using="Type"] Lemma pinv_batch : forall b X hs secs,
  pinv X (bpair b :: flat_map prim_of (qb_chunks b) ++ hs) (flat_map sec_of (qb_chunks b) ++ secs) -> pinv (recycle_batch X b) hs secs.
Proof.
  intros b X hs secs PI. unfold recycle_batch. cbv zeta.
  assert (P1 : pinv (recycle_chunks X (qb_chunks b)) (bpair b :: hs) secs).
  { apply pinv_chunks. eapply pinv_perm; [| apply Permutation_refl| exact PI]. apply Permutation_middle. }
  set (X1 := recycle_chunks X (qb_chunks b)) in *.
  pose proof (pinv_prim X1 (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) K_BCLASS (qb_v b) hs secs eq_refl P1) as P2.
  unfold recycle1 in P2. cbn [qc_kind] in P2. exact P2.
Qed.

#[using="Type"] Lemma pinv_dorecycle : forall bs X hs secs,
  pinv X (map bpair bs ++ flat_map prim_of (flat_map qb_chunks bs) ++ hs) (flat_map sec_of (flat_map qb_chunks bs) ++ secs) ->
  pinv (dorecycle X bs) hs secs.
Proof.
  induction bs as [|b bs IH]; intros X hs secs PI; [exact PI|]. cbn [dorecycle]. apply IH. apply pinv_batch.
  cbn [map flat_map app] in PI. rewrite !flat_map_app in PI. eapply pinv_perm; [| | exact PI].
  - apply perm_skip. rewrite <- !app_assoc.
    eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head. apply Permutation_refl.
  - rewrite <- app_assoc. apply Permutation_refl.
Qed.

End FOLD.

Lemma held_cache_alloc : forall P c hs, 1 <= c <= 31 -> length (pr_cls P) = 32%nat -> pclass_wf c (get_cls P c) ->
  (p_cnt (get_cls P c) = 0 -> refill_budget c (get_cls P c)) -> held_ok P hs ->
  held_ok (fst (cache_alloc P c)) ((c, snd (cache_alloc P c)) :: hs).
Proof.
  intros P c hs Hc LEN WF BUD HO.
  destruct (pre_pop_facts P c Hc LEN WF BUD) as (WF1 & CP1 & LEN1 & OTH1 & EQ1 & _ & EK1).
  set (P1 := pre_pop P c) in *. set (k1 := get_cls P1 c) in *.
  pose proof WF1 as (_ & Lcnt & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). apply NoDup_ListNoDup in ND.
  pose proof WF as (_ & _ & _ & _ & _ & _ & AU0 & _ & _ & AUS & _). pose proof (class_size_mod16 c Hc) as CM.
  assert (HO1 : held_ok P1 hs).
  { apply (held_ok_mono P P1 hs HO). intros c0 v0 Hin. destruct (Z.eq_dec c0 c) as [->|NE]; [| rewrite (OTH1 c0 NE); split; [lia| intros HI; left; exact HI]].
    fold k1. rewrite EK1. destruct (p_cnt (get_cls P c) =? 0); [| split; [lia| intros HI; left; exact HI]].
    split; [apply refill_au; [exact Hc| lia]|]. intros HI. apply (refill_free (get_cls P c) c v0 Hc); [| exact HI].
    clear - AUS CM. Z.div_mod_to_equations. lia. }
  assert (EP : get_cls (fst (cache_alloc P c)) c = fst (cache_alloc_cls k1 c) /\ snd (cache_alloc P c) = snd (cache_alloc_cls k1 c)
               /\ (forall c', c' <> c -> get_cls (fst (cache_alloc P c)) c' = get_cls P c')).
  { unfold cache_alloc. rewrite EQ1. destruct (cache_alloc_cls k1 c) as [kp v]. cbn [fst snd]. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
    split; [apply get_cls_set_same; [exact LEN| lia]|]. split; [reflexivity|]. intros c' NE; apply get_cls_set_off; assumption. }
  destruct EP as (EK & EV & OTH). rewrite EV.
  pose proof (cache_pop_free k1 c 0 Lcnt CP1 ND) as (INV & _ & AU).
  apply (held_ok_pop P1 (fst (cache_alloc P c)) hs c _ HO1 Hc WF1 INV).
  - intros c' NE. rewrite (OTH c' NE), (OTH1 c' NE). reflexivity.
  - rewrite EK. exact AU.
  - intros x. rewrite EK. pose proof (cache_pop_free k1 c x Lcnt CP1 ND) as (_ & FR & _). exact FR.
Qed.

Lemma bpair_map : forall l, map bpair l = map (fun v => (K_BCLASS, v)) (map qb_v l).
Proof. intros l. rewrite map_map. reflexivity. Qed.

Lemma tc_of_app : forall a b, Permutation (tc_of (a ++ b)) (tc_of a ++ tc_of b).
Proof.
  intros a b. unfold tc_of. rewrite map_app, !flat_map_app, <- !app_assoc. apply Permutation_app_head.
  rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma tsc_of_app : forall a b, tsc_of (a ++ b) = tsc_of a ++ tsc_of b.
Proof. intros a b. unfold tsc_of. rewrite !flat_map_app. reflexivity. Qed.
Lemma tc_of_perm : forall a b, Permutation (map qb_v a) (map qb_v b) -> Permutation (flat_map qb_chunks a) (flat_map qb_chunks b) ->
  Permutation (tc_of a) (tc_of b) /\ Permutation (tsc_of a) (tsc_of b).
Proof.
  intros a b PV PC. unfold tc_of, tsc_of. split.
  - apply Permutation_app; [rewrite !bpair_map; apply Permutation_map; exact PV| apply Permutation_flat_map; exact PC].
  - apply Permutation_flat_map; exact PC.
Qed.

Lemma enq_books : forall l ch v,
  Permutation (tc_of (q_enq l ch v)) ((if need_batch l then [(K_BCLASS, v)] else []) ++ tc_of l ++ prim_of ch)
  /\ tsc_of (q_enq l ch v) = tsc_of l ++ sec_of ch.
Proof.
  intros l ch v. unfold tc_of, tsc_of. rewrite q_enq_chunks, !flat_map_app. cbn [flat_map]. rewrite !app_nil_r. split; [| reflexivity].
  rewrite bpair_map, q_enq_vs, map_app, <- bpair_map. destruct (need_batch l); cbn [map app].
  - rewrite <- app_assoc. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite app_assoc. apply Permutation_refl.
  - rewrite app_nil_r, app_assoc. apply Permutation_refl.
Qed.

Lemma sel_books : forall gl,
  Permutation (map qb_v (drain_todo gl ++ drain_rest gl)) (map qb_v gl)
  /\ Permutation (flat_map qb_chunks (drain_todo gl ++ drain_rest gl)) (flat_map qb_chunks gl).
Proof.
  intros gl. unfold drain_todo, drain_rest. destruct (Q_MAX <? qbytes gl); [| split; apply Permutation_refl].
  rewrite (q_recycle_sel_eq gl). cbv zeta. cbn [fst snd].
  set (d := if (Q_BBYTES * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? Q_BBYTES * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])).
  rewrite <- app_assoc, (q_dequeue_app (fst d) (qbytes (fst d)) Q_MIN).
  assert (DD : Permutation (map qb_v (snd d ++ fst d)) (map qb_v gl) /\ flat_map qb_chunks (snd d) = [] /\ flat_map qb_chunks (fst d) = flat_map qb_chunks gl).
  { subst d. destruct ((Q_BBYTES * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? Q_BBYTES * Z.of_nat (length gl) * 200)).
    - destruct gl as [|b rest]; [cbn; split; [apply Permutation_refl| split; reflexivity]|]. cbn [q_merge_list].
      destruct (q_merge_chunks rest b) as [E1 E2]. split; [| split; assumption].
      eapply Permutation_trans; [| exact (q_merge_perm rest b)]. rewrite !map_app. apply Permutation_app_comm.
    - cbn [fst snd app]. split; [apply Permutation_refl| split; reflexivity]. }
  destruct DD as (D1 & D2 & D3). split; [exact D1|]. rewrite flat_map_app, D2, D3. apply Permutation_refl.
Qed.

Lemma put_books : forall P glob loc ch,
  let VN := snd (enq_prim P loc) in
  Permutation (tc_of (put_todo P glob loc ch) ++ tc_of (put_glob P glob loc ch ++ put_loc P loc ch))
              ((if need_batch loc then [(K_BCLASS, VN)] else []) ++ tc_of (glob ++ loc) ++ prim_of ch)
  /\ Permutation (tsc_of (put_todo P glob loc ch) ++ tsc_of (put_glob P glob loc ch ++ put_loc P loc ch)) (tsc_of (glob ++ loc) ++ sec_of ch).
Proof.
  intros P glob loc ch VN.
  assert (GL : Permutation (tc_of (glob ++ put_loc' P loc ch)) ((if need_batch loc then [(K_BCLASS, VN)] else []) ++ tc_of (glob ++ loc) ++ prim_of ch)
               /\ Permutation (tsc_of (glob ++ put_loc' P loc ch)) (tsc_of (glob ++ loc) ++ sec_of ch)).
  { unfold put_loc'. destruct (enq_books loc ch VN) as [B1 B2]. fold VN. split.
    - eapply Permutation_trans; [apply tc_of_app|]. eapply Permutation_trans; [apply Permutation_app_head; exact B1|].
      eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head.
      rewrite app_assoc. apply Permutation_app_tail. apply Permutation_sym. apply tc_of_app.
    - rewrite !tsc_of_app, B2, app_assoc. apply Permutation_refl. }
  destruct GL as [G1 G2]. unfold put_todo, put_glob, put_loc. destruct (pq_drains P loc ch).
  - rewrite app_nil_r. destruct (sel_books (glob ++ put_loc' P loc ch)) as [S1 S2].
    destruct (tc_of_perm _ _ S1 S2) as [T1 T2]. split.
    + eapply Permutation_trans; [apply Permutation_sym; apply tc_of_app|]. eapply Permutation_trans; [exact T1| exact G1].
    + rewrite <- tsc_of_app. eapply Permutation_trans; [exact T2| exact G2].
  - cbn [app]. unfold tc_of at 1. unfold tsc_of at 1. cbn [map flat_map app]. split; [exact G1| exact G2].
Qed.

Section PUT.
Context {HC : HasCeiling}.
Variable AL : alayout.

#[using="Type"] Lemma pre_pop_held : forall P c hs, 1 <= c <= 31 -> length (pr_cls P) = 32%nat -> pclass_wf c (get_cls P c) ->
  (p_cnt (get_cls P c) = 0 -> refill_budget c (get_cls P c)) -> held_ok P hs -> held_ok (pre_pop P c) hs.
Proof.
  intros P c hs Hc LEN WF BUD HO. destruct (pre_pop_facts P c Hc LEN WF BUD) as (WF1 & CP1 & LEN1 & OTH1 & EQ1 & _ & EK1).
  pose proof WF as (_ & _ & _ & _ & _ & _ & AU0 & _ & _ & AUS & _). pose proof (class_size_mod16 c Hc) as CM.
  apply (held_ok_mono P (pre_pop P c) hs HO). intros c0 v0 Hin. destruct (Z.eq_dec c0 c) as [->|NE]; [| rewrite (OTH1 c0 NE); split; [lia| intros HI; left; exact HI]].
  rewrite EK1. destruct (p_cnt (get_cls P c) =? 0); [| split; [lia| intros HI; left; exact HI]].
  split; [apply refill_au; [exact Hc| lia]|]. intros HI. apply (refill_free (get_cls P c) c v0 Hc); [| exact HI].
  clear - AUS CM. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma pinv_enq : forall P S loc hs secs, pinv AL (P, S) hs secs -> pclass_wf K_BCLASS (get_cls P K_BCLASS) ->
  (p_cnt (get_cls P K_BCLASS) = 0 -> refill_budget K_BCLASS (get_cls P K_BCLASS)) ->
  pinv AL (fst (enq_prim P loc), S) ((if need_batch loc then [(K_BCLASS, snd (enq_prim P loc))] else []) ++ hs) secs.
Proof.
  intros P S loc hs secs (LEN & HO & CV & CA & SEP & COK & PSE) WF BUD. cbn [fst snd] in *. unfold enq_prim. destruct (need_batch loc); [| cbn [fst snd app]; unfold pinv; cbn [fst snd]; tauto].
  rewrite enq_P1_eq. assert (H24 : 1 <= K_BCLASS <= 31) by lia.
  destruct (pre_pop_facts P K_BCLASS H24 LEN WF BUD) as (WF1 & CP1 & LEN1 & _ & _ & CA1 & _).
  pose proof (pre_pop_cover P K_BCLASS hs H24 LEN WF CV) as CV1. pose proof (pre_pop_held P K_BCLASS hs H24 LEN WF BUD HO) as HO1.
  set (P1 := pre_pop P K_BCLASS) in *.
  assert (NOB : p_cnt (get_cls P1 K_BCLASS) = 0 -> refill_budget K_BCLASS (get_cls P1 K_BCLASS)) by (intros Z0; exfalso; lia).
  destruct (cover_cache_alloc P1 K_BCLASS hs H24 LEN1 WF1 NOB CV1) as (CV2 & CA2 & LEN2).
  pose proof (held_cache_alloc P1 K_BCLASS hs H24 LEN1 WF1 NOB HO1) as HO2.
  unfold pinv. cbn [fst snd app]. split; [exact LEN2|]. split; [exact HO2|]. split; [exact CV2|].
  split; [rewrite CA2, CA1, CA, sum_cs_cons; cbn [fst]; lia|]. split; [exact SEP|]. split; [exact COK| exact PSE].
Qed.

#[using="Type"] Lemma pinv_put : forall P S glob loc ch hrest secs,
  pinv AL (P, S) (tc_of (glob ++ loc) ++ prim_of ch ++ hrest) (tsc_of (glob ++ loc) ++ sec_of ch ++ secs) ->
  pclass_wf K_BCLASS (get_cls P K_BCLASS) -> (p_cnt (get_cls P K_BCLASS) = 0 -> refill_budget K_BCLASS (get_cls P K_BCLASS)) ->
  pinv AL (dorecycle (fst (enq_prim P loc), S) (put_todo P glob loc ch))
       (tc_of (put_glob P glob loc ch ++ put_loc P loc ch) ++ hrest) (tsc_of (put_glob P glob loc ch ++ put_loc P loc ch) ++ secs).
Proof.
  intros P S glob loc ch hrest secs PI WF BUD. pose proof (pinv_enq P S loc _ _ PI WF BUD) as P1.
  destruct (put_books P glob loc ch) as [B1 B2]. cbv zeta in B1.
  apply pinv_dorecycle. eapply pinv_perm; [| | exact P1].
  - pose proof (Permutation_app_tail hrest (Permutation_sym B1)) as B1'. unfold tc_of at 2 in B1'. rewrite <- !app_assoc in B1'. exact B1'.
  - pose proof (Permutation_app_tail secs (Permutation_sym B2)) as B2'. unfold tsc_of at 2 in B2'. rewrite <- !app_assoc in B2'. exact B2'.
Qed.

#[using="Type"] Lemma put_chunks : forall P glob loc ch,
  Permutation (flat_map qb_chunks (put_todo P glob loc ch) ++ flat_map qb_chunks (put_glob P glob loc ch ++ put_loc P loc ch))
              (flat_map qb_chunks (glob ++ loc) ++ [ch]).
Proof.
  intros P glob loc ch.
  assert (GL : flat_map qb_chunks (glob ++ put_loc' P loc ch) = flat_map qb_chunks (glob ++ loc) ++ [ch]).
  { unfold put_loc'. rewrite !flat_map_app, q_enq_chunks, app_assoc. reflexivity. }
  unfold put_todo, put_glob, put_loc. destruct (pq_drains P loc ch).
  - rewrite app_nil_r, <- flat_map_app, <- GL. exact (proj2 (sel_books (glob ++ put_loc' P loc ch))).
  - cbn [flat_map app]. rewrite GL. apply Permutation_refl.
Qed.

#[using="Type"] Lemma q_dequeue_rest_bytes : forall l mn, 0 <= mn -> qbytes (snd (q_dequeue l (qbytes l) mn)) <= mn.
Proof.
  induction l as [|b l IH]; intros mn Hmn; [cbn; lia|].
  destruct (Z.ltb_spec mn (qbytes (b :: l))) as [K|K].
  - rewrite (q_dequeue_step b l _ mn K). cbn [snd]. replace (qbytes (b :: l) - qb_size b) with (qbytes l) by (cbn [qbytes fold_right]; fold (qbytes l); lia).
    exact (IH mn Hmn).
  - rewrite (q_dequeue_stop (b :: l) _ mn K). cbn [snd]. exact K.
Qed.

#[using="Type"] Lemma sel_wf : forall gl, Forall qbatch_wf gl -> Forall qbatch_wf (drain_rest gl) /\ qbytes (drain_rest gl) <= Q_MAX.
Proof.
  intros gl FW. unfold drain_rest. destruct (Z.ltb_spec Q_MAX (qbytes gl)) as [K|K]; [| split; [exact FW| exact K]].
  rewrite (q_recycle_sel_eq gl). cbv zeta. cbn [fst snd].
  set (d := if (Q_BBYTES * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? Q_BBYTES * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])).
  assert (FD : Forall qbatch_wf (fst d)).
  { subst d. destruct ((Q_BBYTES * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? Q_BBYTES * Z.of_nat (length gl) * 200)); [| exact FW].
    destruct gl as [|b rest]; [constructor|]. cbn [q_merge_list]. exact (q_merge_wf rest b FW). }
  split.
  - rewrite <- (q_dequeue_app (fst d) (qbytes (fst d)) Q_MIN) in FD. apply Forall_app in FD as [_ FR]. exact FR.
  - pose proof (q_dequeue_rest_bytes (fst d) Q_MIN ltac:(lia)) as QB. lia.
Qed.

#[using="Type"] Lemma put_quar_wf : forall P glob loc ch, Forall qbatch_wf (loc ++ glob) -> qbytes glob <= Q_MAX -> qchunk_wf ch ->
  (need_batch loc = true -> 0 <= snd (enq_prim P loc) /\ (16 * snd (enq_prim P loc)) mod Q_BBYTES = 0) ->
  quar_wf (mkAQ (put_loc P loc ch) (put_glob P glob loc ch)).
Proof.
  intros P glob loc ch FW QG WFC NV. apply Forall_app in FW as [FL FG].
  pose proof (q_enq_wf loc ch (snd (enq_prim P loc)) FL WFC NV) as FL'. fold (put_loc' P loc ch) in FL'.
  unfold quar_wf, put_loc, put_glob. cbn [q_loc q_glob]. unfold pq_drains. destruct (Z.ltb_spec Q_CACHE (qbytes (put_loc' P loc ch))) as [K|K].
  - destruct (sel_wf (glob ++ put_loc' P loc ch) ltac:(apply Forall_app; split; assumption)) as [S1 S2].
    cbn [app]. split; [exact S1|]. split; [cbn; lia| exact S2].
  - split; [apply Forall_app; split; assumption|]. split; [exact K| exact QG].
Qed.

End PUT.

Definition ch_cls_ok (ch : qchunk) : Prop :=
  match qc_kind ch with QPrim c _ => c = a0_cls (qc_n ch) /\ c <> 0
  | QSec sc => a0_cls (qc_n ch) = 0 /\ sc_msize sc <= qc_n ch + 16384
  end.

Definition MH (c : Z) : Z := A0_CAP c / a0_csz c + A0_QB / (a0_nmin c + 8) + (if c =? K_BCLASS then A0_QB / Q_BBYTES + 2 else 0).
Definition PM (c : Z) : Z := rup (a0_csz c * (MH c + 16)) K_MAP.
Definition cls_cnt (c : Z) (chs : list qchunk) : Z :=
  Z.of_nat (length (List.filter (fun ch => match qc_kind ch with QPrim c' _ => c' =? c | QSec _ => false end) chs)).

Lemma csz_class_size : forall c, 1 <= c <= 31 -> a0_csz c = class_size c.
Proof.
  intros c Hc. pose proof (range_check (fun c => a0_csz c =? class_size c) 1 31 ltac:(vm_compute; reflexivity) c ltac:(lia)) as X0.
  cbn beta in X0. apply Z.eqb_eq in X0. exact X0.
Qed.
Lemma PM_fits : forall c, 1 <= c <= 31 -> 0 <= PM c /\ PM c + 8 * class_size c + K_MAP <= FA_OFF.
Proof.
  intros c Hc. pose proof (range_check (fun c => (0 <=? PM c) && (PM c + 8 * class_size c + K_MAP <=? FA_OFF)) 1 31 ltac:(vm_compute; reflexivity) c ltac:(lia)) as X0.
  cbn beta in X0. apply andb_true_iff in X0 as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. split; assumption.
Qed.
Lemma MH_facts : forall c, 1 <= c <= 31 -> 0 <= MH c /\ 1 <= a0_nmin c /\ 32 <= a0_csz c.
Proof.
  intros c Hc. pose proof (range_check (fun c => (0 <=? MH c) && (1 <=? a0_nmin c) && (32 <=? a0_csz c)) 1 31 ltac:(vm_compute; reflexivity) c ltac:(lia)) as X0.
  cbn beta in X0. apply andb_true_iff in X0 as [X0 X3]. apply andb_true_iff in X0 as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.leb_le in X3. lia.
Qed.
Lemma refill_budget_of_mu : forall c k, 1 <= c <= 31 -> pclass_wf c k -> p_mu k + 8 * class_size c + K_MAP <= FA_OFF -> refill_budget c k.
Proof.
  intros c k Hc WF MU. pose proof (pfa_bound c k Hc WF) as B. pose proof (class_size_pos c Hc) as CS.
  pose proof WF as (Lnf & Lcnt & CNT & _ & _ & _ & AU & _ & _ & AUM & _ & ND & FB & _). apply NoDup_ListNoDup in ND.
  pose proof (nodup_slots _ (class_size c) (p_au k) ltac:(lia) ltac:(lia) ND FB) as NS. rewrite length_app, Nat2Z.inj_add, <- Lnf, <- Lcnt in NS.
  unfold refill_budget. split; [exact MU|].
  assert (Q1 : (p_mu k + 8 * class_size c + K_MAP - p_au k) / class_size c <= (FA_OFF - p_au k) / class_size c) by (apply Z.div_le_mono; lia).
  assert (Q2 : p_nf k * class_size c + ((FA_OFF - p_au k) / class_size c) * class_size c <= FA_OFF).
  { pose proof (Z.mul_div_le (FA_OFF - p_au k) (class_size c) ltac:(lia)). nia. }
  assert (Q3 : (p_nf k + (FA_OFF - p_au k) / class_size c) * 32 <= FA_OFF) by nia.
  lia.
Qed.

Lemma a0_nmin_le : forall n, 1 <= n -> a0_cls n <> 0 -> a0_nmin (a0_cls n) <= n.
Proof.
  intros n Hn NZ. destruct (Z_le_gt_dec n 65536) as [LE|GT].
  - pose proof (a0_chk_ok (fun n => (a0_cls n =? 0) || (a0_nmin (a0_cls n) <=? n)) (Z.to_nat 65536) 1 ltac:(vm_compute; reflexivity) n ltac:(lia)) as X0.
    cbv beta in X0. apply orb_true_iff in X0 as [X0|X0]; [apply Z.eqb_eq in X0; contradiction| apply Z.leb_le in X0; exact X0].
  - exfalso. apply NZ. unfold a0_cls. replace (a0_need n <=? 65536) with false; [reflexivity|]. symmetry. apply Z.leb_gt.
    unfold a0_need. assert (n <= (Z.max n 8 + 7) / 8 * 8) by (Z.div_mod_to_equations; lia).
    assert (0 <= Z.shiftl 16 (a0_rzlog n)) by (apply Z.shiftl_nonneg; lia). lia.
Qed.

Lemma held_cls_app : forall c a b, length (held_cls c (a ++ b)) = (length (held_cls c a) + length (held_cls c b))%nat.
Proof. intros c a b. unfold held_cls. rewrite List.filter_app, map_app, length_app. reflexivity. Qed.
Lemma held_cls_bpairs : forall c gl, length (held_cls c (map bpair gl)) = if c =? K_BCLASS then length gl else 0%nat.
Proof.
  intros c gl. unfold held_cls. rewrite length_map. induction gl as [|b gl IH]; [destruct (c =? K_BCLASS); reflexivity|].
  cbn [map List.filter bpair fst]. rewrite (Z.eqb_sym K_BCLASS c). destruct (c =? K_BCLASS); cbn [length]; rewrite IH; reflexivity.
Qed.
Lemma held_cls_chunks : forall c chs, Z.of_nat (length (held_cls c (flat_map prim_of chs))) = cls_cnt c chs.
Proof.
  intros c chs. unfold cls_cnt. f_equal. unfold held_cls. rewrite length_map. induction chs as [|ch chs IH]; [reflexivity|].
  cbn [flat_map List.filter]. rewrite List.filter_app, length_app, IH. unfold prim_of. destruct (qc_kind ch) as [c' v'|sc]; [| reflexivity].
  cbn [List.filter fst]. destruct (c' =? c); reflexivity.
Qed.
Lemma cls_cnt_app : forall c a b, cls_cnt c (a ++ b) = cls_cnt c a + cls_cnt c b.
Proof. intros c a b. unfold cls_cnt. rewrite List.filter_app, length_app. lia. Qed.
Lemma cls_cnt_nonneg : forall c a, 0 <= cls_cnt c a. Proof. intros. unfold cls_cnt. lia. Qed.

Definition wsum (chs : list qchunk) : Z := fold_right (fun ch acc => qc_n ch + 8 + acc) 0 chs.
Lemma wsum_cnt : forall c chs, 1 <= c <= 31 -> Forall qchunk_wf chs -> Forall ch_cls_ok chs -> cls_cnt c chs * (a0_nmin c + 8) <= wsum chs.
Proof.
  intros c chs Hc. induction chs as [|ch chs IH]; intros FW FC; [unfold cls_cnt, wsum; cbn [List.filter length fold_right Z.of_nat]; lia|].
  apply Forall_cons_iff in FW as [(_ & _ & N1 & _) FW]. apply Forall_cons_iff in FC as [CK FC]. specialize (IH FW FC).
  change (ch :: chs) with ([ch] ++ chs). rewrite cls_cnt_app. cbn [wsum fold_right app]. fold (wsum chs).
  unfold cls_cnt at 1. cbn [List.filter]. unfold ch_cls_ok in CK. destruct (qc_kind ch) as [c' v'|sc]; [| cbn [length Z.of_nat]; lia].
  destruct (Z.eqb_spec c' c) as [->|NE]; cbn [length Z.of_nat]; [| lia].
  destruct CK as [EC NZ]. pose proof (a0_nmin_le (qc_n ch) ltac:(lia) ltac:(rewrite <- EC; exact NZ)) as NM. rewrite <- EC in NM. lia.
Qed.
Lemma wsum_batch : forall b, qbatch_wf b -> wsum (qb_chunks b) <= qb_size b.
Proof.
  intros b (_ & _ & CNT & SZ & _). rewrite SZ. unfold qb_count in CNT.
  assert (G : forall l : list qchunk, wsum l = fold_right (fun ch acc => qc_n ch + acc) 0 l + 8 * Z.of_nat (length l)).
  { induction l as [|x l IHl]; [reflexivity|]. cbn [wsum fold_right length]. fold (wsum l). rewrite IHl. lia. }
  rewrite G. lia.
Qed.
Lemma quar_cnt : forall c gl, 1 <= c <= 31 -> Forall qbatch_wf gl -> Forall ch_cls_ok (flat_map qb_chunks gl) ->
  cls_cnt c (flat_map qb_chunks gl) * (a0_nmin c + 8) <= qbytes gl /\ Z.of_nat (length gl) * Q_BBYTES <= qbytes gl.
Proof.
  intros c gl Hc. induction gl as [|b gl IH]; intros FW FC; [unfold cls_cnt, qbytes; cbn [flat_map List.filter length fold_right Z.of_nat]; lia|].
  apply Forall_cons_iff in FW as [WB FW]. cbn [flat_map] in FC. apply Forall_app in FC as [FC1 FC2]. destruct (IH FW FC2) as [I1 I2].
  cbn [flat_map qbytes fold_right length]. fold (qbytes gl). rewrite cls_cnt_app.
  pose proof WB as (_ & _ & _ & SZ & FWC). pose proof (wsum_cnt c (qb_chunks b) Hc FWC FC1) as W1. pose proof (wsum_batch b WB) as W2.
  assert (S0 : 0 <= fold_right (fun ch acc => qc_n ch + acc) 0 (qb_chunks b)).
  { clear - FWC. induction (qb_chunks b) as [|x r IHr]; [cbn; lia|]. apply Forall_cons_iff in FWC as [(_ & _ & N1 & _) FR]. specialize (IHr FR). cbn [fold_right]. lia. }
  rewrite Nat2Z.inj_succ. split; lia.
Qed.

Lemma held_count_le : forall gl live c, 1 <= c <= 31 -> Forall qbatch_wf gl -> qbytes gl <= A0_QB -> Forall ch_cls_ok (flat_map qb_chunks gl) ->
  cls_cnt c live * a0_csz c <= A0_CAP c ->
  Z.of_nat (length (held_cls c (tc_of gl ++ flat_map prim_of live))) <= MH c.
Proof.
  intros gl live c Hc FW QB FC CAP. destruct (quar_cnt c gl Hc FW FC) as [Q1 Q2]. destruct (MH_facts c Hc) as (_ & NM & CS).
  unfold tc_of. rewrite !held_cls_app, !Nat2Z.inj_add, !held_cls_chunks, held_cls_bpairs.
  assert (L1 : cls_cnt c live <= A0_CAP c / a0_csz c) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : cls_cnt c (flat_map qb_chunks gl) <= A0_QB / (a0_nmin c + 8)) by (apply Z.div_le_lower_bound; lia).
  assert (L3 : Z.of_nat (length gl) <= A0_QB / Q_BBYTES) by (apply Z.div_le_lower_bound; lia).
  unfold MH. destruct (c =? K_BCLASS); lia.
Qed.

Lemma refill_mu_le : forall c k hc, 1 <= c <= 31 -> pclass_wf c k -> p_cnt k = 0 ->
  p_au k / class_size c <= Z.of_nat (length (cls_free k)) + hc -> hc <= MH c -> p_mu k <= PM c -> p_mu (refill k c) <= PM c.
Proof.
  intros c k hc Hc WF C0 CC HM MU. pose proof (class_size_pos c Hc) as CS. pose proof (half_range c k Hc) as (NR & _).
  pose proof WF as (Lnf & Lcnt & _ & _ & _ & _ & AU & _ & MUM & AUS & _).
  change (p_mu (refill k c)) with (p_mu (gfa_pre k c (max_count c / 2))). unfold gfa_pre. destruct (Z.ltb_spec (p_nf k) (max_count c / 2)) as [LT|GE]; [| exact MU].
  change (p_mu (populate k c (max_count c / 2 - p_nf k))) with (pop_mu k c (max_count c / 2 - p_nf k)). unfold pop_mu. cbv zeta.
  destruct (Z.leb_spec (p_au k + (max_count c / 2 - p_nf k) * class_size c) (p_mu k)) as [LE|GT]; [exact MU|].
  unfold cls_free in CC. rewrite length_app, Nat2Z.inj_add, <- Lnf, <- Lcnt, C0 in CC.
  assert (AUE : p_au k = class_size c * (p_au k / class_size c)) by (apply Z_div_exact_full_2; lia).
  set (qa := p_au k / class_size c) in *. set (n := max_count c / 2) in *. set (sz := class_size c) in *.
  assert (TOT : p_au k + (n - p_nf k) * sz <= sz * (MH c + 16)) by (rewrite AUE; clear - CC HM NR LT CS; nia).
  unfold PM in *. rewrite (csz_class_size c Hc) in *. fold sz in MU |- *.
  pose proof (rup_ge (sz * (MH c + 16)) K_MAP ltac:(lia)) as RG. pose proof (rup_mod (sz * (MH c + 16)) K_MAP ltac:(lia)) as RM.
  set (pm := rup (sz * (MH c + 16)) K_MAP) in *.
  pose proof (rup_le (p_au k + (n - p_nf k) * sz - p_mu k) (pm - p_mu k) K_MAP ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, RM, MUM; reflexivity)) as RL.
  lia.
Qed.

Definition sum_mu (P : prim) : Z := fold_right Z.add 0 (map (fun i => p_mu (get_cls P (Z.of_nat i))) (seq 1 31)).

Lemma sum_upd : forall (l : list nat) (f g : nat -> Z) (c : nat) (d : Z), List.NoDup l ->
  (forall i, In i l -> i <> c -> g i = f i) -> g c = f c + d ->
  fold_right Z.add 0 (map g l) = fold_right Z.add 0 (map f l) + (if in_dec Nat.eq_dec c l then d else 0).
Proof.
  induction l as [|x l IH]; intros f g c d ND OTH EC; [cbn; lia|]. apply NoDup_cons_iff in ND as [NI ND].
  specialize (IH f g c d ND (fun i Hi => OTH i (or_intror Hi)) EC). cbn [map fold_right]. rewrite IH.
  destruct (in_dec Nat.eq_dec c (x :: l)) as [IN|NIN]; destruct (in_dec Nat.eq_dec c l) as [IN'|NIN'].
  - assert (x <> c) by (intros ->; contradiction). rewrite (OTH x (or_introl eq_refl) H). lia.
  - destruct IN as [->|IN]; [rewrite EC; lia| contradiction].
  - exfalso. apply NIN. right. exact IN'.
  - assert (x <> c) by (intros ->; apply NIN; left; reflexivity). rewrite (OTH x (or_introl eq_refl) H). lia.
Qed.

Lemma sum_mu_upd : forall P P' c d, 1 <= c <= 31 ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> p_mu (get_cls P' c') = p_mu (get_cls P c')) ->
  p_mu (get_cls P' c) = p_mu (get_cls P c) + d -> sum_mu P' = sum_mu P + d.
Proof.
  intros P P' c d Hc OTH EC. unfold sum_mu.
  rewrite (sum_upd (seq 1 31) (fun i => p_mu (get_cls P (Z.of_nat i))) (fun i => p_mu (get_cls P' (Z.of_nat i))) (Z.to_nat c) d (seq_NoDup 31 1)).
  - destruct (in_dec Nat.eq_dec (Z.to_nat c) (seq 1 31)) as [IN|NIN]; [reflexivity|]. exfalso. apply NIN. apply in_seq. lia.
  - intros i Hi NE. apply in_seq in Hi. apply OTH; lia.
  - cbv beta. rewrite Z2Nat.id by lia. exact EC.
Qed.
Lemma sum_mu_ext : forall P P', (forall c, 1 <= c <= 31 -> p_mu (get_cls P' c) = p_mu (get_cls P c)) -> sum_mu P' = sum_mu P.
Proof. intros P P' EX. rewrite (sum_mu_upd P P' 1 0 ltac:(lia) (fun c' Hc' _ => EX c' Hc') ltac:(rewrite (EX 1 ltac:(lia)); lia)). lia. Qed.
Lemma sum_mu_bound : forall P B, 0 <= B -> (forall c, 1 <= c <= 31 -> 0 <= p_mu (get_cls P c) <= B) -> 0 <= sum_mu P <= 31 * B.
Proof.
  intros P B HB BD. unfold sum_mu.
  assert (G : forall l : list nat, (forall i, In i l -> (1 <= i <= 31)%nat) ->
            0 <= fold_right Z.add 0 (map (fun i => p_mu (get_cls P (Z.of_nat i))) l) <= Z.of_nat (length l) * B).
  { induction l as [|x l IH]; intros RNG; [cbn; lia|]. cbn [map fold_right length]. rewrite Nat2Z.inj_succ.
    specialize (IH (fun i Hi => RNG i (or_intror Hi))). pose proof (BD (Z.of_nat x) ltac:(specialize (RNG x (or_introl eq_refl)); lia)). lia. }
  specialize (G (seq 1 31) ltac:(intros i Hi; apply in_seq in Hi; lia)). rewrite length_seq in G. exact G.
Qed.

Section MU.
Context {HC : HasCeiling}.
Variable AL : alayout.
Definition same_mu (X X' : pstate) : Prop :=
  (forall c, 1 <= c <= 31 -> p_mu (get_cls (fst X') c) = p_mu (get_cls (fst X) c)) /\ pr_cmapped (fst X') = pr_cmapped (fst X).
#[using="Type"] Lemma same_mu_refl : forall X, same_mu X X. Proof. intros X. split; [intros; reflexivity| reflexivity]. Qed.
#[using="Type"] Lemma same_mu_trans : forall X1 X2 X3, same_mu X1 X2 -> same_mu X2 X3 -> same_mu X1 X3.
Proof. intros X1 X2 X3 [A1 B1] [A2 B2]. split; [intros c Hc; rewrite (A2 c Hc); exact (A1 c Hc)| rewrite B2; exact B1]. Qed.

#[using="Type"] Lemma cdealloc_same_mu : forall P c v, 1 <= c <= 31 -> length (pr_cls P) = 32%nat ->
  (forall c', 1 <= c' <= 31 -> p_mu (get_cls (cache_dealloc P c v) c') = p_mu (get_cls P c')) /\ pr_cmapped (cache_dealloc P c v) = pr_cmapped P.
Proof.
  intros P c v Hc LEN. split; [| reflexivity]. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [| rewrite (get_cls_cdealloc_other P c v c' Hc NE); reflexivity].
  assert (EK : get_cls (cache_dealloc P c v) c = cache_dealloc_cls (get_cls P c) c v).
  { unfold cache_dealloc. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
  rewrite EK. unfold cache_dealloc_cls. destruct (p_cnt (get_cls P c) =? max_count c); reflexivity.
Qed.

#[using="Type"] Lemma recycle1_same_mu : forall X ch hs secs, pinv AL X (prim_of ch ++ hs) secs -> same_mu X (recycle1 X ch).
Proof.
  intros X ch hs secs (LEN & HO & _). unfold recycle1, prim_of in *. destruct (qc_kind ch) as [c v|sc]; [| split; [intros; reflexivity| reflexivity]].
  destruct HO as [_ FH]. apply Forall_cons_iff in FH as [(Hc & _) _]. cbn [fst] in Hc.
  destruct (cdealloc_same_mu (fst X) c v Hc LEN) as [A B]. split; [exact A| exact B].
Qed.

#[using="Type"] Lemma chunks_same_mu : forall chs X hs secs,
  pinv AL X (flat_map prim_of chs ++ hs) (flat_map sec_of chs ++ secs) -> same_mu X (recycle_chunks X chs).
Proof.
  induction chs as [|ch chs IH]; intros X hs secs PI; [apply same_mu_refl|]. cbn [recycle_chunks flat_map] in *. rewrite <- !app_assoc in PI.
  eapply same_mu_trans; [exact (recycle1_same_mu X ch _ _ PI)|]. apply (IH _ hs secs).
  destruct (qc_kind ch) as [c v|sc] eqn:EK; unfold prim_of, sec_of in PI; rewrite EK in PI; cbn [app] in PI.
  - exact (pinv_prim AL X ch c v _ _ EK PI).
  - exact (pinv_sec AL X ch sc _ _ EK PI).
Qed.

#[using="Type"] Lemma batch_same_mu : forall b X hs secs,
  pinv AL X (bpair b :: flat_map prim_of (qb_chunks b) ++ hs) (flat_map sec_of (qb_chunks b) ++ secs) -> same_mu X (recycle_batch X b).
Proof.
  intros b X hs secs PI. unfold recycle_batch. cbv zeta.
  assert (PIc : pinv AL X (flat_map prim_of (qb_chunks b) ++ bpair b :: hs) (flat_map sec_of (qb_chunks b) ++ secs))
    by (eapply pinv_perm; [| apply Permutation_refl| exact PI]; apply Permutation_middle).
  pose proof (chunks_same_mu _ X _ _ PIc) as M1. pose proof (pinv_chunks AL _ X _ _ PIc) as P1.
  set (X1 := recycle_chunks X (qb_chunks b)) in *. eapply same_mu_trans; [exact M1|].
  pose proof (recycle1_same_mu X1 (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) hs secs P1) as M2. unfold recycle1 in M2. cbn [qc_kind] in M2. exact M2.
Qed.

#[using="Type"] Lemma dorecycle_same_mu : forall bs X hs secs,
  pinv AL X (map bpair bs ++ flat_map prim_of (flat_map qb_chunks bs) ++ hs) (flat_map sec_of (flat_map qb_chunks bs) ++ secs) ->
  same_mu X (dorecycle X bs).
Proof.
  induction bs as [|b bs IH]; intros X hs secs PI; [apply same_mu_refl|]. cbn [dorecycle].
  assert (PIb : pinv AL X (bpair b :: flat_map prim_of (qb_chunks b) ++ (map bpair bs ++ flat_map prim_of (flat_map qb_chunks bs) ++ hs))
                       (flat_map sec_of (qb_chunks b) ++ (flat_map sec_of (flat_map qb_chunks bs) ++ secs))).
  { cbn [map flat_map app] in PI. rewrite !flat_map_app in PI. eapply pinv_perm; [| | exact PI].
    - apply perm_skip. rewrite <- !app_assoc. eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head. apply Permutation_refl.
    - rewrite <- app_assoc. apply Permutation_refl. }
  eapply same_mu_trans; [exact (batch_same_mu b X _ _ PIb)|]. exact (IH _ hs secs (pinv_batch AL b X _ _ PIb)).
Qed.

#[using="Type"] Lemma enq_mu : forall P loc, length (pr_cls P) = 32%nat ->
  let PN := fst (enq_prim P loc) in let k := get_cls P K_BCLASS in
  (forall c, 1 <= c <= 31 -> c <> K_BCLASS -> get_cls PN c = get_cls P c)
  /\ p_mu (get_cls PN K_BCLASS) = (if enq_refills P loc then p_mu (refill k K_BCLASS) else p_mu k)
  /\ pr_cmapped PN = pr_cmapped P + (p_mu (get_cls PN K_BCLASS) - p_mu k).
Proof.
  intros P loc LEN. cbv zeta. unfold enq_prim, enq_refills. destruct (need_batch loc); cbn [andb fst]; [| split; [intros; reflexivity| split; [reflexivity| lia]]].
  unfold enq_P1. destruct (Z.eqb_spec (p_cnt (get_cls P K_BCLASS)) 0) as [C0|CN].
  - destruct (refill_cnt K_BCLASS (get_cls P K_BCLASS) ltac:(lia)) as [RC R1].
    assert (EK : get_cls (refill_prim P K_BCLASS) K_BCLASS = refill (get_cls P K_BCLASS) K_BCLASS).
    { unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
    unfold cache_alloc. rewrite EK. unfold cache_alloc_cls. replace (p_cnt (refill (get_cls P K_BCLASS) K_BCLASS) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [fst]. unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
    split; [intros c Hc NE; rewrite get_cls_set_off by (first [lia | assumption]); rewrite nth_set_nth_other by lia; reflexivity|].
    rewrite get_cls_set_same by (first [rewrite set_nth_length; exact LEN | lia]). cbn [p_mu]. split; [reflexivity| lia].
  - unfold cache_alloc, cache_alloc_cls. replace (p_cnt (get_cls P K_BCLASS) =? 0) with false by (symmetry; apply Z.eqb_neq; exact CN).
    cbn [fst]. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
    split; [intros c Hc NE; rewrite get_cls_set_off by (first [lia | assumption]); reflexivity|].
    rewrite get_cls_set_same by (first [exact LEN | lia]). cbn [p_mu]. split; [reflexivity| lia].
Qed.

End MU.


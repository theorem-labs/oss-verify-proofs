(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim APrimSpec2 APrimLem APrimPop APrimPopLens APrimRefill APrimQ APrimDealloc APrimCover ASec ASecD AQuar AQuarM
                        AHeap F_quar_E AQuarR AQuarP F_quar_As F_quar_R F_quar_DR F_quar_D F_quar_P ALedger ALinkPg ALinkVm ALink ALinkPrim ALinkFree.
Import ListNotations.
Open Scope Z_scope.

Definition pwf_all (P : prim) : Prop := forall c, 1 <= c <= 31 -> pclass_wf c (get_cls P c).

Lemma cdealloc_cls_wf : forall c k v, 1 <= c <= 31 -> pclass_wf c k ->
  0 <= v -> 16 * v + class_size c <= p_au k -> (16 * v) mod class_size c = 0 -> ~ In v (cls_free k) ->
  pclass_wf c (cache_dealloc_cls k c v).
Proof.
  intros c k v Hc WF V0 V1 V2 NI. rewrite cache_dealloc_cls_eq. pose proof (max_count_range c Hc) as (MR & MM).
  destruct (Z.eqb_spec (p_cnt k) (max_count c)) as [FULL|NF].
  - apply push_cls_wf; [apply drain_cls_wf; [exact Hc| exact WF| rewrite FULL; clear - MR; Z.div_mod_to_equations; lia]| | exact V0| | exact V2|].
    + unfold drain_cls. cbn [p_cnt]. rewrite FULL. clear - MR. Z.div_mod_to_equations. lia.
    + unfold drain_cls, return_to_allocator. cbn [p_au]. exact V1.
    + intros HI. apply NI. apply (proj1 (drain_cls_free k c v)). exact HI.
  - pose proof WF as (_ & _ & CNT & _). apply push_cls_wf; [exact WF| lia| exact V0| exact V1| exact V2| exact NI].
Qed.

Lemma pwf_cdealloc : forall P c v, length (pr_cls P) = 32%nat -> pwf_all P -> held1 P (c, v) -> pwf_all (cache_dealloc P c v).
Proof.
  intros P c v LEN WF (Hc & V0 & V1 & V2 & NI) c' Hc'. cbn [fst snd] in *. destruct (Z.eq_dec c' c) as [->|NE].
  - assert (EK : get_cls (cache_dealloc P c v) c = cache_dealloc_cls (get_cls P c) c v).
    { unfold cache_dealloc. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
    rewrite EK. exact (cdealloc_cls_wf c _ v Hc (WF c Hc) V0 V1 V2 NI).
  - rewrite (get_cls_cdealloc_other P c v c' Hc NE). exact (WF c' Hc').
Qed.

Lemma cache_alloc_cls_pop : forall k c, p_cnt k <> 0 -> fst (cache_alloc_cls k c) = pop_cls k.
Proof. intros k c NZ. unfold cache_alloc_cls, pop_cls. replace (p_cnt k =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity. Qed.

Lemma pwf_cache_alloc : forall P c, 1 <= c <= 31 -> length (pr_cls P) = 32%nat -> pwf_all P ->
  (p_cnt (get_cls P c) = 0 -> refill_budget c (get_cls P c)) -> pwf_all (fst (cache_alloc P c)).
Proof.
  intros P c Hc LEN WF BUD c' Hc'. destruct (pre_pop_facts P c Hc LEN (WF c Hc) BUD) as (WF1 & CP1 & LEN1 & OTH1 & EQ1 & _).
  set (k1 := get_cls (pre_pop P c) c) in *.
  assert (EP : get_cls (fst (cache_alloc P c)) c = fst (cache_alloc_cls k1 c) /\ (forall c2, c2 <> c -> get_cls (fst (cache_alloc P c)) c2 = get_cls P c2)).
  { unfold cache_alloc. rewrite EQ1. destruct (cache_alloc_cls k1 c) as [kp v]. cbn [fst snd]. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
    split; [apply get_cls_set_same; [exact LEN| lia]|]. intros c2 NE; apply get_cls_set_off; assumption. }
  destruct EP as [EK OTH]. destruct (Z.eq_dec c' c) as [->|NE]; [| rewrite (OTH c' NE); exact (WF c' Hc')].
  rewrite EK, (cache_alloc_cls_pop k1 c ltac:(lia)). exact (pop_cls_wf c k1 WF1 CP1).
Qed.

Lemma pwf_enq : forall P loc, length (pr_cls P) = 32%nat -> pwf_all P ->
  (p_cnt (get_cls P K_BCLASS) = 0 -> refill_budget K_BCLASS (get_cls P K_BCLASS)) -> pwf_all (fst (enq_prim P loc)).
Proof.
  intros P loc LEN WF BUD. unfold enq_prim. destruct (need_batch loc); [| exact WF]. rewrite enq_P1_eq.
  assert (H24 : 1 <= K_BCLASS <= 31) by lia.
  destruct (pre_pop_facts P K_BCLASS H24 LEN (WF K_BCLASS H24) BUD) as (WF1 & CP1 & LEN1 & OTH1 & _).
  apply (pwf_cache_alloc (pre_pop P K_BCLASS) K_BCLASS H24 LEN1); [| intros Z0; exfalso; lia].
  intros c Hc. destruct (Z.eq_dec c K_BCLASS) as [->|NE]; [exact WF1| rewrite (OTH1 c NE); exact (WF c Hc)].
Qed.

Definition sum_mfa (P : prim) : Z := fold_right Z.add 0 (map (fun i => p_mfa (get_cls P (Z.of_nat i))) (seq 1 31)).
Lemma sum_mfa_upd : forall P P' c d, 1 <= c <= 31 ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> p_mfa (get_cls P' c') = p_mfa (get_cls P c')) ->
  p_mfa (get_cls P' c) = p_mfa (get_cls P c) + d -> sum_mfa P' = sum_mfa P + d.
Proof.
  intros P P' c d Hc OTH EC. unfold sum_mfa.
  rewrite (sum_upd (seq 1 31) (fun i => p_mfa (get_cls P (Z.of_nat i))) (fun i => p_mfa (get_cls P' (Z.of_nat i))) (Z.to_nat c) d (seq_NoDup 31 1)).
  - destruct (in_dec Nat.eq_dec (Z.to_nat c) (seq 1 31)) as [IN|NIN]; [reflexivity|]. exfalso. apply NIN. apply in_seq. lia.
  - intros i Hi NE. apply in_seq in Hi. apply OTH; lia.
  - cbv beta. rewrite Z2Nat.id by lia. exact EC.
Qed.
Lemma sum_mfa_bound : forall P, pwf_all P -> 0 <= sum_mfa P <= 31 * K_FA_SIZE.
Proof.
  intros P WF. unfold sum_mfa.
  assert (G : forall l : list nat, (forall i, In i l -> (1 <= i <= 31)%nat) ->
            0 <= fold_right Z.add 0 (map (fun i => p_mfa (get_cls P (Z.of_nat i))) l) <= Z.of_nat (length l) * K_FA_SIZE).
  { induction l as [|x l IH]; intros RNG; [cbn; lia|]. cbn [map fold_right length]. rewrite Nat2Z.inj_succ.
    specialize (IH (fun i Hi => RNG i (or_intror Hi))). pose proof (WF (Z.of_nat x) ltac:(specialize (RNG x (or_introl eq_refl)); lia)) as (_ & _ & _ & _ & MFA & _). lia. }
  specialize (G (seq 1 31) ltac:(intros i Hi; apply in_seq in Hi; lia)). rewrite length_seq in G. exact G.
Qed.

Lemma cdealloc_mfa : forall P c v, 1 <= c <= 31 -> length (pr_cls P) = 32%nat -> pclass_wf c (get_cls P c) ->
  sum_mfa (cache_dealloc P c v) = sum_mfa P + D_cdealloc c (get_cls P c).
Proof.
  intros P c v Hc LEN WF. apply (sum_mfa_upd P (cache_dealloc P c v) c _ Hc).
  - intros c' Hc' NE. rewrite (get_cls_cdealloc_other P c v c' Hc NE). reflexivity.
  - assert (EK : get_cls (cache_dealloc P c v) c = cache_dealloc_cls (get_cls P c) c v).
    { unfold cache_dealloc. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
    rewrite EK. unfold cache_dealloc_cls, D_cdealloc, D_efa. pose proof WF as (_ & Lcnt & _). pose proof (max_count_range c Hc) as (MR & MM).
    destruct (Z.eqb_spec (p_cnt (get_cls P c)) (max_count c)) as [FULL|NF]; cbn [p_mfa return_to_allocator ensure_fa]; [| lia].
    replace (Z.of_nat (length (skipn (Z.to_nat (p_cnt (get_cls P c) - max_count c / 2)) (p_chunks (get_cls P c))))) with (max_count c / 2); [lia|].
    rewrite length_skipn. rewrite Lcnt in FULL |- *. clear - FULL MR MM. Z.div_mod_to_equations. lia.
Qed.

Section FOLDL.
Context {HC : HasCeiling}.
Variable AL : alayout.

Definition cpair (sc : schunk) : Z * Z := (sc_beg sc, sc_msize sc).
Definition linked (v : vabs) (X : pstate) : Prop := Permutation (va_chunks v) (map cpair (se_chunks (snd X))).

Definition foldrel (v : vabs) (X : pstate) (v' : vabs) (X' : pstate) (R : Z) : Prop :=
  let d := sum_mfa (fst X') - sum_mfa (fst X) in
  pwf_all (fst X') /\ linked v' X' /\ va_prim v' = va_prim v + d /\ va_nsec v' = va_nsec v /\ va_aux v' = va_aux v
  /\ R = d + d / 8 /\ d mod 8 = 0 /\ 0 <= d.

#[using="Type"] Lemma foldrel_refl : forall v X, pwf_all (fst X) -> linked v X -> foldrel v X v X 0.
Proof. intros v X WF LK. unfold foldrel. cbv zeta. rewrite Z.sub_diag. split; [exact WF|]. split; [exact LK|]. repeat split; try lia; reflexivity. Qed.

#[using="Type"] Lemma foldrel_trans : forall v X v1 X1 R1 v2 X2 R2, foldrel v X v1 X1 R1 -> foldrel v1 X1 v2 X2 R2 -> foldrel v X v2 X2 (R1 + R2).
Proof.
  intros v X v1 X1 R1 v2 X2 R2 (_ & _ & P1 & N1 & A1 & E1 & M1 & D1) (W2 & L2 & P2 & N2 & A2 & E2 & M2 & D2). unfold foldrel. cbv zeta in *.
  set (d1 := sum_mfa (fst X1) - sum_mfa (fst X)) in *. set (d2 := sum_mfa (fst X2) - sum_mfa (fst X1)) in *.
  replace (sum_mfa (fst X2) - sum_mfa (fst X)) with (d1 + d2) by (unfold d1, d2; lia).
  split; [exact W2|]. split; [exact L2|]. split; [lia|]. split; [congruence|]. split; [congruence|].
  split; [rewrite E1, E2; clear - M1 M2; Z.div_mod_to_equations; lia|]. split; [clear - M1 M2; Z.div_mod_to_equations; lia| lia].
Qed.

#[using="Type"] Lemma step_recycle1 : forall v X ch hs secs, pinv AL X (prim_of ch ++ hs) (sec_of ch ++ secs) -> pwf_all (fst X) -> linked v X ->
  sok_recycle1 v X ch /\ foldrel v X (va_recycle1 v X ch) (recycle1 X ch) (R_recycle1 X ch).
Proof.
  intros v X ch hs secs (LEN & HO & _ & _ & SEP & COK & PSE) WF LK.
  unfold sok_recycle1, va_recycle1, recycle1, R_recycle1, prim_of, sec_of in *. destruct (qc_kind ch) as [c v0|sc]; cbn [app] in *.
  - destruct HO as [_ FH]. apply Forall_cons_iff in FH as [H1 _]. pose proof H1 as (Hc & _). cbn [fst] in Hc.
    assert (SK : sok_cd c (get_cls (fst X) c)) by (split; [exact Hc| split; [exact (WF c Hc)| exact (drain_budget_wf c _ Hc (WF c Hc))]]).
    split; [exact SK|]. destruct (D_cd_facts AL c _ SK) as [D0 D8]. pose proof (cdealloc_mfa (fst X) c v0 Hc LEN (WF c Hc)) as EM.
    unfold foldrel. cbv zeta. cbn [fst snd va_cd va_prim va_chunks va_nsec va_aux]. rewrite EM.
    replace (sum_mfa (fst X) + D_cdealloc c (get_cls (fst X) c) - sum_mfa (fst X)) with (D_cdealloc c (get_cls (fst X) c)) by lia.
    split; [exact (pwf_cdealloc (fst X) c v0 LEN WF H1)|]. split; [exact LK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact D8| exact D0].
  - assert (IN : In sc (se_chunks (snd X))) by (eapply Permutation_in; [apply Permutation_sym; exact PSE| left; reflexivity]).
    assert (POS : Forall (fun c => 0 < sc_msize c) (se_chunks (snd X))).
    { eapply Forall_impl; [| exact COK]. intros d CK. pose proof (chunk_ok_msize AL d CK) as [M1 _]. lia. }
    pose proof (sc_index_nth (se_chunks (snd X)) sc SEP POS IN) as NTH.
    assert (INV : In (sc_beg sc, sc_msize sc) (va_chunks v)).
    { eapply Permutation_in; [apply Permutation_sym; exact LK|]. change (sc_beg sc, sc_msize sc) with (cpair sc). apply in_map. exact IN. }
    split; [exact INV|]. unfold foldrel. cbv zeta. cbn [fst snd va_prim va_chunks va_nsec va_aux sec_dealloc se_chunks]. rewrite Z.sub_diag.
    split; [exact WF|]. split.
    { unfold linked. cbn [va_chunks snd se_chunks]. apply (Permutation_cons_inv (a := cpair sc)).
      eapply Permutation_trans; [apply Permutation_sym; exact (rem1_perm _ _ INV)|].
      eapply Permutation_trans; [exact LK|]. exact (Permutation_map cpair (remove_at_perm _ _ _ NTH)). }
    repeat split; try lia; reflexivity.
Qed.

#[using="Type"] Lemma step_chunks : forall chs v X hs secs, pinv AL X (flat_map prim_of chs ++ hs) (flat_map sec_of chs ++ secs) -> pwf_all (fst X) -> linked v X ->
  sok_recycle_chunks v X chs /\ foldrel v X (va_recycle_chunks v X chs) (recycle_chunks X chs) (R_recycle_chunks X chs).
Proof.
  induction chs as [|ch chs IH]; intros v X hs secs PI WF LK; cbn [sok_recycle_chunks va_recycle_chunks recycle_chunks R_recycle_chunks flat_map] in *.
  - split; [exact I| exact (foldrel_refl v X WF LK)].
  - rewrite <- !app_assoc in PI. destruct (step_recycle1 v X ch _ _ PI WF LK) as [S1 F1].
    assert (PI' : pinv AL (recycle1 X ch) (flat_map prim_of chs ++ hs) (flat_map sec_of chs ++ secs)).
    { destruct (qc_kind ch) as [c v0|sc] eqn:EK; unfold prim_of, sec_of in PI; rewrite EK in PI; cbn [app] in PI;
        [exact (pinv_prim AL X ch c v0 _ _ EK PI)| exact (pinv_sec AL X ch sc _ _ EK PI)]. }
    pose proof F1 as (WF1 & LK1 & _). destruct (IH _ _ hs secs PI' WF1 LK1) as [S2 F2].
    split; [split; assumption| exact (foldrel_trans _ _ _ _ _ _ _ _ F1 F2)].
Qed.

#[using="Type"] Lemma step_batch : forall b v X hs secs,
  pinv AL X (bpair b :: flat_map prim_of (qb_chunks b) ++ hs) (flat_map sec_of (qb_chunks b) ++ secs) -> pwf_all (fst X) -> linked v X ->
  sok_recycle_batch v X b /\ foldrel v X (va_recycle_batch v X b) (recycle_batch X b) (R_recycle_batch X b).
Proof.
  intros b v X hs secs PI WF LK. unfold sok_recycle_batch, va_recycle_batch, recycle_batch, R_recycle_batch. cbv zeta.
  assert (PIc : pinv AL X (flat_map prim_of (qb_chunks b) ++ bpair b :: hs) (flat_map sec_of (qb_chunks b) ++ secs))
    by (eapply pinv_perm; [| apply Permutation_refl| exact PI]; apply Permutation_middle).
  destruct (step_chunks _ v X _ _ PIc WF LK) as [S1 F1]. pose proof (pinv_chunks AL _ X _ _ PIc) as P1. pose proof F1 as (WF1 & LK1 & _).
  set (X1 := recycle_chunks X (qb_chunks b)) in *. set (v1 := va_recycle_chunks v X (qb_chunks b)) in *.
  destruct (step_recycle1 v1 X1 (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) hs secs P1 WF1 LK1) as [S2 F2].
  unfold sok_recycle1, va_recycle1, recycle1, R_recycle1 in S2, F2. cbn [qc_kind] in S2, F2.
  split; [split; assumption| exact (foldrel_trans _ _ _ _ _ _ _ _ F1 F2)].
Qed.

#[using="Type"] Theorem step_dorecycle : forall bs v X hs secs,
  pinv AL X (map bpair bs ++ flat_map prim_of (flat_map qb_chunks bs) ++ hs) (flat_map sec_of (flat_map qb_chunks bs) ++ secs) ->
  pwf_all (fst X) -> linked v X ->
  sok_dorecycle v X bs /\ foldrel v X (va_dorecycle v X bs) (dorecycle X bs) (R_dorecycle X bs).
Proof.
  induction bs as [|b bs IH]; intros v X hs secs PI WF LK; cbn [sok_dorecycle va_dorecycle dorecycle R_dorecycle] in *.
  - split; [exact I| exact (foldrel_refl v X WF LK)].
  - assert (PIb : pinv AL X (bpair b :: flat_map prim_of (qb_chunks b) ++ (map bpair bs ++ flat_map prim_of (flat_map qb_chunks bs) ++ hs))
                         (flat_map sec_of (qb_chunks b) ++ (flat_map sec_of (flat_map qb_chunks bs) ++ secs))).
    { cbn [map flat_map app] in PI. rewrite !flat_map_app in PI. eapply pinv_perm; [| | exact PI].
      - apply perm_skip. rewrite <- !app_assoc. eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head. apply Permutation_refl.
      - rewrite <- app_assoc. apply Permutation_refl. }
    destruct (step_batch b v X _ _ PIb WF LK) as [S1 F1]. pose proof F1 as (WF1 & LK1 & _).
    destruct (IH _ _ hs secs (pinv_batch AL b X _ _ PIb) WF1 LK1) as [S2 F2].
    split; [split; assumption| exact (foldrel_trans _ _ _ _ _ _ _ _ F1 F2)].
Qed.

#[using="Type"] Corollary R_dorecycle_bound : forall bs v X hs secs,
  pinv AL X (map bpair bs ++ flat_map prim_of (flat_map qb_chunks bs) ++ hs) (flat_map sec_of (flat_map qb_chunks bs) ++ secs) ->
  pwf_all (fst X) -> linked v X ->
  8 * R_dorecycle X bs <= 9 * (31 * K_FA_SIZE - sum_mfa (fst X)).
Proof.
  intros bs v X hs secs PI WF LK. destruct (step_dorecycle bs v X hs secs PI WF LK) as [_ (WF' & _ & _ & _ & _ & ER & M8 & D0)]. cbv zeta in *.
  pose proof (sum_mfa_bound _ WF') as [_ B]. rewrite ER. clear - M8 D0 B. Z.div_mod_to_equations. lia.
Qed.

End FOLDL.

Lemma enq_mfa : forall P loc, length (pr_cls P) = 32%nat ->
  let PN := fst (enq_prim P loc) in let k := get_cls P K_BCLASS in
  (forall c, 1 <= c <= 31 -> c <> K_BCLASS -> get_cls PN c = get_cls P c)
  /\ p_mfa (get_cls PN K_BCLASS) = (if enq_refills P loc then p_mfa (refill k K_BCLASS) else p_mfa k).
Proof.
  intros P loc LEN. cbv zeta. destruct (enq_mu P loc LEN) as (EO & _). cbv zeta in EO. split; [exact EO|].
  unfold enq_prim, enq_refills. destruct (need_batch loc); cbn [andb fst]; [| reflexivity].
  unfold enq_P1. destruct (Z.eqb_spec (p_cnt (get_cls P K_BCLASS)) 0) as [C0|CN].
  - destruct (refill_cnt K_BCLASS (get_cls P K_BCLASS) ltac:(lia)) as [RC R1].
    assert (EK : get_cls (refill_prim P K_BCLASS) K_BCLASS = refill (get_cls P K_BCLASS) K_BCLASS).
    { unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
    unfold cache_alloc. rewrite EK. unfold cache_alloc_cls. replace (p_cnt (refill (get_cls P K_BCLASS) K_BCLASS) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [fst]. unfold refill_prim. cbv zeta. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
    rewrite get_cls_set_same by (first [rewrite set_nth_length; exact LEN | lia]). reflexivity.
  - unfold cache_alloc, cache_alloc_cls. replace (p_cnt (get_cls P K_BCLASS) =? 0) with false by (symmetry; apply Z.eqb_neq; exact CN).
    cbn [fst]. destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
    rewrite get_cls_set_same by (first [exact LEN | lia]). reflexivity.
Qed.

Lemma refill_D_gfa : forall k c, p_mu (refill k c) - p_mu k + (p_mfa (refill k c) - p_mfa k) = D_gfa k c (max_count c / 2).
Proof.
  intros k c. change (p_mu (refill k c)) with (p_mu (gfa_pre k c (max_count c / 2))). change (p_mfa (refill k c)) with (p_mfa (gfa_pre k c (max_count c / 2))).
  unfold gfa_pre, D_gfa. destruct (p_nf k <? max_count c / 2); [| lia]. unfold D_pop, D_efa, populate, pop_k1. cbn [p_mu p_mfa ensure_fa]. lia.
Qed.

Lemma D_enq_eq : forall P loc, length (pr_cls P) = 32%nat ->
  D_enq P loc = (sum_mu (fst (enq_prim P loc)) - sum_mu P) + (sum_mfa (fst (enq_prim P loc)) - sum_mfa P).
Proof.
  intros P loc LEN. destruct (enq_mu P loc LEN) as (EO & E24 & _). destruct (enq_mfa P loc LEN) as (_ & F24). cbv zeta in *.
  set (PN := fst (enq_prim P loc)) in *.
  rewrite (sum_mu_upd P PN K_BCLASS (p_mu (get_cls PN K_BCLASS) - p_mu (get_cls P K_BCLASS)) ltac:(lia) ltac:(intros c' Hc' NE; rewrite (EO c' Hc' NE); reflexivity) ltac:(lia)).
  rewrite (sum_mfa_upd P PN K_BCLASS (p_mfa (get_cls PN K_BCLASS) - p_mfa (get_cls P K_BCLASS)) ltac:(lia) ltac:(intros c' Hc' NE; rewrite (EO c' Hc' NE); reflexivity) ltac:(lia)).
  rewrite E24, F24. unfold D_enq. destruct (enq_refills P loc); [| lia]. pose proof (refill_D_gfa (get_cls P K_BCLASS) K_BCLASS). lia.
Qed.

From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import PEnv AHeap2 AHeapB AFreeL8.

Section FREEIN.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).

Definition va_base (v : vabs) (P : prim) : Z := va_prim v - (sum_mu P + sum_mfa P).

#[using="Type"] Theorem free_link_inputs : forall s LB m ch n l1 l2 v,
  RHEAP_B AL E s LB m -> bs_live s = l1 ++ (ch, n) :: l2 -> linked v (bs_X s) ->
  let P := bs_prim s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let X1 := (fst (enq_prim P loc), bs_sec s) in let todo := put_todo P glob loc ch in
  let X' := dorecycle X1 todo in
  let v1 := va_enq v P loc in let v' := va_dorecycle v1 X1 todo in
  (enq_refills P loc = true -> pclass_wf K_BCLASS (get_cls P K_BCLASS) /\ refill_budget K_BCLASS (get_cls P K_BCLASS))
  /\ sok_dorecycle v1 X1 todo
  /\ 8 * R_dorecycle X1 todo <= 9 * (31 * K_FA_SIZE - sum_mfa (fst X1))
  /\ linked v' X' /\ va_base v' (fst X') = va_base v P /\ va_nsec v' = va_nsec v /\ va_aux v' = va_aux v.
Proof.
  intros s LB m ch n l1 l2 v HR EL LK. cbv zeta.
  set (P := bs_prim s). set (glob := q_glob (bs_quar s)). set (loc := q_loc (bs_quar s)).
  set (hrest := flat_map prim_of (map fst (l1 ++ l2))). set (secsR := flat_map sec_of (map fst (l1 ++ l2))).
  pose proof (rheap_pinv AL E s LB m HR) as PI0. destruct (allheld_split s ch n l1 l2 EL) as [PH PS].
  pose proof (pinv_perm AL _ _ _ _ _ PH PS PI0) as PIa. clear PI0 PH PS.
  change (bs_gl s) with (glob ++ loc) in PIa. change (bs_X s) with (P, bs_sec s) in PIa. fold hrest secsR in PIa.
  pose proof (rheap_wf AL E s LB m HR) as WF0. fold P in WF0.
  pose proof (rheap_refill_budget AL E s LB m HR K_BCLASS ltac:(lia)) as RB24. fold P in RB24.
  pose proof (pinv_put_mid AL P (bs_sec s) glob loc ch hrest secsR PIa (WF0 K_BCLASS ltac:(lia)) (fun _ => RB24)) as PIm.
  pose proof PIa as (LEN & _). cbn [fst] in LEN.
  pose proof (pwf_enq P loc LEN WF0 (fun _ => RB24)) as WF1.
  assert (LK1 : linked (va_enq v P loc) (fst (enq_prim P loc), bs_sec s)) by exact LK.
  destruct (step_dorecycle AL _ _ _ _ _ PIm WF1 LK1) as [SOK FR].
  pose proof (R_dorecycle_bound AL _ _ _ _ _ PIm WF1 LK1) as RB.
  pose proof (dorecycle_same_mu AL _ _ _ _ PIm) as [MU1 _]. cbn [fst] in MU1.
  destruct FR as (_ & LK' & EP & EN & EA & _). cbv zeta in EP. cbn [fst] in EP.
  split; [intros _; split; [exact (WF0 K_BCLASS ltac:(lia))| exact RB24]|]. split; [exact SOK|]. split; [exact RB|]. split; [exact LK'|].
  split; [| split; [exact EN| exact EA]].
  unfold va_base. rewrite EP. unfold va_enq at 1. cbn [va_prim]. rewrite (D_enq_eq P loc LEN), (sum_mu_ext _ _ MU1). lia.
Qed.

End FREEIN.


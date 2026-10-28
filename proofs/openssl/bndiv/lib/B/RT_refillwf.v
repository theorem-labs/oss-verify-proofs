(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout R_sizeclass R_cache_defs R_prim_defs R_popfree R_popfree_B R_popfree_T R_getfrom R_prim_lists RT_state RT_rep RT_malstate RT_refillstmt RT_refillst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition refill_room (Σ : rtsA) (c : Z) : Prop :=
  rf_nf (pr Σ c) < MaxCount c / 2 -> ClassSize c * Z.of_nat (length (r_st (pr Σ c))) + 2 ^ 20 <= 2 ^ 31.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rf_slowb (r : regst) (c : Z) : bool := rf_nf r <? MaxCount c / 2.
Definition rf_nc (r : regst) (c : Z) : Z := if rf_slowb r c then rf_newc r c else 0.
Definition rf_mu (r : regst) (c : Z) : Z := if rf_slowb r c then r_muser r + rf_msz r c else r_muser r.
Definition rf_mf (r : regst) (c : Z) : Z := if rf_slowb r c then rf_mfa r c else r_mfa r.
Definition rf_fl2 (r : regst) (c : Z) : list Z :=
  r_fl r ++ rev (map (fun j => Z.of_nat (length (r_st r)) + Z.of_nat j) (seq 0 (Z.to_nat (rf_nc r c)))).
Definition rf_cut (r : regst) (c : Z) : nat := (length (rf_fl2 r c) - Z.to_nat (MaxCount c / 2))%nat.

Lemma fl_len_le : forall (fl : list Z) (N : nat), List.NoDup fl -> Forall (fun i => 0 <= i < Z.of_nat N) fl -> (length fl <= N)%nat.
Proof.
  intros fl N ND HF. replace N with (length (map Z.of_nat (seq 0 N))) by (rewrite length_map, length_seq; reflexivity).
  apply NoDup_incl_length; [exact ND|]. intros x Hx. pose proof (proj1 (Forall_forall _ _) HF x Hx) as (H1 & H2).
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma in_skipn_firstn : forall {X} (l : list X) k x, In x (skipn k l ++ firstn k l) <-> In x l.
Proof.
  intros X l k x. rewrite <- (firstn_skipn k l) at 3. rewrite !in_app_iff. tauto.
Qed.

Lemma in_firstn_l : forall {X} (l : list X) k x, In x (firstn k l) -> In x l.
Proof. intros X l k x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.

Lemma nodup_skipn_firstn : forall {X} (l : list X) k, List.NoDup l -> List.NoDup (skipn k l ++ firstn k l).
Proof.
  intros X l k H. rewrite <- (firstn_skipn k l) in H. exact (Permutation_NoDup (Permutation_app_comm _ _) H).
Qed.

Section RW.
Variables (r : regst) (c : Z).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis HW : reg_wf c r.
Hypothesis HROOM : rf_nf r < MaxCount c / 2 -> ClassSize c * Z.of_nat (length (r_st r)) + 2 ^ 20 <= 2 ^ 31.
#[local] Notation S := (ClassSize c).
#[local] Notation n := (MaxCount c / 2).

Lemma rf_char : refill_reg r c = mkReg (rf_mu r c) (rf_mf r c) (r_st r ++ repeat CkIdle (Z.to_nat (rf_nc r c)))
                                   (firstn (rf_cut r c) (rf_fl2 r c))
  /\ refill_ca r c = skipn (rf_cut r c) (rf_fl2 r c).
Proof using Hc HW.
  unfold rf_cut, rf_fl2, rf_nc, rf_mu, rf_mf, rf_slowb. destruct (Z.ltb_spec (rf_nf r) n) as [X|X].
  - exact (rf_slow r c Hc HW X).
  - destruct (rf_fast r c X) as (E1 & E2). rewrite E1, E2. cbn [Z.to_nat seq map rev]. rewrite !app_nil_r. split; reflexivity.
Qed.

Lemma rf_nums : 0 <= rf_nc r c /\ rf_nc r c * S <= rf_mu r c - rf_au r c < rf_nc r c * S + S /\ rf_nc r c * S < 2 ^ 20
  /\ rf_mu r c mod kUMap = 0 /\ rf_mf r c mod kUMap = 0 /\ 4 * (rf_nf r + rf_nc r c) <= rf_mf r c
  /\ rf_mf r c <= Z.max (r_mfa r) (4 * (rf_nf r + rf_nc r c) + 0x40000) /\ n <= rf_nf r + rf_nc r c
  /\ Z.of_nat (length (rf_fl2 r c)) = rf_nf r + rf_nc r c.
Proof using Hc HW.
  pose proof (ClassSize_range c Hc) as (HS & _). pose proof (MaxCount_half c Hc) as HN.
  pose proof HW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & _). unfold kUMap in *.
  assert (FL : Z.of_nat (length (rf_fl2 r c)) = rf_nf r + rf_nc r c).
  { unfold rf_fl2, rf_nf. rewrite length_app, length_rev, length_map, length_seq.
    assert (0 <= rf_nc r c); [|lia]. unfold rf_nc, rf_slowb. destruct (Z.ltb_spec (rf_nf r) n) as [X|X]; [|lia].
    pose proof (rf_newc_facts r c Hc HW X) as (N1 & _). unfold rf_k in N1. lia. }
  unfold rf_nc, rf_mu, rf_mf, rf_slowb in *. destruct (Z.ltb_spec (rf_nf r) n) as [X|X].
  - pose proof (rf_msz_facts r c Hc HW X) as (M1 & M2 & M3 & M4). pose proof (rf_newc_facts r c Hc HW X) as (N1 & (N2 & N3) & N4).
    pose proof (rf_mfa_facts r c HW) as (A1 & A2 & A3 & A4 & _). unfold rf_k in *.
    assert (0 <= rf_nf r) by (unfold rf_nf; lia).
    assert (rf_newc r c * S < 2 ^ 20) by (clear - N4 HN X HS H; nia).
    repeat split; try lia. rewrite Z.add_mod by lia. rewrite W2, M2. reflexivity.
  - unfold rf_au, rf_nf in *. repeat split; try lia.
Qed.

Lemma rf_fl2_nodup : List.NoDup (rf_fl2 r c).
Proof using Hc HW.
  pose proof HW as (_ & _ & _ & _ & _ & _ & _ & W8 & W9 & _).
  unfold rf_fl2. apply NoDup_app.
  - apply NoDup_ListNoDup. exact W8.
  - apply NoDup_rev. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup]. intros x y _ _ E. lia.
  - intros a Ha Hb. pose proof (proj1 (Forall_forall _ _) W9 a Ha) as (X1 & _).
    apply (proj2 (in_rev _ _)) in Hb. apply in_map_iff in Hb as (j & <- & _). lia.
Qed.

(* [comment removed for export] *)
Lemma rf_fl2_idle : Forall (fun i => 0 <= i < Z.of_nat (length (r_st r ++ repeat CkIdle (Z.to_nat (rf_nc r c))))
                                 /\ nth_error (r_st r ++ repeat CkIdle (Z.to_nat (rf_nc r c))) (Z.to_nat i) = Some CkIdle) (rf_fl2 r c).
Proof using Hc HW.
  pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & W9 & _). pose proof rf_nums as (P0 & _).
  apply Forall_forall. intros x Hx. rewrite length_app, repeat_length. unfold rf_fl2 in Hx. apply in_app_or in Hx as [Hx|Hx].
  - destruct (proj1 (Forall_forall _ _) W9 x Hx) as (X1 & X2). split; [lia|]. rewrite nth_error_app1 by lia. exact X2.
  - apply (proj2 (in_rev _ _)) in Hx. apply in_map_iff in Hx as (j & <- & Hj). apply in_seq in Hj. split; [lia|].
    rewrite nth_error_app2 by lia. apply nth_error_repeat. lia.
Qed.

(* [comment removed for export] *)
Lemma rf_idle_in : forall i, nth_error (r_st r ++ repeat CkIdle (Z.to_nat (rf_nc r c))) i = Some CkIdle ->
  (i < length (r_st r))%nat /\ nth_error (r_st r) i = Some CkIdle \/ In (Z.of_nat i) (rf_fl2 r c).
Proof using Hc HW.
  intros i H. destruct (Nat.lt_ge_cases i (length (r_st r))) as [Hi|Hi].
  - left. rewrite nth_error_app1 in H by exact Hi. split; [exact Hi | exact H].
  - right. rewrite nth_error_app2 in H by exact Hi. assert (Hlt : (i - length (r_st r) < Z.to_nat (rf_nc r c))%nat).
    { pose proof (proj1 (nth_error_Some (repeat CkIdle (Z.to_nat (rf_nc r c))) (i - length (r_st r))) ltac:(rewrite H; discriminate)) as X.
      rewrite repeat_length in X. exact X. }
    unfold rf_fl2. apply in_or_app. right. apply (proj1 (in_rev _ _)). apply in_map_iff.
    exists (i - length (r_st r))%nat. split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Theorem rf_reg_wf : reg_wf c (refill_reg r c).
Proof using Hc HW HROOM.
  pose proof (ClassSize_range c Hc) as (HS & _). pose proof (MaxCount_half c Hc) as HN.
  pose proof rf_nums as (P0 & (P1 & P2) & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  pose proof rf_fl2_nodup as ND. pose proof rf_fl2_idle as ID.
  pose proof HW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  assert (Hnf : rf_nf r <= Z.of_nat (length (r_st r))).
  { unfold rf_nf. pose proof (fl_len_le (r_fl r) (length (r_st r)) ltac:(apply NoDup_ListNoDup; exact W8)
                                ltac:(eapply Forall_impl; [|exact W9]; intros a (A1 & _); exact A1)). lia. }
  assert (Hnf0 : 0 <= rf_nf r) by (unfold rf_nf; lia).
  (* [comment removed for export] *)
  assert (U : 0 <= rf_mu r c <= kUserCap /\ S * (Z.of_nat (length (r_st r)) + rf_nc r c) <= 2 ^ 31 /\ 0 <= rf_mf r c <= kFaCap).
  { destruct (Z.ltb_spec (rf_nf r) n) as [X|X].
    - specialize (HROOM X).
      assert (Hst : 32 * Z.of_nat (length (r_st r)) <= 2 ^ 31) by (clear - HROOM HS; nia).
      assert (Hnc : rf_nc r c <= 2 ^ 15) by (clear - P3 HS P0; nia).
      unfold rf_au in *. unfold kUserCap, kFaCap in *.
      split; [clear - P0 P1 P2 P3 HROOM HS; split; nia|]. split; [clear - HROOM P3 P0 HS; nia|].
      clear - P6 P7 W5 Hnf Hst Hnc P0 Hnf0; split; lia.
    - assert (E0 : rf_nc r c = 0 /\ rf_mu r c = r_muser r /\ rf_mf r c = r_mfa r).
      { unfold rf_nc, rf_mu, rf_mf, rf_slowb. rewrite (proj2 (Z.ltb_ge _ _) X). split; [reflexivity|]. split; reflexivity. }
      destruct E0 as (-> & -> & ->). split; [exact W1|]. split; [clear - W11; lia | exact W5]. }
  destruct U as (U1 & U2 & U3).
  destruct rf_char as (E1 & _). rewrite E1. unfold reg_wf. cbn [r_muser r_mfa r_st r_fl].
  rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by exact P0. unfold rf_au in *. unfold kUserCap, kFaCap, kUMap in *.
  split; [exact U1|]. split; [exact P4|]. split; [clear - P1; nia|]. split; [clear - P2; nia|].
  split; [exact U3|].
  split; [exact P5|]. split.
  { rewrite length_firstn. clear - P6 P9. lia. }
  split; [apply NoDup_ListNoDup; rewrite <- (firstn_skipn (rf_cut r c) (rf_fl2 r c)) in ND; exact (NoDup_app_remove_r _ _ ND)|].
  split.
  { apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) ID x (in_firstn_l _ _ _ Hx)) as X.
    rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id in X by exact P0. exact X. }
  split; [|clear - U2; lia].
  apply Forall_app. split; [exact W10|]. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. exact I.
Qed.

End RW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_cls_le : forall (f : Z -> Z) (k : nat) B, (forall j, 1 <= j <= Z.of_nat k -> f j <= B) -> sum_cls f k <= Z.of_nat k * B.
Proof.
  intros f k B H. induction k as [|k IH]; cbn [sum_cls]; [lia|].
  pose proof (H (Z.of_nat (S k)) ltac:(lia)) as X. assert (sum_cls f k <= Z.of_nat k * B) by (apply IH; intros j Hj; apply H; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma eager_bound : forall Σ, (forall c, 1 <= c <= 31 -> reg_wf c (pr Σ c)) -> secsum Σ <= CREDIT0 -> 0 <= sec_nres Σ <= 0x4000 ->
  rt_eager Σ <= 2 ^ 38.
Proof.
  intros Σ HR HS HN. unfold rt_eager. fold (secsum Σ).
  assert (E : sum_cls (fun c => r_muser (pr Σ c) + r_mfa (pr Σ c)) 31 <= Z.of_nat 31 * (2 ^ 31 + 2 ^ 16 + 2 ^ 29)).
  { apply sum_cls_le. intros j Hj. pose proof (HR j Hj) as (_ & _ & _ & W4 & W5 & _ & _ & _ & _ & _ & W11). pose proof (ClassSize_range j Hj) as (X & _).
    unfold kFaCap in *. lia. }
  unfold CREDIT0 in *. lia.
Qed.

Section WF.
Variables (Σ : rtsA) (c : Z).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hca : ca Σ c = [].
Hypothesis HROOM : refill_room Σ c.
#[local] Notation Σ' := (refillΣ Σ c).

Lemma rfw_reg : reg_wf c (pr Σ c).
Proof using Hc HW0. pose proof HW0 as (_ & HR & _). exact (proj1 HR c Hc). Qed.

Lemma rfs_st : forall c' i st, nth_error (r_st (pr Σ' c')) i = Some st ->
  nth_error (r_st (pr Σ c')) i = Some st \/ (c' = c /\ st = CkIdle /\ (length (r_st (pr Σ c)) <= i)%nat).
Proof using Hc HW0.
  intros c' i st H. cbn [refillΣ pr] in H. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|left; exact H].
  destruct (rf_char (pr Σ c) c Hc rfw_reg) as (E1 & _). rewrite E1 in H. cbn [r_st] in H.
  destruct (Nat.lt_ge_cases i (length (r_st (pr Σ c)))) as [Hi|Hi].
  - left. rewrite nth_error_app1 in H by exact Hi. exact H.
  - right. rewrite nth_error_app2 in H by exact Hi. split; [reflexivity|]. split; [|exact Hi].
    apply nth_error_In in H. apply repeat_spec in H. exact H.
Qed.

Lemma rfs_keep : forall c' i st, nth_error (r_st (pr Σ c')) i = Some st -> nth_error (r_st (pr Σ' c')) i = Some st.
Proof using Hc HW0.
  intros c' i st H. cbn [refillΣ pr]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact H].
  destruct (rf_char (pr Σ c) c Hc rfw_reg) as (E1 & _). rewrite E1. cbn [r_st].
  rewrite nth_error_app1; [exact H|]. apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma rfs_qent : forall e, qent_ok Σ e -> qent_ok Σ' e.
Proof using Hc HW0.
  intros e [(c' & i' & Hc' & Hq & He)|X]; [left | right; exact X].
  exists c', i'. split; [exact Hc'|]. split; [exact (rfs_keep c' i' _ Hq) | exact He].
Qed.

Theorem refill_wf0 : rt_wf0 Σ'.
Proof using Hc HW0 Hca HROOM.
  pose proof HW0 as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof (MaxCount_half c Hc) as HN. pose proof rfw_reg as HWc.
  pose proof (rf_nums (pr Σ c) c Hc HWc) as (P0 & (P1 & P2) & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct (rf_char (pr Σ c) c Hc HWc) as (E1 & E2).
  assert (HRG : regs_wf Σ').
  { destruct W2 as (R1 & R2 & R3 & R4 & R5 & R6). unfold regs_wf. cbn [refillΣ pr ca ca_init].
    split; [intros c' Hc'; destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact (rf_reg_wf (pr Σ c) c Hc HWc HROOM) | exact (R1 c' Hc')]|].
    split; [intros c' Hc'; destruct (Z.eqb_spec c' c) as [->|Hcc]; [lia | exact (R2 c' Hc')]|].
    split.
    { intros c' Hc'. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact (R3 c' Hc')]. rewrite E1, E2. cbn [r_st r_fl].
      split; [rewrite length_skipn; unfold rf_cut; pose proof (MaxCount_range c Hc) as HMC; assert (MaxCount c / 2 <= MaxCount c) by (apply Z.div_le_upper_bound; lia); clear - P8 P9 HN H; lia|]. split.
      - apply NoDup_ListNoDup. apply nodup_skipn_firstn. exact (rf_fl2_nodup (pr Σ c) c Hc HWc).
      - apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) (rf_fl2_idle (pr Σ c) c Hc HWc)).
        rewrite <- (firstn_skipn (rf_cut (pr Σ c) c) (rf_fl2 (pr Σ c) c)). apply in_or_app. right. exact Hx. }
    split; [intros X; discriminate X|]. split; [|intros X; discriminate X].
    intros c' i Hc' Hi. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact (R5 c' i Hc' Hi)].
    rewrite E1, E2. cbn [r_st r_fl]. rewrite E1 in Hi. cbn [r_st] in Hi. apply in_skipn_firstn.
    destruct (rf_idle_in (pr Σ c) c Hc HWc i Hi) as [(_ & Hi0)|X]; [|exact X].
    pose proof (R5 c i Hc Hi0) as X. rewrite Hca in X. cbn [app] in X. unfold rf_fl2. apply in_or_app. left. exact X. }
  split; [exact W1|]. split; [exact HRG|]. split.
  { destruct W3 as (V1 & V2 & V3 & V4 & V5). unfold live_wf. cbn [refillΣ live lay sec].
    split; [exact V1|]. split; [exact V2|]. split; [|split; [|exact V5]].
    - intros p' n' Hin. destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & Ep)|X]; [left|right; exact X].
      exists c', i'. split; [exact Hc'|]. split; [exact (rfs_keep c' i' _ Hn') | exact Ep].
    - intros c' i' n' Hc' Hn'. destruct (rfs_st c' i' _ Hn') as [Hn0|(_ & E & _)]; [exact (V4 c' i' n' Hc' Hn0) | discriminate E]. }
  split; [exact W4|]. split.
  { destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). unfold quar_wf, qents in *. cbn [refillΣ ql qg lay] in *.
    split; [exact Q1|]. split; [exact Q2|]. split.
    { eapply Forall_impl; [|exact Q3]. intros b (j & Hj & Eb). exists j. split; [exact (rfs_keep 24 j _ Hj) | exact Eb]. }
    split; [exact Q4|]. split; [exact Q5|]. split; [eapply Forall_impl; [|exact Q6]; intros e He; exact (rfs_qent e He)|].
    split; [exact Q7|]. intros c' i' Hc' Hi'. destruct (rfs_st c' i' _ Hi') as [Hi0|(_ & E & _)]; [exact (Q8 c' i' Hc' Hi0) | discriminate E]. }
  split; [exact W6|]. split.
  { destruct W7 as (G1 & G2 & G3 & G4 & G5). unfold budget_wf. cbn [refillΣ credit aw].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [|exact G5].
    apply eager_bound; [exact (proj1 HRG) | unfold secsum in *; cbn [refillΣ sec]; lia|].
    cbn [refillΣ sec_nres]. destruct W4 as (_ & X & _). lia. }
  split; [exact W8|]. split; [exact W9|]. split; [exact W10 | exact W11].
Qed.

Theorem refill_count : rt_count Σ -> rt_count Σ'.
Proof using Hc HW0.
  intros (RC1 & RC2). split.
  - intros c' i n' Hc' Hi. unfold qents. cbn [refillΣ ql qg lay]. destruct (rfs_st c' i _ Hi) as [Hi0|(_ & E & _)]; [|discriminate E].
    exact (RC1 c' i n' Hc' Hi0).
  - intros s Hs Hq. exact (RC2 s Hs Hq).
Qed.

End WF.

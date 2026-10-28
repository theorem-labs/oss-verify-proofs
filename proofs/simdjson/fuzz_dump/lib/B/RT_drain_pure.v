(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_depot_defs R_fs_defs RT_state RT_rep RT_drain_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Lemma Forall_upd : forall {X} (P : X -> Prop) l i x, Forall P l -> P x -> Forall P (upd l i x).
Proof.
  intros X P l. induction l as [|y l IH]; intros i x H Hx; [constructor|]. destruct i as [|i]; cbn [upd].
  - inversion H; subst. constructor; assumption.
  - inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma nodup_len_bound : forall (xs : list Z) N, 0 <= N -> List.NoDup xs -> Forall (fun x => 0 <= x < N) xs -> Z.of_nat (length xs) <= N.
Proof.
  intros xs N HN Hnd Hr.
  assert (Hl : (length (map Z.to_nat xs) <= length (seq 0 (Z.to_nat N)))%nat).
  { apply List.NoDup_incl_length.
    - apply (NoDup_map_inv Z.of_nat). rewrite map_map.
      replace (map (fun x => Z.of_nat (Z.to_nat x)) xs) with xs; [exact Hnd|].
      clear Hnd. induction xs as [|x xs IH]; [reflexivity|]. inversion Hr; subst. cbn [map]. rewrite Z2Nat.id by lia. f_equal. apply IH. assumption.
    - intros y Hy. apply in_map_iff in Hy as (x & <- & Hx). pose proof (proj1 (Forall_forall _ _) Hr x Hx) as X.
      cbv beta in X. apply in_seq. lia. }
  rewrite length_map, length_seq in Hl. lia.
Qed.

Lemma nodup_app_comm : forall {X} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup (l2 ++ l1).
Proof. intros X l1 l2 H. apply (Permutation_NoDup (Permutation_app_comm l1 l2) H). Qed.

Lemma nodup_app_l : forall {X} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  intros X l1 l2 H. induction l1 as [|x l1 IH]; [constructor|]. inversion H as [|a b Hx Hl]; subst.
  constructor; [intros Hin; apply Hx; apply in_or_app; left; exact Hin | exact (IH Hl)].
Qed.

Lemma nodup_app_r : forall {X} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. intros X l1 l2 H. exact (nodup_app_l l2 l1 (nodup_app_comm l1 l2 H)). Qed.

Lemma in_skipn' : forall {X} (l : list X) k x, In x (skipn k l) -> In x l.
Proof. intros X l k x H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.
Lemma in_firstn' : forall {X} (l : list X) k x, In x (firstn k l) -> In x l.
Proof. intros X l k x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.

Lemma perm_drain : forall {X} (A B R : list X) x, Permutation (x :: (A ++ B) ++ R) ((A ++ [x]) ++ (R ++ B)).
Proof.
  intros X A B R x. rewrite <- !app_assoc. cbn [app].
  eapply perm_trans; [|apply Permutation_middle]. apply perm_skip. apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma perm_push : forall {X} (A R : list X) x, Permutation (x :: A ++ R) ((A ++ [x]) ++ R).
Proof. intros X A R x. rewrite <- app_assoc. cbn [app]. apply Permutation_middle. Qed.

Lemma perm_split : forall {X} (l : list X) k, Permutation l (firstn k l ++ skipn k l).
Proof. intros X l k. rewrite firstn_skipn. apply Permutation_refl. Qed.

Section Proj.
Variables (Σ : rtsA) (c : Z) (i : nat).

Lemma st_fields : lay (set_st Σ c i CkIdle) = lay Σ /\ ca (set_st Σ c i CkIdle) = ca Σ /\ ca_init (set_st Σ c i CkIdle) = ca_init Σ
  /\ sec (set_st Σ c i CkIdle) = sec Σ /\ sec_nres (set_st Σ c i CkIdle) = sec_nres Σ /\ aw (set_st Σ c i CkIdle) = aw Σ
  /\ ql (set_st Σ c i CkIdle) = ql Σ /\ qg (set_st Σ c i CkIdle) = qg Σ /\ dep (set_st Σ c i CkIdle) = dep Σ
  /\ fs0 (set_st Σ c i CkIdle) = fs0 Σ /\ fsc0 (set_st Σ c i CkIdle) = fsc0 Σ /\ fs4 (set_st Σ c i CkIdle) = fs4 Σ
  /\ credit (set_st Σ c i CkIdle) = credit Σ /\ live (set_st Σ c i CkIdle) = live Σ /\ frames (set_st Σ c i CkIdle) = frames Σ.
Proof. repeat split; reflexivity. Qed.

Lemma cdeal_fields : lay (cdealΣ Σ c i) = lay Σ /\ ca_init (cdealΣ Σ c i) = ca_init Σ
  /\ sec (cdealΣ Σ c i) = sec Σ /\ sec_nres (cdealΣ Σ c i) = sec_nres Σ /\ aw (cdealΣ Σ c i) = aw Σ
  /\ ql (cdealΣ Σ c i) = ql Σ /\ qg (cdealΣ Σ c i) = qg Σ /\ dep (cdealΣ Σ c i) = dep Σ
  /\ fs0 (cdealΣ Σ c i) = fs0 Σ /\ fsc0 (cdealΣ Σ c i) = fsc0 Σ /\ fs4 (cdealΣ Σ c i) = fs4 Σ
  /\ credit (cdealΣ Σ c i) = credit Σ /\ live (cdealΣ Σ c i) = live Σ /\ frames (cdealΣ Σ c i) = frames Σ.
Proof. repeat split; reflexivity. Qed.

Lemma recp_fields : lay (recp Σ c i) = lay Σ /\ ca_init (recp Σ c i) = ca_init Σ
  /\ sec (recp Σ c i) = sec Σ /\ sec_nres (recp Σ c i) = sec_nres Σ /\ aw (recp Σ c i) = aw Σ
  /\ ql (recp Σ c i) = ql Σ /\ qg (recp Σ c i) = qg Σ /\ dep (recp Σ c i) = dep Σ
  /\ fs0 (recp Σ c i) = fs0 Σ /\ fsc0 (recp Σ c i) = fsc0 Σ /\ fs4 (recp Σ c i) = fs4 Σ
  /\ credit (recp Σ c i) = credit Σ /\ live (recp Σ c i) = live Σ /\ frames (recp Σ c i) = frames Σ.
Proof. repeat split; reflexivity. Qed.

Lemma recp_pr : forall c', pr (recp Σ c i) c' = if c' =? c then cdeal_reg c (ureg (pr Σ c) i CkIdle) (ca Σ c) else pr Σ c'.
Proof.
  intros c'. unfold recp, cdealΣ. cbn [pr ca]. destruct (Z.eqb_spec c' c) as [->|Hne].
  - rewrite updf_same. unfold set_st. cbn [pr ca]. rewrite updf_same. reflexivity.
  - rewrite updf_other by exact Hne. unfold set_st. cbn [pr]. rewrite updf_other by exact Hne. reflexivity.
Qed.

Lemma recp_ca : forall c', ca (recp Σ c i) c' = if c' =? c then cdeal_ca c i (ca Σ c) else ca Σ c'.
Proof.
  intros c'. unfold recp, cdealΣ. cbn [pr ca]. destruct (Z.eqb_spec c' c) as [->|Hne].
  - rewrite updf_same. reflexivity.
  - rewrite updf_other by exact Hne. reflexivity.
Qed.

Lemma cdeal_reg_st : forall r l, r_st (cdeal_reg c r l) = r_st r.
Proof. intros r l. unfold cdeal_reg. destruct (cdeal_full c l); reflexivity. Qed.
Lemma cdeal_reg_muser : forall r l, r_muser (cdeal_reg c r l) = r_muser r.
Proof. intros r l. unfold cdeal_reg. destruct (cdeal_full c l); reflexivity. Qed.

Lemma recp_st : forall c' j, nth_error (r_st (pr (recp Σ c i) c')) j =
  if (c' =? c) && Nat.eqb i j then (if Nat.ltb j (length (r_st (pr Σ c))) then Some CkIdle else None) else nth_error (r_st (pr Σ c')) j.
Proof.
  intros c' j. rewrite recp_pr. destruct (Z.eqb_spec c' c) as [->|Hne]; cbn [andb]; [|reflexivity].
  rewrite cdeal_reg_st. unfold ureg. cbn [r_st]. apply nth_upd_ck.
Qed.

Lemma recp_len : forall c', length (r_st (pr (recp Σ c i) c')) = length (r_st (pr Σ c')).
Proof.
  intros c'. rewrite recp_pr. destruct (Z.eqb_spec c' c) as [->|Hne]; [|reflexivity].
  rewrite cdeal_reg_st. unfold ureg. cbn [r_st]. apply upd_length.
Qed.

Lemma recp_muser : forall c', r_muser (pr (recp Σ c i) c') = r_muser (pr Σ c').
Proof. intros c'. rewrite recp_pr. destruct (Z.eqb_spec c' c) as [->|Hne]; [|reflexivity]. rewrite cdeal_reg_muser. reflexivity. Qed.

Lemma recp_mfa : forall c', r_mfa (pr (recp Σ c i) c') =
  if c' =? c then (if cdeal_full c (ca Σ c) then dh_mfa c (ureg (pr Σ c) i CkIdle) else r_mfa (pr Σ c)) else r_mfa (pr Σ c').
Proof.
  intros c'. rewrite recp_pr. destruct (Z.eqb_spec c' c) as [->|Hne]; [|reflexivity].
  unfold cdeal_reg. destruct (cdeal_full c (ca Σ c)); reflexivity.
Qed.

End Proj.

Lemma round_fa_le : forall x, 0 <= x -> x <= 2 ^ 28 -> round_fa x <= 2 ^ 29.
Proof. intros x H1 H2. pose proof (round_fa_ge x H1). lia. Qed.

Section Rec.
Variables (Σ : rtsA) (c : Z) (i : nat) (st : ckst).
Hypothesis HR : regs_wf Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis Hst : st <> CkIdle.
Hypothesis Hinit : ca_init Σ = true.

#[local] Notation r := (pr Σ c).
#[local] Notation l := (ca Σ c).

Lemma rc_facts : reg_wf c r /\ Z.of_nat (length l) <= MaxCount c /\ List.NoDup (l ++ r_fl r)
  /\ Forall (fun j => 0 <= j < Z.of_nat (length (r_st r)) /\ nth_error (r_st r) (Z.to_nat j) = Some CkIdle) l.
Proof.
  destruct HR as (R1 & _ & R3 & _). pose proof (R1 c Hc) as W. destruct (R3 c Hc) as (C1 & C2 & C3).
  split; [exact W|]. split; [exact C1|]. split; [apply NoDup_ListNoDup; exact C2 | exact C3].
Qed.

Lemma rc_notin : ~ In (Z.of_nat i) (l ++ r_fl r).
Proof.
  pose proof rc_facts as (W & _ & _ & C3). destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & W9 & _).
  intros Hin. apply in_app_or in Hin as [Hin|Hin].
  - pose proof (proj1 (Forall_forall _ _) C3 _ Hin) as (_ & X). rewrite Nat2Z.id, Hi in X. injection X as X. exact (Hst X).
  - pose proof (proj1 (Forall_forall _ _) W9 _ Hin) as (_ & X). rewrite Nat2Z.id, Hi in X. injection X as X. exact (Hst X).
Qed.

Lemma rc_i_lt : (i < length (r_st r))%nat.
Proof. apply nth_error_Some. rewrite Hi. discriminate. Qed.

Lemma rc_count : Z.of_nat (length l) + Z.of_nat (length (r_fl r)) + 1 <= Z.of_nat (length (r_st r)) <= 2 ^ 26.
Proof.
  pose proof rc_facts as (W & _ & Hnd & C3). destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & W9 & _ & W11).
  pose proof (ClassSize_range c Hc) as ((Hcs & _) & _).
  assert (H1 : Z.of_nat (length (Z.of_nat i :: l ++ r_fl r)) <= Z.of_nat (length (r_st r))).
  { apply nodup_len_bound; [lia| |].
    - constructor; [exact rc_notin | exact Hnd].
    - constructor; [pose proof rc_i_lt; lia|]. apply Forall_app. split.
      + apply Forall_forall. intros x Hx. exact (proj1 (proj1 (Forall_forall _ _) C3 x Hx)).
      + apply Forall_forall. intros x Hx. exact (proj1 (proj1 (Forall_forall _ _) W9 x Hx)). }
  cbn [length] in H1. rewrite length_app in H1. split; [lia|].
  assert (32 * Z.of_nat (length (r_st r)) <= ClassSize c * Z.of_nat (length (r_st r))) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

Lemma rc_mc : 2 <= MaxCount c <= 16 /\ MaxCount c mod 2 = 0.
Proof. exact (MaxCount_range c Hc). Qed.

Lemma rc_full_len : cdeal_full c l = true -> length l = Z.to_nat (MaxCount c).
Proof. intros H. pose proof rc_facts as (_ & C1 & _). unfold cdeal_full in H. apply Z.leb_le in H. lia. Qed.

Lemma rc_keep : cdeal_full c l = true -> (dh_keep c <= length l)%nat /\ length (skipn (dh_keep c) l) = Z.to_nat (MaxCount c / 2)
  /\ length (firstn (dh_keep c) l) = dh_keep c /\ (1 <= dh_keep c < Z.to_nat (MaxCount c))%nat.
Proof.
  intros H. pose proof (rc_full_len H) as E. pose proof rc_mc as ((M1 & M2) & M3).
  assert (2 <= MaxCount c / 2 * 2) by (pose proof (Z.div_mod (MaxCount c) 2 ltac:(lia)); lia).
  assert (MaxCount c / 2 * 2 = MaxCount c) by (pose proof (Z.div_mod (MaxCount c) 2 ltac:(lia)); lia).
  unfold dh_keep. rewrite length_skipn, length_firstn, E. repeat split; lia.
Qed.

Lemma rc_reg_wf : reg_wf c (cdeal_reg c (ureg r i CkIdle) l).
Proof.
  pose proof rc_facts as (W & C1 & Hnd & C3). pose proof rc_count as (K1 & K2). pose proof rc_i_lt as Hlt.
  destruct W as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  assert (F9 : forall x, In x (r_fl r) \/ In x l ->
             0 <= x < Z.of_nat (length (r_st r)) /\ nth_error (upd (r_st r) i CkIdle) (Z.to_nat x) = Some CkIdle).
  { intros x Hx. rewrite nth_upd_ck.
    assert (Hx' : 0 <= x < Z.of_nat (length (r_st r)) /\ nth_error (r_st r) (Z.to_nat x) = Some CkIdle)
      by (destruct Hx as [Hx|Hx]; [exact (proj1 (Forall_forall _ _) W9 x Hx) | exact (proj1 (Forall_forall _ _) C3 x Hx)]).
    split; [exact (proj1 Hx')|]. destruct (Nat.eqb_spec i (Z.to_nat x)) as [E|E]; [|exact (proj2 Hx')].
    destruct (Nat.ltb_spec (Z.to_nat x) (length (r_st r))); [reflexivity | lia]. }
  assert (F10 : Forall (fun st => match st with CkAlloc n | CkQuar n => 1 <= n /\ rz_size n + n <= ClassSize c /\ c = ClassID (needed n)
                                   | _ => True end) (upd (r_st r) i CkIdle)) by (apply Forall_upd; [exact W10 | exact I]).
  unfold cdeal_reg, ureg. destruct (cdeal_full c l) eqn:EF.
  - pose proof (rc_keep EF) as (Kp1 & Kp2 & Kp3 & Kp4). pose proof rc_mc as ((M1 & M2) & M3).
    unfold reg_wf, dh_mfa, dh_grow, dh_nf. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length.
    assert (Hnfl : Z.of_nat (length (r_fl r ++ skipn (dh_keep c) l)) = Z.of_nat (length (r_fl r)) + MaxCount c / 2).
    { rewrite length_app, Kp2. rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). reflexivity. }
    assert (Hle : MaxCount c / 2 <= Z.of_nat (length l)) by (pose proof (rc_full_len EF) as E; rewrite E, Z2Nat.id by lia;
                                                                pose proof (Z.div_le_upper_bound (MaxCount c) 2 (MaxCount c) ltac:(lia) ltac:(lia)); lia).
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
    split; [destruct (r_mfa r <? 4 * (Z.of_nat (length (r_fl r)) + MaxCount c / 2)) eqn:G;
            [pose proof (round_fa_ge (4 * (Z.of_nat (length (r_fl r)) + MaxCount c / 2)) ltac:(lia)); split; [lia|];
             apply round_fa_le; unfold kFaCap in *; lia | exact W5]|].
    split; [destruct (r_mfa r <? _); [apply round_fa_aligned | exact W6]|].
    split; [rewrite Hnfl; destruct (r_mfa r <? _) eqn:G; [pose proof (round_fa_ge (4 * (Z.of_nat (length (r_fl r)) + MaxCount c / 2)) ltac:(lia)); lia|];
            apply Z.ltb_ge in G; lia|].
    split.
    { apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_app_comm _ _)). rewrite <- (firstn_skipn (dh_keep c) l) in Hnd.
      rewrite <- app_assoc in Hnd. apply nodup_app_r in Hnd. exact Hnd. }
    split; [|split; [exact F10 | exact W11]].
    apply Forall_forall. intros x Hx. apply F9. apply in_app_or in Hx as [Hx|Hx]; [left; exact Hx | right; exact (in_skipn' _ _ _ Hx)].
  - unfold reg_wf. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length.
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|].
    split; [exact W7|]. split; [exact W8|]. split; [|split; [exact F10 | exact W11]].
    apply Forall_forall. intros x Hx. apply F9. left; exact Hx.
Qed.

Lemma rc_cache : Z.of_nat (length (cdeal_ca c i l)) <= MaxCount c
  /\ NoDup (cdeal_ca c i l ++ r_fl (cdeal_reg c (ureg r i CkIdle) l))
  /\ Forall (fun j => 0 <= j < Z.of_nat (length (r_st (cdeal_reg c (ureg r i CkIdle) l)))
                      /\ nth_error (r_st (cdeal_reg c (ureg r i CkIdle) l)) (Z.to_nat j) = Some CkIdle) (cdeal_ca c i l).
Proof.
  pose proof rc_facts as (W & C1 & Hnd & C3). pose proof rc_i_lt as Hlt. pose proof rc_notin as Hni.
  assert (Hrst : r_st (cdeal_reg c (ureg r i CkIdle) l) = upd (r_st r) i CkIdle) by (unfold cdeal_reg, ureg; destruct (cdeal_full c l); reflexivity).
  rewrite Hrst, upd_length.
  assert (Fi : forall x, In x l -> 0 <= x < Z.of_nat (length (r_st r)) /\ nth_error (upd (r_st r) i CkIdle) (Z.to_nat x) = Some CkIdle).
  { intros x Hx. pose proof (proj1 (Forall_forall _ _) C3 x Hx) as (X1 & X2). split; [exact X1|]. rewrite nth_upd_ck.
    destruct (Nat.eqb_spec i (Z.to_nat x)) as [E|E]; [|exact X2]. destruct (Nat.ltb_spec (Z.to_nat x) (length (r_st r))); [reflexivity | lia]. }
  assert (Fii : 0 <= Z.of_nat i < Z.of_nat (length (r_st r)) /\ nth_error (upd (r_st r) i CkIdle) (Z.to_nat (Z.of_nat i)) = Some CkIdle).
  { split; [lia|]. rewrite Nat2Z.id, nth_upd_ck, Nat.eqb_refl. destruct (Nat.ltb_spec i (length (r_st r))); [reflexivity | lia]. }
  unfold cdeal_ca, cdeal_reg, ureg. destruct (cdeal_full c l) eqn:EF.
  - pose proof (rc_keep EF) as (Kp1 & Kp2 & Kp3 & Kp4). cbn [r_fl].
    split; [rewrite length_app, Kp3; cbn [length]; pose proof (rc_full_len EF); lia|].
    split.
    + apply NoDup_ListNoDup. rewrite <- (firstn_skipn (dh_keep c) l) in Hnd, Hni.
      apply (Permutation_NoDup (l := Z.of_nat i :: (firstn (dh_keep c) l ++ skipn (dh_keep c) l) ++ r_fl r)); [|constructor; assumption].
      apply perm_drain.
    + apply Forall_app. split; [apply Forall_forall; intros x Hx; exact (Fi x (in_firstn' _ _ _ Hx)) | constructor; [exact Fii | constructor]].
  - split; [rewrite length_app; cbn [length]; unfold cdeal_full in EF; apply Z.leb_gt in EF; lia|].
    split.
    + apply NoDup_ListNoDup. apply (Permutation_NoDup (l := Z.of_nat i :: l ++ r_fl r)); [|constructor; assumption].
      apply perm_push.
    + apply Forall_app. split; [apply Forall_forall; intros x Hx; exact (Fi x Hx) | constructor; [exact Fii | constructor]].
Qed.

Theorem regs_wf_recp : regs_wf (recp Σ c i).
Proof.
  pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6). pose proof rc_reg_wf as W'. pose proof rc_cache as (K1 & K2 & K3).
  pose proof rc_facts as (_ & _ & Hnd & C3). pose proof rc_i_lt as Hlt.
  assert (Hrst : r_st (cdeal_reg c (ureg r i CkIdle) l) = upd (r_st r) i CkIdle) by (rewrite cdeal_reg_st; reflexivity).
  split; [intros c' Hc'; rewrite recp_pr; destruct (Z.eqb_spec c' c) as [->|Hne]; [exact W' | exact (R1 c' Hc')]|].
  split; [intros c' Hc'; rewrite recp_pr; destruct (Z.eqb_spec c' c) as [->|Hne]; [lia | exact (R2 c' Hc')]|].
  split; [intros c' Hc'; rewrite recp_pr, recp_ca; destruct (Z.eqb_spec c' c) as [->|Hne]; [exact (conj K1 (conj K2 K3)) | exact (R3 c' Hc')]|].
  split; [intros E; cbn [recp cdealΣ ca_init set_st] in E; rewrite Hinit in E; discriminate|].
  split; [|intros E; cbn [recp cdealΣ ca_init set_st] in E; rewrite Hinit in E; discriminate].
  intros c' j Hc' Hj. rewrite recp_pr in Hj. rewrite recp_pr, recp_ca. destruct (Z.eqb_spec c' c) as [->|Hne]; [|exact (R5 c' j Hc' Hj)].
  rewrite Hrst, nth_upd_ck in Hj.
  unfold cdeal_ca, cdeal_reg, ureg. destruct (Nat.eqb_spec i j) as [<-|Hij].
  - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - pose proof (R5 c j Hc Hj) as Hin. destruct (cdeal_full c l); cbn [r_fl].
    + rewrite <- (firstn_skipn (dh_keep c) l) in Hin. apply in_app_or in Hin as [Hin|Hin]; [apply in_app_or in Hin as [Hin|Hin]|].
      * apply in_or_app. left. apply in_or_app. left. exact Hin.
      * apply in_or_app. right. apply in_or_app. right. exact Hin.
      * apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply in_app_or in Hin as [Hin|Hin]; [apply in_or_app; left; apply in_or_app; left; exact Hin | apply in_or_app; right; exact Hin].
Qed.

End Rec.

End GWIN.

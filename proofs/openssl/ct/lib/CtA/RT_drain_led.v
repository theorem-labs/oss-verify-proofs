(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface R_cache_defs R_prim_defs R_depot_defs R_fs_defs RT_state RT_rep RT_facts0 RT_drain_defs RT_drain_pure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div_unique_pos : forall a b x y k, 0 < k -> 0 <= x < k -> 0 <= y < k -> a * k + x = b * k + y -> a = b.
Proof. intros a b x y k Hk Hx Hy E. destruct (Z.lt_trichotomy a b) as [L|[L|L]]; [nia | exact L | nia]. Qed.

Lemma rz_ge16 : forall n, 16 <= rz_size n.
Proof.
  intros n. unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)).
  lia.
Qed.

(* [comment removed for export] *)
Lemma hdr_geo : forall Σ c i n, regs_wf Σ -> 1 <= c <= 31 ->
  (nth_error (r_st (pr Σ c)) i = Some (CkQuar n) \/ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n)) ->
  1 <= n /\ 16 <= rz_size n /\ rz_size n - 16 < ClassSize c /\ (Z.of_nat i + 1) * ClassSize c <= 2 ^ 31 /\ 32 <= ClassSize c.
Proof.
  intros Σ c i n (HR & _) Hc Hi. pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & W11).
  assert (Hin : In (CkQuar n) (r_st (pr Σ c)) \/ In (CkAlloc n) (r_st (pr Σ c))) by (destruct Hi as [Hi|Hi]; [left | right]; exact (nth_error_In _ _ Hi)).
  assert (Hfit : 1 <= n /\ rz_size n + n <= ClassSize c).
  { destruct Hin as [Hin|Hin]; pose proof (proj1 (Forall_forall _ _) W10 _ Hin) as X; cbv beta iota in X; lia. }
  pose proof (rz_ge16 n). pose proof (ClassSize_range c Hc) as ((Hcs & _) & _).
  assert (Hlt : (i < length (r_st (pr Σ c)))%nat) by (apply nth_error_Some; destruct Hi as [Hi|Hi]; rewrite Hi; discriminate).
  assert ((Z.of_nat i + 1) * ClassSize c <= Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by (apply Z.mul_le_mono_nonneg_r; lia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.

Lemma hdr_inj : forall Σ c i n c' i' n', regs_wf Σ -> 1 <= c <= 31 -> 1 <= c' <= 31 ->
  nth_error (r_st (pr Σ c)) i = Some (CkQuar n) -> nth_error (r_st (pr Σ c')) i' = Some (CkQuar n') ->
  p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 = p_abeg (l_SB (lay Σ)) c' i' + rz_size n' - 16 -> c = c' /\ i = i'.
Proof.
  intros Σ c i n c' i' n' HR Hc Hc' Hi Hi' E.
  pose proof (hdr_geo Σ c i n HR Hc (or_introl Hi)) as (A1 & A2 & A3 & A4 & A5).
  pose proof (hdr_geo Σ c' i' n' HR Hc' (or_introl Hi')) as (B1 & B2 & B3 & B4 & B5).
  unfold p_abeg in E.
  assert (Ec : c = c').
  { apply (div_unique_pos c c' (Z.of_nat i * ClassSize c + (rz_size n - 16)) (Z.of_nat i' * ClassSize c' + (rz_size n' - 16)) (2 ^ 32));
      [lia | nia | nia | lia]. }
  subst c'. split; [reflexivity|].
  apply Nat2Z.inj. apply (div_unique_pos (Z.of_nat i) (Z.of_nat i') (rz_size n - 16) (rz_size n' - 16) (ClassSize c)); lia.
Qed.

(* [comment removed for export] *)
Lemma hdr_prim_range : forall Σ c i n, layout_ok (lay Σ) -> regs_wf Σ -> 1 <= c <= 31 ->
  nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
  l_PRB (lay Σ) <= p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 < l_PRB (lay Σ) + 0x2000011000.
Proof.
  intros Σ c i n HL HR Hc Hi. pose proof (hdr_geo Σ c i n HR Hc (or_introl Hi)) as (A1 & A2 & A3 & A4 & A5).
  destruct HL as (_ & _ & _ & _ & _ & _ & (P1 & P2) & _). unfold p_abeg. nia.
Qed.

Lemma smsz_big : forall n, 64513 <= n -> 6144 + n <= smsz n.
Proof. intros n Hn. pose proof (smsz_room n ltac:(lia)). lia. Qed.

Lemma sec_hdr_range : forall Σ s, sec_wf Σ -> In s (sec Σ) ->
  s_mb s < s_mb s + 6128 < s_mb s + smsz (s_n s) /\ apart (s_mb s) (smsz (s_n s)) (l_PRB (lay Σ)) 0x2000011000 /\ 0 < s_mb s.
Proof.
  intros Σ s HS Hs. destruct HS as (_ & _ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF s Hs) as (Hn & (G1 & _) & Hp & _).
  pose proof (smsz_big (s_n s) ltac:(lia)). split; [lia|]. split; [exact Hp | exact G1].
Qed.

Lemma hdr_prim_sec : forall Σ c i n s, layout_ok (lay Σ) -> regs_wf Σ -> sec_wf Σ -> 1 <= c <= 31 ->
  nth_error (r_st (pr Σ c)) i = Some (CkQuar n) -> In s (sec Σ) ->
  p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 <> s_mb s + 6128.
Proof.
  intros Σ c i n s HL HR HS Hc Hi Hs E. pose proof (hdr_prim_range Σ c i n HL HR Hc Hi) as X.
  pose proof (sec_hdr_range Σ s HS Hs) as (Y1 & Y2 & Y3). unfold apart in Y2. lia.
Qed.

Lemma sec_pos_inj : forall Σ k k' s s', sec_wf Σ -> nth_error (sec Σ) k = Some s -> nth_error (sec Σ) k' = Some s' ->
  s_mb s = s_mb s' -> k = k'.
Proof.
  intros Σ k k' s s' HS Hk Hk' E. destruct (Nat.eq_dec k k') as [->|Hne]; [reflexivity|].
  pose proof HS as (_ & _ & _ & _ & HP & _). pose proof (HP k k' s s' Hk Hk' Hne) as A.
  pose proof (sec_hdr_range Σ s HS (nth_error_In _ _ Hk)) as (Y1 & _). pose proof (sec_hdr_range Σ s' HS (nth_error_In _ _ Hk')) as (Y1' & _).
  unfold apart in A. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma removelast_length : forall {X} (l : list X), length (removelast l) = (length l - 1)%nat.
Proof.
  intros X l. induction l as [|x l IH]; [reflexivity|]. destruct l as [|y l]; [reflexivity|].
  cbn [removelast length] in *. rewrite IH. lia.
Qed.

Lemma nth_removelast : forall {X} (l : list X) j, (S j < length l)%nat -> nth_error (removelast l) j = nth_error l j.
Proof.
  intros X l. induction l as [|x l IH]; intros j Hj; cbn in Hj; [lia|]. destruct l as [|y l]; [cbn in Hj; lia|].
  destruct j as [|j]; [reflexivity|]. cbn [removelast nth_error]. apply IH. cbn in *. lia.
Qed.

Lemma last_nth : forall {X} (l : list X) d, l <> [] -> nth_error l (length l - 1) = Some (last l d).
Proof.
  intros X l d H. induction l as [|x l IH]; [congruence|]. destruct l as [|y l]; [reflexivity|].
  cbn [length]. replace (S (S (length l)) - 1)%nat with (S (length (y :: l) - 1)) by (cbn; lia). cbn [nth_error].
  rewrite IH by discriminate. reflexivity.
Qed.

Lemma swap_remove_length : forall {X} (k : nat) (l : list X), (k < length l)%nat -> length (swap_remove k l) = (length l - 1)%nat.
Proof.
  intros X k l Hk. unfold swap_remove. destruct l as [|x l']; [reflexivity|].
  destruct (Nat.eqb_spec (S k) (length (x :: l'))); [apply removelast_length|]. rewrite upd_length. apply removelast_length.
Qed.

(* [comment removed for export] *)
Lemma swap_remove_nth : forall {X} (k : nat) (l : list X) j y, (k < length l)%nat -> nth_error (swap_remove k l) j = Some y ->
  nth_error l (if Nat.eqb j k then (length l - 1)%nat else j) = Some y /\ (j < length l - 1)%nat.
Proof.
  intros X k l j y Hk Hj. pose proof (swap_remove_length k l Hk) as L. pose proof (nth_error_lt _ _ _ Hj) as Hlt. rewrite L in Hlt.
  split; [|exact Hlt]. unfold swap_remove in Hj. destruct l as [|x l']; [cbn in Hk; lia|].
  destruct (Nat.eqb_spec (S k) (length (x :: l'))) as [E|E].
  - rewrite nth_removelast in Hj by lia. destruct (Nat.eqb_spec j k) as [->|]; [lia | exact Hj].
  - destruct (Nat.eqb_spec j k) as [->|Hne].
    + rewrite nth_error_upd_same in Hj by (rewrite removelast_length; lia). injection Hj as <-. exact (last_nth (x :: l') x ltac:(discriminate)).
    + rewrite nth_error_upd_other in Hj by lia. rewrite nth_removelast in Hj by lia. exact Hj.
Qed.

Lemma swap_remove_incl : forall {X} (k : nat) (l : list X) y, (k < length l)%nat -> In y (swap_remove k l) -> In y l.
Proof.
  intros X k l y Hk Hy. destruct (In_nth_error _ _ Hy) as (j & Hj). destruct (swap_remove_nth k l j y Hk Hj) as (X1 & _).
  exact (nth_error_In _ _ X1).
Qed.

(* [comment removed for export] *)
Lemma swap_remove_keep : forall {X} (k : nat) (l : list X) j y, (k < length l)%nat -> j <> k -> nth_error l j = Some y ->
  In y (swap_remove k l).
Proof.
  intros X k l j y Hk Hne Hj. pose proof (nth_error_lt _ _ _ Hj) as Hjl. unfold swap_remove. destruct l as [|x l']; [cbn in Hk; lia|].
  destruct (Nat.eqb_spec (S k) (length (x :: l'))) as [E|E].
  - apply (nth_error_In _ j). rewrite nth_removelast by lia. exact Hj.
  - destruct (Nat.eq_dec j (length (x :: l') - 1)) as [Ej|Ej].
    + subst j. rewrite (last_nth (x :: l') x ltac:(discriminate)) in Hj. injection Hj as <-.
      apply (nth_error_In _ k). rewrite nth_error_upd_same by (rewrite removelast_length; lia). reflexivity.
    + apply (nth_error_In _ j). rewrite nth_error_upd_other by lia. rewrite nth_removelast by lia. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma swap_remove_pairs : forall {X} (k : nat) (l : list X) j1 j2 y1 y2, (k < length l)%nat ->
  nth_error (swap_remove k l) j1 = Some y1 -> nth_error (swap_remove k l) j2 = Some y2 -> j1 <> j2 ->
  exists i1 i2, i1 <> i2 /\ nth_error l i1 = Some y1 /\ nth_error l i2 = Some y2 /\ i1 <> k /\ i2 <> k.
Proof.
  intros X k l j1 j2 y1 y2 Hk H1 H2 Hne.
  destruct (swap_remove_nth k l j1 y1 Hk H1) as (A1 & B1). destruct (swap_remove_nth k l j2 y2 Hk H2) as (A2 & B2).
  exists (if Nat.eqb j1 k then (length l - 1)%nat else j1), (if Nat.eqb j2 k then (length l - 1)%nat else j2).
  split; [destruct (Nat.eqb_spec j1 k); destruct (Nat.eqb_spec j2 k); lia|]. split; [exact A1|]. split; [exact A2|].
  split; destruct (Nat.eqb_spec j1 k); destruct (Nat.eqb_spec j2 k); lia.
Qed.

Lemma swap_remove_other : forall {X} (k : nat) (l : list X) y, (k < length l)%nat -> In y (swap_remove k l) ->
  exists j, j <> k /\ nth_error l j = Some y.
Proof.
  intros X k l y Hk Hy. destruct (In_nth_error _ _ Hy) as (j & Hj). destruct (swap_remove_nth k l j y Hk Hj) as (A & B).
  exists (if Nat.eqb j k then (length l - 1)%nat else j). split; [destruct (Nat.eqb_spec j k); lia | exact A].
Qed.

(* [comment removed for export] *)
Lemma swap_remove_perm : forall {X} (k : nat) (l : list X) y, nth_error l k = Some y -> Permutation l (y :: swap_remove k l).
Proof.
  intros X k l y Hk. pose proof (nth_error_lt _ _ _ Hk) as Hkl. unfold swap_remove. destruct l as [|x l']; [cbn in Hkl; lia|].
  set (l := x :: l') in *. assert (Hne : l <> []) by discriminate.
  assert (E : l = removelast l ++ [last l x]) by (apply app_removelast_last; exact Hne).
  destruct (Nat.eqb_spec (S k) (length l)) as [Ek|Ek].
  - replace k with (length l - 1)%nat in Hk by lia. rewrite (last_nth l x Hne) in Hk. injection Hk as <-.
    rewrite E at 1. apply Permutation_sym. apply Permutation_cons_append.
  - rewrite <- (nth_removelast l k) in Hk by lia.
    destruct (nth_error_split (removelast l) k y Hk) as (pre & post & Ep & Lp).
    rewrite E at 1. rewrite Ep.
    assert (Eu : upd (pre ++ y :: post) k (last l x) = pre ++ last l x :: post).
    { clear -Lp. revert k Lp. induction pre as [|z pre IH]; intros k Lp; cbn in Lp; subst k; [reflexivity|]. cbn. rewrite IH by reflexivity. reflexivity. }
    rewrite Eu. rewrite <- app_assoc. cbn [app].
    eapply perm_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip. apply Permutation_app_head.
    apply Permutation_sym, Permutation_cons_append.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_cls_out : forall f g k c, (Z.of_nat k < c) -> (forall c', c' <> c -> f c' = g c') -> sum_cls f k = sum_cls g k.
Proof.
  intros f g k c Hk H. induction k as [|k IH]; [reflexivity|]. cbn [sum_cls]. rewrite H by lia. rewrite IH by lia. reflexivity.
Qed.

Lemma sum_cls_upd : forall f g k c, 1 <= c <= Z.of_nat k -> (forall c', c' <> c -> f c' = g c') ->
  sum_cls f k = sum_cls g k + (f c - g c).
Proof.
  intros f g k c Hc H. induction k as [|k IH]; [cbn in Hc; lia|]. cbn [sum_cls].
  destruct (Z.eq_dec c (Z.of_nat (S k))) as [E|E].
  - rewrite (sum_cls_out f g k c) by (try lia; exact H). rewrite <- E. lia.
  - rewrite H by lia. rewrite IH by lia. lia.
Qed.

Lemma secsum_app : forall l1 l2, fold_right (fun s acc => smsz (s_n s) + acc) 0 (l1 ++ l2)
  = fold_right (fun s acc => smsz (s_n s) + acc) 0 l1 + fold_right (fun s acc => smsz (s_n s) + acc) 0 l2.
Proof. intros l1 l2. induction l1 as [|s l1 IH]; cbn [app fold_right]; lia. Qed.

Lemma secsum_perm : forall l1 l2, Permutation l1 l2 ->
  fold_right (fun s acc => smsz (s_n s) + acc) 0 l1 = fold_right (fun s acc => smsz (s_n s) + acc) 0 l2.
Proof. intros l1 l2 H. induction H; cbn [fold_right]; lia. Qed.

Lemma smsz_pos : forall n, 64513 <= n -> 0 < smsz n.
Proof. intros n Hn. pose proof (smsz_room n ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma sum_cls_le : forall f k B, (forall j, (1 <= j <= k)%nat -> f (Z.of_nat j) <= B) -> sum_cls f k <= Z.of_nat k * B.
Proof.
  intros f k B H. induction k as [|k IH]; [cbn; lia|]. cbn [sum_cls]. pose proof (H (S k) ltac:(lia)) as X.
  assert (sum_cls f k <= Z.of_nat k * B) by (apply IH; intros j Hj; apply H; lia). lia.
Qed.

Lemma rt_eager_bound : forall Σ, regs_wf Σ -> sec_wf Σ -> secsum Σ <= CREDIT0 -> rt_eager Σ <= 2 ^ 38.
Proof.
  intros Σ (HR & _) HS Hss. unfold rt_eager.
  assert (H1 : sum_cls (fun c => r_muser (pr Σ c) + r_mfa (pr Σ c)) 31 <= Z.of_nat 31 * (kUserCap + kFaCap)).
  { apply sum_cls_le. intros j Hj. pose proof (HR (Z.of_nat j) ltac:(lia)) as (W1 & _ & _ & _ & W5 & _). lia. }
  destruct HS as (_ & HN & _). unfold secsum, CREDIT0, kUserCap, kFaCap in *. lia.
Qed.

Lemma rt_eager_recp : forall Σ c i, 1 <= c <= 31 ->
  rt_eager (recp Σ c i) = rt_eager Σ + (r_mfa (pr (recp Σ c i) c) - r_mfa (pr Σ c)).
Proof.
  intros Σ c i Hc. unfold rt_eager.
  pose proof (recp_fields Σ c i) as (_ & _ & Es & En & _).
  rewrite Es, En. rewrite (sum_cls_upd (fun c' => r_muser (pr (recp Σ c i) c') + r_mfa (pr (recp Σ c i) c'))
                                       (fun c' => r_muser (pr Σ c') + r_mfa (pr Σ c')) 31 c ltac:(lia)).
  - rewrite recp_muser. lia.
  - intros c' Hne. rewrite recp_pr. destruct (Z.eqb_spec c' c); [congruence | reflexivity].
Qed.

Lemma budget_wf_recp : forall Σ c i st, budget_wf Σ -> regs_wf Σ -> sec_wf Σ -> 1 <= c <= 31 ->
  nth_error (r_st (pr Σ c)) i = Some st -> st <> CkIdle -> ca_init Σ = true -> budget_wf (recp Σ c i).
Proof.
  intros Σ c i st (B1 & B2 & B3 & B4 & B5) HR HS Hc Hi Hst Hinit. pose proof (recp_fields Σ c i) as (_ & _ & Es & En & Ea & _ & _ & _ & _ & _ & _ & Ec & _).
  unfold budget_wf. rewrite Ea, Ec. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  assert (Hss : secsum (recp Σ c i) = secsum Σ) by (unfold secsum; rewrite Es; reflexivity). rewrite Hss.
  split; [|exact B5]. apply rt_eager_bound; [exact (regs_wf_recp Σ c i st HR Hc Hi Hst Hinit) | | unfold CREDIT0 in *; lia].
  unfold sec_wf in *. rewrite Es, En, Ea. exact HS.
Qed.

Lemma live_wf_recp : forall Σ c i st, live_wf Σ -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  (forall n, st <> CkAlloc n) -> live_wf (recp Σ c i).
Proof.
  intros Σ c i st (V1 & V2 & V3 & V4 & V5) Hc Hi Hst. pose proof (recp_fields Σ c i) as (El & _ & Es & _ & _ & _ & _ & _ & _ & _ & _ & _ & Elv & _).
  unfold live_wf. rewrite Elv, Es, El. split; [exact V1|]. split; [exact V2|]. split.
  - intros p n Hin. destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|X]; [left | right; exact X].
    exists c', i'. split; [exact Hc'|]. split; [|exact Ep]. rewrite recp_st.
    destruct (Z.eqb_spec c' c) as [->|Hne]; cbn [andb]; [|exact Hn].
    destruct (Nat.eqb_spec i i') as [<-|Hii]; [rewrite Hi in Hn; injection Hn as Hn; exact (False_ind _ (Hst n Hn)) | exact Hn].
  - split; [|exact V5]. intros c' i' n Hc' Hn. apply (V4 c' i' n Hc'). rewrite recp_st in Hn.
    destruct (Z.eqb_spec c' c) as [->|Hne]; cbn [andb] in Hn; [|exact Hn].
    destruct (Nat.eqb_spec i i') as [<-|Hii]; [destruct (Nat.ltb _ _); discriminate | exact Hn].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_app_cons_neq : forall {X} (A B : list X) e x, In x (A ++ e :: B) -> x <> e -> In x (A ++ B).
Proof.
  intros X A B e x H Hne. apply in_app_or in H as [H|[H|H]]; [apply in_or_app; left; exact H | congruence | apply in_or_app; right; exact H].
Qed.

Lemma nodup_map_cons_mid : forall {X Y} (f : X -> Y) (A B : list X) e, NoDup (map f (A ++ e :: B)) ->
  NoDup (map f (A ++ B)) /\ ~ In (f e) (map f (A ++ B)).
Proof.
  intros X Y f A B e H. apply NoDup_ListNoDup in H. rewrite map_app in H. cbn [map] in H.
  pose proof (List.NoDup_remove_1 _ _ _ H) as H1. pose proof (List.NoDup_remove_2 _ _ _ H) as H2.
  rewrite map_app. split; [apply NoDup_ListNoDup; exact H1 | exact H2].
Qed.

Lemma qentsP_pop : forall Σ b e es rest,
  qentsP Σ ((b, e :: es) :: rest) = flat_map snd (ql Σ ++ qg Σ) ++ e :: (es ++ flat_map snd rest).
Proof. intros. unfold qentsP, qallP. rewrite app_assoc, flat_map_app. reflexivity. Qed.
Lemma qentsP_rest : forall Σ b es rest,
  qentsP Σ ((b, es) :: rest) = flat_map snd (ql Σ ++ qg Σ) ++ (es ++ flat_map snd rest).
Proof. intros. unfold qentsP, qallP. rewrite app_assoc, flat_map_app. reflexivity. Qed.

Lemma qallP_fst_pop : forall Σ Σ' b es es' rest, ql Σ' = ql Σ -> qg Σ' = qg Σ ->
  map fst (qallP Σ' ((b, es') :: rest)) = map fst (qallP Σ ((b, es) :: rest)).
Proof. intros Σ Σ' b es es' rest E1 E2. unfold qallP. rewrite E1, E2. rewrite !map_app. reflexivity. Qed.

Lemma qbytes_pop : forall b e es rest, qbytes ((b, e :: es) :: rest) = snd e + qbytes ((b, es) :: rest).
Proof. intros. unfold qbytes, qsum, qn. cbn [fold_right snd length]. lia. Qed.

Lemma qbytes_nonneg' : forall bs, Forall (fun e => 0 <= snd e) (flat_map snd bs) -> 0 <= qbytes bs.
Proof.
  intros bs H. unfold qbytes. assert (0 <= qsum bs); [|lia]. induction bs as [|[b es] bs IH]; [cbn; lia|].
  cbn [flat_map snd] in H. apply Forall_app in H as [H1 H2]. unfold qsum in *. cbn [fold_right]. specialize (IH H2).
  assert (0 <= qn (b, es)); [|lia]. unfold qn. cbn [snd]. clear -H1. induction es as [|e es IH]; cbn [fold_right]; [lia|].
  inversion H1; subst. specialize (IH H3). lia.
Qed.

Lemma qent_n_pos : forall Σ e, regs_wf Σ -> sec_wf Σ -> qent_ok Σ e -> 1 <= snd e.
Proof.
  intros Σ e HR HS [(c & i & Hc & Hi & _)|(s & Hs & _ & Hn & _)].
  - pose proof (hdr_geo Σ c i (snd e) HR Hc (or_introl Hi)) as (X & _). exact X.
  - destruct HS as (_ & _ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF s Hs) as (X & _). lia.
Qed.

(* [comment removed for export] *)
Theorem rt_wfP_recp : forall Σ b h n es rest c i, rt_wfP Σ ((b, (h, n) :: es) :: rest) -> 1 <= c <= 31 ->
  nth_error (r_st (pr Σ c)) i = Some (CkQuar n) -> h = p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 -> ca_init Σ = true ->
  rt_wfP (recp Σ c i) ((b, es) :: rest).
Proof.
  intros Σ b h n es rest c i HW Hc Hi Eh Hinit.
  destruct HW as (H1 & HR & HV & HS & HQ & H6 & HB & H8 & H9 & H10 & H11 & (K1 & K2)).
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof (recp_fields Σ c i) as (El & Eci & Es & En & Ea & Eql & Eqg & Ed & E0 & E2 & E4 & Ec & Elv & Efr).
  assert (Hst : forall c' j st', c' <> c \/ j <> i -> nth_error (r_st (pr (recp Σ c i) c')) j = Some st' -> nth_error (r_st (pr Σ c')) j = Some st').
  { intros c' j st' Hne H. rewrite recp_st in H. destruct (Z.eqb_spec c' c) as [->|Hcc]; cbn [andb] in H; [|exact H].
    destruct (Nat.eqb_spec i j) as [<-|Hij]; [destruct Hne as [Hne|Hne]; congruence | exact H]. }
  assert (Hst' : forall c' j st', c' <> c \/ j <> i -> nth_error (r_st (pr Σ c')) j = Some st' -> nth_error (r_st (pr (recp Σ c i) c')) j = Some st').
  { intros c' j st' Hne H. rewrite recp_st. destruct (Z.eqb_spec c' c) as [->|Hcc]; cbn [andb]; [|exact H].
    destruct (Nat.eqb_spec i j) as [<-|Hij]; [destruct Hne as [Hne|Hne]; congruence | exact H]. }
  rewrite qentsP_pop in Q7, Q8, K1, K2.
  destruct (nodup_map_cons_mid fst _ _ _ Q8) as (ND & NIN). cbn [fst] in NIN.
  (* [comment removed for export] *)
  assert (Hne_e : forall c' j n', 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) j = Some (CkQuar n') ->
            In (p_abeg (l_SB (lay Σ)) c' j + rz_size n' - 16, n') (flat_map snd (ql Σ ++ qg Σ) ++ es ++ flat_map snd rest) -> c' <> c \/ j <> i).
  { intros c' j n' Hc' Hj Hin. destruct (Z.eq_dec c' c) as [->|Hcc]; [|left; exact Hcc]. destruct (Nat.eq_dec j i) as [->|Hji]; [|right; exact Hji].
    rewrite Hi in Hj. injection Hj as <-. exfalso. apply NIN. rewrite Eh. apply in_map_iff. eexists; split; [|exact Hin]. reflexivity. }
  split; [rewrite El; exact H1|]. split; [exact (regs_wf_recp Σ c i (CkQuar n) HR Hc Hi ltac:(discriminate) Hinit)|].
  split; [exact (live_wf_recp Σ c i (CkQuar n) HV Hc Hi ltac:(discriminate))|].
  split; [unfold sec_wf; rewrite Es, En, El, Ea; exact HS|].
  split.
  { unfold quar_wfP. rewrite Eql, Eqg, El. rewrite (qallP_fst_pop (recp Σ c i) Σ b ((h, n) :: es) es rest Eql Eqg).
    rewrite qentsP_rest. rewrite Eql, Eqg.
    split; [exact Q1|]. split; [exact Q2|]. split; [rewrite qbytes_pop in Q3; pose proof (qent_n_pos Σ (h, n) HR HS (proj1 (Forall_forall _ _) Q7 (h, n) ltac:(apply in_or_app; right; left; reflexivity))); cbn [snd] in *; lia|].
    split.
    { unfold qallP in Q4 |- *. rewrite Eql, Eqg. apply Forall_app in Q4 as [Q4a Q4b]. apply Forall_app in Q4b as [Q4b Q4c]. inversion Q4c as [|? ? Q4d Q4e]; subst.
      assert (BK : forall x : batch, (exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst x = p_abeg (l_SB (lay Σ)) 24 j) ->
                    exists j, nth_error (r_st (pr (recp Σ c i) 24)) j = Some CkBatch /\ fst x = p_abeg (l_SB (lay Σ)) 24 j).
      { intros x (j & Hj & Ex). exists j. split; [|exact Ex]. apply Hst'; [|exact Hj].
        destruct (Z.eq_dec 24 c) as [<-|Hcc]; [|left; lia]. destruct (Nat.eq_dec j i) as [->|Hji]; [|right; exact Hji]. rewrite Hi in Hj. discriminate. }
      apply Forall_app. split; [apply Forall_forall; intros x Hx; exact (BK x (proj1 (Forall_forall _ _) Q4a x Hx))|].
      apply Forall_app. split; [apply Forall_forall; intros x Hx; exact (BK x (proj1 (Forall_forall _ _) Q4b x Hx))|].
      constructor; [exact (BK _ Q4d) | apply Forall_forall; intros x Hx; exact (BK x (proj1 (Forall_forall _ _) Q4e x Hx))]. }
    split; [exact Q5|].
    split.
    { unfold qallP in Q6 |- *. rewrite Eql, Eqg. apply Forall_app in Q6 as [Q6a Q6b]. apply Forall_app in Q6b as [Q6b Q6c]. inversion Q6c as [|? ? Q6d Q6e]; subst.
      apply Forall_app. split; [exact Q6a|]. apply Forall_app. split; [exact Q6b|]. constructor; [cbn in Q6d |- *; lia | exact Q6e]. }
    split.
    { apply Forall_forall. intros e' He'. pose proof (proj1 (Forall_forall _ _) Q7 e' ltac:(apply in_app_or in He' as [X|X]; apply in_or_app; [left; exact X | right; right; exact X])) as X.
      destruct X as [(c' & j & Hc' & Hj & Ej)|(s & Hs & Hq & Hn & Es')]; [left | right].
      - exists c', j. split; [exact Hc'|]. try rewrite El. split; [|exact Ej]. apply Hst'; [|exact Hj].
        apply (Hne_e c' j (snd e') Hc' Hj). rewrite <- Ej. destruct e'; exact He'.
      - exists s. rewrite Es. split; [exact Hs|]. split; [exact Hq|]. split; [exact Hn | exact Es']. }
    split; [exact ND|].
    intros c' j Hc' Hj. destruct (Z.eq_dec c' c) as [->|Hcc].
    - destruct (Nat.eq_dec j i) as [->|Hji].
      + rewrite recp_st, Z.eqb_refl, Nat.eqb_refl in Hj. cbn [andb] in Hj. destruct (Nat.ltb _ _); discriminate.
      + try rewrite El. apply (Q9 c j Hc'). apply Hst; [right; exact Hji | exact Hj].
    - try rewrite El. apply (Q9 c' j Hc'). apply Hst; [left; exact Hcc | exact Hj]. }
  split; [exact H6|]. split; [exact (budget_wf_recp Σ c i (CkQuar n) HB HR HS Hc Hi ltac:(discriminate) Hinit)|].
  split; [rewrite Ed, El; exact H8|]. split; [rewrite Ed; exact H9|]. split; [rewrite Ed; exact H10|]. split; [rewrite Ed; exact H11|].
  unfold rt_countP. rewrite qentsP_rest. rewrite Eql, Eqg, El, Es. split.
  - intros c' j n' Hc' Hj. assert (Hne : c' <> c \/ j <> i).
    { destruct (Z.eq_dec c' c) as [->|Hcc]; [|left; exact Hcc]. destruct (Nat.eq_dec j i) as [->|Hji]; [|right; exact Hji].
      rewrite recp_st, Z.eqb_refl, Nat.eqb_refl in Hj. cbn [andb] in Hj. destruct (Nat.ltb _ _); discriminate. }
    pose proof (Hst c' j (CkQuar n') Hne Hj) as Hj0. pose proof (K1 c' j n' Hc' Hj0) as Hin. apply (in_app_cons_neq _ _ _ _ Hin).
    intros E. injection E as Ex1 Ex2. subst n'. destruct (hdr_inj Σ c' j n c i n HR Hc' Hc Hj0 Hi ltac:(rewrite <- Eh; exact Ex1)) as (A1 & A2).
    destruct Hne as [Hne|Hne]; congruence.
  - intros s Hs Hq. pose proof (K2 s Hs Hq) as Hin. apply (in_app_cons_neq _ _ _ _ Hin). intros E. injection E as Ex1 Ex2.
    exact (hdr_prim_sec Σ c i n s H1 HR HS Hc Hi Hs ltac:(rewrite <- Eh; exact (eq_sym Ex1))).
Qed.

(* [comment removed for export] *)
Theorem rt_wfP_batch : forall Σ b rest ib, rt_wfP Σ ((b, []) :: rest) ->
  nth_error (r_st (pr Σ 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σ)) 24 ib -> ca_init Σ = true ->
  rt_wfP (recp Σ 24 ib) rest.
Proof.
  intros Σ b rest ib HW Hi Eb Hinit.
  destruct HW as (H1 & HR & HV & HS & HQ & H6 & HB & H8 & H9 & H10 & H11 & (K1 & K2)).
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof (recp_fields Σ 24 ib) as (El & Eci & Es & En & Ea & Eql & Eqg & Ed & E0 & E2 & E4 & Ec & Elv & Efr).
  assert (Hc : 1 <= 24 <= 31) by lia.
  assert (Hst : forall c' j st', c' <> 24 \/ j <> ib -> nth_error (r_st (pr (recp Σ 24 ib) c')) j = Some st' -> nth_error (r_st (pr Σ c')) j = Some st').
  { intros c' j st' Hne H. rewrite recp_st in H. destruct (Z.eqb_spec c' 24) as [->|Hcc]; cbn [andb] in H; [|exact H].
    destruct (Nat.eqb_spec ib j) as [<-|Hij]; [destruct Hne as [Hne|Hne]; congruence | exact H]. }
  assert (Hst' : forall c' j st', c' <> 24 \/ j <> ib -> nth_error (r_st (pr Σ c')) j = Some st' -> nth_error (r_st (pr (recp Σ 24 ib) c')) j = Some st').
  { intros c' j st' Hne H. rewrite recp_st. destruct (Z.eqb_spec c' 24) as [->|Hcc]; cbn [andb]; [|exact H].
    destruct (Nat.eqb_spec ib j) as [<-|Hij]; [destruct Hne as [Hne|Hne]; congruence | exact H]. }
  assert (EQ : qentsP (recp Σ 24 ib) rest = qentsP Σ ((b, []) :: rest)).
  { unfold qentsP, qallP. rewrite Eql, Eqg. rewrite !flat_map_app. reflexivity. }
  assert (EA : qallP Σ ((b, []) :: rest) = (ql Σ ++ qg Σ) ++ (b, []) :: rest) by (unfold qallP; rewrite app_assoc; reflexivity).
  assert (EA' : qallP (recp Σ 24 ib) rest = (ql Σ ++ qg Σ) ++ rest) by (unfold qallP; rewrite Eql, Eqg, app_assoc; reflexivity).
  rewrite EA in Q4, Q5, Q6, Q9.
  destruct (nodup_map_cons_mid fst _ _ _ Q5) as (ND & NIN). cbn [fst] in NIN.
  (* [comment removed for export] *)
  assert (Hoth : forall j, In (p_abeg (l_SB (lay Σ)) 24 j) (map fst ((ql Σ ++ qg Σ) ++ rest)) -> j <> ib).
  { intros j Hin ->. rewrite <- Eb in Hin. exact (NIN Hin). }
  assert (Hinj : forall j, p_abeg (l_SB (lay Σ)) 24 j = p_abeg (l_SB (lay Σ)) 24 ib -> j = ib).
  { intros j E. unfold p_abeg in E. change (ClassSize 24) with 8192 in E. lia. }
  split; [rewrite El; exact H1|]. split; [exact (regs_wf_recp Σ 24 ib CkBatch HR Hc Hi ltac:(discriminate) Hinit)|].
  split; [exact (live_wf_recp Σ 24 ib CkBatch HV Hc Hi ltac:(discriminate))|].
  split; [unfold sec_wf; rewrite Es, En, El, Ea; exact HS|].
  split.
  { unfold quar_wfP. rewrite Eql, Eqg, El, EQ, EA'. rewrite qentsP_rest in Q7, Q8 |- *. cbn [app] in Q7, Q8 |- *.
    split; [exact Q1|]. split; [exact Q2|]. split; [unfold qbytes, qsum, qn in Q3 |- *; cbn [fold_right length snd] in Q3; lia|].
    split.
    { apply Forall_app in Q4 as [Q4a Q4b]. inversion Q4b as [|? ? Q4d Q4e]; subst.
      apply Forall_forall. intros x Hx.
      assert (Hx0 : exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst x = p_abeg (l_SB (lay Σ)) 24 j).
      { apply in_app_or in Hx as [Hx|Hx]; [exact (proj1 (Forall_forall _ _) Q4a x Hx) | exact (proj1 (Forall_forall _ _) Q4e x Hx)]. }
      destruct Hx0 as (j & Hj & Ex). exists j. split; [|exact Ex]. apply Hst'; [right; apply Hoth; rewrite <- Ex; apply in_map; exact Hx | exact Hj]. }
    split; [exact ND|].
    split; [apply Forall_app in Q6 as [Q6a Q6b]; inversion Q6b; subst; apply Forall_app; split; assumption|].
    split.
    { apply Forall_forall. intros e' He'. destruct (proj1 (Forall_forall _ _) Q7 e' He') as [(c' & j & Hc' & Hj & Ej)|(s & Hs & Hq & Hn & Es')]; [left | right].
      - exists c', j. split; [exact Hc'|]. split; [|exact Ej]. apply Hst'; [|exact Hj].
        destruct (Z.eq_dec c' 24) as [->|Hcc]; [|left; exact Hcc]. destruct (Nat.eq_dec j ib) as [->|Hji]; [|right; exact Hji].
        rewrite Hi in Hj. discriminate.
      - exists s. rewrite Es. split; [exact Hs|]. split; [exact Hq|]. split; [exact Hn | exact Es']. }
    split; [exact Q8|].
    intros c' j Hc' Hj. destruct (Z.eq_dec c' 24) as [->|Hcc].
    - destruct (Nat.eq_dec j ib) as [->|Hji].
      + rewrite recp_st, Z.eqb_refl, Nat.eqb_refl in Hj. cbn [andb] in Hj. destruct (Nat.ltb _ _); discriminate.
      + destruct (Q9 24 j Hc' (Hst 24 j CkBatch (or_intror Hji) Hj)) as (_ & Hin). split; [reflexivity|].
        rewrite map_app in Hin |- *. cbn [map] in Hin. apply in_app_or in Hin as [Hin|[Hin|Hin]]; [apply in_or_app; left; exact Hin | | apply in_or_app; right; exact Hin].
        exfalso. apply Hji. apply Hinj. rewrite <- Eb. exact (eq_sym Hin).
    - destruct (Q9 c' j Hc' (Hst c' j CkBatch (or_introl Hcc) Hj)) as (E24 & _). exfalso. exact (Hcc E24). }
  split; [exact H6|]. split; [exact (budget_wf_recp Σ 24 ib CkBatch HB HR HS Hc Hi ltac:(discriminate) Hinit)|].
  split; [rewrite Ed, El; exact H8|]. split; [rewrite Ed; exact H9|]. split; [rewrite Ed; exact H10|]. split; [rewrite Ed; exact H11|].
  unfold rt_countP. rewrite EQ, El, Es. split.
  - intros c' j n' Hc' Hj. apply (K1 c' j n' Hc'). apply Hst; [|exact Hj].
    destruct (Z.eq_dec c' 24) as [->|Hcc]; [|left; exact Hcc]. destruct (Nat.eq_dec j ib) as [->|Hji]; [|right; exact Hji].
    rewrite recp_st, Z.eqb_refl, Nat.eqb_refl in Hj. cbn [andb] in Hj. destruct (Nat.ltb _ _); discriminate.
  - exact K2.
Qed.

(* [comment removed for export] *)
Lemma recs_fields : forall Σ k, lay (recs Σ k) = lay Σ /\ pr (recs Σ k) = pr Σ /\ ca (recs Σ k) = ca Σ /\ ca_init (recs Σ k) = ca_init Σ
  /\ sec (recs Σ k) = swap_remove k (sec Σ) /\ sec_nres (recs Σ k) = sec_nres Σ /\ aw (recs Σ k) = aw Σ
  /\ ql (recs Σ k) = ql Σ /\ qg (recs Σ k) = qg Σ /\ dep (recs Σ k) = dep Σ
  /\ credit (recs Σ k) = credit Σ /\ live (recs Σ k) = live Σ /\ frames (recs Σ k) = frames Σ.
Proof. intros Σ k. repeat split; reflexivity. Qed.

Lemma secsum_recs : forall Σ k s, nth_error (sec Σ) k = Some s -> secsum Σ = smsz (s_n s) + secsum (recs Σ k).
Proof.
  intros Σ k s Hk. unfold secsum. rewrite (secsum_perm (sec Σ) (s :: swap_remove k (sec Σ)) (swap_remove_perm k (sec Σ) s Hk)).
  reflexivity.
Qed.

Lemma sec_wf_recs : forall Σ k s, sec_wf Σ -> nth_error (sec Σ) k = Some s -> sec_wf (recs Σ k).
Proof.
  intros Σ k s (S1 & S2 & S3 & S4 & S5 & S6) Hk. pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  pose proof (recs_fields Σ k) as (El & _ & _ & _ & Es & En & Ea & _).
  unfold sec_wf. rewrite El, Es, En, Ea. rewrite swap_remove_length by exact Hkl.
  split; [lia|]. split; [exact S2|]. split; [intros _; apply S3; intros E; rewrite E in Hk; destruct k; discriminate|].
  split; [apply Forall_forall; intros x Hx; exact (proj1 (Forall_forall _ _) S4 x (swap_remove_incl k _ x Hkl Hx))|].
  split.
  - intros k1 k2 s1 s2 H1 H2 Hne. destruct (swap_remove_pairs k (sec Σ) k1 k2 s1 s2 Hkl H1 H2 Hne) as (i1 & i2 & Hi & A1 & A2 & _).
    exact (S5 i1 i2 s1 s2 A1 A2 Hi).
  - apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) S6 x (swap_remove_incl k _ x Hkl Hx)).
Qed.

Theorem rt_wfP_recs : forall Σ b h n es rest k s, rt_wfP Σ ((b, (h, n) :: es) :: rest) ->
  nth_error (sec Σ) k = Some s -> s_quar s = true -> h = s_mb s + 6128 -> n = s_n s ->
  rt_wfP (recs Σ k) ((b, es) :: rest).
Proof.
  intros Σ b h n es rest k s HW Hk Hq Eh En'.
  destruct HW as (H1 & HR & HV & HS & HQ & H6 & HB & H8 & H9 & H10 & H11 & (K1 & K2)).
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof (recs_fields Σ k) as (El & Epr & Eca & Eci & Es & En & Ea & Eql & Eqg & Ed & Ec & Elv & Efr).
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  rewrite qentsP_pop in Q7, Q8, K1, K2.
  destruct (nodup_map_cons_mid fst _ _ _ Q8) as (ND & NIN). cbn [fst] in NIN.
  (* [comment removed for export] *)
  assert (Hsk : forall s', In s' (sec Σ) -> s_mb s' + 6128 <> h -> In s' (swap_remove k (sec Σ))).
  { intros s' Hs' Hne. destruct (In_nth_error _ _ Hs') as (j & Hj). apply (swap_remove_keep k _ j s' Hkl); [|exact Hj].
    intros ->. rewrite Hk in Hj. injection Hj as <-. exact (Hne (eq_sym Eh)). }
  assert (Hsk' : forall s', In s' (swap_remove k (sec Σ)) -> In s' (sec Σ) /\ s_mb s' <> s_mb s).
  { intros s' Hs'. destruct (swap_remove_other k _ s' Hkl Hs') as (j & Hj & Ej). split; [exact (nth_error_In _ _ Ej)|].
    intros E. exact (Hj (sec_pos_inj Σ j k s' s HS Ej Hk E)). }
  split; [rewrite El; exact H1|]. split; [unfold regs_wf; rewrite Epr, Eca, Eci; exact HR|].
  split.
  { destruct HV as (V1 & V2 & V3 & V4 & V5). unfold live_wf. rewrite Elv, Epr, El, Es.
    split; [exact V1|]. split; [exact V2|]. split.
    - intros p n0 Hin. destruct (V3 p n0 Hin) as [X|(s' & Hs' & Hq' & Hn' & Ep)]; [left; exact X | right].
      exists s'. split; [|split; [exact Hq' | split; [exact Hn' | exact Ep]]]. apply Hsk; [exact Hs'|].
      intros E. assert (s_mb s' = s_mb s) by lia. destruct (In_nth_error _ _ Hs') as (j & Hj).
      pose proof (sec_pos_inj Σ j k s' s HS Hj Hk H) as ->. rewrite Hk in Hj. injection Hj as ->. congruence.
    - split; [exact V4|]. intros s' Hs' Hq'. exact (V5 s' (proj1 (Hsk' s' Hs')) Hq'). }
  split; [exact (sec_wf_recs Σ k s HS Hk)|].
  split.
  { unfold quar_wfP. rewrite Eql, Eqg, El, Epr. rewrite (qallP_fst_pop (recs Σ k) Σ b ((h, n) :: es) es rest Eql Eqg).
    rewrite qentsP_rest. rewrite Eql, Eqg.
    split; [exact Q1|]. split; [exact Q2|]. split; [rewrite qbytes_pop in Q3; pose proof (qent_n_pos Σ (h, n) HR HS (proj1 (Forall_forall _ _) Q7 (h, n) ltac:(apply in_or_app; right; left; reflexivity))); cbn [snd] in *; lia|].
    split; [unfold qallP in Q4 |- *; rewrite Eql, Eqg; try rewrite Epr; try rewrite El; apply Forall_app in Q4 as [Q4a Q4b]; apply Forall_app in Q4b as [Q4b Q4c];
            inversion Q4c; subst; apply Forall_app; split; [exact Q4a|]; apply Forall_app; split; [exact Q4b|]; constructor; assumption|].
    split; [exact Q5|].
    split.
    { unfold qallP in Q6 |- *. rewrite Eql, Eqg. apply Forall_app in Q6 as [Q6a Q6b]. apply Forall_app in Q6b as [Q6b Q6c]. inversion Q6c as [|? ? Q6d Q6e]; subst.
      apply Forall_app. split; [exact Q6a|]. apply Forall_app. split; [exact Q6b|]. constructor; [cbn in Q6d |- *; lia | exact Q6e]. }
    split.
    { apply Forall_forall. intros e' He'. pose proof (proj1 (Forall_forall _ _) Q7 e' ltac:(apply in_app_or in He' as [X|X]; apply in_or_app; [left; exact X | right; right; exact X])) as X.
      destruct X as [(c' & j & Hc' & Hj & Ej)|(s' & Hs' & Hq' & Hn' & Es')]; [left | right].
      - exists c', j. try rewrite Epr; try rewrite El. exact (conj Hc' (conj Hj Ej)).
      - exists s'. rewrite Es. split; [|exact (conj Hq' (conj Hn' Es'))]. apply Hsk; [exact Hs'|].
        intros E. apply NIN. rewrite <- E, <- Es'. apply in_map. exact He'. }
    split; [exact ND|].
    intros c' j Hc' Hj. try rewrite Epr in Hj. exact (Q9 c' j Hc' Hj). }
  split; [exact H6|].
  split.
  { destruct HB as (B1 & B2 & B3 & B4 & B5). unfold budget_wf. rewrite Ea, Ec. pose proof (secsum_recs Σ k s Hk) as Ess.
    assert (Hsn : 64513 <= s_n s) by (destruct HS as (_ & _ & _ & HF & _); destruct (proj1 (Forall_forall _ _) HF s (nth_error_In _ _ Hk)) as ((X & _) & _); exact X).
    pose proof (smsz_pos (s_n s) Hsn). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    split; [apply rt_eager_bound; [unfold regs_wf; rewrite Epr, Eca, Eci; exact HR | exact (sec_wf_recs Σ k s HS Hk) | unfold CREDIT0 in *; lia] | lia]. }
  split; [rewrite Ed, El; exact H8|]. split; [rewrite Ed; exact H9|]. split; [rewrite Ed; exact H10|]. split; [rewrite Ed; exact H11|].
  unfold rt_countP. rewrite qentsP_rest. rewrite Eql, Eqg, El, Es, Epr. split.
  - intros c' j n' Hc' Hj. pose proof (K1 c' j n' Hc' Hj) as Hin. apply (in_app_cons_neq _ _ _ _ Hin). intros E. injection E as Ex1 Ex2.
    exact (hdr_prim_sec Σ c' j n' s H1 HR HS Hc' Hj (nth_error_In _ _ Hk) ltac:(rewrite <- Eh; exact Ex1)).
  - intros s' Hs' Hq'. destruct (Hsk' s' Hs') as (Hs0 & Hne). pose proof (K2 s' Hs0 Hq') as Hin. apply (in_app_cons_neq _ _ _ _ Hin).
    intros E. injection E as Ex1 Ex2. apply Hne. lia.
Qed.

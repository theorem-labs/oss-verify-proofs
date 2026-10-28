(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_cache_defs R_prim_defs R_popfree R_popfree_B R_popfree_T R_getfrom R_prim_lists RT_state RT_rep RT_malstate RT_refillstmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_cls_upd : forall (f g : Z -> Z) (k : nat) (c : Z), 1 <= c <= Z.of_nat k -> (forall c', c' <> c -> g c' = f c') ->
  sum_cls g k = sum_cls f k + g c - f c.
Proof.
  intros f g k. induction k as [|k IH]; intros c Hc Hfg; [lia|].
  cbn [sum_cls]. destruct (Z.eq_dec (Z.of_nat (S k)) c) as [E|E].
  - rewrite <- E. rewrite (sum_cls_ext g f k) by (intros j Hj; apply Hfg; lia). lia.
  - rewrite (Hfg _ E). rewrite (IH c ltac:(lia) Hfg). lia.
Qed.

Lemma rt_eager_one : forall Σ Σ' c, 1 <= c <= 31 -> sec Σ' = sec Σ -> sec_nres Σ' = sec_nres Σ ->
  (forall c', c' <> c -> pr Σ' c' = pr Σ c') ->
  rt_eager Σ' = rt_eager Σ + (r_muser (pr Σ' c) + r_mfa (pr Σ' c)) - (r_muser (pr Σ c) + r_mfa (pr Σ c)).
Proof.
  intros Σ Σ' c Hc E1 E2 Hpr. unfold rt_eager. rewrite E1, E2.
  rewrite (sum_cls_upd (fun c0 => r_muser (pr Σ c0) + r_mfa (pr Σ c0)) (fun c0 => r_muser (pr Σ' c0) + r_mfa (pr Σ' c0)) 31 c)
    by (first [lia | intros c' Hne; rewrite (Hpr c' Hne); reflexivity]).
  lia.
Qed.

(* [comment removed for export] *)
Definition set_reg (Σ : rtsA) (c : Z) (r : regst) : rtsA :=
  mkRtsA (lay Σ) (fun c' => if c' =? c then r else pr Σ c') (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

Lemma rt_eager_set_reg : forall Σ c r, 1 <= c <= 31 ->
  rt_eager (set_reg Σ c r) = rt_eager Σ + (r_muser r + r_mfa r) - (r_muser (pr Σ c) + r_mfa (pr Σ c)).
Proof.
  intros Σ c r Hc. rewrite (rt_eager_one Σ (set_reg Σ c r) c Hc eq_refl eq_refl).
  - cbn [set_reg pr]. rewrite Z.eqb_refl. reflexivity.
  - intros c' Hne. cbn [set_reg pr]. rewrite (proj2 (Z.eqb_neq c' c) Hne). reflexivity.
Qed.

Lemma rt_eager_refill : forall Σ c, 1 <= c <= 31 ->
  rt_eager (refillΣ Σ c) = rt_eager Σ + (r_muser (refill_reg (pr Σ c) c) + r_mfa (refill_reg (pr Σ c) c))
                            - (r_muser (pr Σ c) + r_mfa (pr Σ c)).
Proof.
  intros Σ c Hc. rewrite (rt_eager_one Σ (refillΣ Σ c) c Hc eq_refl eq_refl).
  - cbn [refillΣ pr]. rewrite Z.eqb_refl. reflexivity.
  - intros c' Hne. cbn [refillΣ pr]. rewrite (proj2 (Z.eqb_neq c' c) Hne). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rf_nf (r : regst) : Z := Z.of_nat (length (r_fl r)).
Definition rf_au (r : regst) (c : Z) : Z := ClassSize c * Z.of_nat (length (r_st r)).
Definition rf_k (r : regst) (c : Z) : Z := MaxCount c / 2 - rf_nf r.
Definition rf_msz (r : regst) (c : Z) : Z := umap_size (rf_au r c) (r_muser r) (rf_k r c) (ClassSize c).
Definition rf_newc (r : regst) (c : Z) : Z := pfa_newc (rf_au r c) (r_muser r) (rf_msz r c) (ClassSize c).
Definition rf_mfa (r : regst) (c : Z) : Z :=
  if r_mfa r <? 4 * (rf_nf r + rf_newc r c) then round_fa (4 * (rf_nf r + rf_newc r c)) else r_mfa r.
Definition rf_fl (r : regst) (c : Z) : list Z :=
  r_fl r ++ rev (map (fun j => Z.of_nat (length (r_st r)) + Z.of_nat j) (seq 0 (Z.to_nat (rf_newc r c)))).

Lemma MaxCount_half : forall c, 1 <= c <= 31 -> 1 <= MaxCount c / 2 <= 8.
Proof.
  intros c Hc. pose proof (MaxCount_range c Hc) as (H1 & _).
  split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia.
Qed.

(* [comment removed for export] *)
Lemma rf_fast : forall r c, MaxCount c / 2 <= rf_nf r ->
  refill_reg r c = mkReg (r_muser r) (r_mfa r) (r_st r) (firstn (length (r_fl r) - Z.to_nat (MaxCount c / 2)) (r_fl r))
  /\ refill_ca r c = skipn (length (r_fl r) - Z.to_nat (MaxCount c / 2)) (r_fl r).
Proof.
  intros r c H. unfold refill_reg, refill_ca, rf_nf in *. rewrite (proj2 (Z.ltb_ge _ _) H). split; [destruct r; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rf_slow : forall r c, 1 <= c <= 31 -> reg_wf c r -> rf_nf r < MaxCount c / 2 ->
  refill_reg r c = mkReg (r_muser r + rf_msz r c) (rf_mfa r c) (r_st r ++ repeat CkIdle (Z.to_nat (rf_newc r c)))
                     (firstn (length (rf_fl r c) - Z.to_nat (MaxCount c / 2)) (rf_fl r c))
  /\ refill_ca r c = skipn (length (rf_fl r c) - Z.to_nat (MaxCount c / 2)) (rf_fl r c).
Proof.
  intros r c Hc HW H. pose proof (ClassSize_range c Hc) as (HS & _). destruct HW as (_ & _ & W3 & W4 & _).
  assert (Hlt : r_muser r < rf_au r c + rf_k r c * ClassSize c).
  { unfold rf_au, rf_k. assert (1 <= MaxCount c / 2 - rf_nf r) by lia. clear - W4 H0 HS. nia. }
  assert (EP : populate r (ClassSize c) (rf_k r c) = mkReg (r_muser r + rf_msz r c) (rf_mfa r c)
                 (r_st r ++ repeat CkIdle (Z.to_nat (rf_newc r c))) (rf_fl r c)).
  { unfold populate. fold (rf_au r c). rewrite (proj2 (Z.ltb_lt _ _) Hlt). unfold rf_mfa, rf_fl, rf_newc, pfa_newc, rf_msz, umap_size, rf_nf.
    f_equal. }
  unfold refill_reg, refill_ca. rewrite (proj2 (Z.ltb_lt _ _) H). fold (rf_k r c). rewrite EP. cbn [r_muser r_mfa r_st r_fl].
  split; reflexivity.
Qed.

Lemma rf_msz_facts : forall r c, 1 <= c <= 31 -> reg_wf c r -> rf_nf r < MaxCount c / 2 ->
  0 < rf_msz r c /\ rf_msz r c mod 0x40000 = 0
  /\ rf_au r c + rf_k r c * ClassSize c <= r_muser r + rf_msz r c < rf_au r c + rf_k r c * ClassSize c + 0x40000.
Proof.
  intros r c Hc HW H. pose proof (ClassSize_range c Hc) as (HS & _). destruct HW as (_ & _ & W3 & W4 & _).
  assert (Hlt : r_muser r < rf_au r c + rf_k r c * ClassSize c).
  { unfold rf_au, rf_k. assert (1 <= MaxCount c / 2 - rf_nf r) by lia. clear - W4 H0 HS. nia. }
  unfold rf_msz, umap_size. pose proof (round_fa_ge (rf_au r c + rf_k r c * ClassSize c - r_muser r) ltac:(lia)) as R1.
  pose proof (round_fa_aligned (rf_au r c + rf_k r c * ClassSize c - r_muser r)) as R2. lia.
Qed.

Lemma rf_newc_facts : forall r c, 1 <= c <= 31 -> reg_wf c r -> rf_nf r < MaxCount c / 2 ->
  rf_k r c <= rf_newc r c /\ rf_newc r c * ClassSize c <= r_muser r + rf_msz r c - rf_au r c < rf_newc r c * ClassSize c + ClassSize c
  /\ rf_newc r c * ClassSize c < rf_k r c * ClassSize c + 0x40000.
Proof.
  intros r c Hc HW H. pose proof (ClassSize_range c Hc) as (HS & _). pose proof (rf_msz_facts r c Hc HW H) as (M1 & M2 & M3 & M4).
  destruct HW as (_ & _ & W3 & W4 & _).
  unfold rf_newc, pfa_newc. pose proof (Z.div_mod (r_muser r + rf_msz r c - rf_au r c) (ClassSize c) ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (r_muser r + rf_msz r c - rf_au r c) (ClassSize c) ltac:(lia)) as B.
  set (q := (r_muser r + rf_msz r c - rf_au r c) / ClassSize c) in *.
  assert (Hk : rf_k r c <= q).
  { unfold q. apply Z.div_le_lower_bound; [lia|]. unfold rf_au in *. lia. }
  split; [exact Hk|]. split; [nia|]. unfold rf_au in *. nia.
Qed.

Lemma rf_mfa_facts : forall r c, reg_wf c r ->
  r_mfa r <= rf_mfa r c /\ rf_mfa r c mod 0x40000 = 0 /\ 4 * (rf_nf r + rf_newc r c) <= rf_mfa r c
  /\ rf_mfa r c <= Z.max (r_mfa r) (4 * (rf_nf r + rf_newc r c) + 0x40000)
  /\ (r_mfa r < rf_mfa r c <-> r_mfa r < 4 * (rf_nf r + rf_newc r c)).
Proof.
  intros r c HW. destruct HW as (_ & _ & _ & _ & W5 & W6 & W7 & _). unfold kUMap in *. unfold rf_mfa.
  destruct (Z.ltb_spec (r_mfa r) (4 * (rf_nf r + rf_newc r c))) as [X|X].
  - pose proof (round_fa_ge (4 * (rf_nf r + rf_newc r c)) ltac:(lia)) as R1. pose proof (round_fa_aligned (4 * (rf_nf r + rf_newc r c))) as R2.
    repeat split; lia.
  - repeat split; lia.
Qed.

Lemma rf_fl_len : forall r c, 0 <= rf_newc r c -> Z.of_nat (length (rf_fl r c)) = rf_nf r + rf_newc r c.
Proof.
  intros r c H. unfold rf_fl, rf_nf. rewrite length_app, length_rev, length_map, length_seq. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cpw_eq : forall c i, cpw c i = Z_to_bv 64 ((i * ClassSize c) / 16).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma carve_prefix : forall (fl : list Z) (ws : list word) (st_len newc : nat) (c : Z),
  firstn (length fl) ws = map (cpw c) fl -> (length fl + newc <= length ws)%nat ->
  firstn (length fl + newc) (carve ws (Z.of_nat (length fl + newc)) (ClassSize c * Z.of_nat st_len) (ClassSize c) newc)
  = map (cpw c) (fl ++ rev (map (fun j => Z.of_nat st_len + Z.of_nat j) (seq 0 newc))).
Proof.
  intros fl ws st_len newc c HP HL. apply nth_error_ext. intros p.
  rewrite nth_error_firstn, nth_error_map.
  destruct (Nat.ltb_spec p (length fl + newc)) as [Hp|Hp].
  - destruct (Nat.lt_ge_cases p (length fl)) as [H1|H1].
    + rewrite carve_nth_other by lia. rewrite nth_error_app1 by exact H1.
      assert (E : nth_error (firstn (length fl) ws) p = nth_error (map (cpw c) fl) p) by (rewrite HP; reflexivity).
      rewrite nth_error_firstn, nth_error_map in E. rewrite (proj2 (Nat.ltb_lt _ _) H1) in E. exact E.
    + set (j := (length fl + newc - 1 - p)%nat).
      replace p with (Z.to_nat (Z.of_nat (length fl + newc) - 1 - Z.of_nat j)) at 1 by (unfold j; lia).
      rewrite carve_nth_new by (unfold j; lia).
      rewrite nth_error_app2 by exact H1. rewrite nth_error_rev, length_map, length_seq.
      rewrite (proj2 (Nat.ltb_lt (p - length fl) newc) ltac:(lia)). rewrite nth_error_map, nth_error_seq.
      rewrite (proj2 (Nat.ltb_lt (newc - S (p - length fl)) newc) ltac:(lia)). cbn [option_map]. f_equal. rewrite cpw_eq. f_equal. f_equal.
      unfold j. replace (newc - S (p - length fl))%nat with (length fl + newc - 1 - p)%nat by lia. nia.
  - rewrite (proj2 (nth_error_None _ _)); [reflexivity|]. rewrite length_app, length_rev, length_map, length_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma dest_prefix : forall (fl : list Z) (ws chs : list word) (c : Z) (base n : nat),
  firstn (length fl) ws = map (cpw c) fl -> (base + n = length fl)%nat -> (n <= length chs)%nat ->
  (forall i, In i fl -> 0 <= i * ClassSize c / 16 < 2 ^ 31) ->
  firstn n (dest ws chs (Z.of_nat base) n) = map (cpw c) (skipn base fl).
Proof.
  intros fl ws chs c base n HP HL HC Hsm. apply nth_error_ext. intros p.
  rewrite nth_error_firstn, nth_error_map, nth_error_skipn.
  destruct (Nat.ltb_spec p n) as [Hp|Hp].
  - rewrite (dest_nth_copied ws chs (Z.of_nat base) n p Hp HC). rewrite Nat2Z.id.
    assert (E : nth_error (firstn (length fl) ws) (base + p) = nth_error (map (cpw c) fl) (base + p)) by (rewrite HP; reflexivity).
    rewrite nth_error_firstn, nth_error_map in E. rewrite (proj2 (Nat.ltb_lt (base + p) (length fl)) ltac:(lia)) in E.
    destruct (nth_error fl (base + p)) as [i|] eqn:Ei; [|apply nth_error_None in Ei; lia].
    rewrite (nth_error_nth' ws (Z_to_bv 64 0) ltac:(apply nth_error_Some; rewrite E; discriminate)) in E.
    injection E as E. rewrite E. cbn [option_map]. f_equal. rewrite cpw_eq. apply sx32_zw. exact (Hsm i (nth_error_In _ _ Ei)).
  - rewrite (proj2 (nth_error_None _ _)); [reflexivity|]. lia.
Qed.

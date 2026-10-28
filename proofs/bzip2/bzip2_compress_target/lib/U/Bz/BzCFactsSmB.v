(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzArrD BzCMem BzCStream BzCState BzCHuff BzCMtf BzCRebuildF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutSM CmpCutSmA BzCFactsSmA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsGm BzCSmF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_iters_S : forall n arr1 nG A nMTF s, sm_iters (S n) arr1 nG A nMTF s = sm_iters n arr1 nG A nMTF (sm_iter arr1 nG A nMTF s).
Proof. reflexivity. Qed.
Lemma sm_iters_iter : forall n arr1 nG A nMTF s, sm_iters n arr1 nG A nMTF s = Nat.iter n (sm_iter arr1 nG A nMTF) s.
Proof.
  induction n as [|n IH]; intros; [reflexivity|]. rewrite sm_iters_S, IH.
  rewrite <- Nat.iter_succ_r. reflexivity.
Qed.
Lemma sm_groups_S : forall f arr1 len lp nG nMTF s,
  sm_groups (S f) arr1 len lp nG nMTF s = (if nMTF <=? g_gs s then s else sm_groups f arr1 len lp nG nMTF (sm_group_iter arr1 len lp nG nMTF s)).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sm_rfreq_zero_S : forall n rf A t, sm_rfreq_zero (S n) rf A t = sm_rfreq_zero n (zfill0 (Z.to_nat A) rf (258 * t)) A (t + 1).
Proof. reflexivity. Qed.
Lemma sm_lenpack_S : forall n lp len v,
  sm_lenpack (S n) lp len v =
  sm_lenpack n (zset (zset (zset lp (4 * v) (Z.lor (Z.shiftl (zget len (258 * 1 + v)) 16) (zget len (258 * 0 + v))))
                              (4 * v + 1) (Z.lor (Z.shiftl (zget len (258 * 3 + v)) 16) (zget len (258 * 2 + v))))
                        (4 * v + 2) (Z.lor (Z.shiftl (zget len (258 * 5 + v)) 16) (zget len (258 * 4 + v)))) len (v + 1).
Proof. reflexivity. Qed.
Lemma sm_cost_fast_S : forall n arr1 lp i c01 c23 c45,
  sm_cost_fast (S n) arr1 lp i c01 c23 c45 =
  sm_cost_fast n arr1 lp (i + 1) ((c01 + zget lp (4 * mtfv_at arr1 i)) mod 4294967296) ((c23 + zget lp (4 * mtfv_at arr1 i + 1)) mod 4294967296) ((c45 + zget lp (4 * mtfv_at arr1 i + 2)) mod 4294967296).
Proof. reflexivity. Qed.
Lemma sm_cost_slow_S : forall n cost len arr1 nG i,
  sm_cost_slow (S n) cost len arr1 nG i = sm_cost_slow n (sm_cost_slow_t (Z.to_nat nG) cost len (mtfv_at arr1 i) 0) len arr1 nG (i + 1).
Proof. reflexivity. Qed.
Lemma sm_cost_slow_t_S : forall n cost len icv t,
  sm_cost_slow_t (S n) cost len icv t = sm_cost_slow_t n (zset cost t ((zget cost t + zget len (258 * t + icv)) mod 65536)) len icv (t + 1).
Proof. reflexivity. Qed.
Lemma sm_best_S : forall n cost t bc bt,
  sm_best (S n) cost t bc bt = (if zget cost t <? bc then sm_best n cost (t + 1) (zget cost t) t else sm_best n cost (t + 1) bc bt).
Proof. reflexivity. Qed.
Lemma sm_rfreq_inc_S : forall n rf arr1 bt i, sm_rfreq_inc (S n) rf arr1 bt i = sm_rfreq_inc n (zincr rf (258 * bt + mtfv_at arr1 i)) arr1 bt (i + 1).
Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition QV (arr1 : zarr) (gs k : Z) : Z := mtfv_at arr1 (gs + k).
Definition PV (arr1 lp : zarr) (gs k j : Z) : Z := zget lp (4 * QV arr1 gs k + j).
(* [comment removed for export] *)
Fixpoint psum (arr1 lp : zarr) (gs : Z) (j : Z) (k0 : nat) (n : nat) : Z :=
  match n with O => 0 | S n' => PV arr1 lp gs (Z.of_nat k0) j + psum arr1 lp gs j (S k0) n' end.
Lemma psum_nonneg : forall arr1 lp gs j n k0, (forall k, Z.of_nat k0 <= k < Z.of_nat k0 + Z.of_nat n -> 0 <= PV arr1 lp gs k j) -> 0 <= psum arr1 lp gs j k0 n.
Proof.
  intros arr1 lp gs j. induction n as [|n IH]; intros k0 H; cbn [psum]; [lia|].
  pose proof (H (Z.of_nat k0) ltac:(lia)). pose proof (IH (S k0) ltac:(intros; apply H; lia)). lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sm_cost_fast_psum : forall n arr1 lp gs k0 c01 c23 c45,
  0 <= c01 < 4294967296 -> 0 <= c23 < 4294967296 -> 0 <= c45 < 4294967296 ->
  sm_cost_fast n arr1 lp (gs + Z.of_nat k0) c01 c23 c45 =
  ((c01 + psum arr1 lp gs 0 k0 n) mod 4294967296, (c23 + psum arr1 lp gs 1 k0 n) mod 4294967296, (c45 + psum arr1 lp gs 2 k0 n) mod 4294967296).
Proof.
  induction n as [|n IH]; intros arr1 lp gs k0 c01 c23 c45 H1 H2 H3.
  - cbn [sm_cost_fast psum]. rewrite !Z.add_0_r, !Z.mod_small by lia. reflexivity.
  - rewrite sm_cost_fast_S. cbn [psum]. unfold PV, QV. rewrite (Z.add_0_r (4 * mtfv_at arr1 (gs + Z.of_nat k0))).
    replace (gs + Z.of_nat k0 + 1) with (gs + Z.of_nat (S k0)) by lia.
    rewrite IH by (apply Z.mod_pos_bound; lia).
    f_equal; [f_equal|].
    + rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
    + rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
    + rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.
(* [comment removed for export] *)
Lemma sm_cost_fast_50 : forall arr1 lp gs,
  sm_cost_fast 50 arr1 lp gs 0 0 0 = (psum arr1 lp gs 0 0 50 mod 4294967296, psum arr1 lp gs 1 0 50 mod 4294967296, psum arr1 lp gs 2 0 50 mod 4294967296).
Proof. intros. rewrite <- (Z.add_0_r gs) at 1. change 0 with (Z.of_nat 0) at 1. rewrite sm_cost_fast_psum by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma psum50_eq : forall arr1 lp gs j, psum arr1 lp gs j 0 50 = PV arr1 lp gs 0 j + PV arr1 lp gs 1 j + PV arr1 lp gs 2 j + PV arr1 lp gs 3 j + PV arr1 lp gs 4 j + PV arr1 lp gs 5 j + PV arr1 lp gs 6 j + PV arr1 lp gs 7 j + PV arr1 lp gs 8 j + PV arr1 lp gs 9 j + PV arr1 lp gs 10 j + PV arr1 lp gs 11 j + PV arr1 lp gs 12 j + PV arr1 lp gs 13 j + PV arr1 lp gs 14 j + PV arr1 lp gs 15 j + PV arr1 lp gs 16 j + PV arr1 lp gs 17 j + PV arr1 lp gs 18 j + PV arr1 lp gs 19 j + PV arr1 lp gs 20 j + PV arr1 lp gs 21 j + PV arr1 lp gs 22 j + PV arr1 lp gs 23 j + PV arr1 lp gs 24 j + PV arr1 lp gs 25 j + PV arr1 lp gs 26 j + PV arr1 lp gs 27 j + PV arr1 lp gs 28 j + PV arr1 lp gs 29 j + PV arr1 lp gs 30 j + PV arr1 lp gs 31 j + PV arr1 lp gs 32 j + PV arr1 lp gs 33 j + PV arr1 lp gs 34 j + PV arr1 lp gs 35 j + PV arr1 lp gs 36 j + PV arr1 lp gs 37 j + PV arr1 lp gs 38 j + PV arr1 lp gs 39 j + PV arr1 lp gs 40 j + PV arr1 lp gs 41 j + PV arr1 lp gs 42 j + PV arr1 lp gs 43 j + PV arr1 lp gs 44 j + PV arr1 lp gs 45 j + PV arr1 lp gs 46 j + PV arr1 lp gs 47 j + PV arr1 lp gs 48 j + PV arr1 lp gs 49 j.
Proof. intros. cbn [psum]. rewrite <- !Z.add_assoc, Z.add_0_r. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fast_half_lo : forall s, 0 <= s -> Z.land (s mod 4294967296) 65535 = s mod 65536.
Proof.
  intros s Hs. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
  change 4294967296 with (65536 * 65536). rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm 65536), Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma fast_half_hi : forall s, 0 <= s -> Z.shiftr (s mod 4294967296) 16 = (s / 65536) mod 65536.
Proof.
  intros s Hs. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. change 4294967296 with (65536 * 65536).
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm 65536), Z.div_add by lia. rewrite (Z.div_small (s mod 65536) 65536) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_best_fst : forall n cost t bc bt,
  fst (sm_best n cost t bc bt) = bc \/ exists t', t <= t' < t + Z.of_nat n /\ fst (sm_best n cost t bc bt) = zget cost t'.
Proof.
  induction n as [|n IH]; intros cost t bc bt; [left; reflexivity|].
  rewrite sm_best_S. destruct (zget cost t <? bc).
  - destruct (IH cost (t + 1) (zget cost t) t) as [E|(t' & Ht' & E)].
    + right. exists t. split; [lia| exact E].
    + right. exists t'. split; [lia| exact E].
  - destruct (IH cost (t + 1) bc bt) as [E|(t' & Ht' & E)].
    + left. exact E.
    + right. exists t'. split; [lia| exact E].
Qed.
Lemma sm_best_fst_hit : forall n cost t bc bt, (1 <= n)%nat -> zget cost t < bc ->
  exists t', t <= t' < t + Z.of_nat n /\ fst (sm_best n cost t bc bt) = zget cost t'.
Proof.
  intros [|n] cost t bc bt Hn Hlt; [lia|]. rewrite sm_best_S.
  replace (zget cost t <? bc) with true by (symmetry; apply Z.ltb_lt; exact Hlt).
  destruct (sm_best_fst n cost (t + 1) (zget cost t) t) as [E|(t' & Ht' & E)].
  - exists t. split; [lia| exact E].
  - exists t'. split; [lia| exact E].
Qed.
Lemma sm_best_fst_bound : forall n cost t bc bt B, (1 <= n)%nat -> zget cost t < bc ->
  (forall t', t <= t' < t + Z.of_nat n -> 0 <= zget cost t' <= B) -> 0 <= fst (sm_best n cost t bc bt) <= B.
Proof.
  intros n cost t bc bt B Hn Hlt HB. cps_destruct (sm_best_fst_hit n cost t bc bt Hn Hlt) as (t' & Ht' & E). rewrite E. apply HB. exact Ht'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fastb (nG nMTF gs : Z) : bool := (nG =? 6) && (GE nMTF gs - gs =? 49).
Lemma COSTC_fast : forall arr1 len lp nG nMTF gs c, fastb nG nMTF gs = true ->
  COSTC arr1 len lp nG gs (GE nMTF gs) c =
  zset (zset (zset (zset (zset (zset (zero6 c) 0 (Z.land (psum arr1 lp gs 0 0 50 mod 4294967296) 65535)) 1 (Z.shiftr (psum arr1 lp gs 0 0 50 mod 4294967296) 16))
       2 (Z.land (psum arr1 lp gs 1 0 50 mod 4294967296) 65535)) 3 (Z.shiftr (psum arr1 lp gs 1 0 50 mod 4294967296) 16))
       4 (Z.land (psum arr1 lp gs 2 0 50 mod 4294967296) 65535)) 5 (Z.shiftr (psum arr1 lp gs 2 0 50 mod 4294967296) 16).
Proof.
  intros arr1 len lp nG nMTF gs c H. unfold fastb in H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  unfold COSTC. rewrite H1. replace (GE nMTF gs - gs + 1 =? 50) with true by (symmetry; apply Z.eqb_eq; apply Z.eqb_eq in H2; lia).
  cbn [andb]. rewrite sm_cost_fast_50. reflexivity.
Qed.
Lemma COSTC_slow : forall arr1 len lp nG nMTF gs c, fastb nG nMTF gs = false ->
  COSTC arr1 len lp nG gs (GE nMTF gs) c = sm_cost_slow (Z.to_nat (GE nMTF gs - gs + 1)) (zero6 c) len arr1 nG gs.
Proof.
  intros arr1 len lp nG nMTF gs c H. unfold fastb in H. unfold COSTC.
  replace ((nG =? 6) && (GE nMTF gs - gs + 1 =? 50))%bool with false; [reflexivity|].
  symmetry. apply Bool.andb_false_iff. apply Bool.andb_false_iff in H. destruct H as [H|H]; [left; exact H| right].
  apply Z.eqb_neq. apply Z.eqb_neq in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_rfreq_inc_S_last : forall n rf arr1 bt i,
  sm_rfreq_inc (S n) rf arr1 bt i = zincr (sm_rfreq_inc n rf arr1 bt i) (258 * bt + mtfv_at arr1 (i + Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros rf arr1 bt i.
  - cbn [sm_rfreq_inc]. rewrite Z.add_0_r. reflexivity.
  - rewrite sm_rfreq_inc_S. rewrite IH. rewrite sm_rfreq_inc_S. do 3 f_equal. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_rfreq_inc_QV : forall k rf arr1 bt gs,
  sm_rfreq_inc (S k) rf arr1 bt gs = zincr (sm_rfreq_inc k rf arr1 bt gs) (258 * bt + QV arr1 gs (Z.of_nat k)).
Proof. intros. rewrite sm_rfreq_inc_S_last. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sm_rfreq_inc_QVz : forall k (kz : Z) rf arr1 bt gs, kz = Z.of_nat k ->
  sm_rfreq_inc (S k) rf arr1 bt gs = zincr (sm_rfreq_inc k rf arr1 bt gs) (258 * bt + QV arr1 gs kz).
Proof. intros k kz rf arr1 bt gs ->. apply sm_rfreq_inc_QV. Qed.
(* [comment removed for export] *)
Definition RFrow (rf : zarr) (bt A B : Z) : Prop :=
  forall v, 0 <= v < A -> zdef rf (258 * bt + v) = true /\ 0 <= zget rf (258 * bt + v) <= B.
Lemma RFrow_incr : forall rf bt A B v0, RFrow rf bt A B -> 0 <= v0 < A -> RFrow (zincr rf (258 * bt + v0)) bt A (B + 1).
Proof.
  intros rf bt A B v0 H Hv0 v Hv. unfold zincr. destruct (H v Hv) as [D R]. destruct (H v0 Hv0) as [_ R0].
  destruct (Z.eq_dec v v0) as [->|NE].
  - rewrite zdef_zset_same, zget_zset_same. split; [reflexivity| lia].
  - rewrite zdef_zset_other, zget_zset_other by lia. split; [exact D| lia].
Qed.
Lemma RFrow_weaken : forall rf bt A B B', RFrow rf bt A B -> B <= B' -> RFrow rf bt A B'.
Proof. intros rf bt A B B' H HB v Hv. destruct (H v Hv) as [D R]. split; [exact D| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section M.
  Variables (e : est) (cost0 fave0 heap0 weight0 parent0 : zarr).
  Let arr1 := e_arr1 e. Let A := sm_alpha e. Let nG := smA_ng e. Let nMTF := sm_nmtf e.

  Definition IT0 : sits := SITS (ip_len (smA_ip e)) (e_rfreq e) (e_len_pack e) (e_selector e) cost0 fave0 0 heap0 weight0 parent0.
  Definition ITk (k : nat) : sits := Nat.iter k (sm_iter arr1 nG A nMTF) IT0.
  Lemma ITk_S : forall k, ITk (S k) = sm_iter arr1 nG A nMTF (ITk k).
  Proof. reflexivity. Qed.
  Lemma smB_it_eq : smB_it e cost0 fave0 heap0 weight0 parent0 = ITk 4.
  Proof. unfold smB_it, ITk, IT0, BZ_N_ITERS. rewrite sm_iters_iter. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition it_rf0 (s : sits) : zarr := sm_rfreq_zero (Z.to_nat nG) (it_rfreq s) A 0.
  Definition it_lpk (s : sits) : zarr := if nG =? 6 then sm_lenpack (Z.to_nat A) (it_lp s) (it_len s) 0 else it_lp s.
  Definition G0 (s : sits) : sgs := SGS (it_rf0 s) (it_sel s) (it_cost s) (zero6 (it_fave s)) 0 0 0.
  Definition Gj (s : sits) (j : nat) : sgs := Nat.iter j (sm_group_iter arr1 (it_len s) (it_lpk s) nG nMTF) (G0 s).
  Lemma Gj_S : forall s j, Gj s (S j) = sm_group_iter arr1 (it_len s) (it_lpk s) nG nMTF (Gj s j).
  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition KSEL : Z := (nMTF + 49) / 50.
  Definition Gend (s : sits) : sgs := Gj s (Z.to_nat KSEL).
  (* [comment removed for export] *)
  Definition ml_step (rf : zarr) (t : nat) (x : zarr * zarr * zarr * zarr) : zarr * zarr * zarr * zarr :=
    let '(l, h, w, p) := x in
    let r := hbMakeCodeLengths l rf h w p (258 * Z.of_nat t) (258 * Z.of_nat t) A 17 in
    (hs_len r, hs_heap r, hs_weight r, hs_parent r).
  Fixpoint MLt (s : sits) (t : nat) : zarr * zarr * zarr * zarr :=
    match t with O => (it_len s, it_heap s, it_weight s, it_parent s) | S t' => ml_step (g_rfreq (Gend s)) t' (MLt s t') end.
  Definition ml_len (s : sits) (t : nat) : zarr := fst (fst (fst (MLt s t))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition smB_static : Prop :=
    3 <= A <= 258 /\ 2 <= nG <= 6 /\ 1 <= nMTF <= NBLOCKMAX + 20 /\ 1 <= e_nInUse e <= 256 /\
    zbok arr1 /\ (forall i, 0 <= i < nMTF -> 0 <= mtfv_at arr1 i < A) /\
    1 <= KSEL <= 18002 /\ 50 * (KSEL - 1) < nMTF <= 50 * KSEL /\ (nG = 6 <-> 2400 <= nMTF).

  (* [comment removed for export] *)
  Definition smB_len (s : sits) : Prop :=
    forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef (it_len s) (258 * t + v) = true /\ 0 <= zget (it_len s) (258 * t + v) <= 17.
  (* [comment removed for export] *)
  Definition smB_lp (s : sits) : Prop :=
    nG = 6 -> forall v j, 0 <= v < A -> 0 <= j < 3 ->
      zdef (it_lpk s) (4 * v + j) = true /\
      zget (it_lpk s) (4 * v + j) = Z.lor (Z.shiftl (zget (it_len s) (258 * (2 * j + 1) + v)) 16) (zget (it_len s) (258 * (2 * j) + v)) /\
      0 <= zget (it_lpk s) (4 * v + j) < 2097152.
  (* [comment removed for export] *)
  Definition smB_grp (s : sits) : Prop :=
    (forall j, (Z.of_nat j <= KSEL) -> let g := Gj s j in
       g_gs g = Z.min (50 * Z.of_nat j) nMTF /\ g_nSel g = Z.of_nat j /\ 0 <= g_totc g <= 65535 * Z.of_nat j /\
       (forall t v, 0 <= t < nG -> 0 <= v < A -> zdef (g_rfreq g) (258 * t + v) = true /\ 0 <= zget (g_rfreq g) (258 * t + v) <= g_gs g) /\
       (forall t, 0 <= t < 6 -> 0 <= zget (g_fave g) t <= Z.of_nat j) /\
       (forall i, 0 <= i < Z.of_nat j -> zdef (g_sel g) i = true /\ 0 <= zget (g_sel g) i < nG)) /\
    sm_groups (Z.to_nat (nMTF + 1)) arr1 (it_len s) (it_lpk s) nG nMTF (G0 s) = Gend s.
  (* [comment removed for export] *)
  Definition smB_ml (s : sits) : Prop :=
    (forall t, (Z.of_nat t < nG) ->
       hm_facts (ml_len s t) (g_rfreq (Gend s)) (258 * Z.of_nat t) (258 * Z.of_nat t) A /\
       ml_len s (S t) = hs_len (hbMakeCodeLengths (ml_len s t) (g_rfreq (Gend s)) znew znew znew (258 * Z.of_nat t) (258 * Z.of_nat t) A 17) /\
       (forall k, ~ (258 * Z.of_nat t <= k < 258 * Z.of_nat t + A) -> zget (ml_len s (S t)) k = zget (ml_len s t) k) /\
       (forall k, zdef (ml_len s t) k = true -> zdef (ml_len s (S t)) k = true)) /\
    sm_iter arr1 nG A nMTF s =
      (let '(l, h, w, p) := MLt s (Z.to_nat nG) in let g := Gend s in
       SITS l (g_rfreq g) (it_lpk s) (g_sel g) (g_cost g) (g_fave g) (g_nSel g) h w p).

  Definition smB_facts : Prop :=
    smB_static /\ forall k, (k < 4)%nat -> let s := ITk k in smB_len s /\ smB_lp s /\ smB_grp s /\ smB_ml s.
End M.

End ACeilS1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCPermM BzCLemmasMs.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCBlock BzCQsortM1 BzCQsortM2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCQsortM1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCFactsMs3.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1.BzCGtU OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.BzCBudget.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pr (nb : Z) (a : zarr) (lo hi : Z) : Prop := forall x, lo <= x <= hi -> 0 <= rd32 a x < nb.
Definition mqsF (a2 : zarr) (qoff nb : Z) (q : mqs) : Prop :=
  let sp := mq_sp q in let lo := zget (mq_slo q) (sp - 1) in let hi := zget (mq_shi q) (sp - 1) in let d := zget (mq_sd q) (sp - 1) in
  sp <= 51 /\ 0 <= lo /\ lo <= hi + 1 /\ hi < nb /\ 0 <= d <= 15 /\
  ((hi - lo < 20 \/ 14 < d) -> zbok (mq_a1 q) -> pr nb (mq_a1 q) 0 (nb - 1) -> 0 <= mq_budget q ->
     -2147483648 < snd (mainSimpleSort (mq_a1 q) a2 qoff nb lo hi d (mq_budget q))).

Theorem mqs_facts : forall (a2 : zarr) (qoff nb lo hi : Z) (a1 sl sh sd nl nh nd : zarr) (budget : Z),
  34 <= nb <= 899990 ->
  (forall z, nb <= z < nb + 34 -> rd8 a2 z = rd8 a2 (z - nb)) ->
  (forall z, nb <= z < nb + 34 -> qrd a2 qoff z = qrd a2 qoff (z - nb)) ->
  0 <= lo -> lo <= hi -> hi < nb ->
  let q0 := mpush (MQS a1 0 sl sh sd nl nh nd budget false) lo hi BZ_N_RADIX in
  (forall v, let q := mqs_loop v a2 qoff nb q0 in 0 < mq_sp q -> mq_exit q = false -> mqsF a2 qoff nb q) /\
  (let q := mqs_loop (mqs_fuel lo hi) a2 qoff nb q0 in mq_sp q <= 0 \/ mq_exit q = true).
Proof.
  intros a2 qoff nb lo hi a1 sl sh sd nl nh nd budget NB Bov Qov Hlo Hlh Hhi. cbv zeta.
  pose proof (mqs_ok lo hi BZ_N_RADIX a2 qoff nb ltac:(unfold BZ_N_RADIX; lia) Hlh ltac:(change (21 * 2 ^ 16) with 1376256; lia) a1 sl sh sd nl nh nd budget) as M.
  cbv zeta in M. destruct M as [MV MF]. split.
  - intros v SP EX. destruct (MV v) as [S51 TOP]. specialize (TOP SP).
    unfold ent in TOP.
    cps_destruct TOP as (L1 & L2 & L3 & L4).
    unfold mqsF. cbv zeta. assert (R2 : BZ_N_RADIX = 2) by reflexivity.
    split; [exact S51|]. split. { clear - L1 Hlo. lia. } split. { clear - L2. lia. } split. { clear - L3 Hhi. lia. } split. { clear - L4 R2. lia. }
    intros LEAF ZB PR BU.
    set (q := mqs_loop v a2 qoff nb _) in *.
    destruct (Z.le_gt_cases (zget (mq_slo q) (mq_sp q - 1)) (zget (mq_shi q) (mq_sp q - 1))) as [LE|GT].
    + apply (mainSimpleSort_budget_int32 a2 qoff nb (zget (mq_sd q) (mq_sp q - 1)) ltac:(lia) ltac:(clear - L4 R2; lia) Bov Qov).
      * lia.
      * intros o. apply ZB.
      * intros p Hp. unfold X. apply PR. lia.
      * exact BU.
    + (* [comment removed for export] *)
      unfold mainSimpleSort. destruct (Z.ltb_spec (zget (mq_shi q) (mq_sp q - 1) - zget (mq_slo q) (mq_sp q - 1) + 1) 2); [cbn [snd]; lia| lia].
  - destruct MF as [MF|MF]; [left; lia| right; exact MF].
Qed.
End BzCFactsMs3.

Export OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2.BzCFactsMs3.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mss_shift_S : forall f a1 a2 qoff nb d h lo j v b,
  mss_shift (S f) a1 a2 qoff nb d h lo j v b =
  let '(gt, b1) := mainGtU (rd32 a1 (j - h) + d) (v + d) a2 qoff nb b in
  if gt then
    let a1' := wr32 a1 j (rd32 a1 (j - h)) in let j' := j - h in
    if j' <=? lo + h - 1 then (a1', j', b1) else mss_shift f a1' a2 qoff nb d h lo j' v b1
  else (a1, j, b1).
Proof. reflexivity. Qed.
(* [comment removed for export] *)

Lemma mss_shift_budget_le : forall f a1 a2 qoff nb d h lo j v b, snd (mss_shift f a1 a2 qoff nb d h lo j v b) <= b.
Proof.
  induction f as [|f IH]; intros; [cbn; lia|].
  rewrite mss_shift_S. pose proof (mainGtU_budget_le (rd32 a1 (j - h) + d) (v + d) a2 qoff nb b) as G.
  destruct (mainGtU _ _ _ _ _ _) as [gt b1]. cbn [snd] in G. destruct gt; [| cbn; lia].
  cbv zeta. destruct (j - h <=? lo + h - 1); [cbn; lia|]. eapply Z.le_trans; [apply IH| lia].
Qed.
(* [comment removed for export] *)
Lemma mss_shift_budget_le_gtu : forall f a1 a2 qoff nb d h lo j v b,
  snd (mss_shift (S f) a1 a2 qoff nb d h lo j v b) <= snd (mainGtU (rd32 a1 (j - h) + d) (v + d) a2 qoff nb b).
Proof.
  intros. rewrite mss_shift_S. destruct (mainGtU _ _ _ _ _ _) as [gt b1]. cbn [snd]. destruct gt; [| cbn; lia].
  cbv zeta. destruct (j - h <=? lo + h - 1); [cbn; lia|]. apply mss_shift_budget_le.
Qed.
(* [comment removed for export] *)

Lemma mss_ins_eq : forall a1 a2 qoff nb d h lo i b,
  mss_ins a1 a2 qoff nb d h lo i b =
  let v := rd32 a1 i in let '(a1', j, b') := mss_shift (S (Z.to_nat (i - lo))) a1 a2 qoff nb d h lo i v b in (wr32 a1' j v, b').
Proof. reflexivity. Qed.
Lemma mss_ins_budget_le : forall a1 a2 qoff nb d h lo i b, snd (mss_ins a1 a2 qoff nb d h lo i b) <= b.
Proof.
  intros. rewrite mss_ins_eq. cbv zeta. pose proof (mss_shift_budget_le (S (Z.to_nat (i - lo))) a1 a2 qoff nb d h lo i (rd32 a1 i) b) as L.
  destruct (mss_shift _ _ _ _ _ _ _ _ _ _ _) as [[a1' j] b']. cbn [snd] in *. exact L.
Qed.
(* [comment removed for export] *)

Lemma mss_hloop_S : forall f a1 a2 qoff nb d h lo hi i b,
  mss_hloop (S f) a1 a2 qoff nb d h lo hi i b =
  if hi <? i then (a1, b, false) else
  let '(a1, b) := mss_ins a1 a2 qoff nb d h lo i b in let i := i + 1 in
  if hi <? i then (a1, b, false) else
  let '(a1, b) := mss_ins a1 a2 qoff nb d h lo i b in let i := i + 1 in
  if hi <? i then (a1, b, false) else
  let '(a1, b) := mss_ins a1 a2 qoff nb d h lo i b in let i := i + 1 in
  if b <? 0 then (a1, b, true) else mss_hloop f a1 a2 qoff nb d h lo hi i b.
Proof. reflexivity. Qed.
Lemma mss_hloop_budget_le : forall f a1 a2 qoff nb d h lo hi i b, snd (fst (mss_hloop f a1 a2 qoff nb d h lo hi i b)) <= b.
Proof.
  induction f as [|f IH]; intros; [cbn; lia|]. rewrite mss_hloop_S.
  destruct (hi <? i); [cbn; lia|].
  pose proof (mss_ins_budget_le a1 a2 qoff nb d h lo i b) as L1. destruct (mss_ins a1 a2 qoff nb d h lo i b) as [a1a ba]. cbn [snd] in L1. cbv zeta.
  destruct (hi <? i + 1); [cbn; lia|].
  pose proof (mss_ins_budget_le a1a a2 qoff nb d h lo (i + 1) ba) as L2. destruct (mss_ins a1a a2 qoff nb d h lo (i + 1) ba) as [a1b bb]. cbn [snd] in L2.
  destruct (hi <? i + 1 + 1); [cbn; lia|].
  pose proof (mss_ins_budget_le a1b a2 qoff nb d h lo (i + 1 + 1) bb) as L3. destruct (mss_ins a1b a2 qoff nb d h lo (i + 1 + 1) bb) as [a1c bc]. cbn [snd] in L3.
  destruct (bc <? 0); [cbn; lia|]. eapply Z.le_trans; [apply IH| lia].
Qed.
(* [comment removed for export] *)

Lemma mss_hps_S : forall r a1 a2 qoff nb d lo hi hp b,
  mss_hps (S r) a1 a2 qoff nb d lo hi hp b =
  let h := incs_at hp in
  let '(a1, b, ex) := mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff nb d h lo hi (lo + h) b in
  if ex then (a1, b, true) else mss_hps r a1 a2 qoff nb d lo hi (hp - 1) b.
Proof. reflexivity. Qed.
Lemma mss_hps_budget_le : forall r a1 a2 qoff nb d lo hi hp b, snd (fst (mss_hps r a1 a2 qoff nb d lo hi hp b)) <= b.
Proof.
  induction r as [|r IH]; intros; [cbn; lia|]. rewrite mss_hps_S. cbv zeta.
  pose proof (mss_hloop_budget_le (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff nb d (incs_at hp) lo hi (lo + incs_at hp) b) as L.
  destruct (mss_hloop _ _ _ _ _ _ _ _ _ _ _) as [[a1' b'] ex]. cbn [fst snd] in L. destruct ex; [cbn; lia|].
  eapply Z.le_trans; [apply IH| exact L].
Qed.
Lemma incs_at_pos : forall hp, 0 <= hp <= 13 -> 1 <= incs_at hp <= 2391484.
Proof.
  intros hp Hhp. unfold incs_at, incs.
  assert (E : exists k, (k <= 13)%nat /\ Z.to_nat hp = k) by (exists (Z.to_nat hp); split; [lia| reflexivity]).
  cps_destruct E as (k & Hk & ->). do 14 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.
(* [comment removed for export] *)
Lemma mainSimpleSort_eq : forall a1 a2 qoff nb lo hi d b,
  mainSimpleSort a1 a2 qoff nb lo hi d b =
  let bigN := hi - lo + 1 in
  if bigN <? 2 then (a1, b) else
  let hp := mss_hp 15%nat bigN 0 - 1 in
  let '(a1, b, _) := mss_hps (Z.to_nat (hp + 1)) a1 a2 qoff nb d lo hi hp b in (a1, b).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mss_hloop_le_ins1 : forall f a1 a2 qoff nb d h lo hi i b, hi <? i = false ->
  snd (fst (mss_hloop (S f) a1 a2 qoff nb d h lo hi i b)) <= snd (mss_ins a1 a2 qoff nb d h lo i b).
Proof.
  intros. rewrite mss_hloop_S, H.
  pose proof (mss_ins_budget_le a1 a2 qoff nb d h lo i b). destruct (mss_ins a1 a2 qoff nb d h lo i b) as [a1a ba]. cbn [snd] in *. cbv zeta.
  destruct (hi <? i + 1); [cbn; lia|].
  pose proof (mss_ins_budget_le a1a a2 qoff nb d h lo (i + 1) ba). destruct (mss_ins a1a a2 qoff nb d h lo (i + 1) ba) as [a1b bb]. cbn [snd] in *.
  destruct (hi <? i + 1 + 1); [cbn; lia|].
  pose proof (mss_ins_budget_le a1b a2 qoff nb d h lo (i + 1 + 1) bb). destruct (mss_ins a1b a2 qoff nb d h lo (i + 1 + 1) bb) as [a1c bc]. cbn [snd] in *.
  destruct (bc <? 0); [cbn; lia|]. pose proof (mss_hloop_budget_le f a1c a2 qoff nb d h lo hi (i + 1 + 1 + 1) bc). lia.
Qed.
Lemma mss_hloop_le_ins2 : forall f a1 a2 qoff nb d h lo hi i b a1a ba, hi <? i = false ->
  mss_ins a1 a2 qoff nb d h lo i b = (a1a, ba) -> hi <? i + 1 = false ->
  snd (fst (mss_hloop (S f) a1 a2 qoff nb d h lo hi i b)) <= snd (mss_ins a1a a2 qoff nb d h lo (i + 1) ba).
Proof.
  intros until ba. intros H E H1. rewrite mss_hloop_S, H, E. cbv zeta. rewrite H1.
  pose proof (mss_ins_budget_le a1a a2 qoff nb d h lo (i + 1) ba). destruct (mss_ins a1a a2 qoff nb d h lo (i + 1) ba) as [a1b bb]. cbn [snd] in *.
  destruct (hi <? i + 1 + 1); [cbn; lia|].
  pose proof (mss_ins_budget_le a1b a2 qoff nb d h lo (i + 1 + 1) bb). destruct (mss_ins a1b a2 qoff nb d h lo (i + 1 + 1) bb) as [a1c bc]. cbn [snd] in *.
  destruct (bc <? 0); [cbn; lia|]. pose proof (mss_hloop_budget_le f a1c a2 qoff nb d h lo hi (i + 1 + 1 + 1) bc). lia.
Qed.
Lemma mss_hloop_le_ins3 : forall f a1 a2 qoff nb d h lo hi i b a1a ba a1b bb, hi <? i = false ->
  mss_ins a1 a2 qoff nb d h lo i b = (a1a, ba) -> hi <? i + 1 = false ->
  mss_ins a1a a2 qoff nb d h lo (i + 1) ba = (a1b, bb) -> hi <? i + 1 + 1 = false ->
  snd (fst (mss_hloop (S f) a1 a2 qoff nb d h lo hi i b)) <= snd (mss_ins a1b a2 qoff nb d h lo (i + 1 + 1) bb).
Proof.
  intros until bb. intros H E H1 E1 H2. rewrite mss_hloop_S, H, E. cbv zeta. rewrite H1, E1, H2.
  pose proof (mss_ins_budget_le a1b a2 qoff nb d h lo (i + 1 + 1) bb). destruct (mss_ins a1b a2 qoff nb d h lo (i + 1 + 1) bb) as [a1c bc]. cbn [snd] in *.
  destruct (bc <? 0); [cbn; lia|]. pose proof (mss_hloop_budget_le f a1c a2 qoff nb d h lo hi (i + 1 + 1 + 1) bc). lia.
Qed.
Lemma mss_ins_shift_budget : forall a1 a2 qoff nb d h lo i b,
  snd (mss_ins a1 a2 qoff nb d h lo i b) = snd (mss_shift (S (Z.to_nat (i - lo))) a1 a2 qoff nb d h lo i (rd32 a1 i) b).
Proof. intros. rewrite mss_ins_eq. cbv zeta. destruct (mss_shift _ _ _ _ _ _ _ _ _ _ _) as [[a1' j] b']. reflexivity. Qed.

(* [comment removed for export] *)
Lemma shift_fuel_ok : forall h x, 1 <= h -> 0 <= x -> x < h * Z.of_nat (S (Z.to_nat x)).
Proof. intros h x Hh Hx. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. nia. Qed.

Lemma mss_hps_le_hloop : forall r a1 a2 qoff nb d lo hi hp b,
  snd (fst (mss_hps (S r) a1 a2 qoff nb d lo hi hp b)) <=
  snd (fst (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff nb d (incs_at hp) lo hi (lo + incs_at hp) b)).
Proof.
  intros. rewrite mss_hps_S. cbv zeta. destruct (mss_hloop _ _ _ _ _ _ _ _ _ _ _) as [[a1' b'] ex]. cbn [fst snd].
  destruct ex; [cbn; lia|]. apply mss_hps_budget_le.
Qed.
Lemma mss_hp_S : forall f bigN hp, mss_hp (S f) bigN hp = if incs_at hp <? bigN then mss_hp f bigN (hp + 1) else hp.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma incs_at_13 : incs_at 13 = 2391484. Proof. reflexivity. Qed.
Lemma incs_at_0 : incs_at 0 = 1. Proof. reflexivity. Qed.
Lemma incs_at_pos13 : forall k, 0 <= k <= 13 -> 1 <= incs_at k.
Proof. intros. pose proof (incs_at_pos k H). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCQsortM1.

(* [comment removed for export] *)

Lemma pr_mswap : forall nb a1 lo hi x y, nb <= 4294967296 -> pr nb a1 lo hi -> lo <= x <= hi -> lo <= y <= hi -> pr nb (mswap a1 x y) lo hi.
Proof.
  intros nb a1 lo hi x y Hnb P Hx Hy z Hz. unfold mswap.
  pose proof (P x Hx). pose proof (P y Hy). pose proof (P z Hz).
  destruct (Z.eq_dec z y) as [->|NE].
  - rewrite rd32_wr32_same by lia. lia.
  - rewrite rd32_wr32_other by lia. destruct (Z.eq_dec z x) as [->|NE2].
    + rewrite rd32_wr32_same by lia. lia.
    + rewrite rd32_wr32_other by lia. lia.
Qed.
Lemma zbok_mswap : forall a1 x y, zbok a1 -> zbok (mswap a1 x y).
Proof. intros. unfold mswap. apply zbok_wr32, zbok_wr32. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSewA.
Lemma mvswap_0 : forall f a1 p1 p2, mvswap f a1 p1 p2 0 = a1.
Proof. intros. destruct f; [reflexivity|]. rewrite mvswap_S. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCQsortM2.

Lemma ntrip_Q2 : forall q pp,
  ntrip (Q2 q pp) 0 = (TOPlo q, KN q pp, TOPd q) /\
  ntrip (Q2 q pp) 1 = (KM q pp, TOPhi q, TOPd q) /\
  ntrip (Q2 q pp) 2 = (KN q pp + 1, KM q pp - 1, TOPd q + 1).
Proof.
  intros. unfold ntrip, Q2. cbn [mq_nlo mq_nhi mq_nd]. rewrite !zget_zset. cbn. repeat split; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma net_explicit : forall q,
  let e0 := ntrip q 0 in let e1 := ntrip q 1 in let e2 := ntrip q 2 in
  let '(f0, f1) := (if nsz e0 <? nsz e1 then (e1, e0) else (e0, e1)) in
  let '(g1, g2) := (if nsz f1 <? nsz e2 then (e2, f1) else (f1, e2)) in
  let '(h0, h1) := (if nsz f0 <? nsz g1 then (g1, f0) else (f0, g1)) in
  ntrip (net q) 0 = h0 /\ ntrip (net q) 1 = h1 /\ ntrip (net q) 2 = g2.
Proof.
  intros q. cbv zeta. unfold net. rewrite !mnextsize_ntrip.
  destruct (nsz (ntrip q 0) <? nsz (ntrip q 1)) eqn:C1;
  rewrite ?mnextsize_ntrip; rewrite ?ntrip_swap by lia; cbn [Z.eqb Pos.eqb];
  [ destruct (nsz (ntrip q 0) <? nsz (ntrip q 2)) eqn:C2 | destruct (nsz (ntrip q 1) <? nsz (ntrip q 2)) eqn:C2 ];
  rewrite ?mnextsize_ntrip; rewrite ?ntrip_swap by lia; cbn [Z.eqb Pos.eqb];
  match goal with |- context [if ?c then mnextswap _ 0 1 else _] => destruct c eqn:C3 end;
  rewrite ?ntrip_swap by lia; cbn [Z.eqb Pos.eqb]; repeat split; reflexivity.
Qed.
Lemma PUSH3_fields : forall q,
  let sp := mq_sp q in
  let '(l0, h0, d0) := ntrip q 0 in let '(l1, h1, d1) := ntrip q 1 in let '(l2, h2, d2) := ntrip q 2 in
  mq_sp (PUSH3 q) = sp + 3 /\
  mq_slo (PUSH3 q) = zset (zset (zset (mq_slo q) sp l0) (sp + 1) l1) (sp + 2) l2 /\
  mq_shi (PUSH3 q) = zset (zset (zset (mq_shi q) sp h0) (sp + 1) h1) (sp + 2) h2 /\
  mq_sd (PUSH3 q) = zset (zset (zset (mq_sd q) sp d0) (sp + 1) d1) (sp + 2) d2 /\
  mq_a1 (PUSH3 q) = mq_a1 q /\ mq_budget (PUSH3 q) = mq_budget q /\ mq_exit (PUSH3 q) = mq_exit q /\
  mq_nlo (PUSH3 q) = mq_nlo q /\ mq_nhi (PUSH3 q) = mq_nhi q /\ mq_nd (PUSH3 q) = mq_nd q.
Proof.
  intros q. cbv zeta. unfold ntrip, PUSH3, mpush. cbn. replace (mq_sp q + 1 + 1) with (mq_sp q + 2) by lia.
  replace (mq_sp q + 2 + 1) with (mq_sp q + 3) by lia. repeat split; reflexivity.
Qed.
Lemma net_frame : forall q, mq_sp (net q) = mq_sp q /\ mq_slo (net q) = mq_slo q /\ mq_shi (net q) = mq_shi q /\ mq_sd (net q) = mq_sd q /\
  mq_a1 (net q) = mq_a1 q /\ mq_budget (net q) = mq_budget q /\ mq_exit (net q) = mq_exit q.
Proof. intros. cps_pose (net_spec q) as (_ & _ & H). exact H. Qed.

(* [comment removed for export] *)
Definition srt2 (x y : Z * Z * Z) : (Z * Z * Z) * (Z * Z * Z) := if nsz x <? nsz y then (y, x) else (x, y).

Lemma iter_push_shape : forall a1 qsp slo shi sd nlo nhi nd b pp,
  let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
  let lo := zget slo (qsp - 1) in let hi := zget shi (qsp - 1) in let d := zget sd (qsp - 1) in
  let kn := lo + mp_unLo pp - mp_ltLo pp - 1 in let km := hi - (mp_gtHi pp - mp_unHi pp) + 1 in
  let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
  let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1) in
  let '(h0, h1) := srt2 f0 g1 in
  let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
  let q' := PUSH3 (net (Q2 q pp)) in
  mq_sp q' = qsp + 2 /\
  mq_slo q' = zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2 /\
  mq_shi q' = zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2 /\
  mq_sd q' = zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2 /\
  mq_a1 q' = A1V q pp /\ mq_budget q' = b /\ mq_exit q' = false.
Proof.
  intros. cbv zeta. unfold srt2.
  pose proof (PUSH3_fields (net (Q2 q pp))) as P. cbv zeta in P.
  cps_pose (net_frame (Q2 q pp)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  pose proof (net_explicit (Q2 q pp)) as NE. cbv zeta in NE.
  cps_pose (ntrip_Q2 q pp) as (N0 & N1 & N2). rewrite N0, N1, N2 in NE.
  unfold KN, KM in NE. unfold TOPlo, TOPhi, TOPd in NE. subst q. cbn [mq_slo mq_shi mq_sd mq_sp] in NE. subst kn km. subst lo hi d.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:C1 end; try rewrite C1 in NE; cbv beta iota in NE; cbv beta iota;
  (match goal with |- context [if ?c then _ else _] => destruct c eqn:C2 end; try rewrite C2 in NE; cbv beta iota in NE; cbv beta iota);
  (match goal with |- context [if ?c then _ else _] => destruct c eqn:C3 end; try rewrite C3 in NE; cbv beta iota in NE; cbv beta iota);
  cps_destruct NE as (E0 & E1 & E2);
  rewrite E0, E1, E2 in P; rewrite F1, F2, F3, F4, F5, F6, F7 in P; unfold Q2 in P; cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget mq_exit] in P;
  replace (qsp - 1 + 1) with qsp in P by lia; replace (qsp - 1 + 2) with (qsp + 1) in P by lia; replace (qsp - 1 + 3) with (qsp + 2) in P by lia;
  cps_destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _); repeat split; assumption.
Qed.

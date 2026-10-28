(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Stdio AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_anndefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_h_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma vcost_pushes_app : forall a b c s,
  vcost_pushes (a + b) c s = vcost_pushes a c s + vcost_pushes b (vcap_iter a c s) (s + Z.of_nat a).
Proof.
  induction a as [|a IH]; intros b c s.
  - cbn [Nat.add vcost_pushes vcap_iter]. rewrite Nat2Z.inj_0, Z.add_0_r. lia.
  - cbn [Nat.add]. rewrite vcost_pushes_S, vcap_iter_S0, (IH b (vcap_after c s) (s + 1)), vcost_pushes_S.
    replace (s + 1 + Z.of_nat a) with (s + Z.of_nat (S a)) by lia. lia.
Qed.

Lemma vcost_nogrow : forall n c s, 0 <= s -> s + Z.of_nat n <= c -> vcost_pushes n c s = 0 /\ vcap_iter n c s = c.
Proof.
  induction n as [|n IH]; intros c s S0 H; [split; reflexivity|].
  rewrite vcost_pushes_S, vcap_iter_S0.
  assert (E1 : vcost_push c s = 0) by (unfold vcost_push; destruct (Z.ltb_spec s c); [reflexivity| lia]).
  assert (E2 : vcap_after c s = c) by (unfold vcap_after; destruct (Z.ltb_spec s c); [reflexivity| lia]).
  rewrite E1, E2. destruct (IH c (s + 1) ltac:(lia) ltac:(lia)) as [-> ->]. split; reflexivity.
Qed.

Fixpoint sumd (k : nat) (c : Z) : Z := match k with O => 0 | S k' => mcost (16 * (2 * c)) + sumd k' (2 * c) end.

Lemma sumd_nonneg : forall k c, 1 <= c -> 0 <= sumd k c.
Proof. induction k as [|k IH]; intros c Hc; cbn [sumd]; [lia|]. pose proof (mcost_nonneg (16 * (2 * c)) ltac:(lia)). specialize (IH (2 * c) ltac:(lia)). lia. Qed.

Lemma vcost_grow_bound : forall k n c s, 1 <= c -> 0 <= s <= c -> s + Z.of_nat n <= c * 2 ^ (Z.of_nat k) -> vcost_pushes n c s <= sumd k c.
Proof.
  induction k as [|k IH]; intros n c s C1 SC H.
  - rewrite Nat2Z.inj_0, Z.pow_0_r, Z.mul_1_r in H. destruct (vcost_nogrow n c s ltac:(lia) H) as [-> _]. cbn [sumd]. lia.
  - destruct (Z_le_gt_dec (s + Z.of_nat n) c) as [LE|GT].
    + destruct (vcost_nogrow n c s ltac:(lia) LE) as [-> _]. apply sumd_nonneg. exact C1.
    +
      set (a := Z.to_nat (c - s)).
      assert (EA : Z.of_nat a = c - s) by (subst a; rewrite Z2Nat.id; lia).
      assert (NB : (a < n)%nat) by lia.
      replace n with (a + S (n - a - 1))%nat by lia.
      rewrite vcost_pushes_app. destruct (vcost_nogrow a c s ltac:(lia) ltac:(lia)) as [-> ->].
      rewrite vcost_pushes_S. replace (s + Z.of_nat a) with c by lia.
      assert (EP : vcost_push c c = mcost (16 * (2 * c))).
      { unfold vcost_push, vcap_next. destruct (Z.ltb_spec c c); [lia|]. f_equal. f_equal. lia. }
      assert (EC : vcap_after c c = 2 * c) by (unfold vcap_after, vcap_next; destruct (Z.ltb_spec c c); lia).
      rewrite EP, EC. cbn [sumd].
      assert (R : vcost_pushes (n - a - 1) (2 * c) (c + 1) <= sumd k (2 * c)).
      { apply IH; [lia| lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
        replace (Z.of_nat (n - a - 1)%nat) with (Z.of_nat n - Z.of_nat a - 1) by lia. lia. }
      lia.
Qed.

Lemma sumd_25_1 : sumd 25 1 = 2200010752.
Proof. vm_compute. reflexivity. Qed.

Lemma atp_P_bound : forall l : list Z, zlength l < 2^26 -> Z.of_nat (atp_P l) <= 2^24 + 1.
Proof.
  intros l H. unfold atp_P, atp_parts. unfold zlength in H.
  destruct l as [|c l']; [cbn; lia|].
  pose proof (split_go_count (S (length (c :: l'))) (c :: l')) as B. change (2^24) with 16777216. change (2^26) with 67108864 in H.
  set (k := length (split_go (S (length (c :: l'))) (c :: l'))) in *. set (L := length (c :: l')) in *. lia.
Qed.

Theorem vcb_ok : forall l : list Z, zlength l < 2^26 -> 8 + vcost_pushes (atp_P l) 0 0 <= 2^31 + 2^26.
Proof.
  intros l H. pose proof (atp_P_bound l H) as PB.
  assert (P2 : (2 <= atp_P l)%nat) by (unfold atp_P; lia).
  destruct (atp_P l) as [|n] eqn:EP; [lia|].
  rewrite vcost_pushes_S. unfold vcost_push, vcap_after, vcap_next.
  replace (0 <? 0) with false by reflexivity.
  replace (Z.max (2 * 0) (0 + 1)) with 1 by reflexivity. replace (0 + 1) with 1 by reflexivity.
  pose proof (vcost_grow_bound 25 n 1 1 ltac:(lia) ltac:(lia)) as G.
  rewrite Z.mul_1_l in G. specialize (G ltac:(change (2 ^ Z.of_nat 25) with 33554432; lia)).
  rewrite sumd_25_1 in G.
  assert (M16 : mcost (16 * 1) = 2097152) by (vm_compute; reflexivity).
  rewrite M16. change (2 ^ 31 + 2 ^ 26) with 2214592512. lia.
Qed.

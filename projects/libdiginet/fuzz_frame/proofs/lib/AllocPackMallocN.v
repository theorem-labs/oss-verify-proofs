(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_ubjson_encoder/lib/S8/Spec/UbjRefFactsS8.v, with its module paths and module names changed; 109 of its 141 lines of code are new or changed and 716 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/AllocPackMallocN.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YO0i YO0f YO0g YO0q.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import AllocPack.
Import ListNotations.
Local Open Scope Z_scope.

Ltac bz2 := repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_prop in H as [? ?]
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ || _) = false |- _ => apply orb_false_iff in H as [? ?]
  end.

Lemma ltb_min u x : x <= 32 -> (u <? 4 * x) = (Z.min u 128 <? 4 * x).
Proof.
  intros H. destruct (Z.le_ge_cases u 128) as [E|E].
  - rewrite Z.min_l by exact E. reflexivity.
  - rewrite Z.min_r by exact E. rewrite (proj2 (Z.ltb_ge u (4 * x))) by lia.
    rewrite (proj2 (Z.ltb_ge 128 (4 * x))) by lia. reflexivity.
Qed.

Lemma hwe_min f : forall cnt u, cnt <= 32 -> halve_while_even f cnt u = halve_while_even f cnt (Z.min u 128).
Proof.
  induction f as [|f IH]; intros cnt u H; [reflexivity|]. cbn [halve_while_even].
  rewrite <- (ltb_min u cnt H). destruct (Z.even cnt && (u <? 4 * cnt)); [|reflexivity].
  apply IH. apply Z.div_le_upper_bound; lia.
Qed.

Lemma small_row k : znth 0 (nth k small_cnt_tab []) <= 32 /\ znth 1 (nth k small_cnt_tab []) <= 32.
Proof. do 9 (destruct k as [|k]; [split; apply Z.leb_le; reflexivity|]). destruct k; split; apply Z.leb_le; reflexivity. Qed.

Lemma med_row i : znth i med_cnt_tab <= 32.
Proof. unfold znth. destruct (Z.to_nat i) as [|[|[|[|k]]]]; [| | | |destruct k]; apply Z.leb_le; reflexivity. Qed.

Lemma init_min c u : initial_cnt c u = initial_cnt c (Z.min u 128).
Proof.
  unfold initial_cnt, small_cnt. cbv zeta. destruct (small_row (Z.to_nat c)) as [R0 R1].
  rewrite (ltb_min u _ R0), (ltb_min u _ R1).
  rewrite (hwe_min 8 _ u (med_row (Z.land c 3))). reflexivity.
Qed.

Definition cnt_ok (c u : Z) : bool :=
  let k := initial_cnt c u in let size := class_size c in
  (1 <=? k) && (k <=? FC c) &&
  implb ((Z.land c 3 =? 1) && (8 * PGSZ <? size * k)) (2 <=? k) &&
  implb ((Z.land c 3 =? 2) && (4 * PGSZ <? size * k)) (3 <=? k) &&
  implb ((Z.land c 3 =? 0) && (8 * PGSZ <? size * k)) (3 <=? k) &&
  implb ((Z.land c 3 =? 0) && (2 * PGSZ <? size * k)) (5 <=? k).

Lemma cnt_tab : forallb (fun c => forallb (fun u => cnt_ok c u) (zseq 0 129)) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cnt_facts c u : 0 <= c < 48 -> 0 <= u -> cnt_ok c u = true.
Proof.
  intros Hc Hu. assert (E : cnt_ok c u = cnt_ok c (Z.min u 128)) by (unfold cnt_ok; rewrite (init_min c u); reflexivity).
  rewrite E. brute cnt_tab c as T. rewrite forallb_forall in T. apply T. apply zseq_In; lia.
Qed.

Lemma cnt_props c u : 0 <= c < 48 -> 0 <= u ->
  1 <= initial_cnt c u <= FC c /\
  (Z.land c 3 = 1 -> 8 * PGSZ < class_size c * initial_cnt c u -> 2 <= initial_cnt c u) /\
  (Z.land c 3 = 2 -> 4 * PGSZ < class_size c * initial_cnt c u -> 3 <= initial_cnt c u) /\
  (Z.land c 3 = 0 -> 8 * PGSZ < class_size c * initial_cnt c u -> 3 <= initial_cnt c u) /\
  (Z.land c 3 = 0 -> 2 * PGSZ < class_size c * initial_cnt c u -> 5 <= initial_cnt c u).
Proof.
  intros Hc Hu. pose proof (cnt_facts c u Hc Hu) as T. unfold cnt_ok in T. cbv zeta in T.
  set (k := initial_cnt c u) in *. clearbody k.
  rewrite !andb_true_iff in T. destruct T as (((((A & B) & C) & D) & E) & F).
  apply Z.leb_le in A. apply Z.leb_le in B.
  split; [lia|]. unfold implb in C, D, E, F.
  split; [|split; [|split]]; intros H1 H2.
  - rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in C. cbn [negb andb orb] in C. apply Z.leb_le. exact C.
  - rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in D. cbn [negb andb orb] in D. apply Z.leb_le. exact D.
  - rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in E. cbn [negb andb orb] in E. apply Z.leb_le. exact E.
  - rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in F. cbn [negb andb orb] in F. apply Z.leb_le. exact F.
Qed.

Lemma init_le c u : 0 <= c < 48 -> 0 <= u -> 1 <= initial_cnt c u <= FC c.
Proof. intros Hc Hu. exact (proj1 (cnt_props c u Hc Hu)). Qed.

Lemma init_big c u : 128 <= u -> initial_cnt c u = FC c.
Proof. intros H. unfold FC. rewrite init_min. rewrite Z.min_r by lia. reflexivity. Qed.

Lemma FC_bounds c : 0 <= c < 48 -> 8 <= FC c <= 32.
Proof. intros H. brute FC_tab c as T. apply andb_prop in T as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia. Qed.

Lemma mmap_cnt s c req u : 0 <= c < 48 -> 0 <= u ->
  1 <= fst (mmap_plan s c req (initial_cnt c u) u) <= initial_cnt c u.
Proof.
  intros Hc Hu. destruct (cnt_props c u Hc Hu) as (K1 & P1 & P2 & P3 & P4).
  set (k := initial_cnt c u) in *. clearbody k.
  unfold mmap_plan. cbv zeta. revert P1 P2 P3 P4.
  destruct (Z.even c && (c <? 32)); destruct (is_bouncing s c); cbn [negb andb];
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  intros P1 P2 P3 P4; cbn [fst]; bz2;
  first [clear P1 P2 P3 P4; lia
        | specialize (P1 ltac:(assumption) ltac:(assumption)); clear P2 P3 P4; lia
        | specialize (P2 ltac:(assumption) ltac:(assumption)); clear P1 P3 P4; lia
        | specialize (P3 ltac:(assumption) ltac:(assumption)); clear P1 P2 P4; lia
        | specialize (P4 ltac:(assumption) ltac:(assumption)); clear P1 P2 P3; lia].
Qed.

Lemma mmap_full s c req u : 0 <= c < 48 -> 128 <= u -> 0 <= usage_of s (c + 1) ->
  fst (mmap_plan s c req (FC c) u) = FC c.
Proof.
  intros Hc Hu Hn. pose proof (FC_bounds c Hc) as [F8 F32]. unfold mmap_plan. cbv zeta.
  destruct (Z.even c && (c <? 32));
  [rewrite (proj2 (Z.ltb_ge (u + usage_of s (c + 1)) (4 * FC c))) by lia | rewrite (proj2 (Z.ltb_ge u (4 * FC c))) by lia];
  cbn [andb]; rewrite (proj2 (Z.leb_gt (FC c) 7)) by lia; rewrite andb_false_r; reflexivity.
Qed.

Lemma stc_le n c : 0 <= n -> 0 <= c < 48 -> n + IB <= class_size c -> size_to_class n <= c.
Proof.
  intros Hn Hc Hf. pose proof (class_size_bounds c Hc) as [_ Cmax].
  unfold size_to_class. set (k := Z.shiftr (n + IB - 1) 4).
  assert (Ek : k = (n + IB - 1) / 16) by (subst k; rewrite Z.shiftr_div_pow2 by (unfold IB; lia); reflexivity).
  assert (Hk : 0 <= k < 8191).
  { rewrite Ek. unfold IB in *. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hkc : k < znth c size_classes).
  { assert (M : 16 * k <= n + IB - 1) by (rewrite Ek; apply Z.mul_div_le; lia). unfold class_size, UNIT, IB in *. lia. }
  brute class_of_units_ok k as T. cbv zeta in T.
  set (c' := class_of_units k) in *.
  apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
  apply Z.leb_le in T1. apply Z.ltb_lt in T2.
  destruct (Z.le_gt_cases c' c) as [L|L]; [exact L|]. exfalso.
  unfold implb in T4. rewrite (proj2 (Z.ltb_lt 0 c')) in T4 by lia. cbn [negb orb] in T4. apply Z.leb_le in T4.
  pose proof (class_size_mono c (c' - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as M. unfold class_size, UNIT in M. lia.
Qed.

Lemma nestF_false c cnt0 : 0 <= c < 48 -> 0 <= cnt0 <= FC c -> PGSZ / 2 < class_size c * cnt0 + UNIT -> nestF c = false.
Proof.
  intros Hc Hk H. unfold nestF. apply Z.leb_gt. pose proof (class_size_bounds c Hc).
  assert (class_size c * cnt0 <= class_size c * FC c) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma nf_len caps k : length (nf_build caps k) = k.
Proof. induction k as [|k IH]; cbn [nf_build]; [reflexivity|]. rewrite length_app, IH. cbn [length]. lia. Qed.

Lemma znth_app_l l x i : 0 <= i < Z.of_nat (length l) -> znth i (l ++ [x]) = znth i l.
Proof. unfold znth. intros H. apply app_nth1. lia. Qed.

Lemma znth_app_r l x i : i = Z.of_nat (length l) -> znth i (l ++ [x]) = x.
Proof. unfold znth. intros ->. rewrite Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma nf_stable caps k k' i : (k <= k')%nat -> 0 <= i < Z.of_nat k -> znth i (nf_build caps k') = znth i (nf_build caps k).
Proof.
  intros Hk. induction Hk as [|k' Hk IH]; intros Hi; [reflexivity|]. cbn [nf_build]. cbv zeta.
  rewrite znth_app_l by (rewrite nf_len; lia). apply IH, Hi.
Qed.

Lemma nf_at caps c : 0 <= c < 48 -> znth c (NF caps) = nf_next caps (nf_build caps (Z.to_nat c)) c.
Proof.
  intros Hc. unfold NF. rewrite (nf_stable caps (S (Z.to_nat c)) 48 c) by lia. cbn [nf_build]. cbv zeta.
  rewrite Z2Nat.id by lia. apply znth_app_r. rewrite nf_len. lia.
Qed.

Lemma nf_prefix caps c i : 0 <= i < c -> c <= 48 -> znth i (nf_build caps (Z.to_nat c)) = znth i (NF caps).
Proof. intros Hi Hc. unfold NF. symmetry. apply nf_stable; lia. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel NodesA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanWf5 AsanBudget AsanBudget2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_alloc_iface B_live B_policy5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arefund_nonneg : forall n, 0 <= arefund n.
Proof.
  intros n. unfold arefund. destruct (from_primary n); [lia|].
  pose proof (map_size_facts n) as (_ & _ & MP). change kPageSize with 4096 in MP.
  destruct (map_size n <? kBigMapSize); clear -MP; Z.div_mod_to_equations; lia.
Qed.
Lemma arefund_le_acharge : forall n, arefund n <= acharge n.
Proof.
  intros n. unfold arefund, acharge, kCmPrim. destruct (from_primary n); [lia|]. destruct (map_size n <? kBigMapSize); lia.
Qed.
Lemma acharge_bound : acharge_bound_stmt acharge arefund.
Proof. intros n. split; [apply arefund_nonneg| apply arefund_le_acharge]. Qed.
Lemma acharge_pos : forall n, 0 < acharge n.
Proof.
  intros n. unfold acharge, kCmPrim. destruct (from_primary n); [lia|].
  pose proof (map_size_facts n) as (_ & _ & MP). change kPageSize with 4096 in MP.
  assert (0 <= map_size n / 4096) by (apply Z.div_pos; lia). assert (0 <= map_size n / 32768) by (apply Z.div_pos; lia).
  destruct (map_size n <? kBigMapSize); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nbigZ (LB : list ablock) : Z := zlen (List.filter (fun b => 64512 <? ab_size b) LB).
Definition DEP (LB : list ablock) : Z := fold_right (fun b acc => arefund (ab_size b) + acc) 0 LB.
Definition ACC (s : aps) (LB : list ablock) : Z :=
  10000 * as_nprim_ever (aps_alloc s) + zlen (as_residue (aps_alloc s)) + as_ndepot_ins (aps_alloc s) + DEP LB + aps_credit s.
Definition BUDGET (s : aps) (LB : list ablock) : Prop :=
  0 <= aps_credit s /\ 0 <= as_nprim_ever (aps_alloc s) /\ 0 <= as_ndepot_ins (aps_alloc s) /\ ACC s LB <= kInitialCredit.

Lemma DEP_nonneg : forall LB, 0 <= DEP LB.
Proof. unfold DEP. induction LB as [|b LB IH]; cbn; [lia|]. pose proof (arefund_nonneg (ab_size b)). lia. Qed.
Lemma DEP_cons : forall b LB, DEP (b :: LB) = arefund (ab_size b) + DEP LB.
Proof. reflexivity. Qed.
Lemma DEP_app : forall L1 L2, DEP (L1 ++ L2) = DEP L1 + DEP L2.
Proof. unfold DEP. induction L1 as [|b L1 IH]; intros L2; cbn; [reflexivity| rewrite IH; lia]. Qed.
Lemma DEP_perm : forall LB LB', Permutation LB LB' -> DEP LB = DEP LB'.
Proof. intros LB LB' P. unfold DEP. induction P; cbn in *; lia. Qed.
Lemma DEP_remove_le : forall A LB, DEP (ab_remove A LB) <= DEP LB.
Proof.
  intros A LB. unfold DEP. induction LB as [|b LB IH]; cbn; [lia|]. pose proof (arefund_nonneg (ab_size b)).
  pose proof (DEP_nonneg LB) as D0. unfold DEP in D0. destruct (ab_addr b =? A); cbn; lia.
Qed.
(* [comment removed for export] *)
Lemma DEP_remove_In : forall A LB b, In b LB -> ab_addr b = A -> List.NoDup (map ab_addr LB) ->
  DEP (ab_remove A LB) + arefund (ab_size b) = DEP LB.
Proof.
  intros A LB. unfold DEP. induction LB as [|x LB IH]; intros b Hin HA ND; [destruct Hin|]. cbn. cbn in ND. apply List.NoDup_cons_iff in ND as [NIN ND'].
  destruct Hin as [->|Hin].
  - rewrite HA, Z.eqb_refl. lia.
  - destruct (Z.eqb_spec (ab_addr x) A) as [EQ|NE].
    + exfalso. apply NIN. rewrite EQ, <- HA. apply in_map. exact Hin.
    + cbn. rewrite <- (IH b Hin HA ND'). lia.
Qed.
Lemma arefund_at_In : forall A LB b, In b LB -> ab_addr b = A -> List.NoDup (map ab_addr LB) ->
  arefund_at arefund A LB = arefund (ab_size b).
Proof.
  intros A LB. induction LB as [|x LB IH]; intros b Hin HA ND; [destruct Hin|]. unfold arefund_at, ab_find in *. cbn.
  cbn in ND. apply List.NoDup_cons_iff in ND as [NIN ND']. destruct Hin as [->|Hin].
  - rewrite HA, Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (ab_addr x) A) as [EQ|NE].
    + exfalso. apply NIN. rewrite EQ, <- HA. apply in_map. exact Hin.
    + exact (IH b Hin HA ND').
Qed.
Lemma arefund_at_nonneg : forall A LB, 0 <= arefund_at arefund A LB.
Proof. intros A LB. unfold arefund_at. destruct (ab_find A LB); [apply arefund_nonneg| lia]. Qed.

Lemma BUDGET_perm : forall s LB LB', Permutation LB LB' -> BUDGET s LB -> BUDGET s LB'.
Proof. intros s LB LB' P B. unfold BUDGET, ACC in *. rewrite <- (DEP_perm _ _ P). exact B. Qed.
Lemma BUDGET_credit_nonneg : forall s LB, BUDGET s LB -> 0 <= aps_credit s.
Proof. intros s LB (B & _). exact B. Qed.
Lemma BUDGET_init : forall E fsb, BUDGET (aps_init E fsb) [].
Proof. intros E fsb. unfold BUDGET, ACC, DEP. cbn. unfold kInitialCredit, zlen. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma BUDGET_close_malloc : forall s s' LB A n,
  BUDGET s LB -> acharge n <= aps_credit s ->
  0 <= aps_credit s' -> 0 <= as_nprim_ever (aps_alloc s') -> 0 <= as_ndepot_ins (aps_alloc s') ->
  10000 * as_nprim_ever (aps_alloc s') + zlen (as_residue (aps_alloc s')) + as_ndepot_ins (aps_alloc s') + arefund n + aps_credit s'
    <= 10000 * as_nprim_ever (aps_alloc s) + zlen (as_residue (aps_alloc s)) + as_ndepot_ins (aps_alloc s) + aps_credit s ->
  BUDGET s' (mkABlock A n :: LB).
Proof.
  intros s s' LB A n (B0 & B1 & B2 & B3) CH C0 N0 D0 STEP. unfold BUDGET, ACC in *. rewrite DEP_cons. cbn [ab_size].
  repeat split; try assumption. lia.
Qed.
Lemma BUDGET_close_free : forall s s' LB A b,
  BUDGET s LB -> In b LB -> ab_addr b = A -> List.NoDup (map ab_addr LB) ->
  0 <= aps_credit s' -> 0 <= as_nprim_ever (aps_alloc s') -> 0 <= as_ndepot_ins (aps_alloc s') ->
  10000 * as_nprim_ever (aps_alloc s') + zlen (as_residue (aps_alloc s')) + as_ndepot_ins (aps_alloc s') + aps_credit s'
    <= 10000 * as_nprim_ever (aps_alloc s) + zlen (as_residue (aps_alloc s)) + as_ndepot_ins (aps_alloc s) + aps_credit s + arefund (ab_size b) ->
  BUDGET s' (ab_remove A LB).
Proof.
  intros s s' LB A b (B0 & B1 & B2 & B3) Hin HA ND C0 N0 D0 STEP. unfold BUDGET, ACC in *.
  pose proof (DEP_remove_In A LB b Hin HA ND) as DR. repeat split; try assumption. lia.
Qed.
Lemma BUDGET_close_same : forall s s' LB,
  BUDGET s LB -> 0 <= aps_credit s' -> 0 <= as_nprim_ever (aps_alloc s') -> 0 <= as_ndepot_ins (aps_alloc s') ->
  10000 * as_nprim_ever (aps_alloc s') + zlen (as_residue (aps_alloc s')) + as_ndepot_ins (aps_alloc s') + aps_credit s'
    <= 10000 * as_nprim_ever (aps_alloc s) + zlen (as_residue (aps_alloc s)) + as_ndepot_ins (aps_alloc s) + aps_credit s ->
  BUDGET s' LB.
Proof. intros s s' LB (B0 & B1 & B2 & B3) C0 N0 D0 STEP. unfold BUDGET, ACC in *. repeat split; try assumption. lia. Qed.

(* [comment removed for export] *)
Lemma BUDGET_caps : forall s LB, BUDGET s LB ->
  DEP LB <= kInitialCredit /\ as_ndepot_ins (aps_alloc s) <= kInitialCredit
  /\ as_nprim_ever (aps_alloc s) <= kInitialCredit /\ zlen (as_residue (aps_alloc s)) <= kInitialCredit.
Proof.
  intros s LB (B0 & B1 & B2 & B3). unfold ACC in B3. pose proof (DEP_nonneg LB). pose proof (zlen_nonneg (as_residue (aps_alloc s))). lia.
Qed.

(* [comment removed for export] *)
Lemma DEP_live : forall LB a, Permutation (map (fun b => (ab_addr b, ab_size b)) LB) (live_blocks a) -> DEP LB = dep_live a.
Proof.
  intros LB a P. unfold DEP, dep_live.
  transitivity (fold_right (fun b acc => arefund (snd b) + acc) 0 (map (fun b => (ab_addr b, ab_size b)) LB)).
  - clear P. induction LB as [|b l IH]; cbn; [reflexivity| rewrite IH; reflexivity].
  - induction P; cbn in *; lia.
Qed.
Lemma nbigZ_live : forall LB a, Permutation (map (fun b => (ab_addr b, ab_size b)) LB) (live_blocks a) -> nbigZ LB = nbig_live a.
Proof.
  intros LB a P. unfold nbigZ, nbig_live, zlen. f_equal.
  transitivity (length (List.filter (fun b => 64512 <? snd b) (map (fun b => (ab_addr b, ab_size b)) LB))).
  - clear P. induction LB as [|b l IH]; cbn; [reflexivity|]. destruct (64512 <? ab_size b); cbn; rewrite IH; reflexivity.
  - apply Permutation_length. clear -P. induction P; cbn; [constructor| | |].
    + destruct (64512 <? x.2); [apply perm_skip|]; assumption.
    + destruct (64512 <? x.2), (64512 <? y.2); try apply perm_swap; try apply perm_skip; reflexivity.
    + etransitivity; eassumption.
Qed.
Lemma nbig_nbigZ : forall LB, nbig LB = nbigZ LB.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma LI_mat_le : forall S N EB mo, LI S N EB mo -> (length (m_vm_materialized mo) <= N)%nat.
Proof. intros S N EB mo L. apply (li_cap S N EB mo L); [apply (li_nodup S N EB mo L)| apply (li_inS S N EB mo L)]. Qed.

Lemma LI_backing_le : forall S N EB mo, LI S N EB mo -> vm_backing_used mo <= EB + Z.of_nat N * 4096.
Proof.
  intros S N EB mo L. rewrite vm_backing_used_split. pose proof (li_eager S N EB mo L) as E. pose proof (LI_mat_le S N EB mo L) as M.
  unfold page_size. apply Nat2Z.inj_le in M. nia.
Qed.

Theorem LI_grant_budget : forall S N EB mo nZ, LI S N EB mo ->
  EB + Z.of_nat N * 4096 + nZ <= vm_limit (m_vmmaps mo) -> vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof. intros S N EB mo nZ L H. pose proof (LI_backing_le S N EB mo L). lia. Qed.

(* [comment removed for export] *)
Definition OSL (aEB aNz : aps -> Z) (R : Z) (s : aps) (mo : Model) : Prop :=
  aEB s + 4096 * aNz s + 4096 * R <= vm_limit (m_vmmaps mo).
Lemma OSL_weaken : forall aEB aNz R R' s mo, R' <= R -> OSL aEB aNz R s mo -> OSL aEB aNz R' s mo.
Proof. intros aEB aNz R R' s mo LE H. unfold OSL in *. lia. Qed.
Lemma OSL_grant : forall aEB aNz R s mo S N nZ,
  LI S N (aEB s) mo -> Z.of_nat N <= aNz s -> OSL aEB aNz R s mo -> 0 <= nZ <= 4096 * R ->
  vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros aEB aNz R s mo S N nZ L HN HO HnZ. apply (LI_grant_budget S N (aEB s) mo nZ L). unfold OSL in HO. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BUDGET_STATIC (A0 : list (Z * Z)) (EB0 : Z) : Z := EB0 + 4096 * A0_pages A0 + 4096 * (kInitialCredit + 320000).

Theorem budget_headroom : forall A0 EB0 E s LB,
  Forall (fun iv => fst iv <= snd iv) A0 -> 0 <= EB0 ->
  AWf E [] [] (aps_alloc s) -> AQbound (aps_alloc s) -> depot_inv E (aps_alloc s) -> binv (aps_alloc s) ->
  Permutation (map (fun b => (ab_addr b, ab_size b)) LB) (live_blocks (aps_alloc s)) -> BUDGET s LB ->
  zlen (ae_keys0 E) <= 1000 -> ae_frames0 E <= 4096 ->
  aEB EB0 s + 4096 * aNz A0 s + 4096 * aps_credit s <= BUDGET_STATIC A0 EB0.
Proof.
  intros A0 EB0 E s LB A0ok EB0nn WF QB DI BI BM (B0 & B1 & B2 & B3) K0 F0.
  pose proof (M1 E _ WF QB BI) as X1. pose proof (M2 E _ WF QB BI) as X2.
  pose proof (depot_growth_amortised E [] [] _ WF DI K0 F0) as X3.
  pose proof (DEP_live LB _ BM) as X5.
  unfold ACC in B3. rewrite X5 in B3. unfold kInitialCredit in B3.
  unfold aEB, aEBa, aNz, aNza, a_eager_bytes, BUDGET_STATIC.
  change (AsanBudget2.interiors_a (aps_alloc s)) with (interiors_bound (aps_alloc s)) in X1.
  unfold kInitialCredit, kDepotNodeBlockBytes, kPtrArrayCommit in *.
  pose proof (zlen_nonneg (as_store_blocks (aps_alloc s))) as ZS. pose proof (zlen_nonneg (as_node_blocks (aps_alloc s))) as ZN.
  pose proof (zlen_nonneg (as_residue (aps_alloc s))) as ZR. pose proof (A0_pages_nonneg A0 A0ok) as ZA.
  assert (DZ : 0 <= dep_live (aps_alloc s)) by (rewrite <- X5; apply DEP_nonneg).
  destruct (as_ptr_committed (aps_alloc s) =? 0); clear -X1 X2 X3 B0 B1 B2 B3 ZS ZN ZR ZA DZ EB0nn; lia.
Qed.

(* [comment removed for export] *)
Corollary OSL_open : forall A0 EB0 E s LB R mo,
  Forall (fun iv => fst iv <= snd iv) A0 -> 0 <= EB0 ->
  AWf E [] [] (aps_alloc s) -> AQbound (aps_alloc s) -> depot_inv E (aps_alloc s) -> binv (aps_alloc s) ->
  Permutation (map (fun b => (ab_addr b, ab_size b)) LB) (live_blocks (aps_alloc s)) -> BUDGET s LB ->
  zlen (ae_keys0 E) <= 1000 -> ae_frames0 E <= 4096 ->
  BUDGET_STATIC A0 EB0 <= vm_limit (m_vmmaps mo) -> 0 <= R <= aps_credit s ->
  OSL (aEB EB0) (aNz A0) R s mo.
Proof.
  intros A0 EB0 E s LB R mo A0ok EB0nn WF QB DI BI BM BU K0 F0 LIM HR.
  pose proof (budget_headroom A0 EB0 E s LB A0ok EB0nn WF QB DI BI BM BU K0 F0). unfold OSL. lia.
Qed.

End RC__1.

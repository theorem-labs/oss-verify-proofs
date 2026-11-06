(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AsDepotInv AG_Malloc2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~03ast06ast_ok" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CarvedSlot.
  Context {HCEIL : HeapCeil}.
  Variable s : ltac2:(zQ "10!je$0").
  Hypothesis OK : ltac2:(zQ "10!k3@2$0?5HCEIL?1s").
  Let st := a_st s.
  Let W : WF st. Proof. exact (proj2 OK). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Variables (c0 : Z) (A0 : Z).
  Hypothesis CV : carved st c0 A0.
  Let sz0 := class_size c0.

  Lemma carved_vs_farray : forall c, 0 <= c < kNumClasses ->
    FA s c + rg_mapped_free_array (get_region st c) <= A0 \/ A0 + sz0 <= FA s c.
  Proof.
    intros c Hc. pose proof (WF_region st c W Hc) as RO. pose proof (ro_fa_bound _ _ RO) as FB. pose proof (ro_alloc_le _ _ RO) as AL. pose proof (ro_mapped_bound _ _ RO) as MB.
    pose proof (carved_range st _ _ W CV) as (CR1 & CR2 & CR3). ndestruct CV as (Hc0 & _ & _ & _ & CL). subst sz0. unfold FA. rewrite free_array_base_eq.
    destruct (Z.eq_dec c c0) as [->|NE].
    - right. unfold st in *. unfold kFreeArrayOffset, kUserMapSize in *. lia.
    - destruct (regions_disjoint st c c0 ltac:(lia) ltac:(unfold kNumClasses in Hc0; lia) NE) as [D|D];
        unfold st in *; unfold kFreeArrayOffset, kFreeArraySize, kUserMapSize in *; lia.
  Qed.

  Lemma carved_vs_tail : forall c, 0 <= c < kNumClasses ->
    RB s c + rg_mapped_user (get_region st c) <= A0 \/ A0 + sz0 <= RB s c + rg_allocated_user (get_region st c).
  Proof.
    intros c Hc. pose proof (WF_region st c W Hc) as RO. pose proof (ro_alloc_nonneg _ _ RO) as AN. pose proof (ro_alloc_le _ _ RO) as AL. pose proof (ro_mapped_bound _ _ RO) as MB.
    pose proof (carved_range st _ _ W CV) as (CR1 & CR2 & CR3). ndestruct CV as (Hc0 & _ & _ & _ & CL). subst sz0. unfold RB.
    destruct (Z.eq_dec c c0) as [->|NE].
    - right. unfold st in *. lia.
    - destruct (regions_disjoint st c c0 ltac:(lia) ltac:(unfold kNumClasses in Hc0; lia) NE) as [D|D];
        unfold st in *; unfold kFreeArrayOffset, kUserMapSize in *; lia.
  Qed.

  Lemma carved_vs_rinfo : A0 + sz0 <= a_ri s.
  Proof. pose proof (carved_in_space s OK _ _ CV) as (CS1 & CS2 & _). unfold a_ri. subst sz0. unfold st in *. lia. Qed.

  Lemma carved_vs_thread : a_thr s + kPageSize <= A0 \/ A0 + sz0 <= a_thr s.
  Proof.
    pose proof (carved_in_space s OK _ _ CV) as (CS1 & CS2 & _). npose PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_ctx : a_ctx s + 160 <= A0 \/ A0 + sz0 <= a_ctx s.
  Proof.
    pose proof (carved_in_space s OK _ _ CV) as (CS1 & CS2 & _). npose PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D3 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_pa : a_pa s + kPtrArrayReserve <= A0 \/ A0 + sz0 <= a_pa s.
  Proof.
    pose proof (carved_in_space s OK _ _ CV) as (CS1 & CS2 & _). npose PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_sec : forall sc, In sc (as_sec st) -> sc_map_beg sc + sc_map_size sc <= A0 \/ A0 + sz0 <= sc_map_beg sc.
  Proof.
    intros sc Hsc. pose proof (carved_in_space s OK _ _ CV) as (CS1 & CS2 & _).
    npose PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    npose (SEC sc Hsc) as (_ & _ & _ & _ & D & _). subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  Lemma carved_vs_depot : forall d, depot_placed s d ->
    (d_nb d + 16 * 65536 <= A0 \/ A0 + sz0 <= d_nb d) /\ (d_sb d + 8 * 32768 <= A0 \/ A0 + sz0 <= d_sb d).
  Proof.
    intros d DPL. pose proof (carved_in_space s OK _ _ CV) as (CS1 & CS2 & _). ndestruct DPL as (_ & _ & G3 & G4 & _).
    subst sz0. unfold st, disj, kSpaceSize, kPageSize in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma carved_vs_freech : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    compact_to_addr st c cp <> A0 ->
    compact_to_addr st c cp + class_size c <= A0 \/ A0 + sz0 <= compact_to_addr st c cp.
  Proof.
    intros c cp Hc Hin NE.
    assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
    destruct (carved_sep st _ _ _ _ W CV C') as [[_ E]|D]; [exfalso; exact (NE (eq_sym E))| subst sz0; lia].
  Qed.
  Lemma carved_vs_batch : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> qb_addr b <> A0 ->
    qb_addr b + kBatchSize <= A0 \/ A0 + sz0 <= qb_addr b.
  Proof.
    intros b Hb NE. pose proof (batch_carved s OK b Hb) as (C' & _).
    destruct (carved_sep st _ _ _ _ W CV C') as [[_ E]|D]; [exfalso; exact (NE (eq_sym E))|].
    change (class_size kBatchClass) with kBatchSize in D. subst sz0. lia.
  Qed.
End CarvedSlot.

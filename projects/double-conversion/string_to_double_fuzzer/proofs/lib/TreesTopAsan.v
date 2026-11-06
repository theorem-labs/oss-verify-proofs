(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs StartupHSAsan KindHSAsan MainHSAsan SegJ1Asan SegAsan MainItab AsanMain SegCertsAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Section Top.
  Variable TT : nat -> option (acs * plan * shape).
  Variable TM0 : nat -> mtree.
  Hypothesis TM0_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_main 0) (root_class i) (TM0 i) = true.

  Definition TH (i : nat) : mtree := MPre0 0 seg_u HT_m [(0%nat, TM0 i)].
  Lemma TH_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_kind 0) (root_class i) (TH i) = true.
  Proof. intros i Hi. unfold TH. apply (mtree_ok_seg00 HS_kind KCm BFUELm FUELm ITm TT 0 (root_class i) seg_u HT_m [(0%nat, TM0 i)] s_m m_lv (m_ok TT) m_holes eq_refl).
    cbn [mforest0_ok ht_of HT_m Nat.eqb fst snd]. rewrite (TM0_ok i Hi). reflexivity. Qed.
  Lemma TH_ok' : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_kind 1) (root_class i) (TH i) = true.
  Proof. exact TH_ok. Qed.

  Definition TREE0 (i : nat) : mtree := MPre0 0 seg_j1 HT_j1 [(0%nat, TH i); (1%nat, TH i)].
  Lemma TREE0_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_asan 0) (root_class i) (TREE0 i) = true.
  Proof. intros i Hi. unfold TREE0. apply (mtree_ok_seg00 HS_asan KCm BFUELm FUELm ITm TT 0 (root_class i) seg_j1 HT_j1 [(0%nat, TH i); (1%nat, TH i)] s_j1 j1_lv (j1_ok TT) j1_holes eq_refl).
    cbn [mforest0_ok ht_of HT_j1 Nat.eqb fst snd]. rewrite (TH_ok i Hi), (TH_ok' i Hi). reflexivity. Qed.
  Definition TREE (h i : nat) : mtree := TREE0 i.
  Lemma TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_asan h) (root_class i) (TREE h i) = true.
  Proof. intros [|h] ch i Hh Hi; [exact (TREE0_ok i Hi) | discriminate Hh]. Qed.
End Top.

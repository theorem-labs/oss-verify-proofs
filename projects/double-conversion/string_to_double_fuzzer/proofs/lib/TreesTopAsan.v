(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the tree is built from each CONFIG_RSEQ value's start-up hand-off (LPS 727298f3), on the renumbered seg_j1 and seg_u. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs StartupHSAsan KindHSAsan MainHSAsan SegJ1Asan SegAsan MainItab AsanMain SegCertsAsan PlanRegen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Section Top.
  Variable TT : nat -> option (acs * plan * shape).
  Variable TM0 : nat -> mtree.
  Hypothesis TM0_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_main 0) (root_class i) (TM0 i) = true.

  Definition TH (i : nat) : mtree := MPre0 0 seg_u_r HT_m [(0%nat, TM0 i)].
  Lemma TH_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_kind 0) (root_class i) (TH i) = true.
  Proof. intros i Hi. unfold TH. apply (mtree_ok_seg00 HS_kind KCm BFUELm FUELm ITm TT 0 (root_class i) seg_u_r HT_m [(0%nat, TM0 i)] s_m m_lv (m_ok TT) m_holes eq_refl).
    cbn [mforest0_ok ht_of HT_m Nat.eqb fst snd]. rewrite (TM0_ok i Hi). reflexivity. Qed.
  Lemma TH_ok' : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_kind 1) (root_class i) (TH i) = true.
  Proof. exact TH_ok. Qed.

  Definition TREE0 (i : nat) : mtree := MPre0 0 seg_j1_r HT_j1 [(0%nat, TH i); (1%nat, TH i)].
  (* one start-up hand-off per CONFIG_RSEQ value: [h] is 0 or 1 *)
  Lemma TREE0_ok : forall h i, (h = 0 \/ h = 1)%nat -> (i < 6)%nat ->
    mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_asan h) (root_class i) (TREE0 i) = true.
  Proof.
    intros h i Hh Hi. unfold TREE0.
    assert (J : pre0_check HS_asan KCm BFUELm FUELm ITm TT h HT_j1 seg_j1_r = COk s_j1)
      by (destruct Hh as [-> | ->]; [exact (j1_ok0 TT) | exact (j1_ok1 TT)]).
    apply (mtree_ok_seg00 HS_asan KCm BFUELm FUELm ITm TT h (root_class i) seg_j1_r HT_j1 [(0%nat, TH i); (1%nat, TH i)] s_j1 j1_lv J j1_holes eq_refl).
    cbn [mforest0_ok ht_of HT_j1 Nat.eqb fst snd]. rewrite (TH_ok i Hi), (TH_ok' i Hi). reflexivity. Qed.
  Definition TREE (h i : nat) : mtree := TREE0 i.
  Lemma TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TT 0 0 (HSA HS_asan h) (root_class i) (TREE h i) = true.
  Proof.
    intros [|[|h]] ch i Hh Hi; [exact (TREE0_ok 0 i (or_introl eq_refl) Hi) | exact (TREE0_ok 1 i (or_intror eq_refl) Hi) |].
    exfalso. unfold HS_asan, hlookup in Hh.
    destruct (find _ HS_asan_list) as [q|] eqn:Hf; [|discriminate Hh].
    apply find_some in Hf as [Hin Hq]. apply Nat.eqb_eq in Hq.
    assert (A : forallb (fun q => Nat.leb (fst q) 1) HS_asan_list = true) by (vm_compute; reflexivity).
    pose proof (proj1 (forallb_forall _ _) A q Hin) as B. apply Nat.leb_le in B. lia.
  Qed.
End Top.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ledger_agree (L1 L2 : mled) : Prop :=
  ld_resv L1 = ld_resv L2
  /\ Permutation (ld_groups L1) (ld_groups L2)
  /\ Permutation (ld_metas L1) (ld_metas L2)
  /\ ld_brkreg L1 = ld_brkreg L2
  /\ ld_brk L1 = ld_brk L2.

Lemma ledger_agree_refl L : ledger_agree L L.
Proof. repeat split; reflexivity. Qed.

Lemma ledger_agree_sym L1 L2 : ledger_agree L1 L2 -> ledger_agree L2 L1.
Proof. intros (A & B & C & D & E). repeat split; try (symmetry; assumption). Qed.

Lemma ledger_agree_trans L1 L2 L3 : ledger_agree L1 L2 -> ledger_agree L2 L3 -> ledger_agree L1 L3.
Proof.
  intros (A & B & C & D & E) (A' & B' & C' & D' & E'). repeat split; try congruence.
  - eapply Permutation_trans; eauto.
  - eapply Permutation_trans; eauto.
Qed.

Lemma ledger_agree_set_live L1 L2 v1 v2 : ledger_agree L1 L2 -> ledger_agree (set_live v1 L1) (set_live v2 L2).
Proof. intros (A & B & C & D & E). destruct L1, L2; cbn in *. repeat split; assumption. Qed.

Lemma strip_proj st : s_ctx (strip st) = s_ctx st /\ s_regions (strip st) = s_regions st /\ s_reserved (strip st) = s_reserved st.
Proof. repeat split; reflexivity. Qed.

Lemma inv_R_ledger_agree X1 X2 st1 st2 L1 L2 :
  inv_R X1 st1 L1 -> inv_R X2 st2 L2 -> strip st1 = strip st2 -> ledger_agree L1 L2.
Proof.
  intros R1 R2 Hs.
  pose proof (strip_proj st1) as (C1 & G1 & V1). pose proof (strip_proj st2) as (C2 & G2 & V2).
  rewrite Hs in C1, G1, V1. rewrite C2 in C1. rewrite G2 in G1. rewrite V2 in V1.
  (* [comment removed for export] *)
  assert (EF : forall rid r, frontier st1 rid r = frontier st2 rid r).
  { intros rid r. unfold frontier. rewrite C1. reflexivity. }
  split; [| split; [| split; [| split]]].
  - rewrite (ir_resv _ _ _ R1), (ir_resv _ _ _ R2). symmetry; exact V1.
  - eapply Permutation_trans; [exact (ir_groups _ _ _ R1)|]. rewrite <- G1. apply Permutation_sym. exact (ir_groups _ _ _ R2).
  - eapply Permutation_trans; [exact (ir_metas _ _ _ R1)|].
    erewrite map_ext; [rewrite <- G1; apply Permutation_sym; exact (ir_metas _ _ _ R2)|].
    intros [rid r]; cbn [fst snd]. rewrite EF. reflexivity.
  - destruct (ld_brkreg L1) as [[b l]|] eqn:E1.
    + symmetry. apply (proj2 (ir_brkreg _ _ _ R2 b l)). rewrite G1. apply (proj1 (ir_brkreg _ _ _ R1 b l)). exact E1.
    + destruct (ld_brkreg L2) as [[b l]|] eqn:E2; [|reflexivity]. exfalso.
      assert (ld_brkreg L1 = Some (b, l)); [|congruence].
      apply (proj2 (ir_brkreg _ _ _ R1 b l)). rewrite <- G1. apply (proj1 (ir_brkreg _ _ _ R2 b l)). exact E2.
  - pose proof (ir_brk _ _ _ R1) as B1. pose proof (ir_brk _ _ _ R2) as B2. rewrite C1 in B2.
    destruct (c_brk (s_ctx st1)); first [rewrite B1, B2 | destruct B1 as [-> _], B2 as [-> _]]; reflexivity.
Qed.

Theorem INVL_ledger_agree X1 X2 st1 st2 L1 L2 BL1 BL2 LS1 LS2 :
  INVL X1 st1 L1 BL1 LS1 -> INVL X2 st2 L2 BL2 LS2 -> strip st1 = strip st2 -> ledger_agree L1 L2.
Proof. intros (R1 & _) (R2 & _) Hs. exact (inv_R_ledger_agree X1 X2 st1 st2 L1 L2 R1 R2 Hs). Qed.
End RC__1.

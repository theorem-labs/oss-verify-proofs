(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocRep MallocTree MallocBlocks MallocFacts_A MallocFacts_inv MallocFacts_inv2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section ND.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variable LB : list block.
Hypothesis CR : CORR st LB BL.

Let IR := proj1 INV. Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
#[using="X st L BL LS INV CR IR IM IG IS"] Lemma LB_addr_slot b1 b2 : In b1 LB -> In b2 LB -> blk_addr b1 = blk_addr b2 -> blk_slot b1 = blk_slot b2.
Proof.
  intros H1 H2 EA.
  destruct (LB_geo X st L BL LS INV LB CR _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & RK1 & A1 & O1 & P1 & F1).
  destruct (LB_geo X st L BL LS INV LB CR _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & RK2 & A2 & O2 & P2 & F2).
  pose proof (sstart_succ st m1 i1) as SS1. pose proof (sstart_succ st m2 i2) as SS2.
  rewrite C1, C2, E1, E2.
  destruct (N.eq_dec (fst bm1) (fst bm2)) as [EF|NF].
  - (* [comment removed for export] *)
    destruct (aptr_eq_dec m2 m1) as [Em|NEm]; [destruct (Z.eq_dec i2 i1) as [Ei|NEi]|].
    + subst m2 i2. rewrite EF. reflexivity.
    + exfalso. rewrite E1 in N1. rewrite E2 in N2.
      destruct (sep_ext X st BL LS IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 (eq_sym EF) Hi2 (or_intror NEi) N2) as [A|A];
        rewrite EF, R2 in R1; inversion R1; subst r2; unfold UNIT, IB in *; lia.
    + exfalso. rewrite E1 in N1. rewrite E2 in N2.
      destruct (sep_ext X st BL LS IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 (eq_sym EF) Hi2 (or_introl NEm) N2) as [A|A];
        rewrite EF, R2 in R1; inversion R1; subst r2; unfold UNIT, IB in *; lia.
  - (* [comment removed for export] *)
    exfalso.
    pose proof (ir_disj _ _ _ IR _ _ _ _ R1 R2 NF) as DJ. unfold region_live_range in DJ. rewrite RK1, RK2 in DJ.
    destruct (group_in_region X st L BL LS INV _ _ Hm1) as (r1' & R1' & _ & B01 & GE1).
    destruct (group_in_region X st L BL LS INV _ _ Hm2) as (r2' & R2' & _ & B02 & GE2).
    rewrite R1 in R1'. inversion R1'; subst r1'. rewrite R2 in R2'. inversion R2'; subst r2'.
    rewrite gend_eq in GE1, GE2.
    pose proof (sstart0 X st LS IM bm1 m1 Hm1) as Z1. pose proof (sstart0 X st LS IM bm2 m2 Hm2) as Z2.
    pose proof (sstart_mono X st LS IG bm1 m1 0 i1 Hm1 ltac:(lia)) as M1. pose proof (sstart_mono X st LS IG bm2 m2 0 i2 Hm2 ltac:(lia)) as M2.
    pose proof (sstart_mono X st LS IG bm1 m1 (i1 + 1) (m_last_idx (MR st m1) + 1) Hm1 ltac:(lia)) as U1.
    pose proof (sstart_mono X st LS IG bm2 m2 (i2 + 1) (m_last_idx (MR st m2) + 1) Hm2 ltac:(lia)) as U2.
    unfold UNIT, IB in *. destruct DJ; lia.
Qed.

#[using="X st L BL LS INV CR IR IM IG IS"] Lemma LB_addr_nodup : List.NoDup (map blk_addr LB).
Proof.
  pose proof (LB_nodup X st L BL LS INV LB CR) as ND.
  assert (INJ : forall x y, In x LB -> In y LB -> blk_addr x = blk_addr y -> blk_slot x = blk_slot y)
    by (intros x y Hx Hy E; exact (LB_addr_slot x y Hx Hy E)).
  clear - ND INJ. induction LB as [|b LB' IH]; cbn in *; [constructor|].
  inversion ND as [|? ? NI ND']; subst. constructor.
  - intros Hin. apply in_map_iff in Hin. ddestruct Hin as (b' & E & Hb'). apply NI.
    rewrite (INJ b b' ltac:(now left) ltac:(now right) (eq_sym E)). apply in_map. exact Hb'.
  - apply IH; [exact ND'|]. intros x y Hx Hy. apply INJ; now right.
Qed.
End ND.

Theorem areach_addr_nodup : forall {resv} st LB, AREACH_from resv st LB -> List.NoDup (map blk_addr LB).
Proof.
  intros resv st LB AR. ddestruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  exact (LB_addr_nodup _ _ _ _ _ INV _ CR).
Qed.

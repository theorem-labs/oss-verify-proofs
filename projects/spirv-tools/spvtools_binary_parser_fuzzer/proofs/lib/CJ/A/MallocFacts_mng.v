(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog MI_Inv MI_Kit MI_Geom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocRep MallocTree MallocBlocks MallocFacts_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv MallocFacts_inv2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma areach_blocks_addr_distinct : forall {resv} st LB b1 b2,
  AREACH_from resv st LB -> In b1 LB -> In b2 LB -> blk_slot b1 <> blk_slot b2 ->
  fst (blk_slot b1) = fst (blk_slot b2) -> blk_addr b1 <> blk_addr b2.
Proof.
  intros resv st LB b1 b2 AR H1 H2 NE Hf.
  destruct (MallocFacts_inv.areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (MallocFacts_inv2.LB_geo _ _ _ _ _ INV _ CR _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & _ & A1 & O1 & P1 & F1).
  destruct (MallocFacts_inv2.LB_geo _ _ _ _ _ INV _ CR _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
  rewrite C1, C2, E1, E2 in Hf. cbn [fst] in Hf. rewrite Hf, R2 in R1. inversion R1; subst r2.
  rewrite A1, A2. pose proof (sstart_succ st m1 i1). pose proof (sstart_succ st m2 i2).
  assert (NE' : m2 <> m1 \/ i2 <> i1). { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, C2, E1, E2, Hf. reflexivity. }
  rewrite E1 in N1. rewrite E2 in N2.
  destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact Hf) Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

Lemma areach_blocks_addr_inj : forall {resv} st LB b1 b2,
  AREACH_from resv st LB -> In b1 LB -> In b2 LB -> blk_addr b1 = blk_addr b2 -> blk_slot b1 = blk_slot b2.
Proof.
  intros resv st LB b1 b2 AR H1 H2 EA.
  destruct (aptr_eq_dec (blk_slot b1) (blk_slot b2)) as [E|NE]; [exact E| exfalso].
  destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [Hf|Nf].
  - exact (areach_blocks_addr_distinct st LB b1 b2 AR H1 H2 NE Hf EA).
  -
    pose proof (MallocFacts_inv2.areach_facts_proof st LB AR) as MF.
    destruct (MallocFacts_inv.areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (MallocFacts_inv2.LB_geo _ _ _ _ _ INV _ CR _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & RK1 & A1 & O1 & P1 & F1).
    destruct (MallocFacts_inv2.LB_geo _ _ _ _ _ INV _ CR _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & RK2 & A2 & O2 & P2 & F2).
    pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
    destruct (MallocFacts_inv2.group_in_region _ _ _ _ _ INV _ _ Hm1) as (r1' & R1' & _ & B1 & G1).
    destruct (MallocFacts_inv2.group_in_region _ _ _ _ _ INV _ _ Hm2) as (r2' & R2' & _ & B2 & G2).
    rewrite R1 in R1'. inversion R1'; subst r1'. rewrite R2 in R2'. inversion R2'; subst r2'.
    rewrite gend_eq in G1, G2.
    pose proof (sstart_lt _ _ _ IG _ m1 i1 (m_last_idx (MR st m1) + 1) Hm1 ltac:(lia)) as U1.
    pose proof (sstart_lt _ _ _ IG _ m2 i2 (m_last_idx (MR st m2) + 1) Hm2 ltac:(lia)) as U2.
    pose proof (sstart_mono _ _ _ IG _ m1 0 i1 Hm1 ltac:(lia)) as L1. rewrite (sstart0 _ _ _ IM _ _ Hm1) in L1.
    pose proof (sstart_mono _ _ _ IG _ m2 0 i2 Hm2 ltac:(lia)) as L2. rewrite (sstart0 _ _ _ IM _ _ Hm2) in L2.
    assert (NR : fst bm1 <> fst bm2) by (rewrite C1, C2, E1, E2 in Nf; exact Nf).
    pose proof (ir_disj _ _ _ IR _ _ _ _ R1 R2 NR) as DJ. unfold region_live_range in DJ. rewrite RK1, RK2 in DJ.
    unfold UNIT, IB in *. lia.
Qed.

End AC_1.

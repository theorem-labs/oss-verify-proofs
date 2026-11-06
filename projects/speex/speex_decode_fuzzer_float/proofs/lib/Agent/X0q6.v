(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1q8 X1po X1pv X1pf X1pm X1px X1pj X1q3 X1qf
X1q0 X1q6 X1qd X1qj X1q5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm X0qn X0px X0q2 X0q7 X0q8 X0q9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HF2.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (LB : list block).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis CR : CORR st LB BL.

#[using="L BL LS INV CR"] Lemma blocks_apart_of_inv b1 b2 g2 i2 : In b1 LB -> In b2 LB -> blk_slot b1 <> blk_slot b2 ->
fst (blk_slot b1) = fst (blk_slot b2) ->
s_slots st !! (blk_slot b2) = Some (g2, i2) ->
blk_addr b1 + blk_size b1 <= conc st (blk_slot b2) - IB
\/ conc st (blk_slot b2) + get_stride (get_meta_rec st g2) <= blk_addr b1.
Proof.
intros H1 H2 NE EF SL2.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as IR IA IM IL IG IS ISH | sf_fb; destruct sfP_ as (IR & IA & IM & IL & IG & IS & ISH) ].
first [ pose proof (LB_geo x0 st L BL LS INV LB CR b1 H1) as sfP_; sf_destruct 20%nat sfP_ as c1 o1 n1 m1 bm1 i1 r1 K1 C1 S1 Hm1 Hi1 E1 N1 R1 RK1 A1 O1 P1 F1 | sf_fb; destruct (LB_geo x0 st L BL LS INV LB CR b1 H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & RK1 & A1 & O1 & P1 & F1) ].
first [ pose proof (LB_geo x0 st L BL LS INV LB CR b2 H2) as sfP_; sf_destruct 15%nat sfP_ as c2 o2 n2 m2 bm2 i2x r2 K2 C2 _ _ _ _ N2 _ | sf_fb; destruct (LB_geo x0 st L BL LS INV LB CR b2 H2) as (c2 & o2 & n2 & m2 & bm2 & i2x & r2 & K2 & C2 & _ & _ & _ & _ & N2 & _) ].
destruct (is_valid _ _ _ IS _ _ _ SL2) as ([bm2' Hm2'] & Hi2' & Ec2).
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm2') in Ec2.
rewrite C2 in Ec2. subst c2.
assert (EF' : fst bm2' = fst bm1) by (rewrite C1, E1, Ec2 in EF; cbn [fst] in EF; symmetry; exact EF).
assert (NE' : g2 <> m1 \/ i2 <> i1).
{ destruct (aptr_eq_dec g2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, E1, Ec2, EF'. reflexivity. }
assert (CC : conc st (blk_slot b2) = r_base r1 + sstart (MR st g2) i2).
{ rewrite Ec2. rewrite (conc_region' st _ r1); cbn [fst snd]; [reflexivity|]. rewrite EF'. exact R1. }
rewrite CC, A1, S1. unfold MR in *.
pose proof (sstart_succ st m1 i1) as X1. pose proof (sstart_succ st g2 i2) as X2. unfold MR in X1, X2.
destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 ltac:(rewrite <- E1; exact N1) g2 bm2' i2 Hm2' EF' Hi2' NE' ltac:(rewrite <- Ec2; exact N2)) as [A|A];
unfold MR in A; unfold UNIT, IB in *; lia.
Qed.

#[using="L BL LS INV"] Lemma stride_small_of_inv bm g ai : s_groups st !! bm = Some (mkGhdr (Some g) ai) ->
m_sizeclass (get_meta_rec st g) < 48 -> get_stride (get_meta_rec st g) < 2^20.
Proof.
intros Hb Hsc. pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as IR IA IM IL IG IS ISH | sf_fb; destruct sfP_ as (IR & IA & IM & IL & IG & IS & ISH) ].
destruct (hosts_GO x0 st L BL LS INV bm g ltac:(exists ai; exact Hb)) as (ai' & _ & GO).
pose proof (g_stride _ _ _ _ _ _ GO Hsc) as (_ & _ & S20). pose proof (g_li _ _ _ _ _ _ GO) as LI.
unfold cnt_of, MR in *.
destruct (Z.le_gt_cases 0 (get_stride (get_meta_rec st g))) as [P|N]; [|lia].
assert (X : get_stride (get_meta_rec st g) * 1 <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1))
by (apply Z.mul_le_mono_nonneg_l; lia).
lia.
Qed.
End HF2.

Theorem blocks_apart_of_areach {RCEIL : RunCeiling} {resv} st LB b1 b2 g2 i2 :
AREACH_from resv st LB -> In b1 LB -> In b2 LB -> blk_slot b1 <> blk_slot b2 ->
fst (blk_slot b1) = fst (blk_slot b2) ->
s_slots st !! (blk_slot b2) = Some (g2, i2) ->
blk_addr b1 + blk_size b1 <= conc st (blk_slot b2) - IB
\/ conc st (blk_slot b2) + get_stride (get_meta_rec st g2) <= blk_addr b1.
Proof.
intros AR H1 H2 NE EF SL. first [ pose proof (areach_inv resv st LB AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV _ _ _ CR | sf_fb; destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR) ].
exact (blocks_apart_of_inv st L BL LS LB INV CR b1 b2 g2 i2 H1 H2 NE EF SL).
Qed.

Theorem stride_small_of_areach {RCEIL : RunCeiling} {resv} st LB bm g ai :
AREACH_from resv st LB -> s_groups st !! bm = Some (mkGhdr (Some g) ai) ->
m_sizeclass (get_meta_rec st g) < 48 -> get_stride (get_meta_rec st g) < 2^20.
Proof.
intros AR Hb Hsc. first [ pose proof (areach_inv resv st LB AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV _ _ _ CR | sf_fb; destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR) ].
exact (stride_small_of_inv st L BL LS INV bm g ai Hb Hsc).
Qed.

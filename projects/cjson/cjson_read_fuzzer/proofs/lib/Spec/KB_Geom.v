(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocBlocks MallocFacts_A MallocFacts_inv MallocFacts_inv2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section G.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variable LB : list block.
Hypothesis CR : CORR st LB BL.

Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Lemma LB_span blk : In blk LB -> exists m bm i r,
  hosts st bm m /\ 0 <= i <= m_last_idx (MR st m) /\ blk_slot blk = (fst bm, sstart (MR st m) i)
  /\ s_groups st !! (fst bm, sstart (MR st m) i) = None
  /\ s_regions st !! (fst bm) = Some r /\ r_kind r = RKGroup
  /\ r_base r + sstart (MR st m) i <= blk_addr blk /\ 0 <= blk_size blk
  /\ blk_addr blk + blk_size blk + IB <= r_base r + sstart (MR st m) (i + 1)
  /\ sstart (MR st m) (i + 1) <= round_up_pg (r_len r) /\ 0 <= sstart (MR st m) i.
Proof.
  intros Hb. destruct (LB_geo _ _ _ _ _ INV _ CR blk Hb) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
  exists m, bm, i, r. rewrite Ec in NH. pose proof (sstart_succ st m i) as SS.
  destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r' & Hr' & _ & Hb0 & GE). rewrite Hr in Hr'. injection Hr' as <-.
  pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)) as SM. rewrite <- gend_eq in SM.
  pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)) as S0. rewrite (sstart0 _ _ _ IM _ _ Hm) in S0.
  rewrite C1, Ec. unfold UNIT, IB in *. splits; auto; lia.
Qed.

Theorem LB_apart b1 b2 : In b1 LB -> In b2 LB -> blk_slot b1 <> blk_slot b2 ->
  blk_addr b1 + blk_size b1 + IB <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + IB <= blk_addr b1.
Proof.
  intros H1 H2 NE.
  destruct (LB_span b1 H1) as (m1 & bm1 & i1 & r1 & Hm1 & Hi1 & E1 & N1 & R1 & K1 & A1 & Z1 & B1 & G1 & P1).
  destruct (LB_span b2 H2) as (m2 & bm2 & i2 & r2 & Hm2 & Hi2 & E2 & N2 & R2 & K2 & A2 & Z2 & B2 & G2 & P2).
  destruct (N.eq_dec (fst bm1) (fst bm2)) as [EF|NF].
  - (* [comment removed for export] *)
    rewrite <- EF in R2. rewrite R1 in R2. injection R2 as <-.
    assert (NE' : m2 <> m1 \/ i2 <> i1).
    { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite E1, E2, EF. reflexivity. }
    destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact EF) Hi2 NE' N2) as [A|A]; lia.
  - (* [comment removed for export] *)
    pose proof (ir_disj _ _ _ IR (fst bm1) (fst bm2) r1 r2 R1 R2 NF) as D.
    unfold region_live_range in D. rewrite K1, K2 in D. lia.
Qed.
End G.

(* [comment removed for export] *)
Theorem areach_blocks_apart : forall {resv} st LB b1 b2,
  AREACH_from resv st LB -> In b1 LB -> In b2 LB -> blk_slot b1 <> blk_slot b2 ->
  blk_addr b1 + blk_size b1 + IB <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + IB <= blk_addr b1.
Proof.
  intros resv st LB b1 b2 AR H1 H2 NE. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  exact (LB_apart _ _ _ _ _ INV _ CR b1 b2 H1 H2 NE).
Qed.

Theorem areach_block_span : forall {resv} st LB blk,
  AREACH_from resv st LB -> In blk LB -> exists r lo hi,
  s_regions st !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
  /\ 0 <= lo /\ r_base r + lo <= blk_addr blk /\ 0 <= blk_size blk /\ blk_addr blk + blk_size blk + IB <= r_base r + hi
  /\ hi <= round_up_pg (r_len r) /\ lo mod 16 = 0 /\ hi mod 16 = 0.
Proof.
  intros resv st LB blk AR Hb. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (LB_span _ _ _ _ _ INV _ CR blk Hb) as (m & bm & i & r & Hm & Hi & E & N & R & K & A & Z0 & B & G & P).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  exists r, (sstart (MR st m) i), (sstart (MR st m) (i + 1)). rewrite E. cbn [fst].
  destruct (hosts_ok _ _ _ IG _ _ Hm) as (ai & Hgb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [S16 SM].
  assert (M1 : sstart (MR st m) i mod 16 = 0).
  { unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hm). unfold UNIT in *.
    rewrite Z.add_mod, (Z.add_mod (snd bm) 16), A16, Z.mul_mod, SM by lia. reflexivity. }
  splits; auto; try lia.
  rewrite sstart_succ. unfold UNIT in *. rewrite Z.add_mod, M1, SM by lia. reflexivity.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

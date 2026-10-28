(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnCmp BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep BnIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma cmp_words_range : forall a b, -1 <= cmp_words a b <= 1.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn [cmp_words]; try lia.
  specialize (IH b). destruct (cmp_words a b =? 0) eqn:E; [|lia].
  destruct (x =? y); [lia|]. destruct (y <? x); lia.
Qed.

Lemma ucmp_pure_range : forall (a b : bignum bptr), bn_okm a -> bn_okm b -> -2147483648 < ucmp_pure a b < 2147483648.
Proof.
  intros a b (_ & TA & DA & _) (_ & TB & DB & _). unfold ucmp_pure. cbv zeta. unfold BN_WORDS_MAX, bn_dmax in *.
  destruct (Z.of_nat (bn_top a) - Z.of_nat (bn_top b) =? 0); [|lia].
  pose proof (cmp_words_range (firstn (bn_top a) (bn_buf a)) (firstn (bn_top b) (bn_buf b))). lia.
Qed.

Lemma cmp_pure_range : forall (a b : bignum bptr), -1 <= cmp_pure a b <= 1.
Proof.
  intros a b. unfold cmp_pure. cbv zeta.
  destruct (negb (eqb (bn_neg a) (bn_neg b))); [destruct (bn_neg a); lia|].
  destruct (bn_top b <? bn_top a)%nat; [destruct (bn_neg a); lia|].
  destruct (bn_top a <? bn_top b)%nat; [destruct (bn_neg a); lia|].
  destruct (cmp_words _ _ =? 0); [lia|]. destruct (0 <? cmp_words _ _); destruct (bn_neg a); lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma limbs_at_firstn : forall m D (l : list Z) k, u64arr bgusegs m D (wlimbs l) -> limbs_at bgusegs m D (firstn k l).
Proof.
  intros m D l k U. destruct (Nat.le_gt_cases k (length l)) as [Hk|Hk].
  - apply (proj1 (limbarr_split bgusegs m D l k Hk)) in U. destruct U as [U _]. apply limbs_at_of_u64arr. exact U.
  - rewrite firstn_all2 by lia. apply limbs_at_of_u64arr. exact U.
Qed.

Lemma arr_splice0 : forall W m m' D (buf w : list Z),
  u64arr bgusegs m D (wlimbs buf) -> munch W m m' -> wmono bgusegs m m' -> limbs_at bgusegs m' D w -> (length w <= length buf)%nat ->
  disjoint_from W D 0 ->
  disjoint_from W (D + 8 * Z.of_nat (length w)) (8 * Z.of_nat (length buf - length w)) ->
  u64arr bgusegs m' D (wlimbs (splice buf 0 w)).
Proof.
  intros W m m' D buf w UR MU WM HWL Hlen DJ0 DJ.
  apply (limbarr_limbs_at bgusegs) in UR. destruct UR as [HL1 HW1].
  assert (LS : length (splice buf 0 w) = length buf) by (apply splice_length; lia).
  pose proof (limbs_at_bound _ _ _ _ HL1) as BD.
  apply u64arr_of_limbs_at.
  - replace D with (D + 8 * Z.of_nat 0)%Z in HWL by lia.
    replace D with (D + 8 * Z.of_nat 0)%Z at 1 by lia. rewrite Z.add_0_r.
    eapply (BnKaraMem.limbs_at_splice bgusegs W m m' D buf 0 w HL1 MU); [lia | exact HWL | |].
    + replace (8 * Z.of_nat 0) with 0 by lia. exact DJ0.
    + exact DJ.
  - rewrite LS. eapply wr_at_transport; [exact HW1 | exact WM].
Qed.

Lemma d_cell : forall m a D (b : bignum bptr), rw_cells bgusegs m a (bn_cells D b) -> rw_cells bgusegs m a [C8 (wz D)].
Proof.
  intros m a D b SX. unfold bn_cells in SX.
  change [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]
    with ([C8 (wz D)] ++ [C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]) in SX.
  apply bk_rw_cells_app in SX. exact (proj1 SX).
Qed.

End WithCeiling0.

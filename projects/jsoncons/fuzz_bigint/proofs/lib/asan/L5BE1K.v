(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5BE1K.
Import L5A. Import L5CA. Import L5SA.
Lemma rg (k : Z) (n : nat) : k = Z.of_nat n -> 0 <= k < 32 -> (Z_to_bv 5 k : bv 5) = reg n.
Proof. intros -> _. reflexivity. Qed.
Lemma r3 : (3%bv : bv 5) = reg 3. Proof. apply bv_eq; reflexivity. Qed.
Lemma r8 : (8%bv : bv 5) = reg 8. Proof. apply bv_eq; reflexivity. Qed.
Lemma r9 : (9%bv : bv 5) = reg 9. Proof. apply bv_eq; reflexivity. Qed.
Lemma r18 : (18%bv : bv 5) = reg 18. Proof. apply bv_eq; reflexivity. Qed.
Lemma xw_eq : L5USA.xs_foot1 = [(6360528, 4); (6363185, 6); (6361072, 8); (6363236, 4)]. Proof. reflexivity. Qed.
Lemma xw2_eq : L5USA.xs_foot = [(6360528, 4); (6363185, 6)]. Proof. reflexivity. Qed.
Section WithLayout.
Variable L : asan_layout.
Hypothesis UNWL : L5USA.as0_unw_layout L.
Lemma xw_img : forall r a, In r [(6360528, 4); (6363185, 6); (6361072, 8); (6363236, 4)] -> L5.in_rng r a -> 0x10000 <= a < 0x634000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Proof.
  intros r a Hr Ha. unfold L5.in_rng in Ha.
  assert (X : exists r', In r' L5USA.UNW_STATICS /\ fst r' <= a < fst r' + snd r').
  { unfold L5USA.UNW_STATICS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO.
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha.
    - exists (0x610dc8, 12). split. left; reflexivity. cbn [fst snd]. clear - Ha; lia.
    - exists (0x611831, 6). split. right; right; left; reflexivity. cbn [fst snd]. clear - Ha; lia.
    - exists (0x610ff0, 8). split. right; left; reflexivity. cbn [fst snd]. clear - Ha; lia.
    - exists (0x611864, 4). split. right; right; right; left; reflexivity. cbn [fst snd]. clear - Ha; lia. }
  destruct X as (r' & Hr' & X). split.
  { pose proof L5USA.unw_statics_img as F. rewrite Forall_forall in F. specialize (F r' Hr'). clear - F X. lia. }
  exact (proj1 UNWL r' a Hr' X).
Qed.
Lemma xw2_img : forall r a, In r [(6360528, 4); (6363185, 6)] -> L5.in_rng r a -> 0x10000 <= a < 0x634000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Proof. intros r a Hr Ha. apply (xw_img r a). destruct Hr as [<-|[<-|[]]]. left; reflexivity. right; left; reflexivity. exact Ha. Qed.
End WithLayout.
End L5BE1K.

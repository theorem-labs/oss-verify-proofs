(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasFs BzCPermF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import
  BzCBlock BzCSortPost. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2Theory BzR3aFs BzR2D1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzR2E.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
Definition mainSort_sorted_hyp (e : est) : Prop :=
  let nb := e_nblock e in
  let qoff := (let i := nb + BZ_N_OVERSHOOT in if Z.land i 1 =? 0 then i else i + 1) in
  let wfact := WORKFACTOR in
  let wfact := if wfact <? 1 then 1 else if 100 <? wfact then 100 else wfact in
  let m := mainSort (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew znew znew znew qoff nb (nb * ((wfact - 1) / 3)) in
  10000 <= nb -> (mr_budget m <? 0) = false ->
  forall i j, 0 <= i -> i <= j -> j < nb ->
    lexle (rot (block_of (e_arr2 e) nb) (Z.to_nat (rd32 (mr_ptr m) i))) (rot (block_of (e_arr2 e) nb) (Z.to_nat (rd32 (mr_ptr m) j))).

Lemma mainSort_hyp_intro : forall e,
  zbok (e_arr2 e) -> 1 <= e_nblock e <= 1000000 -> bh_w32 (e_ftab e) ->
  mainSort_sorted_hyp e -> mainSort_hyp e.
Proof.
  intros e B2 NB FT SRT. unfold mainSort_hyp, mainSort_sorted_hyp in *. cbv zeta in *. intros GE. split.
  - apply mainSort_ftab; [exact B2|exact NB| |exact FT]. unfold BZ_N_OVERSHOOT. destruct (_ =? 0); lia.
  - intros BF. apply SRT; [exact GE|exact BF].
Qed.

Theorem blockSort_bwt' : forall e,
  zbok (e_arr1 e) -> zbok (e_arr2 e) -> bh_w32 (e_ftab e) -> 1 <= e_nblock e <= 900000 ->
  mainSort_sorted_hyp e ->
  let nb := e_nblock e in
  let t := block_of (e_arr2 e) nb in
  let e' := fst (fst (fst (blockSort e znew))) in
  bwt t (perm_pi (e_arr1 e')) (perm_rho (e_arr1 e') nb) /\
  fm_perm (e_arr1 e') nb /\
  e_origPtr e' = Z.of_nat (origPtr (perm_rho (e_arr1 e') nb)) /\
  (forall q, 0 <= q < nb -> rd8 (e_arr2 e') q = rd8 (e_arr2 e) q) /\
  e_nblock e' = nb /\ e_inUse e' = e_inUse e /\ e_unseqToSeq e' = e_unseqToSeq e.
Proof.
  intros e B1 B2 FT NB SRT. apply blockSort_bwt; try assumption. apply mainSort_hyp_intro; try assumption. lia.
Qed.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzR3cMain.
Section ACeilS2. Context {BZP : BzParams}.


Lemma mainSort_sorted_hyp_ok : forall e, zbok (e_arr2 e) -> e_nblock e <= 900000 -> mainSort_sorted_hyp e.
Proof.
  intros e B2 NB. unfold mainSort_sorted_hyp. cbv zeta. intros GE BF.
  match goal with |- context [mainSort ?a1 ?a2 ?ft ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?q ?n ?b] =>
    pose proof (mainSort_sorted a1 a2 ft l1 l2 l3 l4 l5 l6 l7 q n b B2 ltac:(lia)) as MS end.
  cbv zeta in MS. apply MS; [|exact BF]. unfold BZ_N_OVERSHOOT. destruct (_ =? 0); lia.
Qed.

(* [comment removed for export] *)
Theorem blockSort_bwt_ok : forall e,
  zbok (e_arr1 e) -> zbok (e_arr2 e) -> bh_w32 (e_ftab e) -> 1 <= e_nblock e <= 900000 ->
  let nb := e_nblock e in
  let t := block_of (e_arr2 e) nb in
  let e' := fst (fst (fst (blockSort e znew))) in
  bwt t (perm_pi (e_arr1 e')) (perm_rho (e_arr1 e') nb) /\
  fm_perm (e_arr1 e') nb /\
  e_origPtr e' = Z.of_nat (origPtr (perm_rho (e_arr1 e') nb)) /\
  (forall q, 0 <= q < nb -> rd8 (e_arr2 e') q = rd8 (e_arr2 e) q) /\
  e_nblock e' = nb /\ e_inUse e' = e_inUse e /\ e_unseqToSeq e' = e_unseqToSeq e.
Proof.
  intros e B1 B2 FT NB. apply blockSort_bwt'; try assumption. apply mainSort_sorted_hyp_ok; [exact B2|lia].
Qed.

End ACeilS2.

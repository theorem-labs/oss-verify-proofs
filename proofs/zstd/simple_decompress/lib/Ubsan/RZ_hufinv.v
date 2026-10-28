(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange ZdTbl ZdSeqBuildW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_block_iface RZ_tbl.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition HUFINVw (m : fmem) (DCTX : Z) (huf le : word) : Prop :=
  huf = Z_to_bv 64 (DCTX + 10296) /\
  (exists h4 : list byte, bytes_at usegs m (DCTX + 10296) h4 /\ length h4 = 4%nat /\ nth_error h4 0 = Some (Z_to_bv 8 12)) /\
  (bv_unsigned le mod 2^32 <> 0 -> exists dtb, bytes_at usegs m (DCTX + 10296) dtb /\ huf_tbl_ok dtb).

(* [comment removed for export] *)
Lemma bytes_at_agree' : forall (m : fmem) A (bs1 bs2 : list byte), bytes_at usegs m A bs1 -> bytes_at usegs m A bs2 ->
  (length bs1 <= length bs2)%nat -> bs1 = firstn (length bs1) bs2.
Proof.
  intros m A bs1 bs2 (_ & _ & H1) (_ & _ & H2) L.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite nth_error_firstn. replace (i <? length bs1)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i) Hi). symmetry. apply nth_error_None. rewrite firstn_length. lia.
Qed.

Lemma bytes_at_firstn' : forall (m : fmem) A (bs : list byte) n, bytes_at usegs m A bs -> bytes_at usegs m A (firstn n bs).
Proof.
  intros m A bs n (H0 & H1 & H). assert (L : (length (firstn n bs) <= length bs)%nat) by (rewrite firstn_length; lia).
  split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite (H i ltac:(lia)). rewrite nth_error_firstn. rewrite firstn_length in Hi.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hufw_of_full : forall m DCTX huf le dtb,
  huf = Z_to_bv 64 (DCTX + 10296) -> bytes_at usegs m (DCTX + 10296) dtb -> huf_hdr_ok dtb ->
  (bv_unsigned le mod 2^32 <> 0 -> huf_tbl_ok dtb) -> HUFINVw m DCTX huf le.
Proof.
  intros m DCTX huf le dtb E BA (L & N0) TOK. split; [exact E|]. split.
  - exists (firstn 4 dtb). split; [apply bytes_at_firstn'; exact BA|]. unfold HUF_DTABLE_BYTES in L.
    split; [rewrite firstn_length; lia|]. rewrite nth_error_firstn. exact N0.
  - intros NZ. exists dtb. split; [exact BA | exact (TOK NZ)].
Qed.

(* [comment removed for export] *)
Lemma hufw_full : forall m DCTX huf le, HUFINVw m DCTX huf le -> stk usegs m (DCTX + 10296) (DCTX + 26684) ->
  exists dtb, bytes_at usegs m (DCTX + 10296) dtb /\ huf_hdr_ok dtb /\ (bv_unsigned le mod 2^32 <> 0 -> huf_tbl_ok dtb).
Proof.
  intros m DCTX huf le (_ & (h4 & B4 & L4 & N4) & TOK) ST.
  destruct (stk_bytes usegs m _ _ ST ltac:(lia)) as (dtb & LD & BA).
  replace (DCTX + 26684 - (DCTX + 10296)) with 16388 in LD by lia.
  exists dtb. split; [exact BA|]. split.
  - split; [unfold HUF_DTABLE_BYTES; lia|].
    pose proof (bytes_at_agree' m _ h4 dtb B4 BA ltac:(lia)) as E4. rewrite L4 in E4.
    rewrite E4 in N4. rewrite nth_error_firstn in N4. exact N4.
  - intros NZ. destruct (TOK NZ) as (dtb2 & BA2 & OK2).
    assert (L2 : Z.of_nat (length dtb2) = 16388) by (destruct OK2 as [[L _] _]; exact L).
    pose proof (bytes_at_agree' m _ dtb2 dtb BA2 BA ltac:(lia)) as E2.
    replace (length dtb2) with (length dtb) in E2 by lia. rewrite firstn_all in E2. subst dtb2. exact OK2.
Qed.

(* [comment removed for export] *)
Lemma hufw_fine : forall (m m' : fmem) W DCTX huf le, HUFINVw m DCTX huf le -> munch W m m' ->
  (forall x, DCTX + 10296 <= x < DCTX + 26684 -> outside W x) -> HUFINVw m' DCTX huf le.
Proof.
  intros m m' W DCTX huf le (E & (h4 & B4 & L4 & N4) & TOK) MU OUT. split; [exact E|]. split.
  - exists h4. split; [|split; assumption].
    eapply (bytes_at_munch_in usegs m m' W _ _ (DCTX + 10296) (DCTX + 26684)); [exact B4 | exact MU | exact OUT | lia | lia].
  - intros NZ. destruct (TOK NZ) as (dtb & BA & OK). exists dtb. split; [|exact OK].
    assert (L : Z.of_nat (length dtb) = 16388) by (destruct OK as [[L _] _]; exact L).
    eapply (bytes_at_munch_in usegs m m' W _ _ (DCTX + 10296) (DCTX + 26684)); [exact BA | exact MU | exact OUT | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma hufw_init : forall m DCTX,
  bytes_at usegs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) -> HUFINVw m DCTX (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 0).
Proof.
  intros m DCTX BA. split; [reflexivity|]. split.
  - exists (le4 (Z_to_bv 64 201326604)). split; [exact BA|]. split; [reflexivity|].
    rewrite (le4_Z 201326604 201326604 eq_refl). reflexivity.
  - intros NZ. exfalso. apply NZ. reflexivity.
Qed.

Lemma hufw_frame : forall m m' W DCTX huf le,
  HUFINVw m DCTX huf le -> munch W m m' -> mem_inv usegs m -> mem_inv usegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> HUFINVw m' DCTX huf le.
Proof. intros m m' W DCTX huf le H MU _ _ OUT. eapply hufw_fine; [exact H | exact MU |]. intros x Hx. apply OUT. lia. Qed.

Theorem ptblw_laws : tbl_laws (ptbl HUFINVw).
Proof.
  constructor.
  - intros m DCTX BH _. apply (ptbl_init HUFINVw hufw_init). exact BH.
  - intros m m' W DCTX llt mlt oft huf le fe T MU MI MI' OUT. eapply (ptbl_frame HUFINVw hufw_frame); eassumption.
Qed.

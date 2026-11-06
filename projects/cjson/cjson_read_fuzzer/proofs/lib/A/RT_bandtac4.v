(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac3.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.

Definition BIGM : Z := 2^65.

Section CeilWrap.
Context {ACEIL : Ceil}.

Lemma oclr_bigM : forall lo hi, oclr lo hi -> hi <= 2^64 ->
  exists b1 b2 : Z, 0 <= b1 <= 1 /\ 0 <= b2 <= 1 /\ 4096 <= lo
    /\ hi <= 2147446784 + b1 * 36893488147419103232 /\ 17594333495296 * b1 <= lo
    /\ hi <= 65536 + b2 * 36893488147419103232 /\ 6287360 * b2 <= lo.
Proof.
  intros lo hi [S I] Hhi. unfold sclr, iclr, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *. destruct I as [I0 I].
  destruct S as [S|S]; destruct I as [I|I]; [exists 0, 0| exists 0, 1| exists 1, 0| exists 1, 1]; lia.
Qed.

Lemma ablk_bigM : forall lo hi, ablk lo hi ->
  exists b : Z, 0 <= b <= 1 /\ 6287360 <= lo /\ hi <= alloc_ceiling
    /\ hi <= 2147446784 + b * 36893488147419103232 /\ 17594333495296 * b <= lo.
Proof.
  intros lo hi H. pose proof alloc_ceiling_range as CR. unfold ablk, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI in *.
  destruct H as [[H1 H2]|[H1 H2]]; [exists 0| exists 1]; lia.
Qed.

End CeilWrap.

Ltac olin_core P lo hi ::=
  let L := fresh "OLx" in let b1 := fresh "bo" in let b2 := fresh "bi" in
  first [ destruct (oclr_bigM lo hi P ltac:(lia)) as (b1 & b2 & L)
        | pose proof (oclr_lin lo hi P ltac:(lia)) as L; unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in L ].
Ltac alin_core P lo hi ::=
  let L := fresh "ALx" in let b := fresh "bb" in
  destruct (ablk_bigM lo hi P) as (b & L).

Ltac blia_fast :=
  olin_all;
  unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *;
  try (unfold ablk, oclr, sclr, iclr; unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG);
  lia.
Ltac blia_dnf := unfold ablk, oclr, sclr, iclr, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *; lia.
Ltac blia ::= first [ solve [blia_fast] | blia_dnf ].

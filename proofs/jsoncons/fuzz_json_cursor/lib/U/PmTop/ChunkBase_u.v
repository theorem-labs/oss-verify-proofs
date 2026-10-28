(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CB.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Section Xfer.
Variable K : Z -> Prop.
Variables M M' : mem.
Hypothesis AG : TK.samem K M M'.
Hypothesis MG : mem_grows M M'.

Lemma isrc_at_setg : forall IS rep g g' rd, 0 <= IS < 2 ^ 60 ->
  TK2.cov K IS 40 -> TK2.cov K (IS + 48) 224 -> TK2.str_cov K (IS + 80) rep ->
  PML.u64 M' (IS + 40) g' -> PML.srep_data (IS + 80) rep <= g' <= PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) ->
  PML.isrc_at M IS rep g rd -> PML.isrc_at M' IS rep g' rd.
Proof.
  intros IS rep g g' rd HIS HK1 HK2 HS G' Hg' H. unfold PML.isrc_at in *. cbv zeta in *.
  destruct H as (A0 & A16 & A24 & A32 & A40 & A48 & Ag & A56 & A64 & A72 & As & A104 & A112 & A120 & Aio & Ard & Adef).
  assert (X1 : forall off v, 0 <= off -> off + 8 <= 40 -> PML.u64 M (IS + off) v -> PML.u64 M' (IS + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK1 | lia | lia] | exact H]. }
  assert (X2 : forall off v, 48 <= off -> off + 8 <= 272 -> PML.u64 M (IS + off) v -> PML.u64 M' (IS + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK2 | lia | lia] | exact H]. }
  split; [replace IS with (IS + 0) by lia; apply X1; [lia | lia | replace (IS + 0) with IS by lia; exact A0]|].
  split; [apply X1; [lia | lia | exact A16]|]. split; [apply X1; [lia | lia | exact A24]|]. split; [apply X1; [lia | lia | exact A32]|].
  split; [exact G'|]. split; [apply X2; [lia | lia | exact A48]|]. split; [exact Hg'|].
  split; [apply X2; [lia | lia | exact A56]|]. split; [apply X2; [lia | lia | exact A64]|]. split; [apply X2; [lia | lia | exact A72]|].
  split; [apply (TK2.str_at_x K M M' AG); [lia | exact HS | exact As]|].
  split; [apply X2; [lia | lia | exact A104]|].
  split; [apply (TK2.u32_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK2 | lia | lia] | exact A112]|].
  split; [apply X2; [lia | lia | exact A120]|].
  split; [apply (TK2.iosb_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK2 | lia | lia] | exact Aio]|].
  split; [exact Ard|]. exact (L5.defined_grows _ _ _ _ MG Adef).
Qed.

Lemma isrc_at_setrd : forall IS rep g rd rd', 0 <= IS < 2 ^ 60 ->
  TK2.cov K IS 152 -> TK2.cov K (IS + 156) 116 -> TK2.str_cov K (IS + 80) rep ->
  PML.u32 M' (IS + 152) rd' -> (rd' = 0 \/ rd' = 2) ->
  PML.isrc_at M IS rep g rd -> PML.isrc_at M' IS rep g rd'.
Proof.
  intros IS rep g rd rd' HIS HK1 HK2 HS G' Hrd' H. unfold PML.isrc_at in *. cbv zeta in *.
  destruct H as (A0 & A16 & A24 & A32 & A40 & A48 & Ag & A56 & A64 & A72 & As & A104 & A112 & A120 & Aio & Ard & Adef).
  assert (X1 : forall off v, 0 <= off -> off + 8 <= 152 -> PML.u64 M (IS + off) v -> PML.u64 M' (IS + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK1 | lia | lia] | exact H]. }
  assert (X2 : forall off v, 156 <= off -> off + 8 <= 272 -> PML.u64 M (IS + off) v -> PML.u64 M' (IS + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK2 | lia | lia] | exact H]. }
  split; [replace IS with (IS + 0) by lia; apply X1; [lia | lia | replace (IS + 0) with IS by lia; exact A0]|].
  split; [apply X1; [lia | lia | exact A16]|]. split; [apply X1; [lia | lia | exact A24]|]. split; [apply X1; [lia | lia | exact A32]|].
  split; [apply X1; [lia | lia | exact A40]|]. split; [apply X1; [lia | lia | exact A48]|]. split; [exact Ag|].
  split; [apply X1; [lia | lia | exact A56]|]. split; [apply X1; [lia | lia | exact A64]|]. split; [apply X1; [lia | lia | exact A72]|].
  split; [apply (TK2.str_at_x K M M' AG); [lia | exact HS | exact As]|].
  split; [apply X1; [lia | lia | exact A104]|].
  split; [apply (TK2.u32_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK1 | lia | lia] | exact A112]|].
  split; [apply X1; [lia | lia | exact A120]|].
  split; [|split; [exact Hrd' | exact (L5.defined_grows _ _ _ _ MG Adef)]].
  destruct Aio as (H32 & H36 & H40 & H48 & Hk & Hd).
  split; [replace (IS + 120 + 32) with (IS + 152) by lia; exact G'|].
  split; [apply (TK2.u32_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK2 | lia | lia] | exact H36]|].
  split; [replace (IS + 120 + 40) with (IS + 160) in * by lia; apply X2; [lia | lia | exact H40]|].
  split; [replace (IS + 120 + 48) with (IS + 168) in * by lia; apply X2; [lia | lia | exact H48]|].
  split; [intros k Hk0; specialize (Hk k Hk0); replace (IS + 120 + 56 + 8 * k) with (IS + (176 + 8 * k)) in * by lia; apply X2; [lia | lia | exact Hk]|].
  exact (L5.defined_grows _ _ _ _ MG Hd).
Qed.

Lemma rdr_at_upd : forall Rr IS V ch bof bof' de', 0 <= Rr < 2 ^ 59 ->
  TK2.cov K Rr 256 -> TK2.cov K (Rr + 264) 16 -> TK2.cov K (Rr + 297) 23 ->
  PML.u64 M' (Rr + 280) de' -> ch <= de' <= ch + 16384 -> PML.u64 M' (Rr + 288) 0 -> PML.u8 M' (Rr + 296) (PML.b2z bof') ->
  TPS.rdr_at M Rr IS V ch bof -> TPS.rdr_at M' Rr IS V ch bof'.
Proof.
  intros Rr IS V ch bof bof' de' HR HK1 HK2 HK3 C280 Hde C288 C296 (A240 & A248 & A264 & A272 & _ & _ & _ & A304 & A312 & (st0 & Aio) & A32 & Adef).
  assert (X1 : forall off v, 0 <= off -> off + 8 <= 256 -> PML.u64 M (Rr + off) v -> PML.u64 M' (Rr + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK1 | lia | lia] | exact H]. }
  assert (X2 : forall off v, 264 <= off -> off + 8 <= 280 -> PML.u64 M (Rr + off) v -> PML.u64 M' (Rr + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK2 | lia | lia] | exact H]. }
  assert (X3 : forall off v, 297 <= off -> off + 8 <= 320 -> PML.u64 M (Rr + off) v -> PML.u64 M' (Rr + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK3 | lia | lia] | exact H]. }
  unfold TPS.rdr_at.
  split; [apply X1; [lia | lia | exact A240]|]. split; [apply X1; [lia | lia | exact A248]|]. split; [apply X2; [lia | lia | exact A264]|]. split; [apply X2; [lia | lia | exact A272]|].
  split; [exists de'; split; [exact C280 | exact Hde]|]. split; [exact C288|]. split; [exact C296|].
  split; [apply X3; [lia | lia | exact A304]|]. split; [apply X3; [lia | lia | exact A312]|].
  split; [exists st0; apply (TK2.iosb_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK1 | lia | lia] | exact Aio]|].
  split; [apply X1; [lia | lia | exact A32]|]. exact (L5.defined_grows _ _ _ _ MG Adef).
Qed.
End Xfer.
End CB.

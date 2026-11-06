(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition nw_range (lo hi : Z) : Prop :=
  forall a, lo <= a < hi ->
    match find_segment segs a 1 with Some sg => seg_writable sg = false | None => True end.

#[using="Type"] Lemma wview_none_in_nw_pristine : forall m lo hi a,
  nw_range lo hi -> pristine m lo hi -> lo <= a < hi -> wview segs m (wa a) = None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi a NW (Hlo & Hhi & P) Ha.
  unfold wview. rewrite (P a Ha). rewrite wa_unsigned by lia.
  specialize (NW a Ha). destruct (find_segment segs a 1) as [sg|]; [rewrite NW|]; reflexivity.
Qed.

#[using="Type"] Lemma wr_at_outside_pristine : forall m lo hi A n,
  nw_range lo hi -> pristine m lo hi -> lo < hi ->
  wr_at segs m A n -> 0 < n ->
  A + n <= lo \/ hi <= A.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi A n NW PR Hlh (HA & HAn & W) Hn.
  assert (K : forall a, A <= a < A + n -> ~ (lo <= a < hi)).
  { intros a Ha Hin. apply (W (a - A) ltac:(lia)). replace (A + (a - A)) with a by lia.
    eapply wview_none_in_nw_pristine; eassumption. }
  destruct (Z.lt_ge_cases A lo).
  - left. destruct (Z.le_gt_cases (A + n) lo); [assumption|]. exfalso. apply (K lo); lia.
  - right. destruct (Z.lt_ge_cases A hi); [|assumption]. exfalso. apply (K A); lia.
Qed.

#[using="Type"] Lemma stk_outside_pristine : forall m lo hi slo shi,
  nw_range lo hi -> pristine m lo hi -> lo < hi ->
  stk segs m slo shi -> slo < shi ->
  shi <= lo \/ hi <= slo.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi slo shi NW PR Hlh (H1 & H2 & S) Hs.
  assert (K : forall a, slo <= a < shi -> ~ (lo <= a < hi)).
  { intros a Ha Hin. apply (proj1 (S a Ha)). eapply wview_none_in_nw_pristine; eassumption. }
  destruct (Z.lt_ge_cases slo lo).
  - left. destruct (Z.le_gt_cases shi lo); [assumption|]. exfalso. apply (K lo); lia.
  - right. destruct (Z.lt_ge_cases slo hi); [|assumption]. exfalso. apply (K slo); lia.
Qed.

#[using="Type"] Lemma u64arr_outside_pristine : forall m lo hi A ws,
  nw_range lo hi -> pristine m lo hi -> lo < hi ->
  u64arr segs m A ws -> (0 < length ws)%nat ->
  A + 8 * Z.of_nat (length ws) <= lo \/ hi <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros m lo hi A ws NW PR Hlh [_ W] Hl. eapply wr_at_outside_pristine; try eassumption. lia. Qed.

#[using="Type"] Lemma u8arr_outside_pristine : forall m lo hi A bs,
  nw_range lo hi -> pristine m lo hi -> lo < hi ->
  u8arr segs m A bs -> (0 < length bs)%nat ->
  A + Z.of_nat (length bs) <= lo \/ hi <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros m lo hi A bs NW PR Hlh [_ W] Hl. eapply wr_at_outside_pristine; try eassumption. lia. Qed.

#[using="Type"] Lemma rw_cells_outside_pristine : forall m lo hi A cs,
  nw_range lo hi -> pristine m lo hi -> lo < hi ->
  rw_cells segs m A cs -> (0 < cells_size cs)%nat ->
  A + Z.of_nat (cells_size cs) <= lo \/ hi <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros m lo hi A cs NW PR Hlh [_ W] Hl. eapply wr_at_outside_pristine; try eassumption. lia. Qed.

End WithSegs.

(* [comment removed for export] *)

Lemma find_segment_cons : forall sg rest a n,
  find_segment (sg :: rest) a n =
  if Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))
  then Some sg else find_segment rest a n.
Proof. reflexivity. Qed.

Lemma nw_rodata_plain : nw_range Plain.M.loaded_segments 0x10000 0x22000.
Proof.
  unfold nw_range. intros a Ha.
  change Plain.M.loaded_segments with
    [Plain.Plain_segment_000; Plain.Plain_segment_001; Plain.Plain_segment_002; Plain.Plain_segment_003].
  rewrite find_segment_cons.
  change (Z.of_N (seg_base Plain.Plain_segment_000)) with 0x10000.
  change (Z.of_N (seg_size Plain.Plain_segment_000)) with 0x12000.
  replace (0x10000 <=? a) with true by (symmetry; apply Z.leb_le; lia).
  replace (a + 1 <=? 0x10000 + 0x12000) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma nw_rodata_ubsan : nw_range Ubsan.M.loaded_segments 0x10000 0x22000.
Proof.
  unfold nw_range. intros a Ha.
  change Ubsan.M.loaded_segments with
    [Ubsan.Ubsan_segment_000; Ubsan.Ubsan_segment_001;
     Ubsan.Ubsan_segment_002; Ubsan.Ubsan_segment_003].
  rewrite find_segment_cons.
  change (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000.
  change (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x12000.
  replace (0x10000 <=? a) with true by (symmetry; apply Z.leb_le; lia).
  replace (a + 1 <=? 0x10000 + 0x12000) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Section Plain.
Notation PSEGS := Plain.M.loaded_segments.
#[using="Type"] Lemma u64arr_outside_rodata_P : forall m A ws,
  pristine m 0x10000 0x22000 -> u64arr PSEGS m A ws -> (0 < length ws)%nat ->
  A + 8 * Z.of_nat (length ws) <= 0x10000 \/ 0x22000 <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply u64arr_outside_pristine; try eassumption; [apply nw_rodata_plain | lia]. Qed.
#[using="Type"] Lemma u8arr_outside_rodata_P : forall m A bs,
  pristine m 0x10000 0x22000 -> u8arr PSEGS m A bs -> (0 < length bs)%nat ->
  A + Z.of_nat (length bs) <= 0x10000 \/ 0x22000 <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply u8arr_outside_pristine; try eassumption; [apply nw_rodata_plain | lia]. Qed.
#[using="Type"] Lemma rw_cells_outside_rodata_P : forall m A cs,
  pristine m 0x10000 0x22000 -> rw_cells PSEGS m A cs -> (0 < cells_size cs)%nat ->
  A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x22000 <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply rw_cells_outside_pristine; try eassumption; [apply nw_rodata_plain | lia]. Qed.
#[using="Type"] Lemma stk_outside_rodata_P : forall m lo hi,
  pristine m 0x10000 0x22000 -> stk PSEGS m lo hi -> lo < hi ->
  hi <= 0x10000 \/ 0x22000 <= lo.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply stk_outside_pristine; try eassumption; [apply nw_rodata_plain | lia]. Qed.
End Plain.

Section Ubsan.
Notation USEGS := Ubsan.M.loaded_segments.
#[using="Type"] Lemma u64arr_outside_rodata_U : forall m A ws,
  pristine m 0x10000 0x22000 -> u64arr USEGS m A ws -> (0 < length ws)%nat ->
  A + 8 * Z.of_nat (length ws) <= 0x10000 \/ 0x22000 <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply u64arr_outside_pristine; try eassumption; [apply nw_rodata_ubsan | lia]. Qed.
#[using="Type"] Lemma u8arr_outside_rodata_U : forall m A bs,
  pristine m 0x10000 0x22000 -> u8arr USEGS m A bs -> (0 < length bs)%nat ->
  A + Z.of_nat (length bs) <= 0x10000 \/ 0x22000 <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply u8arr_outside_pristine; try eassumption; [apply nw_rodata_ubsan | lia]. Qed.
#[using="Type"] Lemma rw_cells_outside_rodata_U : forall m A cs,
  pristine m 0x10000 0x22000 -> rw_cells USEGS m A cs -> (0 < cells_size cs)%nat ->
  A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x22000 <= A.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply rw_cells_outside_pristine; try eassumption; [apply nw_rodata_ubsan | lia]. Qed.
#[using="Type"] Lemma stk_outside_rodata_U : forall m lo hi,
  pristine m 0x10000 0x22000 -> stk USEGS m lo hi -> lo < hi ->
  hi <= 0x10000 \/ 0x22000 <= lo.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply stk_outside_pristine; try eassumption; [apply nw_rodata_ubsan | lia]. Qed.
End Ubsan.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
(* [comment removed for export] *)
Definition URA : list Z := [0x82958; 0x82a50; 0x82a6c; 0x82a88; 0x82b38; 0x82e2c; 0x82f14; 0x8319c; 0x831c8; 0x83320; 0x8334c; 0x83450; 0x8347c; 0x835c8; 0x835f4; 0x836ec; 0x83718; 0x838f4; 0x83aa8; 0x83ad0; 0x83c70; 0x83ca0; 0x83dac; 0x83ddc; 0x83ec4; 0x83ee8; 0x840ec; 0x84120; 0x841ec; 0x84210; 0x843a4; 0x843d0; 0x84544; 0x84570; 0x84610; 0x8463c; 0x84738; 0x84764; 0x84938; 0x84964; 0x84a7c; 0x84aa8; 0x84bac; 0x84bd8; 0x84cd4; 0x84d00; 0x84e58; 0x84e84; 0x85248; 0x85270; 0x85484; 0x854b4; 0x85564; 0x85594; 0x857d0; 0x857f4; 0x85ea8; 0x85ecc; 0x86160; 0x86ff8; 0x8710c; 0x87318; 0x873fc; 0x87dcc; 0x87ed8; 0x87fd4; 0x880a0; 0x88454; 0x88478; 0x8848c; 0x884b0; 0x884cc; 0x888d4; 0x88954; 0x889c0; 0x88a30; 0x88ad4; 0x88b44; 0x88bc0; 0x88be4; 0x88bf8; 0x88c84; 0x88c9c; 0x88cac; 0x88ec8; 0x89284; 0x892a8; 0x892dc; 0x893d0; 0x893f4; 0x89408; 0x89424; 0x895c0; 0x8b9c4; 0x8bb88].
Section UA.
Variable segs : list Segment.

Inductive uanchor (m : mem) : Z -> word -> word -> Prop :=
| ua_stop : forall SP (ra s0 : word),
    bv_unsigned s0 < alloc_ceiling \/ bv_unsigned s0 <= SP \/ bv_unsigned s0 mod 8 <> 0 ->
    uanchor m SP ra s0
| ua_step : forall SP (ra s0 ra' s0' : word),
    SP + 16 <= bv_unsigned s0 -> bv_unsigned s0 < 2^47 ->
    rw_cells segs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] ->
    uanchor m (bv_unsigned s0) ra' s0' ->
    uanchor m SP ra s0.

Lemma uanchor_triv : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> uanchor m SP ra s0.
Proof. aceil. intros m SP ra s0 H _. apply ua_stop. left; exact H. Qed.

Lemma uanchor_step : forall m SP ra s0 ra' s0',
  In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
  rw_cells segs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> uanchor m (bv_unsigned s0) ra' s0' -> uanchor m SP ra s0.
Proof. aceil. intros m SP ra s0 ra' s0' _ [H1 H2] RC U. eapply ua_step; eauto. Qed.

Lemma rw_cells_agree : forall m m' A cs,
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> m' (wa x) = m (wa x)) ->
  rw_cells segs m A cs -> rw_cells segs m' A cs.
Proof. aceil.
  intros m m' A cs AG [[WF (B0 & B1 & BR)] (W0 & W1 & WR)]. rewrite cells_bytes_length in B1, BR by exact WF.
  split; [split; [exact WF| split; [exact B0| split; [rewrite cells_bytes_length by exact WF; exact B1|]]]|].
  - rewrite cells_bytes_length by exact WF. intros i Hi. rewrite <- (BR i Hi). unfold mrd. rewrite AG by lia. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. specialize (WR i Hi). unfold wview in *. rewrite AG by lia. exact WR.
Qed.

Lemma uanchor_frame : forall m m' SP ra s0,
  (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> uanchor m SP ra s0 -> uanchor m' SP ra s0.
Proof. aceil.
  intros m m' SP ra s0 AG U. induction U as [SP ra s0 H| SP ra s0 ra' s0' H1 H2 RC U IH].
  - apply ua_stop. exact H.
  - eapply ua_step; [exact H1| exact H2| | apply IH; intros a Ha; apply AG; lia].
    eapply rw_cells_agree; [| exact RC]. cbn. intros x Hx. apply AG. lia.
Qed.
End UA.
End RC__1.

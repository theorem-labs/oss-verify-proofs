(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Definition URA : list Z := [0x108540; 0x108564; 0x108588; 0x1086c4; 0x108820; 0x108858; 0x108874; 0x108a24; 0x108a38; 0x108a40; 0x108fe8; 0x109078; 0x1090b4; 0x1090d4; 0x1090e8; 0x109140; 0x1092b4; 0x10932c; 0x109340; 0x8271c; 0x827fc; 0x82818; 0x82834; 0x828d8; 0x1097c0; 0x1097dc; 0x1097f8; 0x10982c; 0x82b94; 0x82c70; 0x82e2c; 0x82e58; 0x82e70; 0x82f68; 0x82f94; 0x82fac; 0x83054; 0x83080; 0x83098; 0x83188; 0x831b4; 0x831cc; 0x83268; 0x83294; 0x832ac; 0x83430; 0x835dc; 0x83600; 0x83618; 0x83760; 0x83790; 0x837a8; 0x83858; 0x83888; 0x838a0; 0x83944; 0x83968; 0x83980; 0x83b14; 0x83b48; 0x83b64; 0x83be4; 0x83c08; 0x83c20; 0x83d58; 0x83d84; 0x83d9c; 0x83ea0; 0x83ecc; 0x83ee4; 0x83f40; 0x83f6c; 0x83f84; 0x84024; 0x84050; 0x84068; 0x841dc; 0x84208; 0x84220; 0x842dc; 0x84308; 0x84320; 0x843c4; 0x843f0; 0x84408; 0x844a8; 0x844d4; 0x844ec; 0x845d8; 0x84604; 0x8461c; 0x84994; 0x849b8; 0x849d0; 0x84b84; 0x84bb4; 0x84bcc; 0x84c3c; 0x84c6c; 0x84c84; 0x84ea4; 0x84ed4; 0x84eec; 0x84f5c; 0x84f80; 0x84f98; 0x85224; 0x85248; 0x85260; 0x85524; 0x85574; 0x85598; 0x855d8; 0x85600; 0x864e0; 0x865d4; 0x867b8; 0x86898; 0x86980; 0x869fc; 0x86a8c; 0x872c0; 0x873a8; 0x8747c; 0x874f4; 0x87544; 0x875bc; 0x8760c; 0x87770; 0x8787c; 0x878a0; 0x878b4; 0x878d4; 0x878f0; 0x87964; 0x87c40; 0x87cb4; 0x87d14; 0x87d78; 0x87e04; 0x87e68; 0x87ee0; 0x87f04; 0x87f18; 0x87f88; 0x87fa0; 0x87fb0; 0x88078; 0x88178; 0x8849c; 0x884c0; 0x884d4; 0x884f0; 0x885d8; 0x885fc; 0x88610; 0x8862c; 0x88734; 0x888fc; 0x889c0; 0x8a974; 0x8ab44; 0x8ac48; 0x8acbc].

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

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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_REAL_STRLEN   : Z := 0xa66c8.  Definition A_MUSL_STRLEN   : Z := 0x9e32c.
Definition A_REAL_READ     : Z := 0xa66f8.  Definition A_MUSL_READ     : Z := 0xa33e0.
Definition A_REAL_FWRITE   : Z := 0xa6700.  Definition A_MUSL_FWRITE   : Z := 0x97d80.
Definition A_REAL_VPRINTF  : Z := 0xa6718.  Definition A_MUSL_VPRINTF  : Z := 0x9d588.
Definition A_REAL_VFPRINTF : Z := 0xa6720.  Definition A_MUSL_VFPRINTF : Z := 0x98008.
Definition A_REAL_STRNLEN  : Z := 0xa67d0.  Definition A_MUSL_STRNLEN  : Z := 0x9e568.
Definition A_REAL_MEMCHR   : Z := 0xa66e8.  Definition A_MUSL_MEMCHR   : Z := 0x9dbe0.
Definition A_GOT_CFLAGS    : Z := 0xa49a0.  Definition A_CFLAGS        : Z := 0x13f6a8.
Definition A_CF_INTERCEPT_STRLEN : Z := 0x13f7a3.   (* [comment removed for export] *)
Definition A_CF_CHECK_PRINTF : Z := 0x13f6fc.      (* [comment removed for export] *)

Section Globals.
Variable segs : list MemImageType.Segment.

Definition icp_globals2 (m : mem) : Prop :=
     rw_cells segs m A_REAL_STRLEN [C8 (Z_to_bv 64 A_MUSL_STRLEN)]
  /\ rw_cells segs m A_REAL_READ [C8 (Z_to_bv 64 A_MUSL_READ)]
  /\ rw_cells segs m A_REAL_FWRITE [C8 (Z_to_bv 64 A_MUSL_FWRITE)]
  /\ rw_cells segs m A_REAL_VPRINTF [C8 (Z_to_bv 64 A_MUSL_VPRINTF)]
  /\ rw_cells segs m A_REAL_VFPRINTF [C8 (Z_to_bv 64 A_MUSL_VFPRINTF)]
  /\ rw_cells segs m A_REAL_STRNLEN [C8 (Z_to_bv 64 A_MUSL_STRNLEN)]
  /\ rw_cells segs m A_REAL_MEMCHR [C8 (Z_to_bv 64 A_MUSL_MEMCHR)]
  /\ rw_cells segs m A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)]
  /\ rw_cells segs m A_CF_INTERCEPT_STRLEN [C1 (Z_to_bv 8 1)]
  /\ rw_cells segs m A_CF_CHECK_PRINTF [C1 (Z_to_bv 8 1)]
  /\ True.

Lemma ig2_strlen : forall m, icp_globals2 m -> rw_cells segs m 0xa66c8 [C8 (Z_to_bv 64 0x9e32c)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_read : forall m, icp_globals2 m -> rw_cells segs m 0xa66f8 [C8 (Z_to_bv 64 0xa33e0)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_fwrite : forall m, icp_globals2 m -> rw_cells segs m 0xa6700 [C8 (Z_to_bv 64 0x97d80)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_vprintf : forall m, icp_globals2 m -> rw_cells segs m 0xa6718 [C8 (Z_to_bv 64 0x9d588)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_vfprintf : forall m, icp_globals2 m -> rw_cells segs m 0xa6720 [C8 (Z_to_bv 64 0x98008)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_strnlen : forall m, icp_globals2 m -> rw_cells segs m 0xa67d0 [C8 (Z_to_bv 64 0x9e568)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_memchr : forall m, icp_globals2 m -> rw_cells segs m 0xa66e8 [C8 (Z_to_bv 64 0x9dbe0)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_cflags : forall m, icp_globals2 m -> rw_cells segs m 0xa49a0 [C8 (Z_to_bv 64 0x13f6a8)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_intercept_strlen : forall m, icp_globals2 m -> rw_cells segs m 0x13f7a3 [C1 (Z_to_bv 8 1)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.
Lemma ig2_check_printf : forall m, icp_globals2 m -> rw_cells segs m 0x13f6fc [C1 (Z_to_bv 8 1)].
Proof. intros m H. unfold icp_globals2 in H. tauto. Qed.

Lemma icp_globals2_transport : forall W m m',
  icp_globals2 m -> munch W m m' -> wmono segs m m' ->
  disjoint_from W 0xa4000 (0xa6f40 - 0xa4000) -> disjoint_from W 0x13ee00 (0x13fdd0 - 0x13ee00) ->
  icp_globals2 m'.
Proof.
  intros W m m' G MU WM D1 D2.
  unfold icp_globals2, A_REAL_STRLEN, A_REAL_READ, A_REAL_FWRITE, A_REAL_VPRINTF, A_REAL_VFPRINTF, A_REAL_STRNLEN,
    A_REAL_MEMCHR, A_GOT_CFLAGS, A_CF_INTERCEPT_STRLEN, A_CF_CHECK_PRINTF in *.
  assert (DD1 : forall A k, 0xa4000 <= A -> A + Z.of_nat k <= 0xa6f40 -> disjoint_from W A (Z.of_nat k)).
  { intros A k H1 H2. eapply disjoint_from_sub; [exact D1| lia | lia]. }
  assert (DD2 : forall A k, 0x13ee00 <= A -> A + Z.of_nat k <= 0x13fdd0 -> disjoint_from W A (Z.of_nat k)).
  { intros A k H1 H2. eapply disjoint_from_sub; [exact D2| lia | lia]. }
  decompose [and] G.
  repeat match goal with
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | first [apply DD1; cbn; lia | apply DD2; cbn; lia] ]
  end.
  repeat (split; [assumption|]). exact I.
Qed.
End Globals.
End RC__1.

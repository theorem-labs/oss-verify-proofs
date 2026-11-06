(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BI_globals2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition icp_globals_cells : list (Z * Z) :=
  [(0xa55a0, 8); (0xae5b8, 8); (0xa6108, 8); (0xaf299, 1); (0xa7400, 8); (0xa7408, 8); (0xa55a8, 8); (0xaf2a8, 8);
   (0xa55b0, 8); (0xaf2b0, 8); (0xa55b8, 8); (0xaf2a0, 8); (0xaf298, 1)]%Z.
Definition icp_globals2_cells : list (Z * Z) :=
  [(0xa72a8, 8); (0xa72d8, 8); (0xa72e0, 8); (0xa72f8, 8); (0xa7300, 8); (0xa73b0, 8); (0xa72c8, 8); (0xa5590, 8); (0x1401e3, 1); (0x14013c, 1)]%Z.

Lemma icp_globals_transport_cells : forall W m m' SB,
  icp_globals bsegs m SB -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun c => disjoint_from W (fst c) (snd c)) icp_globals_cells -> icp_globals bsegs m' SB.
Proof.
  intros W m m' SB G MU WM D. unfold icp_globals_cells in D.
  repeat match type of D with Forall _ (_ :: _) => apply Forall_cons_iff in D; destruct D as [? D] end. cbn [fst snd] in *.
  unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
    A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED in *.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & SBR).
  repeat match goal with
  | |- rw_cells bsegs m' ?A2 ?cs2 /\ _ => split
  | |- rw_cells bsegs m' ?A2 ?cs2 =>
      eapply (rw_cells_transport bsegs W m m' A2 cs2); [ eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add]; assumption ]
  end.
  exact SBR.
Qed.

Lemma icp_globals2_transport_cells : forall W m m',
  icp_globals2 bsegs m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun c => disjoint_from W (fst c) (snd c)) icp_globals2_cells -> icp_globals2 bsegs m'.
Proof.
  intros W m m' G MU WM D. unfold icp_globals2_cells in D.
  repeat match type of D with Forall _ (_ :: _) => apply Forall_cons_iff in D; destruct D as [? D] end. cbn [fst snd] in *.
  unfold icp_globals2, A_REAL_STRLEN, A_REAL_READ, A_REAL_FWRITE, A_REAL_VPRINTF, A_REAL_VFPRINTF, A_REAL_STRNLEN, A_REAL_MEMCHR,
    A_GOT_CFLAGS, A_CF_INTERCEPT_STRLEN, A_CF_CHECK_PRINTF in *.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & _).
  repeat match goal with
  | |- rw_cells bsegs m' ?A2 ?cs2 /\ _ => split
  | |- rw_cells bsegs m' ?A2 ?cs2 =>
      eapply (rw_cells_transport bsegs W m m' A2 cs2); [ eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add]; assumption ]
  | |- True => exact I
  end.
Qed.

End RC__1.
Ltac cells_disjoint := repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; repeat split; lia|]); apply Forall_nil.

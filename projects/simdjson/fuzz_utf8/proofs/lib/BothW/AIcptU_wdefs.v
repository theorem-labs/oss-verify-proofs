(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Cells Frame InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells StdioFiles AExitU_wr AIcptU_hmap AIcptU_defs.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition XSH_HI : Z := 0x10007fff8000.        (* [comment removed for export] *)
Definition MBST_SH : Z := 0x800cdb78.           (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition XSLO : Z := ATOP + 4096.
Definition XSHI : Z := ATOP + 8388608.

Definition icpt_wcr (m : mem) : Prop :=
     rw_cells bsegs m 0x172090 [C8 (Z_to_bv 64 0x1760d4)]
  /\ rw_cells bsegs m 0x1760d4 [C4 (Z_to_bv 64 8)]
  /\ rw_cells bsegs m 0x171ff8 [C8 (Z_to_bv 64 0x17b078)]
  /\ rw_cells bsegs m 0x17b078 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0x172020 [C8 (Z_to_bv 64 0x174058)]
  /\ rw_cells bsegs m MBST_SH [C8 (Z_to_bv 64 0)]
  /\ shadow_bytes m (shad ATOP) XSH_HI (fun _ => 0).

Definition icptW (T : Z) (m : mem) : Prop := icptU T m /\ icpt_wcr m.
Definition icptW_rng (T : Z) (RNG : footprint) : Prop :=
  icptU_rng T RNG /\ rng RNG MBST_SH 8 /\ rng RNG (shad ATOP) (XSH_HI - shad ATOP).

(* [comment removed for export] *)
Lemma icpt_wcr_frame_exit : forall W m m', icpt_wcr m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> icpt_wcr m'.
Proof.
  intros W m m' (G1 & SZ & G2 & SB & G3 & MB & XS) MU WM HW.
  pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
  assert (X : forall A n, (A + n <= 0x176c10 \/ (0x176ed8 <= A /\ A + n <= 0x177a10) \/ (0x177a11 <= A /\ A + n <= 0x6afad8) \/ (0x6cfd80 <= A /\ A + n <= ATOP)) ->
                disjoint_from W A n).
  { intros A n HD. clear - HW HD. induction HW as [|[l h] W H1 HW IH]; cbn; [exact I|]. split; [| exact IH].
    unfold exit_wr_ok in H1. cbn [fst snd] in H1. lia. }
  unfold icpt_wcr, MBST_SH in *.
  repeat match goal with |- _ /\ _ => split end.
  1-6: (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply X; cbn [cells_size csize Nat.add]; lia]).
  eapply shadow_bytes_munch; [exact XS | exact MU |]. apply X. rewrite shad_div. unfold AsanEmbed.ASHOFF, XSH_HI. Z.div_mod_to_equations. lia.
Qed.

Lemma icptW_frame_exit : forall T W m m', icptW T m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> icptW T m'.
Proof.
  intros T W m m' [A B] MU WM HW. split; [exact (icptU_frame_exit T W m m' A MU WM HW) | exact (icpt_wcr_frame_exit W m m' B MU WM HW)].
Qed.

Lemma icptW_rng_mono : forall T RNG RNG', fp_le RNG RNG' -> icptW_rng T RNG -> icptW_rng T RNG'.
Proof.
  intros T RNG RNG' LE (A & B & C). split; [exact (icptU_rng_mono T _ _ LE A)|]. split; (eapply rng_fp_le; [exact LE|]; assumption).
Qed.
End CANSEC1.

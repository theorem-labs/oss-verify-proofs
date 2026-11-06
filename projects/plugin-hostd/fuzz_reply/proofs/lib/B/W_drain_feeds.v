(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the FEEDS composition of the image-B (fuzz_reply.asan-ubsan) walk of
   fuzz_reply's drain: reference_feed's byte loop, from its head DRB (0x836fc) after k of the n = dnum s1 bytes
   to the loop's exit DE (0x838a0).  The statement is lib/B/W_drain_cx.v's dr_feeds_stmt; it takes the one-byte
   segment STATEMENT dr_feed_stmt as its premise, so this file walks no instruction: it chains
     DRB k -(feed)-> DRB (S k)  or  DE
   by induction on the measure dnum s1 - k, which DRB's own `Z.of_nat k < dnum s1` (the do-while: the test
   `bnez s5` is at the loop's bottom 0x83844) keeps positive at every head.  Image-independent: it reads no pc,
   register or frame slot.  lib/A's dr_feeds (lib/A/W_drain_top.v on a working branch) is not proved yet, so
   this is a fresh proof over B's cut, not a port. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_drain_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.

Lemma DRB_klt : forall cx s1 D k W1 c1,
  DRB B MT MMAX RG cx s1 D k W1 c1 -> (Z.of_nat k < dnum s1)%Z.
Proof.
  intros cx s1 D k W1 c1 H. unfold DRB in H.
  repeat match goal with
         | H : ex _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.
  assumption.
Qed.

Theorem dr_feeds : dr_feeds_stmt B MT MMAX RG.
Proof.
  intros FEED cx s1 D k W1 c1 HB HR HE.
  assert (MAIN : forall n k' W c, (Z.to_nat (dnum s1) - k' <= n)%nat ->
            DRB B MT MMAX RG cx s1 D k' W c -> SRr SEGS W c (dPOST B MT RG cx)).
  { induction n as [|n IH]; intros k' W c N H; pose proof (DRB_klt cx s1 D k' W c H) as KL.
    - exfalso. lia.
    - apply (FEED cx s1 D k' W c HB H).
      + intros W2 c2 H2. apply (IH (S k') W2 c2); [lia | exact H2].
      + exact HE. }
  exact (MAIN _ k W1 c1 (le_n _) HR).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x, an internal work row, 2026-10-30): dr_feeds_x proves lib/B/W_drain_cx_x.v's
   dr_feeds_stmt_x, the same chain over that file's DRB_x / DE_x at the entry's ghost list Hp and budget kr:
     DRB_x k -(feed)-> DRB_x (S k)  or  DE_x
   by induction on dnum s1 - k, which DRB_x's own `Z.of_nat k < dnum s1` keeps positive at every head.  It reads no
   instruction and no Section hypothesis (lib/A/W_drain_feed.v's dr_feeds_p_x is the same induction).  Everything
   above is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the R twins of DRB_klt_x and dr_feeds_x at a world relation R that
   contains wle, over W_drain_cx_x.v's R carriers (DRB_xR, DE_xR, dPOST_xR, dr_feeds_stmt_xR). The strict lemmas
   below are these twins at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

Lemma DRB_klt_xR : forall cx Hp kr s1 D k W1 c1,
  DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D k W1 c1 -> (Z.of_nat k < dnum s1)%Z.
Proof.
  intros cx Hp kr s1 D k W1 c1 H. unfold DRB_xR in H.
  repeat match goal with
         | H : ex _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.
  assumption.
Qed.

Theorem dr_feeds_xR : dr_feeds_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
  intros FEED cx Hp kr s1 D k W1 c1 HB HR HE.
  assert (MAIN : forall n k' W c, (Z.to_nat (dnum s1) - k' <= n)%nat ->
            DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D k' W c ->
            YA0nH.SRrG SEGS R W c (dPOST_xR B PST ARx MT RP RG R cx Hp kr)).
  { induction n as [|n IH]; intros k' W c N H; pose proof (DRB_klt_xR cx Hp kr s1 D k' W c H) as KL.
    - exfalso. lia.
    - apply (FEED cx Hp kr s1 D k' W c HB H).
      + intros W2 c2 H2. apply (IH (S k') W2 c2); [lia | exact H2].
      + exact HE. }
  exact (MAIN _ k W1 c1 (le_n _) HR).
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R; the statements are the strict ones, checked by conversion). ---- *)
Lemma DRB_klt_x : forall cx Hp kr s1 D k W1 c1,
  DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D k W1 c1 -> (Z.of_nat k < dnum s1)%Z.
Proof. exact (DRB_klt_xR (@wle SEGS)). Qed.

(* W_drain_cx_x.v dr_feeds_stmt_x *)
Theorem dr_feeds_x : dr_feeds_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dr_feeds_xR (@wle SEGS)). Qed.

End cx.
End bx.
End ax.

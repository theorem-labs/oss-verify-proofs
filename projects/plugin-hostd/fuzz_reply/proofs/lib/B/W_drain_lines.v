(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the LINES composition of the image-B (fuzz_reply.asan-ubsan) walk of
   fuzz_reply's drain, the line loop of relay.c:205-216, ported from lib/A/W_drain_lines.v (W7, a working branch)
   onto lib/B/W_drain_cx.v's cut predicates: from any of the loop's three cut points (DLL 0x8399c, DLN 0x839d4,
   DLR 0x83e34) to the outer loop's head DI (0x833c0) of the next round.  The statement is W_drain_cx.v's
   dr_lines_stmt; it takes the four segment STATEMENTS (dr_linea_stmt, dr_gs_stmt, dr_next_stmt, dr_rest_stmt)
   as premises, so this file walks no instruction: it chains
     DLL p q -(linea)-> DLN (S q)  or  DGS p q -(gs)-> DLN (S q)
     DLN p   -(next)->  DLL p q (p <= q < |dW s1|)  or  DLR p
     DLR p   -(rest)->  DI of the next round
   by induction on the measure |dW s1| - p of DLN.  DLL's own `(p <= q < length (dW s1))%nat` bounds the line
   (on B both DROP and NEXT reach DLL through the one memchr at 0x83990; the bound is the cut's, not the site's).
   Image-independent: the abstract loop dr_lines_loop is A's verbatim, and the B proof reads only that bound. *)
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
(* DR_x: the generic statement dr_lines_stmt_x (W_drain_cx_x.v) and the room record (W_journal_x.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) and dr_spec_xR (W_contract_xR.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma dr_lines_loop {Wt Ct : Type} (n : nat) (P : Wt -> Ct -> Prop)
  (LL : nat -> nat -> Wt -> Ct -> Prop) (LN LR : nat -> Wt -> Ct -> Prop) :
  (forall p q W c, LL p q W c -> (p <= q < n)%nat) ->
  (forall p q W c, LL p q W c -> (forall W2 c2, LN (S q) W2 c2 -> P W2 c2) -> P W c) ->
  (forall p W c, LN p W c ->
     (forall q W2 c2, LL p q W2 c2 -> P W2 c2) -> (forall W2 c2, LR p W2 c2 -> P W2 c2) -> P W c) ->
  (forall p W c, LR p W c -> P W c) ->
  forall W c, ((exists p q, LL p q W c) \/ (exists p, LN p W c) \/ (exists p, LR p W c)) -> P W c.
Proof.
intros HR HLL HLN HLR.
assert (KN : forall k p W c, (n - p <= k)%nat -> LN p W c -> P W c).
{ induction k as [|k IH]; intros p W c Hk H; apply (HLN p W c H).
  - intros q W2 c2 H2. destruct (HR p q W2 c2 H2) as [Hpq Hqn]. exfalso. lia.
  - exact (HLR p).
  - intros q W2 c2 H2. destruct (HR p q W2 c2 H2) as [Hpq Hqn].
    apply (HLL p q W2 c2 H2). intros W3 c3 H3. apply (IH (S q) W3 c3); [lia | exact H3].
  - exact (HLR p). }
intros W c [(p & q & H) | [(p & H) | (p & H)]].
- apply (HLL p q W c H). intros W2 c2 H2. exact (KN _ (S q) W2 c2 (le_n _) H2).
- exact (KN _ p W c (le_n _) H).
- exact (HLR p W c H).
Qed.

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

Lemma DLL_line_bound : forall cx s1 D p q W1 c1,
  DLL B MT MMAX RG cx s1 D p q W1 c1 -> (p <= q < length (dW s1))%nat.
Proof.
  intros cx s1 D p q W1 c1 H. unfold DLL in H.
  repeat match goal with
         | H : ex _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.
  split; assumption.
Qed.

Theorem dr_lines : dr_lines_stmt B MT MMAX RG.
Proof.
intros LINEA GS NEXT REST cx s1 D W1 c1 HB HC HDI.
match goal with |- SRr ?SG _ _ ?Q =>
  refine (dr_lines_loop (length (dW s1)) (fun W c => SRr SG W c Q) _ _ _ _ _ _ _ W1 c1 HC) end; cbv beta.
- intros p q W c H. exact (DLL_line_bound cx s1 D p q W c H).
- intros p q W c H K. apply (LINEA cx s1 D p q W c HB H K).
  intros W2 c2 H2. exact (GS cx s1 D p q W2 c2 HB H2 K).
- intros p W c H K1 K2. exact (NEXT cx s1 D p W c HB H K1 K2).
- intros p W c H. exact (REST cx s1 D p W c HB H HDI).
Qed.

End c.

(* ---- DR_x: dr_lines over any ARx, W_drain_cx_x.v's dr_lines_stmt_x (the image-B twin of a Theorem Labs lane's
   lib/A/W_drain_lines.v dr_lines_x). The walk is dr_lines' above with the entry's ghost list Hp and budget kr
   threaded; DLL_x's own `(p <= q < length (dW s1))%nat` bounds the line, as DLL's does (DLL_line_bound_x). It reads no
   Section hypothesis, so its Section has the variables only. The AR theorem dr_lines is kept as it is. ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.




(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of every composition above, for the drain's
   R carriers (W_drain_cx_x.v Section wR).  Each twin is its strict text with ajournal / SRr at R: SRr SEGS -> SRrG SEGS R,
   each carrier X_x -> its twin X_xR (R last among its section variables), dr_spec_x -> dr_spec_xR (R after ARx), and
   each composition name L -> LR.  A composition walks no instruction, so its R proof is its strict script.  At
   R := wle each twin is its strict text by conversion. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

Lemma DLL_line_bound_xR : forall cx Hp kr s1 D p q W1 c1,
  DLL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 c1 -> (p <= q < length (dW s1))%nat.
Proof.
  intros cx Hp kr s1 D p q W1 c1 H. unfold DLL_xR in H.
  repeat match goal with
         | H : ex _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.
  split; assumption.
Qed.

Theorem dr_lines_xR : dr_lines_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros LINEA GS NEXT REST cx Hp kr s1 D W1 c1 HB HC HDI.
match goal with |- SRrG ?SG _ _ _ ?Q =>
  refine (dr_lines_loop (length (dW s1)) (fun W c => SRrG SG R W c Q) _ _ _ _ _ _ _ W1 c1 HC) end; cbv beta.
- intros p q W c H. exact (DLL_line_bound_xR cx Hp kr s1 D p q W c H).
- intros p q W c H K. apply (LINEA cx Hp kr s1 D p q W c HB H K).
  intros W2 c2 H2. exact (GS cx Hp kr s1 D p q W2 c2 HB H2 K).
- intros p W c H K1 K2. exact (NEXT cx Hp kr s1 D p W c HB H K1 K2).
- intros p W c H. exact (REST cx Hp kr s1 D p W c HB H HDI).
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Lemma DLL_line_bound_x : forall cx Hp kr s1 D p q W1 c1,
  DLL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W1 c1 -> (p <= q < length (dW s1))%nat.
Proof. eapply (DLL_line_bound_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Theorem dr_lines_x : dr_lines_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_lines_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the OUTER composition of the image-B (fuzz_reply.asan-ubsan) walk of
   fuzz_reply's drain, the outer loop of relay.c:173-223, ported from lib/A/W_drain_outer.v (a working branch,
   = a Theorem Labs lane's working branch f41c2c6ab05: DRB_rstart, dr_outer_core, dr_outer) onto
   lib/B/W_drain_cx.v's cut predicates.  From DI (0x833c0) in the round state s1 to drain's post, by induction on
   dneed s1 (lib/A/W_drain_model.v dneed_dclr / dneed_dnext): TOP leads to DI again only through its EINTR arm,
   which dr_top_stmt offers only when ds_eintr s1 = true (so dneed drops by dneed_dclr), to DEND (END closes it),
   or to DRB 0, whose RSTART gives dneed_dnext's premises for the next round.  The statement is W_drain_cx.v's
   dr_outer_stmt; it takes TOP and DROP as segment statements and FEEDS, LINES and END as their conclusions, and
   walks no instruction.  Image-independent: the B proof reads only RSTART out of DRB. *)
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
(* DR_x: the generic statements (W_drain_cx_x.v) and the room record (W_journal_x.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) and dr_spec_xR (W_contract_xR.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
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

Lemma DRB_rstart : forall cx s1 D k W1 c1,
  DRB B MT MMAX RG cx s1 D k W1 c1 -> RSTART cx s1 D.
Proof.
  intros cx s1 D k W1 c1 H. unfold DRB in H.
  repeat match goal with
         | H : ex _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.
  assumption.
Qed.

Lemma dr_outer_core :
dr_top_stmt B MT MMAX RG ->
(forall cx s1 D W1 c1,
   DBASE B MT MMAX RG cx -> DRB B MT MMAX RG cx s1 D 0 W1 c1 ->
   (forall W2 c2, DE B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
   SRr SEGS W1 c1 (dPOST B MT RG cx)) ->
dr_drop_stmt B MT MMAX RG ->
(forall cx s1 D W1 c1,
   DBASE B MT MMAX RG cx ->
   ((exists q, DLL B MT MMAX RG cx s1 D 0 q W1 c1) \/ DLR B MT MMAX RG cx s1 D 0 W1 c1) ->
   (forall W2 c2, DI B MT MMAX RG cx (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 ->
      SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
   SRr SEGS W1 c1 (dPOST B MT RG cx)) ->
(forall cx s1 D W1 c1,
   DBASE B MT MMAX RG cx -> DEND B MT MMAX RG cx s1 D W1 c1 -> SRr SEGS W1 c1 (dPOST B MT RG cx)) ->
forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
  intros TOP FEEDS DROP LINES END.
  assert (MAIN : forall n cx s1 D W1 c1, (dneed s1 <= n)%nat ->
            DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 -> SRr SEGS W1 c1 (dPOST B MT RG cx)).
  { induction n as [|n IH]; intros cx s1 D W1 c1 N HB HI; [unfold dneed in N; lia|].
    apply (TOP cx s1 D W1 c1 HB HI).
    - intros EI W2 c2 H2. apply (IH cx (dclr (dgrow s1)) D W2 c2); [|exact HB|exact H2].
      assert (EI' : drain_b_c.ds_eintr (dgrow s1) = true) by exact EI.
      pose proof (dneed_dclr (dgrow s1) EI') as E. change (dneed (dgrow s1)) with (dneed s1) in E. lia.
    - intros W2 c2 H2. exact (END cx (dgrow s1) D W2 c2 HB H2).
    - intros W2 c2 H2.
      destruct (DRB_rstart cx (dgrow s1) D 0 W2 c2 H2) as (_ & _ & GR & WF & ST & EI & NE).
      destruct (dneed_dnext (dlive cx) (dxmx cx) (dgrow s1) GR NE WF ST EI) as [E _].
      change (dneed (dgrow s1)) with (dneed s1) in E.
      assert (NXT : forall W5 c5,
                 DI B MT MMAX RG cx (dnext (dlive cx) (dxmx cx) (dgrow s1)) (D ++ ddata (dgrow s1)) W5 c5 ->
                 SRr SEGS W5 c5 (dPOST B MT RG cx)).
      { intros W5 c5 H5. apply (IH cx (dnext (dlive cx) (dxmx cx) (dgrow s1)) (D ++ ddata (dgrow s1)) W5 c5);
          [lia|exact HB|exact H5]. }
      apply (FEEDS cx (dgrow s1) D W2 c2 HB H2). intros W3 c3 H3.
      apply (DROP cx (dgrow s1) D W3 c3 HB H3).
      + intros q W4 c4 H4. exact (LINES cx (dgrow s1) D W4 c4 HB (or_introl (ex_intro _ q H4)) NXT).
      + intros W4 c4 H4. exact (LINES cx (dgrow s1) D W4 c4 HB (or_intror H4) NXT). }
  intros cx s1 D W1 c1 HB HI. exact (MAIN (dneed s1) cx s1 D W1 c1 (le_n _) HB HI).
Qed.

Theorem dr_outer : dr_outer_stmt B MT MMAX RG.
Proof.
  intros TOP FEEDS DROP LINES END cx s1 D W1 c1 HB HI.
  refine (dr_outer_core TOP _ DROP _ END cx s1 D W1 c1 HB HI).
  - intros cx' s' D' W' c' HB' H K. exact (FEEDS cx' s' D' 0%nat W' c' HB' H K).
  - intros cx' s' D' W' c' HB' [(q & H)|H] K.
    + exact (LINES cx' s' D' W' c' HB' (or_introl (ex_intro _ 0%nat (ex_intro _ q H))) K).
    + exact (LINES cx' s' D' W' c' HB' (or_intror (or_intror (ex_intro _ 0%nat H))) K).
Qed.

End c.

(* ---- DR_x: the outer loop over any ARx, W_drain_cx_x.v's dr_outer_stmt_x (the image-B twin of a Theorem Labs lane's
   lib/A/W_drain_outer.v DRB_rstart_x / dr_outer_core_x / dr_outer_x). The walk is dr_outer's above with the entry's
   ghost list Hp and budget kr threaded; it reads only RSTART out of DRB_x and no Section hypothesis, so its Section has
   the variables only. The AR theorems are kept as they are. ---- *)
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

Lemma DRB_rstart_xR : forall cx Hp kr s1 D k W1 c1,
  DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D k W1 c1 -> RSTART cx s1 D.
Proof.
  intros cx Hp kr s1 D k W1 c1 H. unfold DRB_xR in H.
  repeat match goal with
         | H : ex _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.
  assumption.
Qed.

Lemma dr_outer_core_xR :
dr_top_stmt_xR B PST ARx MT RP MMAX RG R ->
(forall cx Hp kr s1 D W1 c1,
   DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D 0 W1 c1 ->
   (forall W2 c2, DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 ->
      SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
   SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
dr_drop_stmt_xR B PST ARx MT RP MMAX RG R ->
(forall cx Hp kr s1 D W1 c1,
   DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
   ((exists q, DLL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D 0 q W1 c1) \/
    DLR_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D 0 W1 c1) ->
   (forall W2 c2, DI_xR B PST ARx MT RP MMAX RG R cx Hp kr (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 ->
      SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
   SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall cx Hp kr s1 D W1 c1,
   DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DEND_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W1 c1 ->
   SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
forall cx Hp kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DI_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W1 c1 ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
  intros TOP FEEDS DROP LINES END.
  assert (MAIN : forall n cx Hp kr s1 D W1 c1, (dneed s1 <= n)%nat ->
            DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DI_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W1 c1 ->
            SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)).
  { induction n as [|n IH]; intros cx Hp kr s1 D W1 c1 N HB HI; [unfold dneed in N; lia|].
    apply (TOP cx Hp kr s1 D W1 c1 HB HI).
    - intros EI W2 c2 H2. apply (IH cx Hp kr (dclr (dgrow s1)) D W2 c2); [|exact HB|exact H2].
      assert (EI' : drain_b_c.ds_eintr (dgrow s1) = true) by exact EI.
      pose proof (dneed_dclr (dgrow s1) EI') as E. change (dneed (dgrow s1)) with (dneed s1) in E. lia.
    - intros W2 c2 H2. exact (END cx Hp kr (dgrow s1) D W2 c2 HB H2).
    - intros W2 c2 H2.
      destruct (DRB_rstart_xR cx Hp kr (dgrow s1) D 0 W2 c2 H2) as (_ & _ & GR & WF & ST & EI & NE).
      destruct (dneed_dnext (dlive cx) (dxmx cx) (dgrow s1) GR NE WF ST EI) as [E _].
      change (dneed (dgrow s1)) with (dneed s1) in E.
      assert (NXT : forall W5 c5,
                 DI_xR B PST ARx MT RP MMAX RG R cx Hp kr (dnext (dlive cx) (dxmx cx) (dgrow s1)) (D ++ ddata (dgrow s1))
                   W5 c5 ->
                 SRrG SEGS R W5 c5 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)).
      { intros W5 c5 H5.
        apply (IH cx Hp kr (dnext (dlive cx) (dxmx cx) (dgrow s1)) (D ++ ddata (dgrow s1)) W5 c5);
          [lia|exact HB|exact H5]. }
      apply (FEEDS cx Hp kr (dgrow s1) D W2 c2 HB H2). intros W3 c3 H3.
      apply (DROP cx Hp kr (dgrow s1) D W3 c3 HB H3).
      + intros q W4 c4 H4. exact (LINES cx Hp kr (dgrow s1) D W4 c4 HB (or_introl (ex_intro _ q H4)) NXT).
      + intros W4 c4 H4. exact (LINES cx Hp kr (dgrow s1) D W4 c4 HB (or_intror H4) NXT). }
  intros cx Hp kr s1 D W1 c1 HB HI. exact (MAIN (dneed s1) cx Hp kr s1 D W1 c1 (le_n _) HB HI).
Qed.

Theorem dr_outer_xR : dr_outer_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
  intros TOP FEEDS DROP LINES END cx Hp kr s1 D W1 c1 HB HI.
  refine (dr_outer_core_xR TOP _ DROP _ END cx Hp kr s1 D W1 c1 HB HI).
  - intros cx' Hp' kr' s' D' W' c' HB' H K. exact (FEEDS cx' Hp' kr' s' D' 0%nat W' c' HB' H K).
  - intros cx' Hp' kr' s' D' W' c' HB' [(q & H)|H] K.
    + exact (LINES cx' Hp' kr' s' D' W' c' HB' (or_introl (ex_intro _ 0%nat (ex_intro _ q H))) K).
    + exact (LINES cx' Hp' kr' s' D' W' c' HB' (or_intror (or_intror (ex_intro _ 0%nat H))) K).
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Lemma DRB_rstart_x : forall cx Hp kr s1 D k W1 c1,
  DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D k W1 c1 -> RSTART cx s1 D.
Proof. eapply (DRB_rstart_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dr_outer_core_x :
dr_top_stmt_x B PST ARx MT RP MMAX RG ->
(forall cx Hp kr s1 D W1 c1,
   DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D 0 W1 c1 ->
   (forall W2 c2, DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 ->
      SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
   SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
dr_drop_stmt_x B PST ARx MT RP MMAX RG ->
(forall cx Hp kr s1 D W1 c1,
   DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
   ((exists q, DLL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D 0 q W1 c1) \/
    DLR_x B PST ARx MT RP MMAX RG cx Hp kr s1 D 0 W1 c1) ->
   (forall W2 c2, DI_x B PST ARx MT RP MMAX RG cx Hp kr (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 ->
      SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
   SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall cx Hp kr s1 D W1 c1,
   DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DEND_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W1 c1 ->
   SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
forall cx Hp kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DI_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W1 c1 ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof. eapply (dr_outer_core_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Theorem dr_outer_x : dr_outer_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_outer_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.

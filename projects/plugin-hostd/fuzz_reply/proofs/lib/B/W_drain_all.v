(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ALL composition of the image-B (fuzz_reply.asan-ubsan) walk of
   fuzz_reply's drain, ported from lib/A/W_drain_all.v (W7, a working branch) onto lib/B/W_drain_cx.v: dr_spec
   at A_drainP (0x83278) from the prologue's statement and the outer loop's conclusion.  dr_spec's binders become
   the entry context cx, DBASE is built from dr_spec's premises, and the prologue continues into the outer
   loop's head DI in the initial round state (ds0 cx, nothing handed over yet: D = []).  B's DBASE carries
   `dxSA cx mod 8 = 0` (the UBSan alignment trap at 0x832b4-0x832b8); dr_spec states it (W7's A text, twinned
   by the kit), so it is one more of dr_spec's premises here.  The statement is W_drain_cx.v's dr_all_stmt;
   it walks no instruction. *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane, a Theorem Labs lane's dr_sa_align row): the named premise dr_sa_align is gone; dr_all_core intros SA mod 8 = 0 from dr_spec. *)
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
(* DR_x: the generic statements (W_drain_cx_x.v), dr_spec_x (W_contract_x.v) and the room record (W_journal_x.v) *)
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

Lemma dr_all_core :
  dr_pro_stmt B MT MMAX RG ->
  (forall cx W1 c1, DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx (ds0 cx) [] W1 c1 ->
     SRr SEGS W1 c1 (dPOST B MT RG cx)) ->
  dr_spec B MT MMAX RG A_drainP.
Proof.
intros HPRO HOUT. unfold dr_spec; cbv zeta.
intros W ly S regs mem md ch G SA e j h c O mx no cap out
  Hpre Ha0 HinG HG1 HG2 HSA8 Hent Hawr Hok Hj Hsrc Hoth Hfd Hsk Hu Hout Hrom [rest Hperm] Hps Hcap Hnh Hmax Hlive Hmo.
pose (cx := mkDcx regs ly S W mem md ch G SA e j h c O mx no cap out rest).
assert (HDB : DBASE B MT MMAX RG cx).
{ unfold DBASE, dHA, dtrc, dcost, cx;
  cbn [dxregs dxly dxS dxW dxmem dxmd dxch dxG dxSA dxe dxj dxh dxc dxO dxmx dxno dxcap dxout dxrest].
  repeat (split; [assumption|]). assumption. }
exact (HPRO cx HDB (fun W2 c2 HDI => HOUT cx W2 c2 HDB HDI)).
Qed.

Theorem dr_all : dr_all_stmt B MT MMAX RG.
Proof.
intros HPRO HOUT. apply dr_all_core; [exact HPRO |].
intros cx W1 c1 HB HDI. exact (HOUT cx (ds0 cx) [] W1 c1 HB HDI).
Qed.

End c.

(* ---- DR_x: the top composition over any ARx, W_drain_cx_x.v's dr_all_stmt_x (the image-B twin of a Theorem Labs lane's
   lib/A/W_drain_all.v dr_all_core_x / dr_all_x): dr_spec_x's binders as the entry context (its ghost list Hp and
   budget kr included), DBASE_x from dr_spec_x's premises.  B's DBASE_x keeps `dxSA cx mod 8 = 0` (the UBSan alignment
   trap at 0x832b4-0x832b8) and dr_spec_x states it, so it is one more premise here (HSA8), as in dr_all_core above.
   It reads no Section hypothesis, so its Section has the variables only.  The AR theorems are kept as they are. ---- *)
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

Lemma dr_all_core_xR :
  dr_pro_stmt_xR B PST ARx MT RP MMAX RG R ->
  (forall cx Hp kr W1 c1, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
     DI_xR B PST ARx MT RP MMAX RG R cx Hp kr (ds0 cx) [] W1 c1 ->
     SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
  dr_spec_xR B PST ARx R MT RP MMAX RG A_drainP.
Proof.
intros HPRO HOUT. unfold dr_spec_xR; cbv zeta.
intros W ly S Hp regs mem md ch G SA e j h c O mx no cap out
  Hpre Ha0 HinG HG1 HG2 HSA8 Hent Hawr Hok Hj Hsrc Hoth Hfd Hsk Hu Hout Hrom [rest Hperm] Hps Hcap Hnh Hmax Hlive Hmo
  kr Hrm Hcnt.
pose (cx := mkDcx regs ly S W mem md ch G SA e j h c O mx no cap out rest).
assert (HDB : DBASE_x B ARx MT RP MMAX RG cx Hp kr).
{ unfold DBASE_x, dHA, dtrc, dcost, cx;
  cbn [dxregs dxly dxS dxW dxmem dxmd dxch dxG dxSA dxe dxj dxh dxc dxO dxmx dxno dxcap dxout dxrest].
  repeat (split; [assumption|]). assumption. }
exact (HPRO cx Hp kr HDB (fun W2 c2 HDI => HOUT cx Hp kr W2 c2 HDB HDI)).
Qed.

Theorem dr_all_xR : dr_all_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros HPRO HOUT. apply dr_all_core_xR; [exact HPRO|].
intros cx Hp kr W1 c1 HB HDI. exact (HOUT cx Hp kr (ds0 cx) [] W1 c1 HB HDI).
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Lemma dr_all_core_x :
  dr_pro_stmt_x B PST ARx MT RP MMAX RG ->
  (forall cx Hp kr W1 c1, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
     DI_x B PST ARx MT RP MMAX RG cx Hp kr (ds0 cx) [] W1 c1 ->
     SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
  dr_spec_x B PST ARx MT RP MMAX RG A_drainP.
Proof. eapply (dr_all_core_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Theorem dr_all_x : dr_all_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_all_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.

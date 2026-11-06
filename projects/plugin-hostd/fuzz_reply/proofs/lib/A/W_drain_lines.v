(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: dr_lines, the line loop of fuzz_reply's ASan drain (W_drain_cx.v dr_lines_stmt). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_lines.v, with its module paths and module names changed; 147 of its 164 lines of code are new or changed and 37 lines of the source are left out. *)
(* The LINES composition of fuzz_reply's drain ASan walk (fuzz_reply.asan
   0x836bc .. 0x83a4c, the line loop of relay.c:205-216): from any of the loop's three cut points (DLL 0x836bc,
   DLN 0x836f4, DLR 0x83a4c) to the outer loop's head DI of the next round.  The statement is W_drain_cx.v's
   dr_lines_stmt; it takes the four segment STATEMENTS (dr_linea_stmt, dr_gs_stmt, dr_next_stmt, dr_rest_stmt) as
   premises, so this file walks no instruction: it chains the segments at their cut points
     DLL p q -(linea)-> DLN (S q)  or  DGS p q -(gs)-> DLN (S q)
     DLN p   -(next)->  DLL p q (p <= q < |dW s1|)  or  DLR p
     DLR p   -(rest)->  DI of the next round
   by induction on the measure |dW s1| - p of DLN (plain lib/Prog/drain_b.v's line-loop composition, structure
   only).  The Section header is W_drain_cx.v's, verbatim. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx.
(* DR_x: the generic statement dr_lines_stmt_x (W_drain_cx_x.v) and the room record (W_journal_x.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) and dr_spec_xR (W_contract_xR.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

(* ---- The loop, abstractly: three cut predicates over (world, config), a line [p, q) always inside the
   buffer of n bytes (p <= q < n), and the post P.  LN p has measure n - p: from LN p the next segment reaches
   LL p q with q >= p, and from LL p q the line segment (with gesture_seen composed in) reaches LN (S q), whose
   measure n - S q is below n - p. ---- *)
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
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) ->
  p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
  aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- LINES: the line loop, from DLL / DLN / DLR to DI of the next round. ----
   DLL's own `(p <= q < length (dW s1))%nat` bounds the line; gesture_seen (dr_gs) is composed into the line
   segment's DGS exit, so the abstract loop sees only DLL, DLN and DLR. *)
Theorem dr_lines : dr_lines_stmt B MT MMAX RG.
Proof.
intros LINEA GS NEXT REST cx s1 D W1 c1 HB HC HDI.
match goal with |- SRr ?SG _ _ ?Q =>
  refine (dr_lines_loop (length (dW s1)) (fun W c => SRr SG W c Q) _ _ _ _ _ _ _ W1 c1 HC) end; cbv beta.
- intros p q W c H. unfold DLL in H.
  destruct H as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
    _ & _ & _ & _ & _ & Hpq & _).
  exact Hpq.
- intros p q W c H K. apply (LINEA cx s1 D p q W c HB H K).
  intros W2 c2 H2. exact (GS cx s1 D p q W2 c2 HB H2 K).
- intros p W c H K1 K2. exact (NEXT cx s1 D p W c HB H K1 K2).
- intros p W c H. exact (REST cx s1 D p W c HB H HDI).
Qed.

End c.

(* ---- DR_x: dr_lines over any ARx, W_drain_cx_x.v's dr_lines_stmt_x. The walk is dr_lines' above with the entry's
   ghost list Hp and budget kr threaded; it reads no Section hypothesis, so its Section has the variables only. The AR
   theorem dr_lines is kept as it is. ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.



(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of every composition above, for the drain's R carriers (W_drain_cx_x.v
   Section wR).  Each twin is its strict text with SRr SEGS -> SRrG SEGS R, each carrier X_x -> its twin X_xR (R last
   among its section variables), dr_spec_x -> dr_spec_xR (R after ARx), and each composition name L -> LR.  A
   composition walks no instruction, so its R proof is its strict script.  At R := wle each twin is its strict text
   by conversion. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

Theorem dr_lines_xR : dr_lines_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros LINEA GS NEXT REST cx Hp kr s1 D W1 c1 HB HC HDI.
match goal with |- SRrG ?SG _ _ _ ?Q =>
  refine (dr_lines_loop (length (dW s1)) (fun W c => SRrG SG R W c Q) _ _ _ _ _ _ _ W1 c1 HC) end; cbv beta.
- intros p q W c H. unfold DLL_xR in H.
  destruct H as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks &
    tl & _ & _ & _ & _ & _ & Hpq & _).
  exact Hpq.
- intros p q W c H K. apply (LINEA cx Hp kr s1 D p q W c HB H K).
  intros W2 c2 H2. exact (GS cx Hp kr s1 D p q W2 c2 HB H2 K).
- intros p W c H K1 K2. exact (NEXT cx Hp kr s1 D p W c HB H K1 K2).
- intros p W c H. exact (REST cx Hp kr s1 D p W c HB H HDI).
Qed.

End wR.

Theorem dr_lines_x : dr_lines_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dr_lines_xR (@wle SEGS)). Qed.
End cx.
End b.
End a.

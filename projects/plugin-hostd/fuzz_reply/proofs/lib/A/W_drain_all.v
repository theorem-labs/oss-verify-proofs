(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the top composition of fuzz_reply's drain ASan walk (fuzz_reply.asan
   0x830dc .. 0x83de4): the prologue (dr_pro_stmt) and the outer loop's conclusion (dr_outer_concl) give drain's
   contract dr_spec at A_drainP.  The statement is W_drain_cx.v's dr_all_stmt; the Section header below is that
   file's, verbatim.  The entry context is dr_spec's binders, with the Permutation's `rest` taken from its
   existential; DBASE is exactly dr_spec's premises and dPOST is dr_post at those arguments. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_all.v, with its module paths changed; 52 of its 165 lines of code are new or changed and 6 lines of the source are left out. *)
(* The top composition of fuzz_reply's drain ASan walk (fuzz_reply.asan
   0x830dc .. 0x83de4): the prologue (dr_pro_stmt) and the outer loop's conclusion (dr_outer_concl) give drain's
   contract dr_spec at A_drainP.  The statement is W_drain_cx.v's dr_all_stmt; the Section header below is that
   file's, verbatim.  The entry context is dr_spec's binders, with the Permutation's `rest` taken from its
   existential; DBASE is exactly dr_spec's premises and dPOST is dr_post at those arguments. *)
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
(* DR_x: the generic statements (W_drain_cx_x.v), dr_spec_x (W_contract_x.v) and the room record (W_journal_x.v) *)
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

(* dr_spec's binders as the entry context, and DBASE from dr_spec's premises: the prologue, continued by the
   outer loop's head in the initial round state (s1 = ds0 cx, nothing handed over yet: D = []). *)
Lemma dr_all_core :
  dr_pro_stmt B MT MMAX RG ->
  (forall cx W1 c1, DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx (ds0 cx) [] W1 c1 ->
     SRr SEGS W1 c1 (dPOST B MT RG cx)) ->
  dr_spec B MT MMAX RG A_drainP.
Proof.
intros HPRO HOUT. unfold dr_spec; cbv zeta.
intros W ly S regs mem md ch G SA e j h c O mx no cap out
  Hpre Ha0 HinG HG1 HG2 _ Hent Hawr Hok Hj Hsrc Hoth Hfd Hsk Hu Hout Hrom [rest Hperm] Hps Hcap Hnh Hmax Hlive Hmo.
pose (cx := mkDcx regs ly S W mem md ch G SA e j h c O mx no cap out rest).
assert (HDB : DBASE B MT MMAX RG cx).
{ unfold DBASE, dHA, dtrc, dcost, cx;
  cbn [dxregs dxly dxS dxW dxmem dxmd dxch dxG dxSA dxe dxj dxh dxc dxO dxmx dxno dxcap dxout dxrest].
  repeat (split; [assumption|]). assumption. }
exact (HPRO cx HDB (fun W2 c2 HDI => HOUT cx W2 c2 HDB HDI)).
Qed.

Theorem dr_all : dr_all_stmt B MT MMAX RG.
Proof.
intros HPRO HOUT. apply dr_all_core; [exact HPRO|].
intros cx W1 c1 HB HDI. exact (HOUT cx (ds0 cx) [] W1 c1 HB HDI).
Qed.

End c.

(* ---- DR_x: the top composition over any ARx, W_drain_cx_x.v's dr_all_stmt_x: dr_spec_x's binders as the entry
   context (its ghost list Hp and budget kr included), DBASE_x dr_spec_x's premises but `SA mod 8 = 0`, which no stage
   reads (as dr_all_core drops it).  It reads no Section hypothesis, so its Section has the variables only.  The AR
   theorems are kept as they are. ---- *)
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

Lemma dr_all_core_xR :
  dr_pro_stmt_xR B PST ARx MT RP MMAX RG R ->
  (forall cx Hp kr W1 c1, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
     DI_xR B PST ARx MT RP MMAX RG R cx Hp kr (ds0 cx) [] W1 c1 ->
     SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
  dr_spec_xR B PST ARx R MT RP MMAX RG A_drainP.
Proof.
intros HPRO HOUT. unfold dr_spec_xR; cbv zeta.
intros W ly S Hp regs mem md ch G SA e j h c O mx no cap out
  Hpre Ha0 HinG HG1 HG2 _ Hent Hawr Hok Hj Hsrc Hoth Hfd Hsk Hu Hout Hrom [rest Hperm] Hps Hcap Hnh Hmax Hlive Hmo
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

Lemma dr_all_core_x :
  dr_pro_stmt_x B PST ARx MT RP MMAX RG ->
  (forall cx Hp kr W1 c1, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
     DI_x B PST ARx MT RP MMAX RG cx Hp kr (ds0 cx) [] W1 c1 ->
     SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
  dr_spec_x B PST ARx MT RP MMAX RG A_drainP.
Proof. exact (dr_all_core_xR (@wle SEGS)). Qed.

Theorem dr_all_x : dr_all_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dr_all_xR (@wle SEGS)). Qed.
End cx.
End b.
End a.

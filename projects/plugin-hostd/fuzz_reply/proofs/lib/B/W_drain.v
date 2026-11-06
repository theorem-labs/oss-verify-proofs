(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane, a Theorem Labs lane's dr_sa_align row): dr_assemble loses the premise dr_sa_align; the kit's dr_spec states SA mod 8 = 0 (W_drain_cx.v FINDING 1, closed). *)
(* Modified by Theorem Labs, 2026-10: the assembly of the image-B (fuzz_reply.asan-ubsan) ASan+UBSan walk of
   fuzz_reply's drain, 0x83278 .. 0x841fc (993 instructions), from its segment theorems as lib/B/W_drain_cx.v
   fixes them; the lib/B twin of lib/A/W_drain.v (a working branch d2db3bb89ba).
     dr_spec at A_drainP = dr_all dr_pro
                             (dr_outer dr_top (dr_feeds dr_feed) dr_drop
                                (dr_lines dr_linea (dr_gs_of gs_scan gs_add gs_free) dr_next dr_rest)
                                (dr_end dr_epi)).
   dr_assemble states that composition over the segment STATEMENTS alone, so each premise is supplied by
   exactly one segment theorem; the Section header below is lib/B/W_drain_cx.v's, verbatim.
   B's prologue traps at 0x832b8 unless the entry address SA is 8-aligned; the kit's dr_spec states it (W7's A
   text, twinned by the kit), so the composition is A's (FINDING 1 of W_drain_cx.v's header, closed). *)
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

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
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
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
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) ->
  p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
  aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Lemma dr_assemble :
  dr_pro_stmt B MT MMAX RG -> dr_top_stmt B MT MMAX RG -> dr_feed_stmt B MT MMAX RG ->
  dr_feeds_stmt B MT MMAX RG -> dr_drop_stmt B MT MMAX RG -> dr_linea_stmt B MT MMAX RG ->
  dr_gs_stmt B MT MMAX RG -> dr_next_stmt B MT MMAX RG -> dr_rest_stmt B MT MMAX RG ->
  dr_lines_stmt B MT MMAX RG -> dr_epi_stmt B RG -> dr_end_stmt B MT MMAX RG ->
  dr_outer_stmt B MT MMAX RG -> dr_all_stmt B MT MMAX RG ->
  dr_spec B MT MMAX RG (A_drainP).
Proof.
intros PRO TOP FEED FEEDS DROP LINEA GS NEXT REST LINES EPI END OUTER ALL.
exact (ALL PRO (OUTER TOP (FEEDS FEED) DROP (LINES LINEA GS NEXT REST) (END EPI))).
Qed.

End c.

(* ---- DR_x: the same composition over any ARx, from W_drain_cx_x.v's generic statements to W_contract_x.v's dr_spec_x
   at A_drainP (the image-B twin of a Theorem Labs lane's lib/A/W_drain.v dr_assemble_x). It reads no Section hypothesis, so its
   Section has the variables only; dr_assemble is kept as it is. ---- *)
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

Lemma dr_assemble_xR :
  dr_pro_stmt_xR B PST ARx MT RP MMAX RG R -> dr_top_stmt_xR B PST ARx MT RP MMAX RG R ->
  dr_feed_stmt_xR B PST ARx MT RP MMAX RG R -> dr_feeds_stmt_xR B PST ARx MT RP MMAX RG R ->
  dr_drop_stmt_xR B PST ARx MT RP MMAX RG R -> dr_linea_stmt_xR B PST ARx MT RP MMAX RG R ->
  dr_gs_stmt_xR B PST ARx MT RP MMAX RG R -> dr_next_stmt_xR B PST ARx MT RP MMAX RG R ->
  dr_rest_stmt_xR B PST ARx MT RP MMAX RG R -> dr_lines_stmt_xR B PST ARx MT RP MMAX RG R ->
  dr_epi_stmt_xR B PST ARx RG R -> dr_end_stmt_xR B PST ARx MT RP MMAX RG R ->
  dr_outer_stmt_xR B PST ARx MT RP MMAX RG R -> dr_all_stmt_xR B PST ARx MT RP MMAX RG R ->
  dr_spec_xR B PST ARx R MT RP MMAX RG A_drainP.
Proof.
intros PRO TOP FEED FEEDS DROP LINEA GS NEXT REST LINES EPI END OUTER ALL.
exact (ALL PRO (OUTER TOP (FEEDS FEED) DROP (LINES LINEA GS NEXT REST) (END EPI))).
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Lemma dr_assemble_x :
  dr_pro_stmt_x B PST ARx MT RP MMAX RG -> dr_top_stmt_x B PST ARx MT RP MMAX RG ->
  dr_feed_stmt_x B PST ARx MT RP MMAX RG -> dr_feeds_stmt_x B PST ARx MT RP MMAX RG ->
  dr_drop_stmt_x B PST ARx MT RP MMAX RG -> dr_linea_stmt_x B PST ARx MT RP MMAX RG ->
  dr_gs_stmt_x B PST ARx MT RP MMAX RG -> dr_next_stmt_x B PST ARx MT RP MMAX RG ->
  dr_rest_stmt_x B PST ARx MT RP MMAX RG -> dr_lines_stmt_x B PST ARx MT RP MMAX RG ->
  dr_epi_stmt_x B PST ARx RG -> dr_end_stmt_x B PST ARx MT RP MMAX RG ->
  dr_outer_stmt_x B PST ARx MT RP MMAX RG -> dr_all_stmt_x B PST ARx MT RP MMAX RG ->
  dr_spec_x B PST ARx MT RP MMAX RG A_drainP.
Proof. eapply (dr_assemble_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.

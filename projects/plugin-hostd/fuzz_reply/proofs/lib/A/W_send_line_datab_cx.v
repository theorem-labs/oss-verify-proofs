(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the loop segment of fuzz_reply's ASan send_line walk, in the form of the
   cgif donor's loop over concrete cut states (proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v tcbb_loopX). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_send_line_loop.v; 45 of its 123 lines of code are new or changed and 2095 lines of the source are left out. *)
(* The cut of a data round of fuzz_reply's ASan send_line loop (W_send_line_loop.v sl_arm_data) at the JOIN 0x82850
   (A_sl_join, listing offset 1380): the grow path (realloc at 0x82840, then g_out := the new block and g_capout := its
   size) and the no-grow path (the bgeu at 0x82830 taken) both reach it before the __asan_memcpy setup
   (0x82850 ld a0,0x37c(s4); ld s3,0x104(s10); add a1,s1,s6; add a0,a0,s3; mv a2,s2; 0x82864 jal __asan_memcpy).
   SLM is the state there: SLI (W_send_line_cx.v) of the round with eiL = 0 and a live controller, g_out holding
   capM >= no + sent + n bytes (the round's n bytes not yet copied, g_nout not yet updated), and the plain model's
   rounds after this one.  sl_copy_stmt is the rest of the round: the copy of line[sent .. sent + n) to
   g_out + no + sent, g_nout := no + sent + n, then back to the loop head L (by the loop's bound n0, sl_loop_at) or
   out through the epilogue.  The Section header is W_send_line_cx.v's. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_frame W_sites W_contract W_send_line_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* One round of the plain model sends sl_n mx rem bytes: rem cut to mx when mx <> 0 and rem > mx. *)
Definition sl_n (mx rem : Z) : Z := if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_sl_join : Z := A_sl_loop + 0x88.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
(* nothing a callee's journal may change is a read-only image byte (W_journal.v rom_out / ajournal_gx_rom_view); and
   aout_at's three read-only cells are program globals off the allocator's statics, so a realloc keeps them *)
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* runtime and allocator sites *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
(* instance facts: errno is tp - 164 (W_sites.v aerrno_realizes) and its shadow is zero *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : exists r, In r (as_zero_shadow B) /\ fst r <= as_errno B /\ as_errno B + 4 <= fst r + snd r.
(* errno's 4 bytes are writable image bytes in the segments' own view (W_drain_cx.v HERRW, same text) *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
(* placement: the objects send_line reads by PLdHi, and the kept auipc registers it stores and loads through *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
(* g_send_max is not one of the listing's objects: place it in the image band by its address. *)
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
(* placement: the cells send_line reads or writes are pairwise disjoint ((lo, hi) extents, as extent_of_region
   makes them; the pinned placement decides it by vm_compute; errno is tp - 164, TFIB_ERRNO 0x5d93cc). *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].

(* The loop at a bound n: from L, send_line ends in its post (sl_loop_stmt at one n). *)
Definition sl_loop_at (n : nat) : Prop :=
forall regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat n ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).

(* The registers at the join: s0 = len, s1 = line, s2 = n, s6 = sent, s7 = the shadow base, s4 s5 s8 s9 s10 s11 the
   kept auipc values (sl_regsL's, but s2 = n in place of s3 = 3). *)
Definition sl_regsM (regsM : bvmap 5 word) (len line sent n : Z) : Prop :=
getr regsM 8 = w64 len /\ getr regsM 9 = w64 line /\ getr regsM 18 = w64 n /\ getr regsM 22 = w64 sent /\
getr regsM 23 = w64 SB /\ getr regsM 20 = w64 (VAL (A_HI 24)) /\ getr regsM 21 = w64 (VAL (A_HI 16)) /\
getr regsM 24 = w64 (VAL (A_HI 23)) /\ getr regsM 25 = w64 (VAL (A_HI 19)) /\ getr regsM 26 = w64 (VAL (A_HI 22)) /\
getr regsM 27 = w64 (VAL (A_HI 20)).
(* The state at the join of the round that sends n = sl_n mx (len - sent) bytes from sent. *)
Definition SLM (regsE : bvmap 5 word) ly S W mem md (c : ctl) (O : list byte) (mx no cap out line : Z) (Bl : list byte)
(WM : world SEGS) (regsM : bvmap 5 word) (memM : word -> option byte) (mdM : Model) (sent n : Z) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyM SM kM evL capM outM spent rest,
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S W mem md [] lyM SM WM memM mdM kM /\
spZ regsM = sp0 - SL_FRAME /\ getr regsM 3 = getr regsE 3 /\ getr regsM 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsM regsM len line sent n /\
val_mem SEGS (mrestrict (w_H WM) memM) (sp0 - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
val_mem SEGS (mrestrict (w_H WM) memM) (sp0 - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
sl_saved WM memM (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0 /\ 0 <= sent < len /\ n = sl_n mx (len - sent) /\
evL = (if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyM SM WM memM (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capM outM /\
no + sent + n <= capM /\
garr8 SEGS (arm WM memM) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WM memM /\
sl_line_ok B lyM SM outM line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent + n) capM (len - sent - n) /\
sl_max_run (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n) < MMAX /\
blocks_bytes SM +
  tr_peak (send_line_b_c.send_line_tr true mx (no + sent + n) capM (len - sent - n) 0 RelayRunF.adr0) <= LIVE_MAX /\
apres_kept B W mem WM memM /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SM spent /\
spent + sl_cost_run MT (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n) <= sl_cost MT c mx no cap len /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyM SM) (aout_blks capM outM ++ rest) /\
frames SM = frames S.
(* The copy half: from the join, send_line ends in its post, given the loop at the bound n0 the round leaves. *)
Definition sl_copy_stmt : Prop :=
forall (n0 : nat) regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n,
sl_loop_at n0 ->
SLM regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n ->
2 * (Z.of_nat (length Bl) - sent) <= Z.of_nat (Datatypes.S n0) ->
SRr SEGS WM (mkCfg (mkst regsM (Z_to_bv 64 (BASE + A_sl_join)) memM (seg_rom SEGS)) mdM)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
End c.
End b.
End a.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segment statements of check_reply's walk (fuzz_command.asan, 0x86d78), in
   the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cgif_close's CL_*_stmtX: the entry facts bundled, a
   mid-walk invariant, the registers at the program point, and the configuration at BASE + pc realizing the
   contract's post) and the mid-walk seed of A/AChc.v (cl_seed).

   The bundle `crv` holds the variables of tcheck_reply_spec (lib/A/Prog/check_reply_c.v) and `cr_cx` the facts of
   its premises the segments read (the record's cells, the GOT words, the read-only ranges and the words' shadow are
   derived from the premises in check_reply.v, from CmdRecFacts' cmd_rec_cells, cmd_ro_ok and cmd_ro_in_img and AR's
   zshadow_ok of the stack window), with `w + 32 <= ly_stk_hi ly` (the statement's `w + WORDS_W + 12 <= ly_stk_hi ly`
   with w and ly_stk_hi 8-aligned). `cr_bd` holds the statement's range and alignment premises check_reply_answer's call asks, and
   `cr_ls` the layout and allocator state at a mid-walk point: the entry's layout, and the entry's state up to st_fs
   (the side-stack frame taken at 0x86de0 is the walk's only state change).

   After the frame call (0x86de0) the walk holds the side-stack frame F = frame_addr lyc 1 pos, its flag cell FL at
   F + 120, its shadow S = SB + F / 8, and keeps
     s0 = sp at the entry, s1 = sp = (sp0 - 128) & -32, s2 = s7 = F, s6 = S, s8 = SB, s9 = g_rec,
     s4 = g_rec + 928, s10 = SB + (g_rec + 928) / 8, the entry's ra and s0..s10 at sp0 - 8 .. sp0 - 96.
   The program points (CR_* in check_reply_k.v) cut the walk where a call goes out or the paths meet:
     CR_MEMCHR (0x86ef8), CR_RET_SRC (0x86f18), CR_SNPRINTF (0x86f98), CR_RET_SNP (0x86f9c), CR_STRCMP (0x86fb8),
     CR_STRLEN (0x86f68), CR_JOIN (0x86fcc), CR_EPI (0x86ff8).
   The post CR_POST is the statement's apost_baseF at the segment's own FP state. The snprintf call (0x86f98) is the
   walk's only FP change: the segments up to it carry the statement's rounding-mode-0 premise at the entry's FP state
   (the call's frm0_entry), and CR_RSNP_stmt, the point it returns to, is used at the FP state the call returns
   (PaFx.v srr_after_artF). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_reply_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the entry's callee-saved registers, in the order the prologue stores them below sp0 (ra at sp0 - 8, ...) *)
Definition cr_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the variables of tcheck_reply_spec *)
Record crv := mkCRV {
  c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
  c_ch : list (Z * Z * Z); c_w : Z; c_ww : Z; c_p0 : Z; c_n : Z; c_rep : Z; c_ans : Z; c_ev : Z;
  c_xr : list byte; c_w0 : list byte; c_R : rstate; c_O : list (Z * Z) }.
Definition c_sp (v : crv) : Z := spZ (c_regs v).
Definition c_nr (v : crv) : Z := Z.of_nat (length (c_xr v)).
(* the reply block's address as the code loads it (g_rec.reply, 8 bytes) *)
Definition c_p (v : crv) : Z := c_rep v mod 2 ^ 64.
Definition c_code (v : crv) : Z := reply_code_a (c_xr v).

Section e.
Variable B : asyms.
Variables RLO RHI : Z.

(* the entry facts the segments read: tcheck_reply_spec's premises and what check_reply.v derives from them at the
   entry (cmd_got_ok, cmd_ro_in, aguard_ok, the replace_str flag byte, the errno cell, the words' shadow), and
   w + 32 <= ly_stk_hi ly *)
Definition cr_cx (v : crv) : Prop :=
let ly := c_ly v in let S := c_S v in let W := c_W v in let regs := c_regs v in let mem := c_mem v in
let md := c_md v in let w := c_w v in let n := c_n v in let xr := c_xr v in let w0 := c_w0 v in let R := c_R v in
afn_pre SEGS B CHECK_REPLY_STK ly S W regs mem md (c_ch v) /\
Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_got_ok (rdW W mem) /\ cmd_ro_ok (rdW W mem) /\ cmd_ro_in (in_roP SEGS RLO RHI) /\ cmd_val_objs /\
aguard_ok SEGS W mem 0xa7098 0x6045d8 /\
getr regs 10 = w64 w /\
rec_repA B ly S (rdW W mem) R (c_O v) /\
r_nreplies R = 1 /\ r_reply R = Some (xr ++ [Z_to_bv 8 0]) /\ no0 xr /\
aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 (c_rep v) /\ atail_vis SEGS W mem (c_rep v + Z.of_nat (length xr)) /\
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 (c_ans v) /\
(forall xa, r_answer R = Some xa -> atail_vis SEGS W mem (c_ans v + Z.of_nat (length xa))) /\
w mod 8 = 0 /\ spZ regs <= w /\
range_addressable (rdW W mem) SHADOW_OFF (w + WORDS_W) 12 /\
aval_mem (rdW W mem) (w + WORDS_W) 8 (c_ww v) /\ aval_mem (rdW W mem) (w + WORDS_N) 4 n /\ 0 <= n < 2 ^ 31 /\
(n <> 0 ->
 in_blockA (ablocks B ly S) (c_ww v) 8 /\ aval_mem (rdW W mem) (c_ww v) 8 (c_p0 v) /\
 in_blockA (ablocks B ly S) (c_p0 v) (Z.of_nat (length w0) + 1) /\ astr_atR (rdW W mem) (c_p0 v) w0 /\
 atail_vis SEGS W mem (c_p0 v + Z.of_nat (length w0))) /\
answer_ok_mA (r_answer R) xr n w0 /\ reply_okA n w0 xr /\
rdW W mem A_FLAG_REPLACE_STR = Some 1 /\
rd32 (rdW W mem) (as_errno B) (c_ev v) /\
st_nev S + EV_CHECK_REPLY <= EV_MAX /\
w + 32 <= ly_stk_hi ly.

(* the contract's post *)
Definition CR_POST (v : crv) : world SEGS -> config -> Prop :=
apost_baseF SEGS B CHECK_REPLY_STK [] (c_regs v) (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) EV_CHECK_REPLY
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B (c_ly v) (c_S v)) /\
  ly' = c_ly v /\ exists f, S' = set_fs f (c_S v)).

(* the statement's range premises (check_reply_c.v) that check_reply_answer's call asks, and the word slot's
   alignment `ww mod 8 = 0` (check_reply_c.v:145), which check_reply_answer asks under n = 1 *)
Definition cr_bd (v : crv) : Prop :=
0 <= c_w v < 2 ^ 64 /\ 0 <= c_rep v < 2 ^ 64 /\ 0 <= c_ans v < 2 ^ 64 /\ 0 <= c_ww v < 2 ^ 64 /\
(c_n v <> 0 -> 0 <= c_p0 v < 2 ^ 64) /\ (c_n v <> 0 -> c_ww v mod 8 = 0).

(* the layout and allocator state at a mid-walk point: the entry's layout, the entry's state up to st_fs *)
Definition cr_ls (v : crv) (lyc : alayout) (Sc : astate) : Prop :=
lyc = c_ly v /\ exists f, Sc = set_fs f (c_S v).

(* the entry's callee-saved registers below sp0 *)
Definition cr_saved (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error cr_saved_regs j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* the mid-walk invariant: the journal from the entry with the frame (1, pos) owned, the blocks unchanged, the frame's
   flag pointer at F + 120 and the shadow of refusal[32] (shadow bytes 4..7 of the frame) at 0, the entry's
   callee-saved registers below sp0, g_rec's reply and reply_size fields *)
Definition cr_mid (v : crv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte) (mdc : Model)
(pos : Z) : Prop :=
let F := frame_addr lyc 1 pos in
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc Wc memc mdc 0 /\
Permutation (ablocks B lyc Sc) (ablocks B (c_ly v) (c_S v)) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (F + 120) 8 (flag_addr lyc 1 pos) /\
(forall i, 4 <= i < 8 -> val_mem SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + F / 8 + i) 1 0) /\
cr_saved (mrestrict (w_H Wc) memc) (c_sp v) (c_regs v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (A_G_REC + OFF_REPLY) 8 (c_p v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (A_G_REC + OFF_REPLY_SIZE) 8 (c_nr v + 1).

(* the registers the walk keeps after the frame call *)
Definition cr_regs_at (v : crv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
let F := frame_addr lyc 1 pos in
getr regs1 2 = w64 (sp1_of (c_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (c_sp v) /\ getr regs1 9 = w64 (sp1_of (c_sp v)) /\
getr regs1 18 = w64 F /\ getr regs1 23 = w64 F /\ getr regs1 22 = w64 (SHADOW_OFF + F / 8) /\
getr regs1 24 = w64 SHADOW_OFF /\ getr regs1 25 = w64 A_G_REC /\ getr regs1 20 = w64 (A_G_REC + OFF_REPLY) /\
getr regs1 26 = w64 (SHADOW_OFF + (A_G_REC + OFF_REPLY) / 8) /\
getr regs1 27 = getr (c_regs v) 27.

Definition cr_at (v : crv) (Wc : world SEGS) (regs1 : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (pc : Z) : Prop :=
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) (CR_POST v).

(* the walk from the entry, as cgif states its walk theorems (A/ACh5.v pb_cgif_closeX), with the statement's
   rounding mode 0 *)
Definition CR_ENTRY_stmt : Prop :=
forall v, cr_cx v -> cr_bd v -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS (c_W v) (cfg_at SEGS (BASE + AF_check_reply) (c_regs v) (c_mem v) (c_md v)) (CR_POST v).

(* 0x86ef8 jal memchr: a0 = the reply, a1 = 0 (the byte at rep + nr), a2 = nr; s3 = w *)
Definition CR_MC_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 ->
getr regs1 19 = w64 (c_w v) ->
getr regs1 10 = w64 (c_p v) -> getr regs1 11 = w64 0 -> getr regs1 12 = w64 (c_nr v) ->
cr_bd v -> cr_ls v lyc Sc -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
cr_at v Wc regs1 memc mdc CR_MEMCHR.

(* 0x86f18, after sup_reply_code: a0 = the code; s3 = w *)
Definition CR_CODE_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 ->
getr regs1 19 = w64 (c_w v) -> getr regs1 10 = w64 (c_code v) -> cr_ls v lyc Sc ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
cr_at v Wc regs1 memc mdc CR_RET_SRC.

(* 0x86f98 jal snprintf (refusal): a0 = s3 = F + 32, a1 = 32, a2 = "resp %d", a3 = s5 = the code *)
Definition CR_SNP_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 ->
c_code v < 0 ->
getr regs1 19 = w64 (frame_addr lyc 1 pos + 32) -> getr regs1 21 = w64 (c_code v) ->
getr regs1 10 = w64 (frame_addr lyc 1 pos + 32) -> getr regs1 11 = w64 32 -> getr regs1 12 = w64 0x210c0 ->
getr regs1 13 = w64 (c_code v) -> cr_ls v lyc Sc -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
cr_at v Wc regs1 memc mdc CR_SNPRINTF.

(* 0x86f9c, back from snprintf (refusal): s3 = F + 32 holding "resp <code>", s5 = the code; used at the FP state the
   wrapper returns *)
Definition CR_RSNP_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 ->
c_code v < 0 ->
getr regs1 19 = w64 (frame_addr lyc 1 pos + 32) -> getr regs1 21 = w64 (c_code v) ->
abytes_atR (rdW Wc memc) (frame_addr lyc 1 pos + 32) (refusal_text (c_code v) ++ [Z_to_bv 8 0]) -> cr_ls v lyc Sc ->
cr_at v Wc regs1 memc mdc CR_RET_SNP.

(* 0x86fb8 jal strcmp (refusal): a0 = the reply, a1 = s3 = F + 32 holding "resp <code>" *)
Definition CR_STRCMP_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 ->
c_code v < 0 ->
getr regs1 19 = w64 (frame_addr lyc 1 pos + 32) -> getr regs1 21 = w64 (c_code v) ->
getr regs1 10 = w64 (c_p v) -> getr regs1 11 = w64 (frame_addr lyc 1 pos + 32) ->
abytes_atR (rdW Wc memc) (frame_addr lyc 1 pos + 32) (refusal_text (c_code v) ++ [Z_to_bv 8 0]) -> cr_ls v lyc Sc ->
cr_at v Wc regs1 memc mdc CR_STRCMP.

(* 0x86f68 jal strlen (a verb): a0 = s3 = w->w[0] *)
Definition CR_STRLEN_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 ->
0 <= c_code v -> c_n v <> 0 ->
getr regs1 19 = w64 (c_p0 v mod 2 ^ 64) -> getr regs1 10 = w64 (c_p0 v mod 2 ^ 64) -> cr_ls v lyc Sc ->
cr_at v Wc regs1 memc mdc CR_STRLEN.

(* 0x86fcc, the shape join: a0 = the shape the message's verb declares (or mod-host's "resp 0"), stated as the
   string argument syntax_reply_matches takes (astr_argA, CmdRep.v: a live block or read-only, unowned bytes whose
   shadow says usable) *)
Definition CR_JOIN_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos q,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 ->
0 <= c_code v ->
getr regs1 10 = w64 q -> 0 <= q < 2 ^ 64 ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] q (Some (shape_strA (c_n v) (c_w0 v))) -> cr_ls v lyc Sc ->
cr_at v Wc regs1 memc mdc CR_JOIN.

(* 0x86ff8, the epilogue: the frame's release and the return *)
Definition CR_EPI_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx v -> cr_mid v lyc Sc Wc memc mdc pos -> cr_regs_at v lyc pos regs1 -> cr_ls v lyc Sc ->
cr_at v Wc regs1 memc mdc CR_EPI.

End e.
End f.
End d.

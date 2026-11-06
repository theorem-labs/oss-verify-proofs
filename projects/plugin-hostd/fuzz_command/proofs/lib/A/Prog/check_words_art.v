(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: pins_set's ASan walk assembled from its pieces (lib/A/Prog/pins_set_s1.v ..
   pins_set_s13.v), after proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v (cgif_close's walk assembled from its segments). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/pins_set.v, with its module paths and module names changed; 67 of its 96 lines of code are new or changed and 83 lines of the source are left out. *)
(* The strcspn and strspn wrapper calls of check_words' walk, as instances of PaArt.v's aj_art_at: the contracts
   astrcspn_realizes / astrspn_realizes of lib/A/Rt/RtString.v:135-161 composed into the caller's journal, stated as
   PaArtStr.v states aj_strcmp_at. Neither entry writes outside its scratch window, so the set of other written
   bytes is empty. The guard cell the entries read (aguard_ok at 0xa7098 / 0x6045d8) comes from the record fact
   cmd_rec_cells (check_words_d.v's cmd_rec_cells_P, from CmdRecFacts.v) at the journal's current AR state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.

Lemma aj_strcspn_at : forall pc, astrcspn_realizes SEGS B pc 0xa7098 0x6045d8 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
astr_at SEGS W memT x sx -> astr_at SEGS W memT y sy ->
aread_ok SEGS (2 * ESTACK) W regsT memT x (astr_len sx + 1) -> amem_range x (astr_len sx + 8) ->
aread_ok SEGS (2 * ESTACK) W regsT memT y (astr_len sy + 1) -> amem_range y (astr_len sy + 8) ->
atail_vis SEGS W memT (x + astr_len sx) -> atail_vis SEGS W memT (y + astr_len sy) ->
rt_rom_view SEGS B W memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len sy sx)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hbx Hry Hby Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (proj1 (proj2 (cmd_rec_cells lyc Sc W memT mdc (proj1 HJ)))) as HG.
apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md
own lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len sy sx))) HJ Hsp Hal Hneg ltac:(lia) Hbud
Hra (fun a F => False_ind _ F)).
apply (AS lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.

Lemma aj_strspn_at : forall pc, astrspn_realizes SEGS B pc 0xa7098 0x6045d8 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
astr_at SEGS W memT x sx -> astr_at SEGS W memT y sy ->
aread_ok SEGS (2 * ESTACK) W regsT memT x (astr_len sx + 1) -> amem_range x (astr_len sx + 8) ->
aread_ok SEGS (2 * ESTACK) W regsT memT y (astr_len sy + 1) -> amem_range y (astr_len sy + 8) ->
atail_vis SEGS W memT (x + astr_len sx) -> atail_vis SEGS W memT (y + astr_len sy) ->
rt_rom_view SEGS B W memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (PSpn.spn_len sy sx)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hbx Hry Hby Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (proj1 (proj2 (cmd_rec_cells lyc Sc W memT mdc (proj1 HJ)))) as HG.
apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md
own lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PSpn.spn_len sy sx))) HJ Hsp Hal Hneg ltac:(lia) Hbud
Hra (fun a F => False_ind _ F)).
apply (AS lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.
End e.
End f.
End d.

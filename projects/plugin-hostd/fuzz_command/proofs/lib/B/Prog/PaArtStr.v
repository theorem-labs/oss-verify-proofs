(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: journal step rules for the class-7 side-stack entries and the shadow-fill entries, after cgif_rgb_fuzzer's lib/YC05.v (aj_stack_malloc_sz_at, aj_set_shadow_at, aj_stack_free_at, ajournal_after_write_win). The snprintf entry's step is the kit's (lib/A/Prog/PaFx.v aj_art_own_atF) since statement pass 4. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_s0.v, with its module paths and module names changed; 107 of its 146 lines of code are new or changed and 331 lines of the source are left out. *)
(* The strcmp and strncmp wrapper calls of fuzz_command's program walks, as instances of PaArt.v's aj_art_at: the
   contracts of lib/B/Rt/RtString.v:109-138 composed into the caller's journal, stated like cgif_file_fuzzer's
   aj_bcmp_at (lib/Reusable/YCbq.v): the call site's registers, its stack offset [o] below the caller's entry sp,
   and the entry's own premises over the memory at the call. Neither entry writes outside its scratch window, so
   the set of other written bytes is empty. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.

Lemma aj_strcmp_at : forall pc, astrcmp_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
astr_at segs W memT x sx -> astr_at segs W memT y sy ->
aread_ok segs (2 * ESTACK) W regsT memT x (astr_len sx + 1) ->
aread_ok segs (2 * ESTACK) W regsT memT y (astr_len sy + 1) ->
atail_vis segs W memT (x + astr_len sx) -> atail_vis segs W memT (y + astr_len sy) ->
rt_rom_view segs B W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ (getr regs2 10 = w64 0 <-> sx = sy) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hry Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (aj_art_at segs B LAWS segs_low errno_low (2 * ESTACK) (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md own
lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 0 <-> sx = sy) HJ Hsp Hal Hneg ltac:(lia) Hbud Hra
(fun a F => False_ind _ F)).
apply (AS lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at segs B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.

Lemma aj_strncmp_at : forall pc, astrncmp_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n sx sy (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
astr_at segs W memT x sx -> astr_at segs W memT y sy ->
aread_ok segs (2 * ESTACK) W regsT memT x (Z.min n (astr_len sx + 1)) ->
(* 8 bytes of band room past each string (the strncmp contract, RtString.v:128-132) *)
amem_range x (astr_len sx + 8) ->
aread_ok segs (2 * ESTACK) W regsT memT y (Z.min n (astr_len sy + 1)) ->
amem_range y (astr_len sy + 8) ->
atail_vis segs W memT (x + astr_len sx) -> atail_vis segs W memT (y + astr_len sy) ->
rt_rom_view segs B W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(getr regs2 10 = w64 0 <-> StrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n sx sy o raw
HJ Ha0 Ha1 Ha2 Hn Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hmx Hry Hmy Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (aj_art_at segs B LAWS segs_low errno_low (2 * ESTACK) (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md own
lyc Sc mdc k o raw
(fun regs2 _ => getr regs2 10 = w64 0 <-> StrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0)
HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (AS lyc Sc W regsT memT mdc x y n sx sy); try assumption.
apply (ecall_pre_stk_at segs B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.
(* the strspn entry at any pc: the contract (RtString.v, with its gotw / guard cells) applied through aj_art_at, the
   stack-protector guard taken as a premise. One text for the walks' local copies (check_arity_e.v,
   check_words_art.v), which swap to it. *)
Lemma aj_strspn_at : forall pc gotw guard, astrspn_realizes segs B pc gotw guard ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
aguard_ok segs W memT gotw guard ->
astr_at segs W memT x sx -> astr_at segs W memT y sy ->
aread_ok segs (2 * ESTACK) W regsT memT x (astr_len sx + 1) -> amem_range x (astr_len sx + 8) ->
aread_ok segs (2 * ESTACK) W regsT memT y (astr_len sy + 1) -> amem_range y (astr_len sy + 8) ->
atail_vis segs W memT (x + astr_len sx) -> atail_vis segs W memT (y + astr_len sy) ->
rt_rom_view segs B W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (PSpn.spn_len sy sx)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc gotw guard AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hgd Hsx Hsy Hrx Hbx Hry Hby Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (aj_art_at segs B LAWS segs_low errno_low (2 * ESTACK) (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md own
lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PSpn.spn_len sy sx))) HJ Hsp Hal Hneg ltac:(lia) Hbud Hra
(fun a F => False_ind _ F)).
apply (AS lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at segs B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.
(* the strcspn entry at any pc: the contract (RtString.v, with its gotw / guard cells) applied through aj_art_at, the
   stack-protector guard taken as a premise. One text for the walks' local copies (check_arity_e.v,
   check_words_art.v), which swap to it. *)
Lemma aj_strcspn_at : forall pc gotw guard, astrcspn_realizes segs B pc gotw guard ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
aguard_ok segs W memT gotw guard ->
astr_at segs W memT x sx -> astr_at segs W memT y sy ->
aread_ok segs (2 * ESTACK) W regsT memT x (astr_len sx + 1) -> amem_range x (astr_len sx + 8) ->
aread_ok segs (2 * ESTACK) W regsT memT y (astr_len sy + 1) -> amem_range y (astr_len sy + 8) ->
atail_vis segs W memT (x + astr_len sx) -> atail_vis segs W memT (y + astr_len sy) ->
rt_rom_view segs B W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len sy sx)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc gotw guard AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hgd Hsx Hsy Hrx Hbx Hry Hby Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (aj_art_at segs B LAWS segs_low errno_low (2 * ESTACK) (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md own
lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len sy sx))) HJ Hsp Hal Hneg ltac:(lia) Hbud Hra
(fun a F => False_ind _ F)).
apply (AS lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at segs B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.
End e.
End d.

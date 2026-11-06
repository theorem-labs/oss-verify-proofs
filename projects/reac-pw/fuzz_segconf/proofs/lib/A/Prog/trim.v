(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8dfd4) on the ASan build of plugin-hostd/fuzz_command
   proves its statement tchain_words_spec (chain_words_c.v:94-134) directly: from the six segments and the transport
   (chain_words_a.v's cw_run), at statement passes 4 and 5 (the FP-existential post apost_baseF, the rounding-mode
   premise, no astack_pres). The returned block's size is exact in the statement
   (chain_words_c.v:127), as the walk's post cw_Q (chain_words_d.v) carries it from the two recorder callees. The
   callee contracts and runtime rules are the statement's, in its forall-fx0 form (chain_words_c.v:84-93); the
   per-binary facts the walk names are CmdRecFacts lemmas: relro_img and cmd_ro_ok_of_aro (CmdRecRo.v),
   cmd_prog_unowned (CmdRecImg.v), all over IMG : cmd_img_facts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_exact.v, with its module paths and module names changed; 20 of its 39 lines of code are new or changed and 65 lines of the source are left out. *)
(* trim (reac_segconf.c:51-59, static) on the ASan image A of reac-pw/fuzz_segconf (fuzz_segconf.asan, 0x890a8,
   296 bytes, 74 instructions): the walk, trim_walk : trim_contract (lib/A/Prog/trim_c.v, the contract writer's G3 contracts)
   at image A, in plugin-hostd/fuzz_command's lib/A/Prog walk form (afn_pre at the entry, SRr of apost_base at the
   return, over `Context {PI : PAImg seg_listing}`). Written new by the G3 walk owner for trim's walk (no released or
   image-A proof of trim exists: the unit's internal record, commit dfb49d6ad789,
   path records/segp/g3-lookup.md).
   The instantiation: the entry is the listing term BASE + AF_trim (BASE = pa_val A_TEXT, AF_trim = 0x4374, SegList.v:
   image A 0x890a8); STK_trim = 32 + ESTACK, RLO_A = 0xa14a0, RHI_A = 0xa3748 (SegInstA.v, the image-A owner's unit-wide
   image-A terms).
   The segments, chained here backwards (lib/A/Prog/trim_k.v holds their statements):
     trim_t.v   FIN 0x89190: check 3 (store1 at e), `sb zero,0(a1)`, the epilogue and the return;
     trim_tr.v  TRAIL 0x89148: the trailing-blank loop with check 2 (load1 at e - 1), into FIN;
     trim_s.v   AFTER 0x89120: the strlen call (aj_art_at with ASTRLEN), into TRAIL or FIN;
     trim_l.v   LEAD 0x890e0: the leading-blank loop with check 1 (load1 at s1), into AFTER; and the entry 0x890a8.
   Section hypotheses: ASTRLEN, the interceptor owner's interface row 16 (RtString.astrlen_realizes at the listing's strlen
   trampoline pa_sigma SS___interceptor_trampoline_strlen, image A 0x43a0c), the one callee trim_c.v's head comment
   names; and the record hypothesis TL : PALib B (SegPaLib.v: the shadow-base GOT word and cell are listing objects 0
   and 12, the errno cell is in the image), which fuzz_command's walks take the same way (numberA.v TL). AR_laws is the
   kit's base lemma YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0s YK15 YP09 YI00 YI04 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegInstA trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import trim_k trim_t trim_tr trim_s trim_l.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.
(* the callee's contract: the interceptor owner's interface row 16 at the listing's strlen trampoline *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
(* the record hypothesis: the image's runtime cells the walk reads (SegPaLib.v PALib) *)
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Theorem trim_walk : trim_contract SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Proof.
unfold trim_contract.
intros ly S W regs mem md ch p s HPRE HROD H10 Hp64 HTP HEV.
pose proof (tr_fin_ok B LAWS) as FIN.
pose proof (tr_trail_ok B LAWS FIN) as TRAIL.
pose proof (tr_after_ok B LAWS TL ASTRLEN TRAIL FIN) as AFTER.
pose proof (tr_lead_ok B LAWS AFTER) as LEAD.
exact (tr_entry_ok B LAWS TL LEAD ly S W regs mem md ch p s (conj HPRE (conj HROD (conj H10 (conj Hp64 (conj HTP HEV)))))).
Qed.

End e.
End f.
End d.

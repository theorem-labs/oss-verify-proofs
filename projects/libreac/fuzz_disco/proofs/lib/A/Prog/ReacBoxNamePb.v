(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/rec_canonical.v (a working branch 1d526f2e737) for
   fuzz_command.asan-ubsan (entry 0x897e8, 115 instructions). The malloc wrapper call and its null/abort edge are one
   program call of xmalloc here (0x89814, PCall CS_xmalloc), taken through cl_callS (PaCall.v) with the statement's
   HXMALLOC at the walk's own fx and HSIG (cmd_sig_prog, CmdObj.v: the call target); s0 holds len there, below
   alloc_ceiling, so achain_low gives xmalloc's frame chain, and xmalloc's journal keeps the frame. The copy loop
   keeps i (a4) and o (a3) and recomputes text + i and out + o per byte; ~out (a2), ~text (a5) and text != 0 (a6)
   feed the UBSan checks. The walk is cut at the xmalloc return (0x89818: the empty-line check), the outer head
   (0x8983c), the word-scan head (0x8984c), the word start (0x8989c), the copy head (0x898d0), the tail (0x89954) and
   the store of the terminator (0x8995c, where the empty line enters). Of the seven UBSan trap branches (to the unimp
   at 0x89988) the executor decides six from the seeds' facts: 0x8985c and 0x89860 from text, text + i >= 4096 (the
   block law), 0x898a4, 0x898d0, 0x898f4 and 0x89954 from ~out, ~text >= 2^64 - 1 - CEIL_MAX and o, i <= LMAX; the
   walk refutes 0x89850 (text + i < text) at the branch, since text + i < 2^64. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_canonical.v, with its module paths and module names changed; 1605 of its 1733 lines of code are new or changed and 2250 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacBoxNameSeg5.v, with its module paths and module names changed; 35 of its 73 lines of code are new or changed and 1695 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec DiscoRo DiscoRoList.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ReacBoxName ReacBoxNameCut ReacBoxNameLoops ReacBoxNameAsm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ReacBoxNameSeg1 ReacBoxNameSeg2 ReacBoxNameSeg3Tail ReacBoxNameSeg4 ReacBoxNameSeg5
ReacBoxNameSeg6 ReacBoxNameSeg7 ReacBoxNameSeg8 ReacBoxNameSeg9Asm ReacBoxNameSeg10.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ReacBoxNameL14 ReacBoxNameL23 ReacBoxNameL567.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Hypothesis mc_consts_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ASSF5 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f5) 0xf5.
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis HSBDEC : tsb_dec_spec B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Theorem pb_reac_box_name : treac_box_name_spec B.
Proof.
exact (pb_reac_box_name_of_segs B
  (rbn_seg1 B LAWS TL ML ASM3 TLF SMP)
  (rbn_seg2 B LAWS)
  (rbn_seg3 B LAWS AMEMSET HSBDEC DRO GM HV)
  (rbn_seg4 B LAWS (rbn_l1_fits B LAWS) (rbn_l1_ovf B LAWS))
  (rbn_seg5 B LAWS (rbn_l2_fits B LAWS) (rbn_l2_ovf B LAWS) ABCMP ASTRLEN mc_consts_unowned)
  (rbn_seg6 B LAWS (rbn_l3_fits B LAWS) (rbn_l3_ovf B LAWS))
  (rbn_seg7 B LAWS AMEMSET (rbn_l4_fits B LAWS))
  (rbn_seg8 B LAWS DRO GM HSBDEC (rbn_L5_fits_holds B LAWS) (rbn_L6_fits_holds B LAWS))
  (rbn_seg9 B LAWS AMEMCPY DRO GM HV (rbn_L7_fits_holds B LAWS))
  (rbn_seg10 B LAWS ML ASSF5 ASF FFL)).
Qed.
End h.
End f.
End d.

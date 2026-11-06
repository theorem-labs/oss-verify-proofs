(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v (a walk) and ACa2.v (a class-1 side-stack frame): tnumber_spec of lib/A/Prog/number_c.v, from number's entry (0x8e430) through __asan_stack_malloc_0 and strtol to strtol's return, then numberB.v's n_segB. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberA.v, with its module paths, module names and numbers changed; 1350 of its 1544 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: refuse's walk on reac-pw/fuzz_segconf's ASan image A (fuzz_segconf.asan,
   refuse at 0x88da4), in the form of plugin-hostd/fuzz_command's lib/A/Prog/numberA.v at origin/ossv/recipes
   501c0d516c69 (number: a class-0 side-stack frame released inline): the entry to the call of
   __asan_stack_malloc_0 (0x88e30), the frame and its poisoning, the inline checks of c->refused, c->n_refusals
   and c->reading[0], and the branches up to the snprintf calls (0x88f5c, 0x88f74) and the n_refusals >= 8 exit
   (0x88efc -> 0x88fc4). The refuse walk, 2026-10-30. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/refuse_a.v, with its module paths and module names changed; 15 of its 54 lines of code are new or changed and 1505 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: refuse (reac-pw/fuzz_segconf, ASan image A fuzz_segconf.asan, refuse at
   0x88da4) against its contract lib/A/Prog/refuse_c.v, in the form of plugin-hostd/fuzz_command's released
   lib/A/Prog walks at origin/ossv/recipes 501c0d516c69. The walk itself is in the segment files:

     refuse_e.v    the entry state ss_r0 and its seed, the canonical release state ss_rel, the state tactics
     refuse_f.v    the functional lemmas (rconf_enc over a reader, SegModel.refuse, the refusal text)
     refuse_pft.v  the snprintf / vsnprintf journal steps and the two format-family bridges
     refuse_r.v    the inline release of the class-0 side-stack frame and the return
     refuse_a.v    the walk: entry, the class-0 take at 0x88e30, the marking, the four inline checks, the
                   n_refusals >= 8 arm and the body (the two snprintf calls, the vsnprintf call, n_refusals++)

   The image-A refuse walk, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegObj SegInstA refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require refuse_a.
Import ListNotations.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
Section e.
Variable B : asyms.
(* the runtime laws refuse's contract names (refuse_c.v's head comment) *)
Hypothesis SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
(* the two interceptor rows refuse calls (the interceptor lane's interface rows 4 and 5) *)
Hypothesis SNP : forall fx0 : YK11.FPState, @RtFormat.asnprintf_realizes fx0 rc SEGS B
  (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis VSNP : forall fx0 : YK11.FPState, @RtPFSeg.seg_avsnprintf_realizes fx0 rc SEGS B
  RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
  (SIGMA SS___interceptor_trampoline_vsnprintf) gotwA guardA.
(* the listing's object addresses: the three literals refuse forms (lib/A/Prog/SegObj.v) *)
Hypothesis OBJ : seg_val_objs (PI := PI).
(* the stack-protector cells at an AR state. Forced by the __asan_stack_malloc_0 call: its post (YCbq.v
   acall_kept) keeps an image byte only outside as_owned_static, and whether the GOT word gotwA and the guard
   guardA are owned statics is a record fact of the listing's runtime record, not yet in this tree. *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotwA guardA.
Theorem refuse_walk :
refuse_contract SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Proof. apply refuse_a.r_walk; assumption. Qed.
End e.
End f.
End d.

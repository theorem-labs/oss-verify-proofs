(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   entry to the memchr call 0x86ef8 (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/A/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ef8; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s1.v, with its module paths, module names and numbers changed; 492 of its 627 lines of code are new or changed and 392 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/mf_entry_1.v, with its module paths and module names changed; 14 of its 52 lines of code are new or changed and 589 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin sha256 c3796c0b38f3666f32a3ecff43c9fdb55ead356833af6013a07c404bd0254509,
   unstripped twin 80e82127e8ca; 0x86140, 3,608 bytes): the segment S_MF_ENTRY of its walk, `S_MF_ENTRY_ok`, against the
   fixed cut statements of lib/B/Prog/m_file_m.v (S_MF_ENTRY B = (forall n, MF_HEAD_F B n) -> MF_EXIT_F B ->
   MF_ENTRY_F B). A walk lane of the image-B m_file-family owner's G2B. This file only joins the two halves; it executes no
   instruction itself.

   THE SEGMENT (the image-B m_file segment table section 1, the image-B m_file cut map section 4): 0x86140-0x86374 and 0x86e84-0x86ebc,
   157 instructions. It is cut once inside, at the snprintf return 0x862ac (lib/B/Prog/mf_entry_d.v: MFE_MID,
   MFE_MID_stmt, MFE_MID_F), because the snprintf wrapper returns at its own FP state, so the half after it is
   proved at every FP state:
     mf_entry_1.v (with mf_entry_1c.v, mf_entry_1s.v, mf_entry_1b.v)  0x86140 -> 0x862ac, 92 instructions
       (0x86140-0x862a8 and the `unimp` 0x86e84): mfe_entry_F : ... -> MFE_MID_F B -> MF_ENTRY_F B;
     mf_entry_2.v  0x862ac -> HEAD 0x86378 / EXIT 0x86da0, 65 instructions (0x862ac-0x86374 and the slow paths
       0x86e88-0x86ebc): mfe_mid_F : ... -> (forall n, MF_HEAD_F B n) -> MF_EXIT_F B -> MFE_MID_F B.
   The model and byte-encoding lemmas are lib/B/Prog/mf_entry_m.v; the snprintf call's premise bundle is
   lib/B/Prog/mf_entry_k.v.

   ADAPTED from image A's lanes of the same segment by the image-A m_file-family lane (commit dab7f3ccb5c5,
   lib/A/Prog/m_file_s_entry_m.v; commit 6019db533ca0, lib/A/Prog/m_file_s_entry_k.v) and from
   plugin-hostd/fuzz_command's released class-1 frame walk (lib/A/Prog/check_reply_k.v cr_entry, check_reply_s1.v,
   check_reply_s4.v at origin/ossv/recipes 501c0d516c69); the snprintf step after the shared lib/B/Prog/m_file_sn.v.

   UBSAN TRAP BRANCHES (both to the one `unimp` 0x86e84; the trap instruction is never executed):
     0x8626c `bnez a0` (a0 = c & 3, 0x86248): not taken. m_file_pre's `c mod 16 = 0` is the alignment fact
       mkAF 4096 (2 ^ 47 - 8) 4 on a0's atom in the entry seed, so the executor computes c & 3 = 0 (mf_entry_1.v).
     0x862d4 `blt a0,a1` (a0 = gen + 1 by addiw, a1 = gen): not taken. m_file_pre's `mc_gen mc + 1 < 2 ^ 31` and
       mf_entry_m.v's mf_mconf_gen (0 <= gen) are the fact 0 <= gen <= 2 ^ 31 - 2 on gen's atom (mf_entry_2.v).
   INSTRUMENTED CHECKS (a load of the shadow byte at (a >> 3) + the shadow base and a compare; the error path, a call
   of an errpath_* entry, is not reached; all three in mf_entry_2.v):
     0x862c0 (load4 of c->gen, error path 0x86e94) and 0x862dc (store4 of gen + 1, error path 0x86eac): the block's
       shadow entry from mf_core's sa_addr c SEG_M_SIZE (m_file_sd.v mf_she_blk);
     0x862f0 (load1 of *text, error path 0x86ebc): the text's shadow entry from mf_loop's sa_addr t (|s| + 1)
       (m_file_sd.v mf_she_at).
   CALLS: frame_alloc_1 0x861b4 (`__asan_stack_malloc_1`, stepped by PaCall.v aj_stack_malloc_atS with SM1, SMP,
     ML; only the side-stack branch is walked: 0x861ac reads AR's constant use-after-return cell 1, and 0x861c8
     `bnez s7` is taken because the frame address is at least 4096); the snprintf trampoline 0x862a8 (stepped by
     mf_entry_1s.v mfe_snp_step over the row below, srr_after_artF / aj_art_own_atF / srr_art_postF_of_pf).

   SECTION HYPOTHESES (Print Assumptions below lists exactly these and the standard axioms):
     VOBJS  seg_val_objs: the listing's objects against image B's addresses (the literals "%s" / "reac-pw.conf",
            m_key.words, the frame descriptor, the GOT words);
     TL, TLF  PALib B, PALibF B: the shadow GOT word / cell and the use-after-return GOT word / cell are A_OBJ 0 /
            12 / 1 (image B 0xa3210 / 0xac7b8 / 0xa3268), and the frame request's call target;
     ML, SM1, SMP  the kit's model laws, astack_malloc_realizes 1 and stack_malloc_progressP B (the frame call);
     ASNP  the owner's corrected snprintf row: RtPFSeg.seg_asnprintf_realizes at RtPFCmd.CMD_IMG_LO / _HI /
            CMD_SNP_CR, pc = SIGMA SS___interceptor_trampoline_snprintf, RtPFCmd.CMD_GOTW, RtAPI.A_SSP_GUARD;
     SSP   m_file_k.v's stack-protector hypothesis (sa_ssp at every AR state at SegInstB.gotwA / guardA), taken as
            image A's m_file walk takes it.

   POSITIONAL NAMES checked against image B's own lib/B/Prog/SegAddr.v seg_objs and the twin's .symtab by address
   and anchor symbol: A_OBJ 0 = 0xa3210, 1 = 0xa3268, 10 = 0x1d8fe (the frame descriptor), 11 = 0x86140 (m_file),
   12 = 0xac7b8 (__asan_shadow_memory_dynamic_address), 13 = 0x210a0 "reac-pw.conf", 14 = 0x21080 "%s",
   15 = 0xa2040 (m_key.words); the 17 frame-cell offsets, 6 mconf struct offsets and 3 cut offsets against B.s's own
   stores and immediates; none points elsewhere. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibF SegObj SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_entry_d mf_entry_1 mf_entry_2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFSeg RtPFCmd RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.

(* the segment: the half 0x862ac -> HEAD / EXIT gives the cut 0x862ac at every FP state, the half
   0x86140 -> 0x862ac gives the entry from it *)
Lemma S_MF_ENTRY_ok : S_MF_ENTRY (rc := rc) (SK := SK) (PI := PI) B.
Proof.
unfold S_MF_ENTRY. intros HEAD EXIT.
exact (mfe_entry_F B VOBJS TL TLF ML SM1 SMP ASNP SSP (mfe_mid_F B VOBJS HEAD EXIT)).
Qed.
(* inside the Sections: the segment's hypotheses as its assumptions *)
About S_MF_ENTRY_ok.
Print Assumptions S_MF_ENTRY_ok.
End i.
End h.
End g.
About S_MF_ENTRY_ok.
Print Assumptions S_MF_ENTRY_ok.

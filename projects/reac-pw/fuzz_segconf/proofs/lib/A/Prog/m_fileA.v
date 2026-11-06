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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s1.v, with its module paths, module names and numbers changed; 375 of its 436 lines of code are new or changed and 466 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_entry_2.v, with its module paths and module names changed; 52 of its 83 lines of code are new or changed and 405 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc, 4,496 bytes): its walk, the contract of lib/A/Prog/m_file_c.v at
   the entry BASE + AF_m_file and image A's pure parameters (lib/A/Prog/SegInstA.v), at the current FP state.
   The close of the G2 walk owner's m_file walk.

   No instruction is executed here. The walk is cut into the thirteen segments of lib/A/Prog/m_file_m.v
   (S_MF_ENTRY, EXIT, TAIL, FRONT, LONGP, HDRA, HDRB, KEYA, KROLE, KMOD, KIGNP, KKNOCKP, KDONE; the G2 walk owner's
   cut guide MF-CUTS-A.md, sections 2-4), each proved in its own file:
     s_mf_entry   lib/A/Prog/m_file_s_entry.v
     s_mf_exit    lib/A/Prog/m_file_s_exit.v
     s_mf_tail    lib/A/Prog/m_file_s_tail.v
     s_mf_kdone   lib/A/Prog/m_file_s_tail.v
     s_mf_front   lib/A/Prog/m_file_s_front.v
     s_mf_longp   lib/A/Prog/m_file_s_long.v
     s_mf_kknockp lib/A/Prog/m_file_s_kknock.v
     s_mf_hdra    lib/A/Prog/m_file_s_hdra.v
     s_mf_hdrb    lib/A/Prog/m_file_s_hdrb.v
     s_mf_keya    lib/A/Prog/m_file_s_keya.v
     s_mf_krole   lib/A/Prog/m_file_s_krole.v
     s_mf_kmod    lib/A/Prog/m_file_s_kmod.v
     s_mf_kignp   lib/A/Prog/m_file_s_kign.v
   and m_file_m.v's m_file_contract_of_parts joins them (the line loop by induction on the bound on the text left,
   mf_heads; the contract at every FP state from MF_ENTRY_F, m_file_contract_of_entry).

   SECTION HYPOTHESES: the union of the segments' hypotheses, each in the exact text the segments state it
   (the G2 walk owner's shared list): the listing's objects and program symbols (VOBJS, SIGP), the walk records
   (TL, TLF), the stack guard (SSP), the relro window (RELRO), the kit's model laws (ML), the class-1 side-stack
   frame (ASM, SMP; its inline release ASF, FFL), the interceptors snprintf (row 4), strchr (row 6), strlen (row 16),
   memchr (row 20, the constant window form, with MCROM), bcmp, the checked memcpy / memset, and the program callees
   m_refuse, ieq, m_find, fuzz_catalogue_row at their contracts. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegPaLib PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
  ieq_c m_refuse_c m_find_c fuzz_catalogue_row_c m_file_c m_file_m m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require
  m_file_s_entry m_file_s_exit m_file_s_tail m_file_s_front m_file_s_long m_file_s_hdra m_file_s_hdrb
  m_file_s_keya m_file_s_krole m_file_s_kmod m_file_s_kign m_file_s_kknock.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the walk records, the listing's objects and program symbols, the stack guard, the relro window *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
(* the kit's model laws and the class-1 side-stack frame: its request (0x85f30) and its inline release (0x86ec8) *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* the interceptors at the listing's trampolines and the checked memcpy / memset, at every FP state *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) SegInstA.gotwA SegInstA.guardA.
Hypothesis ASTRCHR : forall fx0 : YK11.FPState, @RtSeg.astrchr_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstA.memchr_loA SegInstA.memchr_hiA (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis MCROM : memchr_rom_fact SEGS B.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
(* the program callees at their contracts, at every FP state *)
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis M_FIND : forall fx0 : YK11.FPState, m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find)
  SegInstA.STK_m_find SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis FCR : forall fx0 : YK11.FPState, fuzz_catalogue_row_contract (fx := fx0) SEGS B (BASE + AF_fuzz_catalogue_row)
  SegInstA.STK_fuzz_catalogue_row SegInstA.RLO_A SegInstA.RHI_A SegInstA.catA.

Theorem m_file_walk : m_file_contract SEGS B (BASE + AF_m_file) SegInstA.STK_m_file SegInstA.RLO_A SegInstA.RHI_A
  SegInstA.seg_litA_fz SegInstA.wordsA SegInstA.rolesA SegInstA.catA SegInstA.gotwA SegInstA.guardA.
Proof.
apply (m_file_contract_of_parts B).
- apply m_file_s_entry.s_mf_entry; assumption.
- exact (m_file_s_exit.s_mf_exit B VOBJS ML ASF FFL).
- exact (m_file_s_tail.s_mf_tail B VOBJS).
- exact (m_file_s_front.s_mf_front B TL ASTRCHR ASTRLEN).
- exact (m_file_s_long.s_mf_longp B SIGP SSP RELRO M_REFUSE).
- exact (m_file_s_hdra.s_mf_hdra B VOBJS SIGP SSP RELRO AMEMCHR MCROM IEQ M_REFUSE).
- exact (m_file_s_hdrb.s_mf_hdrb B VOBJS SIGP SSP RELRO M_FIND M_REFUSE AMEMCPY AMEMSET).
- exact (m_file_s_keya.s_mf_keya B SIGP SSP RELRO M_REFUSE AMEMCHR MCROM).
- exact (m_file_s_krole.s_mf_krole B TL VOBJS SIGP SSP RELRO ASNPRINTF ASTRLEN ABCMP M_REFUSE IEQ).
- exact (m_file_s_kmod.s_mf_kmod B VOBJS SIGP SSP RELRO AMEMCPY M_REFUSE IEQ FCR).
- exact (m_file_s_kign.s_mf_kignp B VOBJS SIGP SSP RELRO IEQ ASNPRINTF M_REFUSE).
- exact (m_file_s_kknock.s_mf_kknockp B VOBJS SIGP SSP RELRO IEQ M_REFUSE).
- exact (m_file_s_tail.s_mf_kdone B VOBJS).
Qed.
(* inside the Sections: the Section hypotheses as the theorem's assumptions *)
About m_file_walk.
Print Assumptions m_file_walk.
End e.
End f.
End d.
(* closed: the hypotheses are arguments; only the standard axioms remain *)
About m_file_walk.
Print Assumptions m_file_walk.

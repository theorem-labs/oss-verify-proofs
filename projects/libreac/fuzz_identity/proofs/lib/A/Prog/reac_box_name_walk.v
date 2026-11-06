(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:358-361
   [Apache-2.0]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/IngestWalk.v; 47 of its 81 lines of code are new or changed and 333 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import WrapRo StrlenDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
reac_box_name_L1 reac_box_name_L2 reac_box_name_L3 reac_box_name_L4 reac_box_name_L5 reac_box_name_L6
reac_box_name_L7.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
reac_box_name_seg1 reac_box_name_seg2 reac_box_name_seg3 reac_box_name_seg4 reac_box_name_seg5
reac_box_name_seg6 reac_box_name_seg7 reac_box_name_seg8 reac_box_name_seg9 reac_box_name_seg10.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Section walk.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI)}.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM3 : astack_malloc_realizes SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IS___interceptor_trampoline_strlen).
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IS___asan_set_shadow_f5) 245.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis PSIG : ident_prog_sig_ok.
Hypothesis HSB : tsb_dec_spec B.
Theorem pb_reac_box_name : treac_box_name_spec B G.
Proof.
exact (rbn_compose B G
  (reac_box_name_seg1.rbn_seg1 B G TL LAWS ML ASM3 SMP TLF)
  (reac_box_name_seg2.rbn_seg2 B G LAWS)
  (reac_box_name_seg3.rbn_seg3 B G LAWS GM IV AMEMSET PSIG HSB)
  (reac_box_name_seg4.rbn_seg4 B G LAWS (reac_box_name_L1.rbn_l1_fits B LAWS) (reac_box_name_L1.rbn_l1_ovf B LAWS))
  (reac_box_name_seg5.rbn_seg5 B G LAWS (reac_box_name_L2.rbn_l2_fits B LAWS) (reac_box_name_L2.rbn_l2_ovf B LAWS)
     ASTRLEN ABCMP)
  (reac_box_name_seg6.rbn_seg6 B G LAWS (reac_box_name_L3.rbn_l3_fits B LAWS) (reac_box_name_L3.rbn_l3_ovf B LAWS))
  (reac_box_name_seg7.rbn_seg7 B G LAWS AMEMSET (reac_box_name_L4.rbn_l4_fits B LAWS))
  (reac_box_name_seg8.rbn_seg8 B G LAWS HSB PSIG GM (reac_box_name_L5.rbn_l5_fits B LAWS)
     (reac_box_name_L6.rbn_l6_fits B LAWS))
  (reac_box_name_seg9.rbn_seg9 B G LAWS AMEMCPY GM (reac_box_name_L7.rbn_l7_fits B LAWS))
  (reac_box_name_seg10.rbn_seg10 B G LAWS ML ASSF5 ASF FFL)).
Qed.
End walk.
End h.
End f.
End d.

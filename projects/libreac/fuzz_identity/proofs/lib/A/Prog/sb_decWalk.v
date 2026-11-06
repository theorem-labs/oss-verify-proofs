(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147
   [Apache-2.0]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v; 7 of its 53 lines of code are new or changed and 277 lines of the source are left out. *)
(* sb_dec (fuzz_identity.asan 0x83494, AF_sb_dec = 0x2d88): the whole ASan-build walk, composed from the
   three segments against the boundary layer of lib/A/Prog/sb_dec_inv.v (unchanged):
     A 0x83494 .. 0x835f4   lib/A/Prog/sb_dec_A.v, pb_seg_sbd_A
     B 0x835f4 .. 0x836e8   lib/A/Prog/sb_dec_B.v, seg_sbd_B_holds
     C 0x836e8 .. ret       lib/A/Prog/sb_dec_C.v, seg_sbd_C_holds
   pb_sb_dec_of_segs (sb_dec_inv.v) chains them into tsb_dec_spec. The Section hypotheses are exactly the
   union of the three segments': the walk's runtime entries, which
   lib/A/IdentTop.v:32-42 discharges through the link (lib/A/Prog/IdentEntryLink.v:283). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85 YC81 YC4b YC45 YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec sb_dec_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec_A sb_dec_B sb_dec_C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Theorem pb_sb_dec : tsb_dec_spec B.
Proof.
exact (pb_sb_dec_of_segs B
  (pb_seg_sbd_A B TL LAWS ML ASM0 SMP FFL TLF)
  (seg_sbd_B_holds B LAWS)
  (seg_sbd_C_holds B LAWS ML ASF FFL)).
Qed.
End h.
End f.
End d.

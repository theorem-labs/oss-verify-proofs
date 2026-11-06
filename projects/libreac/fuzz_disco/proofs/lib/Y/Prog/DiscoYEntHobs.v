(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v; 36 of its 74 lines of code are new or changed and 754 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_frame_clean_len_c slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require RoleOf CheckTable CheckSighting ReacHuntObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntHobsCuts DiscoYEntHobsS1 DiscoYEntHobsS2 DiscoYEntHobsS3 DiscoYEntHobsS4 DiscoYEntHobsS5.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis RHYP : d_ro_hyps B.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BSTEP : d_body_step_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BREAD : d_body_read_stmt B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis TROLE : RoleOf.trole_of_spec B.
Hypothesis THOBS : ReacHuntObserve.treac_hunt_observe_spec B.
Hypothesis TCHKS : CheckSighting.tcheck_sighting_spec B.
Hypothesis TCHKT : CheckTable.tcheck_table_spec B.


Theorem pb_hobs : hobs_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
apply (hb_compose B MT XM_LIB RLO RHI tfib_K).
- exact (hb_L1 B MT XM_LIB RLO RHI tfib_K LAWS TL MT_TRIV AIL KCAN SEAT FACTS BTOBS BRT TROLE).
- exact (hb_L2 B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL MT_TRIV AIL KCAN RHYP SEAT FACTS BSTEP BRT BREAD DCRO THOBS).
- exact (hb_L3 B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL MT_TRIV AIL KCAN SEAT FACTS BTOBS BRT TCHKS).
- exact (hb_L4 B MT XM_LIB RLO RHI tfib_K LAWS TL SEAT FACTS BRT).
- exact (hb_L5 B MT XM_LIB RLO RHI tfib_K LAWS TL MT_TRIV AIL KCAN SEAT FACTS BTOBS TCHKT BRT).
Qed.
End h.
End f.
End d.

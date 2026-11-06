(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA2.v, with its module paths and module names changed; 27 of its 79 lines of code are new or changed and 614 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45 YC88 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3JtokSpec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoArm3FieldMDBKit DiscoArm3FieldMDBA DiscoArm3FieldMDBB DiscoArm3FieldMDBC DiscoArm3FieldMDBD.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing} {POV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi FF_got_canary FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA AS___interceptor_trampoline_snprintf).
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis MCRO : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_can_got tfib_K = FF_got_canary /\ ak_canary tfib_K = FF_canary.

Theorem a3f_mdb : forall p, 0 <= p < 8 -> seg_mdb_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp. apply mdb_of_parts.
- apply a3f_mdbA; assumption.
- apply a3f_mdbB; assumption.
- apply a3f_mdbC; assumption.
- apply a3f_mdbD; assumption.
Qed.

End h.
End f.
End d.

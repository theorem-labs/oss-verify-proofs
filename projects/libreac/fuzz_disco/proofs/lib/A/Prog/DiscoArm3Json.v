(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 60 of its 91 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntRec.v, with its module paths changed; 44 of its 77 lines of code are new or changed and 58 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonC2.v, with its module paths changed; 32 of its 78 lines of code are new or changed and 31 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody JsonScalar JtokIs DiscoArm3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonMs DiscoArm3JsonJs
DiscoArm3JsonADefs DiscoArm3JsonA1 DiscoArm3JsonA2 DiscoArm3JsonA3 DiscoArm3JsonA
DiscoArm3JsonB
DiscoArm3JsonC1 DiscoArm3JsonC2 DiscoArm3JsonC3
DiscoArm3JsonDDefs DiscoArm3JsonDA DiscoArm3JsonDB DiscoArm3JsonDC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ASS00 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_00) 0.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis tjsc_roimg : tjson_scalar_roimg.
Hypothesis TJSC : tjson_scalar_spec B.
Hypothesis TJTOK : tjtok_is_spec B.

Theorem a3_json : a3_json_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  pose proof (d_seat B MT XM_LIB RLO RHI tfib_K) as DSEAT.
  pose proof (d_facts_ok B MT XM_LIB RLO RHI tfib_K) as DFACTS.
  pose proof (d_land B MT XM_LIB RLO RHI tfib_K) as DLAND.
  pose proof (d_body_rt B) as DBRT.
  pose proof (d_body_call_keep B MT XM_LIB RLO RHI tfib_K) as DBCK.
  assert (MSS : ms_step_stmt B MT XM_LIB RLO RHI tfib_K) by (eapply ms_step; eassumption).
  assert (JSC : jsc_step_stmt B MT XM_LIB RLO RHI tfib_K) by (eapply jsc_step; eassumption).
  apply a3_json_of_parts.
  - eapply a3j_A; eassumption.
  - eapply a3j_B; eassumption.
  - apply jseg_C_of_parts.
    + eapply a3j_C1; eassumption.
    + eapply a3j_C2; eassumption.
    + eapply a3j_C3; eassumption.
  - apply jseg_D_of_parts; [eapply a3j_D_A; eassumption | eapply a3j_D_B; eassumption
                           | eapply a3j_D_C; eassumption].
Qed.

End h.
End f.
End d.

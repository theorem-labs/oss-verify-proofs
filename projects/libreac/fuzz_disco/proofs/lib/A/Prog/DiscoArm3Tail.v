(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v; 288 of its 341 lines of code are new or changed and 443 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3TailT1.v, with its module names changed; 34 of its 77 lines of code are new or changed and 298 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ReacHuntStep CheckTable ReacHuntVerdictName ReacHuntRole ReacHuntHeardAnything.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoRo DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBodyCall DiscoArm3 DiscoArm3TailDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoArm3TailTA DiscoArm3TailT1 DiscoArm3TailT2 DiscoArm3TailT3 DiscoArm3TailT4 DiscoArm3TailT5 DiscoArm3TailT6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) pa_relro_lo pa_relro_hi}.
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
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Hypothesis ASSF8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f8) 0xf8.
Hypothesis DUNIV : duniv_ok B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis THSTEP : treac_hunt_step_spec B.
Hypothesis TCHKT : tcheck_table_spec B.
Hypothesis TVNAME : treac_hunt_verdict_name_spec B.
Hypothesis THROLE : treac_hunt_role_spec B.
Hypothesis THHEARD : treac_hunt_heard_anything_spec B.

Theorem a3_tail : a3_tail_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  pose proof (d_seat B MT XM_LIB RLO RHI tfib_K) as DSEAT.
  pose proof (d_facts_ok B MT XM_LIB RLO RHI tfib_K) as DFACTS.
  pose proof (d_land B MT XM_LIB RLO RHI tfib_K) as DLAND.
  pose proof (d_body_pcall B MT XM_LIB RLO RHI tfib_K) as DBPC.
  pose proof (d_body_free B MT XM_LIB RLO RHI tfib_K) as DBFREE.
  assert (DROH : d_ro_hyps B) by (split; [exact DRO | split; [exact GM | exact HV]]).
  apply (a3_tail_of_parts B MT XM_LIB RLO RHI tfib_K).
  - apply (a3t_TA B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T1 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T2 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T3 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T4 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T5 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T6 B MT XM_LIB RLO RHI tfib_K); assumption.
Qed.

End h.
End f.
End d.

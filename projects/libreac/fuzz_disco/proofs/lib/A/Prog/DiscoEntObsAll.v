(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v; 15 of its 54 lines of code are new or changed and 949 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0s YP09 YI16 YM05 YG0f YG0d YCbq YC5d YCbp YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoSyms DiscoList DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntObsCuts DiscoEntObs DiscoEntObs2 DiscoEntObs3 DiscoEntObs3b DiscoEntObs4 DiscoEntObs89
FindEntry CheckTable ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TFIND : tfind_entry_spec B.
Hypothesis TCHK : tcheck_table_spec B.
Hypothesis TTOBS : treac_disco_table_observe_spec B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis DCAN : asink_img_laws SEGS B tfib_K /\ ak_canary tfib_K = AE2k.FF_canary.

Theorem pb_obs_spec : obs_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
apply (obs_of_parts B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL FFL MT_TRIV TFIND TCHK TTOBS DCAN).
- exact (ob_s23 B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL FFL MT_TRIV).
- exact (ob_s45 B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL FFL).
- exact (ob_s67 B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL FFL).
- exact (ob_s89 B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL).
- apply (ob_seg9r_of B MT XM_LIB RLO RHI tfib_K).
  + exact (ob_s9a B MT XM_LIB RLO RHI tfib_K LAWS TL FFL ABCMP).
  + exact (ob_s9b B MT XM_LIB XN_LIB RLO RHI tfib_K LAWS TL FFL).
- exact (ob_s10 B MT XM_LIB RLO RHI tfib_K LAWS TL FFL ABCMP).
Qed.

End h.
End f.
End d.

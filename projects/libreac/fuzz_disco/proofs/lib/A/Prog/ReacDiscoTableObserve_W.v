(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 167 of its 204 lines of code are new or changed and 32 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacDiscoTableObserve_X.v; 24 of its 64 lines of code are new or changed and 164 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ReacDiscoTableObserve_E ReacDiscoTableObserve_L2
ReacDiscoTableObserve_P ReacDiscoTableObserve_K0 ReacDiscoTableObserve_K1 ReacDiscoTableObserve_K2 ReacDiscoTableObserve_K3 ReacDiscoTableObserve_K4 ReacDiscoTableObserve_K5 ReacDiscoTableObserve_K6 ReacDiscoTableObserve_Q ReacDiscoTableObserve_F ReacDiscoTableObserve_N.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Theorem pb_reac_disco_table_observe : treac_disco_table_observe_spec B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t s ow now T G.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30
  H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42.
change (SRr SEGS (tW (mkTC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t s ow now T G))
  (cfg_at (fx := fq) SEGS (BASE + AF_reac_disco_table_observe)
     (tregs (mkTC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t s ow now T G))
     (tmemc (mkTC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t s ow now T G))
     (tmdc (mkTC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t s ow now T G)))
  (tpost (fx := fq) B (mkTC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t s ow now T G))).
eapply (seg_pro (fx := fq)).
all: repeat first
  [ exact LAWS | exact TL | exact AMEMCPY | exact (AMEMCPY fq) | exact AMEMSET | exact (AMEMSET fq)
  | exact ABCMP | exact (ABCMP fq)
  | constructor; assumption
  | eapply (seg_loop_full (fx := fq)) | eapply (seg_found (fx := fq)) | eapply (seg_none (fx := fq))
  | eapply (seg_new (fx := fq)) | eapply (seg_K1 (fx := fq)) | eapply (seg_K2 (fx := fq))
  | eapply (seg_K3 (fx := fq)) | eapply (seg_K4 (fx := fq)) | eapply (seg_K5 (fx := fq))
  | eapply (seg_K6 (fx := fq)) | eapply (seg_seq (fx := fq)) | eapply (seg_ret (fx := fq)) ].
Qed.
End h.
End f.
End d.

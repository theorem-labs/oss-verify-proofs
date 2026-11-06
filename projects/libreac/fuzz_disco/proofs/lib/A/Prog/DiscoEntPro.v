(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 1700 of its 1728 lines of code are new or changed and 41 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProD.v; 23 of its 73 lines of code are new or changed and 1678 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntProCuts DiscoEntProSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ReacDiscoTableInit ReacDiscoGateInit ReacDiscoPeerLockInit ReacHuntInit ReacHuntPin ReacHuntSilenceProven.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC88 YC85s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntProA DiscoEntProB DiscoEntProC DiscoEntProD DiscoEntProE.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
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
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASM6 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 6.
Hypothesis ASSF8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f8) 0xf8.
Hypothesis AMALLOC : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis DUNIV : duniv_ok B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TTI : treac_disco_table_init_spec B.
Hypothesis TGI : treac_disco_gate_init_spec B.
Hypothesis TLI : treac_disco_peer_lock_init_spec B.
Hypothesis THI : treac_hunt_init_spec B.
Hypothesis THP : treac_hunt_pin_spec B.
Hypothesis THS : treac_hunt_silence_proven_spec B.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis CANH : d_can_hyps B tfib_K.
Theorem pb_pro : pro_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
apply pro_of_segs.
- eapply pb_proA; first [eassumption | exact (proj2 CANH)].
- eapply pb_proB; eassumption.
- eapply pc_segC; eassumption.
- eapply pb_proD; eassumption.
- eapply pb_proE; eassumption.
Qed.
End h.
End f.
End d.

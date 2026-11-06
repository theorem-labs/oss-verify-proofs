(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 577 of its 632 lines of code are new or changed and 1223 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProD1.v, with its module names changed; 14 of its 53 lines of code are new or changed and 593 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntProCuts DiscoYEntProDCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require
ReacDiscoTableInit ReacDiscoGateInit ReacDiscoPeerLockInit ReacHuntInit ReacHuntPin ReacHuntSilenceProven.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoYEntProD1 DiscoYEntProD2 DiscoYEntProD3.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TTINIT : ReacDiscoTableInit.treac_disco_table_init_spec B.
Hypothesis TGINIT : ReacDiscoGateInit.treac_disco_gate_init_spec B.
Hypothesis TLINIT : ReacDiscoPeerLockInit.treac_disco_peer_lock_init_spec B.
Hypothesis THINIT : ReacHuntInit.treac_hunt_init_spec B.
Hypothesis TPIN : ReacHuntPin.treac_hunt_pin_spec B.
Hypothesis TSIL : ReacHuntSilenceProven.treac_hunt_silence_proven_spec B.
Theorem pb_proD : pro_segD B MT XM_LIB RLO RHI tfib_K.
Proof.
  apply pd_of_segs.
  - exact (DiscoYEntProD1.pb_proD1 B MT XM_LIB RLO RHI tfib_K LAWS TL MT_TRIV TTINIT TGINIT TLINIT).
  - exact (DiscoYEntProD2.pb_proD2 B MT XM_LIB RLO RHI tfib_K LAWS TL MT_TRIV THINIT).
  - exact (DiscoYEntProD3.pb_proD3 B MT XM_LIB RLO RHI tfib_K LAWS TL MT_TRIV TPIN TSIL).
Qed.
End h.
End f.
End d.

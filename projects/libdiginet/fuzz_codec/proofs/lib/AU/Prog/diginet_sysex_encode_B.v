(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 7 of its 34 lines of code are new or changed and 213 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_sysex_encode_A_1.v, with its module paths and module names changed; 46 of its 72 lines of code are new or changed and 8 lines of the source are left out. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgWalkU CPgWalkIntrU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_sysex_encode_B_0
  diginet_sysex_encode_B_1 diginet_sysex_encode_B_2 diginet_sysex_encode_B_3 diginet_sysex_encode_B_4 diginet_sysex_encode_B_5 diginet_sysex_encode_B_6 diginet_sysex_encode_B_7 diginet_sysex_encode_B_8.
Import ListNotations.
Open Scope Z_scope.

(* diginet_sysex_encode (image B 0x85174) against cdcU_sysex_specX: the walk at each payload length 0 .. 24
   (diginet_sysex_encode_B_1 .. _8), joined here. The premises are the kit's laws and the contract of
   __asan_memcpy (image B 0x51ae8), which the walk calls at 0x852e0 when 0 < n <= 19. The function takes no
   side-stack frame. *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Section c.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy CB_MEMCPY.
Lemma sx_all : forall nn, (nn <= 24)%nat -> sx_case B MT nn.
Proof using MTL TL LAWS ML AMEMCPY.
intros nn Hnn.
destruct nn as [|nn]; [apply sx_case_0; assumption|].
destruct nn as [|nn]; [apply sx_case_1; assumption|].
destruct nn as [|nn]; [apply sx_case_2; assumption|].
destruct nn as [|nn]; [apply sx_case_3; assumption|].
destruct nn as [|nn]; [apply sx_case_4; assumption|].
destruct nn as [|nn]; [apply sx_case_5; assumption|].
destruct nn as [|nn]; [apply sx_case_6; assumption|].
destruct nn as [|nn]; [apply sx_case_7; assumption|].
destruct nn as [|nn]; [apply sx_case_8; assumption|].
destruct nn as [|nn]; [apply sx_case_9; assumption|].
destruct nn as [|nn]; [apply sx_case_10; assumption|].
destruct nn as [|nn]; [apply sx_case_11; assumption|].
destruct nn as [|nn]; [apply sx_case_12; assumption|].
destruct nn as [|nn]; [apply sx_case_13; assumption|].
destruct nn as [|nn]; [apply sx_case_14; assumption|].
destruct nn as [|nn]; [apply sx_case_15; assumption|].
destruct nn as [|nn]; [apply sx_case_16; assumption|].
destruct nn as [|nn]; [apply sx_case_17; assumption|].
destruct nn as [|nn]; [apply sx_case_18; assumption|].
destruct nn as [|nn]; [apply sx_case_19; assumption|].
destruct nn as [|nn]; [apply sx_case_20; assumption|].
destruct nn as [|nn]; [apply sx_case_21; assumption|].
destruct nn as [|nn]; [apply sx_case_22; assumption|].
destruct nn as [|nn]; [apply sx_case_23; assumption|].
destruct nn as [|nn]; [apply sx_case_24; assumption|].
lia.
Qed.
End c.
Theorem diginet_sysex_encode_B_holds : aintrin_realizes tfibsegs B OCpy CB_MEMCPY ->
  cdcU_sysex_specX tfibsegs B MT 0x85174.
Proof using MTL TL LAWS ML.
intros AMEMCPY. unfold cdcU_sysex_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs dev fn pl n out bs before
  HE Hdev Hfn H12 H13 Hn Hn24 H14 H4 HPL HOUT.
exact (sx_all AMEMCPY (length bs) ltac:(lia) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs dev fn pl n out bs
  before HE Hdev Hfn H12 H13 Hn Hn24 H14 H4 HPL HOUT Hn).
Qed.
End b.

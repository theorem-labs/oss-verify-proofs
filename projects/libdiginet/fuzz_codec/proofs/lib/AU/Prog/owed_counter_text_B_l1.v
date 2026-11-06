(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v, with its module paths and module names changed; 20 of its 45 lines of code are new or changed and 686 lines of the source are left out. *)
(* Segment L1 of owed_counter_text's walk in image B: one pass of the first loop, from its three parts
   (owed_counter_text_B_l1_a.v, _b.v, _e.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_inv owed_counter_text_B_s0_a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_s0 owed_counter_text_B_l1_base.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_l1_e owed_counter_text_B_l1_a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_l1_b.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SEG7 : cdcU_owed_seg7_specX tfibsegs B MT RLO RHI GLYPHA ROSTRS B_OSEG7.

Theorem oc_l1_holds : oc_seg_L1 B MT RLO RHI GLYPHA ROSTRS.
Proof.
apply (oc_seg_L1_of_parts B MT RLO RHI GLYPHA ROSTRS).
- exact (oc_part_a_holds B MT RLO RHI GLYPHA ROSTRS LAWS).
- exact (oc_part_b_holds B MT RLO RHI GLYPHA ROSTRS MTL LAWS SEG7).
- exact (oc_part_e_holds B MT RLO RHI GLYPHA ROSTRS LAWS).
Qed.
End d.

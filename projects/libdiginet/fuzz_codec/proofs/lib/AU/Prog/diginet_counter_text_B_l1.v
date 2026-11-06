(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v:26-243 (the harness entry
   segment, tfib_lib_A_seg) at c8557374ad2e for fuzz_knock's ASan image (fuzz_knock.asan, sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118), and the S0/S1 boundary state from the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACf7.v:27-28 (ss_A2). rule 24: no function proved (a port of the released
   cgif_file_fuzzer harness walk structure). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgMain0.v, with its module paths changed; 308 of its 337 lines of code are new or changed and 277 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_counter_text_A_s0.v, with its module paths and module names changed; 15 of its 38 lines of code are new or changed and 314 lines of the source are left out. *)
(* Segment L1 of diginet_counter_text's walk in image B (diginet_counter_text_B_inv.v ct_seg_L1): one pass of the
   first loop, from its three parts (diginet_counter_text_B_l1_base.v ct_seg_L1_of_parts): a, the loop head to the
   call of diginet_seg7 or the dot set (diginet_counter_text_B_l1_a.v); b, the call through diginet_seg7's contract
   and the digit or E_RANGE (diginet_counter_text_B_l1_b.v); c, the next text byte (diginet_counter_text_B_l1_c.v). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_counter_text_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_counter_text_B_l1_base
  diginet_counter_text_B_l1_a diginet_counter_text_B_l1_b diginet_counter_text_B_l1_c.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Variables (B : asyms) (MT : ameter_ops) (RLO RHI SEG7TBL : Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SEG7 : cdcU_seg7_specX tfibsegs B MT RLO RHI SEG7TBL B_SEG7.

Theorem ct_l1_holds : ct_seg_L1 B MT RLO RHI SEG7TBL.
Proof using MTL TL LAWS ML SEG7.
apply ct_seg_L1_of_parts.
- eapply ct_part_a_holds; eassumption.
- eapply ct_part_b_holds; eassumption.
- eapply ct_part_c_holds; eassumption.
Time Qed.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbl.v:141-145 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-148, 156-160 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_A.v, with its module paths and module names changed; 212 of its 260 lines of code are new or changed and 760 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_entry_a.v, with its module paths and module names changed; 19 of its 45 lines of code are new or changed and 234 lines of the source are left out. *)
(* The reader segments RD0 .. RD5 of the image-B walk of LLVMFuzzerTestOneInput (seg_rd_run of
   lib/AU/Prog/codec_bmain_inv.v for the kinds FADER, BUTTON, TOUCH, VPOT, JOG and RING), as one statement over
   the kind; each kind is proved in its own file codec_bmain_rda_<k>.v by the exploration of
   codec_bmain_rdin.v. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require codec_bmain_rda_0 codec_bmain_rda_1
  codec_bmain_rda_2 codec_bmain_rda_3 codec_bmain_rda_4 codec_bmain_rda_5.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem seg_rd_run_0_5 : forall kind, 0 <= kind <= 5 -> seg_rd_run B MT K XM_LIB kind.
Proof.
intros kind Hk.
assert (E : kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5) by lia.
destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]].
- exact (codec_bmain_rda_0.seg_rd0_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rda_1.seg_rd1_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rda_2.seg_rd2_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rda_3.seg_rd3_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rda_4.seg_rd4_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rda_5.seg_rd5_holds B MT K XM_LIB TL LAWS).
Qed.
End b.
End a.

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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_entry_a.v, with its module paths and module names changed; 20 of its 45 lines of code are new or changed and 235 lines of the source are left out. *)
(* The reader segments RD6 .. RD11 of the image-B walk of LLVMFuzzerTestOneInput together: seg_rd_run k of
   lib/AU/Prog/codec_bmain_inv.v for k = 6 .. 11, one file per segment (codec_bmain_rdb_<k>.v, on the shared
   pieces of codec_bmain_rdb_lib.v). The hypotheses are the kit's laws (TfibLib, AR_laws) and the runtime
   contract of __asan_memcpy at image B (RD11 copies the payload into k.bytes). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st CPgTokJU codec_bmain_rdlib codec_bmain_rdin.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_rdb_lib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require
  codec_bmain_rdb_6 codec_bmain_rdb_7 codec_bmain_rdb_8 codec_bmain_rdb_9 codec_bmain_rdb_10 codec_bmain_rdb_11.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy BM_asan_memcpy.

Theorem seg_rdb_holds : forall kind, 6 <= kind <= 11 -> seg_rd_run B MT K XM_LIB kind.
Proof.
intros kind Hk.
assert (H : kind = 6 \/ kind = 7 \/ kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11) by lia.
destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]].
- exact (codec_bmain_rdb_6.seg_rd6_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rdb_7.seg_rd7_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rdb_8.seg_rd8_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rdb_9.seg_rd9_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rdb_10.seg_rd10_holds B MT K XM_LIB TL LAWS).
- exact (codec_bmain_rdb_11.seg_rd11_holds B MT K XM_LIB TL LAWS AMEMCPY).
Qed.
End a.

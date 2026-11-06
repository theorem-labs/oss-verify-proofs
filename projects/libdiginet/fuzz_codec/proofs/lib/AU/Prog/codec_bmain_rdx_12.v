(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbl.v:141-145 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-148, 156-160 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_A.v, with its module paths and module names changed; 586 of its 646 lines of code are new or changed and 748 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_entry.v, with its module names changed; 15 of its 43 lines of code are new or changed and 618 lines of the source are left out. *)
(* Segment RD12 (SCRIBBLE_TEXT) of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v
   seg_rd12): the three parts chained at the two inner cuts of lib/AU/Prog/codec_bmain_rdx_l12.v.
     0x80fa4 .. 0x80fc0  rd12_head (codec_bmain_rdx_12h.v): the test of k.p, diginet_personality_of(1) and SPEC_C24;
     0x80fc0 .. 0x815e0  rd12_ta   (codec_bmain_rdx_12t.v): k.a = fuzz_u8 & 0x7f and text_arg;
     0x815e0 .. 0x82734  rd12_ts   (codec_bmain_rdx_12s.v): the UBSan checks of k.desk, the chars byte at
                                    k.desk + 10, check_text_scribble, k.kind = 9, to ENC9.
   It is the image-A segment lib/A/Prog/codec_amain_rd12.v at image B. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK15 YK18 YK0s YP09 YI00 YI04 YI08 YI09 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgChkU CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_rdx_l12.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_rdx_12h codec_bmain_rdx_12t codec_bmain_rdx_12s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis CTA : cdcU_text_arg_specX tfibsegs B MT BM_text_arg.
Hypothesis CTS : cdcU_check_text_scribble_specX tfibsegs B MT BM_check_text_scribble.

Theorem seg_rd12_holds : seg_rd12 B MT K XM_LIB.
Proof using MTL TL LAWS GM IV CTA CTS ROB.
unfold seg_rd12. intros g pos sp1 ops W2 c2 H.
eapply SRr_bind; [exact (rd12_head B MT K XM_LIB TL LAWS g pos sp1 ops W2 c2 H)|].
intros W3 c3 _ H3.
eapply SRr_bind; [exact (rd12_ta B MT K XM_LIB MTL TL LAWS CTA g pos sp1 ops W3 c3 H3)|].
intros W4 c4 _ H4.
exact (rd12_ts B MT K XM_LIB MTL TL LAWS GM IV CTS g pos sp1 ops W4 c4 H4).
Qed.
End b.
End a.

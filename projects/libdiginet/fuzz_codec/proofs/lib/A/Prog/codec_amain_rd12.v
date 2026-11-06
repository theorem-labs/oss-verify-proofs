(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 14 of its 42 lines of code are new or changed and 195 lines of the source are left out. *)
(* Segment RD12 (SCRIBBLE_TEXT) of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_rd12):
   the three parts chained at the two inner cuts of lib/A/Prog/codec_amain_rd12l.v.
     0x80d70 .. 0x80d8c  rd12_head (codec_amain_rd12h.v): the test of k.p, diginet_personality_of(1) and SPEC_C24;
     0x80d8c .. 0x81294  rd12_ta   (codec_amain_rd12t.v): k.a = fuzz_u8 & 0x7f and text_arg;
     0x81294 .. 0x8210c  rd12_ts   (codec_amain_rd12s.v): the chars byte at k.desk + 10, check_text_scribble,
                                    k.kind = 9, to ENC9. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK15 YK18 YK0s YP09 YI00 YI04 YI08 YI09 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACeh ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_rd12l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_rd12h codec_amain_rd12t codec_amain_rd12s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
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
Hypothesis CTA : cdc_text_arg_specX tfibsegs B MT AM_text_arg.
Hypothesis CTS : cdc_check_text_scribble_specX tfibsegs B MT AM_check_text_scribble.

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

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 18 of its 49 lines of code are new or changed and 192 lines of the source are left out. *)
(* Segment OWE9 (SCRIBBLE) of the image-A walk of LLVMFuzzerTestOneInput: seg_owe 9 of
   lib/A/Prog/codec_amain_inv.v, from the walk for the Control|24 desk (codec_amain_owe9a.v) and the walk for
   the ProControl desk (codec_amain_owe9b.v); a NULL desk is ruled out by inv_owe for this kind. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkIntr CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_owe9a codec_amain_owe9b.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51998.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

Theorem seg_owe9_holds : seg_owe B MT K XM_LIB 9.
Proof using TL LAWS AMEMCPY GM IV ROB.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hkj & Hmo & HC &
  (Hops & _ & c & k & od & Hcur & Hkat & Hrec & Hkk & Hod & Hrc & Hwrc & Hwl & Hwk & Hwd & R23)).
pose proof Hrec as (_ & Hpd & _).
destruct Hpd as [(_ & _ & ->) | [(_ & _ & ->) | (_ & _ & ->)]].
- pose proof (Hod eq_refl). lia.
- exact (o9_walk_c24 B MT K XM_LIB TL LAWS AMEMCPY GM IV g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k
    HJ Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hkk Hrc Hwrc Hwl Hwk Hwd R23).
- exact (o9_walk_pc B MT K XM_LIB TL LAWS AMEMCPY GM IV g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k
    HJ Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hkk Hrc Hwrc Hwl Hwk Hwd R23).
Qed.
End b.
End a.

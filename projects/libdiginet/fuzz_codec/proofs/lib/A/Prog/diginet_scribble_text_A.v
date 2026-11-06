(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v, with its module paths and module names changed; 21 of its 51 lines of code are new or changed and 228 lines of the source are left out. *)
(* diginet_scribble_text in image A (fuzz_codec.asan, 0x85cc4): the segment T of diginet_scribble_text_A_inv.v --
   the store 0x85d64 back to the loop head 0x85d1c or on to the padding 0x85de0 (sc_seg_T).

   The code: a3 := a1 + a5 = o + j, the instrumented check of it, sb t1 at o + j; s0 += t2 (i += d);
   a3 := a0 + s0 = q + i + d, the instrumented check of it, lbu t1 := q[i + d]; a5 += 1; t1 = 0 goes to the
   padding, else j + 1 < n goes back to the loop head and j + 1 = n to the padding.

   The state at 0x85d64 is built over the boundary's own registers (atoms 0 .. 31), the shadow offset (32), and
   three values of its own: 33 the text byte at i + d, 34 the address o + j it writes, 35 the address q + i + d. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_s0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_h.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_t.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_p.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_x.

(* diginet_scribble_text at 0x85cc4 in image A (fuzz_codec.asan): the walk of the function, from its five
   segments. diginet_scribble_text_A_inv.v states each segment and composes them (sc_spec_of_segs); the
   segments are proved in _s0.v (the entry), _h.v and _t.v (the loop), _p.v (the padding by __asan_memset)
   and _x.v (the return). *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Theorem diginet_scribble_text_A_holds :
  aintrin_realizes tfibsegs B OSet 0x51e34 -> cdc_scribble_text_specX tfibsegs B MT 0x85cc4.
Proof.
intros AMEMSET.
change 0x85cc4 with A_ST. apply (sc_spec_of_segs B MT).
- apply ss0_holds; assumption.
- apply sh_holds; assumption.
- apply st_holds; assumption.
- apply sp_holds; assumption.
- apply sx_holds; assumption.
Qed.
End h.
End d.

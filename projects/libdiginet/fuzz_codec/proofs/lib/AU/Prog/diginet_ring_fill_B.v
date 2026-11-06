(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 22 of its 42 lines of code are new or changed and 220 lines of the source are left out. *)
(* diginet_ring_fill at image B (fuzz_codec.asan-ubsan, entry 0x85bf8) against its B contract
   cdcU_ring_fill_specX (lib/AU/Prog/CPgEncU.v). The run is diginet_ring_fill_B_run
   (lib/AU/Prog/diginet_ring_fill_B_walk.v): from a0 = n sign-extended from 32 bits it returns with
   a0 = ring_fill_spec n, writes a1 and a2 and keeps every other register and the memory. CPgEvtLeaf.v's
   leaf_a012_evt / cdc_leaf_evt carry the run into the contract (T = 0, nothing written). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YCeh.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEvtLeaf.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require diginet_ring_fill_B_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem diginet_ring_fill_B_holds : cdcU_ring_fill_specX tfibsegs B MT 0x85bf8.
Proof using MTL LAWS.
unfold cdcU_ring_fill_specX, TB_ring_fill.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n HE [Hn H10].
apply (cdc_leaf_evt tfibsegs YCeh.Hwx_tfa B MT MTL LAWS YCeh.tfib_segs_low); [exact HE|].
apply leaf_a012_evt.
assert (E10 : reg_get regs 10 = Z_to_bv 64 (s32 n)) by exact H10.
rewrite E10.
exact (diginet_ring_fill_B_walk.diginet_ring_fill_B_run n Hn).
Qed.

End d.
End b.

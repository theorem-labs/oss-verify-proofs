(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths changed; 672 of its 728 lines of code are new or changed and 525 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_text_scribble_A.v, with its module paths and module names changed; 26 of its 47 lines of code are new or changed and 707 lines of the source are left out. *)
(* diginet_meter_segments at image B (fuzz_codec.asan-ubsan, entry 0x85f14) against its B contract
   cdcU_meter_segs_specX (lib/AU/Prog/CPgEncU.v).
   The walk is diginet_meter_segments_holds_F (lib/AU/Prog/diginet_meter_segments_F.v), taken under the footprint
   that allows every access: for a mask below 2^16 in a0 the run returns with a0 = DgnLib.v's
   diginet_meter_segments mask, writes a1 and a2 and keeps every other register and the memory. The 14 words hold
   no UBSan check. DgnLib.v's meter_segments_spec_eq says the result is the contract's meter_segments_spec mask, and
   CPgEvtLeaf.v's leaf_a012_evt / cdc_leaf_evt carry the run into the contract. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require diginet_meter_segments_F.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require ExecF.
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

Theorem diginet_meter_segments_B_holds : cdcU_meter_segs_specX tfibsegs B MT 0x85f14.
Proof using MTL LAWS.
unfold cdcU_meter_segs_specX, TB_meter_segs.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs mask HE [Hm H10].
rewrite meter_segments_spec_eq.
apply (cdc_leaf_evt tfibsegs YCeh.Hwx_tfa B MT MTL LAWS YCeh.tfib_segs_low); [exact HE|].
apply leaf_a012_evt.
intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
assert (E10 : reg_get regs 10 = Z_to_bv 64 mask) by exact H10.
rewrite E10.
apply (ExecF.evtF_evt tfibsegs ExecF.RNG_all).
exact (diginet_meter_segments_F.diginet_meter_segments_holds_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4
         a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask Hm).
Qed.

End d.
End b.

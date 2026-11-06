(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Frame MState PropExec Cells Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import SpecFrame SpecLeib WalkL Init SegL FxOut PrintfFmt2 PrintfSeg2.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module MSt := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module APx := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Module PrintfRegs.
Import PrintfFmt2.

Ltac regs_tac XF :=
  let r := fresh "r" in intros r; destruct r;
  cbn [rf_get XF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31];
  first [ rewrite SegL.den_VPz; reflexivity | rewrite PrintfSeg2.den_lit; reflexivity | reflexivity ].

Lemma xf1_regs : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) pc m ro,
  let R := AF.mkR (Z_to_bv 64 0x42264) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x20339) (Z_to_bv 64 139268) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
  forall r, rget (core_of (MSt.MS R F pc fc None m ro)) (reg_of_r5 r) = den (SegL.envW R F fc) (rf_get XF1 r).
Proof. intros until ro. intros R. subst R. regs_tac XF1. Qed.

Lemma xf2_regs : forall (ci szi : int) (sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) pc m ro,
  let R := AF.mkR (Z_to_bv 64 0x422d8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x21e7e) (Z_to_bv 64 4096) (Z_to_bv 64 (to_Z ci)) (Z_to_bv 64 (to_Z szi)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
  forall r, rget (core_of (MSt.MS R F pc fc None m ro)) (reg_of_r5 r) = den (SegL.envW R F fc) (rf_get (XF2 ci szi) r).
Proof. intros until ro. intros R. subst R. regs_tac XF2. Qed.
End PrintfRegs.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import ABase.TwinB.
Import SpecFrame.TwinB SpecLeib.TwinB WalkL.TwinB Init.TwinB SegL.TwinB FxOut.TwinB PrintfFmt2.TwinB PrintfSeg2.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module MSt := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module APx := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Module PrintfRegs.
Import PrintfFmt2.TwinB.PrintfFmt2.

Ltac regs_tac XF :=
  let r := fresh "r" in intros r; destruct r;
  cbn [rf_get XF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31];
  first [ rewrite SegL.TwinB.SegL.den_VPz; reflexivity | rewrite PrintfSeg2.TwinB.PrintfSeg2.den_lit; reflexivity | reflexivity ].

Lemma xf1_regs : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) pc m ro,
  let R := AF.mkR (Z_to_bv 64 0x42bf4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x20400) (Z_to_bv 64 139426) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
  forall r, rget (core_of (MSt.MS R F pc fc None m ro)) (reg_of_r5 r) = den (SegL.TwinB.SegL.envW R F fc) (rf_get XF1 r).
Proof. intros until ro. intros R. subst R. regs_tac XF1. Qed.

Lemma xf2_regs : forall (ci szi : int) (sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) pc m ro,
  let R := AF.mkR (Z_to_bv 64 0x42c68) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x21f1c) (Z_to_bv 64 4096) (Z_to_bv 64 (to_Z ci)) (Z_to_bv 64 (to_Z szi)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
  forall r, rget (core_of (MSt.MS R F pc fc None m ro)) (reg_of_r5 r) = den (SegL.TwinB.SegL.envW R F fc) (rf_get (XF2 ci szi) r).
Proof. intros until ro. intros R. subst R. regs_tac XF2. Qed.
End PrintfRegs.
End TwinB.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closed RUNQ result of the post-read driver leaves, made from
   proofs/cgif/cgif_file_fuzzer/lib/YD2d.v:385 tfib_run_Q (relocated here as lib/Reusable/YD2d.v). For fuzz_preset's
   asan-ubsan image (image B); the asan twin is lib/A/PresetD2runQA.v (lane CwRunqA, 345a4039cd2), and this file is
   its text through port/a2b.py (sha256 b9c3f16342596f93d7e64903139a40399c87c0b7440f92e288113ad664f5a77c, --lib):
   0 code lines differ. STATEMENT only: the proof is lib/AU/PresetD2runQBPf.v. It is apart
   from lib/AU/PresetD2runB.v (whose leaf type run_Q_tfa_cf it concludes) so that PresetD2runB.v does not depend on
   its two premises' files. Nothing in this file is a proof of a function (rule 24: the composition / driver layer of
   a port).
   The premises are other lanes' statements, cited, none copied:
   - lane CwLoopB's loop body PresetD1rB.loop_L_cf_B (lib/AU/PresetD1rB.v, a working branch), arguments
     B xst NR sm iface_room_np, stated at CfParams_preset for every FP state with zero rounding mode (frm_zero); so
     this result is stated there;
   - lane CwRunqm's RUNQM leaf type PresetD2eB.run_QM_tfa_cf (lib/AU/PresetD2eB.v, a working branch
     36ee02d9def), arguments B NP NR (no N_LLVMF any more).
   sm is the program interface's model size map (lib/AU/PresetCfnB.v Section Variable sm) and iface_room_np its
   non-primary room (Section Variable iface_room_np), both quantified here under those names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YD2j YD2i YD1t YD20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1v YD2h YD2f YD1w YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD2runB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetD2eB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetD1rB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
Import ListNotations.
Local Open Scope Z_scope.

(* YD2d.v:385 tfib_run_Q. *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Definition tfib_run_Q_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg)
(B : asyms) (iface_room_np : astate -> Prop)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (NR : ProcInput -> Prop) (sm : list Z -> Z * Z),
YK0o.frm_zero (@YK11.fp_csr fx) -> TfibSyms B ->
PresetD1rB.loop_L_cf_B (LS := LS) B xst NR sm iface_room_np ->
(4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe B))%nat ->
PresetD2eB.run_QM_tfa_cf (LS := LS) B iface_room_np NR ->
run_Q_tfa_cf (LS := LS) B iface_room_np NR.

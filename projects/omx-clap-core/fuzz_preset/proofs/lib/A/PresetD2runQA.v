(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closed RUNQ result of the post-read driver leaves, made from
   proofs/cgif/cgif_file_fuzzer/lib/A/AD2d.v:388 tfib_run_Q (relocated here as lib/A/AD2d.v); B twin lib/YD2d.v:385
   (lane CwRunqB, lib/AU/PresetD2runQB.v). For fuzz_preset's asan image. STATEMENT only: the proof is
   lib/A/PresetD2runQAPf.v. It is apart from lib/A/PresetD2runA.v (whose leaf type run_Q_tfa_cf it concludes) so that
   PresetD2runA.v does not depend on its two premises' files. Nothing in this file is a proof of a function (rule 24:
   the composition / driver layer of a port).
   The premises are other lanes' statements, cited, none copied:
   - lane CwLoopA's loop body PresetD1rA.loop_L_cf_A (lib/A/PresetD1rA.v), arguments B xst NR sm iface_room_np, stated
     at CfParams_preset for every FP state with zero rounding mode (frm_zero); so this result is stated there;
   - lane CwRunqm's RUNQM leaf type PresetD2eA.run_QM_tfa_cf (lib/A/PresetD2eA.v, a working branch
     e8ef6ecc7a47), arguments B NP NR.
   sm is the program interface's model size map (lib/A/PresetCfnA.v Section Variable sm) and iface_room_np its
   non-primary room (Section Variable iface_room_np), both quantified here under those names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD1v AD2h AD2f AD1w ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD2runA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetD2eA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetD1rA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
Import ListNotations.
Local Open Scope Z_scope.

(* AD2d.v:388 tfib_run_Q. *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Definition tfib_run_Q_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg)
(B : asyms) (iface_room_np : astate -> Prop)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (NR : ProcInput -> Prop) (sm : list Z -> Z * Z),
YK0o.frm_zero (@YK11.fp_csr fx) -> TfibSyms B ->
PresetD1rA.loop_L_cf_A (LS := LS) B xst NR sm iface_room_np ->
(4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe B))%nat ->
PresetD2eA.run_QM_tfa_cf (LS := LS) B iface_room_np NR ->
run_Q_tfa_cf (LS := LS) B iface_room_np NR.

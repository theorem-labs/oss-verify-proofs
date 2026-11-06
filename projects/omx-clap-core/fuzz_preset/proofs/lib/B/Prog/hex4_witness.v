(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: instance witnesses for the two walk hypotheses of lib/B/Prog/hex4_x.v hex4_x_holds and
   lib/B/Prog/hex4_mn.v hex4_x_holds_mnI on fuzz_preset's asan-ubsan image B' (#102 pin d663f82d7f48, unstripped twin
   c90d4fa54d43; facts 8f3e7e1a07f1):
   - TL : PALibCore (PI := PI_hex4) B holds at B := TfibB, the image's generated asyms record (lib/Reusable/YD2l.v),
     at the per-function listing instance PI_hex4 (lib/B/PAImg_leaves.v): hex4_B_palib_core. It is derived from
     h-rw-man-5's B' PALib at the whole-program listing (lib/B/PALibB.v exvi_eh_palib): the cells, the allocator pcs
     and the errno environment are the same NAMED values at both listings, each equality closed by vm_compute.
   - LAWS : AR_laws_x rsegs B ARx HL holds at ARx := ARcf rsegs TfibB, HL := cf_head of CfParams_preset
     (lib/B/PALibB.v exvi_eh_laws).
   hex4_B_holds_inst / hex4_B_holds_mnI_inst state both leaf theorems with both hypotheses discharged there.
   Old-pin donor of this file: origin/cold/h-verbs-1-hex4-mn d83df2ff2fa4 (blob 65b86089b1ba; PALibCore closed by
   vm_compute at the old-pin record). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YG00 YG0f YG0d YCbq YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import hex4_xs hex4_xs_mn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_leaves PAImg_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import hex4_x hex4_mn.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog PALibB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
Theorem hex4_B_palib_core : PALibCore (PI := PI_hex4) TB.
Proof.
destruct (palib_core (PI := PAImg_prog.PI_prog_B) TB PALibB.exvi_eh_palib) as [G C GC EN FR ML RB].
assert (V0 : pa_val (PAImg := PI_hex4) (A_OBJ 0) = pa_val (PAImg := PAImg_prog.PI_prog_B) (A_OBJ 0))
  by (vm_compute; reflexivity).
assert (V12 : pa_val (PAImg := PI_hex4) (A_OBJ 12) = pa_val (PAImg := PAImg_prog.PI_prog_B) (A_OBJ 12))
  by (vm_compute; reflexivity).
assert (Sf : pa_sigma (PAImg := PI_hex4) AS___wrap_free = pa_sigma (PAImg := PAImg_prog.PI_prog_B) AS___wrap_free)
  by (vm_compute; reflexivity).
assert (Sm : pa_sigma (PAImg := PI_hex4) AS___wrap_malloc = pa_sigma (PAImg := PAImg_prog.PI_prog_B) AS___wrap_malloc)
  by (vm_compute; reflexivity).
split.
- rewrite V0. exact G.
- rewrite V12. exact C.
- rewrite V0, V12. exact GC.
- exact EN.
- rewrite Sf. exact FR.
- rewrite Sm. exact ML.
- vm_compute. split; reflexivity.
Qed.
Theorem hex4_B_palib_core_sat : exists B, PALibCore (PI := PI_hex4) B.
Proof. exists TB. exact hex4_B_palib_core. Qed.
Theorem hex4_B_holds_inst : forall (SK : YI16.sink_head) (PST : list (Z * Z)),
thex4_leafX SK rsegs TB PST (YG0ncf.ARcf (cp := CP) rsegs TB) (img_sigma AS_hex4).
Proof.
intros SK PST.
exact (hex4_x_holds SK TB PST (YG0ncf.ARcf (cp := CP) rsegs TB) PALibB.exvi_eh_laws hex4_B_palib_core).
Qed.
Theorem hex4_B_holds_mnI_inst : forall (SK : YI16.sink_head) (PST : list (Z * Z)),
thex4_leafXmn SK rsegs TB PST (YG0ncf.ARcf (cp := CP) rsegs TB) (img_sigma AS_hex4).
Proof.
intros SK PST.
exact (hex4_x_holds_mnI SK TB PST (YG0ncf.ARcf (cp := CP) rsegs TB) PALibB.exvi_eh_laws hex4_B_palib_core).
Qed.
End w.

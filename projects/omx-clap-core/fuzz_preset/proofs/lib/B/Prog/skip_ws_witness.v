(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: non-vacuity witness of skip_ws_x.v's Section hypothesis TL: PALibCore at the per-function listing PI_skip_ws holds of the generated asyms record of image B' (the #102 pin d663f82d7f48), lib/Reusable/YD2l.v TfibB (blob 95803a8b9493), each field closed by vm_compute there. RELOCATED from origin/cold/h-verbs-1-skip-union ad1c5072e3e7 (blob b5bf059e2d9f); the errno field cites lib/B/PALibB.v's exvi_eh_errno (computed from the record) instead of the old typed errno address, so this file holds no image numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_leaves PALibB.
Import ListNotations.
Local Open Scope Z_scope.
Theorem skip_ws_palib_core_B {rc : YM05.RunCeil} : PALibCore (PI := PAImg_leaves.PI_skip_ws) YD2l.TfibB.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. vm_compute. discriminate.
- exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PALibB.exvi_eh_errno.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. split; reflexivity.
Qed.

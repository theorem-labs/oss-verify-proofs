(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec StepTac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments.

Lemma img_10040_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
Lemma img_10050_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
Lemma img_10078_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100b0_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100e8_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10120_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10158_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
Lemma img_10190_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
Lemma img_101c8_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
Lemma img_101f0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_10200_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
Lemma img_10238_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
Lemma img_22d48_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142880) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 83956)).
Proof. vm_refl_bv. Qed.
Lemma img_22d70_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_22d78_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 84216)).
Proof. vm_refl_bv. Qed.
Lemma img_22d80_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 105412)).
Proof. vm_refl_bv. Qed.
Lemma img_22d88_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 107308)).
Proof. vm_refl_bv. Qed.
Lemma img_22d90_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_22dd0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 143000) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 475504)).
Proof. vm_refl_bv. Qed.
Lemma img_22dd8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 143008) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 607424)).
Proof. vm_refl_bv. Qed.
Lemma img_22de0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 143016) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 607416)).
Proof. vm_refl_bv. Qed.
Lemma img_22de8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 143024) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 142888)).
Proof. vm_refl_bv. Qed.
Lemma img_22df0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 143032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 142880)).
Proof. vm_refl_bv. Qed.
Lemma img_22df8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 143040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 607400)).
Proof. vm_refl_bv. Qed.
Lemma img_24018_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 147680) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_24020_1 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 147616) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma img_740b8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 606808) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_740c8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 606824) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_740d0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 606832) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_74460_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 607408) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_74488_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 607448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_744a0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 607472) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

(* reloc-zl14c *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec StepTac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.

(* [comment removed for export] *)
Lemma img_10040_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10050_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10078_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100b0_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100e8_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10120_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10158_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10190_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101c8_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101f0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10200_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10238_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21a30_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138152) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 83912)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21a58_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138192) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21a60_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138200) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 84172)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21a68_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138208) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 100684)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21a70_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138216) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 102580)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21a78_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138224) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21ab8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138272) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 470768)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21ac0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138280) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 602688)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21ac8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 602680)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21ad0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 138160)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21ad8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138304) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 138152)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_21ae0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138312) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 602664)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_22d00_4 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142952) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_22d10_1 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142888) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_72da8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602072) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_72db8_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602088) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_72dc0_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602096) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_73150_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602672) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_73178_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602712) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_73190_8 {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602736) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

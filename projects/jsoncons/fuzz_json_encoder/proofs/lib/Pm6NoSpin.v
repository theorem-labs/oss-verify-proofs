(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import SpinAlg NoSpinSite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma src11_no_spin_b : no_spin_b Plain.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma src11_no_spin_site : ~ spin_site_present Plain.M.loaded_segments.
Proof. exact (no_spin_b_sound _ src11_no_spin_b). Qed.

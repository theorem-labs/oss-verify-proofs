(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SpinAlg NoSpinSite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Lemma src11_no_spin_b : no_spin_b Plain.M.loaded_segments = true.
Proof. vmc_refl. Qed.

Lemma src11_no_spin_site : ~ spin_site_present Plain.M.loaded_segments.
Proof. exact (no_spin_b_sound _ src11_no_spin_b). Qed.

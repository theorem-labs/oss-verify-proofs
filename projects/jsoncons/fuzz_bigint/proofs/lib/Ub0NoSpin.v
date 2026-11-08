(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm10NoSpin.v at bde727a7971, with OSSVerify.*.fuzz_json_cursor renamed to OSSVerify.*.fuzz_bigint, images.Plain replaced by images.Ubsan, Plain.M.loaded_segments by Ubsan.M.loaded_segments, and its two lemmas renamed src11_no_spin_b and src11_no_spin_site to ub0_no_spin_b and ub0_no_spin_site, to match this tree's Ub0 prefix for the UBSan build. *)
(* As [Src0NoSpin], for the UBSan build.  The scan reads
   [Ubsan.M.loaded_segments]'s own bytes; nothing about the image is assumed. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import SpinAlg NoSpinSite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].

Lemma ub0_no_spin_b : no_spin_b Ubsan.M.loaded_segments = true.
Proof. vmc_refl. Qed.

Lemma ub0_no_spin_site : ~ spin_site_present Ubsan.M.loaded_segments.
Proof. exact (no_spin_b_sound _ ub0_no_spin_b). Qed.

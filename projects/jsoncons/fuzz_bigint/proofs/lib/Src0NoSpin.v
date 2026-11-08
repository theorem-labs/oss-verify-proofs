(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm10NoSpin.v at bde727a7971, with OSSVerify.*.fuzz_json_cursor renamed to OSSVerify.*.fuzz_bigint and its two lemmas renamed src11_no_spin_b and src11_no_spin_site to src0_no_spin_b and src0_no_spin_site, to match this tree's Src0 prefix for the plain build. *)
(* The plain build's image contains no self-jump word in any read-only
   executable segment, so [srz_spin] is unavailable for it.  The scan below
   reads the image's own bytes: [no_spin_b] fetches every even address of every
   code segment of [Plain.M.loaded_segments] and decodes it, and is reduced by
   [vm_compute]; nothing about the image is assumed. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import SpinAlg NoSpinSite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].

Lemma src0_no_spin_b : no_spin_b Plain.M.loaded_segments = true.
Proof. vmc_refl. Qed.

Lemma src0_no_spin_site : ~ spin_site_present Plain.M.loaded_segments.
Proof. exact (no_spin_b_sound _ src0_no_spin_b). Qed.

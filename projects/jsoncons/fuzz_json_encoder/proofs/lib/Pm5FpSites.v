(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm5FpSites.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Lemma site_9c160 : FPB.inl_step SEGS 0x9c1a8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c164 : FPB.inl_step SEGS 0x9c1ac 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c230 : FPB.inl_step SEGS 0x9c278 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c29c : FPB.inl_step SEGS 0x9c2e4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c2a0 : FPB.inl_step SEGS 0x9c2e8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c314 : FPB.inl_step SEGS 0x9c35c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c454 : FPB.inl_step SEGS 0x9c49c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c458 : FPB.inl_step SEGS 0x9c4a0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9c460 : FPB.inl_step SEGS 0x9c4a8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_be5b4 : FPB.inl_step SEGS 0xbe5fc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_be854 : FPB.inl_step SEGS 0xbe89c 4 [14%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_bebe0 : FPB.inl_step SEGS 0xbec28 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_beb50 : FPB.inl_step SEGS 0xbeb98 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_beac0 : FPB.inl_step SEGS 0xbeb08 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_be8f0 : FPB.inl_step SEGS 0xbe938 4 [14%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_be98c : FPB.inl_step SEGS 0xbe9d4 4 [14%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_ca878 : FPB.inl_step SEGS 0xca8c0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_ca8f0 : FPB.inl_step SEGS 0xca938 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_caa0c : FPB.inl_step SEGS 0xcaa54 4 [22%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cadf0 : FPB.inl_step SEGS 0xcae38 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cae68 : FPB.inl_step SEGS 0xcaeb0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cb1e0 : FPB.inl_step SEGS 0xcb228 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cb304 : FPB.inl_step SEGS 0xcb34c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cb308 : FPB.inl_step SEGS 0xcb350 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cbc8c : FPB.inl_step SEGS 0xcbcd4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cbd04 : FPB.inl_step SEGS 0xcbd4c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cd470 : FPB.inl_step SEGS 0xcd4b8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cd4e8 : FPB.inl_step SEGS 0xcd530 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cd880 : FPB.inl_step SEGS 0xcd8c8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cd8f8 : FPB.inl_step SEGS 0xcd940 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cda14 : FPB.inl_step SEGS 0xcda5c 4 [22%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cd608 : FPB.inl_step SEGS 0xcd650 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cd620 : FPB.inl_step SEGS 0xcd668 4 [10%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cd674 : FPB.inl_step SEGS 0xcd6bc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cbe20 : FPB.inl_step SEGS 0xcbe68 4 [22%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_caf88 : FPB.inl_step SEGS 0xcafd0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_cafa0 : FPB.inl_step SEGS 0xcafe8 4 [10%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_caff8 : FPB.inl_step SEGS 0xcb040 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1046f8 : FPB.inl_step SEGS 0x104740 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_104738 : FPB.inl_step SEGS 0x104780 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_104740 : FPB.inl_step SEGS 0x104788 4 [9%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_143e9c : FPB.inl_step SEGS 0x143ee4 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14402c : FPB.inl_step SEGS 0x144074 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148f40 : FPB.inl_step SEGS 0x148f7c 4 [10%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148f54 : FPB.inl_step SEGS 0x148f90 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148f70 : FPB.inl_step SEGS 0x148fac 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148f74 : FPB.inl_step SEGS 0x148fb0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148f90 : FPB.inl_step SEGS 0x148fcc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148fa8 : FPB.inl_step SEGS 0x148fe4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148fac : FPB.inl_step SEGS 0x148fe8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148fd8 : FPB.inl_step SEGS 0x149014 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148fb4 : FPB.inl_step SEGS 0x148ff0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148fbc : FPB.inl_step SEGS 0x148ff8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148fc8 : FPB.inl_step SEGS 0x149004 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148fcc : FPB.inl_step SEGS 0x149008 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148f84 : FPB.inl_step SEGS 0x148fc0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_148f88 : FPB.inl_step SEGS 0x148fc4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_149a10 : FPB.inl_step SEGS 0x149a4c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14a338 : FPB.inl_step SEGS 0x14a374 4 [10%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14a368 : FPB.inl_step SEGS 0x14a3a4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ada4 : FPB.inl_step SEGS 0x14ade0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14adbc : FPB.inl_step SEGS 0x14adf8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ae1c : FPB.inl_step SEGS 0x14ae58 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ae20 : FPB.inl_step SEGS 0x14ae5c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14addc : FPB.inl_step SEGS 0x14ae18 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14adf4 : FPB.inl_step SEGS 0x14ae30 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152e1c : FPB.inl_step SEGS 0x152e58 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152e20 : FPB.inl_step SEGS 0x152e5c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152e24 : FPB.inl_step SEGS 0x152e60 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152ec4 : FPB.inl_step SEGS 0x152f00 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152f3c : FPB.inl_step SEGS 0x152f78 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_151d8c : FPB.inl_step SEGS 0x151dc8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_151d94 : FPB.inl_step SEGS 0x151dd0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_151d98 : FPB.inl_step SEGS 0x151dd4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_151b44 : FPB.inl_step SEGS 0x151b80 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152604 : FPB.inl_step SEGS 0x152640 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152610 : FPB.inl_step SEGS 0x15264c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152638 : FPB.inl_step SEGS 0x152674 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_152728 : FPB.inl_step SEGS 0x152764 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_15272c : FPB.inl_step SEGS 0x152768 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1526fc : FPB.inl_step SEGS 0x152738 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_15273c : FPB.inl_step SEGS 0x152778 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_151c28 : FPB.inl_step SEGS 0x151c64 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_151c2c : FPB.inl_step SEGS 0x151c68 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_151c30 : FPB.inl_step SEGS 0x151c6c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_153474 : FPB.inl_step SEGS 0x1534b0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_153600 : FPB.inl_step SEGS 0x15363c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_15350c : FPB.inl_step SEGS 0x153548 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_15385c : FPB.inl_step SEGS 0x153898 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm5FpSites.
(* [comment removed for export] *)

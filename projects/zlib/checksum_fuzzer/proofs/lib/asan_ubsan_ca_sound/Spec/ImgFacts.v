(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import ITree Nodes Decode Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import Prelim STree Malloc Gap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.PlainU0 Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ceil_plain : reserved_top (segments_reserved psegs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo.
Proof. rewrite reserved_top_plain, alloc_ceiling_lo_val. vm_compute. discriminate. Qed.
Lemma ceil_ubsan : reserved_top (segments_reserved usegs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo.
Proof. rewrite reserved_top_ubsan, alloc_ceiling_lo_val. vm_compute. discriminate. Qed.
Lemma floor_plain : reserved_top (segments_reserved psegs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR.
Proof. rewrite reserved_top_plain. vm_compute. discriminate. Qed.
Lemma floor_ubsan : reserved_top (segments_reserved usegs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR.
Proof. rewrite reserved_top_ubsan. vm_compute. discriminate. Qed.
(* the image bound that KLink KL_init (so Spec/ModelInv GI_init and Spec/LB_Init
   QI_init) takes at : it puts start_brk far below the vDSO pair. *)
Lemma low_plain : reserved_top (segments_reserved psegs) + brk_aslr_max <= 2 ^ 33.
Proof. rewrite reserved_top_plain. vm_compute. discriminate. Qed.
Lemma low_ubsan : reserved_top (segments_reserved usegs) + brk_aslr_max <= 2 ^ 33.
Proof. rewrite reserved_top_ubsan. vm_compute. discriminate. Qed.
Lemma resv_plain : live_bytes (segments_reserved psegs) <= 2^30.
Proof. rewrite segments_reserved_plain. vm_compute. discriminate. Qed.
Lemma resv_ubsan : live_bytes (segments_reserved usegs) <= 2^30.
Proof. rewrite segments_reserved_ubsan. vm_compute. discriminate. Qed.
Lemma top_pos_plain : 0 < reserved_top (segments_reserved psegs).
Proof. rewrite reserved_top_plain. reflexivity. Qed.
Lemma top_pos_ubsan : 0 < reserved_top (segments_reserved usegs).
Proof. rewrite reserved_top_ubsan. reflexivity. Qed.
Lemma lim_p : 2^31 <= source_alloc_limit. Proof. vm_compute. discriminate. Qed.
Lemma lim_u : 2^31 <= target_alloc_limit. Proof. vm_compute. discriminate. Qed.
Lemma lim_s : 2^31 <= sanitizer_source_limit. Proof. vm_compute. discriminate. Qed.

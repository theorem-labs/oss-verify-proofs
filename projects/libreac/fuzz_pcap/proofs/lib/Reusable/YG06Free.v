(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, image-free and unit-free, for the shared allocator core. The donor
   bounds a class's mapped user area by 2 ^ 31, which it reads out of kUserMapSize * EV_MAX; that holds only while
   EV_MAX <= 8192 (262144 * 8192 = 2 ^ 31). The cap the model itself checks is the free-array offset: the map step
   tests `rg_mapped_user r + map_size <=? kFreeArrayOffset` (YG00.v, kFreeArrayOffset = 0xE0000000). The lemmas
   below state the bound against that cap, so a conclusion stated with them does not depend on EV_MAX's value; the
   only EV_MAX facts used are user_map_fits_free_array, kUserMapSize * EV_MAX < kFreeArrayOffset, and the floor
   ev_max_floor, 2 ^ 12 <= EV_MAX. Both hold at the donor's 8192 and at fuzz_manifest's 11776 alike, and lia
   re-checks them for whatever EV_MAX the core carries. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06.
Local Open Scope Z_scope.

(* The one EV_MAX fact the bound needs: every class's user maps fit below the free array. *)
Lemma user_map_fits_free_array : kUserMapSize * EV_MAX < kFreeArrayOffset.
Proof. unfold kUserMapSize, EV_MAX, kFreeArrayOffset. lia. Qed.

(* The one lower EV_MAX fact: a proof that needs st_nev + 2 <= EV_MAX from a small st_nev uses this, not EV_MAX's value. *)
Lemma ev_max_floor : 2 ^ 12 <= EV_MAX.
Proof. unfold EV_MAX. lia. Qed.

(* The mapped user area of every class is below the free-array offset, whatever EV_MAX is. *)
Lemma mapped_user_le_free_array : forall U pp cc bb s c,
  WfP U pp cc bb s -> 1 <= c <= 31 -> rg_mapped_user (reg s c) < kFreeArrayOffset.
Proof.
  intros U pp cc bb s c W Hc.
  pose proof (mapped_user_bound U pp cc bb s c W Hc) as MB.
  pose proof user_map_fits_free_array as FIT.
  lia.
Qed.

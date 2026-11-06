(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac.
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0xbfe000.

Lemma asan_res_eq : segments_reserved ctbsegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x185000);
   (Z_to_bv 64 0x195000, Z_to_bv 64 0x3d7000);
   (Z_to_bv 64 0x56c000, Z_to_bv 64 0x78000);
   (Z_to_bv 64 0x5e4000, Z_to_bv 64 0x61a000)].
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_len : length (segments_reserved ctbsegs) = 4%nat.
Proof. rewrite asan_res_eq. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => IMG_LO <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= IMG_HI) (segments_reserved ctbsegs).
Proof. rewrite asan_res_eq. unfold IMG_LO, IMG_HI. repeat constructor; cbn [fst snd]; rewrite ?unsigned_lit by lia; lia. Qed.

(* [comment removed for export] *)
Lemma asan_hull_cover : IMG_LO <= IMG_HI /\ forall z, IMG_LO <= z < IMG_HI ->
  exists iv, In iv (segments_reserved ctbsegs) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  rewrite asan_res_eq. unfold IMG_LO, IMG_HI. split; [lia|]. intros z Hz.
  destruct (Z_lt_le_dec z 0x195000); [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x185000); split; [left; reflexivity|]|].
  { cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  destruct (Z_lt_le_dec z 0x56c000); [exists (Z_to_bv 64 0x195000, Z_to_bv 64 0x3d7000); split; [right; left; reflexivity|]|].
  { cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  destruct (Z_lt_le_dec z 0x5e4000); [exists (Z_to_bv 64 0x56c000, Z_to_bv 64 0x78000); split; [right; right; left; reflexivity|]|].
  { cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  exists (Z_to_bv 64 0x5e4000, Z_to_bv 64 0x61a000). split; [right; right; right; left; reflexivity|].
  cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma asan_res_bytes : live_bytes (segments_reserved ctbsegs) = 0xbee000.
Proof. rewrite asan_res_eq. cbn [live_bytes snd]. rewrite !unsigned_lit by lia. reflexivity. Qed.

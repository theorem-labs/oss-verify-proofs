(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0xbcb000.

Lemma asan_res_eq : segments_reserved ctasegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x18a000);
   (Z_to_bv 64 0x19a000, Z_to_bv 64 0x399000);
   (Z_to_bv 64 0x533000, Z_to_bv 64 0x79000);
   (Z_to_bv 64 0x5ac000, Z_to_bv 64 0x61f000)].
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_len : length (segments_reserved ctasegs) = 4%nat.
Proof. rewrite asan_res_eq. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => IMG_LO <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= IMG_HI) (segments_reserved ctasegs).
Proof. rewrite asan_res_eq. unfold IMG_LO, IMG_HI. repeat constructor; cbn [fst snd]; rewrite ?unsigned_lit by lia; lia. Qed.

(* [comment removed for export] *)
Lemma asan_hull_cover : IMG_LO <= IMG_HI /\ forall z, IMG_LO <= z < IMG_HI ->
  exists iv, In iv (segments_reserved ctasegs) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  rewrite asan_res_eq. unfold IMG_LO, IMG_HI. split; [lia|]. intros z Hz.
  destruct (Z_lt_le_dec z 0x19a000); [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x18a000); split; [left; reflexivity|]|].
  { cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  destruct (Z_lt_le_dec z 0x533000); [exists (Z_to_bv 64 0x19a000, Z_to_bv 64 0x399000); split; [right; left; reflexivity|]|].
  { cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  destruct (Z_lt_le_dec z 0x5ac000); [exists (Z_to_bv 64 0x533000, Z_to_bv 64 0x79000); split; [right; right; left; reflexivity|]|].
  { cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  exists (Z_to_bv 64 0x5ac000, Z_to_bv 64 0x61f000). split; [right; right; right; left; reflexivity|].
  cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma asan_res_bytes : live_bytes (segments_reserved ctasegs) = 0xbbb000.
Proof. rewrite asan_res_eq. cbn [live_bytes snd]. rewrite !unsigned_lit by lia. reflexivity. Qed.

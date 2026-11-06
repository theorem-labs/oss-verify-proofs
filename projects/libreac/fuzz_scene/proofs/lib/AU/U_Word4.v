(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the single-byte reads of a 4-byte little-endian store, for the `sw` tag stores of the ASan+UBSan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP09 YO0f YK04 YG0f.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI04 YG0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* A 4-byte little-endian value in memory, read one byte at a time. *)
Lemma val_mem_byte4 : forall segs (m : word -> option byte) a v k,
val_mem segs m a 4 v -> 0 <= v < 2 ^ 32 -> 0 <= k < 4 ->
YP09.mbyte segs m (a + k) = Some (Z_to_bv 8 (Z.shiftr v (8 * k) mod 256)).
Proof.
intros segs m a v k Hm Hv Hk.
assert (Hv4 : 0 <= v < 2 ^ (8 * Z.of_nat 4)) by (change (8 * Z.of_nat 4) with 32; exact Hv).
assert (Hk4 : (Z.to_nat k < 4)%nat) by lia.
unfold val_mem in Hm. pose proof (Hm (Z.to_nat k) Hk4) as Hb.
rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal.
rewrite (le_byte_small v 4 (Z.to_nat k) Hv4 Hk4). rewrite Z2Nat.id by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The same byte through the ASan reader. *)
Lemma val_mem_aview_byte4 : forall segs (H : word -> bool) (m : word -> option byte) a v k,
val_mem segs (mrestrict H m) a 4 v -> 0 <= v < 2 ^ 32 -> 0 <= k < 4 ->
aview segs H m (a + k) = Some (Z.shiftr v (8 * k) mod 256).
Proof.
intros segs H m a v k Hm Hv Hk. unfold aview.
rewrite (val_mem_byte4 segs (mrestrict H m) a v k Hm Hv Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_mod. lia.
Qed.

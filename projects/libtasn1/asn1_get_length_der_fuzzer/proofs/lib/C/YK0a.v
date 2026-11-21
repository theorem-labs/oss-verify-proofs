(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3, module APC's auxv geometry (AUXSZ, AUXV_NULL_IX, AT_RANDOM_VOFF, rseq_z) as projects/cgif/cgif_rgb_fuzzer/proofs/lib/YK0a.v as ported to LPS 727298f3 states it, and the key table of every auxv pair, read off the model's StackLayout.auxv_entries. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
(* The auxv layout the launch writes: [StackLayout.auxv_entries] at 727298f3
   (ARCH_DLINFO's ten pairs first, then [create_elf_tables]'s sixteen, then the
   CONFIG_RSEQ pair, then AT_NULL; [auxv_count] 27 or 29).  It depends on no
   binary.  The consumers (YP0c, UL06/YL06, UO0h/YO0h, UO0i/YO0i, UO0j/YO0j)
   read it by these names. *)
Module APC.
Section q.
(* the run's CONFIG_RSEQ flag as 0 or 1; nothing here pins it *)
Variable rz : Z.
Definition AUXSZ : Z := 432 + 32 * rz.
(* AT_NULL's pair index: no conditional entry precedes index 26, so AT_NULL is
   the only row the flag moves. *)
Definition AUXV_NULL_IX : Z := 26 + 2 * rz.
(** The KEY of every pair, pair index k at byte [16 * k].  musl's
    [get_random_secret] walks the vector from pair 0 to AT_NULL reading every
    key, so a mirror of the vector that names only some pairs stops at the
    first unnamed key.  A key is a literal of [auxv_entries], so naming all of
    them asks nothing of the launch; [AUXV_KEYS_model] is where they are read
    off the model. *)
Definition AUXV_KEYS : list Z :=
[33; 40; 41; 42; 43; 44; 45; 46; 47; 51;
 16; 6; 17; 3; 4; 5; 7; 8; 9; 11;
 12; 13; 14; 23; 25; 31]
++ (if Z.eqb rz 0 then [] else [27; 28]) ++ [0].
(* AT_RANDOM's VALUE word: pair 24, offset 384, value at 392, in both
   CONFIG_RSEQ cases. *)
Definition AT_RANDOM_VOFF : Z := 392.
Lemma AT_RANDOM_key : nth 24 AUXV_KEYS 0 = 25.
Proof. reflexivity. Qed.
Lemma AUXV_NULL_IX_last : AUXV_NULL_IX = AUXSZ / 16 - 1.
Proof.
unfold AUXV_NULL_IX, AUXSZ.
replace (432 + 32 * rz) with ((26 + 2 * rz + 1) * 16) by lia.
rewrite Z.div_mul by lia. lia.
Qed.
Lemma AUXV_KEYS_length : 0 <= rz <= 1 -> Z.of_nat (length AUXV_KEYS) = AUXV_NULL_IX + 1.
Proof.
intros Hr. unfold AUXV_KEYS, AUXV_NULL_IX.
destruct (Z.eqb_spec rz 0) as [->|Hne]; cbn [length app]; lia.
Qed.
(* every key word lies inside the vector, [0, AUXSZ] *)
Lemma auxv_key_range : forall k, 0 <= rz <= 1 -> (k < length AUXV_KEYS)%nat ->
16 * Z.of_nat k + 16 <= AUXSZ.
Proof.
intros k Hr Hk. pose proof AUXV_KEYS_length Hr as L.
unfold AUXSZ. unfold AUXV_NULL_IX in L. lia.
Qed.
End q.
Definition rseq_z (b : bool) : Z := if b then 1 else 0.
Lemma rseq_z_range : forall b, 0 <= rseq_z b <= 1.
Proof. intros [|]; cbn; lia. Qed.
(* the bridge to the model's own size, for every kernel build *)
Lemma AUXSZ_of : forall b, AUXSZ (rseq_z b) = Z.of_nat (StackLayout.auxv_size b).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma AUXV_NULL_IX_of : forall b,
AUXV_NULL_IX (rseq_z b) = Z.of_nat (StackLayout.auxv_count b) - 1.
Proof. intros [|]; vm_compute; reflexivity. Qed.
(* The keys, read off the model rather than retyped, for every launch. *)
Lemma AUXV_KEYS_model : forall la ph entry uid gid hwcap ar ae,
map (fun p => bv_unsigned (fst p)) (StackLayout.auxv_entries la ph entry uid gid hwcap ar ae)
= AUXV_KEYS (rseq_z (StackLayout.la_rseq la)).
Proof.
intros [ehdr c msz [|]] ph entry uid gid hwcap ar ae; vm_compute; reflexivity.
Qed.
End APC.

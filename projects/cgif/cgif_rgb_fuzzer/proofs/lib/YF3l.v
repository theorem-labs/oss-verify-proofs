(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0i YG00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF3v YF3w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3m YF3n YF3o YF3p YF3q YF3r YF3s YF3t YF3u.
Import ListNotations. Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Definition nd_lo (k : Z) : Z := match k with 3 => 584 | 4 => 4232 | 5 => 16648 | 6 => 33288 | _ => 0 end.
Definition nd_hi (k : Z) : Z := match k with 3 => 4096 | 4 => 16384 | 5 => 32768 | 6 => 65536 | _ => 0 end.
Lemma piece_val : forall lo cnt s,
forallb (fun i => zev (fun _ => lo + 8 * Z.of_nat i) CL_hi =? class_id (lo + 8 * Z.of_nat i)) (seq 0 cnt) = true ->
lo <= s < lo + 8 * Z.of_nat cnt -> (s - lo) mod 8 = 0 -> zev (fun _ => s) CL_hi = class_id s.
Proof.
intros lo cnt s SW Hs Hm.
pose proof (Z.div_mod (s - lo) 8 ltac:(img_lia)) as DM.
pose proof (forallb_seq_In _ cnt (Z.to_nat ((s - lo) / 8)) SW ltac:(img_try (img_apply Nat2Z.inj_lt; rewrite Z2Nat.id by (img_apply Z.div_pos; img_lia); img_apply Z.div_lt_upper_bound; img_lia))) as Hp.
cbn beta in Hp. rewrite Z2Nat.id in Hp by (img_try (img_apply Z.div_pos; img_lia)).
replace (lo + 8 * ((s - lo) / 8)) with s in Hp by img_lia. apply Z.eqb_eq in Hp. img_exact Hp.
Qed.
Lemma CL_hi_val : forall k s, 3 <= k <= 6 -> nd_lo k <= s <= nd_hi k -> s mod 8 = 0 -> zev (fun _ => s) CL_hi = class_id s.
Proof.
intros k s Hk Hs Hm.
assert (M8 : forall lo, lo mod 8 = 0 -> (s - lo) mod 8 = 0) by (img_try (intros lo Hlo; rewrite Zminus_mod, Hm, Hlo; img_refl)).
assert (K : k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by img_lia.
destruct K as [->|[->|[->| ->]]]; cbn in Hs.
- img_apply (piece_val 584 440 s sweep3); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
- destruct (Z_lt_le_dec s 10312).
+ img_apply (piece_val 4232 760 s sweep4a); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
+ img_apply (piece_val 10312 760 s sweep4b); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
- destruct (Z_lt_le_dec s 24712).
+ img_apply (piece_val 16648 1008 s sweep5a); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
+ img_apply (piece_val 24712 1008 s sweep5b); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
- destruct (Z_lt_le_dec s 41352); [|img_try (destruct (Z_lt_le_dec s 49416); [|destruct (Z_lt_le_dec s 57480)])].
+ img_apply (piece_val 33288 1008 s sweep6a); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
+ img_apply (piece_val 41352 1008 s sweep6b); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
+ img_apply (piece_val 49416 1008 s sweep6c); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
+ img_apply (piece_val 57480 1008 s sweep6d); [img_try (cbn; img_lia) | img_try (img_apply M8; img_refl)].
Qed.
Lemma CL_lo_val {imgk : img} : forall s, 0 <= s <= 512 -> zev (fun _ => s) CL_lo = class_id s.
Proof.
intros s Hs. pose proof seg1_stops as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ECL & _). rewrite ECL.
cbn [zev zalu_raw]. unfold class_id. replace (s <=? 512) with true by (img_try (symmetry; img_apply Z.leb_le; img_lia)).
rewrite (zcanon_id (s + 31)) by (img_try (unfold M64; img_lia)). rewrite (zcanon_id 5) by (img_try (unfold M64; img_lia)).
img_change (Z.land 5 63) with 5. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 5) with 32. img_apply zcanon_id. unfold M64.
split; [img_try (img_apply Z.div_pos; img_lia) | img_try (img_apply Z.div_lt_upper_bound; img_lia)].
Qed.

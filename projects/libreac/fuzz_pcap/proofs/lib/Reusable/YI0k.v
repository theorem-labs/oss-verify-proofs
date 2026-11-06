(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI0k.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO07 YI0j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma pal_pow_of_bounds : forall s p, 1 <= p <= 8 -> 1 <= s -> (1 < p -> 2 ^ (p - 1) < s) -> s <= 2 ^ p -> pal_pow s = p.
Proof.
intros s p Hp Hs Hlo Hhi. destruct (Z.eq_dec s 1) as [-> | Hs1].
- assert (p = 1) by (destruct (Z.eq_dec p 1); [assumption | exfalso; assert (2 ^ 0 <= 2 ^ (p - 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 0) with 1 in *; specialize (Hlo ltac:(lia)); lia]).
subst p. reflexivity.
- assert (Hlo' : 0 < p -> 2 ^ (p - 1) < s).
{ intros _. destruct (Z.eq_dec p 1) as [-> | Hp1]; [change (2 ^ (1 - 1)) with 1; lia | apply Hlo; lia]. }
rewrite (pal_pow_class p s ltac:(lia) ltac:(intros; lia) Hlo' Hhi). lia.
Qed.
Lemma icl_class : forall k n, 0 <= k <= 16 -> (k = 0 -> n <= 1) -> (0 < k -> 2 ^ (k - 1) < n) -> n <= 2 ^ k -> calcInitCodeLen n = Z.max 2 k + 1.
Proof. intros. unfold calcInitCodeLen. rewrite (np2_class k n) by assumption. destruct (Z.ltb_spec k 3); lia. Qed.
Lemma land_low8_1 : forall x, 0 <= x -> Z.land (x mod 2 ^ 8) 1 = Z.land x 1.
Proof. intros x Hx. rewrite <- (Z.land_ones x 8) by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma test1_false : forall x, (Z.land x 1 =? 0) = true -> flag x 1 = false.
Proof. intros x H. unfold flag. rewrite H. reflexivity. Qed.
Lemma test1_true : forall x, (Z.land x 1 =? 0) = false -> flag x 1 = true.
Proof. intros x H. unfold flag. rewrite H. reflexivity. Qed.
Lemma test1m_false : forall x, 0 <= x -> (Z.land (x mod 2 ^ 8) 1 =? 0) = true -> flag x 1 = false.
Proof. intros x Hx H. rewrite land_low8_1 in H by lia. apply test1_false; assumption. Qed.
Lemma test1m_true : forall x, 0 <= x -> (Z.land (x mod 2 ^ 8) 1 =? 0) = false -> flag x 1 = true.
Proof. intros x Hx H. rewrite land_low8_1 in H by lia. apply test1_true; assumption. Qed.
Definition num_eff (ganim : bool) (rfattr sizeGCT sizeLCT transIndex : Z) : Z :=
let numEff0 := if negb (sizeLCT =? 0) then sizeLCT else sizeGCT in
if ganim && flag rfattr 1 && (numEff0 <=? transIndex) then transIndex + 1 else numEff0.
Lemma num_eff_spec : forall ganim rfattr sgct slct tidx ne0,
ne0 = (if slct =? 0 then sgct else slct) ->
num_eff ganim rfattr sgct slct tidx = (if ganim && flag rfattr 1 && (ne0 <=? tidx) then tidx + 1 else ne0).
Proof. intros ganim rfattr sgct slct tidx ne0 ->. unfold num_eff. destruct (slct =? 0); reflexivity. Qed.

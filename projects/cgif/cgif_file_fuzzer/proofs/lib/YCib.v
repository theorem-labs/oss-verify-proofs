(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP09 YI04 YI00 YK04 YA0i YA0n YG0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0f YC88 YC87.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma cpy_garr8 : forall (segs : list Segment) (H : word -> bool) (mc m' : word -> option byte) (pt fimg w h top lf Wd Hd : Z) (IMG : list Z),
garr8 segs (mrestrict H mc) fimg IMG -> Z.of_nat (length IMG) = Wd * Hd -> 0 < Wd -> 0 <= Hd ->
1 <= w -> 0 <= lf -> lf + w <= Wd -> 1 <= h -> 0 <= top -> top + h <= Hd ->
(forall j kk, 0 <= j < h -> 0 <= kk < w -> aview segs H m' (pt + j * w + kk) = aview segs H mc (fimg + lf + (top + j) * Wd + kk)) ->
garr8 segs (mrestrict H m') pt (YO07.window Wd IMG w h top lf).
Proof.
intros segs H mc m' pt fimg w h top lf Wd Hd IMG HI HIL HWd HHd Hw Hl0 Hlw Hh Ht0 Hth HC.
destruct (window_specZ Wd Hd IMG w h top lf HWd HHd HIL Hw Hl0 Hlw Hh Ht0 Hth) as [WL WN].
intros j Hj. rewrite WL in Hj.
set (k := Z.of_nat j). assert (Hk : 0 <= k < w * h) by lia.
assert (Hkw : 0 <= k / w < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hkm : 0 <= k mod w < w) by (apply Z.mod_pos_bound; lia).
pose proof (Z.div_mod k w ltac:(lia)) as Hdm.
specialize (WN k Hk). replace (Z.to_nat k) with j in WN by lia.
set (bo := (top + k / w) * Wd + lf + k mod w) in WN.
assert (Hbo : 0 <= bo < Z.of_nat (length IMG)) by (subst bo; rewrite HIL; nia).
pose proof (HC (k / w) (k mod w) Hkw Hkm) as Q.
replace (pt + k / w * w + k mod w) with (pt + k) in Q by lia.
replace (fimg + lf + (top + k / w) * Wd + k mod w) with (fimg + bo) in Q by (subst bo; lia).
rewrite (rd_garr8 segs (mrestrict H mc) (aview segs H mc) (fun a => eq_refl) fimg IMG bo HI ltac:(lia) ltac:(lia)) in Q.
rewrite <- WN in Q.
destruct (val_mem1_of_aview segs H m' (pt + k) _ Q) as [Hv Hr]. split; [exact Hv | exact Hr].
Qed.
Lemma fl_tmp_diff : forall (G : YO07.gcfg) (cur b : YO07.frame) w h top left,
YO07.flag (fl_gen3 G cur (Some b)) 2 = true -> fl_dims G cur (Some b) = (w, h, top, left) ->
fl_tmp G cur (Some b) = YO07.window (YO07.g_w G) (YO07.f_img cur) w h top left.
Proof.
intros G cur b w h top left HF HD. unfold fl_tmp, fl_w, fl_h, fl_top, fl_left. rewrite HF, HD. reflexivity.
Qed.

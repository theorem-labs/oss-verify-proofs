(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP09 YI04 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YC4a YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC87.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACik ACil.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
Section e.
Variable B : asyms.
Lemma garr8_keptK : forall lyc Sc (W : world SEGS) (m m' : word -> option byte) slo shi (Er : Z -> Prop) b sz p L,
acall_kept SEGS B lyc Sc W m W m' slo shi Er -> In (b, sz) (ablocks B lyc Sc) ->
b <= p -> p + Z.of_nat (length L) <= b + req_size sz -> (forall a, p <= a < p + Z.of_nat (length L) -> ~ Er a) ->
garr8 SEGS (mrestrict (w_H W) m) p L -> garr8 SEGS (mrestrict (w_H W) m') p L.
Proof.
intros lyc Sc W m m' slo shi Er b sz p L (_ & K2 & _) Hin Hlo Hhi HnE HG.
apply (garr8_aview_kept SEGS (w_H W) (w_H W) m m' p L); [|exact HG].
intros a Ha. replace a with (b + (a - b)) by lia. apply (K2 b sz (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. exact (HnE a Ha).
Qed.
Lemma tout_XD_model : forall (W : world SEGS) (m : word -> option byte) lyc Sc sp1 pt npt (G : YO07.gcfg) (cur bef : YO07.frame)
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx,
cattr = YO07.f_attr cur -> (Z.land cattr 4 <> 0 -> ctidx = YO07.f_ctrans cur) -> cnlp = YO07.f_nlp cur ->
battr = YO07.f_attr bef -> (Z.land battr 4 <> 0 -> btidx = YO07.f_ctrans bef) -> bnlp = YO07.f_nlp bef -> ngp = YO07.g_ngp G ->
(Z.land cattr 1 <> 0 -> garr8 SEGS (mrestrict (w_H W) m) cpal (YO07.f_lpal cur) /\ 3 * cnlp <= Z.of_nat (length (YO07.f_lpal cur)) /\
exists sz, In (cpal, sz) (ablocks B lyc Sc) /\ Z.of_nat (length (YO07.f_lpal cur)) <= req_size sz /\
(pt + npt <= cpal \/ cpal + Z.of_nat (length (YO07.f_lpal cur)) <= pt)) ->
(Z.land battr 1 <> 0 -> garr8 SEGS (mrestrict (w_H W) m) bpal (YO07.f_lpal bef) /\ 3 * bnlp <= Z.of_nat (length (YO07.f_lpal bef)) /\
exists sz, In (bpal, sz) (ablocks B lyc Sc) /\ Z.of_nat (length (YO07.f_lpal bef)) <= req_size sz /\
(pt + npt <= bpal \/ bpal + Z.of_nat (length (YO07.f_lpal bef)) <= pt)) ->
(Z.land cattr 1 = 0 \/ Z.land battr 1 = 0 -> garr8 SEGS (mrestrict (w_H W) m) gpal (YO07.g_gpal G) /\ 3 * ngp <= Z.of_nat (length (YO07.g_gpal G)) /\
exists sz, In (gpal, sz) (ablocks B lyc Sc) /\ Z.of_nat (length (YO07.g_gpal G)) <= req_size sz /\
(pt + npt <= gpal \/ gpal + Z.of_nat (length (YO07.g_gpal G)) <= pt)) ->
tout_XD B W m lyc Sc sp1 pt npt (YO07.cmp_pixel G cur bef) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Proof.
intros W m lyc Sc sp1 pt npt G cur bef gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
Hca Hct Hcn Hba Hbt Hbn Hng HLc HLb HGp mN KN x y Rx Ry.
assert (TR : forall p L sz, In (p, sz) (ablocks B lyc Sc) -> Z.of_nat (length L) <= req_size sz ->
(pt + npt <= p \/ p + Z.of_nat (length L) <= pt) ->
garr8 SEGS (mrestrict (w_H W) m) p L -> garr8 SEGS (mrestrict (w_H W) mN) p L).
{ intros p L sz Hin Hsz Hsep HG. apply (garr8_keptK lyc Sc W m mN _ _ _ p sz p L KN Hin); [lia | lia | | exact HG].
intros a Ha HE. cbn beta in HE. lia. }
change (tcmp_zero (aview SEGS (w_H W) mN) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx x y)
with (YCbr.tcmp_zero (aview SEGS (w_H W) mN) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx x y).
apply (tcmp_zero_model SEGS (mrestrict (w_H W) mN) (aview SEGS (w_H W) mN) (fun a => eq_refl) G cur bef
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx x y Hca Hct Hcn Hba Hbt Hbn Hng); [| | | exact Rx | exact Ry].
- intros Hz. destruct (HLc Hz) as (G0 & L0 & sz & Hin & Hsz & Hsep). split; [exact (TR _ _ sz Hin Hsz Hsep G0) | exact L0].
- intros Hz. destruct (HLb Hz) as (G0 & L0 & sz & Hin & Hsz & Hsep). split; [exact (TR _ _ sz Hin Hsz Hsep G0) | exact L0].
- intros Hz. destruct (HGp Hz) as (G0 & L0 & sz & Hin & Hsz & Hsep). split; [exact (TR _ _ sz Hin Hsz Hsep G0) | exact L0].
Qed.
End e.
Lemma toutV_garr8 : forall (DEC : Z -> Z -> bool) (tv : Z) (H : word -> bool) (m3 m5 : word -> option byte)
(pt bimg w h top lf Wd Hd : Z) (TMP BIMG : list Z),
garr8 SEGS (mrestrict H m3) pt TMP -> Z.of_nat (length TMP) = w * h ->
garr8 SEGS (mrestrict H m3) bimg BIMG -> Z.of_nat (length BIMG) = Wd * Hd -> 0 < Wd -> 0 <= Hd ->
1 <= w -> 0 <= lf -> lf + w <= Wd -> 1 <= h -> 0 <= top -> top + h <= Hd ->
toutV DEC tv w h top lf Wd (aview SEGS H m3) (aview SEGS H m5) pt bimg 0 ->
garr8 SEGS (mrestrict H m5) pt
(map (fun pq => if DEC (fst pq) (snd pq) then fst pq else tv mod 256) (combine TMP (YO07.window Wd BIMG w h top lf))).
Proof.
intros DEC tv H m3 m5 pt bimg w h top lf Wd Hd TMP BIMG HT HTL HB HBL HWd HHd Hw Hl0 Hlw Hh Ht0 Hth TOUT.
destruct (window_specZ Wd Hd BIMG w h top lf HWd HHd HBL Hw Hl0 Hlw Hh Ht0 Hth) as [WL WN].
set (WIN := YO07.window Wd BIMG w h top lf) in *.
set (F := fun pq : Z * Z => if DEC (fst pq) (snd pq) then fst pq else tv mod 256).
assert (Hwh : 0 <= w * h) by nia.
assert (ML : length (map F (combine TMP WIN)) = Z.to_nat (w * h)).
{ rewrite length_map, length_combine, WL. lia. }
intros j Hj. rewrite ML in Hj.
assert (NJ : nth j (map F (combine TMP WIN)) 0 = F (nth j TMP 0, nth j WIN 0)).
{ rewrite (nth_indep _ 0 (F (0, 0))) by (rewrite ML; exact Hj). rewrite map_nth. rewrite combine_nth by (rewrite WL; lia). reflexivity. }
rewrite NJ.
set (k := Z.of_nat j).
assert (Hk : 0 <= k < w * h) by lia.
specialize (WN k Hk). replace (Z.to_nat k) with j in WN by lia.
set (bo := (top + k / w) * Wd + lf + k mod w) in WN.
assert (Hkw : 0 <= k / w < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hkm : 0 <= k mod w < w) by (apply Z.mod_pos_bound; lia).
assert (Hbo : 0 <= bo < Z.of_nat (length BIMG)) by (subst bo; rewrite HBL; nia).
specialize (TOUT (pt + k) ltac:(lia)).
replace ((pt + 0 * w <=? pt + k) && (pt + k <? pt + h * w)) with true in TOUT by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; nia).
replace (pt + k - pt) with k in TOUT by lia. unfold BOF in TOUT. fold bo in TOUT.
rewrite (rd_garr8 SEGS (mrestrict H m3) (aview SEGS H m3) (fun a => eq_refl) pt TMP k HT ltac:(lia) ltac:(lia)) in TOUT.
rewrite (rd_garr8 SEGS (mrestrict H m3) (aview SEGS H m3) (fun a => eq_refl) bimg BIMG bo HB ltac:(lia) ltac:(lia)) in TOUT.
replace (Z.to_nat k) with j in TOUT by lia. rewrite <- WN in TOUT. cbn [trfa] in TOUT.
destruct (val_mem1_of_aview SEGS H m5 (pt + k) _ TOUT) as [Hv Hr].
unfold F. cbn [fst snd]. split; [exact Hv | exact Hr].
Qed.
End d.
End c.

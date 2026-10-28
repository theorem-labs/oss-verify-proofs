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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChd ACje.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07 YI0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC87.
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
Variables (W : world SEGS) (memc : word -> option byte) (fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z).
Variables (G : YO07.gcfg) (cur b : YO07.frame) (N : Z).
Hypothesis Hca : cattr = YO07.f_attr cur. Hypothesis Hct : Z.land cattr 4 <> 0 -> ctidx = YO07.f_ctrans cur. Hypothesis Hcn : cnlp = YO07.f_nlp cur.
Hypothesis Hba : battr = YO07.f_attr b. Hypothesis Hbt : Z.land battr 4 <> 0 -> btidx = YO07.f_ctrans b. Hypothesis Hbn : bnlp = YO07.f_nlp b.
Hypothesis Hng : ngp = YO07.g_ngp G.
Hypothesis HLc : Z.land cattr 1 <> 0 -> garr8 SEGS (mrestrict (w_H W) memc) cpal (YO07.f_lpal cur) /\ 3 * cnlp <= Z.of_nat (length (YO07.f_lpal cur)).
Hypothesis HLb : Z.land battr 1 <> 0 -> garr8 SEGS (mrestrict (w_H W) memc) bpal (YO07.f_lpal b) /\ 3 * bnlp <= Z.of_nat (length (YO07.f_lpal b)).
Hypothesis HGp : Z.land cattr 1 = 0 \/ Z.land battr 1 = 0 -> garr8 SEGS (mrestrict (w_H W) memc) gpal (YO07.g_gpal G) /\ 3 * ngp <= Z.of_nat (length (YO07.g_gpal G)).
Hypothesis HIc : garr8 SEGS (mrestrict (w_H W) memc) fimg (YO07.f_img cur). Hypothesis HLIc : Z.of_nat (length (YO07.f_img cur)) = N.
Hypothesis HIb : garr8 SEGS (mrestrict (w_H W) memc) bimg (YO07.f_img b). Hypothesis HLIb : Z.of_nat (length (YO07.f_img b)) = N.
Lemma PD_model : forall p, 0 <= p < N ->
(PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx p <->
YO07.cmp_pixel G cur b (nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img b) 0) = true).
Proof.
intros p Hp. unfold PD, bval.
rewrite (rd_garr8 SEGS (mrestrict (w_H W) memc) (aview SEGS (w_H W) memc) (fun a => eq_refl) fimg _ p HIc ltac:(lia) ltac:(lia)).
rewrite (rd_garr8 SEGS (mrestrict (w_H W) memc) (aview SEGS (w_H W) memc) (fun a => eq_refl) bimg _ p HIb ltac:(lia) ltac:(lia)).
pose proof (proj2 (HIc (Z.to_nat p) ltac:(lia))) as Rc. pose proof (proj2 (HIb (Z.to_nat p) ltac:(lia))) as Rb.
change (tcmp_zero (aview SEGS (w_H W) memc) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx (nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img b) 0))
with (YCbr.tcmp_zero (aview SEGS (w_H W) memc) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx (nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img b) 0)).
rewrite (tcmp_zero_model SEGS (mrestrict (w_H W) memc) (aview SEGS (w_H W) memc) (fun a => eq_refl) G cur b
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ Hca Hct Hcn Hba Hbt Hbn Hng HLc HLb HGp Rc Rb).
destruct (YO07.cmp_pixel G cur b _ _); split; intros H; [reflexivity | intros X; discriminate X | exfalso; apply H; reflexivity | discriminate H].
Qed.
Variables (Wd Hd : Z).
Hypothesis HW : 1 <= Wd. Hypothesis HH : 1 <= Hd. Hypothesis Hgw : YO07.g_w G = Wd. Hypothesis HN : N = Wd * Hd.
Hypothesis HPX : YO07.px_ne G cur b = YO07.cmp_pixel G cur b.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Lemma PD_D : forall p, 0 <= p < Wd * Hd -> (PDp p <-> YO07.px_ne G cur b (nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img b) 0) = true).
Proof. intros p Hp. rewrite HPX. apply PD_model. rewrite HN. exact Hp. Qed.
Lemma ws_diff_area : forall top bot left right c0,
0 <= top <= bot -> bot < Hd -> 0 <= left <= right -> right < Wd -> 0 <= c0 < Wd ->
PDp (top * Wd + c0) -> (forall p, 0 * Wd <= p < top * Wd -> ~ PDp p) ->
(bot = top \/ exists c1, 0 <= c1 < Wd /\ PDp (bot * Wd + c1)) -> (forall p, (bot + 1) * Wd <= p < (Hd - 1 + 1) * Wd -> ~ PDp p) ->
(exists y', top <= y' <= bot /\ PDp (y' * Wd + left)) -> (forall i x', top <= i <= bot -> 0 <= x' < left -> ~ PDp (i * Wd + x')) ->
(exists y', top <= y' <= bot /\ PDp (y' * Wd + right)) -> (forall i x', top <= i <= bot -> right < x' < Wd -> ~ PDp (i * Wd + x')) ->
YO07.diff_area G cur b = Some (right - left + 1, bot + 1 - top, top, left).
Proof.
intros top bot left right c0 Htb Hb Hlr Hr Hc0 T1 F1 T2 F2 (y3 & Hy3 & T3) F3 (y4 & Hy4 & T4) F4.
replace (right - left + 1) with (right + 1 - left) by lia.
apply (YI0e.diff_area_scan G cur b Wd Hd PDp HW HH Hgw ltac:(rewrite HLIc; exact HN) ltac:(rewrite HLIb; exact HN) PD_D top bot left right Htb Hb Hlr Hr).
- exists c0. split; [exact Hc0 | exact T1].
- intros p Hp. apply F1. lia.
- destruct T2 as [-> | (c1 & Hc1 & T2)]; [exists c0; split; [exact Hc0 | exact T1] | exists c1; split; [exact Hc1 | exact T2]].
- intros p Hp. apply F2. replace (Hd - 1 + 1) with Hd by lia. lia.
- exists y3. split; [lia | exact T3].
- intros i x Hi Hx. apply F3; lia.
- exists y4. split; [lia | exact T4].
- intros i x Hi Hx. apply F4; lia.
Qed.
Lemma ws_diff_none : (forall p, 0 * Wd <= p < Wd * Hd -> ~ PDp p) -> YO07.diff_area G cur b = None.
Proof.
intros F. apply (YI0e.diff_area_ident G cur b Wd Hd PDp HW HH Hgw ltac:(rewrite HLIc; exact HN) ltac:(rewrite HLIb; exact HN) PD_D).
intros p Hp. apply F. lia.
Qed.
End e.
End d.
End c.

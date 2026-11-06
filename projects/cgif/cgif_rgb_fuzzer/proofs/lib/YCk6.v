(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YCpo YCpq YClz YCqd YCqe YCpy YCq3 YCq4 YCq6 YCq5 YP14 YP15 YChh YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCoi YCoj YCok YCol.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YCkr YCks YClv.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP0 : (forall n, rga_fromA B ss_HL (fun _ => INV_HL B n)) -> rga_from B ss_HL0 (INV_A11z B).
Proof.
intros RC. rga_prelude.
destruct HINV as [HINV Hz0]. red in HINV. rga_cbn_cx HINV. rga_cbn_cx Hz0.
destruct HINV as (bs & Hk0 & Hfmt & Eab3 & Hnews & av & E300 & Hav).
destruct Hk0 as [Hk0 Hbud].
unfold news_A9, news_A2, news_A1 in Eab3, Hnews. rga_cbn_cx Eab3. rga_cbn_cx Hnews. cbn [app] in Eab3, Hnews.
cbn [rga_news] in Hnews. destruct bs as [|blk bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rblk & Tblk & Ablk) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|fim bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rfim & Tfim & Afim) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|tb bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rtb & Ttb & Atb) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|fq bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rfq & Tfq & Afq) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|hh bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rhh & Thh & Ahh) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|uu bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Ruu & Tuu & Auu) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|pp bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rpp & Tpp & App) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|xx bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rxx & Txx & Axx) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|? ?]; [|contradiction]. clear Hnews. cbn [combine map snd] in Eab3.
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hfq_in3 : In (fq, 2097236) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 3 right; left; reflexivity).
assert (Hhh_in3 : In (hh, 1572927) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 4 right; left; reflexivity).
assert (Huu_in3 : In (uu, 524309) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 5 right; left; reflexivity).
assert (Hpp_in3 : In (pp, 1572927) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 6 right; left; reflexivity).
assert (Hxx_in3 : In (xx, 2097236) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 7 right; left; reflexivity).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 fq _ HAR3 Hfq_in3 ltac:(clear; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 hh _ HAR3 Hhh_in3 ltac:(clear; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 uu _ HAR3 Huu_in3 ltac:(clear; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 pp _ HAR3 Hpp_in3 ltac:(clear; lia)) as (Hpp4096 & Hppceil & Hpp16 & Hpppres).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 xx _ HAR3 Hxx_in3 ltac:(clear; lia)) as (Hxx4096 & Hxxceil & Hxx16 & Hxxpres).
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil C1; lia).
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil C1; lia).
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil C1; lia).
assert (Bpp : 0 <= pp < 2 ^ 64) by (clear - Hpp4096 Hppceil C1; lia).
assert (Bxx : 0 <= xx < 2 ^ 64) by (clear - Hxx4096 Hxxceil C1; lia).
rewrite Ruu, unsigned_lit_small in Hz0 by exact Buu.
destruct (g_empty_table (w_H W3) (ms_mem ms3) fq hh uu pp xx 524309 ltac:(clear; lia)
ltac:(intros a Ha; apply Hfqpres; clear - Ha; lia) ltac:(intros a Ha; apply Hhhpres; clear - Ha; lia)
ltac:(intros a Ha; apply Hpppres; clear - Ha; lia) ltac:(intros a Ha; apply Hxxpres; clear - Ha; lia) Hz0) as (K0 & HK0T & HK0c & Harr0 & Hinv0).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (Himg_in : In (img, fmt * N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. left.
unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himg_in3 : In (img, fmt * N) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Himg_in).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 img _ HAR3 Himg_in3 ltac:(clear - HfN; lia)) as (Himg4096 & Himgceil & Himg16 & Himgpres).
assert (Bimg : 0 <= img < 2 ^ 64) by (clear - Himg4096 Himgceil HfN C1; lia).
g_slot_set HS (Some 2%nat) (-576) (-488) (SLit 1) ltac:(apply U_inj; rewrite (g_U_sltu0 E 45 img E45 ltac:(clear - Himg4096 Bimg; lia)); reflexivity).
rregU HS (13%bv : bv 5) 0 ltac:(reflexivity) Q13.
rregU HS (15%bv : bv 5) 0 ltac:(reflexivity) Q15.
assert (BF : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
rregU HS (24%bv : bv 5) F ltac:(apply (U_atom _ 54 F RF BF)) Q24.
slot_val HS (Some 305%nat) 0 0 (Z_to_bv 64 fq) ltac:(exact (g_denot_off0 E 337 fq Rfq Bfq)) QF.
slot_val HS (Some 305%nat) 0 8 (Z_to_bv 64 hh) ltac:(exact (g_denot_off0 E 353 hh Rhh Bhh)) QH.
slot_val HS (Some 305%nat) 0 16 (Z_to_bv 64 uu) ltac:(exact (g_denot_off0 E 369 uu Ruu Buu)) QU.
slot_val HS (Some 305%nat) 0 24 (Z_to_bv 64 pp) ltac:(exact (g_denot_off0 E 385 pp Rpp Bpp)) QP.
slot_val HS (Some 305%nat) 0 32 (Z_to_bv 64 xx) ltac:(exact (g_denot_off0 E 401 xx Rxx Bxx)) QX.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 0) ltac:(reflexivity) QC.
slot_val HS (Some 305%nat) 0 44 (Z_to_bv 64 524309) ltac:(reflexivity) QT.
ra_join_slots HS ss_HL 450%nat rga_deads_HL
[(Some 305%nat, 0, 0); (Some 305%nat, 0, 8); (Some 305%nat, 0, 16); (Some 305%nat, 0, 24); (Some 305%nat, 0, 32); (Some 305%nat, 0, 40); (Some 305%nat, 0, 44)]
ltac:(idtac; ga_join_val HS 450%nat 6%nat Q13 N456; ga_join_val HS 450%nat 8%nat Q15 N458; ga_join_val HS 450%nat 17%nat Q24 N467;
ga_join_val HS 450%nat 23%nat QF N473; ga_join_val HS 450%nat 24%nat QH N474; ga_join_val HS 450%nat 25%nat QU N475;
ga_join_val HS 450%nat 26%nat QP N476; ga_join_val HS 450%nat 27%nat QX N477; ga_join_val HS 450%nat 28%nat QC N478; ga_join_val HS 450%nat 29%nat QT N479;
ga_join_fact HS 456%nat (mkAF 0 10000 0) ltac:(rewrite N456; rewrite unsigned_lit_small by (clear; lia); repeat split; first [clear; lia | reflexivity]);
ga_join_fact HS 458%nat (mkAF 0 1 0) ltac:(rewrite N458; rewrite unsigned_lit_small by (clear; lia); repeat split; first [clear; lia | reflexivity]);
ga_join_fact HS 473%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N473; rewrite unsigned_lit_small by exact Bfq; change (2 ^ 4) with 16; split; [clear - Hfq4096 Hfqceil C1; lia|]; split; [exact Hfq16 | clear; lia]);
ga_join_fact HS 474%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N474; rewrite unsigned_lit_small by exact Bhh; change (2 ^ 4) with 16; split; [clear - Hhh4096 Hhhceil C1; lia|]; split; [exact Hhh16 | clear; lia]);
ga_join_fact HS 475%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N475; rewrite unsigned_lit_small by exact Buu; change (2 ^ 4) with 16; split; [clear - Huu4096 Huuceil C1; lia|]; split; [exact Huu16 | clear; lia]);
ga_join_fact HS 476%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N476; rewrite unsigned_lit_small by exact Bpp; change (2 ^ 4) with 16; split; [clear - Hpp4096 Hppceil C1; lia|]; split; [exact Hpp16 | clear; lia]);
ga_join_fact HS 477%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N477; rewrite unsigned_lit_small by exact Bxx; change (2 ^ 4) with 16; split; [clear - Hxx4096 Hxxceil C1; lia|]; split; [exact Hxx16 | clear; lia]);
ga_join_fact HS 478%nat (mkAF 0 16777216 0) ltac:(rewrite N478; rewrite unsigned_lit_small by (clear; lia); repeat split; first [clear; lia | reflexivity]);
ga_join_fact HS 479%nat (mkAF 524309 16777216 0) ltac:(rewrite N479; rewrite unsigned_lit_small by (clear; lia); repeat split; first [clear; lia | reflexivity])).
rga_hand (RC (Z.to_nat N)) HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, 0, 0, K0, (@nil (colour * Z)).
rewrite HK0T, HK0c. change (g_ts_rank 524309) with 0.
split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [rewrite Eab3; unfold cht_blocks; change CHT_SIZE with 48; change (4 * 524309) with 2097236; change (3 * 524309) with 1572927; apply Permutation_refl|].
change (4 * 524309) with 2097236. change (3 * 524309) with 1572927.
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [exact N473 | split; [exact Tfq | exact Afq]]|].
split; [split; [exact N474 | split; [exact Thh | exact Ahh]]|].
split; [split; [exact N475 | split; [exact Tuu | exact Auu]]|].
split; [split; [exact N476 | split; [exact Tpp | exact App]]|].
split; [split; [exact N477 | split; [exact Txx | exact Axx]]|].
split; [exact N478|]. split; [exact N479|]. split; [exact N458|]. split; [left; reflexivity|].
split; [exact N456|]. split; [clear - HN1; lia|]. split; [rewrite Z2Nat.id by (clear - HN1; lia); clear; lia|].
split; [exact Harr0|]. split; [exact Hinv0|]. split; [left; reflexivity|]. split; [cbn; clear; lia|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E300 | exact Hav] | exact N467].
Qed.
End c.
End b.

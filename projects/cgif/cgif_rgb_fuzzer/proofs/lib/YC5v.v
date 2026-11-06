(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk
YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCb2 YCb3 YCb4 YCb5 YCb6 YCbn YCb7 YCba YCbb YCbc YCbd.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_HL0 : rga_fromA B ss_HL0 (fun _ => INV_N B 8 news_A9) -> rga_from B ss_A11 (INV_N B 8 news_A9).
Proof.
intros RC. rga_prelude.
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
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hrin).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x81368 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x80ea8])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; right; right; left; reflexivity).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
srr_branch_tok tratbl_lib_ok HS SHOK GBspan.
-
exfalso. rewrite branch_eq_U in Hc.
lazymatch type of Hc with context [U ?Ex (SMdw _ _ _)] =>
rewrite (U_HW Ex 40 39 Hd Wd) in Hc;
[ | rewrite ?ew_ewset_other by lia; exact E40 | rewrite ?ew_ewset_other by lia; exact E39 | exact R44v | exact R42v
| rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia ];
assert (H0 : U Ex (SLit 0) = 0) by reflexivity; rewrite H0 in Hc end.
apply Z.eqb_eq in Hc. rewrite <- HNhw in Hc. clear - Hc HN1. lia.
- aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x826ac.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
all: try (unfold GBx; ga_obl_cfp HJ3 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join0 HS ss_HL0.
rga_hand RC HS HJ3 k; [rga_E_tac HEE0 | ].
exists [blk; fim; tb; fq; hh; uu; pp; xx]. split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [unfold news_A9, news_A2, news_A1; rga_cbn_cx_goal; cbn [app combine map snd]; exact Eab3|].
split; [ unfold news_A9, news_A2, news_A1; rga_cbn_cx_goal; cbn [app rga_news];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]] | exact I] |].
exists av. split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E300 | exact Hav].
Qed.
End b.
End a.

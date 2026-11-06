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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpo YCpq YClz YCqd YCps YCpt YCpu YCpv YCpw YCpx YCqe YCpy YCm0 YCq1 YCpz YCq0.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_E2h2 : rga_fromA B ss_X38 (fun _ => INV_X38 B) -> rga_fromA B ss_A9 (fun _ => INV_N B 8 news_A9) -> rga_from B ss_A8b (INV_A8b B).
Proof.
intros RX38 RC. rga_prelude.
destruct HINV as (bs & os & Hk0 & Hfmt & Eab3 & Hnews & Hopts & (av & E300 & Hav) & Hnz_fq & Hnz_hh).
destruct Hk0 as [Hk0 Hbud].
try unfold news_A2 in Eab3. try unfold news_A2 in Hnews. try unfold news_A2 in Hopts. try unfold news_A1 in Eab3. try unfold news_A1 in Hnews. try unfold news_A1 in Hopts. try unfold opts_5 in Eab3. try unfold opts_5 in Hnews. try unfold opts_5 in Hopts. try unfold opts_4 in Eab3. try unfold opts_4 in Hnews. try unfold opts_4 in Hopts. try unfold opts_3 in Eab3. try unfold opts_3 in Hnews. try unfold opts_3 in Hopts. try unfold opts_2 in Eab3. try unfold opts_2 in Hnews. try unfold opts_2 in Hopts. try unfold opts_1 in Eab3. try unfold opts_1 in Hnews. try unfold opts_1 in Hopts.
rga_cbn_cx Eab3. rga_cbn_cx Hnews. rga_cbn_cx Hopts. cbn [app] in Eab3, Hnews, Hopts.
cbn [rga_news] in Hnews. destruct bs as [|blk bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rblk & Tblk & Ablk) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|fim bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rfim & Tfim & Afim) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|tb bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rtb & Ttb & Atb) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|? ?]; [|contradiction]. clear Hnews. cbn [combine map snd] in Eab3.
cbn [rga_opts] in Hopts. destruct os as [|fq os]; [contradiction|]. cbn [rga_opts] in Hopts. destruct Hopts as ((Rfq & Hrfq & Hcfq) & Hopts).
cbn [rga_opts] in Hopts. destruct os as [|hh os]; [contradiction|]. cbn [rga_opts] in Hopts. destruct Hopts as ((Rhh & Hrhh & Hchh) & Hopts).
cbn [rga_opts] in Hopts. destruct os as [|uu os]; [contradiction|]. cbn [rga_opts] in Hopts. destruct Hopts as ((Ruu & Hruu & Hcuu) & Hopts).
cbn [rga_opts] in Hopts. destruct os as [|pp os]; [contradiction|]. cbn [rga_opts] in Hopts. destruct Hopts as ((Rpp & Hrpp & Hcpp) & Hopts).
cbn [rga_opts] in Hopts. destruct os as [|xx os]; [contradiction|]. cbn [rga_opts] in Hopts. destruct Hopts as ((Rxx & Hrxx & Hcxx) & Hopts).
cbn [rga_opts] in Hopts. destruct os as [|? ?]; [|contradiction]. clear Hopts. cbn [optl map snd app] in Eab3. rewrite ?app_nil_r in Eab3.
cbn [nth] in Hnz_fq, Hnz_hh.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hrin).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; right; right; left; reflexivity).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
*
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ => assert (Rx : ew Ex 369 = Z_to_bv 64 uu) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu) end.
pose proof (rga_ne_test _ 369 uu true Rx Hruu Hc) as Hnz_uu. cbn beta iota in Hnz_uu. clear Rx Hc.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK GBspan.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
--
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ => assert (Rx : ew Ex 385 = Z_to_bv 64 pp) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp) end.
pose proof (rga_ne_test _ 385 pp true Rx Hrpp Hc) as Hnz_pp. cbn beta iota in Hnz_pp. clear Rx Hc.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK GBspan.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
++
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ => assert (Rx : ew Ex 401 = Z_to_bv 64 xx) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx) end.
pose proof (rga_ne_test _ 401 xx true Rx Hrxx Hc) as Hnz_xx. cbn beta iota in Hnz_xx. clear Rx Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_asan_memset.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join0 HS ss_A9.
rga_hand RC HS HJ3 k; [rga_E_tac HEE0 | ].
exists [blk; fim; tb; fq; hh; uu; pp; xx]. split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [unfold news_A9, news_A2, news_A1; rga_cbn_cx_goal; cbn [app combine map snd]; rewrite Eab3;
rewrite (optb_nz fq _ Hnz_fq), (optb_nz hh _ Hnz_hh), (optb_nz uu _ Hnz_uu), (optb_nz pp _ Hnz_pp), (optb_nz xx _ Hnz_xx); cbn [app]; reflexivity|].
split; [ unfold news_A9, news_A2, news_A1; rga_cbn_cx_goal; cbn [app rga_news];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | exact (Hcfq Hnz_fq)] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | exact (Hchh Hnz_hh)] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | exact (Hcuu Hnz_uu)] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | exact (Hcpp Hnz_pp)] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | exact (Hcxx Hnz_xx)] | exact I] |].
exists av. split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E300 | exact Hav].
++
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843f4.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_X38 500%nat rga_deads_X38 ltac:(idtac).
rga_hand RX38 HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx. split; [split; [rewrite HEVv; clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [cbn [app]; rewrite Eab3; apply Permutation_refl|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Hrfq | exact Hcfq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Hrhh | exact Hchh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Hruu | exact Hcuu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Hrpp | exact Hcpp]] | split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Hrxx | exact Hcxx]]].
--
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843f4.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_X38 500%nat rga_deads_X38 ltac:(idtac).
rga_hand RX38 HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx. split; [split; [rewrite HEVv; clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [cbn [app]; rewrite Eab3; apply Permutation_refl|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Hrfq | exact Hcfq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Hrhh | exact Hchh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Hruu | exact Hcuu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Hrpp | exact Hcpp]] | split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Hrxx | exact Hcxx]]].
*
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843f4.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_X38 500%nat rga_deads_X38 ltac:(idtac).
rga_hand RX38 HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx. split; [split; [rewrite HEVv; clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [cbn [app]; rewrite Eab3; apply Permutation_refl|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Hrfq | exact Hcfq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Hrhh | exact Hchh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Hruu | exact Hcuu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Hrpp | exact Hcpp]] | split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Hrxx | exact Hcxx]]].
Qed.
End b.
End a.

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
YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCb2 YCb3 YCb4 YCb5 YCb6 YCbn YCb7 YCba YCbb YCbc.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_E2j : rga_fromA B ss_A11 (fun _ => INV_N B 8 news_A9) -> rga_from B ss_A10 (INV_N B 8 news_A9).
Proof.
intros RC. rga_prelude. unfold ss_A10 in HS.
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
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; right; right; left; reflexivity).
assert (Huu_in3 : In (uu, 524309) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 5 right; left; reflexivity).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof (req_size_pos (524309) ltac:(clear; lia)) as Hrquu.
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (uu, 524309) HAR3 ltac:(rewrite Eab3; apply Permutation_refl) Hrin ltac:(do 5 right; left; reflexivity)) as HzR_uu.
unfold zdisjoint, block_rng in HzR_uu. cbn [fst snd] in HzR_uu. change (req_size 64) with 64 in HzR_uu.
pose proof (sep_blocks trasegs B LAWS ly3 S3 _ _ _ tb 48 uu (524309) HAR3 Htb_in3 Huu_in3 ltac:(intros Heq; injection Heq as _ Hq; discriminate Hq)) as HdT_uu.
unfold zdisjoint in HdT_uu. cbn [fst snd] in HdT_uu. change (req_size 48) with 48 in HdT_uu.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ uu (524309) HAR3 Huu_in3) as (Huu4096 & Huuzone & Huuceil & Huu16).
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ uu (524309) 7 fpos HAR3 Huu_in3 Hfin3) as HdF_uu.
unfold zdisjoint in HdF_uu. cbn [fst snd] in HdF_uu. change (fs_frame_bytes 7) with 8192 in HdF_uu. rewrite EFA3 in HdF_uu. fold F in HdF_uu.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ uu (524309) cid pos HAR3 Huu_in3 HfinS3) as HdC_uu.
unfold zdisjoint in HdC_uu. cbn [fst snd] in HdC_uu. rewrite EFA3 in HdC_uu.
assert (HnR_uu : forall a, r <= a < r + 64 -> ~ (uu <= a < uu + req_size (524309))) by (intros a Ha Hin; clear - HzR_uu Ha Hin; lia).
assert (HnC_uu : forall a, cfp <= a < cfp + 24 -> ~ (uu <= a < uu + req_size (524309))) by (intros a Ha Hin; clear - HdC_uu Ha Hin Hflo Hfhi; lia).
assert (HnF_uu : forall a, F <= a < F + 8192 -> ~ (uu <= a < uu + req_size (524309))) by (intros a Ha Hin; clear - HdF_uu Ha Hin; lia).
assert (HnS_uu : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (uu <= a < uu + req_size (524309)))
by (intros a Ha Hin; destruct Huuzone as [_ Hbz]; clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1; lia).
gboxh HdF_uu. gboxh HdC_uu. gboxh HzR_uu. gboxh Huuzone. gboxh HdT_uu.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 336460) with (Z_to_bv 64 A_asan_memset).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 _ _ uu 0 (524309) (-512) (Z_to_bv 64 0x82640) HJ3) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact Ruu | rewrite Ruu; reflexivity].
- exact Ra1.
- exact Ra2.
- clear; lia.
- clear - Huu4096. lia.
- clear - Huuceil Hrquu C1. lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (uu + (a - uu)) by lia; apply Auu; [exact Huu_in3 | clear - Ha Hrquu; lia] | unfold ESTACK; clear - Ha Huuceil Hrquu Hceil Hslo FFS; lia].
- apply (amem_range_of_block trasegs B LAWS ly3 S3 _ _ _ uu (524309) uu (524309) HAR3 Huu_in3); [lia | clear - Hrquu; lia].
- apply (range_addressable_of_block trasegs B LAWS ly3 S3 _ _ _ uu (524309) uu (524309) HAR3 Huu_in3); [lia | clear - Hrquu; lia].
- intros _. apply (shadow_hull_vis_of_block trasegs B LAWS ly3 S3 _ _ _ uu (524309) uu (524309) HAR3 Huu_in3); [lia | clear - Hrquu; lia | clear; lia].
- exact I. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Ha06 & Heff6 & Hfr6 & Hpres6).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first [ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply region_kept_aview; [ ga_evalE AG | | exact Hpres6 ];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr6; unfold ESTACK; unfold gbox in HdT_uu; ga_zl1 end
| ga_keptI3 Hfr6 Hpres6 AG HdF_uu HdC_uu HzR_uu Huuzone Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
ga_relow HS AG E10 E11 E10n E11n.
try clear HEEc. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEEc end.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ6 SHOK GBspan 0x82654.
all: try (unfold GBx; ga_obl_blk HJ6 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join0 HS ss_A11.
rga_hand RC HS HJ6 k; [rga_E_tac HEEc | ].
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
End c.
End b.

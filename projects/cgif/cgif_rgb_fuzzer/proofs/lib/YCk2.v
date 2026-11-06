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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YCpo YCpq YClz YCqd YCqe YCpy YCq3 YCq4 YCq6 YCq5 YP14 YP15 YI0d YI0h YChh YCia YCm1 YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCop.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCqg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0f YCd3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YClk YCkr YCks YCkt YCku YCkv YCkw YCkx YClv YClp YCl2 YCky YClq YClb YCl6 YCkz YCl7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YClb.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gH4 : forall (n : nat) (m : nat), rga_fromA B ss_HT (fun _ => INV_HT B (S n) m) -> rga_from B ss_H3 (INV_H3 B (S n) m).
Proof.
intros n m RHT. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & ha & ix & Ht & ent & p1 & p2 & hn & un & fn & K & j & hs & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & Rp1 & Hp1_gp & Rp2 & Hp2_gp & Rhn & Hhn_gp & Run & Hun_gp & Rfn & Hfn_gp & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R755 & HTlt & HKT & HKarr & HKinv & Rj & Rj4 & Rj3 & Hj & Hmj & Huv1 & Hhs & HKfree & HKcnt1 & HKins & Rhs).
pose proof Hp1_gp as Hp1_perm. pose proof Hp2_gp as Hp2_perm. pose proof Hhn_gp as Hhn_perm. pose proof Hun_gp as Hun_perm. pose proof Hfn_gp as Hfn_perm.
unfold g_perm in Hp1_perm, Hp2_perm, Hhn_perm, Hun_perm, Hfn_perm. rga_cbn_cx Hp1_perm. rga_cbn_cx Hp2_perm. rga_cbn_cx Hhn_perm. rga_cbn_cx Hun_perm. rga_cbn_cx Hfn_perm.
destruct Hp1_perm as [Tp1 Ap1]. destruct Hp2_perm as [Tp2 Ap2]. destruct Hhn_perm as [Thn Ahn]. destruct Hun_perm as [Tun Aun]. destruct Hfn_perm as [Tfn Afn].
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_H3 in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (Hcnt0 & _) & _).
assert (HT24 : 524309 <= ht_T Ht <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
assert (Hcnt64 : 0 <= ht_cnt Ht < 2 ^ 64) by (clear - Hcnt0 HT24; lia).
assert (BT : 0 <= ht_T Ht < 2 ^ 64) by (clear - HT24; lia).
set (Tn := getNextPrimePower2 (ht_T Ht)) in *.
pose proof (ts_chain_next _ HTch HTlt) as HTnch. fold Tn in HTnch.
pose proof (ts_chain_next_gt _ HTch HTlt) as HTngt. fold Tn in HTngt.
assert (HTn24 : 1048583 <= Tn <= 16777216) by (clear - HTnch HTngt HT24; unfold ts_chain in HTnch; cbn [In] in HTnch; lia).
assert (BTn : 0 <= Tn < 2 ^ 64) by (clear - HTn24; lia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
pose proof (g_ts_rank_range (ht_T Ht)) as Hrk.
assert (Hrk4 : g_ts_rank (ht_T Ht) <= 4).
{ clear - HTch HTlt. unfold ts_chain in HTch. cbn [In] in HTch. unfold MAX_TABLE_SIZE in HTlt.
destruct HTch as [H|[H|[H|[H|[H|[H|[]]]]]]]; rewrite <- H in *; first [ vm_compute; discriminate | lia ]. }
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (TBL := [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)]).
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ TBL).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest TBL; YI0g.perm_tac).
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) TBL -> In (b, sz) lrest) by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Hcht_in3 : forall b sz, In (b, sz) TBL -> In (b, sz) (ablocks B ly3 S3)).
{ intros b sz Hb. eapply Permutation_in; [apply Permutation_sym; exact HPrt3|]. right. right. exact (Hcht_l b sz Hb). }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
idtac "OK-B".
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fq _ HAR3 Hfq_in3 ltac:(clear - HT24; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_fq].
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil HT24 C1; lia).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ hh _ HAR3 Hhh_in3 ltac:(clear - HT24; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_hh].
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil HT24 C1; lia).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Huu_l : In (uu, ht_T Ht) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ uu _ HAR3 Huu_in3 ltac:(clear - HT24; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_uu].
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil HT24 C1; lia).
assert (Hp1_in3 : In (p1, 3 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hp1_l : In (p1, 3 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ p1 _ HAR3 Hp1_in3 ltac:(clear - HTn24; lia)) as (Hp14096 & Hp1ceil & Hp116 & Hp1pres).
pose proof (req_size_pos (3 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_p1].
assert (Bp1 : 0 <= p1 < 2 ^ 64) by (clear - Hp14096 Hp1ceil HTn24 C1; lia).
assert (Hp2_in3 : In (p2, 4 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hp2_l : In (p2, 4 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ p2 _ HAR3 Hp2_in3 ltac:(clear - HTn24; lia)) as (Hp24096 & Hp2ceil & Hp216 & Hp2pres).
pose proof (req_size_pos (4 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_p2].
assert (Bp2 : 0 <= p2 < 2 ^ 64) by (clear - Hp24096 Hp2ceil HTn24 C1; lia).
assert (Hhn_in3 : In (hn, 3 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hhn_l : In (hn, 3 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ hn _ HAR3 Hhn_in3 ltac:(clear - HTn24; lia)) as (Hhn4096 & Hhnceil & Hhn16 & Hhnpres).
pose proof (req_size_pos (3 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_hn].
assert (Bhn : 0 <= hn < 2 ^ 64) by (clear - Hhn4096 Hhnceil HTn24 C1; lia).
assert (Hun_in3 : In (un, Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hun_l : In (un, Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ un _ HAR3 Hun_in3 ltac:(clear - HTn24; lia)) as (Hun4096 & Hunceil & Hun16 & Hunpres).
pose proof (req_size_pos (Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_un].
assert (Bun : 0 <= un < 2 ^ 64) by (clear - Hun4096 Hunceil HTn24 C1; lia).
assert (Hfn_in3 : In (fn, 4 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hfn_l : In (fn, 4 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fn _ HAR3 Hfn_in3 ltac:(clear - HTn24; lia)) as (Hfn4096 & Hfnceil & Hfn16 & Hfnpres).
pose proof (req_size_pos (4 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_fn].
assert (Bfn : 0 <= fn < 2 ^ 64) by (clear - Hfn4096 Hfnceil HTn24 C1; lia).
assert (Bix : 0 <= ix < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
idtac "OK-BLK".
assert (Bj : 0 <= j < 2 ^ 64) by (clear - Hj HT24; lia).
assert (Bhs : 0 <= hs < 2 ^ 64) by (clear - Hhs HTn24; lia).
fold Tn in Hhs.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ p1 (3 * Tn) HAR3 Hp1_in3) as (_ & Hp1zone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ p1 (3 * Tn) 7 fpos HAR3 Hp1_in3 Hfin3) as HdF_p1.
unfold zdisjoint in HdF_p1. cbn [fst snd] in HdF_p1. change (fs_frame_bytes 7) with 8192 in HdF_p1. rewrite EFA3 in HdF_p1. fold F in HdF_p1.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ p1 (3 * Tn) cid pos HAR3 Hp1_in3 HfinS3) as HdC_p1.
unfold zdisjoint in HdC_p1. cbn [fst snd] in HdC_p1. rewrite EFA3 in HdC_p1.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (p1, 3 * Tn) HAR3 HPrt3 ltac:(right; exact Hp1_l)) as HzR_p1.
unfold zdisjoint, block_rng in HzR_p1. cbn [fst snd] in HzR_p1. change (req_size RGB_SIZE) with 64 in HzR_p1.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (p1, 3 * Tn) HAR3 HPtb3 ltac:(right; exact Hp1_l)) as HzT_p1.
unfold zdisjoint, block_rng in HzT_p1. cbn [fst snd] in HzT_p1. change (req_size 48) with 48 in HzT_p1.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ un (Tn) HAR3 Hun_in3) as (_ & Hunzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ un (Tn) 7 fpos HAR3 Hun_in3 Hfin3) as HdF_un.
unfold zdisjoint in HdF_un. cbn [fst snd] in HdF_un. change (fs_frame_bytes 7) with 8192 in HdF_un. rewrite EFA3 in HdF_un. fold F in HdF_un.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ un (Tn) cid pos HAR3 Hun_in3 HfinS3) as HdC_un.
unfold zdisjoint in HdC_un. cbn [fst snd] in HdC_un. rewrite EFA3 in HdC_un.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (un, Tn) HAR3 HPrt3 ltac:(right; exact Hun_l)) as HzR_un.
unfold zdisjoint, block_rng in HzR_un. cbn [fst snd] in HzR_un. change (req_size RGB_SIZE) with 64 in HzR_un.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (un, Tn) HAR3 HPtb3 ltac:(right; exact Hun_l)) as HzT_un.
unfold zdisjoint, block_rng in HzT_un. cbn [fst snd] in HzT_un. change (req_size 48) with 48 in HzT_un.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fn (4 * Tn) HAR3 Hfn_in3) as (_ & Hfnzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fn (4 * Tn) 7 fpos HAR3 Hfn_in3 Hfin3) as HdF_fn.
unfold zdisjoint in HdF_fn. cbn [fst snd] in HdF_fn. change (fs_frame_bytes 7) with 8192 in HdF_fn. rewrite EFA3 in HdF_fn. fold F in HdF_fn.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fn (4 * Tn) cid pos HAR3 Hfn_in3 HfinS3) as HdC_fn.
unfold zdisjoint in HdC_fn. cbn [fst snd] in HdC_fn. rewrite EFA3 in HdC_fn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (fn, 4 * Tn) HAR3 HPrt3 ltac:(right; exact Hfn_l)) as HzR_fn.
unfold zdisjoint, block_rng in HzR_fn. cbn [fst snd] in HzR_fn. change (req_size RGB_SIZE) with 64 in HzR_fn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (fn, 4 * Tn) HAR3 HPtb3 ltac:(right; exact Hfn_l)) as HzT_fn.
unfold zdisjoint, block_rng in HzT_fn. cbn [fst snd] in HzT_fn. change (req_size 48) with 48 in HzT_fn.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ p2 (4 * Tn) HAR3 Hp2_in3) as (_ & Hp2zone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ p2 (4 * Tn) 7 fpos HAR3 Hp2_in3 Hfin3) as HdF_p2.
unfold zdisjoint in HdF_p2. cbn [fst snd] in HdF_p2. change (fs_frame_bytes 7) with 8192 in HdF_p2. rewrite EFA3 in HdF_p2. fold F in HdF_p2.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ p2 (4 * Tn) cid pos HAR3 Hp2_in3 HfinS3) as HdC_p2.
unfold zdisjoint in HdC_p2. cbn [fst snd] in HdC_p2. rewrite EFA3 in HdC_p2.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (p2, 4 * Tn) HAR3 HPrt3 ltac:(right; exact Hp2_l)) as HzR_p2.
unfold zdisjoint, block_rng in HzR_p2. cbn [fst snd] in HzR_p2. change (req_size RGB_SIZE) with 64 in HzR_p2.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (p2, 4 * Tn) HAR3 HPtb3 ltac:(right; exact Hp2_l)) as HzT_p2.
unfold zdisjoint, block_rng in HzT_p2. cbn [fst snd] in HzT_p2. change (req_size 48) with 48 in HzT_p2.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) HAR3 Hfq_in3) as (_ & Hfqzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) 7 fpos HAR3 Hfq_in3 Hfin3) as HdF_fq.
unfold zdisjoint in HdF_fq. cbn [fst snd] in HdF_fq. change (fs_frame_bytes 7) with 8192 in HdF_fq. rewrite EFA3 in HdF_fq. fold F in HdF_fq.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) cid pos HAR3 Hfq_in3 HfinS3) as HdC_fq.
unfold zdisjoint in HdC_fq. cbn [fst snd] in HdC_fq. rewrite EFA3 in HdC_fq.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (fq, 4 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hfq_l)) as HzR_fq.
unfold zdisjoint, block_rng in HzR_fq. cbn [fst snd] in HzR_fq. change (req_size RGB_SIZE) with 64 in HzR_fq.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (fq, 4 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hfq_l)) as HzT_fq.
unfold zdisjoint, block_rng in HzT_fq. cbn [fst snd] in HzT_fq. change (req_size 48) with 48 in HzT_fq.
assert (HT0 : 0 < ht_T Ht) by (clear - HT24; lia). assert (HTn0 : 0 < Tn) by (clear - HTn24; lia).
destruct (g_sep8_of_AR B LAWS ly3 S3 W3 _ _ (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ [(tb, 48)]) fq hh uu (ht_T Ht) p1 p2 hn un fn Tn HAR3
ltac:(eapply Permutation_trans; [exact HPm3|]; rewrite <- !app_assoc; reflexivity) HT0 HTn0) as (SEPON & SEPK).
pose proof (SEPON hh (3 * ht_T Ht) p1 (3 * Tn) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Dhh_p1.
pose proof HKinv as ((LK1 & LK2 & LK3 & LK4 & LK5) & (HcntK0 & _) & _). rewrite HKT in LK1, LK2, LK3, LK4, LK5, HcntK0.
pose proof Harr as (Af & Ak & Au).
assert (Hkey3 : col3 trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (hh + 3 * j) (key Ht j))
by (unfold key; apply (arr8_col3 trbsegs _ hh (ht_keys Ht) j Ak); [clear - Hj; lia | rewrite L2; clear - Hj; lia]).
set (cn := ht_cnt K) in *.
assert (Hcn : 0 <= cn < Tn) by (exact HcntK0).
assert (BcK : 0 <= cn < 2 ^ 64) by (clear - Hcn HTn24; lia).
idtac "OK-SEP".
assert (Hsj : 0 <= 3 * j /\ 3 * j + 3 <= 3 * ht_T Ht) by (clear - Hj; lia).
assert (Hdh : 0 <= cn * 3 /\ cn * 3 + 3 <= 3 * Tn) by (clear - Hcn; lia).
assert (Bsrc : 0 <= hh + 3 * j < 2 ^ 64) by (clear - Hhh4096 Hhhceil Hrq_hh Hsj C1; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (p1 + cn * 3)
ltac:(apply (U_add_small_q _ _ _ p1 (cn * 3) (U_atom _ 760 p1 Rp1 Bp1));
[ apply (g_U_mul_small _ (SOff 1120 0) (SLit 3) cn 3 (U_atom _ 1120 cn Rcnt BcK) ltac:(reflexivity)); clear - Hcn HTn24; lia | clear - Bp1; lia | clear - Hcn; lia | clear - Hp1ceil Hrq_p1 Hdh C1; lia ]) Ha0.
rregU HS (11%bv : bv 5) (hh + 3 * j)
ltac:(rewrite (Z.add_comm hh);
apply U_add_small_q; [ rewrite U_and_lit by (clear; lia); rewrite (U_atom _ 1102 (3 * j) Rj3 ltac:(clear - Hj HT24; lia));
change 4294967295 with (Z.ones 32); rewrite Z.land_ones by (clear; lia); apply Z.mod_small; clear - Hj HT24; lia
| exact (U_atom _ 474 hh Rhh Bhh) | clear - Hj; lia | clear - Bhh; lia | clear - Hhhceil Hrq_hh Hsj C1; lia ]) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ hh (3 * ht_T Ht) (proj1 HJ3) Hhh_in3) as (_ & _ & _ & _ & HhhP & _).
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
idtac "OK-C0".
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (p1 + cn * 3) (hh + 3 * j) 3 (-576) (Z_to_bv 64 0x82d98) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Hp14096 Hcn; lia.
- clear - Hp1ceil Hrq_p1 Hdh C1; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [| rewrite Hes; clear - Ha Hp1ceil Hrq_p1 Hdh Hceil Hslo FFS; lia].
replace a with (p1 + (a - p1)) by (clear; lia). apply Ap1; [exact Hp1_in3 | clear - Ha Hrq_p1 Hdh; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ p1 (3 * Tn) (p1 + cn * 3) 3 (proj1 HJ3) Hp1_in3); [clear - Hdh; lia | clear - Hrq_p1 Hdh; lia].
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ p1 (3 * Tn) (p1 + cn * 3) 3 (proj1 HJ3) Hp1_in3); [clear - Hdh; lia | clear - Hrq_p1 Hdh; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ p1 (3 * Tn) (p1 + cn * 3) 3 (proj1 HJ3) Hp1_in3); [clear - Hdh; lia | clear - Hrq_p1 Hdh; lia | clear; lia].
- split; [clear - Bsrc; lia|]. split; [clear - Hhhceil Hrq_hh Hsj C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); exact (proj1 (HhhP a ltac:(clear - Ha Hsj Hrq_hh; lia)))
| rewrite HspT, Hes; clear - Ha Hhhceil Hrq_hh Hsj Hceil Hslo FFS C1; lia]. }
split; [clear - Dhh_p1 Hrq_hh Hrq_p1 Hdh Hsj; lia|]. split.
{ apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + 3 * j) 3 (proj1 HJ3) Hhh_in3); [clear - Hsj; lia | clear - Hsj Hrq_hh; lia]. }
split; [apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + 3 * j) 3 (proj1 HJ3) Hhh_in3); [clear - Hsj; lia | clear - Hsj Hrq_hh; lia]|].
intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + 3 * j) 3 (proj1 HJ3) Hhh_in3); [clear - Hsj; lia | clear - Hsj Hrq_hh; lia | clear; lia]. }
idtac "OK-C1".
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
assert (Hfr3 : forall a, 0 <= a < 2 ^ 64 -> ~ (p1 + cn * 3 <= a < p1 + cn * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576) ->
aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha1 Ha2; apply Hfr5; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
assert (HWIN3 : forall a, 0 <= a < alloc_ceiling -> ~ (p1 <= a < p1 + 3 * Tn) ->
0 <= a < 2 ^ 64 /\ ~ (p1 + cn * 3 <= a < p1 + cn * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hn Hdh Hceil Hslo FFS C1; lia).
assert (HWSTc3 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> ~ (spZ regs + 0 <= a < spZ regs + 0) ->
0 <= a < 2 ^ 64 /\ ~ (p1 + cn * 3 <= a < p1 + cn * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hp1ceil Hrq_p1 Hdh Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG8 : ((4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= 2147446784 \/ 17594333495296 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= 2147446784 \/ 17594333495296 <= cfp)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880) /\
(3 * Tn <= req_size (3 * Tn) /\ (p1 + req_size (3 * Tn) <= 2147446784 \/ 17594333495296 <= p1) /\ (p1 + req_size (3 * Tn) <= F \/ F + 8192 <= p1) /\
(r + 64 <= p1 \/ p1 + req_size (3 * Tn) <= r) /\
(p1 + req_size (3 * Tn) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= p1) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid)).
{ unfold gbox, in_app in HFhigh, Hrapp, Hfhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh, Hrapp, Hfhigh. unfold gbox in Hp1zone.
split; [|clear - Hrq_p1 Hp1zone HdF_p1 HzR_p1 HdC_p1 Hflo Hfhi; lia].
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil Hrapp; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi Hfhigh; lia|]. split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
assert (HRtb8 : ((4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= 2147446784 \/ 17594333495296 <= tb)) /\
(F + 8192 <= alloc_ceiling /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ 512 <= F / 8) /\ SB = 2147450880) /\
3 * Tn <= req_size (3 * Tn) /\ (tb + 48 <= p1 \/ p1 + req_size (3 * Tn) <= tb)).
{ unfold gbox in Htbzone. change (req_size 48) with 48 in Htbzone.
split; [|clear - Hrq_p1 HzT_p1; lia]. split; [clear - Htb4096 Htbceil Hrqtb Htbzone C1; lia|]. split; [clear - HFceil HFq HF8 HF8lo; lia | reflexivity]. }
idtac "OK-P0".
m_reseatF HS HJ5 fx regs5 CLOB 535960 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP5)
ltac:(idtac; first
[ m_keptWc Hfr3 Hpres5 HJ5 HWIN3 HWSTc3 HRNG8 AG Usp RF E67 E10n E11n 0 0
ltac:(idtac; first [ m_keptW_blk Hfr3 Hpres5 HWIN3 AG 305%nat tb Rtb HRtb8
| ga_kept_consts Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
idtac "OK-RS".
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
clear KP.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ ((m_ZsP F r a \/ tb <= a < tb + 48) \/ g_cells3 fn un p2 hs a) -> aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) mem5 a) by (intros; reflexivity).
assert (Hpal5 : col3 trbsegs (mrestrict (w_H W3) mem5) (p1 + cn * 3) (key Ht j)) by (exact (g_col3_copy (w_H W3) (ms_mem ms3) mem5 _ _ (key Ht j) Hkey3 Heff5)).
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE5 end.
norm_ss HS.
idtac "OK-P2".
assert (Hj4 : 0 <= 4 * j < 2 ^ 64) by (clear - Hj HT24; lia).
g_fact HS 1125%nat (mkAF 0 16777215 0)
ltac:(rewrite Rhs, unsigned_lit_small by exact Bhs; change (2 ^ 0) with 1; split; [clear - Hhs HTn24; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_fact HS 1101%nat (mkAF 0 67108864 2)
ltac:(rewrite Rj4, unsigned_lit_small by exact Hj4; change (2 ^ 2) with 4; split; [clear - Hj HT24; lia|]; split; [rewrite Z.mul_comm; apply Z_mod_mult | clear; lia]).
idtac "OK-FACT".
pose proof (SEPON fq (4 * ht_T Ht) un Tn ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Dfq_un.
pose proof (SEPON fq (4 * ht_T Ht) fn (4 * Tn) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Dfq_fn.
pose proof (SEPON fq (4 * ht_T Ht) p2 (4 * Tn) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Dfq_p2.
pose proof (SEPON fq (4 * ht_T Ht) p1 (3 * Tn) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Dfq_p1.
pose proof SEPK as SEPK'. unfold g_sep5 in SEPK'.
set (fv := freq Ht j).
destruct (arr32_getz trbsegs _ fq (ht_frequ Ht) j Af ltac:(rewrite L3; exact Hj)) as [Vfv Hfv32]. fold (freq Ht j) in Vfv, Hfv32. fold fv in Vfv, Hfv32.
assert (Hc1_rng : 4096 <= un + hs /\ un + hs + 1 <= alloc_ceiling) by (clear - Hun4096 Hunceil Hhs; lia).
assert (Bc1 : 0 <= un + hs < 2 ^ 64) by (clear - Hc1_rng C1; lia).
assert (Hc2_rng : 4096 <= fq + 4 * j /\ fq + 4 * j + 4 <= alloc_ceiling) by (clear - Hfq4096 Hfqceil Hj; lia).
assert (Bc2 : 0 <= fq + 4 * j < 2 ^ 64) by (clear - Hc2_rng C1; lia).
assert (Hc3_rng : 4096 <= fn + 4 * hs /\ fn + 4 * hs + 4 <= alloc_ceiling) by (clear - Hfn4096 Hfnceil Hhs; lia).
assert (Bc3 : 0 <= fn + 4 * hs < 2 ^ 64) by (clear - Hc3_rng C1; lia).
assert (Hc4_rng : 4096 <= p2 + 4 * hs /\ p2 + 4 * hs + 4 <= alloc_ceiling) by (clear - Hp24096 Hp2ceil Hhs; lia).
assert (Bc4 : 0 <= p2 + 4 * hs < 2 ^ 64) by (clear - Hc4_rng C1; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ un Tn (proj1 HJ5) Hun_in3) as (_ & _ & _ & _ & Hunpres1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fn (4 * Tn) (proj1 HJ5) Hfn_in3) as (_ & _ & _ & _ & Hfnpres1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p2 (4 * Tn) (proj1 HJ5) Hp2_in3) as (_ & _ & _ & _ & Hp2pres1 & _).
assert (Vfv5 : val_mem trbsegs (mrestrict (w_H W3) mem5) (fq + 4 * j) 4 fv).
{ apply (g_val_mem_kept (w_H W3) (ms_mem ms3) mem5 _ _ _ Vfv). intros kk Hkk. apply Hfr3; [clear - Hkk Hc2_rng C1; lia|].
intros [Hx | Hx]; [clear - Hx Hkk Dfq_p1 Hdh Hj Hrq_fq Hrq_p1; lia | rewrite Hes in Hx; clear - Hx Hkk Hc2_rng Hceil Hslo FFS; lia]. }
g_havoc HS 1180%nat [Z_to_bv 64 (un + hs); Z_to_bv 64 (fq + 4 * j); Z_to_bv 64 fv; Z_to_bv 64 (fn + 4 * hs); Z_to_bv 64 (p2 + 4 * hs)].
g_havoc_val HS 1180%nat 0%nat (Z_to_bv 64 (un + hs)) E1180.
g_havoc_val HS 1180%nat 1%nat (Z_to_bv 64 (fq + 4 * j)) E1181.
g_havoc_val HS 1180%nat 2%nat (Z_to_bv 64 fv) E1182.
g_havoc_val HS 1180%nat 3%nat (Z_to_bv 64 (fn + 4 * hs)) E1183.
g_havoc_val HS 1180%nat 4%nat (Z_to_bv 64 (p2 + 4 * hs)) E1184.
m_env_fold HS AG.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE6 end.
idtac "OK-CL0".
g_region HS AG (YQ0b.mkRegion (Some 1180%nat) 0 1 0 1 [])
ltac:(rewrite E1180, unsigned_lit_small by exact Bc1;
split; [clear - Hc1_rng; lia|]; split; [clear - Hc1_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hunpres1 (un + hs + o) ltac:(clear - Ho Hhs Hrq_un; lia))) | apply Forall_nil ])
ltac:(first [ clear - Hc1_rng Hceil Hslo FFS Hhs Hrq_un; lia
| destruct Hunzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs Hrq_un HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_un Hhs Hrq_un; lia
| clear - HdC_un Hhs Hrq_un Hflo Hfhi; lia
| clear - HzR_un Hhs Hrq_un; lia
| clear - HzT_un Hhs Hrq_un; lia
| clear - SEPK' Dfq_un Dfq_fn Dfq_p2 Hhs Hj Hrq_un Hrq_fn Hrq_p2 Hrq_fq; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CL-c1".
g_region HS AG (YQ0b.mkRegion (Some 1181%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 1182 0))])
ltac:(rewrite E1181, unsigned_lit_small by exact Bc2;
split; [clear - Hc2_rng; lia|]; split; [clear - Hc2_rng C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trbsegs _ _ (fq + 4 * j) _ _ (SOff 1182 0) fv);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E1182 | exact Hfv32 | cbn; clear; lia
| rewrite Z.add_0_r; exact Vfv5] | apply Forall_nil] ])
ltac:(first [ clear - Hc2_rng Hceil Hslo FFS Hj Hrq_fq; lia
| destruct Hfqzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hj Hrq_fq HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_fq Hj Hrq_fq; lia
| clear - HdC_fq Hj Hrq_fq Hflo Hfhi; lia
| clear - HzR_fq Hj Hrq_fq; lia
| clear - HzT_fq Hj Hrq_fq; lia
| clear - SEPK' Dfq_un Dfq_fn Dfq_p2 Hhs Hj Hrq_un Hrq_fn Hrq_p2 Hrq_fq; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CL-c2".
g_region HS AG (YQ0b.mkRegion (Some 1183%nat) 0 4 0 4 [])
ltac:(rewrite E1183, unsigned_lit_small by exact Bc3;
split; [clear - Hc3_rng; lia|]; split; [clear - Hc3_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hfnpres1 (fn + 4 * hs + o) ltac:(clear - Ho Hhs Hrq_fn; lia))) | apply Forall_nil ])
ltac:(first [ clear - Hc3_rng Hceil Hslo FFS Hhs Hrq_fn; lia
| destruct Hfnzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs Hrq_fn HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_fn Hhs Hrq_fn; lia
| clear - HdC_fn Hhs Hrq_fn Hflo Hfhi; lia
| clear - HzR_fn Hhs Hrq_fn; lia
| clear - HzT_fn Hhs Hrq_fn; lia
| clear - SEPK' Dfq_un Dfq_fn Dfq_p2 Hhs Hj Hrq_un Hrq_fn Hrq_p2 Hrq_fq; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CL-c3".
g_region HS AG (YQ0b.mkRegion (Some 1184%nat) 0 4 0 4 [])
ltac:(rewrite E1184, unsigned_lit_small by exact Bc4;
split; [clear - Hc4_rng; lia|]; split; [clear - Hc4_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hp2pres1 (p2 + 4 * hs + o) ltac:(clear - Ho Hhs Hrq_p2; lia))) | apply Forall_nil ])
ltac:(first [ clear - Hc4_rng Hceil Hslo FFS Hhs Hrq_p2; lia
| destruct Hp2zone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs Hrq_p2 HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_p2 Hhs Hrq_p2; lia
| clear - HdC_p2 Hhs Hrq_p2 Hflo Hfhi; lia
| clear - HzR_p2 Hhs Hrq_p2; lia
| clear - HzT_p2 Hhs Hrq_p2; lia
| clear - SEPK' Dfq_un Dfq_fn Dfq_p2 Hhs Hj Hrq_un Hrq_fn Hrq_p2 Hrq_fq; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CL-c4".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 808 0) (SOff 1125 0)) (SOff 1180 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 1180 _ E1180 Bc1); apply (U_add_small_q _ _ _ un hs (U_atom _ 808 un Run Bun) (U_atom _ 1125 hs Rhs Bhs)); [clear - Bun; lia | clear - Hhs; lia | clear - Bc1; lia])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 473 0) (SOff 1101 0)) (SOff 1181 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 1181 _ E1181 Bc2); apply (U_add_small_q _ _ _ fq (4 * j) (U_atom _ 473 fq Rfq Bfq) (U_atom _ 1101 (4 * j) Rj4 Hj4)); [clear - Bfq; lia | clear - Hj; lia | clear - Bc2; lia])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 824 0) (SAlu ALU_SLL (SOff 1125 0) (SLit 2))) (SOff 1183 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 1183 _ E1183 Bc3); replace (fn + 4 * hs) with (fn + hs * 2 ^ 2) by (clear; lia);
apply (U_add_small_q _ _ _ fn (hs * 2 ^ 2) (U_atom _ 824 fn Rfn Bfn)
(U_sll_small_q _ _ hs 2 (U_atom _ 1125 hs Rhs Bhs) ltac:(clear - Hhs; lia) ltac:(clear; lia) ltac:(clear - Hhs HTn24; lia)));
[ clear - Bfn; lia | clear - Hhs; lia | clear - Bc3; lia ])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 776 0) (SAlu ALU_SLL (SOff 1125 0) (SLit 2))) (SOff 1184 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 1184 _ E1184 Bc4); replace (p2 + 4 * hs) with (p2 + hs * 2 ^ 2) by (clear; lia);
apply (U_add_small_q _ _ _ p2 (hs * 2 ^ 2) (U_atom _ 776 p2 Rp2 Bp2)
(U_sll_small_q _ _ hs 2 (U_atom _ 1125 hs Rhs Bhs) ltac:(clear - Hhs; lia) ltac:(clear; lia) ltac:(clear - Hhs HTn24; lia)));
[ clear - Bp2; lia | clear - Hhs; lia | clear - Bc4; lia ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "OK-AL0".
g_fact HS 1180%nat (mkAF 4096 140737479966720 0)
ltac:(rewrite E1180, unsigned_lit_small by exact Bc1; change (2 ^ 0) with 1; split; [clear - Hc1_rng C1; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_fact HS 1181%nat (mkAF 4096 140737479966720 2)
ltac:(rewrite E1181, unsigned_lit_small by exact Bc2; change (2 ^ 2) with 4; split; [clear - Hc2_rng C1; lia|]; split; [pose proof (Z.div_mod fq 16 ltac:(clear; lia)) as D16; rewrite Hfq16, Z.add_0_r in D16; rewrite D16; replace (16 * (fq / 16) + 4 * j) with ((4 * (fq / 16) + j) * 4) by (clear; lia); apply Z_mod_mult | clear; lia]).
g_fact HS 1183%nat (mkAF 4096 140737479966720 2)
ltac:(rewrite E1183, unsigned_lit_small by exact Bc3; change (2 ^ 2) with 4; split; [clear - Hc3_rng C1; lia|]; split; [pose proof (Z.div_mod fn 16 ltac:(clear; lia)) as D16; rewrite Hfn16, Z.add_0_r in D16; rewrite D16; replace (16 * (fn / 16) + 4 * hs) with ((4 * (fn / 16) + hs) * 4) by (clear; lia); apply Z_mod_mult | clear; lia]).
g_fact HS 1184%nat (mkAF 4096 140737479966720 2)
ltac:(rewrite E1184, unsigned_lit_small by exact Bc4; change (2 ^ 2) with 4; split; [clear - Hc4_rng C1; lia|]; split; [pose proof (Z.div_mod p2 16 ltac:(clear; lia)) as D16; rewrite Hp216, Z.add_0_r in D16; rewrite D16; replace (16 * (p2 / 16) + 4 * hs) with ((4 * (p2 / 16) + hs) * 4) by (clear; lia); apply Z_mod_mult | clear; lia]).
idtac "OK-AL1".
g_cond HS BC_GEU (SAlu ALU_XOR (SOff 808 0) (SLit (-1))) (SOff 1125 0)
ltac:(apply (YCqg.ub_room_cond _ _ _ un hs (U_atom _ 808 un Run Bun) (U_atom _ 1125 hs Rhs Bhs)); [clear - Bun; lia | clear - Hhs; lia | clear - Hunceil Hhs C1; lia]).
g_cond HS BC_GEU (SOff 1181 0) (SOff 473 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 1181 0) (SOff 473 0) (fq + 4 * j) fq (U_atom _ 1181 _ E1181 Bc2) (U_atom _ 473 fq Rfq Bfq)); clear - Hj; lia).
g_cond HS BC_GEU (SAlu ALU_XOR (SOff 824 0) (SLit (-1))) (SAlu ALU_SLL (SOff 1125 0) (SLit 2))
ltac:(apply (YCqg.ub_room_cond _ _ _ fn (hs * 2 ^ 2) (U_atom _ 824 fn Rfn Bfn)
(U_sll_small_q _ _ hs 2 (U_atom _ 1125 hs Rhs Bhs) ltac:(clear - Hhs; lia) ltac:(clear; lia) ltac:(clear - Hhs HTn24; lia)));
[clear - Bfn; lia | clear - Hhs; lia | clear - Hfnceil Hhs C1; lia]).
g_cond HS BC_GEU (SOff 1184 0) (SOff 776 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 1184 0) (SOff 776 0) (p2 + 4 * hs) p2 (U_atom _ 1184 _ E1184 Bc4) (U_atom _ 776 p2 Rp2 Bp2)); clear - Hhs; lia).
reshok_bx HS 44%nat.
idtac "OK-AL".
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK GBspan 0x82ef0.
idtac "OK-RUN".
all: try (m_obl_cell HJ5 E1180 E44 Hun_in3 ltac:(idtac; first [clear - Hc1_rng C1; lia | clear - Hhs Hrq_un; lia])).
all: try (m_obl_cell HJ5 E1181 E44 Hfq_in3 ltac:(idtac; first [clear - Hc2_rng C1; lia | clear - Hj Hrq_fq; lia])).
all: try (m_obl_cell HJ5 E1183 E44 Hfn_in3 ltac:(idtac; first [clear - Hc3_rng C1; lia | clear - Hhs Hrq_fn; lia])).
all: try (m_obl_cell HJ5 E1184 E44 Hp2_in3 ltac:(idtac; first [clear - Hc4_rng C1; lia | clear - Hhs Hrq_p2; lia])).
all: try (ga_obl_blk HJ5 Rtb E44 Htb_in3).
idtac "OK-OB".
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(fun nb => first [ m_awr_cell 1180%nat E1180 un Aun Hun_in3 ltac:(idtac; first [clear - Hc1_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hhs Hrq_un; lia end]) nb
| m_awr_cell 1183%nat E1183 fn Afn Hfn_in3 ltac:(idtac; first [clear - Hc3_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hhs Hrq_fn; lia end]) nb
| m_awr_cell 1184%nat E1184 p2 Ap2 Hp2_in3 ltac:(idtac; first [clear - Hc4_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hhs Hrq_p2; lia end]) nb ]).
idtac "OK-AWR".
g_kept_run HFr AG (fun a : Z => (m_ZsP F r a \/ tb <= a < tb + 48) \/ (a = un + hs \/ p2 + 4 * hs <= a < p2 + 4 * hs + 4 \/ fn + 4 * hs <= a < fn + 4 * hs + 4)) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-KEPT".
pose proof Hinv as (_ & _ & _ & I4 & _).
assert (Hin : in_slot Ht j) by (split; [exact Hj | rewrite Huv1; clear; lia]).
destruct (I4 j Hin) as (Hcx & Hnth & Hfv1). fold fv in Hnth, Hfv1.
pose proof (zsum_pos_le ent _ _ _ (ent_freq_pos Ht ent Hinv) Hnth) as Hfvz.
assert (Hfv_s : 1 <= fv <= 10001) by (clear - Hfv1 Hfvz Hsum Hix HN; unfold RGB_NMAX in HN; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (Rcntz : ew Ex 1120 = Z_to_bv 64 cn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt);
assert (E1182z : ew Ex 1182 = Z_to_bv 64 fv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E1182);
assert (HB1180 : bv_unsigned (ew Ex 1180) = un + hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E1180; apply unsigned_lit_small; exact Bc1);
assert (HB1183 : bv_unsigned (ew Ex 1183) = fn + 4 * hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E1183; apply unsigned_lit_small; exact Bc3);
assert (HB1184 : bv_unsigned (ew Ex 1184) = p2 + 4 * hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E1184; apply unsigned_lit_small; exact Bc4);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRc4; cbn [ms_mem restrict] in HRc4;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 1 _ HS eq_refl) as HRc3; cbn [ms_mem restrict] in HRc3;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 3 _ HS eq_refl) as HRc1; cbn [ms_mem restrict] in HRc1;
lazymatch type of HRc4 with region_ok _ _ _ (YQ0b.mkRegion (Some 1184%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 1184 (p2 + 4 * hs) cs lo hi wlo whi 0 4%N (SOff 1120 0) HRc4 HB1184 ltac:(cbn; tauto) ltac:(cbn; lia)) as V4;
change (bv_unsigned (sv_denot Ex (SOff 1120 0))) with (U Ex (SOff 1120 0)) in V4; rewrite (U_atom Ex 1120 cn Rcntz BcK) in V4 end;
lazymatch type of HRc3 with region_ok _ _ _ (YQ0b.mkRegion (Some 1183%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 1183 (fn + 4 * hs) cs lo hi wlo whi 0 4%N (SExt true 32 (SOff 1182 0)) HRc3 HB1183 ltac:(cbn; tauto) ltac:(cbn; lia)) as V3;
change (bv_unsigned (sv_denot Ex (SExt true 32 (SOff 1182 0)))) with (U Ex (SExt true 32 (SOff 1182 0))) in V3;
rewrite (U_sext32_small Ex 1182 fv E1182z ltac:(clear - Hfv_s; lia)) in V3 end;
lazymatch type of HRc1 with region_ok _ _ _ (YQ0b.mkRegion (Some 1180%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 1180 (un + hs) cs lo hi wlo whi 0 1%N (SLit 1) HRc1 HB1180 ltac:(cbn; tauto) ltac:(cbn; lia)) as V1 end;
clear HRc1 HRc3 HRc4 end.
change (bv_unsigned (sv_denot _ (SLit 1)) mod 2 ^ (8 * Z.of_N 1)) with 1 in V1.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V3, V4. rewrite Z.mod_small in V4 by (clear - Hcn HTn24; lia). rewrite Z.mod_small in V3 by (clear - Hfv_s; lia).
rewrite Z.add_0_r in V1, V3, V4. change (N.to_nat 4) with 4%nat in V3, V4. change (N.to_nat 1) with 1%nat in V1.
assert (B1 : mbyte trbsegs _ (un + hs) = Some (Z_to_bv 8 1)) by (pose proof (V1 0%nat ltac:(lia)) as Vb; rewrite Z.add_0_r in Vb; exact Vb).
idtac "OK-MEM".
assert (Bcn1 : 0 <= cn + 1 < 2 ^ 64) by (clear - Hcn HTn24; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rjz : ew Ex 1100 = Z_to_bv 64 j) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rj);
assert (Rj4z : ew Ex 1101 = Z_to_bv 64 (4 * j)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rj4);
assert (Rj3z : ew Ex 1102 = Z_to_bv 64 (3 * j)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rj3) end.
rregU HS (23%bv : bv 5) j ltac:(exact (U_atom _ 1100 j Rjz Bj)) Q23.
rregU HS (26%bv : bv 5) (4 * j) ltac:(exact (U_atom _ 1101 (4 * j) Rj4z ltac:(clear - Hj HT24; lia))) Q26.
rregU HS (20%bv : bv 5) (3 * j) ltac:(exact (U_atom _ 1102 (3 * j) Rj3z ltac:(clear - Hj HT24; lia))) Q20.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (cn + 1)) ltac:(exact (g_denot_off _ 1120 cn 1 Rcntz BcK)) QC.
ra_join_slots HS ss_HT 1300%nat rga_deads_HT [(Some 305%nat, 0, 40)]
ltac:(idtac; ga_join_val HS 1300%nat 0%nat Q23 N1300; ga_join_val HS 1300%nat 1%nat Q26 N1301; ga_join_val HS 1300%nat 2%nat Q20 N1302; ga_join_val HS 1300%nat 21%nat QC N1321).
idtac "OK-JOIN".
assert (KOFF : forall b sz, In (b, sz) TBL -> forall a, b <= a < b + sz -> (0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)) /\ 0 <= a < alloc_ceiling).
{ intros b sz Hb a Ha.
assert (Hsz : 0 < sz /\ 4096 <= b /\ b + sz <= alloc_ceiling).
{ subst TBL. cbn [In] in Hb.
repeat (destruct Hb as [Hb | Hb]; [injection Hb as Eb Es; rewrite <- Eb, <- Es; clear - HT24 HTn24 Hfq4096 Hfqceil Hhh4096 Hhhceil Huu4096 Huuceil Hp14096 Hp1ceil Hp24096 Hp2ceil Hhn4096 Hhnceil Hun4096 Hunceil Hfn4096 Hfnceil; lia|]). destruct Hb. }
pose proof (req_size_pos sz ltac:(clear - Hsz; lia)) as [_ Hrq]. split; [apply (Hoff3 b sz (Hcht_l b sz Hb) a); clear - Ha Hrq; lia | clear - Ha Hsz; lia]. }
assert (K5 : forall b sz, In (b, sz) TBL -> forall a, b <= a < b + sz -> ~ (p1 + cn * 3 <= a < p1 + cn * 3 + 3) ->
aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) (ms_mem ms3) a).
{ intros b sz Hb a Ha Hn. destruct (KOFF b sz Hb a Ha) as [[Hq1 Hq2] Hq3]. apply (Hfr3 a Hq1).
intros [Hx | Hx]; [exact (Hn Hx) | rewrite Hes in Hx; clear - Hx Hq3 Hceil Hslo FFS; lia]. }
pose proof (SEPON hh (3 * ht_T Ht) un Tn ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Dhh_un.
pose proof (SEPON hh (3 * ht_T Ht) fn (4 * Tn) ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Dhh_fn.
pose proof (SEPON hh (3 * ht_T Ht) p2 (4 * Tn) ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Dhh_p2.
pose proof (SEPON uu (ht_T Ht) un Tn ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Duu_un.
pose proof (SEPON uu (ht_T Ht) fn (4 * Tn) ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Duu_fn.
pose proof (SEPON uu (ht_T Ht) p2 (4 * Tn) ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Duu_p2.
pose proof (SEPON uu (ht_T Ht) p1 (3 * Tn) ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Duu_p1.
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Hold1 : g_old3 (mrestrict (w_H W3) mF) fq hh uu Ht) end.
{ apply (g_old3_kept (w_H W3) (ms_mem ms3) _ fq hh uu Ht ent Harr Hinv). intros a Ha.
assert (Hq : (0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)) /\ ~ g_cells3 fn un p2 hs a /\ ~ (p1 + cn * 3 <= a < p1 + cn * 3 + 3) /\
exists b sz, In (b, sz) TBL /\ b <= a < b + sz).
{ unfold g_cells3. destruct Ha as [Ha | [Ha | Ha]].
- split; [exact (proj1 (KOFF fq (4 * ht_T Ht) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha))|]. split; [clear - Ha Dfq_un Dfq_fn Dfq_p2 Hhs Hrq_un Hrq_fn Hrq_p2; lia|].
split; [clear - Ha Dfq_p1 Hdh; lia|]. exists fq, (4 * ht_T Ht). split; [subst TBL; cbn [In]; repeat first [left; reflexivity | right] | exact Ha].
- split; [exact (proj1 (KOFF hh (3 * ht_T Ht) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha))|]. split; [clear - Ha Dhh_un Dhh_fn Dhh_p2 Hhs Hrq_un Hrq_fn Hrq_p2; lia|].
split; [clear - Ha Dhh_p1 Hdh; lia|]. exists hh, (3 * ht_T Ht). split; [subst TBL; cbn [In]; repeat first [left; reflexivity | right] | exact Ha].
- split; [exact (proj1 (KOFF uu (ht_T Ht) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha))|]. split; [clear - Ha Duu_un Duu_fn Duu_p2 Hhs Hrq_un Hrq_fn Hrq_p2; lia|].
split; [clear - Ha Duu_p1 Hdh; lia|]. exists uu, (ht_T Ht). split; [subst TBL; cbn [In]; repeat first [left; reflexivity | right] | exact Ha]. }
destruct Hq as ([Hq1 Hq2] & Hq3 & Hq4 & (b0 & sz0 & Hb0 & Ha0)).
rewrite (KP a Hq1 ltac:(intros [Hx | Hx]; [exact (Hq2 Hx) | exact (Hq3 Hx)])). exact (K5 b0 sz0 Hb0 a Ha0 Hq4). }
assert (LENS : g_lens Tn (ht_frequ K) (set_col (ht_keys K) hs (key Ht j)) (ht_used K) (ht_pal K) (ht_colidx K))
by (apply g_lens_keys; exact (conj LK1 (conj LK2 (conj LK3 (conj LK4 LK5))))).
assert (Harr5 : g_arrs (mrestrict (w_H W3) mem5) fn hn un p1 p2 (ht_frequ K) (set_col (ht_keys K) hs (key Ht j)) (ht_used K) (set_col (ht_pal K) cn (key Ht j)) (ht_colidx K)).
{ apply (g_arrs_pal (w_H W3) (ms_mem ms3) mem5 fn hn un p1 p2 Tn _ _ _ _ _ cn (key Ht j) HKarr LENS SEPK Hcn).
- replace (p1 + 3 * cn) with (p1 + cn * 3) by (clear; lia). exact Hpal5.
- intros a Ha Hn. unfold g_in5 in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (K5 fn (4 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha) | apply (K5 hn (3 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha)
| apply (K5 un Tn ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha) | apply (K5 p1 (3 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha)
| apply (K5 p2 (4 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha) ]; clear - Hn; lia. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fn hn un p1 p2 (ht_ins K hs (key Ht j) (freq Ht j))) end.
{ apply g_cht_of_arrs. cbn [ht_ins ht_frequ ht_keys ht_used ht_pal ht_colidx]. fold cn. fold fv.
apply (g_arrs_cells3 (w_H W3) mem5 _ fn hn un p1 p2 Tn _ _ _ _ _ hs cn fv Harr5 (g_lens_pal _ _ _ _ _ _ cn (key Ht j) LENS) SEPK Hhs ltac:(clear - Hcn HTn24; lia) Hfv32 B1 V4 V3).
intros a Ha Hn. unfold g_in5 in Ha.
assert (Hq : 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ exact (proj1 (KOFF fn (4 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha)) | exact (proj1 (KOFF hn (3 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha))
| exact (proj1 (KOFF un Tn ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha)) | exact (proj1 (KOFF p1 (3 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha))
| exact (proj1 (KOFF p2 (4 * Tn) ltac:(subst TBL; cbn [In]; repeat first [left; reflexivity | right]) a Ha)) ]. }
apply (KP a (proj1 Hq)). intros [Hx | Hx]; [exact (proj2 Hq Hx) | exact (Hn Hx)]. }
idtac "OK-GH".
rga_hand RHT HS HJ5 k; [rga_E_tac HEE6 | ].
exists blk, fim, tb, fq, hh, uu, ha, ix, Ht, ent, p1, p2, hn, un, fn, (ht_ins K hs (key Ht j) (freq Ht j)), j.
rga_cbn_cx_goal. change CHT_SIZE with 48. cbn [ht_ins ht_T ht_cnt]. fold cn. fold Tn. m_inv_auto.
Qed.
End d.
End c.

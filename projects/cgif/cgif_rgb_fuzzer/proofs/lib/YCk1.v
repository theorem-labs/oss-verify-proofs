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
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gH3 : forall (n : nat) (m : nat), rga_fromA B ss_H3 (fun _ => INV_H3 B (S n) m) -> rga_from B ss_H2 (INV_H2 B (S n) m).
Proof.
intros n m RH3. rga_prelude.
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
unfold ss_H2 in HS.
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
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ hn (3 * Tn) HAR3 Hhn_in3) as (_ & Hhnzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ hn (3 * Tn) 7 fpos HAR3 Hhn_in3 Hfin3) as HdF_hn.
unfold zdisjoint in HdF_hn. cbn [fst snd] in HdF_hn. change (fs_frame_bytes 7) with 8192 in HdF_hn. rewrite EFA3 in HdF_hn. fold F in HdF_hn.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ hn (3 * Tn) cid pos HAR3 Hhn_in3 HfinS3) as HdC_hn.
unfold zdisjoint in HdC_hn. cbn [fst snd] in HdC_hn. rewrite EFA3 in HdC_hn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (hn, 3 * Tn) HAR3 HPrt3 ltac:(right; exact Hhn_l)) as HzR_hn.
unfold zdisjoint, block_rng in HzR_hn. cbn [fst snd] in HzR_hn. change (req_size RGB_SIZE) with 64 in HzR_hn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (hn, 3 * Tn) HAR3 HPtb3 ltac:(right; exact Hhn_l)) as HzT_hn.
unfold zdisjoint, block_rng in HzT_hn. cbn [fst snd] in HzT_hn. change (req_size 48) with 48 in HzT_hn.
assert (HT0 : 0 < ht_T Ht) by (clear - HT24; lia). assert (HTn0 : 0 < Tn) by (clear - HTn24; lia).
destruct (g_sep8_of_AR B LAWS ly3 S3 W3 _ _ (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ [(tb, 48)]) fq hh uu (ht_T Ht) p1 p2 hn un fn Tn HAR3
ltac:(eapply Permutation_trans; [exact HPm3|]; rewrite <- !app_assoc; reflexivity) HT0 HTn0) as (SEPON & SEPK).
pose proof (SEPON hh (3 * ht_T Ht) hn (3 * Tn) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Dhh_hn.
pose proof HKinv as ((LK1 & LK2 & LK3 & LK4 & LK5) & (HcntK0 & _) & _). rewrite HKT in LK1, LK2, LK3, LK4, LK5, HcntK0.
pose proof Harr as (Af & Ak & Au).
assert (Hkey3 : col3 trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (hh + 3 * j) (key Ht j))
by (unfold key; apply (arr8_col3 trbsegs _ hh (ht_keys Ht) j Ak); [clear - Hj; lia | rewrite L2; clear - Hj; lia]).
idtac "OK-SEP".
assert (Hsj : 0 <= 3 * j /\ 3 * j + 3 <= 3 * ht_T Ht) by (clear - Hj; lia).
assert (Hdh : 0 <= 3 * hs /\ 3 * hs + 3 <= 3 * Tn) by (clear - Hhs; lia).
assert (Bsrc : 0 <= hh + 3 * j < 2 ^ 64) by (clear - Hhh4096 Hhhceil Hrq_hh Hsj C1; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (hn + 3 * hs)
ltac:(apply (U_add_small_q _ _ _ hn (3 * hs) (U_atom _ 792 hn Rhn Bhn));
[ exact (g_U_zext3 _ _ hs (U_atom _ 1125 hs Rhs Bhs) ltac:(clear - Hhs HTn24; lia)) | clear - Bhn; lia | clear - Hhs; lia | clear - Hhnceil Hrq_hn Hdh C1; lia ]) Ha0.
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
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (hn + 3 * hs) (hh + 3 * j) 3 (-576) (Z_to_bv 64 0x82d00) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Hhn4096 Hhs; lia.
- clear - Hhnceil Hrq_hn Hdh C1; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [| rewrite Hes; clear - Ha Hhnceil Hrq_hn Hdh Hceil Hslo FFS; lia].
replace a with (hn + (a - hn)) by (clear; lia). apply Ahn; [exact Hhn_in3 | clear - Ha Hrq_hn Hdh; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ hn (3 * Tn) (hn + 3 * hs) 3 (proj1 HJ3) Hhn_in3); [clear - Hdh; lia | clear - Hrq_hn Hdh; lia].
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ hn (3 * Tn) (hn + 3 * hs) 3 (proj1 HJ3) Hhn_in3); [clear - Hdh; lia | clear - Hrq_hn Hdh; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ hn (3 * Tn) (hn + 3 * hs) 3 (proj1 HJ3) Hhn_in3); [clear - Hdh; lia | clear - Hrq_hn Hdh; lia | clear; lia].
- split; [clear - Bsrc; lia|]. split; [clear - Hhhceil Hrq_hh Hsj C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); exact (proj1 (HhhP a ltac:(clear - Ha Hsj Hrq_hh; lia)))
| rewrite HspT, Hes; clear - Ha Hhhceil Hrq_hh Hsj Hceil Hslo FFS C1; lia]. }
split; [clear - Dhh_hn Hrq_hh Hrq_hn Hdh Hsj; lia|]. split.
{ apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + 3 * j) 3 (proj1 HJ3) Hhh_in3); [clear - Hsj; lia | clear - Hsj Hrq_hh; lia]. }
split; [apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + 3 * j) 3 (proj1 HJ3) Hhh_in3); [clear - Hsj; lia | clear - Hsj Hrq_hh; lia]|].
intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + 3 * j) 3 (proj1 HJ3) Hhh_in3); [clear - Hsj; lia | clear - Hsj Hrq_hh; lia | clear; lia]. }
idtac "OK-C1".
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
assert (Hfr3 : forall a, 0 <= a < 2 ^ 64 -> ~ (hn + 3 * hs <= a < hn + 3 * hs + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576) ->
aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha1 Ha2; apply Hfr5; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
assert (HWIN3 : forall a, 0 <= a < alloc_ceiling -> ~ (hn <= a < hn + 3 * Tn) ->
0 <= a < 2 ^ 64 /\ ~ (hn + 3 * hs <= a < hn + 3 * hs + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hn Hdh Hceil Hslo FFS C1; lia).
assert (HWSTc3 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> ~ (spZ regs + 0 <= a < spZ regs + 0) ->
0 <= a < 2 ^ 64 /\ ~ (hn + 3 * hs <= a < hn + 3 * hs + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hhnceil Hrq_hn Hdh Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG8 : ((4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= 2147446784 \/ 17594333495296 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= 2147446784 \/ 17594333495296 <= cfp)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880) /\
(3 * Tn <= req_size (3 * Tn) /\ (hn + req_size (3 * Tn) <= 2147446784 \/ 17594333495296 <= hn) /\ (hn + req_size (3 * Tn) <= F \/ F + 8192 <= hn) /\
(r + 64 <= hn \/ hn + req_size (3 * Tn) <= r) /\
(hn + req_size (3 * Tn) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= hn) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid)).
{ unfold gbox, in_app in HFhigh, Hrapp, Hfhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh, Hrapp, Hfhigh. unfold gbox in Hhnzone.
split; [|clear - Hrq_hn Hhnzone HdF_hn HzR_hn HdC_hn Hflo Hfhi; lia].
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil Hrapp; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi Hfhigh; lia|]. split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
assert (HRtb8 : ((4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= 2147446784 \/ 17594333495296 <= tb)) /\
(F + 8192 <= alloc_ceiling /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ 512 <= F / 8) /\ SB = 2147450880) /\
3 * Tn <= req_size (3 * Tn) /\ (tb + 48 <= hn \/ hn + req_size (3 * Tn) <= tb)).
{ unfold gbox in Htbzone. change (req_size 48) with 48 in Htbzone.
split; [|clear - Hrq_hn HzT_hn; lia]. split; [clear - Htb4096 Htbceil Hrqtb Htbzone C1; lia|]. split; [clear - HFceil HFq HF8 HF8lo; lia | reflexivity]. }
idtac "OK-P0".
m_reseatF HS HJ5 fx regs5 CLOB 535808 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP5)
ltac:(idtac; first
[ m_keptWc Hfr3 Hpres5 HJ5 HWIN3 HWSTc3 HRNG8 AG Usp RF E67 E10n E11n 0 0
ltac:(idtac; first [ m_keptW_blk Hfr3 Hpres5 HWIN3 AG 305%nat tb Rtb HRtb8
| ga_kept_consts Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
idtac "OK-RS".
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
clear KP.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) mem5 a) by (intros; reflexivity).
assert (Hkey5 : col3 trbsegs (mrestrict (w_H W3) mem5) (hn + 3 * hs) (key Ht j)) by (exact (g_col3_copy (w_H W3) (ms_mem ms3) mem5 _ _ (key Ht j) Hkey3 Heff5)).
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE5 end.
norm_ss HS.
idtac "OK-P2".
assert (BcK : 0 <= ht_cnt K < 2 ^ 64) by (clear - HcntK0 HTn24; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rcntv : ew Ev 1120 = Z_to_bv 64 (ht_cnt K)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
g_fact HS 1120%nat (mkAF 0 16777216 0)
ltac:(rewrite Rcntv, unsigned_lit_small by exact BcK; change (2 ^ 0) with 1; split; [clear - HcntK0 HTn24; lia|]; split; [apply Z.mod_1_r | clear; lia]).
idtac "OK-FACT".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rp1v : ew Ev 760 = Z_to_bv 64 p1) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rp1) end.
g_cond HS BC_GEU (SAlu ALU_ADD (SOff 760 0) (SMd M_MUL (SOff 1120 0) (SLit 3))) (SOff 760 0)
ltac:(apply (g_ptr_geu _ _ _ p1 (ht_cnt K * 3) (U_atom _ 760 p1 Rp1v Bp1));
[ apply (g_U_mul_small _ (SOff 1120 0) (SLit 3) (ht_cnt K) 3 (U_atom _ 1120 _ Rcntv BcK) ltac:(reflexivity)); clear - HcntK0 HTn24; lia | clear - Bp1; lia | clear - HcntK0; lia | clear - Hp1ceil Hrq_p1 HcntK0 C1; lia ]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK GBspan A_asan_memcpy.
idtac "OK-R0".
all: try (lazymatch goal with |- range_addressable _ (U ?Ev _) _ _ =>
assert (Rtbv : ew Ev 305 = Z_to_bv 64 tb) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb);
assert (E44v : ew Ev 44 = Z_to_bv 64 SB) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E44) | _ => idtac end).
all: try (ga_obl_blk HJ5 Rtbv E44v Htb_in3).
idtac "OK-R1".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-R2".
ga_join HS ss_H3 1200%nat rga_deads_H3 ltac:(idtac).
idtac "OK-J".
assert (KOFF : forall b sz, In (b, sz) TBL -> forall a, b <= a < b + sz -> (0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)) /\ 0 <= a < alloc_ceiling).
{ intros b sz Hb a Ha.
assert (Hsz : 0 < sz /\ 4096 <= b /\ b + sz <= alloc_ceiling).
{ subst TBL. cbn [In] in Hb.
repeat (destruct Hb as [Hb | Hb]; [injection Hb as Eb Es; rewrite <- Eb, <- Es; clear - HT24 HTn24 Hfq4096 Hfqceil Hhh4096 Hhhceil Huu4096 Huuceil Hp14096 Hp1ceil Hp24096 Hp2ceil Hhn4096 Hhnceil Hun4096 Hunceil Hfn4096 Hfnceil; lia|]). destruct Hb. }
pose proof (req_size_pos sz ltac:(clear - Hsz; lia)) as [_ Hrq]. split; [apply (Hoff3 b sz (Hcht_l b sz Hb) a); clear - Ha Hrq; lia | clear - Ha Hsz; lia]. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (KALL : forall b sz, In (b, sz) TBL -> forall a, b <= a < b + sz -> ~ (hn + 3 * hs <= a < hn + 3 * hs + 3) ->
aview trbsegs (w_H W3) mF a = aview trbsegs (w_H W3) (ms_mem ms3) a) end.
{ intros b sz Hb a Ha Hn. destruct (KOFF b sz Hb a Ha) as [[Hq1 Hq2] Hq3]. rewrite (KP a Hq1 Hq2). apply (Hfr3 a Hq1).
intros [Hx | Hx]; [exact (Hn Hx) | rewrite Hes in Hx; clear - Hx Hq3 Hceil Hslo FFS; lia]. }
pose proof (SEPON fq (4 * ht_T Ht) hn (3 * Tn) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Dfq_hn.
pose proof (SEPON uu (ht_T Ht) hn (3 * Tn) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as Duu_hn.
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Hold1 : g_old3 (mrestrict (w_H W3) mF) fq hh uu Ht) end.
{ apply (g_old3_kept (w_H W3) (ms_mem ms3) _ fq hh uu Ht ent Harr Hinv). intros a Ha.
destruct Ha as [Ha | [Ha | Ha]];
[ apply (KALL fq (4 * ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha); clear - Ha Dfq_hn Hdh
| apply (KALL hh (3 * ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha); clear - Ha Dhh_hn Hdh
| apply (KALL uu (ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha); clear - Ha Duu_hn Hdh ]; lia. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (HKarr1 : g_arrs (mrestrict (w_H W3) mF) fn hn un p1 p2 (ht_frequ K) (set_col (ht_keys K) hs (key Ht j)) (ht_used K) (ht_pal K) (ht_colidx K)) end.
{ apply (g_arrs_keys (w_H W3) (ms_mem ms3) _ fn hn un p1 p2 Tn _ _ _ _ _ hs (key Ht j) (g_arrs_of_cht _ _ _ _ _ _ K HKarr) (conj LK1 (conj LK2 (conj LK3 (conj LK4 LK5)))) SEPK Hhs).
- apply (g_col3_kept (w_H W3) mem5 _ _ _ Hkey5). intros kk Hkk.
destruct (KOFF hn (3 * Tn) ltac:(subst TBL; cbn [In]; tauto) (hn + 3 * hs + kk) ltac:(clear - Hkk Hdh; lia)) as [[Hq1 Hq2] _]. exact (KP _ Hq1 Hq2).
- intros a Ha Hn. unfold g_in5 in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (KALL fn (4 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha Hn) | apply (KALL hn (3 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha Hn)
| apply (KALL un Tn ltac:(subst TBL; cbn [In]; tauto) a Ha Hn) | apply (KALL p1 (3 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha Hn)
| apply (KALL p2 (4 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha Hn) ]. }
idtac "OK-M".
rga_hand RH3 HS HJ5 k; [rga_E_tac HEE5 | ].
exists blk, fim, tb, fq, hh, uu, ha, ix, Ht, ent, p1, p2, hn, un, fn, K, j, hs.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto.
Qed.
End d.
End c.

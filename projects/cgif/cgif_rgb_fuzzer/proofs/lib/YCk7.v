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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YCpo YCpq YClz YCqd YCqe YCpy YCq3 YCq4 YCq6 YCq5 YP14 YP15 YI0h YChh YCia YCm1 YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCop.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCkr YCks YCkt YClv.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis TGPV : tgpv_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP1 : forall n : nat,
rga_fromA B ss_TL (fun _ => INV_TL B (S n)) -> (forall m : nat, rga_fromA B ss_PB (fun _ => INV_PB B (S n) m)) -> rga_from B ss_HL (INV_HL B (S n)).
Proof.
intros n RTL RPB. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R467).
rga_cbn_cx R467. fold F in R467.
destruct Hk0 as [Hk0 Hbud].
unfold ss_HL in HS.
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
assert (Himg_in : In (img, fmt * N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. left.
unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himg_in3 : In (img, fmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Himg_in]).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 img _ HAR3 Himg_in3 ltac:(clear - HfN; lia)) as (Himg4096 & Himgceil & Himg16 & Himgpres).
assert (Bimg : 0 <= img < 2 ^ 64) by (clear - Himg4096 Himgceil HfN C1; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx (ht_T Ht)).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) lrest)
by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Himg_l : In (img, fmt * N) lrest).
{ subst lrest. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Hpxoff : forall kk, 0 <= kk < fmt -> 0 <= img + fmt * ix + kk < 2 ^ 64 /\ ~ (m_ZsP F r (img + fmt * ix + kk) \/ tb <= img + fmt * ix + kk < tb + 48)).
{ intros kk Hkk. apply (Hoff3 img (fmt * N) Himg_l). pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as [_ Hrq]. clear - Hkk Hfmt Hix Hrq. nia. }
destruct (m_pixel_of_present trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (img + fmt * ix) fmt) as (pc0 & pop & Hpix3).
{ intros kk Hkk. apply g_mbyte_of_apresent. apply Himgpres. clear - Hkk Hfmt Hix. nia. }
{ exact Hfmt. }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
assert (Hcht_in3 : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) (ablocks B ly3 S3)).
{ intros b sz Hb. eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app. right. apply in_or_app. right. right. exact Hb. }
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hpp_in3 : In (pp, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hxx_in3 : In (xx, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fq _ HAR3 Hfq_in3 ltac:(clear - HT24; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
destruct (g_blk B LAWS _ _ _ _ _ hh _ HAR3 Hhh_in3 ltac:(clear - HT24; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
destruct (g_blk B LAWS _ _ _ _ _ uu _ HAR3 Huu_in3 ltac:(clear - HT24; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
destruct (g_blk B LAWS _ _ _ _ _ pp _ HAR3 Hpp_in3 ltac:(clear - HT24; lia)) as (Hpp4096 & Hppceil & Hpp16 & Hpppres).
destruct (g_blk B LAWS _ _ _ _ _ xx _ HAR3 Hxx_in3 ltac:(clear - HT24; lia)) as (Hxx4096 & Hxxceil & Hxx16 & Hxxpres).
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil HT24 C1; lia).
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil HT24 C1; lia).
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil HT24 C1; lia).
assert (Bpp : 0 <= pp < 2 ^ 64) by (clear - Hpp4096 Hppceil HT24 C1; lia).
assert (Bxx : 0 <= xx < 2 ^ 64) by (clear - Hxx4096 Hxxceil HT24 C1; lia).
assert (Bix : 0 <= ix < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
assert (BT : 0 <= ht_T Ht < 2 ^ 64) by (clear - HT24; lia).
ga_join_fact HS 45%nat (mkAF 4096 140737479966720 0) ltac:(rewrite E45; rewrite unsigned_lit_small by exact Bimg; change (2 ^ 0) with 1; split; [clear - Himg4096 Himgceil HfN C1; lia|]; split; [apply Z.mod_1_r | clear; lia]).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_getPixelVal.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG.
assert (Hpx_rng : 4096 <= img + fmt * ix /\ img + fmt * ix + fmt <= img + fmt * N) by (clear - Himg4096 Hfmt Hix; nia).
g_havoc HS 480%nat [Z_to_bv 64 (img + fmt * ix)].
g_havoc_val HS 480%nat 0%nat (Z_to_bv 64 (img + fmt * ix)) E480.
assert (Bpx : 0 <= img + fmt * ix < 2 ^ 64) by (clear - Hpx_rng Himgceil C1 Hfmt; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E45v : ew Ev 45 = Z_to_bv 64 img) by (rewrite ew_havoc_old by lia; exact E45);
assert (E46v : ew Ev 46 = Z_to_bv 64 fmt) by (rewrite ew_havoc_old by lia; exact E46);
assert (Rixv : ew Ev 456 = Z_to_bv 64 ix) by (rewrite ew_havoc_old by lia; exact Rix) end.
g_pin HS (23%bv : bv 5) (SOff 480 0)
ltac:(apply U_inj; rewrite (U_atom _ 480 _ E480 Bpx); symmetry;
apply (U_add_small_q _ _ _ img (fmt * ix) (U_atom _ 45 img E45v Bimg)
(g_U_pixoff _ 46 456 fmt ix E46v Rixv ltac:(clear - Hfmt; lia) ltac:(clear - Hix HN; unfold RGB_NMAX in HN; lia)));
[clear - Bimg; lia | clear - Hfmt Hix; nia | clear - Bpx; lia]).
g_fact HS 480%nat (mkAF 4096 140737479966720 0)
ltac:(rewrite E480, unsigned_lit_small by exact Bpx; change (2 ^ 0) with 1; split; [clear - Hpx_rng Himgceil C1 Hfmt; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_cond HS BC_GEU (SOff 480 0) (SOff 45 0)
ltac:(rewrite branch_geu_U, (U_atom _ 480 _ E480 Bpx), (U_atom _ 45 img E45v Bimg); apply Bool.negb_true_iff, Z.ltb_ge; clear - Hfmt Hix; nia).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_getPixelVal.
all: lazymatch goal with |- range_addressable _ (U ?Ev _) _ _ =>
assert (Rtbv : ew Ev 305 = Z_to_bv 64 tb) by (rewrite ew_havoc_old by lia; exact Rtb);
assert (E44v : ew Ev 44 = Z_to_bv 64 SB) by (rewrite ew_havoc_old by lia; exact E44) | _ => idtac end.
all: try (unfold GBx; ga_obl_blk HJ3 Rtbv E44v Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG.
norm_ss HS.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mX a = _ =>
assert (Hpix : pixel_at trbsegs (mrestrict (w_H W3) mX) (img + fmt * ix) fmt pc0 pop)
by (apply (g_pixel_at_kept (w_H W3) (ms_mem ms3) mX _ _ _ _ Hpix3 Hfmt); intros kk Hkk; destruct (Hpxoff kk Hkk) as [Hq1 Hq2]; exact (KP _ Hq1 Hq2)) end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
change (Z_to_bv 64 544908) with (Z_to_bv 64 A_getPixelVal).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (TGPV TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
img (fmt * N) (img + fmt * ix) fmt pc0 pop HJ3) end.
- rewrite Rra. apply ret_ok_even; vm_compute; reflexivity.
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear; lia). clear; lia.
- rewrite HspT. clear - Hal32. pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (spZ regs / 32) + -576) with ((2 * (spZ regs / 32) - 36) * 16) by lia. apply Z_mod_mult.
- rewrite HspT, FFS. unfold TGPV_STK. clear. lia.
- rewrite HspT. clear. lia.
- rewrite Ra0. unfold w64. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. exact E480.
- rewrite Ra1. unfold w64. rewrite E46. clear - Hfmt. destruct Hfmt as [-> | ->]; apply bv_eq; reflexivity.
- exact Hfmt.
- exact Himg_in3.
- clear - Hfmt Hix; nia.
- clear - Hpx_rng; lia.
- exact Hpix. }
cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & HP7 & R10 & Hfr7 & Hpres7).
rewrite Rra.
unfold TGPV_STK in Hfr7. rewrite HspT in Hfr7.
clear Ra0 Ra1 Rsp.
assert (KP7 : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) mem7 a = aview trbsegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. rewrite (Hfr7 a Ha ltac:(unfold m_ZsP in Hn; clear - Hn Hceil Hslo FFS; lia)). exact (KP a Ha Hn). }
clear KP. rename KP7 into KP.
pose proof (proj1 HJ7) as HAR7.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 Hrin3) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 Htb_in3) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ tb 48 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb. change (req_size 48) with 48 in HdF_tb.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ r 64 7 fpos HAR3 Hrin3 Hfin3) as HdF_r.
unfold zdisjoint in HdF_r. cbn [fst snd] in HdF_r. change (fs_frame_bytes 7) with 8192 in HdF_r. rewrite EFA3 in HdF_r. fold F in HdF_r. change (req_size 64) with 64 in HdF_r.
assert (HRNG7 : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= F \/ F + 8192 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= F \/ F + 8192 <= cfp)) /\
(4096 <= tb /\ tb + 48 <= alloc_ceiling /\ (tb + 48 <= F \/ F + 8192 <= tb)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880).
{ unfold gbox, in_app in HFhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh. unfold gbox in HdFC.
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil HdF_r; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi HdFC; lia|]. split; [clear - Htb4096 Htbceil Hrqtb HdF_tb; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
m_env_fold HS AG.
m_reseatF HS HJ7 fx regs7 CLOB 534024 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP7)
ltac:(idtac; first
[ g_keptP Hfr7 HRNG7 HJ7 AG Usp RF E67 E10n E11n Rtb F HFpres7 Hrpres7 Htbpres7
ltac:(idtac; m_keptE_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
rreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite R10 in Rres. symmetry in Rres. unfold w64 in Rres.
norm_ss HS.
pose proof Hpix as [(_ & _ & _ & Hcok) _].
pose proof (g_pw_range pc0 pop Hcok) as Hpw32.
g_fact HS 485%nat (mkAF 0 4294967295 0)
ltac:(rewrite Rres, unsigned_lit_small by (clear - Hpw32; lia); change (2 ^ 0) with 1; split; [clear - Hpw32; lia|]; split; [apply Z.mod_1_r | clear; lia]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x8267c.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
2: {
rewrite branch_ne_U, (g_U_pw_shr24 _ 485 pc0 pop Rres Hcok) in Hc. change (U _ (SLit 0)) with 0 in Hc.
assert (Hop : pop = false) by (destruct pop; [discriminate Hc | reflexivity]). subst pop.
assert (Hfmt4 : fmt = 4) by (destruct Hpix as [_ [(_ & Hx) | (Hx & _)]]; [discriminate Hx | exact Hx]).
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x83054.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
rregU HS (12%bv : bv 5) 1 ltac:(reflexivity) Q12.
assert (BF : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
rregU HS (21%bv : bv 5) (tb + 40) ltac:(rewrite (U_atom_off _ 305 tb 40 Rtb) by (clear - Htb4096 Htbceil Hrqtb C1; lia); reflexivity) Q21.
rregU HS (24%bv : bv 5) F ltac:(apply (U_atom _ 467 F R467 BF)) Q24.
slot_val HS (Some 305%nat) 0 0 (Z_to_bv 64 fq) ltac:(exact (g_denot_off0 _ 473 fq Rfq Bfq)) QF.
slot_val HS (Some 305%nat) 0 8 (Z_to_bv 64 hh) ltac:(exact (g_denot_off0 _ 474 hh Rhh Bhh)) QH.
slot_val HS (Some 305%nat) 0 16 (Z_to_bv 64 uu) ltac:(exact (g_denot_off0 _ 475 uu Ruu Buu)) QU.
slot_val HS (Some 305%nat) 0 24 (Z_to_bv 64 pp) ltac:(exact (g_denot_off0 _ 476 pp Rpp Bpp)) QP.
slot_val HS (Some 305%nat) 0 32 (Z_to_bv 64 xx) ltac:(exact (g_denot_off0 _ 477 xx Rxx Bxx)) QX.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (ht_cnt Ht)) ltac:(exact (g_denot_off0 _ 478 _ Rcnt Hcnt64)) QC.
slot_val HS (Some 305%nat) 0 44 (Z_to_bv 64 (ht_T Ht)) ltac:(exact (g_denot_off0 _ 479 _ RT BT)) QT.
slot_val HS (Some 2%nat) (-576) (-392) (Z_to_bv 64 ix) ltac:(exact (g_denot_off0 _ 456 ix Rix Bix)) QI.
ra_join_slots HS ss_TL 1000%nat rga_deads_TL
[(Some 305%nat, 0, 0); (Some 305%nat, 0, 8); (Some 305%nat, 0, 16); (Some 305%nat, 0, 24); (Some 305%nat, 0, 32); (Some 305%nat, 0, 40); (Some 305%nat, 0, 44); (Some 2%nat, (-576), (-392))]
ltac:(idtac; ga_join_val HS 1000%nat 14%nat Q12 N1014; ga_join_val HS 1000%nat 13%nat Q21 N1013; ga_join_val HS 1000%nat 17%nat Q24 N1017;
ga_join_val HS 1000%nat 23%nat QF N1023; ga_join_val HS 1000%nat 24%nat QH N1024; ga_join_val HS 1000%nat 25%nat QU N1025;
ga_join_val HS 1000%nat 26%nat QP N1026; ga_join_val HS 1000%nat 27%nat QX N1027; ga_join_val HS 1000%nat 28%nat QC N1028; ga_join_val HS 1000%nat 29%nat QT N1029;
ga_join_val HS 1000%nat 30%nat QI N1030;
ga_join_fact HS 1014%nat (mkAF 0 1 0) ltac:(rewrite N1014; rewrite unsigned_lit_small by (clear; lia); repeat split; first [clear; lia | reflexivity]);
ga_join_fact HS 1030%nat (mkAF 0 10000 0) ltac:(rewrite N1030; rewrite unsigned_lit_small by exact Bix; change (2 ^ 0) with 1; split; [clear - Hix HN; unfold RGB_NMAX in HN; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1023%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1023; rewrite unsigned_lit_small by exact Bfq; change (2 ^ 4) with 16; split; [clear - Hfq4096 Hfqceil HT24 C1; lia|]; split; [exact Hfq16 | clear; lia]);
ga_join_fact HS 1024%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1024; rewrite unsigned_lit_small by exact Bhh; change (2 ^ 4) with 16; split; [clear - Hhh4096 Hhhceil HT24 C1; lia|]; split; [exact Hhh16 | clear; lia]);
ga_join_fact HS 1025%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1025; rewrite unsigned_lit_small by exact Buu; change (2 ^ 4) with 16; split; [clear - Huu4096 Huuceil HT24 C1; lia|]; split; [exact Huu16 | clear; lia]);
ga_join_fact HS 1026%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1026; rewrite unsigned_lit_small by exact Bpp; change (2 ^ 4) with 16; split; [clear - Hpp4096 Hppceil HT24 C1; lia|]; split; [exact Hpp16 | clear; lia]);
ga_join_fact HS 1027%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1027; rewrite unsigned_lit_small by exact Bxx; change (2 ^ 4) with 16; split; [clear - Hxx4096 Hxxceil HT24 C1; lia|]; split; [exact Hxx16 | clear; lia]);
ga_join_fact HS 1028%nat (mkAF 0 16777216 0) ltac:(rewrite N1028; rewrite unsigned_lit_small by exact Hcnt64; change (2 ^ 0) with 1; split; [clear - Hcnt0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1029%nat (mkAF 524309 16777216 0) ltac:(rewrite N1029; rewrite unsigned_lit_small by exact BT; change (2 ^ 0) with 1; split; [clear - HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
rga_hand RTL HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, 1, ix, Ht, ent.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [m_ewT | split; [exact Tblk | exact Ablk]]|].
split; [split; [m_ewT | split; [exact Tfim | exact Afim]]|].
split; [split; [m_ewT | split; [exact Ttb | exact Atb]]|].
split; [split; [exact N1023 | split; [exact Tfq | exact Afq]]|].
split; [split; [exact N1024 | split; [exact Thh | exact Ahh]]|].
split; [split; [exact N1025 | split; [exact Tuu | exact Auu]]|].
split; [split; [exact N1026 | split; [exact Tpp | exact App]]|].
split; [split; [exact N1027 | split; [exact Txx | exact Axx]]|].
split; [exact N1028|]. split; [exact N1029|]. split; [exact N1014|]. split; [right; split; [reflexivity | exact Hfmt4]|].
split; [exact N1030|]. split; [exact Hix|]. split; [exact Hnix|].
split.
{ lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5) end.
intros b sz Hb i Hi.
assert (Hsz : 0 <= sz) by (clear - Hi; lia). pose proof (req_size_pos sz Hsz) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
exact (KP (b + i) Hq1 Hq2). }
split; [exact Hinv|]. split; [exact HTch|]. split; [clear - Hsum; lia|].
split; [exists av; split; [m_ewT | exact Hav]|]. split; [exact N1013 | exact N1017]. }
rewrite branch_ne_U, (g_U_pw_shr24 _ 485 pc0 pop Rres Hcok) in Hc. change (U _ (SLit 0)) with 0 in Hc.
assert (Hop : pop = true) by (destruct pop; [reflexivity | discriminate Hc]). subst pop.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x8267c.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
set (h0 := hash0 (ht_T Ht) pc0).
assert (Hh0 : 0 <= h0 < ht_T Ht) by (subst h0; unfold hash0; apply Z.mod_pos_bound; clear - HT24; lia).
g_havoc HS 497%nat [Z_to_bv 64 h0; Z_to_bv 64 (uu + h0)].
g_havoc_val HS 497%nat 0%nat (Z_to_bv 64 h0) E497.
g_havoc_val HS 497%nat 1%nat (Z_to_bv 64 (uu + h0)) E498.
m_env_fold HS AG.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE8 end.
assert (UH : forall Ev, ew Ev 485 = Z_to_bv 64 (pixel_word pc0 true) -> ew Ev 479 = Z_to_bv 64 (ht_T Ht) -> U Ev (g_hashx (SOff 485 0) 479) = h0).
{ intros Ev H485 H479. subst h0. apply (g_U_hashx Ev (SOff 485 0) 479 255 pc0 (ht_T Ht) Hcok ltac:(clear; lia)); [|exact H479 | clear - HT24; lia].
rewrite (U_atom Ev 485 _ H485) by (clear - Hpw32; lia). unfold pixel_word. clear. lia. }
g_pin HS (10%bv : bv 5) (SOff 497 0) ltac:(apply U_inj; rewrite (U_atom _ 497 h0 E497) by (clear - Hh0 HT24; lia); symmetry; exact (UH _ Rres RT)).
g_pin HS (11%bv : bv 5) (SOff 498 0)
ltac:(apply U_inj; rewrite (U_atom _ 498 (uu + h0) E498) by (clear - Hh0 HT24 Buu Huuceil C1; lia); symmetry;
rewrite (Z.add_comm uu h0); apply (U_add_small_q _ _ _ h0 uu (UH _ Rres RT) (U_atom _ 475 uu Ruu Buu)); [clear - Hh0; lia | clear - Buu; lia | clear - Hh0 HT24 Huuceil C1; lia]).
g_fact HS 497%nat (mkAF 0 16777215 0)
ltac:(rewrite E497, unsigned_lit_small by (clear - Hh0 HT24; lia); change (2 ^ 0) with 1; split; [clear - Hh0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_fact HS 498%nat (mkAF 4096 140737479966720 0)
ltac:(rewrite E498, unsigned_lit_small by (clear - Hh0 HT24 Buu Huuceil C1; lia); change (2 ^ 0) with 1; split; [clear - Hh0 HT24 Huu4096 Huuceil C1; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_cond HS BC_GEU (SOff 498 0) (SOff 475 0)
ltac:(rewrite branch_geu_U, (U_atom _ 498 (uu + h0) E498), (U_atom _ 475 uu Ruu Buu) by (clear - Hh0 HT24 Buu Huuceil C1; lia); apply Bool.negb_true_iff, Z.ltb_ge; clear - Hh0; lia).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x8267c.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
rregU HS (10%bv : bv 5) h0 ltac:(apply (U_atom _ 497 h0 E497); clear - Hh0 HT24; lia) Q10.
rregU HS (26%bv : bv 5) h0 ltac:(apply (U_atom _ 497 h0 E497); clear - Hh0 HT24; lia) Q26.
rregU HS (20%bv : bv 5) 0 ltac:(reflexivity) Q20.
ra_join_slots HS ss_PB 520%nat rga_deads_PB (@nil (option nat * Z * Z))
ltac:(idtac; ga_join_val HS 520%nat 0%nat Q10 N520; ga_join_val HS 520%nat 1%nat Q26 N521; ga_join_val HS 520%nat 2%nat Q20 N522;
ga_join_fact HS 520%nat (mkAF 0 16777215 0) ltac:(rewrite N520; rewrite unsigned_lit_small by (clear - Hh0 HT24; lia); change (2 ^ 0) with 1; split; [clear - Hh0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 521%nat (mkAF 0 16777215 0) ltac:(rewrite N521; rewrite unsigned_lit_small by (clear - Hh0 HT24; lia); change (2 ^ 0) with 1; split; [clear - Hh0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 522%nat (mkAF 0 16777216 0) ltac:(rewrite N522; rewrite unsigned_lit_small by (clear; lia); repeat split; first [clear; lia | reflexivity])).
destruct (find_off_exists Ht ent Hinv pc0) as [js Hjs].
destruct (find_off_spec Ht ent Hinv pc0 js Hjs) as (Hjs0 & _ & _).
rga_hand (RPB (Z.to_nat js)) HS HJ7 k; [rga_E_tac HEE8 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, pc0, js, 0.
split.
{ unfold g_trip. rga_cbn_cx_goal.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [m_ewT | split; [exact Tblk | exact Ablk]]|].
split; [split; [m_ewT | split; [exact Tfim | exact Afim]]|].
split; [split; [m_ewT | split; [exact Ttb | exact Atb]]|].
split; [split; [m_ewT | split; [exact Tfq | exact Afq]]|].
split; [split; [m_ewT | split; [exact Thh | exact Ahh]]|].
split; [split; [m_ewT | split; [exact Tuu | exact Auu]]|].
split; [split; [m_ewT | split; [exact Tpp | exact App]]|].
split; [split; [m_ewT | split; [exact Txx | exact Axx]]|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [m_ewT|]. split; [exact Hix|]. split; [exact Hnix|].
split.
{ lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5) end.
intros b sz Hb i Hi.
assert (Hsz : 0 <= sz) by (clear - Hi; lia). pose proof (req_size_pos sz Hsz) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
exact (KP (b + i) Hq1 Hq2). }
split; [exact Hinv|]. split; [exact HTch|]. split; [clear - Hsum; lia|].
exists av. split; [m_ewT | exact Hav]. }
split.
{ unfold g_pix. rga_cbn_cx_goal. split; [m_ewT|].
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mX a = _ =>
apply (g_pixel_at_kept (w_H W3) (ms_mem ms3) mX _ _ _ _ Hpix3 Hfmt) end.
intros kk Hkk. destruct (Hpxoff kk Hkk) as [Hq1 Hq2]. exact (KP _ Hq1 Hq2). }
split; [exact Hjs|]. split; [clear - Hjs0; lia|]. split; [rewrite Z2Nat.id by (clear - Hjs0; lia); clear; lia|].
rewrite (probe_start Ht ent Hinv pc0). fold h0. split; [exact N520|]. split; [exact N521 | exact N522].
Qed.
End d.
End c.

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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClc YCld YCkr YCks YCkt YCku YCkv YClv.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP5 : forall n : nat, rga_fromA B ss_RT (fun _ => INV_RT B (S n)) -> rga_from B ss_M2 (INV_M2 B (S n)).
Proof.
intros n RRT. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & pc0 & js & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & (R480 & Hpix3) & Hjs & Huz & R521 & R522).
rga_cbn_cx R480. rga_cbn_cx Hpix3.
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_M2 in HS.
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
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
idtac "OK-B".
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
idtac "OK-BLK".
pose proof (inv_T_pos Ht ent Hinv) as HTpos.
set (hs := cyc (ht_T Ht) (hash0 (ht_T Ht) pc0) js) in *.
assert (Hhs : 0 <= hs < ht_T Ht) by (subst hs; apply cyc_range; exact HTpos).
set (uv := usedz Ht hs).
assert (Huv : uv = 0 \/ uv = 1) by (subst uv; exact (inv_used01 Ht ent Hinv hs Hhs)).
destruct Harr as (Af & Ak & Au & Ap & Ax).
assert (Vuv : mbyte trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (uu + hs) = Some (Z_to_bv 8 uv)).
{ destruct (Au (Z.to_nat hs) ltac:(clear - Hhs L1; unfold zlen in L1; lia)) as [Vb _]. rewrite Z2Nat.id in Vb by (clear - Hhs; lia). exact Vb. }
idtac "OK-PRE".
assert (Hhs64 : 0 <= hs < 2 ^ 64) by (clear - Hhs HT24; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) HAR3 Hpp_in3) as (_ & Hppzone & _ & _).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq3T].
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as [_ HrqfN].
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) 7 fpos HAR3 Hpp_in3 Hfin3) as HdF_pp.
unfold zdisjoint in HdF_pp. cbn [fst snd] in HdF_pp. change (fs_frame_bytes 7) with 8192 in HdF_pp. rewrite EFA3 in HdF_pp. fold F in HdF_pp.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) cid pos HAR3 Hpp_in3 HfinS3) as HdC_pp.
unfold zdisjoint in HdC_pp. cbn [fst snd] in HdC_pp. rewrite EFA3 in HdC_pp.
assert (Hpp_l : In (pp, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (pp, 3 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hpp_l)) as HzR_pp.
unfold zdisjoint, block_rng in HzR_pp. cbn [fst snd] in HzR_pp. change (req_size RGB_SIZE) with 64 in HzR_pp.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (pp, 3 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hpp_l)) as HzT_pp.
unfold zdisjoint, block_rng in HzT_pp. cbn [fst snd] in HzT_pp. change (req_size 48) with 48 in HzT_pp.
assert (HzI_pp : pp + req_size (3 * ht_T Ht) <= img \/ img + req_size (fmt * N) <= pp).
{ assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx (ht_T Ht) ++ ((r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * ht_T Ht) (img, fmt * N) HAR3 HPx ltac:(cbn [cht_blocks In]; tauto)
ltac:(right; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; unfold timg_block; destruct Hfmt as [-> | ->]; left; reflexivity)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. exact Dd. }
assert (SEP5 : g_sep5 fq hh uu pp xx (ht_T Ht)).
{ apply (g_sep5_of_AR B LAWS ly3 S3 _ _ _ (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ [(tb, 48)]) fq hh uu pp xx (ht_T Ht) HAR3); [|exact HTpos].
eapply Permutation_trans; [exact HPm3|]. rewrite <- !app_assoc. reflexivity. }
set (cn := ht_cnt Ht) in *.
assert (Hcn : 0 <= cn < ht_T Ht) by (subst cn; exact Hcnt0).
idtac "OK-SEP".
assert (Bpx : 0 <= img + fmt * ix < 2 ^ 64) by (clear - Himg4096 Himgceil Hfmt Hix HfN C1; nia).
assert (Hpx : 0 <= fmt * ix /\ fmt * ix + fmt <= fmt * N) by (clear - Hfmt Hix; nia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (pp + cn * 3)
ltac:(apply (U_add_small_q _ _ _ pp (cn * 3) (U_atom _ 476 pp Rpp Bpp));
[ apply (g_U_mul_small _ (SOff 478 0) (SLit 3) cn 3 (U_atom _ 478 cn Rcnt Hcnt64) ltac:(reflexivity)); clear - Hcn HT24; lia | clear - Bpp; lia | clear - Hcn; lia | clear - Hppceil Hcn HT24 C1; lia ]) Ha0.
rregU HS (11%bv : bv 5) (img + fmt * ix) ltac:(apply (U_atom _ 480 _ R480 Bpx)) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) (proj1 HJ3) Himg_in3) as (_ & _ & _ & _ & HimgP & _).
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
idtac "OK-C0".
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (pp + cn * 3) (img + fmt * ix) 3 (-576) (Z_to_bv 64 0x828ac) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Hpp4096 Hcn; lia.
- clear - Hppceil Hrq3T Hcn C1; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [| rewrite Hes; clear - Ha Hppceil Hrq3T Hcn Hceil Hslo FFS; lia].
replace a with (pp + (a - pp)) by (clear; lia). apply App; [exact Hpp_in3 | clear - Ha Hrq3T Hcn; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) (pp + cn * 3) 3 (proj1 HJ3) Hpp_in3); [clear - Hcn; lia | clear - Hrq3T Hcn; lia].
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) (pp + cn * 3) 3 (proj1 HJ3) Hpp_in3); [clear - Hcn; lia | clear - Hrq3T Hcn; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) (pp + cn * 3) 3 (proj1 HJ3) Hpp_in3); [clear - Hcn; lia | clear - Hrq3T Hcn; lia | clear; lia].
- split; [clear - Bpx; lia|]. split; [clear - Himgceil HrqfN Hpx Hfmt C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); exact (proj1 (HimgP a ltac:(clear - Ha Hpx HrqfN Hfmt; lia)))
| rewrite HspT, Hes; clear - Ha Himgceil HrqfN Hpx Hfmt Hceil Hslo FFS C1; lia]. }
split; [clear - HzI_pp Hrq3T HrqfN Hcn Hpx Hfmt; lia|]. split.
{ apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ img (fmt * N) (img + fmt * ix) 3 (proj1 HJ3) Himg_in3); [clear - Hpx; lia | clear - Hpx HrqfN Hfmt; lia]. }
split; [apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ img (fmt * N) (img + fmt * ix) 3 (proj1 HJ3) Himg_in3); [clear - Hpx; lia | clear - Hpx HrqfN Hfmt; lia]|].
intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ img (fmt * N) (img + fmt * ix) 3 (proj1 HJ3) Himg_in3); [clear - Hpx; lia | clear - Hpx HrqfN Hfmt; lia | clear; lia]. }
idtac "OK-C1".
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
assert (Hfr3 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp + cn * 3 <= a < pp + cn * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576) ->
aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha1 Ha2; apply Hfr5; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
assert (HWIN3 : forall a, 0 <= a < alloc_ceiling -> ~ (pp <= a < pp + 3 * ht_T Ht) ->
0 <= a < 2 ^ 64 /\ ~ (pp + cn * 3 <= a < pp + cn * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hn Hcn Hceil Hslo FFS C1; lia).
assert (HWSTc3 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> ~ (spZ regs + 0 <= a < spZ regs + 0) ->
0 <= a < 2 ^ 64 /\ ~ (pp + cn * 3 <= a < pp + cn * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hppceil Hrq3T Hcn Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG8 : ((4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= 2147446784 \/ 17594333495296 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= 2147446784 \/ 17594333495296 <= cfp)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880) /\
(3 * ht_T Ht <= req_size (3 * ht_T Ht) /\ (pp + req_size (3 * ht_T Ht) <= 2147446784 \/ 17594333495296 <= pp) /\ (pp + req_size (3 * ht_T Ht) <= F \/ F + 8192 <= pp) /\
(r + 64 <= pp \/ pp + req_size (3 * ht_T Ht) <= r) /\
(pp + req_size (3 * ht_T Ht) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= pp) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid)).
{ unfold gbox, in_app in HFhigh, Hrapp, Hfhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh, Hrapp, Hfhigh. unfold gbox in Hppzone.
split; [|clear - Hrq3T Hppzone HdF_pp HzR_pp HdC_pp Hflo Hfhi; lia].
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil Hrapp; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi Hfhigh; lia|]. split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
assert (HRtb8 : ((4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= 2147446784 \/ 17594333495296 <= tb)) /\
(F + 8192 <= alloc_ceiling /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ 512 <= F / 8) /\ SB = 2147450880) /\
3 * ht_T Ht <= req_size (3 * ht_T Ht) /\ (tb + 48 <= pp \/ pp + req_size (3 * ht_T Ht) <= tb)).
{ unfold gbox in Htbzone. change (req_size 48) with 48 in Htbzone.
split; [|clear - Hrq3T HzT_pp; lia]. split; [clear - Htb4096 Htbceil Hrqtb Htbzone C1; lia|]. split; [clear - HFceil HFq HF8 HF8lo; lia | reflexivity]. }
idtac "OK-P0".
m_reseatF HS HJ5 fx regs5 CLOB 534700 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP5)
ltac:(idtac; first
[ m_keptWc Hfr3 Hpres5 HJ5 HWIN3 HWSTc3 HRNG8 AG Usp RF E67 E10n E11n 0 0
ltac:(idtac; first [ m_keptW_blk Hfr3 Hpres5 HWIN3 AG 305%nat tb Rtb HRtb8
| ga_kept_consts Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
idtac "OK-RS".
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
clear KP.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ ((m_ZsP F r a \/ tb <= a < tb + 48) \/ g_cells3 fq uu xx hs a) -> aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) mem5 a) by (intros; reflexivity).
assert (Hpal5 : col3 trbsegs (mrestrict (w_H W3) mem5) (pp + cn * 3) pc0) by (exact (g_col3_copy (w_H W3) (ms_mem ms3) mem5 _ _ pc0 (proj1 Hpix3) Heff5)).
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE5 end.
norm_ss HS.
idtac "OK-P2".
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq4T].
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as [_ HrqT].
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ uu (ht_T Ht) HAR3 Huu_in3) as (_ & Huuzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ uu (ht_T Ht) 7 fpos HAR3 Huu_in3 Hfin3) as HdF_uu.
unfold zdisjoint in HdF_uu. cbn [fst snd] in HdF_uu. change (fs_frame_bytes 7) with 8192 in HdF_uu. rewrite EFA3 in HdF_uu. fold F in HdF_uu.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ uu (ht_T Ht) cid pos HAR3 Huu_in3 HfinS3) as HdC_uu.
unfold zdisjoint in HdC_uu. cbn [fst snd] in HdC_uu. rewrite EFA3 in HdC_uu.
assert (Huu_l : In (uu, ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (uu, ht_T Ht) HAR3 HPrt3 ltac:(right; exact Huu_l)) as HzR_uu.
unfold zdisjoint, block_rng in HzR_uu. cbn [fst snd] in HzR_uu. change (req_size RGB_SIZE) with 64 in HzR_uu.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (uu, ht_T Ht) HAR3 HPtb3 ltac:(right; exact Huu_l)) as HzT_uu.
unfold zdisjoint, block_rng in HzT_uu. cbn [fst snd] in HzT_uu. change (req_size 48) with 48 in HzT_uu.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ xx (4 * ht_T Ht) HAR3 Hxx_in3) as (_ & Hxxzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ xx (4 * ht_T Ht) 7 fpos HAR3 Hxx_in3 Hfin3) as HdF_xx.
unfold zdisjoint in HdF_xx. cbn [fst snd] in HdF_xx. change (fs_frame_bytes 7) with 8192 in HdF_xx. rewrite EFA3 in HdF_xx. fold F in HdF_xx.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ xx (4 * ht_T Ht) cid pos HAR3 Hxx_in3 HfinS3) as HdC_xx.
unfold zdisjoint in HdC_xx. cbn [fst snd] in HdC_xx. rewrite EFA3 in HdC_xx.
assert (Hxx_l : In (xx, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (xx, 4 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hxx_l)) as HzR_xx.
unfold zdisjoint, block_rng in HzR_xx. cbn [fst snd] in HzR_xx. change (req_size RGB_SIZE) with 64 in HzR_xx.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (xx, 4 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hxx_l)) as HzT_xx.
unfold zdisjoint, block_rng in HzT_xx. cbn [fst snd] in HzT_xx. change (req_size 48) with 48 in HzT_xx.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) HAR3 Hfq_in3) as (_ & Hfqzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) 7 fpos HAR3 Hfq_in3 Hfin3) as HdF_fq.
unfold zdisjoint in HdF_fq. cbn [fst snd] in HdF_fq. change (fs_frame_bytes 7) with 8192 in HdF_fq. rewrite EFA3 in HdF_fq. fold F in HdF_fq.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) cid pos HAR3 Hfq_in3 HfinS3) as HdC_fq.
unfold zdisjoint in HdC_fq. cbn [fst snd] in HdC_fq. rewrite EFA3 in HdC_fq.
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (fq, 4 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hfq_l)) as HzR_fq.
unfold zdisjoint, block_rng in HzR_fq. cbn [fst snd] in HzR_fq. change (req_size RGB_SIZE) with 64 in HzR_fq.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (fq, 4 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hfq_l)) as HzT_fq.
unfold zdisjoint, block_rng in HzT_fq. cbn [fst snd] in HzT_fq. change (req_size 48) with 48 in HzT_fq.
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
idtac "OK-SEP3".
assert (Hc1_rng : 4096 <= uu + hs /\ uu + hs + 1 <= alloc_ceiling) by (clear - Huu4096 Huuceil Hhs; lia).
assert (Hc2_rng : 4096 <= xx + 4 * hs /\ xx + 4 * hs + 4 <= alloc_ceiling) by (clear - Hxx4096 Hxxceil Hhs Hrq4T; lia).
assert (Hc3_rng : 4096 <= fq + 4 * hs /\ fq + 4 * hs + 4 <= alloc_ceiling) by (clear - Hfq4096 Hfqceil Hhs Hrq4T; lia).
assert (Bc1 : 0 <= uu + hs < 2 ^ 64) by (clear - Hc1_rng C1; lia).
assert (Bc2 : 0 <= xx + 4 * hs < 2 ^ 64) by (clear - Hc2_rng C1; lia).
assert (Bc3 : 0 <= fq + 4 * hs < 2 ^ 64) by (clear - Hc3_rng C1; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ uu (ht_T Ht) (proj1 HJ5) Huu_in3) as (_ & _ & _ & _ & Huupres1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ xx (4 * ht_T Ht) (proj1 HJ5) Hxx_in3) as (_ & _ & _ & _ & Hxxpres1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fq (4 * ht_T Ht) (proj1 HJ5) Hfq_in3) as (_ & _ & _ & _ & Hfqpres1 & _).
g_havoc HS 680%nat [Z_to_bv 64 (uu + hs); Z_to_bv 64 (xx + 4 * hs); Z_to_bv 64 (fq + 4 * hs)].
g_havoc_val HS 680%nat 0%nat (Z_to_bv 64 (uu + hs)) E680.
g_havoc_val HS 680%nat 1%nat (Z_to_bv 64 (xx + 4 * hs)) E681.
g_havoc_val HS 680%nat 2%nat (Z_to_bv 64 (fq + 4 * hs)) E682.
m_env_fold HS AG.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE6 end.
idtac "OK-CL0".
g_region HS AG (YQ0b.mkRegion (Some 680%nat) 0 1 0 1 [])
ltac:(rewrite E680, unsigned_lit_small by exact Bc1;
split; [clear - Hc1_rng; lia|]; split; [clear - Hc1_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Huupres1 (uu + hs + o) ltac:(clear - Ho Hhs HrqT; lia))) | apply Forall_nil ])
ltac:(first [ clear - Hc1_rng Hceil Hslo FFS Hhs HrqT; lia
| destruct Huuzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs HrqT HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_uu Hhs HrqT; lia
| clear - HdC_uu Hhs HrqT Hflo Hfhi; lia
| clear - HzR_uu Hhs HrqT; lia
| clear - HzT_uu Hhs HrqT; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CL1".
g_region HS AG (YQ0b.mkRegion (Some 681%nat) 0 4 0 4 [])
ltac:(rewrite E681, unsigned_lit_small by exact Bc2;
split; [clear - Hc2_rng; lia|]; split; [clear - Hc2_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hxxpres1 (xx + 4 * hs + o) ltac:(clear - Ho Hhs Hrq4T; lia))) | apply Forall_nil ])
ltac:(first [ clear - Hc2_rng Hceil Hslo FFS Hhs Hrq4T; lia
| destruct Hxxzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs Hrq4T HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_xx Hhs Hrq4T; lia
| clear - HdC_xx Hhs Hrq4T Hflo Hfhi; lia
| clear - HzR_xx Hhs Hrq4T; lia
| clear - HzT_xx Hhs Hrq4T; lia
| unfold g_sep5 in SEP5; clear - SEP5 Hhs HrqT Hrq4T; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CL2".
g_region HS AG (YQ0b.mkRegion (Some 682%nat) 0 4 0 4 [])
ltac:(rewrite E682, unsigned_lit_small by exact Bc3;
split; [clear - Hc3_rng; lia|]; split; [clear - Hc3_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hfqpres1 (fq + 4 * hs + o) ltac:(clear - Ho Hhs Hrq4T; lia))) | apply Forall_nil ])
ltac:(first [ clear - Hc3_rng Hceil Hslo FFS Hhs Hrq4T; lia
| destruct Hfqzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs Hrq4T HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_fq Hhs Hrq4T; lia
| clear - HdC_fq Hhs Hrq4T Hflo Hfhi; lia
| clear - HzR_fq Hhs Hrq4T; lia
| clear - HzT_fq Hhs Hrq4T; lia
| unfold g_sep5 in SEP5; clear - SEP5 Hhs HrqT Hrq4T; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CL3".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 475 0) (SOff 521 0)) (SOff 680 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 680 _ E680 Bc1); apply (U_add_small_q _ _ _ uu hs (U_atom _ 475 uu Ruu Buu) (U_atom _ 521 hs R521 Hhs64)); [clear - Buu; lia | clear - Hhs; lia | clear - Bc1; lia])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 477 0) (SAlu ALU_SLL (SOff 521 0) (SLit 2))) (SOff 681 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 681 _ E681 Bc2); replace (xx + 4 * hs) with (xx + hs * 2 ^ 2) by (clear; lia);
apply (U_add_small_q _ _ _ xx (hs * 2 ^ 2) (U_atom _ 477 xx Rxx Bxx)
(U_sll_small_q _ _ hs 2 (U_atom _ 521 hs R521 Hhs64) ltac:(clear - Hhs; lia) ltac:(clear; lia) ltac:(clear - Hhs HT24; lia)));
[ clear - Bxx; lia | clear - Hhs; lia | clear - Bc2; lia ])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 473 0) (SAlu ALU_SLL (SOff 521 0) (SLit 2))) (SOff 682 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 682 _ E682 Bc3); replace (fq + 4 * hs) with (fq + hs * 2 ^ 2) by (clear; lia);
apply (U_add_small_q _ _ _ fq (hs * 2 ^ 2) (U_atom _ 473 fq Rfq Bfq)
(U_sll_small_q _ _ hs 2 (U_atom _ 521 hs R521 Hhs64) ltac:(clear - Hhs; lia) ltac:(clear; lia) ltac:(clear - Hhs HT24; lia)));
[ clear - Bfq; lia | clear - Hhs; lia | clear - Bc3; lia ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
g_fact HS 680%nat (mkAF 4096 140737479966720 0)
ltac:(rewrite E680, unsigned_lit_small by exact Bc1; change (2 ^ 0) with 1; split; [clear - Hc1_rng C1; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_fact HS 681%nat (mkAF 4096 140737479966720 2)
ltac:(rewrite E681, unsigned_lit_small by exact Bc2; change (2 ^ 2) with 4; split; [clear - Hc2_rng C1; lia|]; split; [pose proof (Z.div_mod xx 16 ltac:(clear; lia)) as D16; rewrite Hxx16, Z.add_0_r in D16; rewrite D16; replace (16 * (xx / 16) + 4 * hs) with ((4 * (xx / 16) + hs) * 4) by (clear; lia); apply Z_mod_mult | clear; lia]).
g_fact HS 682%nat (mkAF 4096 140737479966720 2)
ltac:(rewrite E682, unsigned_lit_small by exact Bc3; change (2 ^ 2) with 4; split; [clear - Hc3_rng C1; lia|]; split; [pose proof (Z.div_mod fq 16 ltac:(clear; lia)) as D16; rewrite Hfq16, Z.add_0_r in D16; rewrite D16; replace (16 * (fq / 16) + 4 * hs) with ((4 * (fq / 16) + hs) * 4) by (clear; lia); apply Z_mod_mult | clear; lia]).
g_cond HS BC_GEU (SOff 680 0) (SOff 475 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 680 0) (SOff 475 0) (uu + hs) uu (U_atom _ 680 _ E680 Bc1) (U_atom _ 475 uu Ruu Buu)); clear - Hhs; lia).
g_cond HS BC_GEU (SOff 681 0) (SOff 477 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 681 0) (SOff 477 0) (xx + 4 * hs) xx (U_atom _ 681 _ E681 Bc2) (U_atom _ 477 xx Rxx Bxx)); clear - Hhs; lia).
g_cond HS BC_GEU (SOff 682 0) (SOff 473 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 682 0) (SOff 473 0) (fq + 4 * hs) fq (U_atom _ 682 _ E682 Bc3) (U_atom _ 473 fq Rfq Bfq)); clear - Hhs; lia).
reshok_bx HS 44%nat.
idtac "OK-AL".
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK GBspan 0x829f8.
idtac "OK-RUN".
all: try (m_obl_cell HJ5 E680 E44 Huu_in3 ltac:(idtac; first [clear - Hc1_rng C1; lia | clear - Hhs HrqT; lia])).
all: try (m_obl_cell HJ5 E681 E44 Hxx_in3 ltac:(idtac; first [clear - Hc2_rng C1; lia | clear - Hhs Hrq4T; lia])).
all: try (m_obl_cell HJ5 E682 E44 Hfq_in3 ltac:(idtac; first [clear - Hc3_rng C1; lia | clear - Hhs Hrq4T; lia])).
all: try (ga_obl_blk HJ5 Rtb E44 Htb_in3).
idtac "OK-OB".
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(fun nb => first [ m_awr_cell 680%nat E680 uu Auu Huu_in3 ltac:(idtac; first [clear - Hc1_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hhs HrqT; lia end]) nb
| m_awr_cell 681%nat E681 xx Axx Hxx_in3 ltac:(idtac; first [clear - Hc2_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hhs Hrq4T; lia end]) nb
| m_awr_cell 682%nat E682 fq Afq Hfq_in3 ltac:(idtac; first [clear - Hc3_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hhs Hrq4T; lia end]) nb ]).
idtac "OK-AWR".
g_kept_run HFr AG (fun a : Z => (m_ZsP F r a \/ tb <= a < tb + 48) \/ (a = uu + hs \/ xx + 4 * hs <= a < xx + 4 * hs + 4 \/ fq + 4 * hs <= a < fq + 4 * hs + 4)) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-KEPT".
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (Rcntz : ew Ex 478 = Z_to_bv 64 cn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt);
assert (HB680 : bv_unsigned (ew Ex 680) = uu + hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E680; apply unsigned_lit_small; exact Bc1);
assert (HB681 : bv_unsigned (ew Ex 681) = xx + 4 * hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E681; apply unsigned_lit_small; exact Bc2);
assert (HB682 : bv_unsigned (ew Ex 682) = fq + 4 * hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E682; apply unsigned_lit_small; exact Bc3);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRc3; cbn [ms_mem restrict] in HRc3;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 1 _ HS eq_refl) as HRc2; cbn [ms_mem restrict] in HRc2;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 2 _ HS eq_refl) as HRc1; cbn [ms_mem restrict] in HRc1;
lazymatch type of HRc3 with region_ok _ _ _ (YQ0b.mkRegion (Some 682%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 682 (fq + 4 * hs) cs lo hi wlo whi 0 4%N (SLit 1) HRc3 HB682 ltac:(cbn; tauto) ltac:(cbn; lia)) as V3 end;
lazymatch type of HRc2 with region_ok _ _ _ (YQ0b.mkRegion (Some 681%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 681 (xx + 4 * hs) cs lo hi wlo whi 0 4%N (SOff 478 0) HRc2 HB681 ltac:(cbn; tauto) ltac:(cbn; lia)) as V2;
change (bv_unsigned (sv_denot Ex (SOff 478 0))) with (U Ex (SOff 478 0)) in V2; rewrite (U_atom Ex 478 cn Rcntz Hcnt64) in V2 end;
lazymatch type of HRc1 with region_ok _ _ _ (YQ0b.mkRegion (Some 680%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 680 (uu + hs) cs lo hi wlo whi 0 1%N (SLit 1) HRc1 HB680 ltac:(cbn; tauto) ltac:(cbn; lia)) as V1 end;
clear HRc1 HRc2 HRc3 end.
change (bv_unsigned (sv_denot _ (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in V3.
change (bv_unsigned (sv_denot _ (SLit 1)) mod 2 ^ (8 * Z.of_N 1)) with 1 in V1.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V2. rewrite Z.mod_small in V2 by (clear - Hcn HT24; lia).
rewrite Z.add_0_r in V1, V2, V3. change (N.to_nat 4) with 4%nat in V2, V3. change (N.to_nat 1) with 1%nat in V1.
assert (B1 : mbyte trbsegs _ (uu + hs) = Some (Z_to_bv 8 1)) by (pose proof (V1 0%nat ltac:(lia)) as Vb; rewrite Z.add_0_r in Vb; exact Vb).
idtac "OK-MEM".
assert (Bcn1 : 0 <= cn + 1 < 2 ^ 64) by (clear - Hcn HT24; lia).
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (cn + 1)) ltac:(exact (g_denot_off _ 478 cn 1 Rcntz Hcnt64)) QC.
ra_join_slots HS ss_RT 700%nat rga_deads_RT [(Some 305%nat, 0, 40)]
ltac:(idtac; ga_join_val HS 700%nat 16%nat QC N716;
ga_join_fact HS 716%nat (mkAF 0 16777216 0) ltac:(rewrite N716; rewrite unsigned_lit_small by exact Bcn1; change (2 ^ 0) with 1; split; [clear - Hcn HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-JOIN".
pose proof Hpix3 as [(_ & _ & _ & Hcok) _].
pose proof (zsum_ge_length ent (ent_freq_pos Ht ent Hinv)) as Hlen_s.
pose proof Hinv as (_ & (_ & Helen & _) & _). fold cn in Helen.
assert (Hcn_s : cn <= 10000) by (clear - Hlen_s Helen Hsum Hix HN; unfold RGB_NMAX in HN; lia).
pose proof (ht_ins_inv Ht ent Hinv hs pc0 1 (find_slot_of_off Ht pc0 js Hjs) Huz Hcok ltac:(clear; lia) ltac:(fold cn; clear - Hcn_s HT24; lia)) as Hinv1.
assert (Hsum2 : zsum (map snd (ent ++ [(pc0, 1)])) <= ix + 1) by (rewrite map_app, zsum_app; cbn [map snd zsum]; clear - Hsum; cbn; lia).
assert (SEPK : forall a, g_in5 fq hh uu pp xx (ht_T Ht) a -> (0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)) /\ 0 <= a < alloc_ceiling).
{ intros a Ha. split.
- destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (Hoff3 fq (4 * ht_T Ht) Hfq_l) | apply (Hoff3 hh (3 * ht_T Ht) Hhh_l) | apply (Hoff3 uu (ht_T Ht) Huu_l) | apply (Hoff3 pp (3 * ht_T Ht) Hpp_l) | apply (Hoff3 xx (4 * ht_T Ht) Hxx_l) ];
clear - Ha Hrq4T Hrq3T HrqT; lia.
- clear - Ha Hfq4096 Hfqceil Hhh4096 Hhhceil Huu4096 Huuceil Hpp4096 Hppceil Hxx4096 Hxxceil Hrq4T Hrq3T HrqT. unfold g_in5 in Ha. lia. }
assert (LENS : g_lens (ht_T Ht) (ht_frequ Ht) (set_col (ht_keys Ht) hs pc0) (ht_used Ht) (ht_pal Ht) (ht_colidx Ht))
by (apply g_lens_keys; exact (conj L1 (conj L2 (conj L3 (conj L4 L5))))).
assert (Harr5 : g_arrs (mrestrict (w_H W3) mem5) fq hh uu pp xx (ht_frequ Ht) (set_col (ht_keys Ht) hs pc0) (ht_used Ht) (set_col (ht_pal Ht) cn pc0) (ht_colidx Ht)).
{ apply (g_arrs_pal (w_H W3) (ms_mem ms3) mem5 fq hh uu pp xx (ht_T Ht) _ _ _ _ _ cn pc0 (conj Af (conj Ak (conj Au (conj Ap Ax)))) LENS SEP5 Hcn).
- replace (pp + 3 * cn) with (pp + cn * 3) by (clear; lia). exact Hpal5.
- intros a Ha Hn. destruct (SEPK a Ha) as [[Hq1 Hq2] Hq3]. apply (Hfr3 a Hq1).
intros [Hx | Hx]; [apply Hn; clear - Hx; lia | rewrite Hes in Hx; clear - Hx Hq3 Hceil Hslo FFS; lia]. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx (ht_ins Ht hs pc0 1)) end.
{ apply g_cht_of_arrs. cbn [ht_ins ht_frequ ht_keys ht_used ht_pal ht_colidx]. fold cn.
apply (g_arrs_cells3 (w_H W3) mem5 _ fq hh uu pp xx (ht_T Ht) _ _ _ _ _ hs cn 1 Harr5 (g_lens_pal _ _ _ _ _ _ cn pc0 LENS) SEP5 Hhs ltac:(clear - Hcn HT24; lia) ltac:(clear; lia) B1 V2 V3).
intros a Ha Hn. destruct (SEPK a Ha) as [[Hq1 Hq2] Hq3]. apply (KP a Hq1). intros [Hx | Hx]; [exact (Hq2 Hx) | exact (Hn Hx)]. }
idtac "OK-GH".
rga_hand RRT HS HJ5 k; [rga_E_tac HEE6 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, (ht_ins Ht hs pc0 1), (ent ++ [(pc0, 1)]).
rga_cbn_cx_goal. cbn [ht_ins ht_T ht_cnt]. fold cn. m_inv_auto.
Qed.
End d.
End c.

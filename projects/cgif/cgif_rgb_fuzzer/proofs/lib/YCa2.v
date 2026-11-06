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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c YCbe YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8j YC8k YC8l YC8m YC8n YC8o YC8t YC9t YC9u YC9v YC9w YC9x YC9y YC9z YC8r YC8z YC8w YC8p YC9s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC59 YC5a YC5b YP16 YI0f YI09 YC68.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC4b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC90 YC9d YC9r YCam YCaf YCag.
Ltac q_keptP Hfr HRNG HJ2 AG Usp RF E67 E10n E11n Rtb F HFpres Hrpres Htbpres consts :=
lazymatch goal with
| |- m_region_kept_ck _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
apply m_region_kept_ck_of_kept; [vm_compute; reflexivity|];
lazymatch n with
| 2%nat =>
lazymatch type of Usp with _ = ?sp =>
eapply (m_region_kept_av _ _ _ _ _ 2%nat sp);
[ ga_evalE0 AG; first [reflexivity | exact Usp]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha;
destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _); apply Hsp; clear - Ha HRNG; lia ] end
| 54%nat =>
eapply (m_region_kept_av _ _ _ _ _ 54%nat F);
[ ga_evalE0 AG; first [reflexivity | exact RF | rewrite RF; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (HFpres a Hx)); clear - Ha; lia ]
| 67%nat =>
eapply (m_region_kept_av _ _ _ _ _ 67%nat (SB + F / 8));
[ ga_evalE0 AG; first [reflexivity | exact E67 | rewrite E67; apply unsigned_lit_small; unfold SB; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; unfold SB in Ha |- *; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ]
| 10%nat =>
lazymatch type of E10n with _ = Z_to_bv 64 ?r =>
eapply (m_region_kept_av _ _ _ _ _ 10%nat r);
[ ga_evalE0 AG; first [reflexivity | exact E10n | rewrite E10n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Hrpres a Hx)); clear - Ha; lia ] end
| 11%nat =>
lazymatch type of E11n with _ = Z_to_bv 64 ?cfp =>
eapply (m_region_kept_av _ _ _ _ _ 11%nat cfp);
[ ga_evalE0 AG; first [reflexivity | exact E11n | rewrite E11n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ] end
| 305%nat =>
lazymatch type of Rtb with _ = Z_to_bv 64 ?tb =>
eapply (m_region_kept_av _ _ _ _ _ 305%nat tb);
[ ga_evalE0 AG; first [reflexivity | exact Rtb | rewrite Rtb; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Htbpres a Hx)); clear - Ha; lia ] end
end
| |- m_region_kept_ck _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => consts
end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis GETPAL : tgetpal_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_q2 : rga_fromA B ss_Q2 (fun _ => INV_CX B) -> rga_from B ss_Q1 (INV_CX B).
Proof.
intros RC. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & Tt & cnt & tr & Hk0 & Hnodes & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Rcnt & RT & Rha & Hha &
(av & Rav & Hav) & HTch & Hcnt & Rroot & Htree & Hfull & Hth & Hwft).
destruct Hk0 as [Hk0 Hbud].
unfold ss_Q1 in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x81368 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x80ea8])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
ga_ra_frame HS AG HFq F 532 532 96 HRApal.
assert (Htr_in3 : forall b, In b (tree_blocks tr) -> In b (ablocks B ly3 S3)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app; right. cbn [cht_blocks app]. do 9 right. exact Hb. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -512) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
change (Z_to_bv 64 545720) with (Z_to_bv 64 A_get_palette).
assert (HGPS : GP_STK (Z.of_nat (Z.to_nat TREE_HMAX)) + 512 <= 25088) by (vm_compute; discriminate).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (GETPAL (Z.to_nat TREE_HMAX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
tr (F + 4256) 7 fpos HJ3 Hth Hfull) end.
- rewrite Rra. apply ret_ok_even; vm_compute; reflexivity.
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear; lia). clear; lia.
- rewrite Ra0. unfold w64. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. exact Rroot.
- rewrite Ra1. unfold w64. f_equal. rewrite RF. rewrite unsigned_lit_small by exact HFrng. reflexivity.
- rewrite HspT. clear - Hal32. pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (spZ regs / 32) + -512) with ((2 * (spZ regs / 32) - 32) * 16) by lia. apply Z_mod_mult.
- rewrite HspT, FFS. clear - HGPS. lia.
- rewrite HspT. clear. lia.
- exact Hfrm.
- left; reflexivity.
- clear; lia.
- rewrite EFA3. fold F. clear; lia.
- rewrite EFA3. fold F. change (fs_frame_bytes 7) with 8192. clear; lia.
- replace (F + 4256) with (F + 8 * 532) by (clear; lia). exact HRApal.
- exact Htr_in3.
- exact Htree. }
cbv beta. intros W7 c7 _ (-> & fx7 & regs7 & mem7 & md7 & -> & Hfrm7 & HJ7 & HP7 & Hfr7 & Hpres7).
rewrite Rra.
let v := eval vm_compute in (GP_STK (Z.of_nat (Z.to_nat TREE_HMAX))) in change (GP_STK (Z.of_nat (Z.to_nat TREE_HMAX))) with v in Hfr7.
rewrite HspT in Hfr7.
clear Ra0 Ra1 Rsp.
pose proof (proj1 HJ7) as HAR7.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 Hrin3) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 Htb_in3) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ tb 48 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb. change (req_size 48) with 48 in HdF_tb.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ r 64 7 fpos HAR3 Hrin3 Hfin3) as HdF_r.
unfold zdisjoint in HdF_r. cbn [fst snd] in HdF_r. change (fs_frame_bytes 7) with 8192 in HdF_r. rewrite EFA3 in HdF_r. fold F in HdF_r. change (req_size 64) with 64 in HdF_r.
assert (HRNG7 : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= F \/ F + 8192 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= F \/ F + 8192 <= cfp)) /\
(4096 <= tb /\ tb + 48 <= alloc_ceiling /\ (tb + 48 <= F \/ F + 8192 <= tb)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25088 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25088 /\ SB = 2147450880).
{ unfold gbox, in_app in HFhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh. unfold gbox in HdFC.
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil HdF_r; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi HdFC; lia|]. split; [clear - Htb4096 Htbceil Hrqtb HdF_tb; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
m_reseatF HS HJ7 fx7 regs7 CLOB 539112 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG (m_same_of_preserved _ _ HP7)
ltac:(idtac; first
[ q_keptP Hfr7 HRNG7 HJ7 AG Usp RF E67 E10n E11n Rtb F HFpres7 Hrpres7 Htbpres7
ltac:(idtac; m_keptE_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tt ++ [(dn, 4 * cnt)] ++ tree_blocks tr).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Htr_l : forall b sz, In (b, sz) (tree_blocks tr) -> In (b, sz) lrest)
by (intros b sz Hb; subst lrest; apply in_or_app; right; cbn [cht_blocks app]; do 8 right; exact Hb).
assert (Htree7 : tree_at trasegs (mrestrict (w_H W3) mem7) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) (ms_mem ms3) _ tr Htree). intros b sz Hb i Hi.
destruct (Hoff3 b sz (Htr_l b sz Hb) (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). unfold m_ZsP in Hq2.
apply Hfr7; [exact Hq1 | clear - Hq2 HRNG7; lia | clear - Hq2; lia]. }
clear Hfr7 Hpres7.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan A_wrap_free.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree8 : tree_at trasegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) mem7 _ tr Htree7). intros b sz Hb i Hi.
destruct (Hoff3 b sz (Htr_l b sz Hb) (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN2; assumption. }
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with ss_Q2 in HS | idtac "STATE-MISMATCH"] end.
rga_hand RC HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, Tt, cnt, tr.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hnodes|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rdn | split; [exact Tdn | exact Adn]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
split; [exact HTch|]. split; [exact Hcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rroot|].
split; [exact Htree8|]. split; [exact Hfull|]. split; [exact Hth | exact Hwft].
Qed.
End d.
End c.

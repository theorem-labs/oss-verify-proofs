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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCnb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCfp.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCpg YCp3 YCp9 YCpa YCpb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjh YCjd YCjf.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_q5 : rga_fromA B ss_Q5D (fun _ => INV_Q4 B) -> rga_fromA B ss_Q5N (fun _ => INV_Q4 B) -> rga_from B ss_Q4 (INV_Q4 B).
Proof.
intros RCD RCN. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & Tt & cnt & flt & tr & Hk0 & Hnodes & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rflt & Tflt & Aflt) & Rcnt & RT & Rha & Hha &
(av & Rav & Hav) & HTch & Hcnt & Rroot & Htree & Hfull & Hth & Hwft).
destruct Hk0 as [Hk0 Hbud].
unfold ss_Q4 in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
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
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as (_ & _ & _ & _ & _ & _ & _ & [_ R42v] & [_ R44v] & _).
cbn [fst snd N.to_nat Z.of_N] in R42v, R44v.
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
assert (HN31 : 0 <= Hd * Wd < 2 ^ 31) by (rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia).
set (Mq := fmt * N).
assert (HMq : 3 <= Mq <= 40000) by (subst Mq; clear - HfN; unfold RGB_NMAX in HfN; lia).
assert (UfN : U E (SMdw M_MUL (SExt true 32 (SOff 46 0)) (SMdw M_MUL (SOff 40 0) (SOff 39 0))) = Mq).
{ subst Mq. rewrite HNhw. apply U_mulw_small; [apply (U_sext32_small E 46 fmt E46); clear - Hfmt; lia | apply (U_HW E 40 39 Hd Wd E40 E39); [clear - R44v; cbn in R44v; lia | clear - R42v; cbn in R42v; lia | exact HN31]
| clear - Hfmt; lia | clear - HN31; lia | rewrite <- HNhw; clear - HfN; unfold RGB_NMAX in HfN; lia]. }
assert (Himg_in : In (img, Mq) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. left.
unfold timg_block. subst Mq. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himg_in3 : In (img, Mq) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Himg_in]).
assert (Hflt_in3 : In (flt, 4 * Mq) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app; right. cbn [cht_blocks app]. do 8 right. apply in_or_app. right. left. reflexivity. }
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ img Mq HAR3 Himg_in3) as (Himg4096 & _ & Himgceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ flt (4 * Mq) HAR3 Hflt_in3) as (Hflt4096 & Hfltzone & Hfltceil & Hflt16).
pose proof (req_size_pos Mq ltac:(clear - HMq; lia)) as Hrqimg. pose proof (req_size_pos (4 * Mq) ltac:(clear - HMq; lia)) as Hrqflt.
assert (Uimg : U E (SOff 45 0) = img) by (apply (U_atom _ 45 img E45); clear - Himg4096 Himgceil Hrqimg C1; lia).
assert (Uflt : U E (SOff 875 0) = flt) by (apply (U_atom _ 875 flt Rflt); clear - Hflt4096 Hfltceil Hrqflt C1; lia).
rregU HS (10%bv : bv 5) img ltac:(exact Uimg) G10.
rregU HS (17%bv : bv 5) img ltac:(exact Uimg) G17.
rregU HS (29%bv : bv 5) img ltac:(exact Uimg) G29.
rregU HS (12%bv : bv 5) 0 ltac:(reflexivity) G12.
rregU HS (14%bv : bv 5) 0 ltac:(reflexivity) G14.
rregU HS (15%bv : bv 5) (4 * Mq) ltac:(replace (4 * Mq) with (Mq * 2 ^ 2) by (clear; lia); apply U_sll_small_q; [apply U_zext32_shifts; [exact UfN | clear - HMq; lia] | clear - HMq; lia | clear; lia | clear - HMq; lia]) G15.
rregU HS (13%bv : bv 5) (2 ^ 64 - 1 - flt) ltac:(apply (YCfp.U_not_gen E (SOff 875 0) flt Uflt); clear - Hflt4096 Hfltceil Hrqflt C1; lia) G13.
rregU HS (16%bv : bv 5) 1 ltac:(apply YCfp.U_sltu_lt; rewrite Uimg; change (U E (SLit 0)) with 0; clear - Himg4096; lia) G16.
rregU HS (23%bv : bv 5) flt ltac:(exact Uflt) G23.
rregU HS (27%bv : bv 5) SB ltac:(apply (U_atom _ 44 SB E44); unfold SB; clear; lia) G27.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
change (Z_to_bv 64 540204) with (Z_to_bv 64 LQT_HEAD).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (rga_lqt B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 img Mq img flt (4 * Mq) Mq fx (ms_regs msX) (ms_mem msX) mdX
HJ3 Hfrm Himg_in3 ltac:(clear; lia) ltac:(clear; lia) Hflt_in3 ltac:(clear; lia)) end.
- intros Heq. injection Heq as _ Hq. clear - Hq HMq. lia.
- clear - HMq. lia.
- exact Aflt.
- exact G10. - exact G17. - exact G12. - exact G15. - exact G13. - exact G14. - exact G16. - exact G29. - exact G23. - exact G27. }
cbv beta. intros W7 c7 _ (-> & fx7 & regs7 & mem7 & md7 & -> & Hfrm7 & HJ7 & HK7 & _ & _ & _ & Hfr7 & Hpres7).
clear G10 G17 G29 G12 G14 G15 G13 G16 G23 G27.
pose proof (proj1 HJ7) as HAR7.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 Hrin3) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 Htb_in3) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
set (rq := req_size (4 * Mq)) in *.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ flt (4 * Mq) 7 fpos HAR3 Hflt_in3 Hfin3) as HdF_flt.
unfold zdisjoint in HdF_flt. cbn [fst snd] in HdF_flt. change (fs_frame_bytes 7) with 8192 in HdF_flt. rewrite EFA3 in HdF_flt. fold F rq in HdF_flt.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ flt (4 * Mq) cid pos HAR3 Hflt_in3 HfinS3) as HdC_flt.
unfold zdisjoint in HdC_flt. cbn [fst snd] in HdC_flt. rewrite EFA3 in HdC_flt. fold rq in HdC_flt.
assert (HPflt : Permutation (ablocks B ly3 S3) ((flt, 4 * Mq) :: (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ tree_blocks tr)))
by (eapply Permutation_trans; [exact HPm3|]; unfold Mq; YI0g.perm_tac).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (r, 64) HAR3 HPflt ltac:(apply in_or_app; left; exact Hrin)) as HdR_flt.
unfold zdisjoint, block_rng in HdR_flt. cbn [fst snd] in HdR_flt. change (req_size 64) with 64 in HdR_flt. fold rq in HdR_flt.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (tb, 48) HAR3 HPflt ltac:(apply in_or_app; right; right; right; left; reflexivity)) as HdT_flt.
unfold zdisjoint, block_rng in HdT_flt. cbn [fst snd] in HdT_flt. change (req_size 48) with 48 in HdT_flt. fold rq in HdT_flt.
assert (HRNG7 : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (flt + rq <= F \/ F + 8192 <= flt)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (flt + rq <= r \/ r + 64 <= flt)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (flt + rq <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= flt) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid) /\
(4096 <= tb /\ tb + 48 <= alloc_ceiling /\ (flt + rq <= tb \/ tb + 48 <= flt)) /\
(4096 <= flt /\ flt + rq <= alloc_ceiling /\ 4 * Mq <= rq /\ (flt + rq <= 2147446784 \/ 17594333495296 <= flt)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880).
{ split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HdF_flt; lia|]. split; [clear - Hr4096 Hrceil HdR_flt; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi HdC_flt; lia|]. split; [clear - Htb4096 Htbceil Hrqtb HdT_flt; lia|].
split; [destruct Hfltzone as [_ Hz2]; fold rq in Hz2, Hfltceil, Hrqflt; clear - Hflt4096 Hfltceil Hrqflt Hz2; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
m_reseatF HS HJ7 fx7 regs7 ([5; 6; 7; 10; 11; 12; 17]%bv : list (bv 5)) 540332 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG HK7
ltac:(idtac; first
[ q_keptP Hfr7 HRNG7 HJ7 AG Usp RF E67 E10n E11n Rtb F HFpres7 Hrpres7 Htbpres7
ltac:(idtac; m_keptE_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
assert (Htree7 : tree_at trbsegs (mrestrict (w_H W3) mem7) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) (ms_mem ms3) _ tr Htree). intros b sz Hb i Hi.
assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPflt | right; apply in_or_app; right; cbn [cht_blocks app]; do 8 right; exact Hb]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b sz HAR3 Hb3) as (Hb4096 & _ & Hbceil & _).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (b, sz) HAR3 HPflt ltac:(apply in_or_app; right; cbn [cht_blocks app]; do 8 right; exact Hb)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. fold rq in Dd.
apply Hfr7; [clear - Hi Hb4096 Hbceil C1; lia | destruct HRNG7 as (_ & _ & _ & _ & (_ & _ & Hq & _) & _); clear - Dd Hi Hq; lia]. }
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tt ++ tree_blocks tr ++ [(flt, 4 * (fmt * N))])))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; YI0g.perm_tac).
assert (HoffT : forall b sz, In (b, sz) (tree_blocks tr) -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha.
pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 ltac:(apply in_or_app; right; cbn [cht_blocks app]; do 7 right; apply in_or_app; left; exact Hb) Hfin3 a Ha) as Hq.
rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x83eb8.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
-
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x844dc.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree9 : tree_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) mem7 _ tr Htree7). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). rewrite (UN3 _ Hq1 Hq2). apply UN2; assumption. }
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with ss_Q5N in HS | idtac "STATE-MISMATCH"] end.
rga_hand RCN HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, Tt, cnt, flt, tr.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hnodes|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rflt | split; [exact Tflt | exact Aflt]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
split; [exact HTch|]. split; [exact Hcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rroot|].
split; [exact Htree9|]. split; [exact Hfull|]. split; [exact Hth | exact Hwft].
-
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x83ec0.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree9 : tree_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) mem7 _ tr Htree7). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). rewrite (UN3 _ Hq1 Hq2). apply UN2; assumption. }
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with ss_Q5D in HS | idtac "STATE-MISMATCH"] end.
rga_hand RCD HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, Tt, cnt, flt, tr.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hnodes|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rflt | split; [exact Tflt | exact Aflt]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
split; [exact HTch|]. split; [exact Hcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rroot|].
split; [exact Htree9|]. split; [exact Hfull|]. split; [exact Hth | exact Hwft].
Qed.
End d.
End c.

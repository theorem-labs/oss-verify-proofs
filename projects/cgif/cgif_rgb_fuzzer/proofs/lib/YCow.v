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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YCq5 YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCpg YCp3 YCo0 YCp9 YCpa.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjh YCj9 YCja YCjd YCjg YCjf YCp5 YCpc YCp1 YCp4.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YCia YCjc.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCfp.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis GLNI : forall fy : YK11.FPState, @tglni_spec fy rc B.
Hypothesis ROLC : trb_rol_const B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_q6 : rga_fromA B ss_QE (fun _ => INV_QE B) -> rga_from B ss_Q5D (INV_Q4 B).
Proof.
intros RC. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & Tt & cnt & flt & tr & Hk0 & Hnodes & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rflt & Tflt & Aflt) & Rcnt & RT & Rha & Hha &
(av & Rav & Hav) & HTch & Hcnt & Rroot & Htree & Hfull & Hth & Hwft).
destruct Hk0 as [Hk0 Hbud].
unfold ss_Q5D in HS.
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
assert (HWd1 : 1 <= Wd /\ 1 <= Hd) by (rewrite <- HcW, <- HcH; clear - HW1 HH1; lia).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83ee4.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
set (Mq := fmt * N).
assert (HMq : 3 <= Mq <= 40000) by (subst Mq; clear - HfN; unfold RGB_NMAX in HfN; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tt ++ tree_blocks tr ++ [(flt, 4 * (fmt * N))])))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; YI0g.perm_tac).
assert (HoffT : forall b sz, In (b, sz) (tree_blocks tr) -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha.
pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 ltac:(apply in_or_app; right; cbn [cht_blocks app]; do 7 right; apply in_or_app; left; exact Hb) Hfin3 a Ha) as Hq.
rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree0 : tree_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) (ms_mem ms3) _ tr Htree). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN0; assumption. }
assert (Hflt_in3 : In (flt, 4 * Mq) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app; right. cbn [cht_blocks app]. do 8 right. apply in_or_app. right. left. reflexivity. }
assert (Hfim_in3 : In (fim, N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; right; left; reflexivity]).
assert (Htr_in3 : forall b, In b (tree_blocks tr) -> In b (ablocks B ly3 S3)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app; right. cbn [cht_blocks app]. do 8 right. apply in_or_app. left. exact Hb. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Hsprng : alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 FFS; lia).
assert (E2n : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (AG 2%nat) by lia; rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ flt (4 * Mq) HAR3 Hflt_in3) as (Hflt4096 & Hfltzone & Hfltceil & Hflt16).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fim N HAR3 Hfim_in3) as (Hfim4096 & Hfimzone & Hfimceil & Hfim16).
pose proof (req_size_pos (4 * Mq) ltac:(clear - HMq; lia)) as Hrqflt. pose proof (req_size_pos N ltac:(clear - HN1; lia)) as Hrqfim.
assert (Hroot_rng : 4096 <= troot tr /\ troot tr + 56 <= alloc_ceiling).
{ destruct tr as [|nd|nd tl tr']; [exfalso; exact Hfull | |];
(assert (Hb : In (tn_addr nd, NODE_SIZE) (ablocks B ly3 S3)) by (apply Htr_in3; cbn [tree_blocks]; left; reflexivity);
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ _ _ HAR3 Hb) as (Hb4096 & _ & Hbceil & _); change (req_size NODE_SIZE) with 56 in Hbceil; cbn [troot]; clear - Hb4096 Hbceil; lia). }
assert (HRNGq : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling) /\ (4096 <= cfp /\ cfp + 24 <= alloc_ceiling) /\ (4096 <= tb /\ tb + 48 <= alloc_ceiling) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880).
{ unfold gbox, in_app in HFhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh.
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi; lia|]. split; [clear - Htb4096 Htbceil Hrqtb; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 540388) with (Z_to_bv 64 QF_DI0).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (q_fmv_di0 B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 fx (ms_regs msX) (ms_mem msX) mdX HJ3 Hfrm) end. }
cbv beta. intros W5 c5 _ (-> & fx5 & regs5 & mem5 & md5 & -> & HJ5 & Hfrm5 & HF8a & HFKa & HK5 & HM5 & HP5).
assert (Hsame5 : forall r0 : bv 5, reg_in r0 ([] : list (bv 5)) = false -> getr regs5 r0 = getr (ms_regs ms) r0).
{ intros r0 _. pose proof (all_regs_in r0) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [ rewrite !getr_zero; reflexivity | apply HK5; cbv; tauto ] |]). destruct Hin. }
pose proof (proj1 HJ5) as HAR5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR5 Hfin3) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 7) with 8192 in HFpres5, HFSpres5.
change (8192 / 8) with 1024 in HFSpres5. rewrite EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR5 Hrin3) as (_ & _ & _ & _ & Hrpres5 & _). change (req_size 64) with 64 in Hrpres5.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR5 Htb_in3) as (_ & _ & _ & _ & Htbpres5 & _). change (req_size 48) with 48 in Htbpres5.
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
m_reseatF HS HJ5 fx5 regs5 ([] : list (bv 5)) 540392 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG Hsame5
ltac:(idtac; first
[ q_keptP HM5 HRNGq HJ5 AG Usp RF E67 E10n E11n Rtb F HFpres5 Hrpres5 Htbpres5
ltac:(idtac; m_keptE_consts Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
norm_ss HS.
assert (Htree5 : tree_at trbsegs (mrestrict (w_H W3) mem5) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) (ms_mem ms) _ tr Htree0). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & _). apply HM5. exact Hq1. }
clear HM5 HP5 Hsame5 HK5 HFpres5 HFSpres5 Hrpres5 Htbpres5 HAR5 UN0 Htree0.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK GBspan 0x83f0c.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN5.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree5u : tree_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) mem5 _ tr Htree5). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN5; assumption. }
rregU HS (13%bv : bv 5) S255 ltac:(reflexivity) G13.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 540428) with (Z_to_bv 64 QF_DI1).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ5 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (q_fmv_di1 B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 fx5 (ms_regs msX) (ms_mem msX) mdX HJ5 Hfrm5 G13) end. }
cbv beta. intros W6 c6 _ (-> & fx6 & regs6 & mem6 & md6 & -> & HJ6 & Hfrm6 & HF9b & HFKb & HK6 & HM6 & HP6).
lazymatch type of HK6 with forall r0, _ -> _ = getr ?rgX r0 =>
assert (Hsame6 : forall r0 : bv 5, reg_in r0 ([] : list (bv 5)) = false -> getr regs6 r0 = getr rgX r0) end.
{ intros r0 _. pose proof (all_regs_in r0) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [ rewrite !getr_zero; reflexivity | apply HK6; cbv; tauto ] |]). destruct Hin. }
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR6 Hfin3) as (_ & _ & HFpres6 & HFSpres6). change (fs_frame_bytes 7) with 8192 in HFpres6, HFSpres6.
change (8192 / 8) with 1024 in HFSpres6. rewrite EFA3 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR6 Hrin3) as (_ & _ & _ & _ & Hrpres6 & _). change (req_size 64) with 64 in Hrpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR6 Htb_in3) as (_ & _ & _ & _ & Htbpres6 & _). change (req_size 48) with 48 in Htbpres6.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
m_reseatF HS HJ6 fx6 regs6 ([] : list (bv 5)) 540432 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG Hsame6
ltac:(idtac; first
[ q_keptP HM6 HRNGq HJ6 AG Usp RF E67 E10n E11n Rtb F HFpres6 Hrpres6 Htbpres6
ltac:(idtac; m_keptE_consts Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
ga_relow HS AG E10 E11 E10n E11n.
norm_ss HS.
assert (Htree6 : tree_at trbsegs (mrestrict (w_H W3) mem6) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) _ _ tr Htree5u). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & _). apply HM6. exact Hq1. }
clear HM6 HP6 Hsame6 HK6 HFpres6 HFSpres6 Hrpres6 Htbpres6 HAR6 UN5 Htree5 Htree5u G13.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ6 SHOK GBspan 0x83f14.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN6.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree6u : tree_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) mem6 _ tr Htree6). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN6; assumption. }
rregU HS (14%bv : bv 5) Shi ltac:(reflexivity) G14.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 540436) with (Z_to_bv 64 QF_DI2).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ6 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (q_fmv_di2 B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 fx6 (ms_regs msX) (ms_mem msX) mdX HJ6 Hfrm6 G14) end. }
cbv beta. intros W8 c8 _ (-> & fx8 & regs8 & mem8 & md8 & -> & HJ8 & Hfrm8 & HF18c & HFKc & HK8 & HM8 & HP8).
lazymatch type of HK8 with forall r0, _ -> _ = getr ?rgX r0 =>
assert (Hsame8 : forall r0 : bv 5, reg_in r0 ([] : list (bv 5)) = false -> getr regs8 r0 = getr rgX r0) end.
{ intros r0 _. pose proof (all_regs_in r0) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [ rewrite !getr_zero; reflexivity | apply HK8; cbv; tauto ] |]). destruct Hin. }
pose proof (proj1 HJ8) as HAR8.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR8 Hfin3) as (_ & _ & HFpres8 & HFSpres8). change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8.
change (8192 / 8) with 1024 in HFSpres8. rewrite EFA3 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR8 Hrin3) as (_ & _ & _ & _ & Hrpres8 & _). change (req_size 64) with 64 in Hrpres8.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR8 Htb_in3) as (_ & _ & _ & _ & Htbpres8 & _). change (req_size 48) with 48 in Htbpres8.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
m_reseatF HS HJ8 fx8 regs8 ([] : list (bv 5)) 540440 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG Hsame8
ltac:(idtac; first
[ q_keptP HM8 HRNGq HJ8 AG Usp RF E67 E10n E11n Rtb F HFpres8 Hrpres8 Htbpres8
ltac:(idtac; m_keptE_consts Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot8 into Kgot0. rename Kcell8 into Kcell0. rename Kguar8 into Kguar0. rename Kuar8 into Kuar0. rename Vgr8 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
ga_relow HS AG E10 E11 E10n E11n.
norm_ss HS.
assert (Htree8 : tree_at trbsegs (mrestrict (w_H W3) mem8) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) _ _ tr Htree6u). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & _). apply HM8. exact Hq1. }
clear HM8 HP8 Hsame8 HK8 HFpres8 HFSpres8 Hrpres8 Htbpres8 HAR8 UN6 Htree6 Htree6u G14.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ8 SHOK GBspan 0x83f24.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN8.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree8u : tree_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) mem8 _ tr Htree8). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN8; assumption. }
assert (HWdN : Wd <= N) by (rewrite HNhw; clear - HWd1; nia).
assert (HWd16 : 1 <= Wd < 2 ^ 16) by (clear - HWd1 R42v; cbn in R42v; lia).
assert (HfW : 0 <= fmt * (Wd - 1) /\ fmt * (Wd + 1) < 2 ^ 29) by (clear - Hfmt HWd16; nia).
lazymatch type of HS with st_ok _ ?Ev _ _ => set (EV := Ev) in * end.
assert (E46v : ew EV 46 = Z_to_bv 64 fmt) by (unfold EV; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E46).
assert (E39v : ew EV 39 = Z_to_bv 64 Wd) by (unfold EV; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E39).
assert (E40v : ew EV 40 = Z_to_bv 64 Hd) by (unfold EV; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E40).
assert (QMUL : forall a b x y, U EV a = x -> U EV b = y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= x * y < 2 ^ 64 -> U EV (SMd M_MUL a b) = x * y).
{ intros a b x y Ha Hb Hx Hy Hxy. rewrite U_SMd, Ha, Hb. cbn [zmd_raw]. apply zcanon_id. unfold M64. lia. }
assert (QSUBW : forall a b x y, U EV a = x -> U EV b = y -> 0 <= y -> y <= x -> x < 2 ^ 31 -> U EV (SAluw ALU_SUB a b) = x - y).
{ intros a b x y Ha Hb Hy Hyx Hx. rewrite YI0g.U_SAluw, Ha, Hb. cbn [zalu_raw].
rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small y) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x - y + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia. }
assert (Ufmt : U EV (SExt true 32 (SOff 46 0)) = fmt) by (apply (U_sext32_small EV 46 fmt E46v); clear - Hfmt; lia).
assert (UN : U EV (SMdw M_MUL (SOff 40 0) (SOff 39 0)) = N)
by (rewrite HNhw; apply (U_HW EV 40 39 Hd Wd E40v E39v); [clear - R44v; cbn in R44v; lia | clear - R42v; cbn in R42v; lia | exact HN31]).
assert (Uflt : U EV (SOff 875 0) = flt) by (apply (U_atom _ 875 flt Rflt); clear - Hflt4096 Hfltceil Hrqflt C1; lia).
rregU HS (25%bv : bv 5) 0 ltac:(reflexivity) G25.
rregU HS (31%bv : bv 5) (fmt * 0) ltac:(rewrite Z.mul_0_r; reflexivity) G31.
rregU HS (18%bv : bv 5) fmt ltac:(exact Ufmt) G18.
rregU HS (1%bv : bv 5) (fmt * (Wd - 1)) ltac:(replace (Wd - 1) with (Wd + -1) by (clear; lia);
apply QMUL; [exact Ufmt | apply (U_atom_off EV 39 Wd (-1) E39v); clear - HWd16; lia | clear - Hfmt; lia | clear - HWd16; lia | replace (Wd + -1) with (Wd - 1) by (clear; lia); clear - HfW Hfmt HWd16; nia]) G1.
rregU HS (26%bv : bv 5) (fmt * Wd) ltac:(apply QMUL; [exact Ufmt | apply (U_atom EV 39 Wd E39v); clear - HWd16; lia | clear - Hfmt; lia | clear - HWd16; lia | clear - HfW Hfmt HWd16; nia]) G26.
rregU HS (24%bv : bv 5) (Wd - 1) ltac:(rewrite (U_atom_off EV 39 Wd (-1) E39v) by (clear - HWd16; lia); clear; lia) G24.
rregU HS (22%bv : bv 5) (2 ^ 64 - 1 - flt) ltac:(apply (YCfp.U_not_gen EV (SOff 875 0) flt Uflt); clear - Hflt4096 Hfltceil Hrqflt C1; lia) G22.
rregU HS (23%bv : bv 5) flt ltac:(exact Uflt) G23.
rregU HS (27%bv : bv 5) SB ltac:(apply (U_atom _ 44 SB E44); unfold SB; clear; lia) G27.
assert (E2v : ew EV 2 = Z_to_bv 64 (spZ regs)) by (rewrite (AG 2%nat) by lia; rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
rregU HS (9%bv : bv 5) (spZ regs - 576) ltac:(rewrite (U_atom_off EV 2 (spZ regs) (-576) E2v) by (clear - Hsprng C1; lia); clear; lia) G9.
rregU HS (2%bv : bv 5) (spZ regs - 576) ltac:(rewrite (U_atom_off EV 2 (spZ regs) (-576) E2v) by (clear - Hsprng C1; lia); clear; lia) G2.
rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
assert (U2v : bv_unsigned (ew EV 2) = spZ regs) by (rewrite E2v; apply unsigned_lit_small; clear - Hsprng C1; lia).
assert (Rrootv : ew EV 767 = Z_to_bv 64 (troot tr)) by (unfold EV; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rroot).
assert (Rfimv : ew EV 184 = Z_to_bv 64 fim) by (unfold EV; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim).
assert (RFv : ew EV 54 = Z_to_bv 64 F) by (unfold EV; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
pose proof (fun off e v => q_slot_of_state EV _ msX (w_H W3) 7%nat _ _ _ _ _ (spZ regs) off e v HS eq_refl) as SL0 end.
lazymatch type of SL0 with forall off e v, In _ ?cs -> _ -> _ -> _ -> ?concl =>
assert (SL : forall off e v, In (YQ0b.mkChunk (off - 576) (CVal 8 e)) cs -> sv_denot EV e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> concl)
by (intros off e v Hin He Hv; exact (SL0 off e v Hin U2v He Hv)) end.
clear SL0.
assert (Hfim_rng : 0 <= fim < 2 ^ 64) by (clear - Hfim4096 Hfimceil Hrqfim C1; lia).
assert (HNW : 0 <= N - Wd < 2 ^ 31) by (clear - HWdN HWd16 HN31 HNhw; lia).
pose proof (SL 192 (SExt true 32 (SOff 46 0)) fmt ltac:(cbn; repeat first [left; reflexivity | right]) (q_denot_sext32 EV 46 fmt E46v ltac:(clear - Hfmt; lia)) ltac:(clear - Hfmt; lia)) as V192.
pose proof (SL 232 (SOff 39 0) Wd ltac:(cbn; repeat first [left; reflexivity | right]) (q_denot_off0 EV 39 Wd E39v ltac:(clear - HWd16; lia)) ltac:(clear - HWd16; lia)) as V232.
pose proof (SL 240 (SOff 767 0) (troot tr) ltac:(cbn; repeat first [left; reflexivity | right]) (q_denot_off0 EV 767 (troot tr) Rrootv ltac:(clear - Hroot_rng C1; lia)) ltac:(clear - Hroot_rng C1; lia)) as V240.
pose proof (SL 312 (SOff 184 0) fim ltac:(cbn; repeat first [left; reflexivity | right]) (q_denot_off0 EV 184 fim Rfimv Hfim_rng) Hfim_rng) as V312.
pose proof (SL 376 (SMd M_MUL (SExt true 32 (SOff 46 0)) (SOff 39 1)) (fmt * (Wd + 1)) ltac:(cbn; repeat first [left; reflexivity | right])
(q_denot_U EV _ _ (QMUL _ _ fmt (Wd + 1) Ufmt (U_atom_off EV 39 Wd 1 E39v ltac:(clear - HWd16; lia) ltac:(clear - HWd16; lia)) ltac:(clear - Hfmt; lia) ltac:(clear - HWd16; lia) ltac:(clear - HfW Hfmt HWd16; nia)))
ltac:(clear - HfW Hfmt HWd16; nia)) as V376.
pose proof (SL 384 (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_MUL (SOff 40 0) (SOff 39 0)) (SLit 32)) (SLit 32)) N ltac:(cbn; repeat first [left; reflexivity | right])
(q_denot_U EV _ _ (U_zext32_shifts EV _ N UN ltac:(clear - HN1 HN31 HNhw; lia))) ltac:(clear - HN1 HN31 HNhw; lia)) as V384.
pose proof (SL 392 (SOff 54 4256) (F + 4256) ltac:(cbn; repeat first [left; reflexivity | right]) (q_denot_off EV 54 F 4256 RFv HFrng) ltac:(clear - HF4096 HFceil C1; lia)) as V392.
pose proof (SL 400 (SLit 1) 1 ltac:(cbn; repeat first [left; reflexivity | right]) eq_refl ltac:(clear; lia)) as V400.
pose proof (SL 408 (SAlu ALU_SRL (SAlu ALU_SLL (SAluw ALU_SUB (SMdw M_MUL (SOff 40 0) (SOff 39 0)) (SOff 39 0)) (SLit 32)) (SLit 32)) (N - Wd) ltac:(cbn; repeat first [left; reflexivity | right])
(q_denot_U EV _ _ (U_zext32_shifts EV _ (N - Wd) (QSUBW _ _ N Wd UN (U_atom EV 39 Wd E39v ltac:(clear - HWd16; lia)) ltac:(clear - HWd16; lia) HWdN ltac:(clear - HN31 HNhw; lia)) ltac:(clear - HNW; lia)))
ltac:(clear - HNW; lia)) as V408.
clear SL.
assert (HF8v : reg_get (@fp_regs fx8) (8%bv : bv 5) = nan_box (Z_to_bv 32 0))
by (rewrite (HFKc (8%bv : bv 5) ltac:(cbv; tauto)), (HFKb (8%bv : bv 5) ltac:(cbv; tauto)); exact HF8a).
assert (HF9v : reg_get (@fp_regs fx8) (9%bv : bv 5) = nan_box (Z_to_bv 32 S255)) by (rewrite (HFKc (9%bv : bv 5) ltac:(cbv; tauto)); exact HF9b).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (VROL : val_mem trbsegs (mrestrict (w_H W3) (ms_mem msX)) LDK_ROL 4 Slo) end.
{ exact (q_rol_val B _ _ ROLC (arodata_ok_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ8 HROD)). }
assert (HfN29 : 3 <= fmt < 2 ^ 29 /\ 0 < N <= 2 ^ 29 /\ fmt * N <= 2 ^ 29) by (clear - Hfmt HN1 HN HMq; subst Mq; unfold RGB_NMAX in HN; lia).
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 540452) with (Z_to_bv 64 LDH_HEAD).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ8 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (rga_ldi_loop B LAWS GLNI TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 flt (4 * Mq) (spZ regs - 576) fmt N Wd (F + 4256) fim fim N
(Wd - 1) (N - Wd) (fmt * Wd) (fmt * (Wd - 1)) (fmt * (Wd + 1)) 7 fpos tr 0 fx8 (ms_regs msX) (ms_mem msX) mdX HJ8 Hfrm8 Hflt_in3 Aflt) end.
- rewrite FFS. clear. lia.
- clear. lia.
- clear - Hal32. pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (spZ regs / 32) - 576) with ((2 * (spZ regs / 32) - 36) * 16) by lia. apply Z_mod_mult.
- exact Hfmt.
- exact (proj1 (proj2 HfN29)). - exact (proj2 (proj2 HfN29)).
- clear - HWd16. lia.
- exact Hfin3.
- rewrite EFA3. fold F. clear. lia.
- rewrite EFA3. fold F. change (fs_frame_bytes 7) with 8192. clear. lia.
- clear - Hfmt HWd16. nia.
- clear - Hfmt HWd16. nia.
- clear - Hfmt HWd16. nia.
- clear - HWd16. lia.
- clear - HNW. lia.
- exact Hfim_in3.
- clear. lia. - clear. lia.
- intros Heq. injection Heq as Hq1 Hq2. clear - Hq2 HMq HN1 Hfmt. subst Mq. nia.
- exact Afim.
- exact Hfull. - exact Hwft. - exact Htr_in3.
- intros b Hb Heq. subst b. apply tree_blocks_in_nodes in Hb. destruct Hb as (nd & _ & Hq). injection Hq as _ Hq. unfold NODE_SIZE in Hq. subst Mq. clear - Hq Hfmt. destruct Hfmt as [-> | ->]; lia.
- intros b Hb Heq. subst b.
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt)) (tree_blocks tr ++ [(flt, 4 * (fmt * N))]) (fim, N) (fim, N) HAR3
ltac:(eapply Permutation_trans; [exact HPm3|]; YI0g.perm_tac)
ltac:(apply in_or_app; right; right; left; reflexivity) ltac:(apply in_or_app; left; exact Hb)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. clear - Dd Hrqfim. lia.
- clear. lia.
- intros i j Hi Hj Hg. exact (q_inb1 fmt N Wd Hd i j ltac:(rewrite HNhw; reflexivity) ltac:(clear - HWd1; lia) ltac:(clear - Hfmt; lia) Hi Hj Hg).
- intros i j Hi Hj Hg. split; [clear - Hfmt HWd16; nia|]. exact (q_inb2 fmt N Wd i j ltac:(clear - HWd1; lia) ltac:(clear - Hfmt; lia) Hi Hj Hg).
- intros i j Hi Hj Hg Hne. split; [|exact (q_inb3 fmt N Wd i j ltac:(clear - HWd1; lia) ltac:(clear - Hfmt; lia) Hi Hj Hg)].
assert (2 <= Wd) by (destruct (Z.eq_dec Wd 1) as [-> |]; [exfalso; apply Hne; apply Z.mod_1_r | clear - HWd16 n; lia]). clear - H Hfmt. nia.
- intros i j Hi Hj Hg Hg2. split; [clear - Hfmt HWd16; nia|]. exact (q_inb4 fmt N Wd Hd i j ltac:(rewrite HNhw; reflexivity) ltac:(clear - HWd1; lia) ltac:(clear - Hfmt; lia) Hi Hj Hg Hg2).
- exact Htree8u.
- exact V192. - exact V232. - exact V240. - exact V312. - exact V376. - exact V384. - exact V392. - exact V400. - exact V408. - exact VROL.
- exact HF8v. - exact HF9v. - exact HF18c.
- clear - HN1. lia.
- exact G25. - exact G31. - exact G18. - exact G1. - exact G2.
- rewrite Rgp. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact G9. - exact G22. - exact G23. - exact G24. - exact G26. - exact G27. }
cbv beta. intros W7 c7 _ (-> & fx7 & regs7 & mem7 & md7 & -> & Hfrm7 & HJ7 & HK7 & HFK7 & G25e & G31e & G18e & Htree7 & Hfr7 & Hpres7).
unfold LDL_CLOB in HK7.
pose proof (proj1 HJ7) as HAR7.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 Hrin3) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 Htb_in3) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
set (rq := req_size (4 * Mq)) in *. set (rqi := req_size N) in *.
assert (SEPF : forall b sz, In (b, sz) (ablocks B ly3 S3) -> (b, sz) <> (flt, 4 * Mq) -> b + req_size sz <= flt \/ flt + rq <= b).
{ intros b sz Hb Hne. pose proof (sep_blocks trbsegs B LAWS ly3 S3 _ _ _ b sz flt (4 * Mq) HAR3 Hb Hflt_in3 Hne) as Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. exact Dd. }
assert (SEPI : forall b sz, In (b, sz) (ablocks B ly3 S3) -> (b, sz) <> (fim, N) -> b + req_size sz <= fim \/ fim + rqi <= b).
{ intros b sz Hb Hne. pose proof (sep_blocks trbsegs B LAWS ly3 S3 _ _ _ b sz fim N HAR3 Hb Hfim_in3 Hne) as Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. exact Dd. }
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ flt (4 * Mq) 7 fpos HAR3 Hflt_in3 Hfin3) as HdF_flt.
unfold zdisjoint in HdF_flt. cbn [fst snd] in HdF_flt. change (fs_frame_bytes 7) with 8192 in HdF_flt. rewrite EFA3 in HdF_flt. fold F rq in HdF_flt.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ flt (4 * Mq) cid pos HAR3 Hflt_in3 HfinS3) as HdC_flt.
unfold zdisjoint in HdC_flt. cbn [fst snd] in HdC_flt. rewrite EFA3 in HdC_flt. fold rq in HdC_flt.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim N 7 fpos HAR3 Hfim_in3 Hfin3) as HdF_fim.
unfold zdisjoint in HdF_fim. cbn [fst snd] in HdF_fim. change (fs_frame_bytes 7) with 8192 in HdF_fim. rewrite EFA3 in HdF_fim. fold F rqi in HdF_fim.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim N cid pos HAR3 Hfim_in3 HfinS3) as HdC_fim.
unfold zdisjoint in HdC_fim. cbn [fst snd] in HdC_fim. rewrite EFA3 in HdC_fim. fold rqi in HdC_fim.
assert (HPflt : Permutation (ablocks B ly3 S3) ((flt, 4 * Mq) :: (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ tree_blocks tr)))
by (eapply Permutation_trans; [exact HPm3|]; unfold Mq; YI0g.perm_tac).
assert (HPfim : Permutation (ablocks B ly3 S3) ((fim, N) :: (ablocks B ly S ++ [(blk, fmt * N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ tree_blocks tr ++ [(flt, 4 * (fmt * N))])))
by (eapply Permutation_trans; [exact HPm3|]; YI0g.perm_tac).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (r, 64) HAR3 HPflt ltac:(apply in_or_app; left; exact Hrin)) as HdR_flt.
unfold zdisjoint, block_rng in HdR_flt. cbn [fst snd] in HdR_flt. change (req_size 64) with 64 in HdR_flt. fold rq in HdR_flt.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (tb, 48) HAR3 HPflt ltac:(apply in_or_app; right; right; right; left; reflexivity)) as HdT_flt.
unfold zdisjoint, block_rng in HdT_flt. cbn [fst snd] in HdT_flt. change (req_size 48) with 48 in HdT_flt. fold rq in HdT_flt.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (fim, N) _ (r, 64) HAR3 HPfim ltac:(apply in_or_app; left; exact Hrin)) as HdR_fim.
unfold zdisjoint, block_rng in HdR_fim. cbn [fst snd] in HdR_fim. change (req_size 64) with 64 in HdR_fim. fold rqi in HdR_fim.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (fim, N) _ (tb, 48) HAR3 HPfim ltac:(apply in_or_app; right; right; left; reflexivity)) as HdT_fim.
unfold zdisjoint, block_rng in HdT_fim. cbn [fst snd] in HdT_fim. change (req_size 48) with 48 in HdT_fim. fold rqi in HdT_fim.
assert (HRNG7 : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (flt + rq <= F \/ F + 8192 <= flt) /\ (fim + rqi <= F \/ F + 8192 <= fim)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (flt + rq <= r \/ r + 64 <= flt) /\ (fim + rqi <= r \/ r + 64 <= fim)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (flt + rq <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= flt) /\
(fim + rqi <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= fim) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid) /\
(4096 <= tb /\ tb + 48 <= alloc_ceiling /\ (flt + rq <= tb \/ tb + 48 <= flt) /\ (fim + rqi <= tb \/ tb + 48 <= fim)) /\
(4096 <= flt /\ flt + rq <= alloc_ceiling /\ 4 * Mq <= rq /\ (flt + rq <= 2147446784 \/ 17594333495296 <= flt)) /\
(4096 <= fim /\ fim + rqi <= alloc_ceiling /\ N <= rqi /\ (fim + rqi <= 2147446784 \/ 17594333495296 <= fim)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880).
{ split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HdF_flt HdF_fim; lia|]. split; [clear - Hr4096 Hrceil HdR_flt HdR_fim; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi HdC_flt HdC_fim; lia|]. split; [clear - Htb4096 Htbceil Hrqtb HdT_flt HdT_fim; lia|].
split; [destruct Hfltzone as [_ Hz2]; clear - Hflt4096 Hfltceil Hrqflt Hz2; lia|].
split; [destruct Hfimzone as [_ Hz2]; clear - Hfim4096 Hfimceil Hrqfim Hz2; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
m_reseatF HS HJ7 fx7 regs7 ([5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 25; 28; 29; 30; 31]%bv : list (bv 5)) 542728 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG HK7
ltac:(idtac; first
[ q_keptP Hfr7 HRNG7 HJ7 AG Usp RF E67 E10n E11n Rtb F HFpres7 Hrpres7 Htbpres7
ltac:(idtac; m_keptE_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
assert (Hflt_rng : 0 <= flt < 2 ^ 64) by (destruct HRNG7 as (_ & _ & _ & _ & (Hq1 & Hq2 & Hq3 & _) & _); clear - Hq1 Hq2 Hq3 C1 Hrqflt; lia).
rregU HS (23%bv : bv 5) flt ltac:(apply (U_atom _ 875 flt Rflt); exact Hflt_rng) G23x.
slot_val HS (Some 2%nat) (-576) (-336) (Z_to_bv 64 (troot tr)) ltac:(exact (q_denot_off0 _ 767 (troot tr) Rroot ltac:(clear - Hroot_rng C1; lia))) QSroot.
ra_join_slots HS ss_QE2 2000%nat rga_deads_QE2 [(Some 2%nat, (-576), (-408)); (Some 2%nat, (-576), (-336))]
ltac:(idtac; ga_join_val HS 2000%nat 19%nat G23x E2019; ga_join_val HS 2000%nat 24%nat QSroot E2024;
ga_join_fact HS 2019%nat (mkAF 4096 140737479966720 4)
ltac:(rewrite E2019; rewrite unsigned_lit_small by exact Hflt_rng; change (2 ^ 4) with 16; split; [clear - Hflt4096 Hfltceil Hrqflt C1; lia|]; split; [exact Hflt16 | clear; lia])).
unfold ss_QE2 in HS.
rregU HS (23%bv : bv 5) flt ltac:(apply (U_atom _ 2019 flt E2019); exact Hflt_rng) G23y.
slot_val HS (Some 2%nat) (-576) (-336) (Z_to_bv 64 (troot tr)) ltac:(exact (q_denot_off0 _ 2024 (troot tr) E2024 ltac:(clear - Hroot_rng C1; lia))) QSroot2.
m_join_slots_win HS ss_QE 900%nat rga_deads_QE [(Some 2%nat, (-576), (-408)); (Some 2%nat, (-576), (-336))]
ltac:(idtac; ga_join_val HS 900%nat 19%nat G23y N919; ga_join_val HS 900%nat 24%nat QSroot2 N924;
ga_join_fact HS 919%nat (mkAF 4096 140737479966720 4)
ltac:(rewrite N919; rewrite unsigned_lit_small by exact Hflt_rng; change (2 ^ 4) with 16; split; [clear - Hflt4096 Hfltceil Hrqflt C1; lia|]; split; [exact Hflt16 | clear; lia])).
rga_hand RC HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, flt, (4 * (fmt * N)), Tt, tr.
split; [split; [clear - Hk0 Hnodes HEVv; rewrite HEVv; (let v := eval vm_compute in EV_ADDFRAME in change EV_ADDFRAME with v); unfold EV_HD, EV_FREECHT in *; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia|].
split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx|].
split; [split; [exact N919 | split; [exact Tflt | exact Aflt]]|].
split; [clear - HMq; subst Mq; lia|].
split; [exact N924|].
split; [exact Htree7 | exact Hth].
Qed.
End d.
End c.

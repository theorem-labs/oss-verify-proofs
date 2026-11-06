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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCi2 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCnb YCoh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCpg YCp3 YCpd.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjh YCj9 YCjd YCjg YCjf YCp1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCpf.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis FREETREE : tfree_tree_specV B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_qXTb : rga_fromA B ss_XD (fun _ => INV_XD B) -> rga_from B ss_XTb (INV_XT B).
Proof.
intros RC.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & Tsz & dn & nd & tr & Hk0 & Hfmt & HTsz & Hnd & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
Rf & Rh & Ru & Rp & Rx & (Rdn & Tdn & Adn) & Rroot & Htree & Hth).
destruct Hk0 as [Hk0 Hbud].
unfold ss_XTb in HS.
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
set (keep3 := [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tsz) ++ [(dn, nd)]) in *.
assert (HPm3' : Permutation (ablocks B ly3 S3) (ablocks B ly S ++ keep3 ++ tree_blocks tr))
by (eapply Permutation_trans; [exact HPm3|]; subst keep3; rewrite <- !app_assoc; cbn [app]; apply Permutation_refl).
assert (HFPlive : forall b n, In (b, n) (tree_blocks tr) -> In (b, n) (keep3 ++ tree_blocks tr) /\ In (b, n) (ablocks B ly3 S3)).
{ intros b n Hbn. assert (Hn2 : In (b, n) (keep3 ++ tree_blocks tr)) by (apply in_or_app; right; exact Hbn).
split; [exact Hn2 | eapply Permutation_in; [apply Permutation_sym; exact HPm3' | apply in_or_app; right; exact Hn2]]. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ3 AG EE.
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
assert (HEA : 0 <= EV_ADDFRAME) by (vm_compute; discriminate).
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS Hsegs W3 Ex ssX msX TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k
(FDT_STK (Z.of_nat (Z.to_nat TREE_HMAX))) (ablocks_fp (tree_blocks tr)) (Z.of_nat (length (tree_nodes tr)))
(-576) (ew Ex 2) (Z_to_bv 64 0x848f4) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) (ablocks B ly S ++ keep3) /\ bud_le S3 S2 (Z.of_nat (length (tree_nodes tr))) 0 0 0) HS eq_refl HJ3);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| ga_evalE AG
| reflexivity
| clear; lia
| vm_compute; discriminate
| rewrite FFS; vm_compute; discriminate
| rewrite Rgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| rewrite unsigned_lit_small by (clear; lia); clear; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -576) with (spZ regs - 576) by (clear; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (FREETREE (Z.to_nat TREE_HMAX) ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) tr (ablocks B ly S ++ keep3) Hth HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc];
let v := eval vm_compute in A_free_decision_tree in change (w64 A_free_decision_tree) with (Z_to_bv 64 v) in CALL;
apply CALL; clear CALL
| cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJc & HPc & HK7);
exists ly7, S7, regs7, mem7, md7; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc | exact HK7] ]
| idtac ]
| ] end end.
- unfold raZ at 1. rewrite Rra, unsigned_lit_small by (clear; lia). cbn [spine map fst snd]. fold (spine ch). rewrite <- ?Hra88. destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; rewrite <- ?Hra88; tauto.
- rewrite Ra0. first [exact Rroot | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rroot].
- exact Htree.
- eapply Permutation_trans; [exact HPm3'|]. YI0g.perm_tac.
- rga_room Hev Hbud; (try (unfold EV_FREECHT in Hk0); clear - Hk0 HEVv; rga_lia).
- intros a Ha. right. destruct (inFP_ablocks_fp_inv _ _ Ha) as (b & n & Hbn & Hrg). exists b, n.
destruct (HFPlive b n Hbn) as (Hn2 & Hlv). split; [exact Hlv|]. split; [|exact Hrg].
intros Hin0. pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (b, n) (b, n) HAR3 HPm3' Hin0 Hn2) as Hdj.
unfold zdisjoint, block_rng in Hdj. cbn [fst snd] in Hdj. clear - Hdj Hrg. lia.
- cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc & HP7 & HK7 & Hd7).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs7 & _). cbn [app] in Hfrs7.
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (eapply Permutation_in; [apply Permutation_sym; exact HK7 | apply in_or_app; left; exact Hrin]).
assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (eapply Permutation_in; [apply Permutation_sym; exact HK7 | apply in_or_app; right; subst keep3; right; right; left; reflexivity]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HnoF : forall a, F <= a < F + 8192 -> ~ inFP (ablocks_fp (tree_blocks tr)) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (_ & Hlv).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ b n 7 fpos HAR3 Hlv Hfin3) as Dd.
rewrite EFA3 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hrg. lia. }
assert (HnoS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ inFP (ablocks_fp (tree_blocks tr)) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (_ & Hlv).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b n HAR3 Hlv) as (_ & (_ & Hbz) & _). clear - Ha Hrg Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
assert (HnoR : forall a, r <= a < r + 64 -> ~ inFP (ablocks_fp (tree_blocks tr)) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (Hn2 & _).
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (b, n) HAR3 HPm3' Hrin Hn2) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. change (req_size 64) with 64 in Dd. clear - Dd Ha Hrg. lia. }
assert (HnoC : forall a, cfp <= a < cfp + 24 -> ~ inFP (ablocks_fp (tree_blocks tr)) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (_ & Hlv).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ b n cid pos HAR3 Hlv HfinS3) as Dd.
rewrite EFA3 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hrg Hflo Hfhi. lia. }
assert (HnoT : forall a, tb <= a < tb + 48 -> ~ inFP (ablocks_fp (tree_blocks tr)) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg).
assert (HPtb : Permutation (ablocks B ly3 S3) ((tb, 48) :: (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tsz ++ [(dn, nd)] ++ tree_blocks tr)))
by (eapply Permutation_trans; [exact HPm3'|]; subst keep3; YI0g.perm_tac).
pose proof (m_blk_off_blk B LAWS ly3 S3 _ _ _ b n tb 48 _ HAR3 HPtb ltac:(apply in_or_app; right; right; right; apply (in_or_app (cht_blocks fq hh uu pp xx Tsz)); right; right; exact Hbn) a Hrg) as Dd.
change (req_size 48) with 48 in Dd. exact (Dd Ha). }
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 13; 14]%nat AG
ltac:(idtac; first
[ m_keptJ HJc HJ7 AG Usp FFS RF E67 E10n E11n Hfin3 HfinS3 Hrin3 Hrin7 EFA3 F HFpres7 HnoF HnoS HnoR HnoC LAWS
ltac:(idtac; m_keptJ_blk HJc AG 305%nat Rtb Htb_in3 Htb_in7 48 HnoT LAWS)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x848fc.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
norm_ss HS.
ga_join HS ss_XD 2600%nat rga_deads_XD ltac:(idtac).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RC HS HJ7 (k + Z.of_nat (length (tree_nodes tr))); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, Tsz, dn, nd. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HTsz|]. split; [exact Hnd|].
split; [exact HK7|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
do 5 (split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; assumption|]).
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rdn | split; [exact Tdn | exact Adn]].
Qed.
End e.
End d.

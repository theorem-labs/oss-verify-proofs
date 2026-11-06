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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCni YCnb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCnw YCnx YCny YCop YCne.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCiq.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YCj8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqj.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_PW : forall n pm, rga_from B ss_PL (INV_PL B n pm) -> rga_from B ss_PW1 (INV_PW B n pm).
Proof.
intros n pm IH.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & El & i1 & k1 & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HCLm8 & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & R818 & Hmeas & Hqlt & Hlt & R821 &
R869 & R867 & R862 & R868 & R870 & R824 & Hix0 & Hlt1 & Hkxc & HlenEl & PIperm & HPIm).
destruct Hk0 as [Hk0 Hbud].
unfold ss_PW1 in HS.
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
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
assert (HT24 : 0 < T <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
destruct (cinv_counts cnt ent st Hcinv) as (HL1 & Hlen_ns & Hq0n & Hlen_E & HpermE).
set (q := c_q st) in *. set (ns := c_ns st) in *. set (L := nleaves ns) in *.
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx T ++ [(dn, 4 * cnt)] ++ m_node_blocks tns).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz ->
0 <= a < 2 ^ 64 /\ ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq.
destruct Hq as [Hq1 Hq2]. split; [exact Hq1|]. intros Hc. apply Hq2. unfold m_ZsP. clear - Hc. lia. }
assert (Hpp_l : In (pp, 3 * T) lrest) by (subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); left; cbn [cht_blocks In]; tauto).
assert (Hdn_l : In (dn, 4 * cnt) lrest) by (subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); right; left; reflexivity).
assert (Hnode_l : forall t, In t tns -> In (tn_addr t, NODE_SIZE) lrest)
by (intros t Ht; subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); right; right; unfold m_node_blocks; apply in_map_iff; exists t; split; [reflexivity | exact Ht]).
assert (Htns_in : forall j, 0 <= j < elen tns -> In (tnth tns j) tns) by (intros j Hj; unfold tnth; apply znth_In; exact Hj).
assert (Hntns : elen tns <= 509) by (rewrite Hlen_tns; fold ns; rewrite Hlen_ns; fold L; clear - HL254; lia).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ r 64 7 fpos HAR3 Hrin3 Hfin3) as HdF_r.
unfold zdisjoint in HdF_r. cbn [fst snd] in HdF_r. change (fs_frame_bytes 7) with 8192 in HdF_r. change (req_size 64) with 64 in HdF_r. rewrite EFA3 in HdF_r. fold F in HdF_r.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ tb 48 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. change (req_size 48) with 48 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb.
set (tn := tnth tns q) in *. set (nd := node ns q) in *.
assert (Hq_t : 0 <= q < elen tns) by (rewrite Hlen_tns; fold ns; clear - Hq0n Hqlt; lia).
cbv zeta in HPIm. fold q ns nd tn in HPIm.
set (cut := tn_cut tn) in *. set (lo := n_lo nd) in *. set (hi := n_hi nd) in *.
set (sg := dseg cut (c_E st) lo hi) in *. set (P := Ptest cut (wsum sg) (wdot sg)) in *.
destruct HPIm as (PI1 & Hpm1).
assert (Hzl : zlen (pal_bytes El ++ tail) = 3 * T)
by (unfold zlen; rewrite length_app, Nat2Z.inj_add; change (Z.of_nat (length (pal_bytes El))) with (zlen (pal_bytes El)); change (Z.of_nat (length tail)) with (zlen tail);
rewrite zlen_pal_bytes, HlenEl; clear - Htail; lia).
assert (Hi1r : 0 <= i1 < cnt /\ 0 <= k1 < cnt /\ 3 * cnt <= 3 * T) by (clear - Hix0 Hlt1 Hkxc HcntT; lia).
assert (Hpp_in3 : In (pp, 3 * T) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hpp_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * T) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq3T.
assert (HRNG7 : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= 2147446784 \/ 17594333495296 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= 2147446784 \/ 17594333495296 <= cfp)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880).
{ unfold gbox, in_app in HFhigh, Hrapp, Hfhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh, Hrapp, Hfhigh.
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil Hrapp; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi Hfhigh; lia|]. split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
assert (HRtb7 : (4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= 2147446784 \/ 17594333495296 <= tb)) /\
(F + 8192 <= alloc_ceiling /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ 512 <= F / 8) /\ SB = 2147450880).
{ unfold gbox in Htbzone. change (req_size 48) with 48 in Htbzone. split; [clear - Htb4096 Htbceil Hrqtb Htbzone C1; lia|]. split; [clear - HFceil HFq HF8 HF8lo; lia | reflexivity]. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rpp1 : ew Ex 618 = Z_to_bv 64 pp) by m_ewT;
assert (Rx12a : ew Ex 862 = Z_to_bv 64 (3 * i1)) by m_ewT;
assert (HB2a : bv_unsigned (ew Ex 2) = spZ regs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp) end.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (spZ regs + -131) ltac:(apply (U_atom_off _ 2 (spZ regs) (-131)); [rewrite <- HB2a; symmetry; apply Z_to_bv_bv_unsigned | clear - Hceil Hslo Hshi H47 FFS C1; lia | clear - Hceil Hslo Hshi H47 FFS C1; lia]) Ha0.
rregU HS (11%bv : bv 5) (pp + 3 * i1)
ltac:(apply m_U_add0; apply U_add_small_q; [apply (U_atom _ 618 pp Rpp1); clear - Hpp4096 Hppceil Hrq3T C1; lia
| apply U_zext32_shifts; [apply (U_atom _ 862 (3 * i1) Rx12a); clear - Hi1r HcntT HT24; lia | clear - Hi1r HcntT HT24; lia]
| clear - Hpp4096; lia | clear - Hi1r; lia | clear - Hi1r Hppceil Hrq3T C1; lia]) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
pose proof HJ3 as (_ & Hly7 & _). pose proof Hly7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo7 & Ehi7 & _).
destruct (rg_stack_shadow B LAWS W3 ly3 S3 _ _ (spZ regs + -131) 3 (proj1 HJ3)
ltac:(rewrite Elo7; clear - Hslo FFS; lia) ltac:(rewrite Ehi7; clear - Hshi; lia) ltac:(clear; lia)) as [HRAt HHVt].
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp (3 * T) (proj1 HJ3) Hpp_in3) as (_ & _ & _ & _ & HppP & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) 7 fpos HAR3 Hpp_in3 Hfin3) as HdF_pp.
unfold zdisjoint in HdF_pp. cbn [fst snd] in HdF_pp. change (fs_frame_bytes 7) with 8192 in HdF_pp. rewrite EFA3 in HdF_pp. fold F in HdF_pp.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (spZ regs + -131) (pp + 3 * i1) 3 (-576) (Z_to_bv 64 0x83ad4) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Hceil Hslo FFS C1; lia.
- clear - Hshi H47; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [left; rewrite FFS; clear - Ha; lia | rewrite Hes; clear - Ha; lia].
- right. unfold kHighMemBeg, kHighMemEnd. clear - Hceil Hslo Hshi H47 FFS C1. lia.
- exact HRAt.
- intros _. apply HHVt. clear; lia.
- split; [clear - Hpp4096 Hi1r; lia|]. split; [clear - Hppceil Hrq3T Hi1r C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); exact (proj1 (HppP a ltac:(clear - Ha Hrq3T Hi1r; lia)))
| rewrite HspT, Hes; clear - Ha Hppceil Hrq3T Hi1r Hceil Hslo FFS; lia]. }
split; [right; clear - Hppceil Hrq3T Hi1r Hceil Hslo FFS; lia|]. split.
{ apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * i1) 3 (proj1 HJ3) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia]. }
split; [apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * i1) 3 (proj1 HJ3) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia]|].
intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * i1) 3 (proj1 HJ3) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia | clear; lia]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Ha06 & Heff6 & Hfr6 & Hpres6).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
assert (Hfr2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -131 <= a < spZ regs + -131 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576) ->
aview trbsegs (w_H W3) mem6 a = aview trbsegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha1 Ha2; apply Hfr6; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
assert (HWIN : forall a, 0 <= a < alloc_ceiling -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs + -131 <= a < spZ regs + -131 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha; rewrite Hes; clear - Ha Hceil Hslo FFS C1; lia).
assert (HWSTc : forall a, spZ regs + -576 <= a < spZ regs + 0 -> ~ (spZ regs + -131 <= a < spZ regs + -128) ->
0 <= a < 2 ^ 64 /\ ~ (spZ regs + -131 <= a < spZ regs + -131 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hn Hceil Hslo Hshi H47 FFS C1; lia).
m_reseatF HS HJ6 fx regs6 CLOB 539348 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP6)
ltac:(idtac; first
[ m_keptWc Hfr2 Hpres6 HJ6 HWIN HWSTc HRNG7 AG Usp RF E67 E10n E11n (-131) (-128)
ltac:(idtac; first [ m_keptW_blk Hfr2 Hpres6 HWIN AG 305%nat tb Rtb HRtb7
| ga_kept_consts Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
ga_relow HS AG E10 E11 E10n E11n.
clear HEE0. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE0 end.
norm_ss HS.
assert (MBA : forall (m m' : word -> option byte) a x b, aview trbsegs (w_H W3) m' a = aview trbsegs (w_H W3) m x ->
mbyte trbsegs (mrestrict (w_H W3) m) x = Some b -> mbyte trbsegs (mrestrict (w_H W3) m') a = Some b).
{ intros m0 m1 a x b Ev Hb. unfold aview in Ev. rewrite Hb in Ev. destruct (mbyte trbsegs (mrestrict (w_H W3) m1) a) as [b1|]; cbn in Ev; [|discriminate].
injection Ev as Ev. f_equal. apply bv_eq. exact Ev. }
set (palc := pal_bytes El ++ tail) in *.
assert (HK6 : forall a, 0 <= a < alloc_ceiling -> aview trbsegs (w_H W3) mem6 a = aview trbsegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha; apply Hfr2; apply (HWIN a Ha)).
assert (HCLm9 : m_CLmem (w_H W3) mem6 pp dn F tail (mkC El (c_ns st) (c_q st)) tns).
{ apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail (mkC El (c_ns st) (c_q st)) tns HCLm8); cbn [c_E c_ns].
- intros i Hi. fold palc in Hi. rewrite Hzl in Hi. apply HK6. clear - Hi Hpp4096 Hppceil Hrq3T. lia.
- intros i Hi. rewrite zlen_fr_vals, HlenEl in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * cnt) HAR3 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hdn_l])) as (Hdn4096 & _ & Hdnceil & _).
apply HK6. clear - Hi Hdn4096 Hdnceil Hrq. lia.
- intros j Hj i Hi.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ _ NODE_SIZE HAR3 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact (Hnode_l _ (Htns_in j Hj))])) as (Hn4096 & _ & Hnceil & _).
change (req_size NODE_SIZE) with 56 in Hnceil. apply HK6. unfold NODE_SIZE in Hi. clear - Hi Hn4096 Hnceil. lia.
- intros i Hi. apply HK6. clear - Hi Hntns HF4096 HFceil. lia. }
pose proof (proj1 HCLm8) as CB1. cbn [c_E] in CB1. fold palc in CB1.
assert (Htmp : forall j, 0 <= j < 3 -> val_mem trbsegs (mrestrict (w_H W3) mem6) (spZ regs + (-131 + j)) 1 (getz palc (3 * i1 + j)) /\ 0 <= getz palc (3 * i1 + j) < 256).
{ intros j Hj. destruct (arr8_getz trbsegs _ pp palc (3 * i1 + j) CB1 ltac:(rewrite Hzl; clear - Hj Hi1r; lia)) as [Hbyte Hbr]. split; [|exact Hbr].
apply (YI0d.val_mem_byte trbsegs); [|exact Hbr].
apply (MBA (ms_mem ms3) mem6 _ (pp + (3 * i1 + j))); [|exact Hbyte].
replace (spZ regs + (-131 + j)) with (spZ regs + -131 + j) by (clear; lia). replace (pp + (3 * i1 + j)) with (pp + 3 * i1 + j) by (clear; lia). apply Heff6. exact Hj. }
destruct (Htmp 0 ltac:(clear; lia)) as [Vt0 Rt0]. destruct (Htmp 1 ltac:(clear; lia)) as [Vt1 Rt1]. destruct (Htmp 2 ltac:(clear; lia)) as [Vt2 Rt2].
change (-131 + 0) with (-131) in Vt0. change (-131 + 1) with (-130) in Vt1. change (-131 + 2) with (-129) in Vt2.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trbsegs 887%nat Ex ssx msx [Z_to_bv 64 (getz palc (3 * i1 + 0)); Z_to_bv 64 (getz palc (3 * i1 + 1)); Z_to_bv 64 (getz palc (3 * i1 + 2))]
HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
assert (E887 : ew (havoc E0v 887 vals) 887 = Z_to_bv 64 (getz palc (3 * i1 + 0)))
by (change 887%nat with (887 + 0)%nat at 2; rewrite (ew_havoc_new _ 887%nat vals 0%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E888 : ew (havoc E0v 887 vals) 888 = Z_to_bv 64 (getz palc (3 * i1 + 1)))
by (change 888%nat with (887 + 1)%nat; rewrite (ew_havoc_new _ 887%nat vals 1%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E889 : ew (havoc E0v 887 vals) 889 = Z_to_bv 64 (getz palc (3 * i1 + 2)))
by (change 889%nat with (887 + 2)%nat; rewrite (ew_havoc_new _ 887%nat vals 2%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
m_add_chunk HS 2%nat (-131) 1%N (SOff 887 0) (spZ regs) (getz palc (3 * i1 + 0))
ltac:(repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E887) ltac:(cbn; exact Rt0) Vt0.
m_add_chunk HS 2%nat (-130) 1%N (SOff 888 0) (spZ regs) (getz palc (3 * i1 + 1))
ltac:(repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E888) ltac:(cbn; exact Rt1) Vt1.
m_add_chunk HS 2%nat (-129) 1%N (SOff 889 0) (spZ regs) (getz palc (3 * i1 + 2))
ltac:(repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E889) ltac:(cbn; exact Rt2) Vt2.
m_env_fold HS AG.
clear HEE0. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE0 end.
reshok_bx HS 44%nat.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HUppq : U Ev (SOff 618 0) = pp) by (apply (U_atom Ev 618 pp); [m_ewT | clear - Hpp4096 Hppceil Hrq3T C1; lia]);
assert (HUz3k : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SOff 868 0) (SLit 32)) (SLit 32)) = 3 * k1)
by (apply U_zext32_shifts; [apply (U_atom Ev 868 (3 * k1)); [m_ewT | clear - Hi1r HcntT HT24; lia] | clear - Hi1r HcntT HT24; lia]) end.
m_add_cond HS BC_GEU (SAlu ALU_XOR (SOff 618 0) (SLit (-1))) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 868 0) (SLit 32)) (SLit 32))
ltac:(eapply (ub_room_cond _ _ _ pp (3 * k1) HUppq HUz3k); clear - Hpp4096 Hppceil Hrq3T C1 Hi1r HcntT HT24; lia).
clear HUppq HUz3k.
aj_run_to_tok trbtbl_lib_ok HS HJ6 SHOK GBspan 0x52074.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * T) HAR3 Hpp_in3) as (_ & Hppzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) cid pos HAR3 Hpp_in3 HfinS3) as HdC_pp.
unfold zdisjoint in HdC_pp. cbn [fst snd] in HdC_pp. rewrite EFA3 in HdC_pp.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (pp, 3 * T) HAR3 HPrt3 ltac:(right; exact Hpp_l)) as HzR_pp.
unfold zdisjoint, block_rng in HzR_pp. cbn [fst snd] in HzR_pp. change (req_size RGB_SIZE) with 64 in HzR_pp.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (pp, 3 * T) HAR3 HPtb3 ltac:(right; exact Hpp_l)) as HzT_pp.
unfold zdisjoint, block_rng in HzT_pp. cbn [fst snd] in HzT_pp. change (req_size 48) with 48 in HzT_pp.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rpp2 : ew Ex 618 = Z_to_bv 64 pp) by m_ewT;
assert (Rx12b : ew Ex 862 = Z_to_bv 64 (3 * i1)) by m_ewT;
assert (Rx13b : ew Ex 868 = Z_to_bv 64 (3 * k1)) by m_ewT end.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (pp + 3 * i1)
ltac:(apply m_U_add0; apply U_add_small_q; [apply (U_atom _ 618 pp Rpp2); clear - Hpp4096 Hppceil Hrq3T C1; lia
| apply U_zext32_shifts; [apply (U_atom _ 862 (3 * i1) Rx12b); clear - Hi1r HcntT HT24; lia | clear - Hi1r HcntT HT24; lia]
| clear - Hpp4096; lia | clear - Hi1r; lia | clear - Hi1r Hppceil Hrq3T C1; lia]) Ha0.
rregU HS (11%bv : bv 5) (pp + 3 * k1)
ltac:(apply m_U_add0; apply U_add_small_q; [apply (U_atom _ 618 pp Rpp2); clear - Hpp4096 Hppceil Hrq3T C1; lia
| apply U_zext32_shifts; [apply (U_atom _ 868 (3 * k1) Rx13b); clear - Hi1r HcntT HT24; lia | clear - Hi1r HcntT HT24; lia]
| clear - Hpp4096; lia | clear - Hi1r; lia | clear - Hi1r Hppceil Hrq3T C1; lia]) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT2 : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp (3 * T) (proj1 HJ6) Hpp_in3) as (_ & _ & _ & _ & HppP2 & _).
rga_chain HS HJ6 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ6 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (pp + 3 * i1) (pp + 3 * k1) 3 (-576) (Z_to_bv 64 0x83af4) HJ6) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Hpp4096 Hi1r; lia.
- clear - Hppceil Hrq3T Hi1r C1; lia.
- exact HspT2.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [| rewrite Hes; clear - Ha Hppceil Hrq3T Hi1r Hceil Hslo FFS; lia].
replace a with (pp + (a - pp)) by (clear; lia). apply App; [exact Hpp_in3 | clear - Ha Hrq3T Hi1r; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * i1) 3 (proj1 HJ6) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia].
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * i1) 3 (proj1 HJ6) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * i1) 3 (proj1 HJ6) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia | clear; lia].
- split; [clear - Hpp4096 Hi1r; lia|]. split; [clear - Hppceil Hrq3T Hi1r C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); exact (proj1 (HppP2 a ltac:(clear - Ha Hrq3T Hi1r; lia)))
| rewrite HspT2, Hes; clear - Ha Hppceil Hrq3T Hi1r Hceil Hslo FFS; lia]. }
split; [left; clear - Hlt1; lia|]. split.
{ apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * k1) 3 (proj1 HJ6) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia]. }
split; [apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * k1) 3 (proj1 HJ6) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia]|].
intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * k1) 3 (proj1 HJ6) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia | clear; lia]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
assert (Hfr3 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 3 * i1 <= a < pp + 3 * i1 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576) ->
aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) (ms_mem ms) a)
by (intros a Ha1 Ha2; apply Hfr5; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
assert (HWIN3 : forall a, 0 <= a < alloc_ceiling -> ~ (pp <= a < pp + 3 * T) ->
0 <= a < 2 ^ 64 /\ ~ (pp + 3 * i1 <= a < pp + 3 * i1 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hn Hi1r Hceil Hslo FFS C1; lia).
assert (HWSTc3 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> ~ (spZ regs + 0 <= a < spZ regs + 0) ->
0 <= a < 2 ^ 64 /\ ~ (pp + 3 * i1 <= a < pp + 3 * i1 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hppceil Hrq3T Hi1r Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG8 : ((4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= 2147446784 \/ 17594333495296 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= 2147446784 \/ 17594333495296 <= cfp)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880) /\
(3 * T <= req_size (3 * T) /\ (pp + req_size (3 * T) <= 2147446784 \/ 17594333495296 <= pp) /\ (pp + req_size (3 * T) <= F \/ F + 8192 <= pp) /\
(r + 64 <= pp \/ pp + req_size (3 * T) <= r) /\
(pp + req_size (3 * T) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= pp) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid)).
{ split; [exact HRNG7|]. unfold gbox in Hppzone. clear - Hrq3T Hppzone HdF_pp HzR_pp HdC_pp Hflo Hfhi. lia. }
assert (HRtb8 : ((4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= 2147446784 \/ 17594333495296 <= tb)) /\
(F + 8192 <= alloc_ceiling /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ 512 <= F / 8) /\ SB = 2147450880) /\
3 * T <= req_size (3 * T) /\ (tb + 48 <= pp \/ pp + req_size (3 * T) <= tb)).
{ split; [exact HRtb7|]. clear - Hrq3T HzT_pp. lia. }
m_reseatF HS HJ5 fx regs5 CLOB 539380 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP5)
ltac:(idtac; first
[ m_keptWc Hfr3 Hpres5 HJ5 HWIN3 HWSTc3 HRNG8 AG Usp RF E67 E10n E11n 0 0
ltac:(idtac; first [ m_keptW_blk Hfr3 Hpres5 HWIN3 AG 305%nat tb Rtb HRtb8
| ga_kept_consts Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
clear HEE0. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE0 end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK GBspan 0x52074.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rpp3 : ew Ex 618 = Z_to_bv 64 pp) by m_ewT;
assert (Rx13c : ew Ex 868 = Z_to_bv 64 (3 * k1)) by m_ewT;
assert (Rt887 : ew Ex 887 = Z_to_bv 64 (getz palc (3 * i1 + 0))) by m_ewT;
assert (Rt888 : ew Ex 888 = Z_to_bv 64 (getz palc (3 * i1 + 1))) by m_ewT;
assert (Rt889 : ew Ex 889 = Z_to_bv 64 (getz palc (3 * i1 + 2))) by m_ewT;
assert (HB2c : bv_unsigned (ew Ex 2) = spZ regs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp) end.
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 8 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-131) 1%N (SOff 887 0) (getz palc (3 * i1 + 0)) HRc HB2c ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Rt887) ltac:(cbn; exact Rt0) ltac:(cbn; lia)) as Wt0;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-130) 1%N (SOff 888 0) (getz palc (3 * i1 + 1)) HRc HB2c ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Rt888) ltac:(cbn; exact Rt1) ltac:(cbn; lia)) as Wt1;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-129) 1%N (SOff 889 0) (getz palc (3 * i1 + 2)) HRc HB2c ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Rt889) ltac:(cbn; exact Rt2) ltac:(cbn; lia)) as Wt2
end; clear HRc end.
change (N.to_nat 1) with 1%nat in Wt0, Wt1, Wt2.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (pp + 3 * k1)
ltac:(apply m_U_add0; apply U_add_small_q; [apply (U_atom _ 618 pp Rpp3); clear - Hpp4096 Hppceil Hrq3T C1; lia
| apply U_zext32_shifts; [apply (U_atom _ 868 (3 * k1) Rx13c); clear - Hi1r HcntT HT24; lia | clear - Hi1r HcntT HT24; lia]
| clear - Hpp4096; lia | clear - Hi1r; lia | clear - Hi1r Hppceil Hrq3T C1; lia]) Ha0.
rregU HS (11%bv : bv 5) (spZ regs + -131) ltac:(apply (U_atom_off _ 2 (spZ regs) (-131)); [rewrite <- HB2c; symmetry; apply Z_to_bv_bv_unsigned | clear - Hceil Hslo Hshi H47 FFS C1; lia | clear - Hceil Hslo Hshi H47 FFS C1; lia]) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT3 : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
pose proof HJ5 as (_ & Hly5 & _). pose proof Hly5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo5 & Ehi5 & _).
destruct (rg_stack_shadow B LAWS W3 ly3 S3 _ _ (spZ regs + -131) 3 (proj1 HJ5)
ltac:(rewrite Elo5; clear - Hslo FFS; lia) ltac:(rewrite Ehi5; clear - Hshi; lia) ltac:(clear; lia)) as [HRAt3 HHVt3].
pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp5 & _).
rga_chain HS HJ5 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ5 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (pp + 3 * k1) (spZ regs + -131) 3 (-576) (Z_to_bv 64 0x83b04) HJ5) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Hpp4096 Hi1r; lia.
- clear - Hppceil Hrq3T Hi1r C1; lia.
- exact HspT3.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [| rewrite Hes; clear - Ha Hppceil Hrq3T Hi1r Hceil Hslo FFS; lia].
replace a with (pp + (a - pp)) by (clear; lia). apply App; [exact Hpp_in3 | clear - Ha Hrq3T Hi1r; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * k1) 3 (proj1 HJ5) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia].
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * k1) 3 (proj1 HJ5) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ pp (3 * T) (pp + 3 * k1) 3 (proj1 HJ5) Hpp_in3); [clear - Hi1r; lia | clear - Hrq3T Hi1r; lia | clear; lia].
- split; [clear - Hceil Hslo FFS C1; lia|]. split; [clear - Hshi H47; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply Hsp5; rewrite FFS; clear - Ha; lia
| rewrite HspT3, Hes; clear - Ha; lia]. }
split; [left; clear - Hppceil Hrq3T Hi1r Hceil Hslo FFS; lia|]. split.
{ right. unfold kHighMemBeg, kHighMemEnd. clear - Hceil Hslo Hshi H47 FFS C1. lia. }
split; [exact HRAt3|]. intros _. apply HHVt3. clear; lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff4 & Hfr4 & Hpres4).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
assert (Hfr5b : forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 3 * k1 <= a < pp + 3 * k1 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576) ->
aview trbsegs (w_H W3) mem4 a = aview trbsegs (w_H W3) (ms_mem ms0) a)
by (intros a Ha1 Ha2; apply Hfr4; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
assert (HWIN4 : forall a, 0 <= a < alloc_ceiling -> ~ (pp <= a < pp + 3 * T) ->
0 <= a < 2 ^ 64 /\ ~ (pp + 3 * k1 <= a < pp + 3 * k1 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hn Hi1r Hceil Hslo FFS C1; lia).
assert (HWSTc4 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> ~ (spZ regs + 0 <= a < spZ regs + 0) ->
0 <= a < 2 ^ 64 /\ ~ (pp + 3 * k1 <= a < pp + 3 * k1 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hppceil Hrq3T Hi1r Hceil Hslo Hshi H47 FFS C1; lia).
m_reseatF HS HJ4 fx regs4 CLOB 539396 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP4)
ltac:(idtac; first
[ m_keptWc Hfr5b Hpres4 HJ4 HWIN4 HWSTc4 HRNG8 AG Usp RF E67 E10n E11n 0 0
ltac:(idtac; first [ m_keptW_blk Hfr5b Hpres4 HWIN4 AG 305%nat tb Rtb HRtb8
| ga_kept_consts Kgot0 Kgot4 Kcell0 Kcell4 Kguar0 Kguar4 Kuar0 Kuar4 Vgr0 Vgr4 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot4 into Kgot0. rename Kcell4 into Kcell0. rename Kguar4 into Kguar0. rename Kuar4 into Kuar0. rename Vgr4 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ4 end.
ga_relow HS AG E10 E11 E10n E11n.
clear HEE0. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE0 end.
norm_ss HS.
reshok_bx HS 44%nat.
assert (Hdn_in3q : In (dn, 4 * cnt) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hdn_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * cnt) HAR3 Hdn_in3q) as (Hdn4096q & _ & Hdnceilq & _).
pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq4cq.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HUdnq : U Ev (SOff 626 0) = dn) by (apply (U_atom Ev 626 dn); [m_ewT | clear - Hdn4096q Hdnceilq Hrq4cq C1; lia]);
assert (HU4k : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SOff 869 0) (SLit 32)) (SLit 30)) = 4 * k1)
by (apply m_U_idx4; [apply (U_atom Ev 869 k1); [m_ewT | clear - Hi1r HcntT HT24; lia] | clear - Hi1r HcntT HT24; lia]) end.
m_add_cond HS BC_GEU (SAlu ALU_XOR (SOff 626 0) (SLit (-1))) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 869 0) (SLit 32)) (SLit 30))
ltac:(eapply (ub_room_cond _ _ _ dn (4 * k1) HUdnq HU4k); clear - Hdn4096q Hdnceilq Hrq4cq C1 Hi1r; lia).
clear HUdnq HU4k.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK GBspan 0x83b20.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN4.
clear HF HFr HG.
norm_ss HS.
assert (Hdn_in3 : In (dn, 4 * cnt) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hdn_l]).
pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq4c.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * cnt) HAR3 Hdn_in3) as (Hdn4096 & Hdnzone & Hdnceil & Hdn16).
assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx T ++ ((dn, 4 * cnt) :: m_node_blocks tns ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
assert (Hpp_c : In (pp, 3 * T) (cht_blocks fq hh uu pp xx T)) by (cbn [cht_blocks In]; tauto).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * T) (dn, 4 * cnt) HAR3 HPx Hpp_c ltac:(left; reflexivity)) as Hs_pd.
unfold zdisjoint, block_rng in Hs_pd. cbn [fst snd] in Hs_pd.
assert (Hs_pn : forall j, 0 <= j < elen tns -> pp + req_size (3 * T) <= tn_addr (tnth tns j) \/ tn_addr (tnth tns j) + 56 <= pp).
{ intros j Hj. pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * T) (tn_addr (tnth tns j), NODE_SIZE) HAR3 HPx Hpp_c
ltac:(right; apply in_or_app; left; unfold m_node_blocks; apply in_map_iff; exists (tnth tns j); split; [reflexivity | exact (Htns_in j Hj)])) as Hdz.
unfold zdisjoint, block_rng in Hdz. cbn [fst snd] in Hdz. change (req_size NODE_SIZE) with 56 in Hdz. exact Hdz. }
assert (HPy : Permutation (ablocks B ly3 S3) ((dn, 4 * cnt) :: (m_node_blocks tns ++ cht_blocks fq hh uu pp xx T ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
assert (Hs_dn : forall j, 0 <= j < elen tns -> dn + req_size (4 * cnt) <= tn_addr (tnth tns j) \/ tn_addr (tnth tns j) + 56 <= dn).
{ intros j Hj. pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (dn, 4 * cnt) _ (tn_addr (tnth tns j), NODE_SIZE) HAR3 HPy
ltac:(apply in_or_app; left; unfold m_node_blocks; apply in_map_iff; exists (tnth tns j); split; [reflexivity | exact (Htns_in j Hj)])) as Hdz.
unfold zdisjoint, block_rng in Hdz. cbn [fst snd] in Hdz. change (req_size NODE_SIZE) with 56 in Hdz. exact Hdz. }
assert (HCLmA : m_CLmem (w_H W3) (ms_mem ms) pp dn F tail (mkC El (c_ns st) (c_q st)) tns).
{ apply (m_CLmem_kept (w_H W3) (w_H W3) mem6 _ pp dn F tail (mkC El (c_ns st) (c_q st)) tns HCLm9); cbn [c_E c_ns].
- intros i Hi. fold palc in Hi. rewrite Hzl in Hi. destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq3T; lia)) as (Hq1 & Hq2). exact (UN2 _ Hq1 Hq2).
- intros i Hi. rewrite zlen_fr_vals, HlenEl in Hi. destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq4c; lia)) as (Hq1 & Hq2). exact (UN2 _ Hq1 Hq2).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
exact (UN2 _ Hq1 Hq2).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
exact (UN2 _ Hq1 Hq2). }
assert (KEEP2 : forall a, 0 <= a < alloc_ceiling -> ~ ((F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (pp + 3 * i1 <= a < pp + 3 * i1 + 3) -> ~ (pp + 3 * k1 <= a < pp + 3 * k1 + 3) ->
aview trbsegs (w_H W3) (ms_mem ms1) a = aview trbsegs (w_H W3) (ms_mem ms) a).
{ intros a Ha Hx Hn1 Hn2.
assert (Hq1 : 0 <= a < 2 ^ 64) by (clear - Ha C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48)) by (clear - Ha Hx; lia).
rewrite (UN4 _ Hq1 Hq2).
rewrite (Hfr5b _ Hq1 ltac:(rewrite Hes; clear - Ha Hn2 Hceil Hslo FFS; lia)).
rewrite (UN3 _ Hq1 Hq2).
exact (Hfr3 _ Hq1 ltac:(rewrite Hes; clear - Ha Hn1 Hceil Hslo FFS; lia)). }
assert (Hdense2 : arr32 trbsegs (mrestrict (w_H W3) (ms_mem ms1)) dn (fr_vals El)).
{ apply (arr32_frame trbsegs _ _ dn _ (proj1 (proj2 HCLmA))). intros a Ha. cbn [c_E] in Ha. rewrite zlen_fr_vals, HlenEl in Ha. apply (mbyte_of_aview trbsegs).
destruct (Hoff3 dn _ Hdn_l a ltac:(clear - Ha Hrq4c; lia)) as (Hq1 & Hq2).
apply KEEP2; [clear - Ha Hdn4096 Hdnceil Hrq4c; lia | clear - Hq2; tauto | clear - Ha Hs_pd Hrq4c Hrq3T Hi1r; lia | clear - Ha Hs_pd Hrq4c Hrq3T Hi1r; lia]. }
destruct (arr32_getz trbsegs _ dn (fr_vals El) k1 Hdense2 ltac:(rewrite zlen_fr_vals, HlenEl; clear - Hi1r; lia)) as [Vfk Rfk].
destruct (arr32_getz trbsegs _ dn (fr_vals El) i1 Hdense2 ltac:(rewrite zlen_fr_vals, HlenEl; clear - Hi1r; lia)) as [Vfi Rfi].
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ dn (4 * cnt) 7 fpos HAR3 Hdn_in3 Hfin3) as HdF_dn.
unfold zdisjoint in HdF_dn. cbn [fst snd] in HdF_dn. change (fs_frame_bytes 7) with 8192 in HdF_dn. rewrite EFA3 in HdF_dn. fold F in HdF_dn.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ dn (4 * cnt) cid pos HAR3 Hdn_in3 HfinS3) as HdC_dn.
unfold zdisjoint in HdC_dn. cbn [fst snd] in HdC_dn. rewrite EFA3 in HdC_dn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (dn, 4 * cnt) HAR3 HPrt3 ltac:(right; exact Hdn_l)) as HzR_dn.
unfold zdisjoint, block_rng in HzR_dn. cbn [fst snd] in HzR_dn. change (req_size RGB_SIZE) with 64 in HzR_dn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (dn, 4 * cnt) HAR3 HPtb3 ltac:(right; exact Hdn_l)) as HzT_dn.
unfold zdisjoint, block_rng in HzT_dn. cbn [fst snd] in HzT_dn. change (req_size 48) with 48 in HzT_dn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ dn (4 * cnt) (proj1 HJ4) Hdn_in3) as (_ & _ & _ & _ & Hdnpres & _).
set (fk := getz (fr_vals El) k1) in *. set (fi := getz (fr_vals El) i1) in *.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trbsegs 924%nat Ex ssx msx [Z_to_bv 64 (dn + 4 * k1); Z_to_bv 64 fk; Z_to_bv 64 (dn + 4 * i1); Z_to_bv 64 fi] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
assert (E924 : ew (havoc E0v 924 vals) 924 = Z_to_bv 64 (dn + 4 * k1))
by (change 924%nat with (924 + 0)%nat at 2; rewrite (ew_havoc_new _ 924%nat vals 0%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E925 : ew (havoc E0v 924 vals) 925 = Z_to_bv 64 fk)
by (change 925%nat with (924 + 1)%nat; rewrite (ew_havoc_new _ 924%nat vals 1%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E926 : ew (havoc E0v 924 vals) 926 = Z_to_bv 64 (dn + 4 * i1))
by (change 926%nat with (924 + 2)%nat; rewrite (ew_havoc_new _ 924%nat vals 2%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E927 : ew (havoc E0v 924 vals) 927 = Z_to_bv 64 fi)
by (change 927%nat with (924 + 3)%nat; rewrite (ew_havoc_new _ 924%nat vals 3%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
assert (HcK : 4096 <= dn + 4 * k1 /\ dn + 4 * k1 + 4 <= alloc_ceiling) by (clear - Hdn4096 Hdnceil Hrq4c Hi1r; lia).
assert (HcI : 4096 <= dn + 4 * i1 /\ dn + 4 * i1 + 4 <= alloc_ceiling) by (clear - Hdn4096 Hdnceil Hrq4c Hi1r; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E924c : ew Ev 924 = Z_to_bv 64 (dn + 4 * k1)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E924);
assert (E925c : ew Ev 925 = Z_to_bv 64 fk) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E925);
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 924%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 925 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E924c, unsigned_lit_small by (clear - HcK C1; lia);
split; [clear - HcK; lia|]; split; [clear - HcK C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hdnpres (dn + 4 * k1 + o) ltac:(clear - Ho Hi1r Hrq4c; lia)))
| apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ (dn + 4 * k1) _ _ (SOff 925 0) fk);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E925c | exact Rfk | cbn; clear; lia
| rewrite Z.add_0_r; exact Vfk] | apply Forall_nil] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - HcK Hceil Hslo FFS Hi1r Hrq4c; lia
| destruct Hdnzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hi1r Hrq4c HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_dn Hi1r Hrq4c; lia
| clear - HdC_dn Hi1r Hrq4c Hflo Hfhi; lia
| clear - HzR_dn Hi1r Hrq4c; lia
| clear - HzT_dn Hi1r Hrq4c; lia
| fail
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E926c : ew Ev 926 = Z_to_bv 64 (dn + 4 * i1)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E926);
assert (E927c : ew Ev 927 = Z_to_bv 64 fi) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E927);
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 926%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 927 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E926c, unsigned_lit_small by (clear - HcI C1; lia);
split; [clear - HcI; lia|]; split; [clear - HcI C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hdnpres (dn + 4 * i1 + o) ltac:(clear - Ho Hi1r Hrq4c; lia)))
| apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ (dn + 4 * i1) _ _ (SOff 927 0) fi);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E927c | exact Rfi | cbn; clear; lia
| rewrite Z.add_0_r; exact Vfi] | apply Forall_nil] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - HcI Hceil Hslo FFS Hi1r Hrq4c; lia
| destruct Hdnzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hi1r Hrq4c HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_dn Hi1r Hrq4c; lia
| clear - HdC_dn Hi1r Hrq4c Hflo Hfhi; lia
| clear - HzR_dn Hi1r Hrq4c; lia
| clear - HzT_dn Hi1r Hrq4c; lia
| clear - Hlt1; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rdn4 : ew Ev 626 = Z_to_bv 64 dn) by m_ewT;
assert (Rk4 : ew Ev 869 = Z_to_bv 64 k1) by m_ewT;
assert (Ri4 : ew Ev 867 = Z_to_bv 64 i1) by m_ewT;
assert (E924d : ew Ev 924 = Z_to_bv 64 (dn + 4 * k1)) by m_ewT;
assert (E926d : ew Ev 926 = Z_to_bv 64 (dn + 4 * i1)) by m_ewT;
assert (HUA : U Ev (SAlu ALU_ADD (SOff 626 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 869 0) (SLit 32)) (SLit 30))) = U Ev (SOff 924 0)) end.
{ lazymatch goal with |- U ?Ev _ = _ =>
rewrite (U_atom Ev 924 (dn + 4 * k1) E924d) by (clear - HcK C1; lia);
apply (m_U_elem4 Ev 626 dn (SOff 869 0) k1);
[ exact Rdn4 | clear - Hdn4096; lia | clear - HcK C1; lia
| apply (U_atom Ev 869 k1 Rk4); clear - Hi1r HcntT HT24; lia
| clear - Hi1r HcntT HT24; lia ] end. }
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (10%bv : bv 5) (SOff 924 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (10%bv : bv 5) HS); change (sv_denot Ev (SOff 924 0) = sv_denot Ev e);
apply U_inj; symmetry; exact HUA)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 924%nat (mkAF 4096 140737479966720 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E924d, unsigned_lit_small by (clear - HcK C1; lia); change (2 ^ 2) with 4;
split; [clear - HcK C1; lia|]; split; [rewrite Z.add_mod, (Z.mul_comm 4 k1), Z_mod_mult, Z.add_0_r, Z.mod_mod by lia; clear - Hdn16; pose proof (Z.div_mod dn 16 ltac:(lia)) as D; rewrite Hdn16, Z.add_0_r in D; rewrite D; replace (16 * (dn / 16)) with ((4 * (dn / 16)) * 4) by lia; apply Z_mod_mult | clear - HcK C1; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 926%nat (mkAF 4096 140737479966720 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E926d, unsigned_lit_small by (clear - HcI C1; lia); change (2 ^ 2) with 4;
split; [clear - HcI C1; lia|]; split; [rewrite Z.add_mod, (Z.mul_comm 4 i1), Z_mod_mult, Z.add_0_r, Z.mod_mod by lia; clear - Hdn16; pose proof (Z.div_mod dn 16 ltac:(lia)) as D; rewrite Hdn16, Z.add_0_r in D; rewrite D; replace (16 * (dn / 16)) with ((4 * (dn / 16)) * 4) by lia; apply Z_mod_mult | clear - HcI C1; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK GBspan 0x83b38.
all: try (m_obl_cell HJ4 E924c E44 Hdn_in3 ltac:(idtac; first [clear - HcK C1; lia | clear - Hi1r Hrq4c; lia])).
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(fun nb => first [ m_awr_cell 924%nat E924c dn Adn Hdn_in3 ltac:(idtac; first [clear - HcK C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hi1r Hrq4c; lia end]) nb
| m_awr_cell 926%nat E926c dn Adn Hdn_in3 ltac:(idtac; first [clear - HcI C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hi1r Hrq4c; lia end]) nb ]).
m_run_keptG HFr AG (fun a : Z => (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ dn + 4 * k1 <= a < dn + 4 * k1 + 4 \/ dn + 4 * i1 <= a < dn + 4 * i1 + 4) Hceil Hslo FFS UN5.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rdn5 : ew Ev 626 = Z_to_bv 64 dn) by m_ewT;
assert (Ri5 : ew Ev 867 = Z_to_bv 64 i1) by m_ewT;
assert (E926e : ew Ev 926 = Z_to_bv 64 (dn + 4 * i1)) by m_ewT;
assert (HUB : U Ev (SAlu ALU_ADD (SOff 626 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 867 0) (SLit 32)) (SLit 30))) = U Ev (SOff 926 0)) end.
{ lazymatch goal with |- U ?Ev _ = _ =>
rewrite (U_atom Ev 926 (dn + 4 * i1) E926e) by (clear - HcI C1; lia);
apply (m_U_elem4 Ev 626 dn (SOff 867 0) i1);
[ exact Rdn5 | clear - Hdn4096; lia | clear - HcI C1; lia
| apply (U_atom Ev 867 i1 Ri5); clear - Hi1r HcntT HT24; lia
| clear - Hi1r HcntT HT24; lia ] end. }
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (11%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (11%bv : bv 5) (SOff 926 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (11%bv : bv 5) HS); change (sv_denot Ev (SOff 926 0) = sv_denot Ev e);
apply U_inj; symmetry; exact HUB)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
set (va := tn_addr tn) in *.
assert (Hva_l : In (va, NODE_SIZE) lrest) by (exact (Hnode_l _ (Htns_in q Hq_t))).
assert (Hva_in3 : In (va, NODE_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hva_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ va NODE_SIZE HAR3 Hva_in3) as (Hva4096 & Hvazone & Hvaceil & Hva16). change (req_size NODE_SIZE) with 56 in Hvazone, Hvaceil.
assert (Hva_rng : 0 <= va < 2 ^ 64) by (clear - Hva4096 Hvaceil C1; lia).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ va NODE_SIZE 7 fpos HAR3 Hva_in3 Hfin3) as HdF_va.
unfold zdisjoint in HdF_va. cbn [fst snd] in HdF_va. change (fs_frame_bytes 7) with 8192 in HdF_va. change (req_size NODE_SIZE) with 56 in HdF_va. rewrite EFA3 in HdF_va. fold F in HdF_va.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ va NODE_SIZE cid pos HAR3 Hva_in3 HfinS3) as HdC_va.
unfold zdisjoint in HdC_va. cbn [fst snd] in HdC_va. change (req_size NODE_SIZE) with 56 in HdC_va. rewrite EFA3 in HdC_va.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (va, NODE_SIZE) HAR3 HPrt3 ltac:(right; exact Hva_l)) as HzR_va.
unfold zdisjoint, block_rng in HzR_va. cbn [fst snd] in HzR_va. change (req_size RGB_SIZE) with 64 in HzR_va. change (req_size NODE_SIZE) with 56 in HzR_va.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (va, NODE_SIZE) HAR3 HPtb3 ltac:(right; exact Hva_l)) as HzT_va.
unfold zdisjoint, block_rng in HzT_va. cbn [fst snd] in HzT_va. change (req_size 48) with 48 in HzT_va. change (req_size NODE_SIZE) with 56 in HzT_va.
pose proof (Hs_dn q Hq_t) as Hsd_va. pose proof (Hs_pn q Hq_t) as Hsp_va. fold tn va in Hsd_va, Hsp_va.
pose proof (proj1 (proj2 (proj2 HCLmA)) q Hq_t) as Hnm. unfold node_mem in Hnm. cbn [c_ns] in Hnm. fold ns nd tn in Hnm.
assert (Hleaf : n_leaf nd = true) by (apply (cinv_unprocessed_leaf cnt ent st Hcinv q); fold q ns; clear - Hq0n Hqlt; lia).
rewrite Hleaf in Hnm. destruct Hnm as (c0 & c1 & Hobj).
destruct (Hmatch q Hq_t) as (_ & _ & _ & Mwf & _). fold tn ns nd in Mwf.
destruct (m_node_fields _ _ c0 c1 tn 1 (proj1 (proj2 (proj2 (proj2 (proj2 Mwf))))) Hobj) as (_ & _ & _ & (Vcut0 & Rcut) & _).
fold va cut in Vcut0, Rcut.
assert (Hcut : 0 <= cut <= 2) by (exact (proj1 Mwf)).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Vcut : val_mem trbsegs (mrestrict (w_H W3) (ms_mem msX)) (va + 48) 1 cut) end.
{ apply (YI0d.val_mem_kept trbsegs _ _ _ _ _ Vcut0). intros a Ha. apply (mbyte_of_aview trbsegs).
destruct (Hoff3 _ _ Hva_l a ltac:(change (req_size NODE_SIZE) with 56; clear - Ha; lia)) as (Hq1 & Hq2).
assert (Hq3 : ~ ((alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ dn + 4 * k1 <= a < dn + 4 * k1 + 4 \/ dn + 4 * i1 <= a < dn + 4 * i1 + 4))
by (clear - Hq2 Ha Hsd_va Hrq4c Hi1r; lia).
rewrite (UN5 _ Hq1 Hq3).
apply KEEP2; [clear - Ha Hva4096 Hvaceil; lia | clear - Hq2; tauto | clear - Ha Hsp_va Hrq3T Hi1r; lia | clear - Ha Hsp_va Hrq3T Hi1r; lia]. }
idtac "OK-VCUT".
assert (Hvai : va + 56 <= 65536 \/ 6156288 <= va) by (clear - Hvazone; lia).
assert (Hvaz : va + 56 <= 2147446784 \/ 17594333495296 <= va) by (clear - Hvazone; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E821c : ew Ev 821 = Z_to_bv 64 va) by m_ewT;
assert (E824c : ew Ev 824 = Z_to_bv 64 cut) by m_ewT;
assert (E924n : ew Ev 924 = Z_to_bv 64 (dn + 4 * k1)) by m_ewT;
assert (E926n : ew Ev 926 = Z_to_bv 64 (dn + 4 * i1)) by m_ewT;
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 821%nat) 0 56 0 0 [YQ0b.mkChunk 48 (CVal 1 (SOff 824 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E821c, unsigned_lit_small by exact Hva_rng;
split; [clear - Hva4096; lia|]; split; [clear - Hvaceil C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ va 48 1 (SOff 824 0) cut);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E824c | clear - Hcut; lia | cbn; clear; lia | exact Vcut] | apply Forall_nil] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite ?E924n, ?E926n, ?(unsigned_lit_small (dn + 4 * k1)), ?(unsigned_lit_small (dn + 4 * i1)) by (clear - HcK HcI C1; lia);
ga_evalE0 AG; repeat split;
first [ clear - Hva4096 Hvaceil Hceil Hslo FFS; lia
| clear - Hvaz HF8lo HF8hi HFq HF8 HFceil C1; unfold SB in *; lia
| clear - Hvai; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_va; lia
| clear - HdC_va Hflo Hfhi; lia
| clear - HzR_va; lia
| clear - HzT_va; lia
| clear - Hsd_va Hi1r Hrq4c; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
idtac "OK-NODEREG".
gboxh Hvai. gboxh Hvaz. gboxh HdF_va. gboxh HdC_va. gboxh HzR_va. gboxh HzT_va. gboxh Hvazone. gboxh Hsd_va. gboxh Hsp_va.
unfold NODE_SIZE in Hva_in3.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HUppq : U Ev (SOff 618 0) = pp) by (apply (U_atom Ev 618 pp); [m_ewT | clear - Hpp4096 Hppceil Hrq3T C1; lia]);
assert (HUnx : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SExt false 8 (SOff 824 0)) (SOff 870 0)) (SLit 32)) (SLit 32)) = cut + 3 * i1)
by (apply U_zext32_shifts; [apply U_add_small_q; [apply (c_Uz8 Ev 824 cut E824c); clear - Hcut; lia | apply (U_atom Ev 870 (3 * i1)); [m_ewT | clear - Hi1r HcntT HT24; lia]
| clear - Hcut; lia | clear - Hi1r; lia | clear - Hcut Hi1r HcntT HT24; lia]
| clear - Hcut Hi1r HcntT HT24; lia]) end.
m_add_cond HS BC_GEU (SAlu ALU_XOR (SOff 618 0) (SLit (-1))) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SExt false 8 (SOff 824 0)) (SOff 870 0)) (SLit 32)) (SLit 32))
ltac:(eapply (ub_room_cond _ _ _ pp (cut + 3 * i1) HUppq HUnx); clear - Hpp4096 Hppceil Hrq3T C1 Hi1r HcntT HT24 Hcut; lia).
clear HUppq HUnx.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK GBspan 0x839b8.
all: try (m_obl_cell HJ4 E924c E44 Hdn_in3 ltac:(idtac; first [clear - HcK C1; lia | clear - Hi1r Hrq4c; lia])).
all: try (m_obl_cell HJ4 E926c E44 Hdn_in3 ltac:(idtac; first [clear - HcI C1; lia | clear - Hi1r Hrq4c; lia])).
1: { lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 821 48)) ?len =>
rewrite (U_atom_off Ex 821 va 48) by first [exact E821c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E821c | exact Hva_rng | clear - Hva4096 Hvaceil C1; lia];
eapply (obl_of_block trbsegs _ LAWS _ _ _ _ _ Ex (SOff bx 0) _ len va 56 (proj1 HJ4) Hva_in3);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear; lia | change (req_size 56) with 56; clear; lia ] end. }
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(fun nb => first [ m_awr_cell 924%nat E924c dn Adn Hdn_in3 ltac:(idtac; first [clear - HcK C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hi1r Hrq4c; lia end]) nb
| m_awr_cell 926%nat E926c dn Adn Hdn_in3 ltac:(idtac; first [clear - HcI C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hi1r Hrq4c; lia end]) nb ]).
m_run_keptG HFr AG (fun a : Z => (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ dn + 4 * k1 <= a < dn + 4 * k1 + 4 \/ dn + 4 * i1 <= a < dn + 4 * i1 + 4) Hceil Hslo FFS UN6.
clear HF HFr HG.
norm_ss HS.
assert (Hfk32 : 0 <= fk < 2 ^ 32) by (exact Rfk). assert (Hfi32 : 0 <= fi < 2 ^ 32) by (exact Rfi).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HB924 : bv_unsigned (ew Ex 924) = dn + 4 * k1) by (rewrite ?ew_ewset_other by lia; rewrite E924c; apply unsigned_lit_small; clear - HcK C1; lia);
assert (HB926 : bv_unsigned (ew Ex 926) = dn + 4 * i1) by (rewrite ?ew_ewset_other by lia; rewrite E926c; apply unsigned_lit_small; clear - HcI C1; lia);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 2 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 924%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 924 (dn + 4 * k1) cs lo hi wlo whi 0 4%N (SExt true 32 (SOff 927 0)) HRc HB924 ltac:(cbn; tauto) ltac:(cbn; lia)) as VnewK;
change (bv_unsigned (sv_denot Ex (SExt true 32 (SOff 927 0)))) with (U Ex (SExt true 32 (SOff 927 0))) in VnewK; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in VnewK;
rewrite (U_sext32_low Ex 927 fi ltac:(rewrite ?ew_ewset_other by lia; exact E927) Hfi32) in VnewK
end; clear HRc;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 1 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 926%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 926 (dn + 4 * i1) cs lo hi wlo whi 0 4%N (SExt true 32 (SOff 925 0)) HRc HB926 ltac:(cbn; tauto) ltac:(cbn; lia)) as VnewI;
change (bv_unsigned (sv_denot Ex (SExt true 32 (SOff 925 0)))) with (U Ex (SExt true 32 (SOff 925 0))) in VnewI; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in VnewI;
rewrite (U_sext32_low Ex 925 fk ltac:(rewrite ?ew_ewset_other by lia; exact E925) Hfk32) in VnewI
end; clear HRc end.
rewrite Z.add_0_r in VnewK, VnewI. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in VnewK, VnewI.
assert (MV1 : forall (m0 : word -> option byte) a v, val_mem trbsegs m0 a 1 v -> 0 <= v < 256 -> mbyte trbsegs m0 a = Some (Z_to_bv 8 v)).
{ intros m0 a v Hv0 Hv. specialize (Hv0 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0. rewrite Hv0. f_equal. f_equal.
unfold YP0g.le_byte. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. reflexivity. }
assert (KEEP5 : forall a, 0 <= a < alloc_ceiling -> ~ ((F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (dn + 4 * k1 <= a < dn + 4 * k1 + 4) -> ~ (dn + 4 * i1 <= a < dn + 4 * i1 + 4) ->
aview trbsegs (w_H W3) (ms_mem ms4) a = aview trbsegs (w_H W3) (ms_mem ms1) a).
{ intros a Ha Hx Hn1 Hn2.
assert (Hq1 : 0 <= a < 2 ^ 64) by (clear - Ha C1; lia).
assert (Hq2 : ~ ((alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ dn + 4 * k1 <= a < dn + 4 * k1 + 4 \/ dn + 4 * i1 <= a < dn + 4 * i1 + 4))
by (clear - Ha Hx Hn1 Hn2; lia).
rewrite (UN6 _ Hq1 Hq2). exact (UN5 _ Hq1 Hq2). }
assert (Hdense5 : arr32 trbsegs (mrestrict (w_H W3) (ms_mem ms4)) dn (fr_vals (eswap dentry El i1 k1))).
{ apply (arr32_eswap trbsegs _ _ dn El i1 k1 Hdense2); [rewrite HlenEl; clear - Hi1r; lia | rewrite HlenEl; clear - Hi1r; lia | exact Hlt1 | | exact VnewI | exact VnewK].
intros x Hx Hn1 Hn2. rewrite HlenEl in Hx. apply (mbyte_of_aview trbsegs).
destruct (Hoff3 dn _ Hdn_l (dn + x) ltac:(clear - Hx Hrq4c; lia)) as (Hq1 & Hq2).
apply KEEP5; [clear - Hx Hdn4096 Hdnceil Hrq4c; lia | clear - Hq2; tauto | clear - Hn2; lia | clear - Hn1; lia]. }
assert (HEokl : ent_ok El) by (exact (ent_ok_perm _ _ PIperm (ent_ok_perm _ _ HpermE HentOk))).
pose proof (proj1 HCLmA) as CPA. cbn [c_E] in CPA. fold palc in CPA.
assert (Hq2pp : forall x, 0 <= x < 3 * T -> 0 <= pp + x < alloc_ceiling /\ ~ ((F <= pp + x < F + 32 \/ F + 5152 <= pp + x < F + 8192) \/ r <= pp + x < r + 64 \/ tb <= pp + x < tb + 48) /\
~ (dn + 4 * k1 <= pp + x < dn + 4 * k1 + 4) /\ ~ (dn + 4 * i1 <= pp + x < dn + 4 * i1 + 4)).
{ intros x Hx. destruct (Hoff3 pp _ Hpp_l (pp + x) ltac:(clear - Hx Hrq3T; lia)) as (Hq1 & Hq2).
split; [clear - Hx Hpp4096 Hppceil Hrq3T; lia|]. split; [clear - Hq2; tauto|]. split; clear - Hx Hs_pd Hrq3T Hrq4c Hi1r; lia. }
assert (Hgz : forall x, 0 <= x < 3 * cnt -> getz palc x = getz (pal_bytes El) x).
{ intros x Hx. subst palc. apply getz_app_l. rewrite zlen_pal_bytes, HlenEl. exact Hx. }
assert (Hpal5 : arr8 trbsegs (mrestrict (w_H W3) (ms_mem ms4)) pp (pal_bytes (eswap dentry El i1 k1) ++ tail)).
{ apply (arr8_eswap trbsegs _ _ pp El tail i1 k1 CPA HEokl); [rewrite HlenEl; clear - Hi1r; lia | rewrite HlenEl; clear - Hi1r; lia | exact Hlt1 | | | ].
- intros x Hx Hn1 Hn2. rewrite HlenEl in Hx. apply (mbyte_of_aview trbsegs).
destruct (Hq2pp x ltac:(clear - Hx Htail; lia)) as (Q1 & Q2 & Q3 & Q4).
rewrite (KEEP5 _ Q1 Q2 Q3 Q4). apply (KEEP2 _ Q1 Q2); [clear - Hn1; lia | clear - Hn2; lia].
- intros d Hd3b.
destruct (Hq2pp (3 * i1 + d) ltac:(clear - Hd3b Hi1r; lia)) as (Q1 & Q2 & Q3 & Q4).
assert (Hq1 : 0 <= pp + (3 * i1 + d) < 2 ^ 64) by (clear - Q1 C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= pp + (3 * i1 + d) \/ (F <= pp + (3 * i1 + d) < F + 32 \/ F + 5152 <= pp + (3 * i1 + d) < F + 8192) \/ r <= pp + (3 * i1 + d) < r + 64 \/ tb <= pp + (3 * i1 + d) < tb + 48)) by (clear - Q1 Q2; lia).
destruct (arr8_getz trbsegs _ pp palc (3 * k1 + d) CPA ltac:(rewrite Hzl; clear - Hd3b Hi1r; lia)) as [Hbyte _].
rewrite (Hgz (3 * k1 + d) ltac:(clear - Hd3b Hi1r; lia)) in Hbyte.
replace (pp + 3 * i1 + d) with (pp + (3 * i1 + d)) by (clear; lia).
apply (MBA (ms_mem ms) (ms_mem ms4) _ (pp + (3 * k1 + d))); [|exact Hbyte].
rewrite (KEEP5 _ Q1 Q2 Q3 Q4), (UN4 _ Hq1 Hq2).
rewrite (Hfr5b _ Hq1 ltac:(rewrite Hes; clear - Q1 Hd3b Hlt1 Hceil Hslo FFS; lia)).
rewrite (UN3 _ Hq1 Hq2).
replace (pp + (3 * i1 + d)) with (pp + 3 * i1 + d) by (clear; lia). replace (pp + (3 * k1 + d)) with (pp + 3 * k1 + d) by (clear; lia). exact (Heff5 d Hd3b).
- intros d Hd3b.
destruct (Hq2pp (3 * k1 + d) ltac:(clear - Hd3b Hi1r; lia)) as (Q1 & Q2 & Q3 & Q4).
assert (Hq1 : 0 <= pp + (3 * k1 + d) < 2 ^ 64) by (clear - Q1 C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= pp + (3 * k1 + d) \/ (F <= pp + (3 * k1 + d) < F + 32 \/ F + 5152 <= pp + (3 * k1 + d) < F + 8192) \/ r <= pp + (3 * k1 + d) < r + 64 \/ tb <= pp + (3 * k1 + d) < tb + 48)) by (clear - Q1 Q2; lia).
assert (Hbyte : mbyte trbsegs (mrestrict (w_H W3) (ms_mem ms0)) (spZ regs + -131 + d) = Some (Z_to_bv 8 (getz (pal_bytes El) (3 * i1 + d)))).
{ rewrite <- (Hgz (3 * i1 + d) ltac:(clear - Hd3b Hi1r; lia)).
assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by (clear - Hd3b; lia). destruct Hd3 as [-> | [-> | ->]].
- replace (spZ regs + -131 + 0) with (spZ regs + -131) by (clear; lia). exact (MV1 _ _ _ Wt0 Rt0).
- replace (spZ regs + -131 + 1) with (spZ regs + -130) by (clear; lia). exact (MV1 _ _ _ Wt1 Rt1).
- replace (spZ regs + -131 + 2) with (spZ regs + -129) by (clear; lia). exact (MV1 _ _ _ Wt2 Rt2). }
replace (pp + 3 * k1 + d) with (pp + (3 * k1 + d)) by (clear; lia).
apply (MBA (ms_mem ms0) (ms_mem ms4) _ (spZ regs + -131 + d)); [|exact Hbyte].
rewrite (KEEP5 _ Q1 Q2 Q3 Q4), (UN4 _ Hq1 Hq2).
replace (pp + (3 * k1 + d)) with (pp + 3 * k1 + d) by (clear; lia). exact (Heff4 d Hd3b). }
assert (HCLmZ : m_CLmem (w_H W3) (ms_mem ms4) pp dn F tail (mkC (eswap dentry El i1 k1) (c_ns st) (c_q st)) tns).
{ split; [exact Hpal5|]. split; [exact Hdense5|]. split.
- intros j Hj. apply (node_mem_frame trbsegs _ _ _ _ j (proj1 (proj2 (proj2 HCLmA)) j Hj)). intros i Hi. apply (mbyte_of_aview trbsegs).
destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ _ NODE_SIZE HAR3 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact (Hnode_l _ (Htns_in j Hj))])) as (Hn4096 & _ & Hnceil & _).
change (req_size NODE_SIZE) with 56 in Hnceil. unfold NODE_SIZE in Hi.
pose proof (Hs_pn j Hj) as Hsp1. pose proof (Hs_dn j Hj) as Hsd1.
assert (Q1 : 0 <= tn_addr (tnth tns j) + i < alloc_ceiling) by (clear - Hi Hn4096 Hnceil; lia).
assert (Q2 : ~ ((F <= tn_addr (tnth tns j) + i < F + 32 \/ F + 5152 <= tn_addr (tnth tns j) + i < F + 8192) \/ r <= tn_addr (tnth tns j) + i < r + 64 \/ tb <= tn_addr (tnth tns j) + i < tb + 48)) by (clear - Hq2; tauto).
rewrite (KEEP5 _ Q1 Q2 ltac:(clear - Hi Hsd1 Hrq4c Hi1r; lia) ltac:(clear - Hi Hsd1 Hrq4c Hi1r; lia)).
apply (KEEP2 _ Q1 Q2); clear - Hi Hsp1 Hrq3T Hi1r; lia.
- intros j Hj. apply (rg_val_mem_blk_kept (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms4) (F + 32) (8 * elen tns) _ 8 _ (proj2 (proj2 (proj2 HCLmA)) j Hj)); [| clear - Hj; lia | cbn; clear - Hj; lia].
intros i Hi.
assert (Q1 : 0 <= F + 32 + i < alloc_ceiling) by (clear - Hi Hntns HF4096 HFceil; lia).
assert (Q2 : ~ ((F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48)) by (clear - Hi Hntns HdF_r HdF_tb; lia).
rewrite (KEEP5 _ Q1 Q2 ltac:(clear - Hi Hntns HdF_dn Hrq4c Hi1r; lia) ltac:(clear - Hi Hntns HdF_dn Hrq4c Hi1r; lia)).
apply (KEEP2 _ Q1 Q2); clear - Hi Hntns HdF_pp Hrq3T Hi1r; lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rk6 : ew Ex 869 = Z_to_bv 64 k1) by m_ewT; assert (Ri6 : ew Ex 867 = Z_to_bv 64 i1) by m_ewT end.
rregU HS (21%bv : bv 5) k1 ltac:(apply (U_atom _ 869 k1 Rk6); clear - Hi1r HcntT HT24; lia) Q21.
rregU HS (18%bv : bv 5) i1 ltac:(apply (U_atom _ 867 i1 Ri6); clear - Hi1r HcntT HT24; lia) Q18.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rs86 : ew Ex 870 = Z_to_bv 64 (3 * i1)) by m_ewT; assert (Rc6 : ew Ex 824 = Z_to_bv 64 cut) by m_ewT end.
assert (Hi29 : 0 <= i1 < 2 ^ 29) by (clear - Hi1r HcntT HT24; lia).
assert (Rcut8 : 0 <= cut < 256) by (clear - Hcut; lia).
ga_join HS ss_PL2 2102%nat rga_deads_PL2
ltac:(idtac; ga_join_val HS 2102%nat 15%nat Q21 E2117; ga_join_val HS 2102%nat 16%nat Q18 E2118;
c_pin HS (24%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 2118 0) (SLit 1)) (SOff 2118 0))
ltac:(apply U_inj; transitivity (3 * i1);
[ apply c_U3x; [apply (U_atom _ 2118 _ E2118); clear - Hi29; lia | exact Hi29]
| symmetry; apply (U_atom _ 870 (3 * i1)); [rewrite ew_havoc_old by lia; exact Rs86 | clear - Hi29; lia] ]);
c_pin HS (11%bv : bv 5) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 2118 0) (SLit 1)) (SOff 2118 0)) (SExt false 8 (SOff 824 0))) (SLit 32)) (SLit 32))
ltac:(apply U_inj; transitivity (3 * i1 + cut);
[ apply c_Uoff; [apply c_U3x; [apply (U_atom _ 2118 _ E2118); clear - Hi29; lia | exact Hi29] | apply (c_Uz8 _ 824 cut); [rewrite ew_havoc_old by lia; exact Rc6 | exact Rcut8] | clear - Hi29; lia | exact Rcut8]
| symmetry; rewrite (Z.add_comm (3 * i1) cut); apply U_zext32_shifts;
[ apply U_add_small_q; [apply (c_Uz8 _ 824 cut); [rewrite ew_havoc_old by lia; exact Rc6 | exact Rcut8] | apply (U_atom _ 870 (3 * i1)); [rewrite ew_havoc_old by lia; exact Rs86 | clear - Hi29; lia]
| clear - Rcut8; lia | clear - Hi29; lia | clear - Rcut8 Hi29; lia]
| clear - Rcut8 Hi29; lia ] ])).
idtac "OK-JOIN-A".
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (Rc7 : ew Ex 824 = Z_to_bv 64 cut) by m_ewT end.
m_join_win HS ss_PL 842%nat rga_deads_PL
ltac:(idtac; ga_join_val HS 842%nat 15%nat Q21 N857; ga_join_val HS 842%nat 16%nat Q18 N858;
c_pin HS (24%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 858 0) (SLit 1)) (SOff 858 0))
ltac:(apply U_inj; transitivity (3 * i1);
[ apply c_U3x; [apply (U_atom _ 858 _ N858); clear - Hi29; lia | exact Hi29]
| symmetry; apply c_U3x; [apply (U_atom _ 2118 i1); [rewrite YCft.ew_havoc_above by (cbn [length]; lia); exact E2118 | clear - Hi29; lia] | exact Hi29] ]);
c_pin HS (11%bv : bv 5) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 858 0) (SLit 1)) (SOff 858 0)) (SExt false 8 (SOff 824 0))) (SLit 32)) (SLit 32))
ltac:(apply U_inj; transitivity (3 * i1 + cut);
[ apply c_Uoff; [apply c_U3x; [apply (U_atom _ 858 _ N858); clear - Hi29; lia | exact Hi29] | apply (c_Uz8 _ 824 cut); [rewrite ew_havoc_old by lia; exact Rc7 | exact Rcut8] | clear - Hi29; lia | exact Rcut8]
| symmetry; apply c_Uoff; [apply c_U3x; [apply (U_atom _ 2118 i1); [rewrite YCft.ew_havoc_above by (cbn [length]; lia); exact E2118 | clear - Hi29; lia] | exact Hi29] | apply (c_Uz8 _ 824 cut); [rewrite ew_havoc_old by lia; exact Rc7 | exact Rcut8] | clear - Hi29; lia | exact Rcut8] ])).
idtac "OK-JOIN-B".
m_hand_ih IH HS HJ4 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns, (eswap dentry El i1 k1), i1, k1.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact HCLmZ|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exact Hmeas|].
split; [exact Hqlt|].
split; [exact Hlt|].
split; [m_ewT|].
split; [exact N857|]. split; [exact N858|].
split; [fold q tn cut; m_ewT|].
cbv zeta. fold q ns nd tn cut lo hi sg P. split; [exact PI1 | exact Hpm1].
Qed.
End f.
End c.

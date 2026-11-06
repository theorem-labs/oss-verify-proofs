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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCnw YCme YCob YCny.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YCj8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqj.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_PL1 : forall n pm, rga_fromA B ss_ST (fun _ => INV_ST B n) -> rga_fromA B ss_PW1 (fun _ => INV_PW B n pm) -> rga_from B ss_PL (INV_PL B n (S pm)).
Proof.
intros n pm RST RPW.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & El & ix & kx & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HCLm & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & R818 & Hmeas & Hqlt & Hlt & R821 & R857 & R858 & R824 & HPIm).
destruct Hk0 as [Hk0 Hbud].
unfold ss_PL in HS.
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
destruct (Hmatch q Hq_t) as (Mlo & Mhi & Mcol & Mwf & Mnz). fold tn ns nd in Mlo, Mhi, Mcol, Mwf, Mnz.
destruct (cinv_node cnt ent st Hcinv q ltac:(fold ns; clear - Hq0n Hqlt; lia)) as (Hnlo & Hnhi & _). fold ns nd in Hnlo, Hnhi.
cbv zeta in HPIm. fold q ns nd tn in HPIm.
set (cut := tn_cut tn) in *. set (lo := n_lo nd) in *. set (hi := n_hi nd) in *.
set (sg := dseg cut (c_E st) lo hi) in *. set (P := Ptest cut (wsum sg) (wdot sg)) in *.
destruct HPIm as (HPI & Hpm).
pose proof HPI as (PIik & PIk & _ & PIhi & PIlen & PIperm & _).
assert (HlenEl : elen El = cnt) by (unfold elen in *; rewrite PIlen; exact Hlen_E).
assert (Hzl : zlen (pal_bytes El ++ tail) = 3 * T)
by (unfold zlen; rewrite length_app, Nat2Z.inj_add; change (Z.of_nat (length (pal_bytes El))) with (zlen (pal_bytes El)); change (Z.of_nat (length tail)) with (zlen tail);
rewrite zlen_pal_bytes, HlenEl; clear - Htail; lia).
destruct (part_round_spec dentry P lo hi (c_E st) El ix kx HPI) as (i1 & k1 & _ & _ & Hi1 & Hk1 & Sbig & Ssmall & Sup & Sdn & Hcase).
assert (Hcut : 0 <= cut <= 2) by (exact (proj1 Mwf)).
assert (Hpt : forall x, 0 <= x < cnt -> ptest (pal_bytes El ++ tail) cut (wsum sg) (wdot sg) x = smallb dentry P El x).
{ intros x Hx. symmetry. apply smallb_ptest; [apply pal_agrees_app | clear - Hcut; lia | rewrite HlenEl; exact Hx]. }
assert (Hseg : zsub (c_E st) lo hi = n_seg nd) by (apply (cinv_seg cnt ent st Hcinv q); fold q ns; clear - Hq0n Hqlt; lia).
assert (Hquot : is_quot (nth (Z.to_nat cut) (tn_mean tn) 0) (wdot sg) (wsum sg)).
{ subst sg. rewrite dseg_segd, Hseg. apply (proj1 (Hfacts q ltac:(fold q; clear - Hq_t; lia))). exact Hcut. }
destruct HCLm as (CA1 & CA2 & CA3 & CA4). cbn [c_E c_ns] in CA1, CA2, CA3.
pose proof (CA3 q Hq_t) as Hnm. unfold node_mem in Hnm. fold ns nd tn in Hnm.
assert (Hleaf : n_leaf nd = true) by (apply (cinv_unprocessed_leaf cnt ent st Hcinv q); fold q ns; clear - Hq0n Hqlt; lia).
rewrite Hleaf in Hnm. destruct Hnm as (c0 & c1 & Hobj).
set (va := tn_addr tn) in *.
assert (Hva_l : In (va, NODE_SIZE) lrest) by (exact (Hnode_l _ (Htns_in q Hq_t))).
assert (Hva_in3 : In (va, NODE_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hva_l]).
assert (Hpp_in3 : In (pp, 3 * T) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hpp_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ va NODE_SIZE HAR3 Hva_in3) as (Hva4096 & Hvazone & Hvaceil & Hva16). change (req_size NODE_SIZE) with 56 in Hvazone, Hvaceil.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * T) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq3T.
assert (Hva_rng : 0 <= va < 2 ^ 64) by (clear - Hva4096 Hvaceil C1; lia).
assert (HB2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
pose proof (st_ok_region_nth E _ (restrict (w_H W3) ms3) 8 _ HS eq_refl) as HRc. cbn [ms_mem restrict] in HRc.
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region E _ 2 (spZ regs) cs lo hi wlo whi (-168) 8%N (SOff 821 16) (va + 16) HRc HB2 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite R821, unsigned_lit_small by exact Hva_rng; reflexivity) ltac:(cbn; clear - Hva4096 Hvaceil C1; lia) ltac:(cbn; lia)) as V408
end; clear HRc.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V408.
destruct (m_node_fields _ _ c0 c1 tn 1 (proj1 (proj2 (proj2 (proj2 (proj2 Mwf))))) Hobj) as (Vmean & _).
destruct (Vmean cut Hcut) as (Vmc & Rmc). fold va in Vmc.
assert (Hix29 : 0 <= ix < 2 ^ 29 /\ 0 <= kx < 2 ^ 29) by (clear - PIik PIk Hnlo Hnhi HcntT HT24; lia).
assert (Rcut8 : 0 <= cut < 256) by (clear - Hcut; lia).
rregU HS (9%bv : bv 5) (spZ regs + -576) ltac:(rewrite (U_atom_off _ 2 (spZ regs) (-576)) by first [exact HB2 | rewrite (AG 2%nat) by lia; rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned | clear - Hceil Hslo Hshi H47 FFS C1; lia]; reflexivity) G9.
rregU HS (18%bv : bv 5) ix ltac:(apply (U_atom _ 858 ix R858); clear - Hix29; lia) G18.
rregU HS (21%bv : bv 5) kx ltac:(apply (U_atom _ 857 kx R857); clear - Hix29; lia) G21.
rregU HS (24%bv : bv 5) (3 * ix) ltac:(apply c_U3x; [apply (U_atom _ 858 ix R858); clear - Hix29; lia | exact (proj1 Hix29)]) G24.
rregU HS (12%bv : bv 5) cut ltac:(apply (c_Uz8 _ 824 cut R824 Rcut8)) G12.
rregU HS (11%bv : bv 5) (cut + 3 * ix) ltac:(rewrite (Z.add_comm cut (3 * ix)); apply c_Uoff; [apply c_U3x; [apply (U_atom _ 858 ix R858); clear - Hix29; lia | exact (proj1 Hix29)] | apply (c_Uz8 _ 824 cut R824 Rcut8) | clear - Hix29; lia | exact Rcut8]) G11.
rregU HS (25%bv : bv 5) (2 ^ 64 - 1 - (va + 16)) ltac:(apply (YCfp.U_not_gen _ (SOff 821 16) (va + 16)); [apply (U_atom_off _ 821 va 16 R821); [exact Hva_rng | clear - Hva4096 Hvaceil C1; lia] | clear - Hva4096 Hvaceil C1; lia]) G25.
rregU HS (5%bv : bv 5) 2 ltac:(reflexivity) G5.
rregU HS (26%bv : bv 5) pp ltac:(apply (U_atom _ 618 pp Rpp); clear - Hpp4096 Hppceil Hrq3T C1; lia) G26.
rregU HS (23%bv : bv 5) (2 ^ 64 - 1 - pp) ltac:(apply (YCfp.U_not_gen _ (SOff 618 0) pp); [apply (U_atom _ 618 pp Rpp); clear - Hpp4096 Hppceil Hrq3T C1; lia | clear - Hpp4096 Hppceil Hrq3T C1; lia]) G23.
rregU HS (27%bv : bv 5) SB ltac:(apply (U_atom _ 44 SB E44); unfold SB; clear; lia) G27.
change (N.to_nat 8) with 8%nat in V408.
assert (Hb1 : lo <= i1 <= hi /\ lo <= k1 <= hi /\ 0 <= lo /\ hi < cnt) by (clear - Hi1 Hk1 PIik PIk Hnlo Hnhi; lia).
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 539064) with (Z_to_bv 64 LCP_HEAD).
eapply SRr_bind.
{ eapply (rga_lcr_part B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 pp (3 * T) pp (pal_bytes El ++ tail)
(spZ regs + -576) va cut (nth (Z.to_nat cut) (tn_mean tn) 0) (wsum sg) (wdot sg) ix kx i1 k1 (2 ^ 64 - 1 - (va + 16)) fx (ms_regs ms3) (ms_mem ms3) _ HJ3 Hfrm).
- change TRGBADD_STK with 25152. clear. lia.
- clear. lia.
- exact Hva_in3.
- exact Hpp_in3.
- clear. lia.
- rewrite Hzl. clear. lia.
- intros Heq. injection Heq as _ H3T. unfold NODE_SIZE in H3T. clear - H3T. lia.
- exact Hcut.
- exact Rmc.
- exact Hquot.
- replace (spZ regs + -576 + 408) with (spZ regs + -168) by (clear; lia). exact V408.
- exact Vmc.
- exact CA1.
- clear - Hi1 PIik Hnlo. lia.
- clear - Hb1 HcntT HT24. lia.
- rewrite Hzl. clear - Hb1 HcntT Hcut. lia.
- intros z Hz. rewrite (Hpt z ltac:(clear - Hz Hb1 PIik; lia)). apply Sup. exact Hz.
- rewrite (Hpt i1 ltac:(clear - Hb1; lia)). exact Sbig.
- clear - Hk1 Hb1. lia.
- clear - PIk Hnhi HcntT HT24. lia.
- rewrite Hzl. clear - PIk Hnhi HcntT Hcut. lia.
- intros z Hz. rewrite (Hpt z ltac:(clear - Hz Hb1 PIk Hnhi; lia)). apply Sdn. exact Hz.
- rewrite (Hpt k1 ltac:(clear - Hb1; lia)). exact Ssmall.
- exact G9.
- exact G11.
- exact G12.
- exact G18.
- exact G24.
- exact G21.
- exact G25.
- clear - Hva4096 Hvaceil C1. lia.
- exact G5.
- exact G26.
- exact G23.
- exact G27. }
cbv beta. intros W7 c7 _ (-> & fx7 & regs7 & mem7 & md7 & -> & Hfrm7 & HJ7 & HK7 & R18 & R21 & R13 & R24 & R20 & R12 & Hm7 & Hp7).
clear G9 G11 G12 G18 G24 G21 G25 G5 G26 G23 G27.
pose proof HJ7 as (HAR7 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 Hrin3) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 Htb_in3) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HWIN7 : forall a, 0 <= a < alloc_ceiling -> 0 <= a < 2 ^ 64) by (intros a Ha; clear - Ha C1; lia).
assert (HWST7 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> 0 <= a < 2 ^ 64) by (intros a Ha; clear - Ha Hceil Hslo Hshi H47 FFS C1; lia).
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
m_reseatF HS HJ7 fx7 regs7 LCP_CLOB 539312 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG HK7
ltac:(idtac; apply m_region_kept_ck_of_kept; [vm_compute; reflexivity|]; first
[ m_keptA Hm7 HWIN7 HWST7 HRNG7 HJ7 AG Usp RF E67 E10n E11n F HFpres7 Hrpres7
ltac:(idtac; first [ m_keptA_blk Hm7 HWIN7 AG 305%nat tb Rtb Htbpres7 HRtb7
| ga_kept_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
rreg HS (18%bv : bv 5) Rx18. cbn [ms_regs] in Rx18. rewrite R18 in Rx18. symmetry in Rx18. unfold w64 in Rx18.
rreg HS (21%bv : bv 5) Rx21. cbn [ms_regs] in Rx21. rewrite R21 in Rx21. symmetry in Rx21. unfold w64 in Rx21.
rreg HS (13%bv : bv 5) Rx13. cbn [ms_regs] in Rx13. rewrite R13 in Rx13. symmetry in Rx13. unfold w64 in Rx13.
rreg HS (24%bv : bv 5) Rx24. cbn [ms_regs] in Rx24. rewrite R24 in Rx24. symmetry in Rx24. unfold w64 in Rx24.
rreg HS (20%bv : bv 5) Rx20. cbn [ms_regs] in Rx20. rewrite R20 in Rx20. symmetry in Rx20. unfold w64 in Rx20.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
-
assert (Hdone : pdone dentry P lo hi (c_E st) El i1).
{ destruct Hcase as [(_ & _ & _ & Hdn0) | (Hlt1 & _)]; [exact Hdn0|]. exfalso.
rewrite YO3v.branch_geu_U in Hc. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc.
rewrite (U_atom _ 867 i1 Rx18), (U_atom _ 869 k1 Rx21) in Hc by (clear - Hb1 HcntT HT24; lia). clear - Hc Hlt1. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x83bd8.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HCLm7 : m_CLmem (w_H W3) (ms_mem msX) pp dn F tail (mkC El (c_ns st) (c_q st)) tns) end.
{ apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail (mkC El (c_ns st) (c_q st)) tns (conj CA1 (conj CA2 (conj CA3 CA4)))); cbn [c_E c_ns].
- intros i Hi. rewrite Hzl in Hi.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq3T; lia)) as (Hq1 & Hq2). rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1).
- intros i Hi. rewrite zlen_fr_vals, HlenEl in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1). }
ga_join HS ss_ST 871%nat (@nil (bv 5)) ltac:(idtac).
rga_hand RST HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns, El, i1.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact HCLm7|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exact Hmeas|].
split; [exact Hqlt|].
split; [exact Hlt|].
split; [m_ewT|].
split; [m_ewT|].
exists P. exact Hdone.
-
assert (Hsw : i1 < k1 /\ pinv dentry P lo hi (c_E st) (eswap dentry El i1 k1) i1 k1 /\ 0 <= part_meas dentry P (eswap dentry El i1 k1) i1 k1 < part_meas dentry P El ix kx).
{ destruct Hcase as [(Hle & _) | (Hlt1 & _ & PI1 & Hms1)]; [exfalso | exact (conj Hlt1 (conj PI1 Hms1))].
rewrite YO3v.branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc.
rewrite (U_atom _ 867 i1 Rx18), (U_atom _ 869 k1 Rx21) in Hc by (clear - Hb1 HcntT HT24; lia). clear - Hc Hle. lia. }
destruct Hsw as (Hlt1 & PI1 & Hms1).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HUppq : U Ev (SOff 618 0) = pp) by (apply (U_atom Ev 618 pp); [m_ewT | clear - Hpp4096 Hppceil Hrq3T C1; lia]);
assert (HUz3i : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SOff 862 0) (SLit 32)) (SLit 32)) = 3 * i1)
by (apply U_zext32_shifts; [apply (U_atom Ev 862 _ Rx13); clear - Hb1 HcntT HT24; lia | clear - Hb1 HcntT HT24; lia]) end.
m_add_cond HS BC_GEU (SAlu ALU_XOR (SOff 618 0) (SLit (-1))) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 862 0) (SLit 32)) (SLit 32))
ltac:(eapply (ub_room_cond _ _ _ pp (3 * i1) HUppq HUz3i); clear - Hpp4096 Hppceil Hrq3T C1 Hb1 HcntT HT24; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x52074.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
set (palc := pal_bytes El ++ tail) in *.
assert (HCLm8 : m_CLmem (w_H W3) (ms_mem ms) pp dn F tail (mkC El (c_ns st) (c_q st)) tns).
{ apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail (mkC El (c_ns st) (c_q st)) tns (conj CA1 (conj CA2 (conj CA3 CA4)))); cbn [c_E c_ns].
- intros i Hi. fold palc in Hi. rewrite Hzl in Hi.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq3T; lia)) as (Hq1 & Hq2). rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1).
- intros i Hi. rewrite zlen_fr_vals, HlenEl in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
rewrite (UN1 _ Hq1 Hq2). exact (Hm7 _ Hq1). }
ga_join HS ss_PW1 871%nat (@nil (bv 5)) ltac:(idtac).
rga_hand RPW HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns, El, i1, k1.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact HCLm8|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exact Hmeas|].
split; [exact Hqlt|].
split; [exact Hlt|].
split; [m_ewT|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [clear - Hb1; lia|]. split; [exact Hlt1|]. split; [clear - Hb1; lia|]. split; [exact HlenEl|]. split; [exact PIperm|].
cbv zeta. fold q ns nd tn cut lo hi sg P. split; [exact PI1|]. clear - Hms1 Hpm. lia.
Qed.
End d.
End c.

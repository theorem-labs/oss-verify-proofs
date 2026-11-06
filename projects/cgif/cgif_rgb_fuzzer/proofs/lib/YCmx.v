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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCop YCne YCng YCnh YCoc YCoe YCof.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YCj8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqk.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_ST3b1 : forall n, rga_from B ss_ST5 (INV_ST5 B n) -> rga_from B ss_ST4 (INV_ST4 B (S n)).
Proof.
intros n RST5.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & El & i1 & k0 & k1 & res0 & res1 & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HSTm & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & Hmeas & Hqlt & Hlt & R821 & R866 & R870 & R871 & R872 &
(P & Hdone) & Hres0nz & Hres1nz & R877 & R905 & R930 & Hkid0 & Hkid1).
destruct Hk0 as [Hk0 Hbud].
unfold ss_ST4 in HS.
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
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx T ++ [(dn, 4 * cnt)] ++ m_node_blocks (tns ++ k0 ++ k1)).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz ->
0 <= a < 2 ^ 64 /\ ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq.
destruct Hq as [Hq1 Hq2]. split; [exact Hq1|]. intros Hc. apply Hq2. unfold m_ZsP. clear - Hc. lia. }
assert (Hpp_l : In (pp, 3 * T) lrest) by (subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); left; cbn [cht_blocks In]; tauto).
assert (Hdn_l : In (dn, 4 * cnt) lrest) by (subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); right; left; reflexivity).
assert (Hnode_lx : forall t, In t (tns ++ k0 ++ k1) -> In (tn_addr t, NODE_SIZE) lrest)
by (intros t Ht; subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); right; right; unfold m_node_blocks; apply in_map_iff; exists t; split; [reflexivity | exact Ht]).
assert (Hnode_l : forall t, In t tns -> In (tn_addr t, NODE_SIZE) lrest) by (intros t Ht; apply Hnode_lx; apply in_or_app; left; exact Ht).
assert (Htns_in : forall j, 0 <= j < elen tns -> In (tnth tns j) tns) by (intros j Hj; unfold tnth; apply znth_In; exact Hj).
assert (Hntns : elen tns <= 509) by (rewrite Hlen_tns; fold ns; rewrite Hlen_ns; fold L; clear - HL254; lia).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ r 64 7 fpos HAR3 Hrin3 Hfin3) as HdF_r.
unfold zdisjoint in HdF_r. cbn [fst snd] in HdF_r. change (fs_frame_bytes 7) with 8192 in HdF_r. change (req_size 64) with 64 in HdF_r. rewrite EFA3 in HdF_r. fold F in HdF_r.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ tb 48 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. change (req_size 48) with 48 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb.
set (tn := tnth tns q) in *. set (nd := node ns q) in *.
assert (Hq_t : 0 <= q < elen tns) by (rewrite Hlen_tns; fold ns; clear - Hq0n Hqlt; lia).
destruct (Hmatch q Hq_t) as (Mlo & Mhi & Mcol & Mwf & Mnz). fold tn ns nd in Mlo, Mhi, Mcol, Mwf, Mnz.
destruct (cinv_node cnt ent st Hcinv q ltac:(fold ns; clear - Hq0n Hqlt; lia)) as (Hnlo & Hnhi & Hncol & _). fold ns nd in Hnlo, Hnhi, Hncol.
set (lo := n_lo nd) in *. set (hi := n_hi nd) in *.
assert (HEokc : ent_ok (c_E st)) by (exact (ent_ok_perm _ _ HpermE HentOk)).
destruct (kids_segments P lo hi (c_E st) El i1 Hdone ltac:(clear - Hnlo; lia) ltac:(rewrite Hlen_E; exact Hnhi) HEokc) as (HlenEl0 & HEokl & Ki1 & Ki2 & Ki3 & Ki4 & Kw).
assert (HlenEl : elen El = cnt) by (rewrite HlenEl0; exact Hlen_E).
pose proof Hdone as (PDi & PDlen & PDperm & _).
assert (Hzl : zlen (pal_bytes El ++ tail) = 3 * T)
by (unfold zlen; rewrite length_app, Nat2Z.inj_add; change (Z.of_nat (length (pal_bytes El))) with (zlen (pal_bytes El)); change (Z.of_nat (length tail)) with (zlen tail);
rewrite zlen_pal_bytes, HlenEl; clear - Htail; lia).
destruct HSTm as (CA1 & CA2 & CA3 & Hobj & CA4). fold q ns tn in CA3, Hobj.
set (va := tn_addr tn) in *.
assert (Hk01 : 0 <= elen k0 <= 1) by (unfold elen; destruct k0 as [|t0 [|t1 l0]]; cbn [length m_kid_ok] in *; [clear; lia | clear; lia | contradiction]).
assert (Hk11 : 0 <= elen k1 <= 1) by (unfold elen; destruct k1 as [|t0 [|t1 l0]]; cbn [length m_kid_ok] in *; [clear; lia | clear; lia | contradiction]).
idtac "OK-ST3-FACTS".
assert (Hva_l : In (va, NODE_SIZE) lrest) by (exact (Hnode_l _ (Htns_in q Hq_t))).
assert (Hva_in3 : In (va, NODE_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hva_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ va NODE_SIZE HAR3 Hva_in3) as (Hva4096 & Hvazone & Hvaceil & Hva16). change (req_size NODE_SIZE) with 56 in Hvazone, Hvaceil.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ va NODE_SIZE 7 fpos HAR3 Hva_in3 Hfin3) as HdF_va.
unfold zdisjoint in HdF_va. cbn [fst snd] in HdF_va. change (fs_frame_bytes 7) with 8192 in HdF_va. change (req_size NODE_SIZE) with 56 in HdF_va. rewrite EFA3 in HdF_va. fold F in HdF_va.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ va NODE_SIZE cid pos HAR3 Hva_in3 HfinS3) as HdC_va.
unfold zdisjoint in HdC_va. cbn [fst snd] in HdC_va. change (req_size NODE_SIZE) with 56 in HdC_va. rewrite EFA3 in HdC_va.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (va, NODE_SIZE) HAR3 HPrt3 ltac:(right; exact Hva_l)) as HzR_va.
unfold zdisjoint, block_rng in HzR_va. cbn [fst snd] in HzR_va. change (req_size RGB_SIZE) with 64 in HzR_va. change (req_size NODE_SIZE) with 56 in HzR_va.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (va, NODE_SIZE) HAR3 HPtb3 ltac:(right; exact Hva_l)) as HzT_va.
unfold zdisjoint, block_rng in HzT_va. cbn [fst snd] in HzT_va. change (req_size 48) with 48 in HzT_va. change (req_size NODE_SIZE) with 56 in HzT_va.
destruct (al_blocks _ _ LAWS _ _ _ _ _ va NODE_SIZE (proj1 HJ3) Hva_in3) as (_ & _ & _ & _ & Hvapres & _). change (req_size NODE_SIZE) with 56 in Hvapres.
assert (Hva_rng : 0 <= va < 2 ^ 64) by (clear - Hva4096 Hvaceil C1; lia).
assert (HFz : F + 8192 <= 2147446784 \/ 17594333495296 <= F) by (unfold gbox, in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg in HFhigh; clear - HFhigh; lia).
unfold gbox in HdFC.
assert (HFi : F + 8192 <= 65536 \/ 6156288 <= F) by (unfold gbox, off_img in HFhigh_img; clear - HFhigh_img; lia).
assert (Hvai : va + 56 <= 65536 \/ 6156288 <= va) by (clear - Hvazone; lia).
assert (Hvaz : va + 56 <= 2147446784 \/ 17594333495296 <= va) by (clear - Hvazone; lia).
assert (Hpp_in3 : In (pp, 3 * T) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hpp_l]).
assert (Hdn_in3 : In (dn, 4 * cnt) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hdn_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * T) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * cnt) HAR3 Hdn_in3) as (Hdn4096 & _ & Hdnceil & Hdn16).
pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq3T.
pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq4c.
assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx T ++ ((dn, 4 * cnt) :: m_node_blocks (tns ++ k0 ++ k1) ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
assert (Hva_n : In (va, NODE_SIZE) (m_node_blocks (tns ++ k0 ++ k1))) by (unfold m_node_blocks; apply in_map_iff; exists tn; split; [reflexivity | apply in_or_app; left; exact (Htns_in q Hq_t)]).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * T) (dn, 4 * cnt) HAR3 HPx ltac:(cbn [cht_blocks In]; tauto) ltac:(left; reflexivity)) as Hpd.
unfold zdisjoint, block_rng in Hpd. cbn [fst snd] in Hpd.
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * T) (va, NODE_SIZE) HAR3 HPx ltac:(cbn [cht_blocks In]; tauto) ltac:(right; apply in_or_app; left; exact Hva_n)) as Hs_pq.
unfold zdisjoint, block_rng in Hs_pq. cbn [fst snd] in Hs_pq. change (req_size NODE_SIZE) with 56 in Hs_pq.
assert (HPy : Permutation (ablocks B ly3 S3) ((dn, 4 * cnt) :: (m_node_blocks (tns ++ k0 ++ k1) ++ cht_blocks fq hh uu pp xx T ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (dn, 4 * cnt) _ (va, NODE_SIZE) HAR3 HPy ltac:(apply in_or_app; left; exact Hva_n)) as Hs_dq.
unfold zdisjoint, block_rng in Hs_dq. cbn [fst snd] in Hs_dq. change (req_size NODE_SIZE) with 56 in Hs_dq.
assert (HPn : Permutation (ablocks B ly3 S3) (m_node_blocks (tns ++ k0 ++ k1) ++ ((dn, 4 * cnt) :: cht_blocks fq hh uu pp xx T ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
assert (Hs_nn : forall j, 0 <= j < elen tns -> j <> q -> tn_addr (tnth tns j) + 56 <= va \/ va + 56 <= tn_addr (tnth tns j)).
{ intros j Hj Hne. assert (Hel : elen (tns ++ k0 ++ k1) = elen tns + elen k0 + elen k1) by (unfold elen; rewrite !length_app; clear; lia).
pose proof (m_sep_nodes B LAWS ly3 S3 _ _ _ (tns ++ k0 ++ k1) _ j q HAR3 HPn ltac:(rewrite Hel; clear - Hj Hk01 Hk11; lia) ltac:(rewrite Hel; clear - Hq_t Hk01 Hk11; lia) Hne) as Hsn.
rewrite !tnth_app_l in Hsn by assumption. exact Hsn. }
assert (Hres_rng : forall (kl : list tnode) res, (kl = [] -> res = 0) -> (forall t, kl = [t] -> res = tn_addr t /\ In t (tns ++ k0 ++ k1)) -> (length kl <= 1)%nat -> 0 <= res < 2 ^ 64).
{ intros kl res H0 H1 Hl. destruct kl as [|t0 [|t1 l0]]; [rewrite (H0 eq_refl); clear; lia | | cbn [length] in Hl; lia].
destruct (H1 t0 eq_refl) as (Hr0 & Hin0). rewrite Hr0.
assert (Ht0_3 : In (tn_addr t0, NODE_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hnode_lx; exact Hin0]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ _ NODE_SIZE HAR3 Ht0_3) as (Ht4096 & _ & Htceil & _). change (req_size NODE_SIZE) with 56 in Htceil. clear - Ht4096 Htceil C1. lia. }
assert (Hres0_rng : 0 <= res0 < 2 ^ 64).
{ apply (Hres_rng k0 res0); [intros ->; exact Hkid0 | intros t ->; cbn [m_kid_ok] in Hkid0; split; [exact (proj1 Hkid0) | apply in_or_app; right; apply in_or_app; left; left; reflexivity] | unfold elen in Hk01; clear - Hk01; lia]. }
assert (Hres1_rng : 0 <= res1 < 2 ^ 64).
{ apply (Hres_rng k1 res1); [intros ->; exact Hkid1 | intros t ->; cbn [m_kid_ok] in Hkid1; split; [exact (proj1 Hkid1) | apply in_or_app; right; apply in_or_app; right; left; reflexivity] | unfold elen in Hk11; clear - Hk11; lia]. }
assert (Hel3 : elen (tns ++ k0 ++ k1) = elen tns + elen k0 + elen k1) by (unfold elen; rewrite !length_app; clear; lia).
set (mw := elen tns) in *.
assert (Hmw0 : 0 <= mw <= 509) by (subst mw; unfold elen in *; clear - Hntns; lia).
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (TRANS : forall mem' : word -> option byte,
(forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (F + 32 + 8 * mw <= a < F + 32 + 8 * mw + 16) -> aview trbsegs (w_H W3) mem' a = aview trbsegs (w_H W3) (ms_mem ms3) a) ->
arr8 trbsegs (mrestrict (w_H W3) mem') pp (pal_bytes El ++ tail) /\ arr32 trbsegs (mrestrict (w_H W3) mem') dn (fr_vals El) /\
obj_at trbsegs (mrestrict (w_H W3) mem') va LAY_Node (node_vals res0 res1 tn 0) /\
(forall j, 0 <= j < mw -> j <> q -> node_mem trbsegs (mrestrict (w_H W3) mem') ns tns j) /\
(forall j, 0 <= j < mw -> val_mem trbsegs (mrestrict (w_H W3) mem') (F + 32 + 8 * j) 8 (tn_addr (tnth tns j))) /\
m_kid_ok B cxv (w_H W3) mem' k0 res0 lo (i1 - 1) (n_col nd) (zsub El lo (i1 - 1)) /\
m_kid_ok B cxv (w_H W3) mem' k1 res1 i1 hi (L - 1 + elen k0) (zsub El i1 hi)) end.
{ intros mem' HK.
assert (HKb : forall b sz, In (b, sz) lrest -> forall i, 0 <= i < req_size sz -> aview trbsegs (w_H W3) mem' (b + i) = aview trbsegs (w_H W3) (ms_mem ms3) (b + i)).
{ intros b sz Hb i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply (HK _ Hq1 Hq2).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ b sz 7 fpos HAR3 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hb]) Hfin3) as HdFb.
unfold zdisjoint in HdFb. cbn [fst snd] in HdFb. change (fs_frame_bytes 7) with 8192 in HdFb. rewrite EFA3 in HdFb. fold F in HdFb. clear - Hi HdFb Hmw0. lia. }
split. { apply (arr8_frame trbsegs _ _ pp _ CA1). intros a Ha. rewrite Hzl in Ha. apply (mbyte_of_aview trbsegs). replace a with (pp + (a - pp)) by (clear; lia). apply (HKb pp _ Hpp_l). clear - Ha Hrq3T. lia. }
split. { apply (arr32_frame trbsegs _ _ dn _ CA2). intros a Ha. rewrite zlen_fr_vals, HlenEl in Ha. apply (mbyte_of_aview trbsegs). replace a with (dn + (a - dn)) by (clear; lia). apply (HKb dn _ Hdn_l). clear - Ha Hrq4c. lia. }
split. { apply (obj_at_transport_range trbsegs _ _ _ _ _ NODE_SIZE Hobj (proj1 lay_inside_Node)). intros i Hi. apply (mbyte_of_aview trbsegs). apply (HKb va _ Hva_l). change (req_size NODE_SIZE) with 56. exact Hi. }
split. { intros j Hj Hne. apply (node_mem_frame trbsegs _ _ _ _ j (CA3 j Hj Hne)). intros i Hi. apply (mbyte_of_aview trbsegs). apply (HKb _ _ (Hnode_l _ (Htns_in j Hj))). change (req_size NODE_SIZE) with 56. exact Hi. }
split. { intros j Hj. pose proof (CA4 j Hj) as Vw. intros k0' Hk0'. rewrite <- (Vw k0' Hk0'). apply (mbyte_of_aview trbsegs).
set (aw := F + 32 + 8 * j + Z.of_nat k0').
assert (Haw : F + 32 <= aw < F + 32 + 8 * mw) by (subst aw; clear - Hj Hk0'; lia).
pose proof HdF_r as HdFr. pose proof HdF_tb as HdFt. unfold gbox in HdFr, HdFt.
change (aview trbsegs (w_H W3) mem' aw = aview trbsegs (w_H W3) (ms_mem ms3) aw).
apply HK; [clear - Haw HFrng HFceil Hmw0 C1; lia | clear - Haw Hmw0 HFceil HdFr HdFt; lia | clear - Haw; lia]. }
lazymatch goal with |- m_kid_ok _ ?cxv _ _ _ _ _ _ _ _ /\ _ =>
assert (KID2 : forall kl res lo' hi' cidx' seg, m_kid_ok B cxv (w_H W3) (ms_mem ms3) kl res lo' hi' cidx' seg -> (forall t, kl = [t] -> In t (tns ++ k0 ++ k1)) ->
m_kid_ok B cxv (w_H W3) mem' kl res lo' hi' cidx' seg) end.
{ intros kl res lo' hi' cidx' seg K Hin. destruct kl as [|t [|t' l0]]; cbn [m_kid_ok] in K |- *; [exact K | | contradiction].
destruct K as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & (d0 & d1 & Q7) & Q8 & Q9).
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [|split; [exact Q8 | exact Q9]].
exists d0, d1. apply (obj_at_transport_range trbsegs _ _ _ _ _ NODE_SIZE Q7 (proj1 lay_inside_Node)). intros i Hi. apply (mbyte_of_aview trbsegs).
apply (HKb _ _ (Hnode_lx _ (Hin t eq_refl))). change (req_size NODE_SIZE) with 56. exact Hi. }
split; [apply (KID2 _ _ _ _ _ _ Hkid0); intros t ->; apply in_or_app; right; apply in_or_app; left; left; reflexivity
| apply (KID2 _ _ _ _ _ _ Hkid1); intros t ->; apply in_or_app; right; apply in_or_app; right; left; reflexivity]. }
idtac "OK-TRANS".
assert (OLDK : forall j, 0 <= j < mw -> n_leaf (node ns j) = false -> forall c, (n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) -> 0 <= c < elen tns).
{ intros j Hj Hl c Hc. destruct (cinv_kids cnt ent st Hcinv j ltac:(fold ns; rewrite <- Hlen_tns; exact Hj) Hl) as (c' & K0 & K1 & R1 & R2). fold ns in K0, K1, R2.
rewrite K0, K1 in Hc. rewrite <- Hlen_tns in R2. fold mw in R2 |- *. destruct Hc as [Hc|Hc]; injection Hc as <-; clear - Hj R1 R2; lia. }
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (OKG : forall (mem' : word -> option byte) t0 t1, k0 = [t0] -> k1 = [t1] ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (F + 32 + 8 * mw <= a < F + 32 + 8 * mw + 16) -> aview trbsegs (w_H W3) mem' a = aview trbsegs (w_H W3) (ms_mem ms3) a) ->
val_mem trbsegs (mrestrict (w_H W3) mem') (F + 32 + 8 * mw) 8 res0 -> val_mem trbsegs (mrestrict (w_H W3) mem') (F + 32 + 8 * (mw + 1)) 8 res1 ->
cinv cnt ent (csplit st El i1) /\ nleaves (c_ns (csplit st El i1)) = L + 1 /\ c_q (csplit st El i1) = q + 1 /\ elen (c_ns (csplit st El i1)) = mw + 2 /\
m_CLmem (w_H W3) mem' pp dn F tail (csplit st El i1) (tns ++ [t0; t1]) /\ elen (tns ++ [t0; t1]) = elen (c_ns (csplit st El i1)) /\
(forall j, 0 <= j < elen (tns ++ [t0; t1]) -> tn_matches (tnth (tns ++ [t0; t1]) j) (node (c_ns (csplit st El i1)) j)) /\
(forall j, c_q (csplit st El i1) <= j < elen (tns ++ [t0; t1]) -> tn_facts (tnth (tns ++ [t0; t1]) j) (node (c_ns (csplit st El i1)) j)) /\
(forall t, In t (tns ++ [t0; t1]) -> m_blk_own B cxv (tn_addr t) NODE_SIZE)) end.
{ intros mem' t0 t1 E0k E1k HK W0 W1. destruct (TRANS mem' HK) as (Hpa' & Hfa' & OBJ' & NM' & NL' & KID0' & KID1'). subst k0 k1.
cbn [m_kid_ok] in Hkid0, Hkid1, KID0', KID1'. change (elen [t0]) with 1 in *. change (elen [t1]) with 1 in *.
destruct Hkid0 as (Er0 & Tnz0 & Ti0 & Tx0 & Tc0 & Twf0 & _ & Tf0 & Tow0). destruct Hkid1 as (Er1 & Tnz1 & Ti1 & Tx1 & Tc1 & Twf1 & _ & Tf1 & Tow1).
destruct KID0' as (_ & _ & _ & _ & _ & _ & Tobj0 & _). destruct KID1' as (_ & _ & _ & _ & _ & _ & Tobj1 & _).
assert (Et0 : tnth (tns ++ [t0; t1]) mw = t0) by (subst mw; apply tnth_app_new0).
assert (Et1 : tnth (tns ++ [t0; t1]) (mw + 1) = t1) by (subst mw; apply tnth_app_new1).
destruct (csplit_inv dentry cnt ent st P El i1 Hcinv Hqlt Hlt Hdone) as (CINV' & HL' & Hlen').
destruct (csplit_nodes st El i1 ltac:(fold q ns; rewrite <- Hlen_tns; exact Hq_t)) as (Hlen2 & NDo & NDq & ND0 & ND1 & Hq' & HE').
fold ns q nd L in HL', Hlen', Hlen2, NDo, NDq, ND0, ND1, Hq'. rewrite <- Hlen_tns in Hlen', Hlen2, NDo, NDq, ND0, ND1. fold mw in Hlen', Hlen2, NDo, NDq, ND0, ND1. fold lo hi in NDq, ND0, ND1.
set (ns' := c_ns (csplit st El i1)) in *.
assert (Hel2 : elen (tns ++ [t0; t1]) = mw + 2) by (subst mw; apply elen_app2).
split; [exact CINV'|]. split; [exact HL'|]. split; [exact Hq'|]. split; [exact Hlen2|].
split.
{ unfold m_CLmem. rewrite HE'. fold ns'. split; [exact Hpa'|]. split; [exact Hfa'|]. split.
- intros j Hj. rewrite Hel2 in Hj.
destruct (Z.eq_dec j q) as [-> | Hnq].
{ unfold node_mem. rewrite NDq. cbn [n_leaf n_k0 n_k1 oaddr]. rewrite Et0, Et1, (tnth_app_l tns [t0; t1] q Hq_t). fold tn va. rewrite <- Er0, <- Er1. exact OBJ'. }
destruct (Z_lt_le_dec j mw) as [Hjm | Hjm].
{ apply (node_mem_ext trbsegs _ ns _ tns [t0; t1] j (NDo j ltac:(clear - Hj Hjm; lia) Hnq) ltac:(fold mw; clear - Hj Hjm; lia) (OLDK j ltac:(clear - Hj Hjm; lia)) (NM' j ltac:(clear - Hj Hjm; lia) Hnq)). }
destruct (Z.eq_dec j mw) as [-> | Hnm].
{ unfold node_mem. rewrite ND0. cbn [n_leaf]. rewrite Et0. exact Tobj0. }
assert (Ej : j = mw + 1) by (clear - Hj Hjm Hnm; lia). subst j. unfold node_mem. rewrite ND1. cbn [n_leaf]. rewrite Et1. exact Tobj1.
- intros j Hj. rewrite Hel2 in Hj. destruct (Z_lt_le_dec j mw) as [Hjm | Hjm]; [rewrite (tnth_app_l tns [t0; t1] j ltac:(fold mw; clear - Hj Hjm; lia)); apply NL'; clear - Hj Hjm; lia|].
destruct (Z.eq_dec j mw) as [-> | Hnm]; [rewrite Et0, <- Er0; exact W0|].
assert (Ej : j = mw + 1) by (clear - Hj Hjm Hnm; lia). subst j. rewrite Et1, <- Er1. exact W1. }
split; [rewrite Hel2, Hlen2; reflexivity|].
split.
{ intros j Hj. rewrite Hel2 in Hj.
destruct (Z.eq_dec j q) as [-> | Hnq]; [rewrite (tnth_app_l tns [t0; t1] q Hq_t), NDq; fold tn; exact (conj Mlo (conj Mhi (conj Mcol (conj Mwf Mnz))))|].
destruct (Z_lt_le_dec j mw) as [Hjm | Hjm]; [rewrite (tnth_app_l tns [t0; t1] j ltac:(fold mw; clear - Hj Hjm; lia)), (NDo j ltac:(clear - Hj Hjm; lia) Hnq); apply Hmatch; fold mw; clear - Hj Hjm; lia|].
destruct (Z.eq_dec j mw) as [-> | Hnm].
{ rewrite Et0, ND0. split; [exact Ti0|]. split; [exact Tx0|]. split; [exact Tc0|]. split; [exact Twf0 | exact Tnz0]. }
assert (Ej : j = mw + 1) by (clear - Hj Hjm Hnm; lia). subst j. rewrite Et1, ND1.
split; [exact Ti1|]. split; [exact Tx1|]. split; [cbn [n_col]; rewrite Tc1; clear; lia|]. split; [exact Twf1 | exact Tnz1]. }
split.
{ intros j Hj. rewrite Hq', Hel2 in Hj. destruct (Z_lt_le_dec j mw) as [Hjm | Hjm].
- rewrite (tnth_app_l tns [t0; t1] j ltac:(fold mw; clear - Hj Hjm Hq0n; lia)), (NDo j ltac:(clear - Hj Hjm Hq0n; lia) ltac:(clear - Hj; lia)). apply Hfacts. fold q mw. clear - Hj Hjm. lia.
- destruct (Z.eq_dec j mw) as [-> | Hnm]; [rewrite Et0, ND0; exact Tf0|].
assert (Ej : j = mw + 1) by (clear - Hj Hjm Hnm; lia). subst j. rewrite Et1, ND1. exact Tf1. }
intros t Ht. apply in_app_or in Ht as [Ht | [<- | [<- | []]]]; [exact (Hown t Ht) | exact Tow0 | exact Tow1]. }
idtac "OK-OKG".
assert (MOKG : forall t0 t1, k0 = [t0] -> k1 = [t1] -> forall j, 0 <= j < elen (tns ++ [t0; t1]) -> tnode_means_ok (tnth (tns ++ [t0; t1]) j)).
{ intros t0 t1 E0k E1k j Hj. pose proof Hkid0 as Hkq0. pose proof Hkid1 as Hkq1. rewrite E0k in Hkq0. rewrite E1k in Hkq1. cbn [m_kid_ok] in Hkq0, Hkq1.
destruct Hkq0 as (_ & _ & _ & _ & _ & Twf0 & _ & Tf0 & _). destruct Hkq1 as (_ & _ & _ & _ & _ & Twf1 & _ & Tf1 & _).
assert (Hel2 : elen (tns ++ [t0; t1]) = mw + 2) by (subst mw; apply elen_app2). rewrite Hel2 in Hj.
destruct (Z_lt_le_dec j mw) as [Hjm | Hjm]; [rewrite (tnth_app_l tns [t0; t1] j ltac:(fold mw; clear - Hj Hjm; lia)); apply MOK; fold mw; clear - Hj Hjm; lia|].
destruct (Z.eq_dec j mw) as [-> | Hnm].
- assert (Et0 : tnth (tns ++ [t0; t1]) mw = t0) by (subst mw; apply tnth_app_new0). rewrite Et0.
refine (c_means_ok_of_facts t0 _ El lo (i1 - 1) HEokl _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 Twf0))))) Tf0); [clear - Hnlo; lia | rewrite HlenEl; clear - PDi Hnhi; lia | reflexivity].
- assert (Ej : j = mw + 1) by (clear - Hj Hjm Hnm; lia). subst j.
assert (Et1 : tnth (tns ++ [t0; t1]) (mw + 1) = t1) by (subst mw; apply tnth_app_new1). rewrite Et1.
refine (c_means_ok_of_facts t1 _ El i1 hi HEokl _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 Twf1))))) Tf1); [clear - Hnlo PDi; lia | rewrite HlenEl; exact Hnhi | reflexivity]. }
idtac "OK-MOKG".
destruct k0 as [|t0 [|t0' l0]]; [cbn [m_kid_ok] in Hkid0; contradiction | | cbn [m_kid_ok] in Hkid0; contradiction].
destruct k1 as [|t1 [|t1' l1]]; [cbn [m_kid_ok] in Hkid1; contradiction | | cbn [m_kid_ok] in Hkid1; contradiction].
change (elen [t0]) with 1 in *. change (elen [t1]) with 1 in *.
assert (Hmw2 : mw = 2 * L - 1) by (subst mw; rewrite Hlen_tns; fold ns; exact Hlen_ns).
idtac "OK-KIDS2".
gboxh HFz. gboxh HFi. gboxh Hvai. gboxh Hvaz. gboxh HdF_va. gboxh HdC_va. gboxh HzR_va. gboxh HzT_va. gboxh HdF_r. gboxh HdF_tb. gboxh HdFC. gboxh Hvazone.
unfold NODE_SIZE in Hva_in3.
reshok_bx HS 44%nat.
assert (UNLt : forall E' (nl c : Z), ew E' 930 = Z_to_bv 64 nl -> 0 <= nl < 2 ^ 16 -> 0 <= c <= 2 * nl ->
U E' (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (- c))) = 2 * nl - c).
{ intros E' nl c Hn Hnl Hcc. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SExt, (U_atom E' 930 nl Hn), !U_SLit by (clear - Hnl; lia). change (2 ^ Z.of_N 16) with 65536. rewrite Z.mod_small by (clear - Hnl; lia).
rewrite (zcanon_id nl) by (unfold M64; clear - Hnl; lia). change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 1) with 2.
rewrite (zcanon_id (nl * 2)) by (unfold M64; clear - Hnl; lia).
unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace (nl * 2 + - c) with (2 * nl - c) by (clear; lia). apply Z.mod_small. clear - Hnl Hcc. lia. }
assert (UNL8 : forall E' (nl c : Z), ew E' 930 = Z_to_bv 64 nl -> 0 <= nl < 2 ^ 16 -> 0 <= c <= 2 * nl ->
U E' (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (- c))) (SLit 3)) = 8 * (2 * nl - c)).
{ intros E' nl c Hn Hnl Hcc. replace (8 * (2 * nl - c)) with ((2 * nl - c) * 2 ^ 3) by (clear; lia).
apply U_sll_small_q; [exact (UNLt E' nl c Hn Hnl Hcc) | clear - Hcc; lia | clear; lia | clear - Hnl Hcc; lia]. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (R930k : ew Ev 930 = Z_to_bv 64 (L - 1 + 1 + 1)) by m_ewT;
assert (RFk : ew Ev 54 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF);
assert (HUnl32 : U Ev (SOff 54 32) = F + 32) by (apply (U_atom_off Ev 54 F 32 RFk); [exact HFrng | clear - HF4096 HFceil C1; lia]) end.
m_add_cond HS BC_GEU (SLit 511) (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (-3)))
ltac:(eapply (ub_geu_cond _ (SLit 511) _ 511 (2 * (L - 1 + 1 + 1) - 3) ltac:(reflexivity) (UNLt _ (L - 1 + 1 + 1) 3 R930k ltac:(clear - HL1 HL254; lia) ltac:(clear - HL1; lia))); clear - HL254; lia).
m_add_cond HS BC_GEU (SAlu ALU_XOR (SOff 54 32) (SLit (-1))) (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (-3))) (SLit 3))
ltac:(eapply (ub_room_cond _ _ _ (F + 32) (8 * (2 * (L - 1 + 1 + 1) - 3)) HUnl32 (UNL8 _ (L - 1 + 1 + 1) 3 R930k ltac:(clear - HL1 HL254; lia) ltac:(clear - HL1; lia)));
clear - HL1 HL254 HF4096 HFceil C1; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83cd4.
idtac "OK-RUN-NL0".
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
idtac "OK-RUN-NL0b".
assert (UNL : forall E' (nl b c : Z) (bsv : sv), ew E' 930 = Z_to_bv 64 nl -> 0 <= nl < 2 ^ 16 -> U E' bsv = b -> 0 <= b -> 0 <= c -> 0 <= 16 * nl + b - c -> 16 * nl + b < 2 ^ 64 ->
U E' (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 4)) bsv) (SLit (- c))) = 16 * nl + b - c).
{ intros E' nl b c bsv Hn Hnl Hb Hb0 Hcc0 Hlo0 Hhi0. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SExt, (U_atom E' 930 nl Hn), Hb, !U_SLit by (clear - Hnl; lia). change (2 ^ Z.of_N 16) with 65536. rewrite Z.mod_small by (clear - Hnl; lia).
rewrite (zcanon_id nl) by (unfold M64; clear - Hnl; lia). change (Z.land (zcanon 4) 63) with 4. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 4) with 16.
rewrite (zcanon_id (nl * 16)) by (unfold M64; clear - Hnl; lia). rewrite (zcanon_id (nl * 16 + b)) by (unfold M64; clear - Hnl Hb0 Hhi0; lia).
unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace (nl * 16 + b + - c) with (16 * nl + b - c) by (clear; lia). apply Z.mod_small. clear - Hlo0 Hhi0 Hcc0. lia. }
idtac "OK-UNL".
set (c0a := F + 32 + 8 * mw) in *. set (c1a := F + 32 + 8 * (mw + 1)) in *.
assert (Hc0_rng : F + 32 <= c0a /\ c0a + 8 <= F + 4128) by (subst c0a; clear - Hmw0; lia).
assert (Hc1_rng : F + 32 <= c1a /\ c1a + 8 <= F + 4128) by (subst c1a; clear - Hmw0; lia).
pose proof HFz as HFz'. pose proof HFi as HFi'. pose proof HdF_r as HdFr'. pose proof HdF_tb as HdFt'. pose proof HdFC as HdFC'. unfold gbox in HFz', HFi', HdFr', HdFt', HdFC'.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ3) Hfin3) as (_ & _ & HFpresN & _). change (fs_frame_bytes 7) with 8192 in HFpresN. rewrite EFA3 in HFpresN. fold F in HFpresN.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trbsegs 950%nat Ex ssx msx [Z_to_bv 64 c0a; Z_to_bv 64 c1a] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
assert (E950 : ew (havoc E0v 950 vals) 950 = Z_to_bv 64 c0a)
by (change 950%nat with (950 + 0)%nat at 2; rewrite (ew_havoc_new _ 950%nat vals 0%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E951 : ew (havoc E0v 950 vals) 951 = Z_to_bv 64 c1a)
by (change 951%nat with (950 + 1)%nat; rewrite (ew_havoc_new _ 950%nat vals 1%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
idtac "OK-HAVOC-NL".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E950c : ew Ev 950 = Z_to_bv 64 c0a) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E950);
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 950%nat) 0 8 0 8 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E950c, unsigned_lit_small by (clear - Hc0_rng HF4096 HFceil C1; lia);
split; [clear - Hc0_rng HF4096; lia|]; split; [clear - Hc0_rng HFceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpresN (c0a + o) ltac:(clear - Ho Hc0_rng; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hc0_rng HFceil Hceil Hslo FFS; lia
| clear - Hc0_rng HF8lo HF8hi HFq HF8 HFceil HFz' C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - Hc0_rng; lia
| clear - Hc0_rng HFi'; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - Hc0_rng HdFC' Hflo Hfhi; lia
| clear - Hc0_rng HdFr'; lia
| clear - Hc0_rng HdFt'; lia
| fail
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "OK-CELL0".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E951c : ew Ev 951 = Z_to_bv 64 c1a) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E951);
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 951%nat) 0 8 0 8 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E951c, unsigned_lit_small by (clear - Hc1_rng HF4096 HFceil C1; lia);
split; [clear - Hc1_rng HF4096; lia|]; split; [clear - Hc1_rng HFceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpresN (c1a + o) ltac:(clear - Ho Hc1_rng; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hc1_rng HFceil Hceil Hslo FFS; lia
| clear - Hc1_rng HF8lo HF8hi HFq HF8 HFceil HFz' C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - Hc1_rng; lia
| clear - Hc1_rng HFi'; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - Hc1_rng HdFC' Hflo Hfhi; lia
| clear - Hc1_rng HdFr'; lia
| clear - Hc1_rng HdFt'; lia
| subst c0a c1a; clear; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "OK-CELL1".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (R930z : ew Ev 930 = Z_to_bv 64 (L - 1 + 1 + 1)) by m_ewT;
assert (RFz : ew Ev 54 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF);
assert (E950d : ew Ev 950 = Z_to_bv 64 c0a) by m_ewT;
assert (E951d : ew Ev 951 = Z_to_bv 64 c1a) by m_ewT;
assert (HUA : U Ev (SAlu ALU_ADD (SOff 54 32) (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (-3))) (SLit 3))) = U Ev (SOff 950 0)) end.
{
lazymatch goal with |- U ?Ev _ = _ =>
rewrite (U_atom Ev 950 c0a E950d) by (clear - Hc0_rng HF4096 HFceil C1; lia);
replace c0a with ((F + 32) + 8 * (2 * (L - 1 + 1 + 1) - 3)) by (subst c0a; rewrite Hmw2; clear; lia);
apply U_add_small_q; [apply (U_atom_off Ev 54 F 32 RFz); [exact HFrng | clear - HF4096 HFceil C1; lia]
| exact (UNL8 Ev (L - 1 + 1 + 1) 3 R930z ltac:(clear - HL1 HL254; lia) ltac:(clear - HL1; lia))
| clear - HF4096; lia | clear - HL1; lia | clear - HL254 HFceil C1; lia] end. }
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (10%bv : bv 5) (SOff 950 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (10%bv : bv 5) HS); change (sv_denot Ev (SOff 950 0) = sv_denot Ev e);
apply U_inj; symmetry; exact HUA)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 950%nat (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E950d, unsigned_lit_small by (clear - Hc0_rng HF4096 HFceil C1; lia); change (2 ^ 3) with 8;
split; [clear - Hc0_rng HF4096 HFceil C1; lia|]; split; [subst c0a; clear - HFq; rewrite HFq; replace (32 * (F / 32) + 32 + 8 * mw) with ((4 * (F / 32) + 4 + mw) * 8) by lia; apply Z_mod_mult | clear - Hc0_rng HFceil C1; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 951%nat (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E951d, unsigned_lit_small by (clear - Hc1_rng HF4096 HFceil C1; lia); change (2 ^ 3) with 8;
split; [clear - Hc1_rng HF4096 HFceil C1; lia|]; split; [subst c1a; clear - HFq; rewrite HFq; replace (32 * (F / 32) + 32 + 8 * (mw + 1)) with ((4 * (F / 32) + 4 + mw + 1) * 8) by lia; apply Z_mod_mult | clear - Hc1_rng HFceil C1; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "OK-PIN-NL0".
ga_ra_frame HS AG HFq F 4 4 512 HRAnl.
reshok_bx HS 44%nat.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (R930m : ew Ev 930 = Z_to_bv 64 (L - 1 + 1 + 1)) by m_ewT;
assert (RFm : ew Ev 54 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF);
assert (HUnl32m : U Ev (SOff 54 32) = F + 32) by (apply (U_atom_off Ev 54 F 32 RFm); [exact HFrng | clear - HF4096 HFceil C1; lia]) end.
m_add_cond HS BC_GEU (SLit 511) (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (-2)))
ltac:(eapply (ub_geu_cond _ (SLit 511) _ 511 (2 * (L - 1 + 1 + 1) - 2) ltac:(reflexivity) (UNLt _ (L - 1 + 1 + 1) 2 R930m ltac:(clear - HL1 HL254; lia) ltac:(clear - HL1; lia))); clear - HL254; lia).
m_add_cond HS BC_GEU (SAlu ALU_XOR (SOff 54 32) (SLit (-1))) (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (-2))) (SLit 3))
ltac:(eapply (ub_room_cond _ _ _ (F + 32) (8 * (2 * (L - 1 + 1 + 1) - 2)) HUnl32m (UNL8 _ (L - 1 + 1 + 1) 2 R930m ltac:(clear - HL1 HL254; lia) ltac:(clear - HL1; lia)));
clear - HL1 HL254 HF4096 HFceil C1; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83d18.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 821 ?c)) ?len =>
rewrite (U_atom_off Ex 821 va c); [| first [exact E821c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E821c | m_ewT] | exact Hva_rng | clear - Hva4096 Hvaceil C1; lia];
eapply (obl_of_block trbsegs _ LAWS _ _ _ _ _ Ex (SOff bx 0) _ len va 56 (proj1 HJ3) Hva_in3);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear; lia | change (req_size 56) with 56; clear; lia ] end).
idtac "OK-RUN-NL1".
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 950 0)) ?len =>
rewrite (U_atom Ex 950 c0a); [| first [exact E950c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E950c] | clear - Hc0_rng HF4096 HFceil C1; lia];
eapply (obl_of_range trbsegs _ _ Ex (SOff bx 0) _ len (F + 8 * 4) (8 * 512));
[ exact HRAnl
| rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear - Hc0_rng; lia | clear - Hc0_rng; lia ] end).
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 951 0)) ?len =>
rewrite (U_atom Ex 951 c1a); [| first [exact E951c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E951c] | clear - Hc1_rng HF4096 HFceil C1; lia];
eapply (obl_of_range trbsegs _ _ Ex (SOff bx 0) _ len (F + 8 * 4) (8 * 512));
[ exact HRAnl
| rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear - Hc1_rng; lia | clear - Hc1_rng; lia ] end).
idtac "OK-OBL-NL".
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(fun nb => first
[ lazymatch nb with 950%nat =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 950%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E950c; apply unsigned_lit_small; clear - Hc0_rng HF4096 HFceil C1; lia | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; rewrite ?EFA3; fold F; clear - Ha Hc0_rng; lia | ] end
| lazymatch nb with 951%nat =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 951%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E951c; apply unsigned_lit_small; clear - Hc1_rng HF4096 HFceil C1; lia | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; rewrite ?EFA3; fold F; clear - Ha Hc1_rng; lia | ] end ]).
idtac "OK-AWR-NL".
m_run_keptG HFr AG (fun a : Z => (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ c0a <= a < c0a + 8 \/ c1a <= a < c1a + 8) Hceil Hslo FFS UN4.
clear HF HFr HG.
norm_ss HS.
idtac "OK-KEPT-NL1".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (R930y : ew Ev 930 = Z_to_bv 64 (L - 1 + 1 + 1)) by m_ewT;
assert (RFy : ew Ev 54 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF);
assert (E951e : ew Ev 951 = Z_to_bv 64 c1a) by m_ewT;
assert (HUB : U Ev (SAlu ALU_ADD (SOff 54 32) (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff 930 0)) (SLit 1)) (SLit (-2))) (SLit 3))) = U Ev (SOff 951 0)) end.
{
lazymatch goal with |- U ?Ev _ = _ =>
rewrite (U_atom Ev 951 c1a E951e) by (clear - Hc1_rng HF4096 HFceil C1; lia);
replace c1a with ((F + 32) + 8 * (2 * (L - 1 + 1 + 1) - 2)) by (subst c1a; rewrite Hmw2; clear; lia);
apply U_add_small_q; [apply (U_atom_off Ev 54 F 32 RFy); [exact HFrng | clear - HF4096 HFceil C1; lia]
| exact (UNL8 Ev (L - 1 + 1 + 1) 2 R930y ltac:(clear - HL1 HL254; lia) ltac:(clear - HL1; lia))
| clear - HF4096; lia | clear - HL1; lia | clear - HL254 HFceil C1; lia] end. }
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (10%bv : bv 5) (SOff 951 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (10%bv : bv 5) HS); change (sv_denot Ev (SOff 951 0) = sv_denot Ev e);
apply U_inj; symmetry; exact HUB)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKn : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (F + 32 + 8 * mw <= a < F + 32 + 8 * mw + 16) -> aview trbsegs (w_H W3) (ms_mem msX) a = aview trbsegs (w_H W3) (ms_mem ms3) a) end.
{ intros a Ha1 Ha2 Ha3.
assert (Ha4 : ~ ((alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ c0a <= a < c0a + 8 \/ c1a <= a < c1a + 8))
by (subst c0a c1a; clear - Ha2 Ha3; lia).
rewrite (UN4 a Ha1 Ha4). exact (UN3 a Ha1 Ha2). }
destruct (TRANS _ HKn) as (_ & _ & OBJn & _).
pose proof (obj_at_nth trbsegs _ va LAY_Node _ 1%nat (8, 8%N) res1 OBJn eq_refl eq_refl) as Vright.
unfold field_ok in Vright. cbn [fst snd N.to_nat Z.of_N Pos.to_nat Pos.iter_op Nat.add] in Vright.
pose proof HdF_va as HdFva'. pose proof HdC_va as HdCva'. pose proof HzR_va as HzRva'. pose proof HzT_va as HzTva'. pose proof Hvai as Hvai'. pose proof Hvaz as Hvaz'.
unfold gbox in HdFva', HdCva', HzRva', HzTva', Hvai', Hvaz'.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E821n : ew Ev 821 = Z_to_bv 64 va) by m_ewT;
assert (E905n : ew Ev 905 = Z_to_bv 64 res1) by m_ewT;
assert (E950n : ew Ev 950 = Z_to_bv 64 c0a) by m_ewT;
assert (E951n : ew Ev 951 = Z_to_bv 64 c1a) by m_ewT;
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 821%nat) 8 16 0 0 [YQ0b.mkChunk 8 (CVal 8 (SOff 905 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E821n, unsigned_lit_small by exact Hva_rng;
split; [clear - Hva4096; lia|]; split; [clear - Hvaceil C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ va 8 8 (SOff 905 0) res1);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E905n | exact Hres1_rng | cbn; clear; lia | exact (proj1 Vright)] | apply Forall_nil] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite ?E950n, ?E951n, ?(unsigned_lit_small c0a), ?(unsigned_lit_small c1a) by (clear - Hc0_rng Hc1_rng HF4096 HFceil C1; lia);
ga_evalE0 AG; repeat split;
first [ clear - Hva4096 Hvaceil Hceil Hslo FFS; lia
| clear - Hvaz' HF8lo HF8hi HFq HF8 HFceil C1; unfold SB in *; lia
| clear - Hvai'; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdFva'; lia
| clear - HdFva' Hc0_rng Hc1_rng; lia
| clear - HdCva' Hflo Hfhi; lia
| clear - HzRva'; lia
| clear - HzTva'; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
clear HdFva' HdCva' HzRva' HzTva' Hvai' Hvaz'.
idtac "OK-NODEREG".
idtac "OK-PIN-NL1".
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ3) Hfin3) as (_ & _ & HFpresM & _). change (fs_frame_bytes 7) with 8192 in HFpresM. rewrite EFA3 in HFpresM. fold F in HFpresM.
ga_ra_frame HS AG HFq F 4 4 512 HRAnl2.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83d48.
idtac "OK-RUN-LT".
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 950 0)) ?len =>
rewrite (U_atom Ex 950 c0a); [| first [exact E950c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E950c] | clear - Hc0_rng HF4096 HFceil C1; lia];
eapply (obl_of_range trbsegs _ _ Ex (SOff bx 0) _ len (F + 8 * 4) (8 * 512));
[ exact HRAnl2
| rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear - Hc0_rng; lia | clear - Hc0_rng; lia ] end).
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 951 0)) ?len =>
rewrite (U_atom Ex 951 c1a); [| first [exact E951c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E951c] | clear - Hc1_rng HF4096 HFceil C1; lia];
eapply (obl_of_range trbsegs _ _ Ex (SOff bx 0) _ len (F + 8 * 4) (8 * 512));
[ exact HRAnl2
| rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear - Hc1_rng; lia | clear - Hc1_rng; lia ] end).
idtac "OK-OBL-NL".
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(fun nb => first
[ lazymatch nb with 950%nat =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 950%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E950c; apply unsigned_lit_small; clear - Hc0_rng HF4096 HFceil C1; lia | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; rewrite ?EFA3; fold F; clear - Ha Hc0_rng; lia | ] end
| lazymatch nb with 951%nat =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 951%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E951c; apply unsigned_lit_small; clear - Hc1_rng HF4096 HFceil C1; lia | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; rewrite ?EFA3; fold F; clear - Ha Hc1_rng; lia | ] end ]).
idtac "OK-AWR-NL".
m_run_keptG HFr AG (fun a : Z => (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ c0a <= a < c0a + 8 \/ c1a <= a < c1a + 8) Hceil Hslo FFS UN5.
clear HF HFr HG.
norm_ss HS.
idtac "OK-KEPT-NL2".
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
assert (HB950 : bv_unsigned (ew Ex 950) = c0a) by (assert (Rq : ew Ex 950 = Z_to_bv 64 c0a) by m_ewT; rewrite Rq; apply unsigned_lit_small; clear - Hc0_rng HF4096 HFceil C1; lia);
assert (HB951 : bv_unsigned (ew Ex 951) = c1a) by (assert (Rq : ew Ex 951 = Z_to_bv 64 c1a) by m_ewT; rewrite Rq; apply unsigned_lit_small; clear - Hc1_rng HF4096 HFceil C1; lia);
assert (R877z : ew Ex 877 = Z_to_bv 64 res0) by m_ewT; assert (R905z : ew Ex 905 = Z_to_bv 64 res1) by m_ewT;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 1 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 951%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 951 c1a cs lo hi wlo whi 0 8%N (SOff 905 0) res1 HRc HB951 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R905z) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hres1_rng) ltac:(cbn; lia)) as W1
end; clear HRc;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 2 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 950%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 950 c0a cs lo hi wlo whi 0 8%N (SOff 877 0) res0 HRc HB950 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R877z) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hres0_rng) ltac:(cbn; lia)) as W0
end; clear HRc end.
change (N.to_nat 8) with 8%nat in W0, W1. rewrite Z.add_0_r in W0, W1.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (tl (tl (tl (ss_mem ssx)))) in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
assert (HK4 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (F + 32 + 8 * mw <= a < F + 32 + 8 * mw + 16) -> aview trbsegs (w_H W3) (ms_mem ms1) a = aview trbsegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha1 Ha2 Ha3.
assert (Ha4 : ~ ((alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ c0a <= a < c0a + 8 \/ c1a <= a < c1a + 8))
by (subst c0a c1a; clear - Ha2 Ha3; lia).
rewrite (UN5 a Ha1 Ha4), (UN4 a Ha1 Ha4). exact (UN3 a Ha1 Ha2). }
idtac "OK-W01".
reshok_bx HS 44%nat.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
destruct (OKG (ms_mem msX) t0 t1 eq_refl eq_refl HK4 W0 W1) as (CINV' & HL' & Hq' & Hlen2 & HCLm' & Hlen_t' & Hmatch' & Hfacts' & Hown') end.
idtac "OK-OKG-ST5".
ga_join HS ss_ST5 952%nat (@nil (bv 5)) ltac:(idtac).
m_hand_ih RST5 HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, (csplit st El i1), (tns ++ [t0; t1]).
split; [split; [rewrite elen_app2; fold mw; clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown'|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact CINV'|].
split; [rewrite HL'; clear - HL254; lia|]. split; [exact Htail|].
split; [exact HCLm'|]. split; [exact Hlen_t'|]. split; [exact Hmatch'|]. split; [exact Hfacts'|]. split; [exact (MOKG t0 t1 eq_refl eq_refl)|].
split; [rewrite (tnth_app_l tns [t0; t1] 0 ltac:(clear - Hq_t; lia)); m_ewT|].
split; [rewrite Hq'; replace (q + 1 - 1) with q by (clear; lia); m_ewT|].
split; [rewrite HL'; replace (L + 1) with (L - 1 + 1 + 1) by (clear; lia); m_ewT|].
split; [rewrite Hq'; clear - Hq0n; lia|].
rewrite Hq'. clear - Hmeas. lia.
Qed.
End f.
End d.

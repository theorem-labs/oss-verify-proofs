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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCnk YCnj.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqj.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_CL1a : forall n, rga_from B ss_CLb (INV_CLb B (S n)) -> rga_from B ss_CLn (INV_CL B (S n)).
Proof.
intros n RCLb.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HCLm & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & R818 & Hmeas).
destruct Hk0 as [Hk0 Hbud].
unfold ss_CLn in HS.
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
assert (Hqlt : q < elen ns) by (apply (cinv_progress cnt ent st Hcinv); fold ns L; clear - HL254 HcntT; lia).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
m_add_cond HS BC_NE (SOff 817 0) (SLit 512)
ltac:(rewrite branch_ne_U, (U_atom E 817 q R817) by (clear - Hq0n Hqlt Hlen_ns HL254; lia); change (U E (SLit 512)) with 512;
apply Bool.negb_true_iff, Z.eqb_neq; clear - Hqlt Hlen_ns HL254; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x838d0.
idtac "OK-RUN1".
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
idtac "OK-RUN1b".
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
assert (Hzl : zlen (pal_bytes (c_E st) ++ tail) = 3 * T)
by (unfold zlen; rewrite length_app, Nat2Z.inj_add; change (Z.of_nat (length (pal_bytes (c_E st)))) with (zlen (pal_bytes (c_E st))); change (Z.of_nat (length tail)) with (zlen tail);
rewrite zlen_pal_bytes, Hlen_E; clear - Htail; lia).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HCLm1 : m_CLmem (w_H W3) (ms_mem msX) pp dn F tail st tns) end.
{ apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail st tns HCLm).
- intros i Hi. rewrite Hzl in Hi. pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Htail Hrq; lia)) as (Hq1 & Hq2). exact (UN0 _ Hq1 Hq2).
- intros i Hi. rewrite zlen_fr_vals, Hlen_E in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). exact (UN0 _ Hq1 Hq2).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2). exact (UN0 _ Hq1 Hq2).
- intros i Hi. apply UN0; [clear - Hi HFrng Hntns HFceil C1; lia | clear - Hi Hntns HFceil HdF_r HdF_tb; lia]. }
idtac "OK-CLM1".
set (tn := tnth tns q). set (nd := node ns q).
assert (Hq_t : 0 <= q < elen tns) by (rewrite Hlen_tns; fold ns; clear - Hq0n Hqlt; lia).
destruct (Hmatch q Hq_t) as (Mlo & Mhi & Mcol & Mwf & Mnz). fold tn ns nd in Mlo, Mhi, Mcol, Mwf, Mnz.
destruct HCLm1 as (CA1 & CA2 & CA3 & CA4).
pose proof (CA3 q Hq_t) as Hnm. unfold node_mem in Hnm. fold ns nd tn in Hnm.
assert (Hleaf : n_leaf nd = true) by (apply (cinv_unprocessed_leaf cnt ent st Hcinv q); fold q ns; clear - Hq0n Hqlt; lia).
rewrite Hleaf in Hnm. destruct Hnm as (c0 & c1 & Hobj).
destruct (m_node_fields _ _ c0 c1 tn 1 (proj1 (proj2 (proj2 (proj2 (proj2 Mwf))))) Hobj) as (Vmean & (Vimin & Rimin) & (Vimax & Rimax) & (Vcut & Rcut) & (Vcidx & Rcidx) & (Vleaf & _)).
pose proof (CA4 q Hq_t) as Vcell. fold tn in Vcell.
destruct (cinv_node cnt ent st Hcinv q ltac:(fold ns; clear - Hq0n Hqlt; lia)) as (Hnlo & Hnhi & _). fold ns nd in Hnlo, Hnhi.
set (va := tn_addr tn) in *.
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
assert (Hcell_rng : F + 32 <= F + 32 + 8 * q /\ F + 32 + 8 * q + 8 <= F + 4128) by (clear - Hq_t Hntns; lia).
idtac "OK-NODEFACTS".
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trbsegs 820%nat Ex ssx msx [Z_to_bv 64 (F + 32 + 8 * q); Z_to_bv 64 va; Z_to_bv 64 (n_lo nd); Z_to_bv 64 (n_hi nd); Z_to_bv 64 (tn_cut tn); Z_to_bv 64 (n_col nd); Z_to_bv 64 1]
HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
assert (E820 : ew (havoc E0v 820 vals) 820 = Z_to_bv 64 (F + 32 + 8 * q))
by (change 820%nat with (820 + 0)%nat at 2; rewrite (ew_havoc_new _ 820%nat vals 0%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E821 : ew (havoc E0v 820 vals) 821 = Z_to_bv 64 va)
by (change 821%nat with (820 + 1)%nat; rewrite (ew_havoc_new _ 820%nat vals 1%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E822 : ew (havoc E0v 820 vals) 822 = Z_to_bv 64 (n_lo nd))
by (change 822%nat with (820 + 2)%nat; rewrite (ew_havoc_new _ 820%nat vals 2%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E823 : ew (havoc E0v 820 vals) 823 = Z_to_bv 64 (n_hi nd))
by (change 823%nat with (820 + 3)%nat; rewrite (ew_havoc_new _ 820%nat vals 3%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E824 : ew (havoc E0v 820 vals) 824 = Z_to_bv 64 (tn_cut tn))
by (change 824%nat with (820 + 4)%nat; rewrite (ew_havoc_new _ 820%nat vals 4%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E825 : ew (havoc E0v 820 vals) 825 = Z_to_bv 64 (n_col nd))
by (change 825%nat with (820 + 5)%nat; rewrite (ew_havoc_new _ 820%nat vals 5%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E826 : ew (havoc E0v 820 vals) 826 = Z_to_bv 64 1)
by (change 826%nat with (820 + 6)%nat; rewrite (ew_havoc_new _ 820%nat vals 6%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
idtac "OK-HAVOC7".
assert (Hva_rng : 0 <= va < 2 ^ 64) by (clear - Hva4096 Hvaceil C1; lia).
assert (HFz : F + 8192 <= 2147446784 \/ 17594333495296 <= F) by (unfold gbox, in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg in HFhigh; clear - HFhigh; lia).
unfold gbox in HdFC.
assert (HFi : F + 8192 <= 65536 \/ 6156288 <= F) by (unfold gbox, off_img in HFhigh_img; clear - HFhigh_img; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 820%nat) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 821 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E820, unsigned_lit_small by (clear - Hcell_rng HF4096 HFceil C1; lia);
split; [clear - Hcell_rng HF4096; lia|]; split; [clear - Hcell_rng HFceil C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ (F + 32 + 8 * q) _ _ (SOff 821 0) va);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E821 | exact Hva_rng | cbn; clear; lia
| rewrite Z.add_0_r; exact Vcell] | apply Forall_nil] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hcell_rng HFceil Hceil Hslo FFS; lia
| clear - Hcell_rng HF8lo HF8hi HFq HF8 HFceil HFz C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - Hcell_rng; lia
| clear - Hcell_rng HFi; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - Hcell_rng HdFC Hflo Hfhi; lia
| clear - Hcell_rng HdF_r; lia
| clear - Hcell_rng HdF_tb; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
idtac "OK-CELLREG".
assert (Hvai : va + 56 <= 65536 \/ 6156288 <= va) by (clear - Hvazone; lia).
assert (Hvaz : va + 56 <= 2147446784 \/ 17594333495296 <= va) by (clear - Hvazone; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E820c : ew Ev 820 = Z_to_bv 64 (F + 32 + 8 * q)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E820);
assert (E821c : ew Ev 821 = Z_to_bv 64 va) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E821);
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 821%nat) 0 56 0 0 [YQ0b.mkChunk 40 (CVal 4 (SOff 822 0)); YQ0b.mkChunk 44 (CVal 4 (SOff 823 0)); YQ0b.mkChunk 48 (CVal 1 (SOff 824 0));
YQ0b.mkChunk 49 (CVal 1 (SOff 825 0)); YQ0b.mkChunk 50 (CVal 1 (SOff 826 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E821c, unsigned_lit_small by exact Hva_rng;
split; [clear - Hva4096; lia|]; split; [clear - Hvaceil C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| repeat (apply Forall_cons; [
lazymatch goal with
| |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk 40 _) => eapply (chunk_ok_val trbsegs Ev _ va 40 4 (SOff 822 0) (n_lo nd)); [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; exact E822 | rewrite <- Mlo; exact Rimin | cbn; clear; lia | rewrite <- Mlo; exact Vimin]
| |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk 44 _) => eapply (chunk_ok_val trbsegs Ev _ va 44 4 (SOff 823 0) (n_hi nd)); [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; exact E823 | rewrite <- Mhi; exact Rimax | cbn; clear; lia | rewrite <- Mhi; exact Vimax]
| |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk 48 _) => eapply (chunk_ok_val trbsegs Ev _ va 48 1 (SOff 824 0) (tn_cut tn)); [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; exact E824 | exact Rcut | cbn; clear; lia | exact Vcut]
| |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk 49 _) => eapply (chunk_ok_val trbsegs Ev _ va 49 1 (SOff 825 0) (n_col nd)); [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; exact E825 | rewrite <- Mcol; exact Rcidx | cbn; clear; lia | rewrite <- Mcol; exact Vcidx]
| |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk 50 _) => eapply (chunk_ok_val trbsegs Ev _ va 50 1 (SOff 826 0) 1); [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; exact E826 | cbn; clear; lia | cbn; clear; lia | exact Vleaf]
end |]); apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hva4096 Hvaceil Hceil Hslo FFS; lia
| clear - Hvaz HF8lo HF8hi HFq HF8 HFceil C1; unfold SB in *; lia
| clear - Hvai; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_va; lia
| clear - HdF_va Hcell_rng; lia
| clear - HdC_va Hflo Hfhi; lia
| clear - HzR_va; lia
| clear - HzT_va; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
idtac "OK-NODEREG".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HUA : U Ev (SAlu ALU_ADD (SOff 54 32) (SAlu ALU_SLL (SOff 817 0) (SLit 3))) = U Ev (SOff 820 0)) end.
{ lazymatch goal with |- U ?Ev _ = _ =>
rewrite (U_atom Ev 820 (F + 32 + 8 * q)) by first [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E820 | clear - Hcell_rng HF4096 HFceil C1; lia];
replace (F + 32 + 8 * q) with ((F + 32) + 8 * q) by (clear; lia);
apply U_add_small_q;
[ apply (U_atom_off Ev 54 F 32); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF | exact HFrng | clear - HF4096 HFceil C1; lia]
| replace (8 * q) with (q * 2 ^ 3) by (clear; lia); apply U_sll_small_q; [apply (U_atom Ev 817 q); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R817 | clear - Hq_t Hntns; lia] | clear - Hq_t; lia | clear; lia | clear - Hq_t Hntns; lia]
| clear - HF4096; lia | clear - Hq_t; lia | clear - Hcell_rng HFceil C1; lia ] end. }
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (10%bv : bv 5) (SOff 820 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (10%bv : bv 5) HS); change (sv_denot Ev (SOff 820 0) = sv_denot Ev e);
apply U_inj; symmetry; exact HUA)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 820%nat (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E820c, unsigned_lit_small by (clear - Hcell_rng HF4096 HFceil C1; lia); change (2 ^ 3) with 8;
split; [clear - Hcell_rng HF4096 HFceil C1; lia|]; split; [clear - HFq; rewrite HFq; replace (32 * (F / 32) + 32 + 8 * q) with ((4 * (F / 32) + 4 + q) * 8) by lia; apply Z_mod_mult | clear - Hcell_rng HFceil C1; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 821%nat (mkAF 4096 140737479966720 4) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E821c, unsigned_lit_small by exact Hva_rng; change (2 ^ 4) with 16;
split; [clear - Hva4096 Hvaceil C1; lia|]; split; [exact Hva16 | clear - Hvaceil C1; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
gboxh HFz. gboxh HFi. gboxh Hvai. gboxh Hvaz. gboxh HdF_va. gboxh HdC_va. gboxh HzR_va. gboxh HzT_va. gboxh HdF_r. gboxh HdF_tb. gboxh HdFC. gboxh Hvazone.
unfold NODE_SIZE in Hva_in3.
ga_ra_frame HS AG HFq F 4 4 512 HRAnl.
reshok_bx HS 44%nat.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HU821 : U Ev (SOff 821 0) = va)
by (apply (U_atom Ev 821 va); [first [exact E821 | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E821] | clear - Hva4096 Hvaceil C1; lia]) end.
m_add_cond HS BC_NE (SOff 821 0) (SLit 0)
ltac:(rewrite branch_ne_U, HU821; lazymatch goal with |- negb (_ =? U ?Ev (SLit 0)) = true => change (U Ev (SLit 0)) with 0 end;
apply Bool.negb_true_iff, Z.eqb_neq; clear - Hva4096; lia).
m_add_cond HS BC_EQ (SAlu ALU_AND (SOff 821 0) (SLit 7)) (SLit 0)
ltac:(eapply (ub_al_cond _ _ _ 3 HU821); [clear - Hva4096; lia | clear; lia |];
change (2 ^ 3) with 8; clear - Hva16; pose proof (Z.div_mod va 16 ltac:(lia)) as D; rewrite Hva16, Z.add_0_r in D; rewrite D;
replace (16 * (va / 16)) with ((2 * (va / 16)) * 8) by lia; apply Z_mod_mult).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x8393c.
all: try (m_obl_cell HJ3 E821c E44 Hva_in3 ltac:(idtac; first [exact Hva_rng | clear - Hva4096 Hvaceil C1; lia | clear; lia])).
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 820 0)) ?len =>
rewrite (U_atom Ex 820 (F + 32 + 8 * q)); [| first [exact E820c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E820c] | clear - Hcell_rng HF4096 HFceil C1; lia];
eapply (obl_of_range trbsegs _ _ Ex (SOff bx 0) _ len (F + 8 * 4) (8 * 512));
[ exact HRAnl
| rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear - Hcell_rng; lia | clear - Hcell_rng; lia ] end).
idtac "OK-OBL".
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 821 ?c)) ?len =>
rewrite (U_atom_off Ex 821 va c); [| first [exact E821c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E821c] | exact Hva_rng | clear - Hva4096 Hvaceil C1; lia];
eapply (obl_of_block trbsegs _ LAWS _ _ _ _ _ Ex (SOff bx 0) _ len va 56 (proj1 HJ3) Hva_in3);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear; lia | change (req_size 56) with 56; clear; lia ] end).
idtac "OK-OBL2".
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
reshok_bx HS 44%nat.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HCLmB : m_CLmem (w_H W3) (ms_mem msX) pp dn F tail st tns) end.
{ apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms) _ pp dn F tail st tns (conj CA1 (conj CA2 (conj CA3 CA4)))).
- intros i Hi. rewrite Hzl in Hi. pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). exact (UN1 _ Hq1 Hq2).
- intros i Hi. rewrite zlen_fr_vals, Hlen_E in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). exact (UN1 _ Hq1 Hq2).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
exact (UN1 _ Hq1 Hq2).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (unfold gbox in HdF_r, HdF_tb; clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
exact (UN1 _ Hq1 Hq2). }
ga_join HS ss_CLb 832%nat (@nil (bv 5)) ltac:(idtac).
m_hand_ih RCLb HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact HCLmB|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|].
split; [m_ewT|]. split; [m_ewT|].
split; [exact Hmeas|].
split; [exact Hqlt|].
split; [fold q tn va; m_ewT|].
split; [fold q ns nd; m_ewT|]. split; [fold q ns nd; m_ewT|].
fold q tn. m_ewT.
Qed.
End f.
End d.

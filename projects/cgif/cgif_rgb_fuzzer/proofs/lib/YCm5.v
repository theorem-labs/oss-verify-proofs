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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCnk YCnl YCnw YCnj.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02.
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
Lemma rga_CL1b : forall n, rga_from B ss_CLn (INV_CL B n) -> (forall pm, rga_from B ss_PL (INV_PL B (S n) pm)) -> rga_from B ss_CLb (INV_CLb B (S n)).
Proof.
intros n IH RPL.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HCLm & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & R818 & Hmeas & Hqlt0 & E821 & E822 & E823 & E824).
destruct Hk0 as [Hk0 Hbud].
unfold ss_CLb in HS.
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
pose proof HCLm as HCLm1.
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
fold q tn va in E821. fold q ns nd in E822, E823. fold q tn in E824. pose proof E821 as E821c.
assert (Hva_rng : 0 <= va < 2 ^ 64) by (clear - Hva4096 Hvaceil C1; lia).
assert (HFz : F + 8192 <= 2147446784 \/ 17594333495296 <= F) by (unfold gbox, in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg in HFhigh; clear - HFhigh; lia).
unfold gbox in HdFC.
assert (HFi : F + 8192 <= 65536 \/ 6156288 <= F) by (unfold gbox, off_img in HFhigh_img; clear - HFhigh_img; lia).
assert (Hvai : va + 56 <= 65536 \/ 6156288 <= va) by (clear - Hvazone; lia).
assert (Hvaz : va + 56 <= 2147446784 \/ 17594333495296 <= va) by (clear - Hvazone; lia).
gboxh HFz. gboxh HFi. gboxh Hvai. gboxh Hvaz. gboxh HdF_va. gboxh HdC_va. gboxh HzR_va. gboxh HzT_va. gboxh HdF_r. gboxh HdF_tb. gboxh HdFC. gboxh Hvazone.
unfold NODE_SIZE in Hva_in3.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
idtac "OK-BR1".
-
assert (Heq : n_lo nd = n_hi nd).
{ rewrite YO3v.branch_eq_U in Hc. apply Z.eqb_eq in Hc.
rewrite (U_sext32_small _ 823 (n_hi nd)) in Hc by first [ m_ewT | clear - Hnlo Hnhi HcntT HT24; lia ].
rewrite (U_sext32_small _ 822 (n_lo nd)) in Hc by first [ m_ewT | clear - Hnlo Hnhi HcntT HT24; lia ].
symmetry; exact Hc. }
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83d48.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
idtac "OK-BR2".
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x838ac.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HCLm2 : m_CLmem (w_H W3) (ms_mem msX) pp dn F tail (cskip st) tns) end.
{ lazymatch goal with |- m_CLmem ?Hh ?mm _ _ _ _ _ _ => change (m_CLmem Hh mm pp dn F tail st tns) end.
apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail st tns (conj CA1 (conj CA2 (conj CA3 CA4)))).
- intros i Hi. rewrite Hzl in Hi. pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2).
- intros i Hi. rewrite zlen_fr_vals, Hlen_E in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (unfold gbox in HdF_r, HdF_tb; clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2). }
idtac "OK-CLM2".
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rx17 : ew Ex 817 = Z_to_bv 64 q) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R817);
assert (Rx18 : ew Ex 818 = Z_to_bv 64 L) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R818) end.
assert (HUz16 : forall E' n0 v, ew E' n0 = Z_to_bv 64 v -> 0 <= v < 65536 -> U E' (SExt false 16 (SOff n0 0)) = v).
{ intros E' n0 v Hn Hv. rewrite U_SExt, (U_atom E' n0 v Hn) by (clear - Hv; lia). change (2 ^ Z.of_N 16) with 65536. rewrite Z.mod_small by exact Hv. apply zcanon_id. unfold M64. clear - Hv. lia. }
rregU HS (11%bv : bv 5) (q + 1) ltac:(rewrite (U_atom_off _ 817 q 1 Rx17) by (clear - Hq_t Hntns; lia); reflexivity) Q12.
slot_val HS (Some 2%nat) (-576) (-134) (Z_to_bv 64 L)
ltac:(rewrite denot_lit_U; f_equal; apply (U_atom _ 818 L Rx18); clear - HL1 HL254; lia) QS.
ra_join_slots HS ss_CLn2 1999%nat rga_deads_CLn2 [(Some 2%nat, (-576), (-134))]
ltac:(idtac; ga_join_val HS 1999%nat 18%nat Q12 E2017; ga_join_val HS 1999%nat 19%nat QS E2018;
c_pin HS (12%bv : bv 5) (SOff 2018 0)
ltac:(apply U_inj; transitivity L; [apply (U_atom _ 2018 L E2018); clear - HL1 HL254; lia
| symmetry; apply (HUz16 _ 818%nat L); [rewrite ew_havoc_old by lia; exact Rx18 | clear - HL1 HL254; lia]])).
idtac "OK-JOIN-A".
slot_val HS (Some 2%nat) (-576) (-134) (Z_to_bv 64 L)
ltac:(rewrite denot_lit_U; f_equal; apply (U_atom _ 2018 L E2018); clear - HL1 HL254; lia) QS2.
m_join_slots_win HS ss_CLn 799%nat rga_deads_CLn [(Some 2%nat, (-576), (-134))]
ltac:(idtac; ga_join_val HS 799%nat 18%nat Q12 N817; ga_join_val HS 799%nat 19%nat QS2 N818;
c_pin HS (12%bv : bv 5) (SOff 818 0)
ltac:(apply U_inj; transitivity L; [apply (U_atom _ 818 L N818); clear - HL1 HL254; lia
| symmetry; apply (U_atom _ 2018 L); [m_ewT | clear - HL1 HL254; lia]])).
idtac "OK-JOIN-B".
m_hand_ih IH HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, (cskip st), tns.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [apply (cskip_inv cnt ent st Hcinv); [fold q ns; exact Hqlt | fold q ns nd; exact Heq]|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact HCLm2|]. split; [exact Hlen_tns|]. split; [exact Hmatch|].
split; [intros j Hj; apply Hfacts; cbn [cskip c_q] in Hj; fold q in Hj |- *; clear - Hj; lia|]. split; [exact MOK|].
split; [m_ewT|].
split; [exact N817|]. split; [exact N818|].
cbn [cskip c_q]. fold q. clear - Hmeas. lia.
+
exfalso. rewrite YO3v.branch_ltu_U in Hc0. apply Z.ltb_ge in Hc0.
rewrite U_SExt, (U_atom _ 818 L) in Hc0 by first [m_ewT | clear - HL1 HL254; lia].
rewrite U_SLit in Hc0. change (2 ^ Z.of_N 16) with 65536 in Hc0. rewrite Z.mod_small in Hc0 by (clear - HL1 HL254; lia).
rewrite (zcanon_id L) in Hc0 by (unfold M64; clear - HL1 HL254; lia). change (zcanon 255) with 255 in Hc0. clear - Hc0 HL254. lia.
-
assert (Hlt : n_lo nd < n_hi nd).
{ rewrite YO3v.branch_eq_U in Hc. apply Z.eqb_neq in Hc.
rewrite (U_sext32_small _ 823 (n_hi nd)) in Hc by first [ m_ewT | clear - Hnlo Hnhi HcntT HT24; lia ].
rewrite (U_sext32_small _ 822 (n_lo nd)) in Hc by first [ m_ewT | clear - Hnlo Hnhi HcntT HT24; lia ].
clear - Hc Hnlo. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83944.
idtac "OK-RUN5".
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
idtac "OK-BR3".
+ exfalso. rewrite YO3v.branch_geu_U in Hc0. apply Bool.negb_true_iff in Hc0. apply Z.ltb_ge in Hc0.
rewrite (U_sext32_small _ 823 (n_hi nd)) in Hc0 by first [ m_ewT | clear - Hnlo Hnhi HcntT HT24; lia ].
rewrite (U_sext32_small _ 822 (n_lo nd)) in Hc0 by first [ m_ewT | clear - Hnlo Hnhi HcntT HT24; lia ].
clear - Hc0 Hlt. lia.
+
assert (Hpp_in3e : In (pp, 3 * T) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hpp_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * T) HAR3 Hpp_in3e) as (Hpp4096e & _ & Hppceile & _).
pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq3Te.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rx22p : ew Ev 822 = Z_to_bv 64 (n_lo nd)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E822);
assert (Rx24p : ew Ev 824 = Z_to_bv 64 (tn_cut tn)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E824);
assert (HUlo : U Ev (SExt true 32 (SOff 822 0)) = n_lo nd) by (apply (U_sext32_small Ev 822 _ Rx22p); clear - Hnlo Hnhi HcntT HT24; lia);
assert (HUcut : U Ev (SExt false 8 (SOff 824 0)) = tn_cut tn)
by (rewrite U_SExt, (U_atom Ev 824 _ Rx24p) by (clear - Rcut; lia); change (2 ^ Z.of_N 8) with 256; rewrite Z.mod_small by (clear - Rcut; lia);
apply zcanon_id; unfold M64; clear - Rcut; lia);
assert (HU3lo : U Ev (SAlu ALU_ADD (SAlu ALU_SLL (SExt true 32 (SOff 822 0)) (SLit 1)) (SExt true 32 (SOff 822 0))) = 3 * n_lo nd)
by (replace (3 * n_lo nd) with (n_lo nd * 2 ^ 1 + n_lo nd) by (clear; lia);
apply U_add_small_q; [apply U_sll_small_q; [exact HUlo | clear - Hnlo; lia | clear; lia | clear - Hnlo Hnhi HcntT HT24; lia] | exact HUlo
| clear - Hnlo; lia | clear - Hnlo; lia | clear - Hnlo Hnhi HcntT HT24; lia]);
assert (HUzx : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SExt true 32 (SOff 822 0)) (SLit 1)) (SExt true 32 (SOff 822 0))) (SExt false 8 (SOff 824 0))) (SLit 32)) (SLit 32)) = 3 * n_lo nd + tn_cut tn)
by (apply U_zext32_shifts; [apply U_add_small_q; [exact HU3lo | exact HUcut | clear - Hnlo; lia | clear - Rcut; lia | clear - Hnlo Hnhi HcntT HT24 Rcut; lia]
| clear - Hnlo Hnhi HcntT HT24 Rcut; lia]);
assert (HUppe : U Ev (SOff 618 0) = pp)
by (apply (U_atom Ev 618 pp); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | clear - Hpp4096e Hppceile Hrq3Te C1; lia]) end.
lazymatch type of HUzx with U ?Ev ?ZX = _ =>
assert (HUX : U Ev (SAlu ALU_ADD ZX (SOff 618 0)) = 3 * n_lo nd + tn_cut tn + pp)
by (apply U_add_small_q; [exact HUzx | exact HUppe | clear - Hnlo Rcut; lia | clear - Hpp4096e; lia | clear - Hnlo Hnhi HcntT HT24 Rcut Hppceile Hrq3Te C1; lia]);
m_add_cond HS BC_GEU (SAlu ALU_ADD ZX (SOff 618 0)) (SOff 618 0) ltac:(eapply (ub_geu_cond _ _ _ _ _ HUX HUppe); clear - Hnlo Rcut; lia) end.
lazymatch type of HUX with U ?Ev ?X = _ =>
m_add_cond HS BC_NE (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU X (SLit 1))) (SLit 0) ltac:(eapply (ub_nz_cond _ _ _ HUX); clear - Hnlo Rcut Hpp4096e; lia) end.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x839b8.
idtac "OK-RUN6".
1: { lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 821 48)) ?len =>
rewrite (U_atom_off Ex 821 va 48) by first [exact E821c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E821c | clear - Hva4096 Hvaceil C1; lia];
eapply (obl_of_block trbsegs _ LAWS _ _ _ _ _ Ex (SOff bx 0) _ len va 56 (proj1 HJ3) Hva_in3);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E44 | unfold SB; lia]
| clear; lia | change (req_size 56) with 56; clear; lia ] end. }
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
idtac "OK-RUN6b".
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HCLm3 : m_CLmem (w_H W3) (ms_mem msX) pp dn F tail (mkC (c_E st) (c_ns st) (c_q st)) tns) end.
{ lazymatch goal with |- m_CLmem ?Hh ?mm _ _ _ _ _ _ => change (m_CLmem Hh mm pp dn F tail st tns) end.
apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail st tns (conj CA1 (conj CA2 (conj CA3 CA4)))).
- intros i Hi. rewrite Hzl in Hi. pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2).
- intros i Hi. rewrite zlen_fr_vals, Hlen_E in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (unfold gbox in HdF_r, HdF_tb; clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
rewrite (UN3 _ Hq1 Hq2). exact (UN2 _ Hq1 Hq2). }
idtac "OK-CLM3".
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rx22 : ew Ex 822 = Z_to_bv 64 (n_lo nd)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E822);
assert (Rx23 : ew Ex 823 = Z_to_bv 64 (n_hi nd)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E823) end.
rregU HS (21%bv : bv 5) (n_hi nd) ltac:(apply (U_sext32_small _ 823 _ Rx23); clear - Hnlo Hnhi HcntT HT24; lia) Q21.
rregU HS (18%bv : bv 5) (n_lo nd) ltac:(apply (U_sext32_small _ 822 _ Rx22); clear - Hnlo Hnhi HcntT HT24; lia) Q18.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rx24 : ew Ex 824 = Z_to_bv 64 (tn_cut tn)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E824) end.
assert (Hlo29 : 0 <= n_lo nd < 2 ^ 29) by (clear - Hnlo Hnhi HcntT HT24; lia).
ga_join HS ss_PL 842%nat rga_deads_PL
ltac:(idtac; ga_join_val HS 842%nat 15%nat Q21 N857; ga_join_val HS 842%nat 16%nat Q18 N858;
c_pin HS (24%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 858 0) (SLit 1)) (SOff 858 0))
ltac:(apply U_inj; transitivity (3 * n_lo nd);
[ apply c_U3x; [apply (U_atom _ 858 _ N858); clear - Hlo29; lia | exact Hlo29]
| symmetry; apply c_U3x; [apply (U_sext32_small _ 822); [rewrite ew_havoc_old by lia; exact Rx22 | clear - Hlo29; lia] | exact Hlo29] ]);
c_pin HS (11%bv : bv 5) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 858 0) (SLit 1)) (SOff 858 0)) (SExt false 8 (SOff 824 0))) (SLit 32)) (SLit 32))
ltac:(apply U_inj; transitivity (3 * n_lo nd + tn_cut tn);
[ apply c_Uoff; [apply c_U3x; [apply (U_atom _ 858 _ N858); clear - Hlo29; lia | exact Hlo29] | apply (c_Uz8 _ 824); [rewrite ew_havoc_old by lia; exact Rx24 | clear - Rcut; lia] | clear - Hlo29; lia | clear - Rcut; lia]
| symmetry; apply c_Uoff; [apply c_U3x; [apply (U_sext32_small _ 822); [rewrite ew_havoc_old by lia; exact Rx22 | clear - Hlo29; lia] | exact Hlo29] | apply (c_Uz8 _ 824); [rewrite ew_havoc_old by lia; exact Rx24 | clear - Rcut; lia] | clear - Hlo29; lia | clear - Rcut; lia] ])).
idtac "OK-JOIN-PL".
assert (HEokc : ent_ok (c_E st)) by (exact (ent_ok_perm _ _ HpermE HentOk)).
assert (Hseg : zsub (c_E st) (n_lo nd) (n_hi nd) = n_seg nd) by (apply (cinv_seg cnt ent st Hcinv q); fold q ns; clear - Hq0n Hqlt; lia).
assert (HPI : pinv dentry (Ptest (tn_cut tn) (wsum (dseg (tn_cut tn) (c_E st) (n_lo nd) (n_hi nd))) (wdot (dseg (tn_cut tn) (c_E st) (n_lo nd) (n_hi nd))))
(n_lo nd) (n_hi nd) (c_E st) (c_E st) (n_lo nd) (n_hi nd)).
{ apply (pinv_start (c_E st) (n_lo nd) (n_hi nd) (tn_cut tn) HEokc ltac:(clear - Hnlo; lia) ltac:(clear - Hnlo; lia) ltac:(rewrite Hlen_E; exact Hnhi)).
rewrite dseg_segd, Hseg. apply (proj2 (Hfacts q ltac:(fold q; clear - Hq_t; lia))). fold ns nd. exact Hlt. }
pose proof (pinv_meas_bound dentry _ _ _ _ _ _ _ HPI) as HPM.
m_hand_ih (RPL (Datatypes.S (Z.to_nat (2 * (n_hi nd - n_lo nd) + 2)))) HS HJ3 k; [rga_E_tac HEE0 | ].
idtac "OK-HAND-PL".
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns, (c_E st), (n_lo nd), (n_hi nd).
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact HCLm3|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exact Hmeas|].
split; [exact Hqlt|].
split; [fold q ns nd; exact Hlt|].
split; [fold q tn va; m_ewT|].
split; [exact N857|]. split; [exact N858|].
split; [fold q tn; m_ewT|].
fold q ns nd tn. cbv zeta. split; [exact HPI|]. clear - HPM. lia.
Qed.
End d.
End c.

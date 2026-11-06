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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCni YCnb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCop YCne YCng YCoc YCod.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YCj8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis NTN2 : tntn_spec2V B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_ST2 : forall n, rga_fromA B ss_ST3 (fun _ => INV_ST3 B n) -> rga_from B ss_ST2 (INV_ST2 B n).
Proof.
intros n RST3.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & El & i1 & k0 & res0 & c0 & c1 & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HSTm & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & Hmeas & Hqlt & Hlt & R821 & R866 & R870 & R871 & R872 &
(P & Hdone) & R877 & R900 & Hkid0).
destruct Hk0 as [Hk0 Hbud].
unfold ss_ST2 in HS.
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
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx T ++ [(dn, 4 * cnt)] ++ m_node_blocks (tns ++ k0)).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz ->
0 <= a < 2 ^ 64 /\ ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq.
destruct Hq as [Hq1 Hq2]. split; [exact Hq1|]. intros Hc. apply Hq2. unfold m_ZsP. clear - Hc. lia. }
assert (Hpp_l : In (pp, 3 * T) lrest) by (subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); left; cbn [cht_blocks In]; tauto).
assert (Hdn_l : In (dn, 4 * cnt) lrest) by (subst lrest; apply in_or_app; right; right; right; cbn [app]; apply (in_or_app (cht_blocks fq hh uu pp xx T)); right; left; reflexivity).
assert (Hnode_lx : forall t, In t (tns ++ k0) -> In (tn_addr t, NODE_SIZE) lrest)
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
destruct (al_blocks _ _ LAWS _ _ _ _ _ va NODE_SIZE (proj1 HJ3) Hva_in3) as (_ & _ & _ & _ & Hvapres2 & _). change (req_size NODE_SIZE) with 56 in Hvapres2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E821c : ew Ev 821 = Z_to_bv 64 va) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R821);
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 821%nat) 0 8 0 8 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E821c, unsigned_lit_small by exact Hva_rng;
split; [clear - Hva4096; lia|]; split; [clear - Hvaceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hvapres2 (va + o) ltac:(clear - Ho; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hva4096 Hvaceil Hceil Hslo FFS; lia
| clear - Hvaz HF8lo HF8hi HFq HF8 HFceil C1; unfold SB in *; lia
| clear - Hvai; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_va; lia
| clear - HdC_va Hflo Hfhi; lia
| clear - HzR_va; lia
| clear - HzT_va; lia
| clear; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
gboxh HFz. gboxh HFi. gboxh Hvai. gboxh Hvaz. gboxh HdF_va. gboxh HdC_va. gboxh HzR_va. gboxh HzT_va. gboxh HdF_r. gboxh HdF_tb. gboxh HdFC. gboxh Hvazone.
unfold NODE_SIZE in Hva_in3.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_new_tree_node.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 821 ?c)) ?len =>
rewrite (U_atom_off Ex 821 va c); [| first [exact E821c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E821c] | exact Hva_rng | clear - Hva4096 Hvaceil C1; lia];
eapply (obl_of_block trbsegs _ LAWS _ _ _ _ _ Ex (SOff bx 0) _ len va 56 (proj1 HJ3) Hva_in3);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear; lia | change (req_size 56) with 56; clear; lia ] end).
pose proof (proj2 (Hown tn (Htns_in q Hq_t))) as Ava. fold va in Ava. cbn [c_regs] in Ava. unfold rgc_FPs in Ava. cbn [c_r c_ly c_S] in Ava.
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(m_awr_cell 821%nat E821c va Ava Hva_in3 ltac:(idtac; first [exact Hva_rng | clear - Hva4096 Hvaceil C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => change (req_size NODE_SIZE) with 56; clear - Ha; lia end])).
m_run_keptG HFr AG (fun a : Z => (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ va <= a < va + 8 \/ va + 50 <= a < va + 51) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
assert (Hpp_in3 : In (pp, 3 * T) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hpp_l]).
assert (Hdn_in3 : In (dn, 4 * cnt) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hdn_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * T) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * cnt) HAR3 Hdn_in3) as (Hdn4096 & _ & Hdnceil & Hdn16).
pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq3T.
pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq4c.
assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx T ++ ((dn, 4 * cnt) :: m_node_blocks (tns ++ k0) ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
assert (Hva_n : In (va, NODE_SIZE) (m_node_blocks (tns ++ k0))) by (unfold m_node_blocks; apply in_map_iff; exists tn; split; [reflexivity | apply in_or_app; left; exact (Htns_in q Hq_t)]).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * T) (dn, 4 * cnt) HAR3 HPx ltac:(cbn [cht_blocks In]; tauto) ltac:(left; reflexivity)) as Hpd.
unfold zdisjoint, block_rng in Hpd. cbn [fst snd] in Hpd.
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * T) (va, NODE_SIZE) HAR3 HPx ltac:(cbn [cht_blocks In]; tauto) ltac:(right; apply in_or_app; left; exact Hva_n)) as Hs_pq.
unfold zdisjoint, block_rng in Hs_pq. cbn [fst snd] in Hs_pq. change (req_size NODE_SIZE) with 56 in Hs_pq.
assert (HPy : Permutation (ablocks B ly3 S3) ((dn, 4 * cnt) :: (m_node_blocks (tns ++ k0) ++ cht_blocks fq hh uu pp xx T ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (dn, 4 * cnt) _ (va, NODE_SIZE) HAR3 HPy ltac:(apply in_or_app; left; exact Hva_n)) as Hs_dq.
unfold zdisjoint, block_rng in Hs_dq. cbn [fst snd] in Hs_dq. change (req_size NODE_SIZE) with 56 in Hs_dq.
assert (HPn : Permutation (ablocks B ly3 S3) (m_node_blocks (tns ++ k0) ++ ((dn, 4 * cnt) :: cht_blocks fq hh uu pp xx T ++ (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
assert (Hs_nn : forall j, 0 <= j < elen tns -> j <> q -> tn_addr (tnth tns j) + 56 <= va \/ va + 56 <= tn_addr (tnth tns j)).
{ intros j Hj Hne. assert (Hel : elen (tns ++ k0) = elen tns + elen k0) by (unfold elen; rewrite length_app; clear; lia).
pose proof (m_sep_nodes B LAWS ly3 S3 _ _ _ (tns ++ k0) _ j q HAR3 HPn ltac:(rewrite Hel; clear - Hj Hk01; lia) ltac:(rewrite Hel; clear - Hq_t Hk01; lia) Hne) as Hsn.
rewrite !tnth_app_l in Hsn by assumption. exact Hsn. }
assert (KU1 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) -> ~ (va <= a < va + 8) -> ~ (va + 50 <= a < va + 51) ->
aview trbsegs (w_H W3) (ms_mem ms) a = aview trbsegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha1 Ha2 Ha3 Ha4; apply UN1; [exact Ha1 | clear - Ha2 Ha3 Ha4; tauto]).
assert (Hpal1 : arr8 trbsegs (mrestrict (w_H W3) (ms_mem ms)) pp (pal_bytes El ++ tail)).
{ apply (arr8_frame trbsegs _ _ pp _ CA1). intros a Ha. rewrite Hzl in Ha. apply (mbyte_of_aview trbsegs).
destruct (Hoff3 pp _ Hpp_l a ltac:(clear - Ha Hrq3T; lia)) as (Hq1 & Hq2). apply (KU1 _ Hq1 Hq2); clear - Ha Hs_pq Hrq3T; lia. }
assert (Hdense1 : arr32 trbsegs (mrestrict (w_H W3) (ms_mem ms)) dn (fr_vals El)).
{ apply (arr32_frame trbsegs _ _ dn _ CA2). intros a Ha. rewrite zlen_fr_vals, HlenEl in Ha. apply (mbyte_of_aview trbsegs).
destruct (Hoff3 dn _ Hdn_l a ltac:(clear - Ha Hrq4c; lia)) as (Hq1 & Hq2). apply (KU1 _ Hq1 Hq2); clear - Ha Hs_dq Hrq4c; lia. }
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
assert (HB2x : bv_unsigned (ew Ex 2) = spZ regs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp);
assert (R900x : ew Ex 900 = Z_to_bv 64 (L - 1 + elen k0)) by m_ewT;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 10 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-134) 2%N (SOff 900 0) (L - 1 + elen k0) HRc HB2x ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R900x) ltac:(cbn; clear - HL1 HL254 Hk01; lia) ltac:(cbn; lia)) as Vnln
end; clear HRc end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnln.
m_drop_chunk HS 2%nat (-134).
assert (Hpag : pal_agrees (pal_bytes El ++ tail) El) by (apply pal_agrees_app).
assert (HsumEl : zsum (fr_vals El) <= N) by (rewrite (zsum_fr_perm _ _ (Permutation_trans HpermE PDperm)); exact Hsum).
assert (Hcnt24 : cnt < 16777216) by (clear - HcntT HT24; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rpp1 : ew Ex 618 = Z_to_bv 64 pp) by m_ewT; assert (Rdn1 : ew Ex 626 = Z_to_bv 64 dn) by m_ewT;
assert (R871x : ew Ex 871 = Z_to_bv 64 hi) by m_ewT; assert (R900y : ew Ex 900 = Z_to_bv 64 (L - 1 + elen k0)) by m_ewT;
assert (R866x : ew Ex 867 = Z_to_bv 64 i1) by m_ewT end.
assert (Hcol : 0 <= L - 1 + elen k0 < 256) by (clear - HL1 HL254 Hk01; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) pp ltac:(apply (U_atom _ 618 pp Rpp1); clear - Hpp4096 Hppceil Hrq3T C1; lia) Ha0.
rregU HS (11%bv : bv 5) dn ltac:(apply (U_atom _ 626 dn Rdn1); clear - Hdn4096 Hdnceil Hrq4c C1; lia) Ha1.
rregU HS (12%bv : bv 5) (spZ regs - 134) ltac:(rewrite (U_atom_off _ 2 (spZ regs) (-134)) by first [rewrite <- HB2x; symmetry; apply Z_to_bv_bv_unsigned | clear - Hceil Hslo Hshi H47 FFS C1; lia]; clear; lia) Ha2.
rregU HS (13%bv : bv 5) i1 ltac:(apply (U_atom _ 867 i1 R866x); clear - Ki1 Ki3 Hnlo Hnhi Hcnt24; lia) Ha3.
rregU HS (14%bv : bv 5) hi ltac:(apply (U_sext32_small _ 871 _ R871x); clear - Hnlo Hnhi Hcnt24; lia) Ha4.
rregU HS (15%bv : bv 5) (L - 1 + elen k0) ltac:(apply (m_U_zext8_small _ 900 _ R900y); exact Hcol) Ha5.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
change (Z_to_bv 64 545716) with (Z_to_bv 64 A_new_tree_node).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (NTN2 fx TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
pp dn (spZ regs - 134) i1 hi (L - 1 + elen k0) (L - 1 + elen k0) (pal_bytes El ++ tail) (fr_vals El) pp (3 * T) dn (4 * cnt) HJ3) end.
- rewrite Rra. apply ret_ok_even; vm_compute; reflexivity.
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear; lia). clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- rewrite HspT. clear - Hal32. pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (spZ regs / 32) + -576) with ((2 * (spZ regs / 32) - 36) * 16) by lia. apply Z_mod_mult.
- rewrite HspT, FFS. unfold TNTN_STK, NTN_FRAME, ASTACK. clear. lia.
- rewrite HspT. clear. lia.
- exact Hfrm.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- exact Ha3.
- exact Ha4.
- exact Ha5.
- exact Hpp_in3.
- clear; lia.
- rewrite Hzl. clear; lia.
- exact Hdn_in3.
- clear; lia.
- rewrite zlen_fr_vals, HlenEl. clear; lia.
- clear - Hdn16. pose proof (Z.div_mod dn 16 ltac:(lia)) as D. rewrite Hdn16, Z.add_0_r in D. rewrite D. replace (16 * (dn / 16)) with ((4 * (dn / 16)) * 4) by lia. apply Z_mod_mult.
- intros Heq. injection Heq as Hq1 Hq2. clear - Hq1 Hpd Hrq3T Hrq4c. lia.
- exact Hpal1.
- exact Hdense1.
- clear - Ki1 Ki3 Hnlo. lia.
- clear - Ki4 HlenEl Hcnt24. lia.
- rewrite Hzl. assert (Htl0 : 0 <= zlen tail) by (unfold zlen; clear; lia). clear - Ki4 HlenEl Htail Htl0. lia.
- rewrite zlen_fr_vals, HlenEl. clear - Ki4 HlenEl. lia.
- exact Hcol.
- intros i Hi. exact (proj1 (m_fr_bounds El N i HEokl HsumEl ltac:(rewrite HlenEl; clear - Hi Hnlo Ki1 Ki4 HlenEl; lia))).
- rewrite (node_list_dseg (pal_bytes El ++ tail) El i1 hi 0 Hpag) by (rewrite ?HlenEl; clear - Hnlo Ki1 Ki3 Ki4 HlenEl; lia).
pose proof (proj1 (proj2 (Kw 0))) as [_ Kw0]. rewrite <- (zsum_fr_perm _ _ HpermE) in Hsum. clear - Kw0 Hsum HN. unfold RGB_NMAX in *. lia.
- rewrite HspT. clear; lia.
- clear; lia.
- clear - Hal32. pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (spZ regs / 32) - 134) with (2 + (4 * (spZ regs / 32) - 17) * 8) by lia. rewrite Z_mod_plus_full. reflexivity.
- replace (spZ regs - 134) with (spZ regs + -134) by (clear; lia). exact Vnln.
- clear - HL1 HL254 Hk01. lia.
- rga_room Hev Hbud; (try (unfold EV_NTN); clear - Hk0 HEVv Hntns; try (unfold EV_HD in Hk0); rga_lia).
- rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPm3), !bsum_app, <- (blocks_bytes_bsum B ly S), m_bsum_node_blocks. cbn [bsum fold_right snd cht_blocks]. assert (Hel2 : elen (tns ++ k0) = elen tns + elen k0) by (unfold elen; rewrite length_app; clear; lia). rewrite Hel2.
clear - Hlive HfN HN1 HN HT24 Hcnt24 HcntT Hntns Hk01. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX, NODE_SIZE in *. lia. }
cbv beta. intros W7 c7 Hwle7 (fx7 & ly7 & S7 & regs7 & mem7 & md7 & res & -> & Hfrm7 & HJ7 & HP7 & Hfrs7 & Hd7 & Ha07 & HK7 & Hres7).
rewrite Rra.
clear Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (HBin7 : forall b m, In (b, m) (ablocks B ly3 S3) -> In (b, m) (ablocks B ly7 S7))
by (intros b m Hb; destruct Hres7 as [(_ & -> & _) | (_ & -> & _)]; [exact Hb | apply in_or_app; left; exact Hb]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 (HBin7 _ _ Hrin3)) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 (HBin7 _ _ Htb_in3)) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ va 56 HAR7 (HBin7 _ _ Hva_in3)) as (_ & _ & _ & _ & Hvapres7 & _). change (req_size 56) with 56 in Hvapres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HRNG : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling) /\ (4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\
spZ (ms_regs ms) = spZ regs + -576 /\ TNTN_STK = 16576 /\ TRGBADD_STK = 25152).
{ split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8; lia|]. split; [clear - Hr4096 Hrceil; lia|]. split; [clear - Hf4096 Hfceil Hflo Hfhi; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; [exact HspT | split; reflexivity]. }
assert (HRtb : 4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs) by (clear - Htb4096 Htbceil Hrqtb Hceil Hslo FFS C1; lia).
assert (HRr : 4096 <= r /\ r + 64 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs) by (clear - Hr4096 Hrceil Hceil Hslo FFS C1; lia).
assert (HRva : 4096 <= va /\ va + 56 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs) by (clear - Hva4096 Hvaceil Hceil Hslo FFS C1; lia).
m_reseatF HS HJ7 fx7 regs7 CLOB 539764 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17]%nat AG (m_same_of_preserved _ _ HP7)
ltac:(idtac; first
[ m_keptE HK7 HJ7 HRNG AG Usp RF E67 E10n E11n Hfin3 HfinS3 EFA3 F (-134) (-132) HFpres7 HFSpres7
ltac:(idtac; first [ m_keptE_blk HK7 AG 305%nat tb 48 Rtb Htb_in3 Htbpres7 HRtb
| m_keptE_blk HK7 AG 10%nat r 64 E10n Hrin3 Hrpres7 HRr
| m_keptE_blk HK7 AG 821%nat va 56 E821c Hva_in3 Hvapres7 HRva
| m_keptE_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
rreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite Ha07 in Rres. symmetry in Rres. unfold w64 in Rres.
norm_ss HS.
assert (HEndl : List.NoDup (map fst El)) by (exact (NoDup_fst_perm _ _ (Permutation_trans HpermE PDperm) HentND)).
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (HK1 : exists (k1 : list tnode), val_mem trbsegs (mrestrict (w_H W7) mem7) (spZ regs - 134) 2 (L - 1 + elen k0 + elen k1) /\
ablocks B ly7 S7 = ablocks B ly3 S3 ++ m_node_blocks k1 /\ 0 <= elen k1 <= 1 /\
m_kid_ok B cxv (w_H W7) mem7 k1 res i1 hi (L - 1 + elen k0) (zsub El i1 hi)) end.
{ destruct Hres7 as [(Hz & Ebl7 & Vn) | (Hres4096 & Ebl7 & Vn & nd0 & Hnd_addr & Hnd_imin & Hnd_imax & Hnd_cidx & Hnd_tree & Hnd_wf & Hnd_quot & Hnd_split)].
- exists []. change (elen (@nil tnode)) with 0. rewrite Z.add_0_r. split; [exact Vn|]. split; [rewrite Ebl7; cbn [m_node_blocks map]; rewrite app_nil_r; reflexivity|]. split; [clear; lia | exact Hz].
- exists [nd0]. change (elen [nd0]) with 1. split; [exact Vn|]. split; [rewrite Ebl7; unfold m_node_blocks; cbn [map]; rewrite Hnd_addr; reflexivity|]. split; [clear; lia|].
cbn [m_kid_ok]. split; [symmetry; exact Hnd_addr|]. split; [rewrite Hnd_addr; clear - Hres4096; lia|]. split; [exact Hnd_imin|]. split; [exact Hnd_imax|]. split; [exact Hnd_cidx|]. split; [exact Hnd_wf|].
split; [exact (proj2 (proj2 Hnd_tree))|].
split.
{ apply (tn_facts_intro (pal_bytes El ++ tail) El i1 hi nd0 _ Hpag HEokl HEndl); cbn [n_lo n_hi n_seg];
[ clear - Hnlo Ki1; lia | exact Ki3 | exact Ki4 | reflexivity | reflexivity | reflexivity | exact (proj1 Hnd_wf) | exact Hnd_quot | exact Hnd_split ]. }
rewrite Hnd_addr. split.
+ exact (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res NODE_SIZE HJ3 HAR7 Ebl7 ltac:(unfold NODE_SIZE; clear; lia)).
+ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res NODE_SIZE blc i lyq ownq HJ3 HAR7 Ebl7 ltac:(unfold NODE_SIZE; clear; lia) Hbl Hi). }
destruct HK1 as (k1 & Vnl & Ebl7 & Hk11 & Hkid1).
assert (HK37 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W7) (ms_mem ms) mem7 b (req_size sz)).
{ intros b sz Hb i Hi.
assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hb]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b sz HAR3 Hb3) as (_ & _ & Hbceil & _).
apply (proj1 (proj2 HK7) b sz i Hb3 Hi). clear - Hi Hbceil Hceil Hslo FFS. lia. }
assert (HKva : forall i, 8 <= i < 56 -> i <> 50 -> aview trbsegs (w_H W7) mem7 (va + i) = aview trbsegs (w_H W3) (ms_mem ms3) (va + i)).
{ intros i Hi Hne. rewrite (HK37 va _ Hva_l i ltac:(change (req_size NODE_SIZE) with 56; clear - Hi; lia)).
destruct (Hoff3 va _ Hva_l (va + i) ltac:(change (req_size NODE_SIZE) with 56; clear - Hi; lia)) as (Hq1 & Hq2). apply (KU1 _ Hq1 Hq2); clear - Hi Hne; lia. }
pose proof (obj_at_nth trbsegs _ va LAY_Node _ 1%nat (8, 8%N) c1 Hobj eq_refl eq_refl) as [Vc1 Rc1].
cbn [fst snd] in Vc1, Rc1. change (N.to_nat 8) with 8%nat in Vc1.
assert (Hres0_rng : 0 <= res0 < 2 ^ 64).
{ destruct k0 as [|t0 [|t1 l0]]; cbn [m_kid_ok] in Hkid0; [rewrite Hkid0; clear; lia | | contradiction].
destruct Hkid0 as (Hr0 & _). rewrite Hr0.
assert (Ht0_3 : In (tn_addr t0, NODE_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hnode_lx; apply in_or_app; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ _ NODE_SIZE HAR3 Ht0_3) as (Ht4096 & _ & Htceil & _). change (req_size NODE_SIZE) with 56 in Htceil. clear - Ht4096 Htceil C1. lia. }
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
assert (HB821 : bv_unsigned (ew Ex 821) = va) by (assert (Rq : ew Ex 821 = Z_to_bv 64 va) by m_ewT; rewrite Rq; apply unsigned_lit_small; exact Hva_rng);
assert (R877y : ew Ex 877 = Z_to_bv 64 res0) by m_ewT;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W7) msX) 0 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 821%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 821 va cs lo hi wlo whi 0 8%N (SOff 877 0) res0 HRc HB821 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R877y) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hres0_rng) ltac:(cbn; lia)) as Vch0
end; clear HRc;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W7) msX) 1 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 821%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 821 va cs lo hi wlo whi 50 1%N (SLit 0) 0 HRc HB821 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; lia)) as Vlf0
end; clear HRc end.
change (N.to_nat 1) with 1%nat in Vlf0. change (N.to_nat 8) with 8%nat in Vch0. rewrite Z.add_0_r in Vch0.
assert (Hobj7 : obj_at trbsegs (mrestrict (w_H W7) mem7) va LAY_Node (node_vals res0 c1 tn 0)).
{ apply (m_node_upd3 (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W7) mem7) va c0 c1 tn 0 res0 c1 0 Hobj (proj1 (proj2 (proj2 (proj2 (proj2 Mwf)))))).
- intros i Hi. apply (mbyte_of_aview trbsegs). apply HKva; clear - Hi; lia.
- exact Vch0.
- exact Hres0_rng.
- intros k0' Hk0'. rewrite <- (Vc1 k0' Hk0'). apply (mbyte_of_aview trbsegs). rewrite <- Z.add_assoc. apply HKva; clear - Hk0'; lia.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rc1. exact Rc1.
- exact Vlf0.
- clear; lia. }
assert (HSTm7 : m_STmem (w_H W7) mem7 pp dn F tail El ns tns q res0 c1).
{ split; [|split; [|split; [|split]]].
- apply (arr8_frame trbsegs _ _ pp _ Hpal1). intros a Ha. rewrite Hzl in Ha. apply (mbyte_of_aview trbsegs). replace a with (pp + (a - pp)) by (clear; lia).
apply (HK37 pp _ Hpp_l). clear - Ha Hrq3T. lia.
- apply (arr32_frame trbsegs _ _ dn _ Hdense1). intros a Ha. rewrite zlen_fr_vals, HlenEl in Ha. apply (mbyte_of_aview trbsegs). replace a with (dn + (a - dn)) by (clear; lia).
apply (HK37 dn _ Hdn_l). clear - Ha Hrq4c. lia.
- intros j Hj Hne. apply (node_mem_frame trbsegs _ _ _ _ j (CA3 j Hj Hne)). intros i Hi. apply (mbyte_of_aview trbsegs). unfold NODE_SIZE in Hi.
rewrite (HK37 _ _ (Hnode_l _ (Htns_in j Hj)) i ltac:(change (req_size NODE_SIZE) with 56; exact Hi)).
destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; clear - Hi; lia)) as (Hq1 & Hq2).
pose proof (Hs_nn j Hj Hne) as Hsn. apply (KU1 _ Hq1 Hq2); clear - Hi Hsn; lia.
- exact Hobj7.
- intros j Hj. pose proof (CA4 j Hj) as Vw. intros k0' Hk0'. rewrite <- (Vw k0' Hk0'). apply (mbyte_of_aview trbsegs).
set (aw := F + 32 + 8 * j + Z.of_nat k0').
assert (Haw : F + 32 <= aw < F + 32 + 8 * 509) by (subst aw; clear - Hj Hk0' Hntns; lia).
assert (Hq1w : 0 <= aw < 2 ^ 64) by (clear - Haw HFrng HFceil C1; lia).
pose proof HdF_va as HdFv. pose proof HdF_r as HdFr. pose proof HdF_tb as HdFt. unfold gbox in HdFv, HdFr, HdFt.
assert (Hz1 : in_zr aw (frame_rng ly3 (7, fpos)) \/ in_zr aw (shadow_addr (frame_addr ly3 7 fpos), fs_frame_bytes 7 / 8)).
{ left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 7) with 8192. rewrite ?EFA3. fold F. clear - Haw. lia. }
assert (Hz2 : ~ (spZ regs - 134 <= aw < spZ regs - 134 + 2)) by (clear - Haw HFceil Hceil Hslo FFS; lia).
change (aview trbsegs (w_H W7) mem7 aw = aview trbsegs (w_H W3) (ms_mem ms3) aw).
rewrite (proj1 (proj2 (proj2 (proj2 HK7))) 7 fpos aw Hfin3 Hz1 Hz2).
apply (KU1 _ Hq1w); [clear - Haw HFceil HdFr HdFt; lia | clear - Haw HdFv; lia | clear - Haw HdFv; lia]. }
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (Hkid0' : m_kid_ok B cxv (w_H W7) mem7 k0 res0 lo (i1 - 1) (n_col nd) (zsub El lo (i1 - 1))) end.
{ destruct k0 as [|t0 [|t1 l0]]; cbn [m_kid_ok] in Hkid0 |- *; [exact Hkid0 | | contradiction].
destruct Hkid0 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & (d0 & d1 & Q7) & Q8 & Q9).
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [|split; [exact Q8 | exact Q9]].
exists d0, d1. apply (obj_at_transport_range trbsegs _ _ _ _ _ NODE_SIZE Q7 (proj1 lay_inside_Node)). intros i Hi. apply (mbyte_of_aview trbsegs). unfold NODE_SIZE in Hi.
assert (Ht0_l : In (tn_addr t0, NODE_SIZE) lrest) by (apply Hnode_lx; apply in_or_app; right; left; reflexivity).
rewrite (HK37 _ _ Ht0_l i ltac:(change (req_size NODE_SIZE) with 56; exact Hi)).
destruct (Hoff3 _ _ Ht0_l (tn_addr t0 + i) ltac:(change (req_size NODE_SIZE) with 56; clear - Hi; lia)) as (Hq1 & Hq2).
assert (Hel : elen (tns ++ [t0]) = elen tns + 1) by (unfold elen; rewrite length_app; cbn [length]; clear; lia).
pose proof (m_sep_nodes B LAWS ly3 S3 _ _ _ (tns ++ [t0]) _ (elen tns) q HAR3 HPn ltac:(rewrite Hel; clear - Hq_t; lia) ltac:(rewrite Hel; clear - Hq_t; lia) ltac:(clear - Hq_t; lia)) as Hsn.
rewrite tnth_app_new0, (tnth_app_l tns [t0] q Hq_t) in Hsn. fold tn va in Hsn.
apply (KU1 _ Hq1 Hq2); clear - Hi Hsn; lia. }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trbsegs 930%nat Ex ssx msx [Z_to_bv 64 (L - 1 + elen k0 + elen k1)] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
assert (E930 : ew (havoc E0v 930 vals) 930 = Z_to_bv 64 (L - 1 + elen k0 + elen k1))
by (change 930%nat with (930 + 0)%nat at 2; rewrite (ew_havoc_new _ 930%nat vals 0%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
assert (Vnl2 : val_mem trbsegs (mrestrict (w_H W7) mem7) (spZ regs + -134) 2 (L - 1 + elen k0 + elen k1)) by (replace (spZ regs + -134) with (spZ regs - 134) by (clear; lia); exact Vnl).
m_add_chunk HS 2%nat (-134) 2%N (SOff 930 0) (spZ regs) (L - 1 + elen k0 + elen k1)
ltac:(repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E930) ltac:(cbn; clear - Hk01 Hk11 HL1 HL254; lia)
Vnl2.
ga_join HS ss_ST3 931%nat (@nil (bv 5)) ltac:(idtac).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RST3 HS HJ7 (k + EV_NTN); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns, El, i1, k0, k1, res0, res, c0, c1.
split; [split; [unfold EV_NTN; clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split. { assert (Hmb : m_node_blocks (tns ++ k0 ++ k1) = m_node_blocks (tns ++ k0) ++ m_node_blocks k1) by (unfold m_node_blocks; rewrite app_assoc, map_app; reflexivity).
rewrite Ebl7, Hmb. eapply Permutation_trans; [apply Permutation_app_tail; exact HPm3|]. change CHT_SIZE with 48. rewrite <- !app_assoc. cbn [app]. apply Permutation_refl. }
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact HSTm7|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|]. split; [m_ewT|].
split; [exact Hmeas|].
split; [exact Hqlt|].
split; [exact Hlt|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exists P; exact Hdone|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exact Hkid0' | exact Hkid1].
Qed.
End e.
End d.

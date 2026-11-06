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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8q YCa0 YC8s YC8u YC8v YC9o YC9p YC9q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC90 YCam.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YC5x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC59 YC5a YC5b YP16 YI0f YI09 YC68.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC4b.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_ST3a : forall n, rga_fromA B ss_XT (fun _ => INV_XT B) -> rga_from B ss_ST4 (INV_ST4 B n) -> rga_from B ss_ST3 (INV_ST3 B n).
Proof.
intros n RXT RST4.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & El & i1 & k0 & k1 & res0 & res1 & c0 & c1 & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HSTm & Hlen_tns & Hmatch & Hfacts & Rroot & R817 & Hmeas & Hqlt & Hlt & R821 & R866 & R870 & R871 & R872 &
(P & Hdone) & R877 & R905 & R930 & Hkid0 & Hkid1).
destruct Hk0 as [Hk0 Hbud].
unfold ss_ST3 in HS.
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
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ r 64 7 fpos HAR3 Hrin3 Hfin3) as HdF_r.
unfold zdisjoint in HdF_r. cbn [fst snd] in HdF_r. change (fs_frame_bytes 7) with 8192 in HdF_r. change (req_size 64) with 64 in HdF_r. rewrite EFA3 in HdF_r. fold F in HdF_r.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ tb 48 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
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
assert (Hva_l : In (va, NODE_SIZE) lrest) by (exact (Hnode_l _ (Htns_in q Hq_t))).
assert (Hva_in3 : In (va, NODE_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hva_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ va NODE_SIZE HAR3 Hva_in3) as (Hva4096 & Hvazone & Hvaceil & Hva16). change (req_size NODE_SIZE) with 56 in Hvazone, Hvaceil.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ va NODE_SIZE 7 fpos HAR3 Hva_in3 Hfin3) as HdF_va.
unfold zdisjoint in HdF_va. cbn [fst snd] in HdF_va. change (fs_frame_bytes 7) with 8192 in HdF_va. change (req_size NODE_SIZE) with 56 in HdF_va. rewrite EFA3 in HdF_va. fold F in HdF_va.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ va NODE_SIZE cid pos HAR3 Hva_in3 HfinS3) as HdC_va.
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
assert (HFi : F + 8192 <= 65536 \/ 6287360 <= F) by (unfold gbox, off_img in HFhigh_img; clear - HFhigh_img; lia).
assert (Hvai : va + 56 <= 65536 \/ 6287360 <= va) by (clear - Hvazone; lia).
assert (Hvaz : va + 56 <= 2147446784 \/ 17594333495296 <= va) by (clear - Hvazone; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ va NODE_SIZE (proj1 HJ3) Hva_in3) as (_ & _ & _ & _ & Hvapres2 & _). change (req_size NODE_SIZE) with 56 in Hvapres2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E821c : ew Ev 821 = Z_to_bv 64 va) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R821);
pose proof (ast_ok_add_region trasegs Ev _ _
(YQ0b.mkRegion (Some 821%nat) 8 16 8 16 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E821c, unsigned_lit_small by exact Hva_rng;
split; [clear - Hva4096; lia|]; split; [clear - Hvaceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Hvapres2 (va + o) ltac:(clear - Ho; lia)))
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
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x838f4.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff 821 ?c)) ?len =>
rewrite (U_atom_off Ex 821 va c); [| first [exact E821c | rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E821c] | exact Hva_rng | clear - Hva4096 Hvaceil C1; lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff bx 0) _ len va 56 (proj1 HJ3) Hva_in3);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E44 | unfold SB; clear; lia]
| clear; lia | change (req_size 56) with 56; clear; lia ] end).
pose proof (proj2 (Hown tn (Htns_in q Hq_t))) as Ava. fold va in Ava. cbn [c_regs] in Ava. unfold rgc_FPs in Ava. cbn [c_r c_ly c_S] in Ava.
1: m_awrR AG fpos F EFA3 54%nat 67%nat
ltac:(m_awr_cell 821%nat E821c va Ava Hva_in3 ltac:(idtac; first [exact Hva_rng | clear - Hva4096 Hvaceil C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => change (req_size NODE_SIZE) with 56; clear - Ha; lia end])).
m_run_keptG HFr AG (fun a : Z => (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) \/ va <= a < va + 8 \/ va + 8 <= a < va + 16 \/ va + 50 <= a < va + 51) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
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
assert (KU1 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) -> ~ (va <= a < va + 16) -> ~ (va + 50 <= a < va + 51) ->
aview trasegs (w_H W3) (ms_mem ms) a = aview trasegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha1 Ha2 Ha3 Ha4; apply UN1; [exact Ha1 | clear - Ha2 Ha3 Ha4; lia]).
assert (Hpal1 : arr8 trasegs (mrestrict (w_H W3) (ms_mem ms)) pp (pal_bytes El ++ tail)).
{ apply (arr8_frame trasegs _ _ pp _ CA1). intros a Ha. rewrite Hzl in Ha. apply (mbyte_of_aview trasegs).
destruct (Hoff3 pp _ Hpp_l a ltac:(clear - Ha Hrq3T; lia)) as (Hq1 & Hq2). apply (KU1 _ Hq1 Hq2); clear - Ha Hs_pq Hrq3T; lia. }
assert (Hdense1 : arr32 trasegs (mrestrict (w_H W3) (ms_mem ms)) dn (fr_vals El)).
{ apply (arr32_frame trasegs _ _ dn _ CA2). intros a Ha. rewrite zlen_fr_vals, HlenEl in Ha. apply (mbyte_of_aview trasegs).
destruct (Hoff3 dn _ Hdn_l a ltac:(clear - Ha Hrq4c; lia)) as (Hq1 & Hq2). apply (KU1 _ Hq1 Hq2); clear - Ha Hs_dq Hrq4c; lia. }
assert (HKva : forall i, 16 <= i < 50 -> aview trasegs (w_H W3) (ms_mem ms) (va + i) = aview trasegs (w_H W3) (ms_mem ms3) (va + i)).
{ intros i Hi. destruct (Hoff3 va _ Hva_l (va + i) ltac:(change (req_size NODE_SIZE) with 56; clear - Hi; lia)) as (Hq1 & Hq2). apply (KU1 _ Hq1 Hq2); clear - Hi; lia. }
assert (Hres_rng : forall (kl : list tnode) res, (kl = [] -> res = 0) -> (forall t, kl = [t] -> res = tn_addr t /\ In t (tns ++ k0 ++ k1)) -> (length kl <= 1)%nat -> 0 <= res < 2 ^ 64).
{ intros kl res H0 H1 Hl. destruct kl as [|t0 [|t1 l0]]; [rewrite (H0 eq_refl); clear; lia | | cbn [length] in Hl; lia].
destruct (H1 t0 eq_refl) as (Hr0 & Hin0). rewrite Hr0.
assert (Ht0_3 : In (tn_addr t0, NODE_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hnode_lx; exact Hin0]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ _ NODE_SIZE HAR3 Ht0_3) as (Ht4096 & _ & Htceil & _). change (req_size NODE_SIZE) with 56 in Htceil. clear - Ht4096 Htceil C1. lia. }
assert (Hres0_rng : 0 <= res0 < 2 ^ 64).
{ apply (Hres_rng k0 res0); [intros ->; exact Hkid0 | intros t ->; cbn [m_kid_ok] in Hkid0; split; [exact (proj1 Hkid0) | apply in_or_app; right; apply in_or_app; left; left; reflexivity] | unfold elen in Hk01; clear - Hk01; lia]. }
assert (Hres1_rng : 0 <= res1 < 2 ^ 64).
{ apply (Hres_rng k1 res1); [intros ->; exact Hkid1 | intros t ->; cbn [m_kid_ok] in Hkid1; split; [exact (proj1 Hkid1) | apply in_or_app; right; apply in_or_app; right; left; reflexivity] | unfold elen in Hk11; clear - Hk11; lia]. }
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
assert (HB821 : bv_unsigned (ew Ex 821) = va) by (assert (Rq : ew Ex 821 = Z_to_bv 64 va) by m_ewT; rewrite Rq; apply unsigned_lit_small; exact Hva_rng);
assert (R877y : ew Ex 877 = Z_to_bv 64 res0) by m_ewT; assert (R905y : ew Ex 905 = Z_to_bv 64 res1) by m_ewT;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 821%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 821 va cs lo hi wlo whi 8 8%N (SOff 905 0) res1 HRc HB821 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R905y) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hres1_rng) ltac:(cbn; lia)) as Vch1
end; clear HRc;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 1 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 821%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 821 va cs lo hi wlo whi 0 8%N (SOff 877 0) res0 HRc HB821 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R877y) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hres0_rng) ltac:(cbn; lia)) as Vch0
end; clear HRc;
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 2 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 821%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 821 va cs lo hi wlo whi 50 1%N (SLit 0) 0 HRc HB821 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; lia)) as Vlf0
end; clear HRc end.
change (N.to_nat 1) with 1%nat in Vlf0. change (N.to_nat 8) with 8%nat in Vch0, Vch1. rewrite Z.add_0_r in Vch0.
assert (Hobj1 : obj_at trasegs (mrestrict (w_H W3) (ms_mem ms)) va LAY_Node (node_vals res0 res1 tn 0)).
{ apply (m_node_upd3 (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) va res0 c1 tn 0 res0 res1 0 Hobj (proj1 (proj2 (proj2 (proj2 (proj2 Mwf)))))).
- intros i Hi. apply (mbyte_of_aview trasegs). apply HKva; exact Hi.
- exact Vch0.
- exact Hres0_rng.
- exact Vch1.
- exact Hres1_rng.
- exact Vlf0.
- clear; lia. }
assert (Hnodes1 : forall j, 0 <= j < elen tns -> j <> q -> node_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) ns tns j).
{ intros j Hj Hne. apply (node_mem_frame trasegs _ _ _ _ j (CA3 j Hj Hne)). intros i Hi. apply (mbyte_of_aview trasegs). unfold NODE_SIZE in Hi.
destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; clear - Hi; lia)) as (Hq1 & Hq2).
pose proof (Hs_nn j Hj Hne) as Hsn. apply (KU1 _ Hq1 Hq2); clear - Hi Hsn; lia. }
assert (Hnl1 : forall j, 0 <= j < elen tns -> val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) (F + 32 + 8 * j) 8 (tn_addr (tnth tns j))).
{ intros j Hj. pose proof (CA4 j Hj) as Vw. intros k0' Hk0'. rewrite <- (Vw k0' Hk0'). apply (mbyte_of_aview trasegs).
set (aw := F + 32 + 8 * j + Z.of_nat k0').
assert (Haw : F + 32 <= aw < F + 32 + 8 * 509) by (subst aw; clear - Hj Hk0' Hntns; lia).
assert (Hq1w : 0 <= aw < 2 ^ 64) by (clear - Haw HFrng HFceil C1; lia).
pose proof HdF_va as HdFv. pose proof HdF_r as HdFr. pose proof HdF_tb as HdFt. unfold gbox in HdFv, HdFr, HdFt.
change (aview trasegs (w_H W3) (ms_mem ms) aw = aview trasegs (w_H W3) (ms_mem ms3) aw).
apply (KU1 _ Hq1w); [clear - Haw HFceil HdFr HdFt; lia | clear - Haw HdFv; lia | clear - Haw HdFv; lia]. }
assert (Hel3 : elen (tns ++ k0 ++ k1) = elen tns + elen k0 + elen k1) by (unfold elen; rewrite !length_app; clear; lia).
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (KID : forall kl res lo' hi' cidx' seg jj, m_kid_ok B cxv (w_H W3) (ms_mem ms3) kl res lo' hi' cidx' seg ->
(forall t, kl = [t] -> tnth (tns ++ k0 ++ k1) jj = t /\ elen tns <= jj < elen tns + elen k0 + elen k1) ->
m_kid_ok B cxv (w_H W3) (ms_mem ms) kl res lo' hi' cidx' seg) end.
{ intros kl res lo' hi' cidx' seg jj K Hjj. destruct kl as [|t [|t' l0]]; cbn [m_kid_ok] in K |- *; [exact K | | contradiction].
destruct K as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & (d0 & d1 & Q7) & Q8 & Q9). destruct (Hjj t eq_refl) as [Htj Hjr].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [|split; [exact Q8 | exact Q9]].
exists d0, d1. apply (obj_at_transport_range trasegs _ _ _ _ _ NODE_SIZE Q7 (proj1 lay_inside_Node)). intros i Hi. apply (mbyte_of_aview trasegs). unfold NODE_SIZE in Hi.
assert (Ht_in : In t (tns ++ k0 ++ k1)) by (rewrite <- Htj; unfold tnth; apply znth_In; rewrite Hel3; clear - Hjr Hq_t; lia).
destruct (Hoff3 _ _ (Hnode_lx _ Ht_in) (tn_addr t + i) ltac:(change (req_size NODE_SIZE) with 56; clear - Hi; lia)) as (Hq1 & Hq2).
pose proof (m_sep_nodes B LAWS ly3 S3 _ _ _ (tns ++ k0 ++ k1) _ jj q HAR3 HPn ltac:(rewrite Hel3; clear - Hjr Hq_t; lia) ltac:(rewrite Hel3; clear - Hq_t Hk01 Hk11; lia) ltac:(clear - Hjr Hq_t; lia)) as Hsn.
rewrite Htj, (tnth_app_l tns (k0 ++ k1) q Hq_t) in Hsn. fold tn va in Hsn.
apply (KU1 _ Hq1 Hq2); clear - Hi Hsn; lia. }
assert (Hkid0m := KID k0 res0 lo (i1 - 1) (n_col nd) _ (elen tns) Hkid0
ltac:(intros t ->; split; [apply (tnth_app_new0 tns t k1) | change (elen [t]) with 1; clear - Hk11; lia])).
assert (Hkid1m := KID k1 res1 i1 hi (L - 1 + elen k0) _ (elen tns + elen k0) Hkid1
ltac:(intros t ->; split; [destruct k0 as [|t0 [|t1 l0]]; [change (elen (@nil tnode)) with 0; rewrite Z.add_0_r; apply (tnth_app_new0 tns t [])
| change (elen [t0]) with 1; apply (tnth_app_new1 tns t0 t [])
| cbn [m_kid_ok] in Hkid0; contradiction]
| change (elen [t]) with 1; clear - Hk01; lia])).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (tl (tl (tl (ss_mem ssx)))) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
set (mw := elen tns) in *.
assert (Hmw0 : 0 <= mw <= 509) by (subst mw; unfold elen in *; clear - Hntns; lia).
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (TRANS : forall mem' : word -> option byte,
(forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (F + 32 + 8 * mw <= a < F + 32 + 8 * mw + 16) -> aview trasegs (w_H W3) mem' a = aview trasegs (w_H W3) (ms_mem ms) a) ->
arr8 trasegs (mrestrict (w_H W3) mem') pp (pal_bytes El ++ tail) /\ arr32 trasegs (mrestrict (w_H W3) mem') dn (fr_vals El) /\
obj_at trasegs (mrestrict (w_H W3) mem') va LAY_Node (node_vals res0 res1 tn 0) /\
(forall j, 0 <= j < mw -> j <> q -> node_mem trasegs (mrestrict (w_H W3) mem') ns tns j) /\
(forall j, 0 <= j < mw -> val_mem trasegs (mrestrict (w_H W3) mem') (F + 32 + 8 * j) 8 (tn_addr (tnth tns j))) /\
m_kid_ok B cxv (w_H W3) mem' k0 res0 lo (i1 - 1) (n_col nd) (zsub El lo (i1 - 1)) /\
m_kid_ok B cxv (w_H W3) mem' k1 res1 i1 hi (L - 1 + elen k0) (zsub El i1 hi)) end.
{ intros mem' HK.
assert (HKb : forall b sz, In (b, sz) lrest -> forall i, 0 <= i < req_size sz -> aview trasegs (w_H W3) mem' (b + i) = aview trasegs (w_H W3) (ms_mem ms) (b + i)).
{ intros b sz Hb i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply (HK _ Hq1 Hq2).
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ b sz 7 fpos HAR3 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hb]) Hfin3) as HdFb.
unfold zdisjoint in HdFb. cbn [fst snd] in HdFb. change (fs_frame_bytes 7) with 8192 in HdFb. rewrite EFA3 in HdFb. fold F in HdFb. clear - Hi HdFb Hmw0. lia. }
split. { apply (arr8_frame trasegs _ _ pp _ Hpal1). intros a Ha. rewrite Hzl in Ha. apply (mbyte_of_aview trasegs). replace a with (pp + (a - pp)) by (clear; lia). apply (HKb pp _ Hpp_l). clear - Ha Hrq3T. lia. }
split. { apply (arr32_frame trasegs _ _ dn _ Hdense1). intros a Ha. rewrite zlen_fr_vals, HlenEl in Ha. apply (mbyte_of_aview trasegs). replace a with (dn + (a - dn)) by (clear; lia). apply (HKb dn _ Hdn_l). clear - Ha Hrq4c. lia. }
split. { apply (obj_at_transport_range trasegs _ _ _ _ _ NODE_SIZE Hobj1 (proj1 lay_inside_Node)). intros i Hi. apply (mbyte_of_aview trasegs). apply (HKb va _ Hva_l). change (req_size NODE_SIZE) with 56. exact Hi. }
split. { intros j Hj Hne. apply (node_mem_frame trasegs _ _ _ _ j (Hnodes1 j Hj Hne)). intros i Hi. apply (mbyte_of_aview trasegs). apply (HKb _ _ (Hnode_l _ (Htns_in j Hj))). change (req_size NODE_SIZE) with 56. exact Hi. }
split. { intros j Hj. pose proof (Hnl1 j Hj) as Vw. intros k0' Hk0'. rewrite <- (Vw k0' Hk0'). apply (mbyte_of_aview trasegs).
set (aw := F + 32 + 8 * j + Z.of_nat k0').
assert (Haw : F + 32 <= aw < F + 32 + 8 * mw) by (subst aw; clear - Hj Hk0'; lia).
pose proof HdF_r as HdFr. pose proof HdF_tb as HdFt. unfold gbox in HdFr, HdFt.
change (aview trasegs (w_H W3) mem' aw = aview trasegs (w_H W3) (ms_mem ms) aw).
apply HK; [clear - Haw HFrng HFceil Hmw0 C1; lia | clear - Haw Hmw0 HFceil HdFr HdFt; lia | clear - Haw; lia]. }
lazymatch goal with |- m_kid_ok _ ?cxv _ _ _ _ _ _ _ _ /\ _ =>
assert (KID2 : forall kl res lo' hi' cidx' seg, m_kid_ok B cxv (w_H W3) (ms_mem ms) kl res lo' hi' cidx' seg -> (forall t, kl = [t] -> In t (tns ++ k0 ++ k1)) ->
m_kid_ok B cxv (w_H W3) mem' kl res lo' hi' cidx' seg) end.
{ intros kl res lo' hi' cidx' seg K Hin. destruct kl as [|t [|t' l0]]; cbn [m_kid_ok] in K |- *; [exact K | | contradiction].
destruct K as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & (d0 & d1 & Q7) & Q8 & Q9).
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [|split; [exact Q8 | exact Q9]].
exists d0, d1. apply (obj_at_transport_range trasegs _ _ _ _ _ NODE_SIZE Q7 (proj1 lay_inside_Node)). intros i Hi. apply (mbyte_of_aview trasegs).
apply (HKb _ _ (Hnode_lx _ (Hin t eq_refl))). change (req_size NODE_SIZE) with 56. exact Hi. }
split; [apply (KID2 _ _ _ _ _ _ Hkid0m); intros t ->; apply in_or_app; right; apply in_or_app; left; left; reflexivity
| apply (KID2 _ _ _ _ _ _ Hkid1m); intros t ->; apply in_or_app; right; apply in_or_app; right; left; reflexivity]. }
assert (OLDK : forall j, 0 <= j < mw -> n_leaf (node ns j) = false -> forall c, (n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) -> 0 <= c < elen tns).
{ intros j Hj Hl c Hc. destruct (cinv_kids cnt ent st Hcinv j ltac:(fold ns; rewrite <- Hlen_tns; exact Hj) Hl) as (c' & K0 & K1 & R1 & R2). fold ns in K0, K1, R2.
rewrite K0, K1 in Hc. rewrite <- Hlen_tns in R2. fold mw in R2 |- *. destruct Hc as [Hc|Hc]; injection Hc as <-; clear - Hj R1 R2; lia. }
assert (FAILG : forall mem' : word -> option byte,
(forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) ->
~ (F + 32 + 8 * mw <= a < F + 32 + 8 * mw + 16) -> aview trasegs (w_H W3) mem' a = aview trasegs (w_H W3) (ms_mem ms) a) ->
exists t : tree, troot t = tn_addr (tnth tns 0) /\ tree_at trasegs (mrestrict (w_H W3) mem') t /\ (tree_height t <= Z.to_nat TREE_HMAX)%nat /\
Permutation (tree_blocks t) (m_node_blocks (tns ++ k0 ++ k1)) /\ Z.of_nat (length (tree_nodes t)) = mw + elen k0 + elen k1).
{ intros mem' HK. destruct (TRANS mem' HK) as (_ & _ & OBJ' & NM' & _ & KID0' & KID1').
set (ok0 := match k0 with [] => false | _ => true end). set (ok1 := match k1 with [] => false | _ => true end).
destruct (cfail_ok cnt ent st i1 (L - 1 + elen k0) ok0 ok1 Hcinv Hqlt) as (PO & TI & D0 & Hlen' & TOK). fold ns q L in PO, TI, D0, Hlen', TOK.
destruct (cfail_nodes ns q i1 (L - 1 + elen k0) ok0 ok1 ltac:(rewrite <- Hlen_tns; exact Hq_t)) as (_ & NDo & NDq & NK0 & NK1). fold nd in NDq, NK0, NK1. rewrite <- Hlen_tns in NDo, NDq, NK0, NK1. fold mw in NDo, NDq, NK0, NK1.
assert (Hb0 : elen k0 = (if ok0 then 1 else 0)) by (subst ok0; destruct k0 as [|? [|? ?]]; [reflexivity | reflexivity | cbn [m_kid_ok] in Hkid0; contradiction]).
assert (Hb1 : elen k1 = (if ok1 then 1 else 0)) by (subst ok1; destruct k1 as [|? [|? ?]]; [reflexivity | reflexivity | cbn [m_kid_ok] in Hkid1; contradiction]).
set (ns' := cfail_ns ns q i1 (L - 1 + elen k0) ok0 ok1) in *. set (tns' := tns ++ k0 ++ k1).
assert (Hlen2 : elen ns' = elen tns') by (rewrite Hlen'; subst tns'; rewrite Hel3, Hb0, Hb1, <- Hlen_tns; reflexivity).
pose proof (tree_ok_node _ _ _ TOK) as [Hm0 Hh1].
exists (build ns' tns' 0 (Z.to_nat (L + 1))).
split. { rewrite build_root by exact Hh1. subst tns'. apply f_equal. apply tnth_app_l. clear - Hq_t. lia. }
split.
{ apply (build_at trasegs _ ns' tns' _ 0 TOK). intros j Hj. rewrite Hlen2 in Hj. subst tns'. rewrite Hel3 in Hj. fold mw in Hj.
destruct (Z.eq_dec j q) as [-> | Hnq].
{
rewrite (tnth_app_l tns (k0 ++ k1) q Hq_t). fold tn va. split; [| split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 Mwf))))) | exact Mnz]].
unfold node_mem. subst ns'. rewrite NDq. cbn [n_leaf n_k0 n_k1]. rewrite (tnth_app_l tns (k0 ++ k1) q Hq_t). fold tn va.
assert (O0 : oaddr (tns ++ k0 ++ k1) (if ok0 then Some mw else None) = res0).
{ subst ok0. destruct k0 as [|t0 [|? ?]]; cbn [m_kid_ok] in Hkid0; [cbn; symmetry; exact Hkid0 | | contradiction].
cbn [oaddr app]. subst mw. rewrite (tnth_app_new0 tns t0 k1). symmetry. exact (proj1 Hkid0). }
assert (O1 : oaddr (tns ++ k0 ++ k1) (if ok1 then Some (mw + (if ok0 then 1 else 0)) else None) = res1).
{ rewrite <- Hb0. subst ok1. destruct k1 as [|t1 [|? ?]]; cbn [m_kid_ok] in Hkid1; [cbn; symmetry; exact Hkid1 | | contradiction].
cbn [oaddr]. destruct k0 as [|t0 [|? ?]]; [| | cbn [m_kid_ok] in Hkid0; contradiction].
- change (elen (@nil tnode)) with 0. rewrite Z.add_0_r. subst mw. cbn [app]. rewrite (tnth_app_new0 tns t1 []). symmetry. exact (proj1 Hkid1).
- change (elen [t0]) with 1. subst mw. cbn [app]. rewrite (tnth_app_new1 tns t0 t1 []). symmetry. exact (proj1 Hkid1). }
rewrite O0, O1. exact OBJ'. }
destruct (Z_lt_le_dec j mw) as [Hjm | Hjm].
{
rewrite (tnth_app_l tns (k0 ++ k1) j ltac:(fold mw; clear - Hj Hjm; lia)). destruct (Hmatch j ltac:(fold mw; clear - Hj Hjm; lia)) as (_ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tz).
split; [| split; [exact Wl | exact Tz]].
apply (node_mem_ext trasegs _ ns _ tns (k0 ++ k1) j (NDo j ltac:(clear - Hj Hjm; lia) Hnq) ltac:(fold mw; clear - Hj Hjm; lia) (OLDK j ltac:(clear - Hj Hjm; lia)) (NM' j ltac:(clear - Hj Hjm; lia) Hnq)). }
subst ok0 ok1.
destruct k0 as [|t0 [|? ?]]; [| | cbn [m_kid_ok] in Hkid0; contradiction]; destruct k1 as [|t1 [|? ?]]; try (cbn [m_kid_ok] in Hkid1; contradiction);
cbn [app] in *; change (elen (@nil tnode)) with 0 in *; try change (elen [t0]) with 1 in *; try change (elen [t1]) with 1 in *.
- exfalso. clear - Hj Hjm. lia.
-
assert (Ej : j = mw) by (clear - Hj Hjm; lia). subst j.
assert (Et : tnth (tns ++ [t1]) mw = t1) by (subst mw; apply tnth_app_new0). rewrite Et.
cbn [m_kid_ok] in KID1'. destruct KID1' as (Er & Tnz1 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz1]]. unfold node_mem. subst ns'. rewrite !Z.add_0_r in NK1. rewrite ?Z.add_0_r. rewrite (NK1 eq_refl). cbn [n_leaf]. rewrite Et. exact Tobj.
-
assert (Ej : j = mw) by (clear - Hj Hjm; lia). subst j.
assert (Et : tnth (tns ++ [t0]) mw = t0) by (subst mw; apply tnth_app_new0). rewrite Et.
cbn [m_kid_ok] in KID0'. destruct KID0' as (Er & Tnz0 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz0]]. unfold node_mem. subst ns'. rewrite (NK0 eq_refl). cbn [n_leaf]. rewrite Et. exact Tobj.
-
assert (Et0 : tnth (tns ++ [t0; t1]) mw = t0) by (subst mw; apply tnth_app_new0).
assert (Et1 : tnth (tns ++ [t0; t1]) (mw + 1) = t1) by (subst mw; apply tnth_app_new1).
destruct (Z.eq_dec j mw) as [-> | Hnm].
+ rewrite Et0. cbn [m_kid_ok] in KID0'. destruct KID0' as (Er & Tnz0 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz0]]. unfold node_mem. subst ns'. rewrite (NK0 eq_refl). cbn [n_leaf]. rewrite Et0. exact Tobj.
+ assert (Ej : j = mw + 1) by (clear - Hj Hjm Hnm; lia). subst j. rewrite Et1.
cbn [m_kid_ok] in KID1'. destruct KID1' as (Er & Tnz1 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz1]]. unfold node_mem. subst ns'. rewrite (NK1 eq_refl). cbn [n_leaf]. rewrite Et1. exact Tobj. }
split. { pose proof (build_height ns' tns' 0 (Z.to_nat (L + 1))) as Hbh. unfold TREE_HMAX. clear - Hbh HL1 HL254. lia. }
split. { eapply Permutation_trans; [apply (build_blocks_root ns' tns' _ PO TOK)|]. rewrite Hlen2. rewrite (m_node_blocks_zseq tns'). apply Permutation_refl. }
rewrite (Permutation_length (build_nodes_root ns' tns' _ PO TOK)), length_map, YP14.zseq_length, Hlen2. subst tns'. rewrite Hel3. fold mw.
rewrite Z2Nat.id by (clear - Hmw0 Hk01 Hk11; lia). reflexivity. }
reshok_bx HS 44%nat.
srr_branch_tok tratbl_lib_ok HS SHOK GBspan.
-
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x844d4.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
destruct (FAILG (ms_mem msX) ltac:(intros a Ha1 Ha2 _; exact (UN2 a Ha1 Ha2))) as (tf & Hroot_f & Hat_f & Hh_f & Hbl_f & Hnn_f) end.
ga_join HS ss_XT 1300%nat rga_deads_XT ltac:(idtac).
rga_hand RXT HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, T, dn, (4 * cnt), tf.
assert (HEA : 0 <= EV_ADDFRAME) by (vm_compute; discriminate).
split; [split; [rewrite Hnn_f; unfold EV_HD, EV_FREECHT, EV_RGBADD in *; clear - Hk0 Hmw0 Hk01 Hk11 HEA; lia | rga_bud_tac Hbud]|].
split; [exact Hfmt|]. split; [clear - HT24; lia|]. split; [clear - HcntT; lia|].
split. { eapply Permutation_trans; [exact HPm3|]. change CHT_SIZE with 48. repeat apply Permutation_app_head. apply Permutation_sym. exact Hbl_f. }
split; [split; [m_ewT | split; eassumption]|]. split; [split; [m_ewT | split; eassumption]|]. split; [split; [m_ewT | split; eassumption]|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [split; [m_ewT | split; eassumption]|].
split; [rewrite Hroot_f; m_ewT|].
split; [exact Hat_f | exact Hh_f].
-
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x838f8.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok tratbl_lib_ok HS SHOK GBspan.
+
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x844d4.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
destruct (FAILG (ms_mem msX) ltac:(intros a Ha1 Ha2 _; rewrite (UN3 a Ha1 Ha2); exact (UN2 a Ha1 Ha2))) as (tf & Hroot_f & Hat_f & Hh_f & Hbl_f & Hnn_f) end.
ga_join HS ss_XT 1300%nat rga_deads_XT ltac:(idtac).
rga_hand RXT HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, T, dn, (4 * cnt), tf.
assert (HEA : 0 <= EV_ADDFRAME) by (vm_compute; discriminate).
split; [split; [rewrite Hnn_f; unfold EV_HD, EV_FREECHT, EV_RGBADD in *; clear - Hk0 Hmw0 Hk01 Hk11 HEA; lia | rga_bud_tac Hbud]|].
split; [exact Hfmt|]. split; [clear - HT24; lia|]. split; [clear - HcntT; lia|].
split. { eapply Permutation_trans; [exact HPm3|]. change CHT_SIZE with 48. repeat apply Permutation_app_head. apply Permutation_sym. exact Hbl_f. }
split; [split; [m_ewT | split; eassumption]|]. split; [split; [m_ewT | split; eassumption]|]. split; [split; [m_ewT | split; eassumption]|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [split; [m_ewT | split; eassumption]|].
split; [rewrite Hroot_f; m_ewT|].
split; [exact Hat_f | exact Hh_f].
+
assert (Hres0nz : res0 <> 0).
{ rewrite YO3v.branch_eq_U in Hc. apply Z.eqb_neq in Hc. rewrite (U_atom _ 877 res0) in Hc by first [m_ewT | exact Hres0_rng]. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc. exact Hc. }
assert (Hres1nz : res1 <> 0).
{ rewrite YO3v.branch_eq_U in Hc0. apply Z.eqb_neq in Hc0. rewrite (U_atom _ 905 res1) in Hc0 by first [m_ewT | exact Hres1_rng]. rewrite U_SLit in Hc0. change (zcanon 0) with 0 in Hc0. exact Hc0. }
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x838fc.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
destruct (TRANS (ms_mem msX) ltac:(intros a Ha1 Ha2 _; rewrite (UN3 a Ha1 Ha2); exact (UN2 a Ha1 Ha2))) as (Hpa4 & Hfa4 & OBJ4 & NM4 & NL4 & KID04 & KID14) end.
ga_join HS ss_ST4 931%nat (@nil (bv 5)) ltac:(idtac).
m_hand_ih RST4 HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns, El, i1, k0, k1, res0, res1.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|].
split; [exact HL254|]. split; [exact Htail|].
split; [exact (conj Hpa4 (conj Hfa4 (conj NM4 (conj OBJ4 NL4))))|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|].
split; [m_ewT|]. split; [m_ewT|].
split; [exact Hmeas|].
split; [exact Hqlt|].
split; [exact Hlt|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exists P; exact Hdone|].
split; [exact Hres0nz|]. split; [exact Hres1nz|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|].
split; [exact KID04 | exact KID14].
Qed.
End e.
End d.

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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCop YCne YCng YCnh YCof YCnk YCnl YCno.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnn.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YCj8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqk.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_ST3b2 : forall n, rga_fromA B ss_CLn (fun _ => INV_CL B n) -> rga_fromA B ss_CX (fun _ => INV_CX B) -> rga_from B ss_ST5 (INV_ST5 B n).
Proof.
intros n RCL RCX.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL255a & Htail & HCLm & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & R930 & Hqge1 & Hmeas).
destruct Hk0 as [Hk0 Hbud].
unfold ss_ST5 in HS.
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
assert (Hntns : elen tns <= 509) by (rewrite Hlen_tns; fold ns; rewrite Hlen_ns; fold L; clear - HL255a; lia).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ r 64 7 fpos HAR3 Hrin3 Hfin3) as HdF_r.
unfold zdisjoint in HdF_r. cbn [fst snd] in HdF_r. change (fs_frame_bytes 7) with 8192 in HdF_r. change (req_size 64) with 64 in HdF_r. rewrite EFA3 in HdF_r. fold F in HdF_r.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ tb 48 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. change (req_size 48) with 48 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb.
assert (Hzl : zlen (pal_bytes (c_E st) ++ tail) = 3 * T)
by (unfold zlen; rewrite length_app, Nat2Z.inj_add; change (Z.of_nat (length (pal_bytes (c_E st)))) with (zlen (pal_bytes (c_E st))); change (Z.of_nat (length tail)) with (zlen tail);
rewrite zlen_pal_bytes, Hlen_E; clear - Htail; lia).
destruct HCLm as (CA1 & CA2 & CA3 & CA4).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
idtac "OK-BR3".
-
assert (HL254 : L <= 254).
{ rewrite YO3v.branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
rewrite U_SExt, (U_atom _ 930 L) in Hc by first [m_ewT | clear - HL1 HL255a; lia].
rewrite U_SLit in Hc. change (2 ^ Z.of_N 16) with 65536 in Hc. rewrite Z.mod_small in Hc by (clear - HL1 HL255a; lia).
rewrite (zcanon_id L) in Hc by (unfold M64; clear - HL1 HL255a; lia). change (zcanon 255) with 255 in Hc. clear - Hc. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x838ac.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HCLm2 : m_CLmem (w_H W3) (ms_mem msX) pp dn F tail st tns) end.
{ apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail st tns (conj CA1 (conj CA2 (conj CA3 CA4)))).
- intros i Hi. rewrite Hzl in Hi. pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). exact (UN3 _ Hq1 Hq2).
- intros i Hi. rewrite zlen_fr_vals, Hlen_E in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). exact (UN3 _ Hq1 Hq2).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
exact (UN3 _ Hq1 Hq2).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (unfold gbox in HdF_r, HdF_tb; clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
exact (UN3 _ Hq1 Hq2). }
idtac "OK-CLM2".
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rx17 : ew Ex 817 = Z_to_bv 64 (q - 1)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R817);
assert (Rx18 : ew Ex 930 = Z_to_bv 64 L) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R930) end.
assert (HUz16 : forall E' n0 v, ew E' n0 = Z_to_bv 64 v -> 0 <= v < 65536 -> U E' (SExt false 16 (SOff n0 0)) = v).
{ intros E' n0 v Hn Hv. rewrite U_SExt, (U_atom E' n0 v Hn) by (clear - Hv; lia). change (2 ^ Z.of_N 16) with 65536. rewrite Z.mod_small by exact Hv. apply zcanon_id. unfold M64. clear - Hv. lia. }
rregU HS (11%bv : bv 5) q ltac:(rewrite (U_atom_off _ 817 (q - 1) 1 Rx17) by (clear - Hqge1 Hq0n Hlen_ns HL255a; lia); clear; lia) Q12.
slot_val HS (Some 2%nat) (-576) (-134) (Z_to_bv 64 L)
ltac:(rewrite denot_lit_U; f_equal; apply (U_atom _ 930 L Rx18); clear - HL1 HL254; lia) QS.
ra_join_slots HS ss_CLn2 1999%nat rga_deads_CLn2 [(Some 2%nat, (-576), (-134))]
ltac:(idtac; ga_join_val HS 1999%nat 18%nat Q12 E2017; ga_join_val HS 1999%nat 19%nat QS E2018;
c_pin HS (12%bv : bv 5) (SOff 2018 0)
ltac:(apply U_inj; transitivity L; [apply (U_atom _ 2018 L E2018); clear - HL1 HL254; lia
| symmetry; apply (HUz16 _ 930%nat L); [rewrite ew_havoc_old by lia; exact Rx18 | clear - HL1 HL254; lia]])).
idtac "OK-JOIN-A".
slot_val HS (Some 2%nat) (-576) (-134) (Z_to_bv 64 L)
ltac:(rewrite denot_lit_U; f_equal; apply (U_atom _ 2018 L E2018); clear - HL1 HL254; lia) QS2.
m_join_slots_win HS ss_CLn 799%nat rga_deads_CLn [(Some 2%nat, (-576), (-134))]
ltac:(idtac; ga_join_val HS 799%nat 18%nat Q12 N817; ga_join_val HS 799%nat 19%nat QS2 N818;
c_pin HS (12%bv : bv 5) (SOff 818 0)
ltac:(apply U_inj; transitivity L; [apply (U_atom _ 818 L N818); clear - HL1 HL254; lia
| symmetry; apply (U_atom _ 2018 L); [first [m_ewT | rewrite YCft.ew_havoc_above by (cbn [length]; lia); exact E2018] | clear - HL1 HL254; lia]])).
idtac "OK-JOIN-B".
rga_hand RCL HS HJ3 k; [rga_E_tac HEE0 | ].
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
split; [exact HCLm2|]. split; [exact Hlen_tns|]. split; [exact Hmatch|].
split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|].
split; [exact N817|]. split; [exact N818|].
fold q. exact Hmeas.
-
assert (HL255 : L = 255).
{ rewrite YO3v.branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
rewrite U_SExt, (U_atom _ 930 L) in Hc by first [m_ewT | clear - HL1 HL255a; lia].
rewrite U_SLit in Hc. change (2 ^ Z.of_N 16) with 65536 in Hc. rewrite Z.mod_small in Hc by (clear - HL1 HL255a; lia).
rewrite (zcanon_id L) in Hc by (unfold M64; clear - HL1 HL255a; lia). change (zcanon 255) with 255 in Hc. clear - Hc HL255a. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83db4.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => alloc_ceiling <= a \/ (F <= a < F + 32 \/ F + 5152 <= a < F + 8192) \/ r <= a < r + 64 \/ tb <= a < tb + 48) Hceil Hslo FFS UN6.
clear HF HFr HG.
norm_ss HS.
idtac "OK-RUN-CX".
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HCLm2 : m_CLmem (w_H W3) (ms_mem msX) pp dn F tail st tns) end.
{ apply (m_CLmem_kept (w_H W3) (w_H W3) (ms_mem ms3) _ pp dn F tail st tns (conj CA1 (conj CA2 (conj CA3 CA4)))).
- intros i Hi. rewrite Hzl in Hi. pose proof (req_size_pos (3 * T) ltac:(clear - HT24; lia)) as Hrq.
destruct (Hoff3 pp _ Hpp_l (pp + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). exact (UN6 _ Hq1 Hq2).
- intros i Hi. rewrite zlen_fr_vals, Hlen_E in Hi. pose proof (req_size_pos (4 * cnt) ltac:(clear - HcntT; lia)) as Hrq.
destruct (Hoff3 dn _ Hdn_l (dn + i) ltac:(clear - Hi Hrq; lia)) as (Hq1 & Hq2). exact (UN6 _ Hq1 Hq2).
- intros j Hj i Hi. destruct (Hoff3 _ _ (Hnode_l _ (Htns_in j Hj)) (tn_addr (tnth tns j) + i) ltac:(change (req_size NODE_SIZE) with 56; unfold NODE_SIZE in Hi; clear - Hi; lia)) as (Hq1 & Hq2).
exact (UN6 _ Hq1 Hq2).
- intros i Hi.
assert (Hq1 : 0 <= F + 32 + i < 2 ^ 64) by (clear - Hi HFrng Hntns HFceil C1; lia).
assert (Hq2 : ~ (alloc_ceiling <= F + 32 + i \/ (F <= F + 32 + i < F + 32 \/ F + 5152 <= F + 32 + i < F + 8192) \/ r <= F + 32 + i < r + 64 \/ tb <= F + 32 + i < tb + 48))
by (unfold gbox in HdF_r, HdF_tb; clear - Hi Hntns HFceil HdF_r HdF_tb; lia).
exact (UN6 _ Hq1 Hq2). }
idtac "OK-OKG-CX".
pose proof (cinv_root_ok cnt ent _ Hcinv) as TOK. fold ns L in TOK. rewrite HL255 in TOK.
pose proof (cinv_par_ok cnt ent _ Hcinv) as PO. fold ns in PO.
pose proof (tree_ok_node _ _ _ TOK) as [Hm0' Hh1'].
destruct HCLm2 as (_ & _ & NMx & _).
set (tx := build ns tns 0 (Z.to_nat 255)).
assert (Hroot_x : troot tx = tn_addr (tnth tns 0)).
{ subst tx. rewrite build_root by exact Hh1'. reflexivity. }
assert (Hnn_x : Z.of_nat (length (tree_nodes tx)) = elen tns).
{ subst tx. rewrite (Permutation_length (build_nodes_root ns tns _ PO TOK)), length_map, YP14.zseq_length.
rewrite Z2Nat.id by (rewrite Hlen_ns; clear - HL1; lia). symmetry. exact Hlen_tns. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hat_x : tree_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) tx) end.
{ subst tx. apply (build_at trbsegs _ ns tns _ 0 TOK). intros j Hj. rewrite <- Hlen_tns in Hj.
destruct (Hmatch j Hj) as (_ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tz). split; [exact (NMx j Hj) | split; [exact Wl | exact Tz]]. }
assert (Hfull_x : tree_full tx).
{ subst tx. apply (build_full ns tns _ 0 TOK). intros j Hj Hl. destruct (cinv_kids cnt ent _ Hcinv j Hj Hl) as (c & K0 & K1 & _). exists c. split; assumption. }
assert (Hh_x : (tree_height tx <= Z.to_nat TREE_HMAX)%nat).
{ subst tx. pose proof (build_height ns tns 0 (Z.to_nat 255)) as Hbh. unfold TREE_HMAX. clear - Hbh. lia. }
assert (Hwf_x : tree_forall tnode_wf tx).
{ subst tx. apply (build_forall tnode_wf ns tns _ 0 PO TOK). intros j Hj. rewrite <- Hlen_tns in Hj. exact (proj1 (proj2 (proj2 (proj2 (Hmatch j Hj))))). }
assert (Hbl_x : Permutation (tree_blocks tx) (m_node_blocks tns)).
{ subst tx. eapply Permutation_trans; [apply (build_blocks_root ns tns _ PO TOK)|]. rewrite <- Hlen_tns. rewrite (m_node_blocks_zseq tns). apply Permutation_refl. }
assert (Hmo_x : tree_forall tnode_means_ok tx).
{ subst tx. apply (build_forall tnode_means_ok ns tns _ 0 PO TOK). intros j Hj. rewrite <- Hlen_tns in Hj. exact (MOK j Hj). }
idtac "OK-TREE-CX".
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; clear; lia).
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as (_ & _ & _ & _ & _ & _ & _ & [_ R42v] & [_ R44v] & _).
cbn [fst snd N.to_nat Z.of_N] in R42v, R44v.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rc620 : ew Ev 620 = Z_to_bv 64 cnt) by m_ewT;
assert (X40 : ew Ev 40 = Z_to_bv 64 Hd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E40);
assert (X39 : ew Ev 39 = Z_to_bv 64 Wd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E39);
assert (X46 : ew Ev 46 = Z_to_bv 64 fmt) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E46) end.
m_add_cond HS BC_NE (SExt true 32 (SOff 620 0)) (SLit 0) ltac:(apply (cx_cond_cnt_nz _ 620 cnt Rc620); clear - HcntT HT24; lia).
m_add_cond HS BC_LTU (SLit 255) (SOff 620 0) ltac:(apply (cx_cond_cnt_gt _ 620 cnt Rc620); clear - HcntT HT24; lia).
m_add_cond HS BC_NE (SMdw M_MUL (SOff 40 0) (SOff 39 0)) (SLit 0)
ltac:(apply (cx_cond_N_nz _ 40 39 Hd Wd X40 X39 R44v R42v); rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia).
m_add_cond HS BC_GEU (SLit 1) (SAluw ALU_ADD (SExt true 32 (SOff 46 0)) (SLit (-3))) ltac:(apply (cx_cond_fmt _ 46 fmt X46 Hfmt)).
idtac "OK-CX-CONDS".
ga_join HS ss_CX2 2000%nat rga_deads_CX2 ltac:(idtac).
idtac "OK-JOIN-CXA".
m_join_win HS ss_CX 800%nat rga_deads_CX ltac:(idtac).
idtac "OK-JOIN-CXB".
rga_hand RCX HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, tx.
split; [split; [rewrite Hnn_x; exact Hk0 | rga_bud_tac Hbud]|].
split; [rewrite Hnn_x; exact Hntns|].
split; [exact Hfmt|].
split. { eapply Permutation_trans; [exact HPm3|]. change CHT_SIZE with 48. repeat apply Permutation_app_head. apply Permutation_sym. exact Hbl_x. }
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [rewrite Hroot_x; m_ewT|].
split; [exact Hat_x|]. split; [exact Hfull_x|]. split; [exact Hh_x|]. split; [exact Hwf_x | exact Hmo_x].
Qed.
End e.
End d.

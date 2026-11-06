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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YCpo YCpq YClz YCqd YCqe YCpy YCq3 YCq4 YCq6 YCq5 YP14 YP15 YI0d YI0h YChh YCia YCm1 YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCop.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCqg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClc YCkr YCks YCkt YCku YClv.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP3 : forall n : nat,
rga_fromA B ss_RT (fun _ => INV_RT B (S n)) -> rga_fromA B ss_M1 (fun _ => INV_M1 B (S n)) -> rga_from B ss_FD (INV_FD B (S n)).
Proof.
intros n RRT RM1. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & pc0 & js & HTRIP & (R480 & Hpix3) & Hjs & R521 & R522).
unfold g_trip in HTRIP. rga_cbn_cx HTRIP. rga_cbn_cx R480. rga_cbn_cx Hpix3.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav)).
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_FD in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (Hcnt0 & _) & _).
assert (HT24 : 524309 <= ht_T Ht <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
assert (Hcnt64 : 0 <= ht_cnt Ht < 2 ^ 64) by (clear - Hcnt0 HT24; lia).
assert (Himg_in : In (img, fmt * N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. left.
unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himg_in3 : In (img, fmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Himg_in]).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 img _ HAR3 Himg_in3 ltac:(clear - HfN; lia)) as (Himg4096 & Himgceil & Himg16 & Himgpres).
assert (Bimg : 0 <= img < 2 ^ 64) by (clear - Himg4096 Himgceil HfN C1; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx (ht_T Ht)).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) lrest)
by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Himg_l : In (img, fmt * N) lrest).
{ subst lrest. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Hpxoff : forall kk, 0 <= kk < fmt -> 0 <= img + fmt * ix + kk < 2 ^ 64 /\ ~ (m_ZsP F r (img + fmt * ix + kk) \/ tb <= img + fmt * ix + kk < tb + 48)).
{ intros kk Hkk. apply (Hoff3 img (fmt * N) Himg_l). pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as [_ Hrq]. clear - Hkk Hfmt Hix Hrq. nia. }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
idtac "OK-B".
assert (Hcht_in3 : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) (ablocks B ly3 S3)).
{ intros b sz Hb. eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app. right. apply in_or_app. right. right. exact Hb. }
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hpp_in3 : In (pp, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hxx_in3 : In (xx, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fq _ HAR3 Hfq_in3 ltac:(clear - HT24; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
destruct (g_blk B LAWS _ _ _ _ _ hh _ HAR3 Hhh_in3 ltac:(clear - HT24; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
destruct (g_blk B LAWS _ _ _ _ _ uu _ HAR3 Huu_in3 ltac:(clear - HT24; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
destruct (g_blk B LAWS _ _ _ _ _ pp _ HAR3 Hpp_in3 ltac:(clear - HT24; lia)) as (Hpp4096 & Hppceil & Hpp16 & Hpppres).
destruct (g_blk B LAWS _ _ _ _ _ xx _ HAR3 Hxx_in3 ltac:(clear - HT24; lia)) as (Hxx4096 & Hxxceil & Hxx16 & Hxxpres).
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil HT24 C1; lia).
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil HT24 C1; lia).
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil HT24 C1; lia).
assert (Bpp : 0 <= pp < 2 ^ 64) by (clear - Hpp4096 Hppceil HT24 C1; lia).
assert (Bxx : 0 <= xx < 2 ^ 64) by (clear - Hxx4096 Hxxceil HT24 C1; lia).
assert (Bix : 0 <= ix < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
assert (BT : 0 <= ht_T Ht < 2 ^ 64) by (clear - HT24; lia).
idtac "OK-BLK".
pose proof (inv_T_pos Ht ent Hinv) as HTpos.
set (hs := cyc (ht_T Ht) (hash0 (ht_T Ht) pc0) js) in *.
assert (Hhs : 0 <= hs < ht_T Ht) by (subst hs; apply cyc_range; exact HTpos).
set (uv := usedz Ht hs).
assert (Huv : uv = 0 \/ uv = 1) by (subst uv; exact (inv_used01 Ht ent Hinv hs Hhs)).
destruct Harr as (Af & Ak & Au & Ap & Ax).
assert (Vuv : mbyte trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (uu + hs) = Some (Z_to_bv 8 uv)).
{ destruct (Au (Z.to_nat hs) ltac:(clear - Hhs L1; unfold zlen in L1; lia)) as [Vb _]. rewrite Z2Nat.id in Vb by (clear - Hhs; lia). exact Vb. }
idtac "OK-PRE".
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ uu (ht_T Ht) HAR3 Huu_in3) as (_ & Huuzone & _ & _).
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as [_ HrqT].
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ uu (ht_T Ht) 7 fpos HAR3 Huu_in3 Hfin3) as HdF_uu.
unfold zdisjoint in HdF_uu. cbn [fst snd] in HdF_uu. change (fs_frame_bytes 7) with 8192 in HdF_uu. rewrite EFA3 in HdF_uu. fold F in HdF_uu.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ uu (ht_T Ht) cid pos HAR3 Huu_in3 HfinS3) as HdC_uu.
unfold zdisjoint in HdC_uu. cbn [fst snd] in HdC_uu. rewrite EFA3 in HdC_uu.
assert (Huu_l : In (uu, ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (uu, ht_T Ht) HAR3 HPrt3 ltac:(right; exact Huu_l)) as HzR_uu.
unfold zdisjoint, block_rng in HzR_uu. cbn [fst snd] in HzR_uu. change (req_size RGB_SIZE) with 64 in HzR_uu.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (uu, ht_T Ht) HAR3 HPtb3 ltac:(right; exact Huu_l)) as HzT_uu.
unfold zdisjoint, block_rng in HzT_uu. cbn [fst snd] in HzT_uu. change (req_size 48) with 48 in HzT_uu.
assert (Hcell_rng : 4096 <= uu + hs /\ uu + hs + 1 <= alloc_ceiling) by (clear - Huu4096 Huuceil Hhs; lia).
g_havoc HS 620%nat [Z_to_bv 64 (uu + hs); Z_to_bv 64 uv].
g_havoc_val HS 620%nat 0%nat (Z_to_bv 64 (uu + hs)) E620.
g_havoc_val HS 620%nat 1%nat (Z_to_bv 64 uv) E621.
m_env_fold HS AG.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE1 end.
idtac "OK-CELL2".
assert (Huv8 : 0 <= uv < 256) by (clear - Huv; lia).
g_region HS AG (YQ0b.mkRegion (Some 620%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 621 0))])
ltac:(rewrite E620, unsigned_lit_small by (clear - Hcell_rng C1; lia);
split; [clear - Hcell_rng; lia|]; split; [clear - Hcell_rng C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trbsegs _ _ (uu + hs) _ _ (SOff 621 0) uv);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E621 | clear - Huv8; lia | cbn; clear; lia
| apply (YI0d.val_mem_byte trbsegs); [rewrite Z.add_0_r; exact Vuv | exact Huv8]] | apply Forall_nil] ])
ltac:(first [ clear - Hcell_rng Hceil Hslo FFS Hhs HrqT; lia
| destruct Huuzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs HrqT HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_uu Hhs HrqT; lia
| clear - HdC_uu Hhs HrqT Hflo Hfhi; lia
| clear - HzR_uu Hhs HrqT; lia
| clear - HzT_uu Hhs HrqT; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CELL3".
assert (Bhs : 0 <= hs < 2 ^ 64) by (clear - Hhs HT24; lia).
assert (Bcell : 0 <= uu + hs < 2 ^ 64) by (clear - Hcell_rng C1; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 475 0) (SOff 521 0)) (SOff 620 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 620 _ E620 Bcell); apply (U_add_small_q _ _ _ uu hs (U_atom _ 475 uu Ruu Buu) (U_atom _ 521 hs R521 Bhs)); [clear - Buu; lia | clear - Bhs; lia | clear - Bcell; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
g_fact HS 620%nat (mkAF 4096 140737479966720 0)
ltac:(rewrite E620, unsigned_lit_small by exact Bcell; change (2 ^ 0) with 1; split; [clear - Hcell_rng C1; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_fact HS 621%nat (mkAF 0 1 0)
ltac:(rewrite E621, unsigned_lit_small by (clear - Huv; lia); change (2 ^ 0) with 1; split; [clear - Huv; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_cond HS BC_GEU (SOff 620 0) (SOff 475 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 620 0) (SOff 475 0) (uu + hs) uu (U_atom _ 620 _ E620 Bcell) (U_atom _ 475 uu Ruu Buu)); clear - Hhs; lia).
reshok_bx HS 44%nat.
idtac "OK-AL1".
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x829f8.
idtac "OK-AL2".
all: try (m_obl_cell HJ3 E620 E44 Huu_in3 ltac:(idtac; first [clear - Hcell_rng C1; lia | clear - Hhs HrqT; lia])).
all: try (ga_obl_blk HJ3 Rtb E44 Htb_in3).
idtac "OK-OBL0".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-KEPT0".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
2: {
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (E621x : ew Ex 621 = Z_to_bv 64 uv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E621) end.
rewrite branch_eq_U, (U_atom _ 621 uv E621x ltac:(clear - Huv; lia)) in Hc. change (U _ (SLit 0)) with 0 in Hc. apply Z.eqb_neq in Hc. clear E621x.
assert (Huv1 : uv = 1) by (clear - Huv Hc; lia).
assert (Hin : in_slot Ht hs) by (split; [exact Hhs | fold uv; exact Hc]).
set (fv := freq Ht hs).
destruct (arr32_getz trbsegs _ fq (ht_frequ Ht) hs Af ltac:(rewrite L3; exact Hhs)) as [Vfv Hfv32]. fold (freq Ht hs) in Vfv, Hfv32. fold fv in Vfv, Hfv32.
idtac "OK-H0".
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) HAR3 Hfq_in3) as (_ & Hfqzone & _ & _).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq4T].
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) 7 fpos HAR3 Hfq_in3 Hfin3) as HdF_fq.
unfold zdisjoint in HdF_fq. cbn [fst snd] in HdF_fq. change (fs_frame_bytes 7) with 8192 in HdF_fq. rewrite EFA3 in HdF_fq. fold F in HdF_fq.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) cid pos HAR3 Hfq_in3 HfinS3) as HdC_fq.
unfold zdisjoint in HdC_fq. cbn [fst snd] in HdC_fq. rewrite EFA3 in HdC_fq.
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (fq, 4 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hfq_l)) as HzR_fq.
unfold zdisjoint, block_rng in HzR_fq. cbn [fst snd] in HzR_fq. change (req_size RGB_SIZE) with 64 in HzR_fq.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (fq, 4 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hfq_l)) as HzT_fq.
unfold zdisjoint, block_rng in HzT_fq. cbn [fst snd] in HzT_fq. change (req_size 48) with 48 in HzT_fq.
assert (SEP5 : g_sep5 fq hh uu pp xx (ht_T Ht)).
{ apply (g_sep5_of_AR B LAWS ly3 S3 _ _ _ (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ [(tb, 48)]) fq hh uu pp xx (ht_T Ht) HAR3); [|exact HTpos].
eapply Permutation_trans; [exact HPm3|]. rewrite <- !app_assoc. reflexivity. }
assert (Hfcell_rng : 4096 <= fq + 4 * hs /\ fq + 4 * hs + 4 <= alloc_ceiling) by (clear - Hfq4096 Hfqceil Hhs Hrq4T; lia).
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Vfv1 : val_mem trbsegs (mrestrict (w_H W3) mF) (fq + 4 * hs) 4 fv) end.
{ apply (g_val_mem_kept (w_H W3) (ms_mem ms3) _ _ _ _ Vfv). intros kk Hkk.
destruct (Hoff3 fq (4 * ht_T Ht) Hfq_l (fq + 4 * hs + kk) ltac:(clear - Hkk Hhs Hrq4T; cbn in Hkk; lia)) as [Hq1 Hq2]. exact (KP _ Hq1 Hq2). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ fq (4 * ht_T Ht) (proj1 HJ3) Hfq_in3) as (_ & _ & _ & _ & Hfqpres1 & _).
g_havoc HS 630%nat [Z_to_bv 64 (fq + 4 * hs); Z_to_bv 64 fv].
g_havoc_val HS 630%nat 0%nat (Z_to_bv 64 (fq + 4 * hs)) E630.
g_havoc_val HS 630%nat 1%nat (Z_to_bv 64 fv) E631.
m_env_fold HS AG.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE2 end.
idtac "OK-H1".
assert (Bfcell : 0 <= fq + 4 * hs < 2 ^ 64) by (clear - Hfcell_rng C1; lia).
g_region HS AG (YQ0b.mkRegion (Some 630%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 631 0))])
ltac:(rewrite E630, unsigned_lit_small by exact Bfcell;
split; [clear - Hfcell_rng; lia|]; split; [clear - Hfcell_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hfqpres1 (fq + 4 * hs + o) ltac:(clear - Ho Hhs Hrq4T; lia)))
| apply Forall_cons; [eapply (chunk_ok_val trbsegs _ _ (fq + 4 * hs) _ _ (SOff 631 0) fv);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E631 | exact Hfv32 | cbn; clear; lia
| rewrite Z.add_0_r; exact Vfv1] | apply Forall_nil] ])
ltac:(first [ clear - Hfcell_rng Hceil Hslo FFS Hhs Hrq4T; lia
| destruct Hfqzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hhs Hrq4T HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_fq Hhs Hrq4T; lia
| clear - HdC_fq Hhs Hrq4T Hflo Hfhi; lia
| clear - HzR_fq Hhs Hrq4T; lia
| clear - HzT_fq Hhs Hrq4T; lia
| unfold g_sep5 in SEP5; clear - SEP5 Hhs HrqT Hrq4T; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-H2".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 473 0) (SAlu ALU_SLL (SOff 521 0) (SLit 2))) (SOff 630 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 630 _ E630 Bfcell); replace (fq + 4 * hs) with (fq + hs * 2 ^ 2) by (clear; lia);
apply (U_add_small_q _ _ _ fq (hs * 2 ^ 2) (U_atom _ 473 fq Rfq Bfq)
(U_sll_small_q _ _ hs 2 (U_atom _ 521 hs R521 Bhs) ltac:(clear - Hhs; lia) ltac:(clear; lia) ltac:(clear - Hhs HT24; lia)));
[ clear - Bfq; lia | clear - Hhs; lia | clear - Bfcell; lia ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
g_fact HS 630%nat (mkAF 4096 140737479966720 2)
ltac:(rewrite E630, unsigned_lit_small by exact Bfcell; change (2 ^ 2) with 4; split; [clear - Hfcell_rng C1; lia|]; split; [pose proof (Z.div_mod fq 16 ltac:(clear; lia)) as D16; rewrite Hfq16, Z.add_0_r in D16; rewrite D16; replace (16 * (fq / 16) + 4 * hs) with ((4 * (fq / 16) + hs) * 4) by (clear; lia); apply Z_mod_mult | clear; lia]).
g_fact HS 631%nat (mkAF 0 4294967295 0)
ltac:(rewrite E631, unsigned_lit_small by (clear - Hfv32; lia); change (2 ^ 0) with 1; split; [clear - Hfv32; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_cond HS BC_GEU (SOff 630 0) (SOff 473 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 630 0) (SOff 473 0) (fq + 4 * hs) fq (U_atom _ 630 _ E630 Bfcell) (U_atom _ 473 fq Rfq Bfq)); clear - Hhs; lia).
reshok_bx HS 44%nat.
idtac "OK-H3".
lazymatch type of KP with forall a, _ -> _ -> aview _ ?Hn ?mn a = aview _ ?H0 ?m0 a =>
assert (KPc : forall a, 0 <= a < 2 ^ 64 -> ~ ((m_ZsP F r a \/ tb <= a < tb + 48) \/ fq + 4 * hs <= a < fq + 4 * hs + 4) -> aview trbsegs Hn mn a = aview trbsegs H0 m0 a)
by (intros a Ha Hn'; apply (KP a Ha); intros Hx; apply Hn'; left; exact Hx) end.
clear KP. rename KPc into KP.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x829f8.
idtac "OK-H4".
all: try (m_obl_cell HJ3 E630 E44 Hfq_in3 ltac:(idtac; first [clear - Hfcell_rng C1; lia | clear - Hhs Hrq4T; lia])).
all: try (ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(m_awr_cell 630%nat E630 fq Afq Hfq_in3 ltac:(idtac; first [clear - Hfcell_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hhs Hrq4T; lia end])).
g_kept_run HFr AG (fun a : Z => (m_ZsP F r a \/ tb <= a < tb + 48) \/ fq + 4 * hs <= a < fq + 4 * hs + 4) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-H5".
pose proof Hinv as (_ & _ & _ & I4 & _). destruct (I4 hs Hin) as (Hcx & Hnth & Hfv1). fold fv in Hnth, Hfv1.
pose proof (zsum_pos_le ent _ _ _ (ent_freq_pos Ht ent Hinv) Hnth) as Hfvz.
assert (Hfv_s : 1 <= fv <= 10000) by (clear - Hfv1 Hfvz Hsum Hix HN; unfold RGB_NMAX in HN; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (E631z : ew Ex 631 = Z_to_bv 64 fv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E631);
assert (HB630 : bv_unsigned (ew Ex 630) = fq + 4 * hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E630; apply unsigned_lit_small; exact Bfcell);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 630%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 630 (fq + 4 * hs) cs lo hi wlo whi 0 4%N (SAlu ALU_ADD (SExt true 32 (SOff 631 0)) (SLit 1)) HRc HB630 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vnew;
change (bv_unsigned (sv_denot Ex (SAlu ALU_ADD (SExt true 32 (SOff 631 0)) (SLit 1)))) with (U Ex (SAlu ALU_ADD (SExt true 32 (SOff 631 0)) (SLit 1))) in Vnew;
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vnew;
rewrite (U_add_small_q Ex (SExt true 32 (SOff 631 0)) (SLit 1) fv 1 (U_sext32_small Ex 631 fv E631z ltac:(clear - Hfv_s; lia)) ltac:(reflexivity) ltac:(clear - Hfv_s; lia) ltac:(clear; lia) ltac:(clear - Hfv_s; lia)) in Vnew;
rewrite Z.mod_small in Vnew by (clear - Hfv_s; lia)
end; clear HRc end.
rewrite Z.add_0_r in Vnew. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew.
idtac "OK-H6".
change (N.to_nat 4) with 4%nat in Vnew.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rcntz : ew Ex 478 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (ht_cnt Ht)) ltac:(exact (g_denot_off0 _ 478 _ Rcntz Hcnt64)) QC.
ra_join_slots HS ss_RT 700%nat rga_deads_RT [(Some 305%nat, 0, 40)]
ltac:(idtac; ga_join_val HS 700%nat 16%nat QC N716;
ga_join_fact HS 716%nat (mkAF 0 16777216 0) ltac:(rewrite N716; rewrite unsigned_lit_small by exact Hcnt64; change (2 ^ 0) with 1; split; [clear - Hcnt0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-H7".
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hpp_l : In (pp, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hxx_l : In (xx, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq3T].
assert (SEPK : forall a, g_in5 fq hh uu pp xx (ht_T Ht) a -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros a [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (Hoff3 fq (4 * ht_T Ht) Hfq_l) | apply (Hoff3 hh (3 * ht_T Ht) Hhh_l) | apply (Hoff3 uu (ht_T Ht) Huu_l) | apply (Hoff3 pp (3 * ht_T Ht) Hpp_l) | apply (Hoff3 xx (4 * ht_T Ht) Hxx_l) ];
clear - Ha Hrq4T Hrq3T HrqT; lia. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx (ht_hit Ht hs)) end.
{ apply (g_cht_hit (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht hs (conj Af (conj Ak (conj Au (conj Ap Ax)))) L1 L2 L3 L4 L5 SEP5 Hhs); [fold fv; clear - Hfv_s; lia | fold fv; exact Vnew |].
intros a Ha Hn. destruct (SEPK a Ha) as [Hq1 Hq2]. apply (KP a Hq1). intros [Hx | Hx]; [exact (Hq2 Hx) | exact (Hn Hx)]. }
pose proof (ht_hit_inv Ht ent Hinv hs Hin) as Hinv1.
pose proof (ht_hit_sum Ht ent Hinv hs Hin) as Hsum1.
assert (Hsum2 : zsum (map snd (lset ent (Z.to_nat (cidx Ht hs)) (key Ht hs, freq Ht hs + 1))) <= ix + 1) by (rewrite Hsum1; clear - Hsum; lia).
rga_hand RRT HS HJ3 k; [rga_E_tac HEE2 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, (ht_hit Ht hs), (lset ent (Z.to_nat (cidx Ht hs)) (key Ht hs, freq Ht hs + 1)).
rga_cbn_cx_goal. m_inv_auto.
}
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (E621x : ew Ex 621 = Z_to_bv 64 uv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E621) end.
rewrite branch_eq_U, (U_atom _ 621 uv E621x ltac:(clear - Huv; lia)) in Hc. change (U _ (SLit 0)) with 0 in Hc. apply Z.eqb_eq in Hc. clear E621x.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rhhx : ew Ex 474 = Z_to_bv 64 hh) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh);
assert (R521x : ew Ex 521 = Z_to_bv 64 hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R521) end.
g_cond HS BC_GEU (SAlu ALU_ADD (SOff 474 0) (SMd M_MUL (SOff 521 0) (SLit 3))) (SOff 474 0)
ltac:(apply (g_ptr_geu _ _ _ hh (hs * 3) (U_atom _ 474 hh Rhhx Bhh));
[ apply (g_U_mul_small _ (SOff 521 0) (SLit 3) hs 3 (U_atom _ 521 hs R521x Bhs) ltac:(reflexivity)); clear - Hhs HT24; lia | clear - Bhh; lia | clear - Hhs; lia | clear - Hhhceil Hhs HT24 C1; lia ]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_asan_memcpy.
idtac "OK-I0".
all: try (lazymatch goal with |- range_addressable _ (U ?Ev _) _ _ =>
assert (Rtbv : ew Ev 305 = Z_to_bv 64 tb) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb);
assert (E44v : ew Ev 44 = Z_to_bv 64 SB) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E44) | _ => idtac end).
all: try (ga_obl_blk HJ3 Rtbv E44v Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-I1".
ga_join HS ss_M1 640%nat rga_deads_M1 ltac:(idtac).
idtac "OK-I2".
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht (conj Af (conj Ak (conj Au (conj Ap Ax)))) L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2)
| assert (Hpix1 : pixel_at trbsegs (mrestrict (w_H W3) mF) (img + fmt * ix) fmt pc0 true);
[ apply (g_pixel_at_kept (w_H W3) (ms_mem ms3) mF _ _ _ _ Hpix3 Hfmt); intros kk Hkk; destruct (Hpxoff kk Hkk) as [Hq1 Hq2]; exact (KP _ Hq1 Hq2) | ] ] end.
rga_hand RM1 HS HJ3 k; [rga_E_tac HEE1 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, pc0, js.
split; [unfold g_trip; rga_cbn_cx_goal; m_inv_auto|].
split; [unfold g_pix; rga_cbn_cx_goal; split; [m_ewT | exact Hpix1]|].
split; [exact Hjs|]. fold hs. split; [fold uv; exact Hc|]. split; m_ewT.
Qed.
End d.
End c.

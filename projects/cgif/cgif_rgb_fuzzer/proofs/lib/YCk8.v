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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YCkr YCks YCkt YClv.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_tra.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP2 : forall n m : nat,
rga_fromA B ss_FD (fun _ => INV_FD B (S n)) -> (forall m', m = S m' -> rga_fromA B ss_PB (fun _ => INV_PB B (S n) m')) -> rga_from B ss_PB (INV_PB B (S n) m).
Proof.
intros n m RFD RNEXT. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & pc0 & js & jj & HTRIP & (R480 & Hpix3) & Hjs & Hjj & Hm & R520 & R521 & R522).
unfold g_trip in HTRIP. rga_cbn_cx HTRIP. rga_cbn_cx R480. rga_cbn_cx Hpix3.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav)).
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_PB in HS.
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
set (hs := cyc (ht_T Ht) (hash0 (ht_T Ht) pc0) jj) in *.
assert (Hhs : 0 <= hs < ht_T Ht) by (subst hs; apply cyc_range; exact HTpos).
set (uv := usedz Ht hs).
assert (Huv : uv = 0 \/ uv = 1) by (subst uv; exact (inv_used01 Ht ent Hinv hs Hhs)).
destruct Harr as (Af & Ak & Au & Ap & Ax).
assert (Vuv : mbyte trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (uu + hs) = Some (Z_to_bv 8 uv)).
{ destruct (Au (Z.to_nat hs) ltac:(clear - Hhs L1; unfold zlen in L1; lia)) as [Vb _]. rewrite Z2Nat.id in Vb by (clear - Hhs; lia). exact Vb. }
idtac "OK-CELL1".
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
g_havoc HS 538%nat [Z_to_bv 64 (uu + hs); Z_to_bv 64 uv].
g_havoc_val HS 538%nat 0%nat (Z_to_bv 64 (uu + hs)) E538.
g_havoc_val HS 538%nat 1%nat (Z_to_bv 64 uv) E539.
m_env_fold HS AG.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE1 end.
idtac "OK-CELL2".
assert (Huv8 : 0 <= uv < 256) by (clear - Huv; lia).
g_region HS AG (YQ0b.mkRegion (Some 538%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 539 0))])
ltac:(rewrite E538, unsigned_lit_small by (clear - Hcell_rng C1; lia);
split; [clear - Hcell_rng; lia|]; split; [clear - Hcell_rng C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trbsegs _ _ (uu + hs) _ _ (SOff 539 0) uv);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E539 | clear - Huv8; lia | cbn; clear; lia
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
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 475 0) (SOff 520 0)) (SOff 538 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 538 _ E538 Bcell); apply (U_add_small_q _ _ _ uu hs (U_atom _ 475 uu Ruu Buu) (U_atom _ 520 hs R520 Bhs)); [clear - Buu; lia | clear - Bhs; lia | clear - Bcell; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
g_fact HS 538%nat (mkAF 4096 140737479966720 0)
ltac:(rewrite E538, unsigned_lit_small by exact Bcell; change (2 ^ 0) with 1; split; [clear - Hcell_rng C1; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_fact HS 539%nat (mkAF 0 1 0)
ltac:(rewrite E539, unsigned_lit_small by (clear - Huv; lia); change (2 ^ 0) with 1; split; [clear - Huv; lia|]; split; [apply Z.mod_1_r | clear; lia]).
reshok_bx HS 44%nat.
idtac "OK-AL1".
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x8270c.
idtac "OK-AL2".
all: try (m_obl_cell HJ3 E538 E44 Huu_in3 ltac:(idtac; first [clear - Hcell_rng C1; lia | clear - Hhs HrqT; lia])).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-OBL".
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
2: {
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (E539x : ew Ex 539 = Z_to_bv 64 uv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E539) end.
rewrite branch_eq_U, (U_atom _ 539 uv E539x ltac:(clear - Huv; lia)) in Hc. change (U _ (SLit 0)) with 0 in Hc. apply Z.eqb_neq in Hc. clear E539x.
assert (Huv1 : uv = 1) by (clear - Huv Hc; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_bcmp_tra.
idtac "OK-U1".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-U2".
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rhhx : ew Ex 474 = Z_to_bv 64 hh) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh);
assert (R521x : ew Ex 521 = Z_to_bv 64 hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R521) end.
g_cond HS BC_GEU (SAlu ALU_ADD (SOff 474 0) (SMd M_MUL (SOff 521 0) (SLit 3))) (SOff 474 0)
ltac:(apply (g_ptr_geu _ _ _ hh (hs * 3) (U_atom _ 474 hh Rhhx Bhh));
[ apply (g_U_mul_small _ (SOff 521 0) (SLit 3) hs 3 (U_atom _ 521 hs R521x Bhs) ltac:(reflexivity)); clear - Hhs HT24; lia | clear - Bhh; lia | clear - Hhs; lia | clear - Hhhceil Hhs HT24 C1; lia ]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_bcmp_tra.
idtac "OK-U3".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-U4".
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (R480x : ew Ex 480 = Z_to_bv 64 (img + fmt * ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R480) end.
assert (Bpx : 0 <= img + fmt * ix < 2 ^ 64) by (clear - Himg4096 Himgceil Hfmt Hix HfN C1; nia).
assert (Hpx : 0 <= fmt * ix /\ fmt * ix + fmt <= fmt * N) by (clear - Hfmt Hix; nia).
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as [_ HrqfN].
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq3T].
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (img + fmt * ix) ltac:(apply (U_atom _ 480 _ R480x Bpx)) Ha0.
rregU HS (11%bv : bv 5) (hh + hs * 3)
ltac:(apply (U_add_small_q _ _ _ hh (hs * 3) (U_atom _ 474 hh Rhhx Bhh));
[ apply (g_U_mul_small _ (SOff 521 0) (SLit 3) hs 3 (U_atom _ 521 hs R521x Bhs) ltac:(reflexivity)); clear - Hhs HT24; lia | clear - Bhh; lia | clear - Hhs; lia | clear - Hhhceil Hhs HT24 C1; lia ]) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) (proj1 HJ3) Himg_in3) as (_ & _ & _ & _ & HimgP & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hh (3 * ht_T Ht) (proj1 HJ3) Hhh_in3) as (_ & _ & _ & _ & HhhP & _).
assert (HWIN : forall a, 0 <= a < alloc_ceiling -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs + -576 - 2 * ESTACK <= a < spZ regs + -576))
by (intros a Ha; rewrite Hes; clear - Ha Hceil Hslo FFS C1; lia).
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
idtac "OK-CALL0".
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_bcmp_at trbsegs B LAWS Hsegs A_bcmp_tra ABCMP W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 mdX k (img + fmt * ix) (hh + hs * 3) 3 (-576) (Z_to_bv 64 0x826d4) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Bpx; lia.
- clear - Himgceil HrqfN Hpx Hfmt C1; lia.
- clear - Bhh Hhs; lia.
- clear - Hhhceil Hhs HT24 C1; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (proj1 (HimgP a ltac:(clear - Ha Hpx HrqfN Hfmt; lia)))|].
intros Hw. rewrite HspT, Hes in Hw. clear - Hw Ha Himgceil HrqfN Hpx Hfmt Hceil Hslo FFS C1. lia.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (proj1 (HhhP a ltac:(clear - Ha Hhs Hrq3T; lia)))|].
intros Hw. rewrite HspT, Hes in Hw. clear - Hw Ha Hhhceil Hhs Hrq3T Hceil Hslo FFS C1. lia.
- intros a Ha. apply (HWIN a). clear - Ha Himg4096 Himgceil HrqfN Hpx Hfmt. lia.
- intros a Ha. apply (HWIN a). clear - Ha Hhh4096 Hhhceil Hhs Hrq3T. lia.
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) Himg_in3); clear - Hpx HrqfN Hfmt; lia.
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 W3 _ _ hh (3 * ht_T Ht) _ _ (proj1 HJ3) Hhh_in3); clear - Hhs Hrq3T; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) Himg_in3); clear - Hpx HrqfN Hfmt; lia.
- intros _; apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) Himg_in3); clear - Hpx HrqfN Hfmt; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 W3 _ _ hh (3 * ht_T Ht) _ _ (proj1 HJ3) Hhh_in3); clear - Hhs Hrq3T; lia.
- intros _; apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 W3 _ _ hh (3 * ht_T Ht) _ _ (proj1 HJ3) Hhh_in3); clear - Hhs Hrq3T; lia. }
idtac "OK-CALL1".
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ2 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HWST : forall a, spZ regs + -576 <= a < spZ regs + 0 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs + -576 - 2 * ESTACK <= a < spZ regs + -576))
by (intros a Ha; rewrite Hes; clear - Ha Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17592186044416) /\ (4096 <= r /\ r + 64 <= alloc_ceiling) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling) /\ 140735332483072 <= alloc_ceiling <= 140737479966720)
by (clear - HF4096 HFceil HF8lo HF8hi Hr4096 Hrceil Hf4096 Hfceil Hflo Hfhi C1; lia).
assert (HRtb : 4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
m_env_fold HS AG.
ga_relow HS AG E10 E11 E10n E11n.
idtac "OK-POST0".
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16]%nat AG
ltac:(idtac; first
[ m_keptW Hfr2 Hpres2 HWIN HWST HRNG AG Usp RF E67 E10n E11n
ltac:(idtac; first [ m_keptW_blk Hfr2 Hpres2 HWIN AG 305%nat tb Rtb HRtb
| m_keptW_blk Hfr2 Hpres2 HWIN AG 538%nat (uu + hs) E538 Hcell_rng
| ga_kept_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
idtac "OK-RESEAT".
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) mem2 a = aview trbsegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. rewrite (Hfr2 a Ha ltac:(unfold m_ZsP in Hn; rewrite Hes; clear - Hn Hceil Hslo FFS; lia)). exact (KP a Ha Hn). }
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ2 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
idtac "OK-POST2".
rreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite Hv in Rres. symmetry in Rres.
idtac "OK-RES".
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hkey3 : col3 trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (hh + hs * 3) (key Ht hs)).
{ replace (hh + hs * 3) with (hh + 3 * hs) by (clear; lia). unfold key. apply (arr8_col3 trbsegs _ hh (ht_keys Ht) hs Ak); [clear - Hhs; lia | rewrite L2; clear - Hhs; lia]. }
assert (Hzero : v = w64 0 <-> pc0 = key Ht hs).
{ rewrite Hcmp. rewrite <- (g_bcmp3_iff (w_H W3) (ms_mem ms3) (img + fmt * ix) (hh + hs * 3) pc0 (key Ht hs) (proj1 Hpix3) Hkey3).
assert (KX : forall i, 0 <= i < 3 -> aview trbsegs (w_H W3) (ms_mem ms1) (img + fmt * ix + i) = aview trbsegs (w_H W3) (ms_mem ms3) (img + fmt * ix + i) /\
aview trbsegs (w_H W3) (ms_mem ms1) (hh + hs * 3 + i) = aview trbsegs (w_H W3) (ms_mem ms3) (hh + hs * 3 + i)).
{ intros i Hi. split.
- destruct (Hpxoff i ltac:(clear - Hi Hfmt; lia)) as [Hq1 Hq2]. exact (KP _ Hq1 Hq2).
- destruct (Hoff3 hh (3 * ht_T Ht) Hhh_l (hh + hs * 3 + i) ltac:(clear - Hi Hhs Hrq3T; lia)) as [Hq1 Hq2]. exact (KP _ Hq1 Hq2). }
split; intros K i Hi; destruct (KX i Hi) as [K1 K2]; [rewrite <- K1, <- K2 | rewrite K1, K2]; exact (K i Hi). }
destruct (find_off_spec Ht ent Hinv pc0 js Hjs) as (Rjs & Hstop & Hbefore).
idtac "OK-ZERO".
clear KP. rename KP2 into KP.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
idtac "OK-BR2".
*
cbn [branch_taken sv_denot] in Hc0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Rres in Hc0. apply bv_eqb_eq in Hc0. apply Hzero in Hc0.
assert (Ejj : jj = js).
{ destruct (Z_lt_le_dec jj js) as [Hlt|Hge]; [|clear - Hge Hjj; lia]. exfalso. specialize (Hbefore jj ltac:(clear - Hlt Hjj; lia)). fold hs in Hbefore.
unfold slot_stop in Hbefore. rewrite <- Hc0, colour_eqb_refl, orb_true_r in Hbefore. discriminate Hbefore. }
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK GBspan 0x8270c.
idtac "OK-EQ1".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (tl (ss_mem ssx)) in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "OK-EQ2".
ga_join HS ss_FD 600%nat rga_deads_FD ltac:(idtac).
idtac "OK-FDJ".
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht (conj Af (conj Ak (conj Au (conj Ap Ax)))) L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2)
| assert (Hpix1 : pixel_at trbsegs (mrestrict (w_H W3) mF) (img + fmt * ix) fmt pc0 true);
[ apply (g_pixel_at_kept (w_H W3) (ms_mem ms3) mF _ _ _ _ Hpix3 Hfmt); intros kk Hkk; destruct (Hpxoff kk Hkk) as [Hq1 Hq2]; exact (KP _ Hq1 Hq2) | ] ] end.
rga_hand RFD HS HJ2 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, pc0, js.
split; [unfold g_trip; rga_cbn_cx_goal; m_inv_auto|].
split; [unfold g_pix; rga_cbn_cx_goal; split; [m_ewT | exact Hpix1]|].
split; [exact Hjs|]. rewrite <- Ejj. fold hs. split; m_ewT.
*
cbn [branch_taken sv_denot] in Hc0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Rres in Hc0.
assert (Hne : pc0 <> key Ht hs) by (intros Heq; apply (proj2 Hzero) in Heq; rewrite Heq in Hc0; unfold w64 in Hc0; rewrite bv_eqb_refl in Hc0; discriminate Hc0).
assert (Hjs1 : jj + 1 <= js).
{ destruct (Z.eqb_spec jj js) as [Ej|Ej]; [|clear - Ej Hjj; lia]. exfalso. pose proof Hstop as Hsj. rewrite <- Ej in Hsj. fold hs in Hsj.
unfold slot_stop in Hsj. fold uv in Hsj. replace (uv =? 0) with false in Hsj by (symmetry; apply Z.eqb_neq; exact Hc).
cbn [orb] in Hsj. apply (proj1 (colour_eqb_spec _ _)) in Hsj. exact (Hne (eq_sym Hsj)). }
destruct m as [|m']; [exfalso; clear - Hm Hjs1; cbn in Hm; lia|].
pose proof (RNEXT m' eq_refl) as RPB. clear RNEXT.
idtac "OK-NE0".
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Ruux : ew Ex 475 = Z_to_bv 64 uu) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu);
assert (RTx : ew Ex 479 = Z_to_bv 64 (ht_T Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT);
assert (R521y : ew Ex 521 = Z_to_bv 64 hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R521) end.
pose proof (probe_next_range (ht_T Ht) hs Hhs) as Hnx.
g_cond HS BC_GEU (SAlu ALU_XOR (SOff 475 0) (SLit (-1))) (YI0g.sv_nextz 521 479)
ltac:(apply (YCqg.ub_room_cond _ _ _ uu (probe_next (ht_T Ht) hs) (U_atom _ 475 uu Ruux Buu)
(YI0g.U_sv_nextz _ 521 479 hs (ht_T Ht) R521y RTx Hhs ltac:(clear - HT24; lia)));
[clear - Buu; lia | clear - Hnx; lia | clear - Huuceil Hnx HT24 C1; lia]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK GBspan 0x8267c.
idtac "OK-NE1".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-NE2".
set (nx := probe_next (ht_T Ht) hs) in *.
assert (Bnx : 0 <= nx < 2 ^ 64) by (clear - Hnx HT24; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (RTz : ew Ex 479 = Z_to_bv 64 (ht_T Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT);
assert (R521z : ew Ex 521 = Z_to_bv 64 hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R521);
assert (R522z : ew Ex 522 = Z_to_bv 64 jj) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R522) end.
assert (Bjj : 0 <= jj /\ jj + 1 < 2 ^ 64) by (clear - Hjj Hjs1 Rjs HT24; lia).
rregU HS (10%bv : bv 5) nx ltac:(exact (YI0g.U_sv_nextz _ 521 479 hs (ht_T Ht) R521z RTz Hhs ltac:(clear - HT24; lia))) Q10.
rregU HS (26%bv : bv 5) nx ltac:(exact (YI0g.U_sv_next _ 521 479 hs (ht_T Ht) R521z RTz Hhs ltac:(clear - HT24; lia))) Q26.
rregU HS (20%bv : bv 5) (jj + 1) ltac:(rewrite (U_atom_off _ 522 jj 1 R522z) by (clear - Bjj; lia); reflexivity) Q20.
idtac "OK-J0".
ra_join_slots HS ss_PB2 2100%nat rga_deads_PB2 (@nil (option nat * Z * Z))
ltac:(idtac; ga_join_val HS 2100%nat 0%nat Q10 N2100; ga_join_val HS 2100%nat 1%nat Q26 N2101; ga_join_val HS 2100%nat 2%nat Q20 N2102;
ga_join_fact HS 2100%nat (mkAF 0 16777215 0) ltac:(rewrite N2100; rewrite unsigned_lit_small by exact Bnx; change (2 ^ 0) with 1; split; [clear - Hnx HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 2101%nat (mkAF 0 16777215 0) ltac:(rewrite N2101; rewrite unsigned_lit_small by exact Bnx; change (2 ^ 0) with 1; split; [clear - Hnx HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 2102%nat (mkAF 0 16777216 0) ltac:(rewrite N2102; rewrite unsigned_lit_small by (clear - Bjj; lia); change (2 ^ 0) with 1; split; [clear - Hjj Hjs1 Rjs HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-J1".
rregU HS (10%bv : bv 5) nx ltac:(apply (U_atom _ 2100 _ N2100); exact Bnx) P10.
rregU HS (26%bv : bv 5) nx ltac:(apply (U_atom _ 2101 _ N2101); exact Bnx) P26.
rregU HS (20%bv : bv 5) (jj + 1) ltac:(apply (U_atom _ 2102 _ N2102); clear - Bjj; lia) P20.
m_join_slots_win HS ss_PB 520%nat rga_deads_PB (@nil (option nat * Z * Z))
ltac:(idtac; ga_join_val HS 520%nat 0%nat P10 N520; ga_join_val HS 520%nat 1%nat P26 N521; ga_join_val HS 520%nat 2%nat P20 N522;
ga_join_fact HS 520%nat (mkAF 0 16777215 0) ltac:(rewrite N520; rewrite unsigned_lit_small by exact Bnx; change (2 ^ 0) with 1; split; [clear - Hnx HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 521%nat (mkAF 0 16777215 0) ltac:(rewrite N521; rewrite unsigned_lit_small by exact Bnx; change (2 ^ 0) with 1; split; [clear - Hnx HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 522%nat (mkAF 0 16777216 0) ltac:(rewrite N522; rewrite unsigned_lit_small by (clear - Bjj; lia); change (2 ^ 0) with 1; split; [clear - Hjj Hjs1 Rjs HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-J2".
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht (conj Af (conj Ak (conj Au (conj Ap Ax)))) L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2)
| assert (Hpix1 : pixel_at trbsegs (mrestrict (w_H W3) mF) (img + fmt * ix) fmt pc0 true);
[ apply (g_pixel_at_kept (w_H W3) (ms_mem ms3) mF _ _ _ _ Hpix3 Hfmt); intros kk Hkk; destruct (Hpxoff kk Hkk) as [Hq1 Hq2]; exact (KP _ Hq1 Hq2) | ] ] end.
rga_hand RPB HS HJ2 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, pc0, js, (jj + 1).
split; [unfold g_trip; rga_cbn_cx_goal; m_inv_auto|].
split; [unfold g_pix; rga_cbn_cx_goal; split; [m_ewT | exact Hpix1]|].
split; [exact Hjs|]. split; [clear - Hjj Hjs1; lia|]. split; [rewrite Nat2Z.inj_succ in Hm; clear - Hm; lia|].
rewrite (cyc_succ (ht_T Ht) (hash0 (ht_T Ht) pc0) jj HTpos). fold hs. fold nx. split; [exact N520|]. split; [exact N521 | exact N522].
}
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (E539x : ew Ex 539 = Z_to_bv 64 uv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E539) end.
rewrite branch_eq_U, (U_atom _ 539 uv E539x ltac:(clear - Huv; lia)) in Hc. change (U _ (SLit 0)) with 0 in Hc. apply Z.eqb_eq in Hc. clear E539x.
destruct (find_off_spec Ht ent Hinv pc0 js Hjs) as (Rjs & Hstop & Hbefore).
assert (Ejj : jj = js).
{ destruct (Z_lt_le_dec jj js) as [Hlt|Hge]; [|clear - Hge Hjj; lia]. exfalso. specialize (Hbefore jj ltac:(clear - Hlt Hjj; lia)). fold hs in Hbefore.
unfold slot_stop in Hbefore. fold uv in Hbefore. rewrite Hc in Hbefore. cbn in Hbefore. discriminate Hbefore. }
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x8270c.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
ga_join HS ss_FD 600%nat rga_deads_FD ltac:(idtac).
idtac "OK-FREE1".
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht (conj Af (conj Ak (conj Au (conj Ap Ax)))) L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2)
| assert (Hpix1 : pixel_at trbsegs (mrestrict (w_H W3) mF) (img + fmt * ix) fmt pc0 true);
[ apply (g_pixel_at_kept (w_H W3) (ms_mem ms3) mF _ _ _ _ Hpix3 Hfmt); intros kk Hkk; destruct (Hpxoff kk Hkk) as [Hq1 Hq2]; exact (KP _ Hq1 Hq2) | ] ] end.
rga_hand RFD HS HJ3 k; [rga_E_tac HEE1 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, pc0, js.
split; [unfold g_trip; rga_cbn_cx_goal; m_inv_auto|].
split; [unfold g_pix; rga_cbn_cx_goal; split; [m_ewT | exact Hpix1]|].
split; [exact Hjs|]. rewrite <- Ejj. fold hs. split; m_ewT.
Qed.
End d.
End c.

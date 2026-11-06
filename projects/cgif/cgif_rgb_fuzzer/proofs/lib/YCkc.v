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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCkr YCks YCkt YCku YCkv YClv.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP6 : forall n : nat, rga_fromA B ss_TL (fun _ => INV_TL B (S n)) -> rga_fromA B ss_RL (fun _ => INV_RT B (S n)) -> rga_from B ss_RT (INV_RT B (S n)).
Proof.
intros n RTL RRL. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav)).
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_RT in HS.
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
pose proof (zsum_ge_length ent (ent_freq_pos Ht ent Hinv)) as Hlen_s.
pose proof Hinv as (_ & (_ & Helen & _) & _).
assert (Hcn_s : ht_cnt Ht <= 10000) by (clear - Hlen_s Helen Hsum Hix HN; unfold RGB_NMAX in HN; lia).
g_fact HS 716%nat (mkAF 0 10000 0)
ltac:(rewrite Rcnt, unsigned_lit_small by exact Hcnt64; change (2 ^ 0) with 1; split; [clear - Hcnt0 Hcn_s; lia|]; split; [apply Z.mod_1_r | clear; lia]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83054.
idtac "OK-R0".
all: try (ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-R1".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
2: {
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82a28.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-L0".
ga_join HS ss_RL 720%nat rga_deads_RL ltac:(idtac).
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2) | ] end.
rga_hand RRL HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent.
rga_cbn_cx_goal. m_inv_auto.
}
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83054.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-T0".
assert (Bha : 0 <= ha < 2 ^ 64) by (clear - Hha; lia).
rregU HS (12%bv : bv 5) ha ltac:(apply (U_atom _ 458 ha Rha Bha)) Q12.
assert (BF : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
rregU HS (21%bv : bv 5) (tb + 40) ltac:(apply (U_atom_off _ 305 tb 40 Rtb); clear - Htb4096 Htbceil Hrqtb C1; lia) Q21.
rregU HS (24%bv : bv 5) F ltac:(apply (U_atom _ 54 F RF BF)) Q24.
slot_val HS (Some 305%nat) 0 0 (Z_to_bv 64 fq) ltac:(exact (g_denot_off0 _ 473 fq Rfq Bfq)) QF.
slot_val HS (Some 305%nat) 0 8 (Z_to_bv 64 hh) ltac:(exact (g_denot_off0 _ 474 hh Rhh Bhh)) QH.
slot_val HS (Some 305%nat) 0 16 (Z_to_bv 64 uu) ltac:(exact (g_denot_off0 _ 475 uu Ruu Buu)) QU.
slot_val HS (Some 305%nat) 0 24 (Z_to_bv 64 pp) ltac:(exact (g_denot_off0 _ 476 pp Rpp Bpp)) QP.
slot_val HS (Some 305%nat) 0 32 (Z_to_bv 64 xx) ltac:(exact (g_denot_off0 _ 477 xx Rxx Bxx)) QX.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (ht_cnt Ht)) ltac:(exact (g_denot_off0 _ 716 _ Rcnt Hcnt64)) QC.
slot_val HS (Some 305%nat) 0 44 (Z_to_bv 64 (ht_T Ht)) ltac:(exact (g_denot_off0 _ 479 _ RT BT)) QT.
slot_val HS (Some 2%nat) (-576) (-392) (Z_to_bv 64 ix) ltac:(exact (g_denot_off0 _ 456 ix Rix Bix)) QI.
idtac "OK-T1".
ra_join_slots HS ss_TL 1000%nat rga_deads_TL
[(Some 305%nat, 0, 0); (Some 305%nat, 0, 8); (Some 305%nat, 0, 16); (Some 305%nat, 0, 24); (Some 305%nat, 0, 32); (Some 305%nat, 0, 40); (Some 305%nat, 0, 44); (Some 2%nat, (-576), (-392))]
ltac:(idtac; ga_join_val HS 1000%nat 14%nat Q12 N1014; ga_join_val HS 1000%nat 13%nat Q21 N1013; ga_join_val HS 1000%nat 17%nat Q24 N1017;
ga_join_val HS 1000%nat 23%nat QF N1023; ga_join_val HS 1000%nat 24%nat QH N1024; ga_join_val HS 1000%nat 25%nat QU N1025;
ga_join_val HS 1000%nat 26%nat QP N1026; ga_join_val HS 1000%nat 27%nat QX N1027; ga_join_val HS 1000%nat 28%nat QC N1028; ga_join_val HS 1000%nat 29%nat QT N1029;
ga_join_val HS 1000%nat 30%nat QI N1030;
ga_join_fact HS 1014%nat (mkAF 0 1 0) ltac:(rewrite N1014; rewrite unsigned_lit_small by exact Bha; change (2 ^ 0) with 1; split; [clear - Hha; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1030%nat (mkAF 0 10000 0) ltac:(rewrite N1030; rewrite unsigned_lit_small by exact Bix; change (2 ^ 0) with 1; split; [clear - Hix HN; unfold RGB_NMAX in HN; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1023%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1023; rewrite unsigned_lit_small by exact Bfq; change (2 ^ 4) with 16; split; [clear - Hfq4096 Hfqceil HT24 C1; lia|]; split; [exact Hfq16 | clear; lia]);
ga_join_fact HS 1024%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1024; rewrite unsigned_lit_small by exact Bhh; change (2 ^ 4) with 16; split; [clear - Hhh4096 Hhhceil HT24 C1; lia|]; split; [exact Hhh16 | clear; lia]);
ga_join_fact HS 1025%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1025; rewrite unsigned_lit_small by exact Buu; change (2 ^ 4) with 16; split; [clear - Huu4096 Huuceil HT24 C1; lia|]; split; [exact Huu16 | clear; lia]);
ga_join_fact HS 1026%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1026; rewrite unsigned_lit_small by exact Bpp; change (2 ^ 4) with 16; split; [clear - Hpp4096 Hppceil HT24 C1; lia|]; split; [exact Hpp16 | clear; lia]);
ga_join_fact HS 1027%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1027; rewrite unsigned_lit_small by exact Bxx; change (2 ^ 4) with 16; split; [clear - Hxx4096 Hxxceil HT24 C1; lia|]; split; [exact Hxx16 | clear; lia]);
ga_join_fact HS 1028%nat (mkAF 0 16777216 0) ltac:(rewrite N1028; rewrite unsigned_lit_small by exact Hcnt64; change (2 ^ 0) with 1; split; [clear - Hcnt0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1029%nat (mkAF 524309 16777216 0) ltac:(rewrite N1029; rewrite unsigned_lit_small by exact BT; change (2 ^ 0) with 1; split; [clear - HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-T2".
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2) | ] end.
rga_hand RTL HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent.
rga_cbn_cx_goal. m_inv_auto.
Qed.
End d.
End c.

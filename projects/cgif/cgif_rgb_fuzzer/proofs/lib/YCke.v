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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClc YCld YCkr YCks YCkt YCku YCkv YClv YClw.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP8 : forall n : nat, rga_fromA B ss_HL (fun _ => INV_HL B n) -> rga_fromA B ss_HD (fun _ => INV_HD B) -> rga_from B ss_TL (INV_TL B (S n)).
Proof.
intros n RHL RHD. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R1013 & R1017).
fold F in R1017.
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_TL in HS.
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
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x8257c.
idtac "OK-R0".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-R1".
assert (UN : forall Ex, ew Ex 40 = Z_to_bv 64 Hd -> ew Ex 39 = Z_to_bv 64 Wd ->
U Ex (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_MUL (SOff 40 0) (SOff 39 0)) (SLit 32)) (SLit 32)) = N).
{ intros Ex X40 X39. apply U_zext32_shifts; [rewrite HNhw; apply (U_HW _ 40 39 Hd Wd X40 X39 R44v R42v); rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia
| clear - HN1 HN; unfold RGB_NMAX in *; lia]. }
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
2: {
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rixx : ew Ex 1030 = Z_to_bv 64 ix) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rix);
assert (X40 : ew Ex 40 = Z_to_bv 64 Hd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E40);
assert (X39 : ew Ex 39 = Z_to_bv 64 Wd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E39) end.
rewrite branch_ne_U, (U_atom_off _ 1030 ix 1 Rixx) in Hc by (clear - Hix HN; unfold RGB_NMAX in HN; lia). rewrite (UN _ X40 X39) in Hc.
apply Bool.negb_false_iff, Z.eqb_eq in Hc. clear Rixx X40 X39.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x8322c.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-X0".
assert (Bha : 0 <= ha < 2 ^ 64) by (clear - Hha; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (E45z : ew Ex 45 = Z_to_bv 64 img) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E45);
assert (Rhaz : ew Ex 1014 = Z_to_bv 64 ha) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha);
assert (Rfqz : ew Ex 1023 = Z_to_bv 64 fq) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq);
assert (Rhhz : ew Ex 1024 = Z_to_bv 64 hh) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh);
assert (Ruuz : ew Ex 1025 = Z_to_bv 64 uu) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu);
assert (Rppz : ew Ex 1026 = Z_to_bv 64 pp) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp);
assert (Rxxz : ew Ex 1027 = Z_to_bv 64 xx) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx);
assert (Rcntz : ew Ex 1028 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt);
assert (RTz : ew Ex 1029 = Z_to_bv 64 (ht_T Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT) end.
g_slot_set HS (Some 2%nat) (-576) (-488) (SAlu ALU_SLTU (SLit 0) (SOff 45 0)) ltac:(apply U_inj; rewrite (g_U_sltu0 _ 45 img E45z ltac:(clear - Himg4096 Bimg; lia)); reflexivity).
rregU HS (12%bv : bv 5) ha ltac:(apply (U_atom _ 1014 ha Rhaz Bha)) Q12.
slot_val HS (Some 305%nat) 0 0 (Z_to_bv 64 fq) ltac:(exact (g_denot_off0 _ 1023 fq Rfqz Bfq)) QF.
slot_val HS (Some 305%nat) 0 8 (Z_to_bv 64 hh) ltac:(exact (g_denot_off0 _ 1024 hh Rhhz Bhh)) QH.
slot_val HS (Some 305%nat) 0 16 (Z_to_bv 64 uu) ltac:(exact (g_denot_off0 _ 1025 uu Ruuz Buu)) QU.
slot_val HS (Some 305%nat) 0 24 (Z_to_bv 64 pp) ltac:(exact (g_denot_off0 _ 1026 pp Rppz Bpp)) QP.
slot_val HS (Some 305%nat) 0 32 (Z_to_bv 64 xx) ltac:(exact (g_denot_off0 _ 1027 xx Rxxz Bxx)) QX.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (ht_cnt Ht)) ltac:(exact (g_denot_off0 _ 1028 _ Rcntz Hcnt64)) QC.
slot_val HS (Some 305%nat) 0 44 (Z_to_bv 64 (ht_T Ht)) ltac:(exact (g_denot_off0 _ 1029 _ RTz BT)) QT.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (X40 : ew Ex 40 = Z_to_bv 64 Hd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E40);
assert (X39 : ew Ex 39 = Z_to_bv 64 Wd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E39);
assert (X46 : ew Ex 46 = Z_to_bv 64 fmt) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E46) end.
g_cond HS BC_NE (SMdw M_MUL (SOff 40 0) (SOff 39 0)) (SLit 0)
ltac:(rewrite branch_ne_U, (U_HW _ 40 39 Hd Wd X40 X39 R44v R42v) by (rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia);
change (U _ (SLit 0)) with 0; apply Bool.negb_true_iff, Z.eqb_neq; rewrite <- HNhw; clear - HN1; lia).
g_cond HS BC_GEU (SLit 1) (SAluw ALU_ADD (SExt true 32 (SOff 46 0)) (SLit (-3)))
ltac:(rewrite branch_geu_U, YI0g.U_SAluw, (U_sext32_small _ 46 fmt X46) by (clear - Hfmt; lia); rewrite !U_SLit;
clear - Hfmt; destruct Hfmt as [-> | ->]; vm_compute; reflexivity).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (R1013z : ew Ex 1013 = Z_to_bv 64 (tb + 40)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R1013);
assert (R1017z : ew Ex 1017 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R1017);
assert (Rtbz : ew Ex 305 = Z_to_bv 64 tb) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb);
assert (RFz : ew Ex 54 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF) end.
g_pin HS (21%bv : bv 5) (SOff 305 40) ltac:(rewrite (g_denot_off _ 305 tb 40 Rtbz Htb_rng), (g_denot_off0 _ 1013 (tb + 40) R1013z ltac:(clear - Htb4096 Htbceil Hrqtb C1; lia)); reflexivity).
g_pin HS (24%bv : bv 5) (SOff 54 0) ltac:(rewrite (g_denot_off0 _ 54 F RFz ltac:(clear - HF4096 HFceil C1; lia)), (g_denot_off0 _ 1017 F R1017z ltac:(clear - HF4096 HFceil C1; lia)); reflexivity).
idtac "OK-X1".
g_join_slots_gap_win HS ss_HD 590%nat rga_deads_HD [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]
[(Some 305%nat, 0, 0); (Some 305%nat, 0, 8); (Some 305%nat, 0, 16); (Some 305%nat, 0, 24); (Some 305%nat, 0, 32); (Some 305%nat, 0, 40); (Some 305%nat, 0, 44)]
ltac:(idtac; ga_join_val HS 590%nat 14%nat Q12 N604;
ga_join_val HS 590%nat 25%nat QF N615; ga_join_val HS 590%nat 26%nat QH N616; ga_join_val HS 590%nat 27%nat QU N617;
ga_join_val HS 590%nat 28%nat QP N618; ga_join_val HS 590%nat 29%nat QX N619; ga_join_val HS 590%nat 30%nat QC N620; ga_join_val HS 590%nat 31%nat QT N621;
ga_join_fact HS 604%nat (mkAF 0 1 0) ltac:(rewrite N604; rewrite unsigned_lit_small by exact Bha; change (2 ^ 0) with 1; split; [clear - Hha; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 615%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N615; rewrite unsigned_lit_small by exact Bfq; change (2 ^ 4) with 16; split; [clear - Hfq4096 Hfqceil HT24 C1; lia|]; split; [exact Hfq16 | clear; lia]);
ga_join_fact HS 616%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N616; rewrite unsigned_lit_small by exact Bhh; change (2 ^ 4) with 16; split; [clear - Hhh4096 Hhhceil HT24 C1; lia|]; split; [exact Hhh16 | clear; lia]);
ga_join_fact HS 617%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N617; rewrite unsigned_lit_small by exact Buu; change (2 ^ 4) with 16; split; [clear - Huu4096 Huuceil HT24 C1; lia|]; split; [exact Huu16 | clear; lia]);
ga_join_fact HS 618%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N618; rewrite unsigned_lit_small by exact Bpp; change (2 ^ 4) with 16; split; [clear - Hpp4096 Hppceil HT24 C1; lia|]; split; [exact Hpp16 | clear; lia]);
ga_join_fact HS 619%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N619; rewrite unsigned_lit_small by exact Bxx; change (2 ^ 4) with 16; split; [clear - Hxx4096 Hxxceil HT24 C1; lia|]; split; [exact Hxx16 | clear; lia]);
ga_join_fact HS 620%nat (mkAF 0 4294967295 0) ltac:(rewrite N620; rewrite unsigned_lit_small by exact Hcnt64; change (2 ^ 0) with 1; split; [clear - Hcnt0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 621%nat (mkAF 0 4294967295 0) ltac:(rewrite N621; rewrite unsigned_lit_small by exact BT; change (2 ^ 0) with 1; split; [clear - HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-X2".
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2) | ] end.
pose proof (g_ts_rank_range (ht_T Ht)) as Hrk.
assert (Hk68 : k <= EV_HD) by (unfold EV_HD; clear - Hk0 Hrk; lia).
assert (HsumN : zsum (map snd ent) <= N) by (clear - Hsum Hc; lia).
rga_hand RHD HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, Ht, ent.
rga_cbn_cx_goal. m_inv_auto. }
idtac "OK-X3".
-
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rixx : ew Ex 1030 = Z_to_bv 64 ix) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rix);
assert (X40 : ew Ex 40 = Z_to_bv 64 Hd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E40);
assert (X39 : ew Ex 39 = Z_to_bv 64 Wd) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E39) end.
rewrite branch_ne_U, (U_atom_off _ 1030 ix 1 Rixx) in Hc by (clear - Hix HN; unfold RGB_NMAX in HN; lia). rewrite (UN _ X40 X39) in Hc.
apply Bool.negb_true_iff, Z.eqb_neq in Hc. clear Rixx X40 X39.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x8257c.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-B0".
assert (Bha : 0 <= ha < 2 ^ 64) by (clear - Hha; lia).
assert (Bix1 : 0 <= ix + 1 < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rixz : ew Ex 1030 = Z_to_bv 64 ix) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rix);
assert (Rhaz : ew Ex 1014 = Z_to_bv 64 ha) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha);
assert (Rfqz : ew Ex 1023 = Z_to_bv 64 fq) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq);
assert (Rhhz : ew Ex 1024 = Z_to_bv 64 hh) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh);
assert (Ruuz : ew Ex 1025 = Z_to_bv 64 uu) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu);
assert (Rppz : ew Ex 1026 = Z_to_bv 64 pp) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp);
assert (Rxxz : ew Ex 1027 = Z_to_bv 64 xx) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx);
assert (Rcntz : ew Ex 1028 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt);
assert (RTz : ew Ex 1029 = Z_to_bv 64 (ht_T Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT) end.
rregU HS (13%bv : bv 5) (ix + 1) ltac:(rewrite (U_atom_off _ 1030 ix 1 Rixz) by (clear - Bix1 Hix; lia); reflexivity) Q13.
rregU HS (15%bv : bv 5) ha ltac:(apply (U_atom _ 1014 ha Rhaz Bha)) Q15.
assert (BF : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (R1017z : ew Ex 1017 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R1017) end.
rregU HS (24%bv : bv 5) F ltac:(apply (U_atom _ 1017 F R1017z BF)) Q24.
slot_val HS (Some 305%nat) 0 0 (Z_to_bv 64 fq) ltac:(exact (g_denot_off0 _ 1023 fq Rfqz Bfq)) QF.
slot_val HS (Some 305%nat) 0 8 (Z_to_bv 64 hh) ltac:(exact (g_denot_off0 _ 1024 hh Rhhz Bhh)) QH.
slot_val HS (Some 305%nat) 0 16 (Z_to_bv 64 uu) ltac:(exact (g_denot_off0 _ 1025 uu Ruuz Buu)) QU.
slot_val HS (Some 305%nat) 0 24 (Z_to_bv 64 pp) ltac:(exact (g_denot_off0 _ 1026 pp Rppz Bpp)) QP.
slot_val HS (Some 305%nat) 0 32 (Z_to_bv 64 xx) ltac:(exact (g_denot_off0 _ 1027 xx Rxxz Bxx)) QX.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (ht_cnt Ht)) ltac:(exact (g_denot_off0 _ 1028 _ Rcntz Hcnt64)) QC.
slot_val HS (Some 305%nat) 0 44 (Z_to_bv 64 (ht_T Ht)) ltac:(exact (g_denot_off0 _ 1029 _ RTz BT)) QT.
idtac "OK-B1".
m_join_slots_win HS ss_HL 450%nat rga_deads_HL
[(Some 305%nat, 0, 0); (Some 305%nat, 0, 8); (Some 305%nat, 0, 16); (Some 305%nat, 0, 24); (Some 305%nat, 0, 32); (Some 305%nat, 0, 40); (Some 305%nat, 0, 44)]
ltac:(idtac; ga_join_val HS 450%nat 6%nat Q13 N456; ga_join_val HS 450%nat 8%nat Q15 N458; ga_join_val HS 450%nat 17%nat Q24 N467;
ga_join_val HS 450%nat 23%nat QF N473; ga_join_val HS 450%nat 24%nat QH N474; ga_join_val HS 450%nat 25%nat QU N475; ga_join_val HS 450%nat 26%nat QP N476; ga_join_val HS 450%nat 27%nat QX N477; ga_join_val HS 450%nat 28%nat QC N478; ga_join_val HS 450%nat 29%nat QT N479;
ga_join_fact HS 456%nat (mkAF 0 10000 0) ltac:(rewrite N456; rewrite unsigned_lit_small by (clear - Bix1; lia); change (2 ^ 0) with 1; split; [clear - Hix HN; unfold RGB_NMAX in HN; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 458%nat (mkAF 0 1 0) ltac:(rewrite N458; rewrite unsigned_lit_small by exact Bha; change (2 ^ 0) with 1; split; [clear - Hha; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 473%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N473; rewrite unsigned_lit_small by exact Bfq; change (2 ^ 4) with 16; split; [clear - Hfq4096 Hfqceil HT24 C1; lia|]; split; [exact Hfq16 | clear; lia]);
ga_join_fact HS 474%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N474; rewrite unsigned_lit_small by exact Bhh; change (2 ^ 4) with 16; split; [clear - Hhh4096 Hhhceil HT24 C1; lia|]; split; [exact Hhh16 | clear; lia]);
ga_join_fact HS 475%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N475; rewrite unsigned_lit_small by exact Buu; change (2 ^ 4) with 16; split; [clear - Huu4096 Huuceil HT24 C1; lia|]; split; [exact Huu16 | clear; lia]);
ga_join_fact HS 476%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N476; rewrite unsigned_lit_small by exact Bpp; change (2 ^ 4) with 16; split; [clear - Hpp4096 Hppceil HT24 C1; lia|]; split; [exact Hpp16 | clear; lia]);
ga_join_fact HS 477%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N477; rewrite unsigned_lit_small by exact Bxx; change (2 ^ 4) with 16; split; [clear - Hxx4096 Hxxceil HT24 C1; lia|]; split; [exact Hxx16 | clear; lia]);
ga_join_fact HS 478%nat (mkAF 0 16777216 0) ltac:(rewrite N478; rewrite unsigned_lit_small by exact Hcnt64; change (2 ^ 0) with 1; split; [clear - Hcnt0 HT24; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 479%nat (mkAF 524309 16777216 0) ltac:(rewrite N479; rewrite unsigned_lit_small by exact BT; change (2 ^ 0) with 1; split; [clear - HT24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-B3".
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fq hh uu pp xx Ht);
[ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) mF fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5);
intros b sz Hb i Hi; assert (Hsz : 0 <= sz) by (clear - Hi; lia); pose proof (req_size_pos sz Hsz) as [_ Hrqb];
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2); exact (KP (b + i) Hq1 Hq2) | ] end.
assert (Hix1 : 0 <= ix + 1 < N) by (clear - Hix Hc; lia).
assert (Hnix1 : N - (ix + 1) <= Z.of_nat n) by (rewrite Nat2Z.inj_succ in Hnix; clear - Hnix; lia).
assert (Hsum1 : zsum (map snd ent) <= ix + 1 + 0) by (clear - Hsum; lia).
rga_hand RHL HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, (ix + 1), Ht, ent.
rga_cbn_cx_goal. m_inv_auto.
Qed.
End d.
End c.

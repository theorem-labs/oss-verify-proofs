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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpp YClz YCqd YCqe YCqf YCea.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCoi YCog.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis FREECHT : tfree_cht_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_XC1 : rga_fromA B ss_XCa (fun _ => INV_XB B) -> rga_from B ss_XC (INV_XC B).
Proof.
intros RC.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & Tsz & Hk0 & Hfmt & HTsz & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
Rf & Rh & Ru & Rp & Rx).
destruct Hk0 as [Hk0 Hbud].
unfold ss_XC in HS.
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
assert (HEA : 0 <= EV_ADDFRAME) by (vm_compute; discriminate).
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Hfq_in3 : In (fq, 4 * Tsz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; right; cbn [cht_blocks]; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fq (4 * Tsz) HAR3 Hfq_in3) as (Hfq4096 & _ & Hfqceil & _).
pose proof (req_size_pos (4 * Tsz) ltac:(clear - HTsz; lia)) as Hrqfq.
assert (Hrfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil Hrqfq C1; lia).
assert (Hnzfq : fq <> 0) by (clear - Hfq4096; lia).
assert (Hhh_in3 : In (hh, 3 * Tsz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; right; cbn [cht_blocks]; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ hh (3 * Tsz) HAR3 Hhh_in3) as (Hhh4096 & _ & Hhhceil & _).
pose proof (req_size_pos (3 * Tsz) ltac:(clear - HTsz; lia)) as Hrqhh.
assert (Hrhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil Hrqhh C1; lia).
assert (Hnzhh : hh <> 0) by (clear - Hhh4096; lia).
assert (Huu_in3 : In (uu, Tsz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; right; cbn [cht_blocks]; right; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ uu (Tsz) HAR3 Huu_in3) as (Huu4096 & _ & Huuceil & _).
pose proof (req_size_pos (Tsz) ltac:(clear - HTsz; lia)) as Hrquu.
assert (Hruu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil Hrquu C1; lia).
assert (Hnzuu : uu <> 0) by (clear - Huu4096; lia).
assert (Hpp_in3 : In (pp, 3 * Tsz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; right; cbn [cht_blocks]; right; right; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * Tsz) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
pose proof (req_size_pos (3 * Tsz) ltac:(clear - HTsz; lia)) as Hrqpp.
assert (Hrpp : 0 <= pp < 2 ^ 64) by (clear - Hpp4096 Hppceil Hrqpp C1; lia).
assert (Hnzpp : pp <> 0) by (clear - Hpp4096; lia).
assert (Hxx_in3 : In (xx, 4 * Tsz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; right; cbn [cht_blocks]; right; right; right; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ xx (4 * Tsz) HAR3 Hxx_in3) as (Hxx4096 & _ & Hxxceil & _).
pose proof (req_size_pos (4 * Tsz) ltac:(clear - HTsz; lia)) as Hrqxx.
assert (Hrxx : 0 <= xx < 2 ^ 64) by (clear - Hxx4096 Hxxceil Hrqxx C1; lia).
assert (Hnzxx : xx <> 0) by (clear - Hxx4096; lia).
set (fpl := (tb, 48) :: optb fq (4 * Tsz) ++ optb hh (3 * Tsz) ++ optb uu Tsz ++ optb pp (3 * Tsz) ++ optb xx (4 * Tsz)).
assert (Efpl : fpl = (tb, 48) :: cht_blocks fq hh uu pp xx Tsz)
by (subst fpl; rewrite (optb_nz fq _ Hnzfq), (optb_nz hh _ Hnzhh), (optb_nz uu _ Hnzuu), (optb_nz pp _ Hnzpp), (optb_nz xx _ Hnzxx); reflexivity).
assert (HPm3' : Permutation (ablocks B ly3 S3) (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ fpl)) by (rewrite Efpl; exact HPm3).
assert (HFPlive : forall b n, In (b, n) fpl -> In (b, n) ([(blk, fmt * N); (fim, N)] ++ fpl) /\ In (b, n) (ablocks B ly3 S3)).
{ intros b n Hbn. assert (Hn2 : In (b, n) ([(blk, fmt * N); (fim, N)] ++ fpl)) by (apply in_or_app; right; exact Hbn).
split; [exact Hn2 | eapply Permutation_in; [apply Permutation_sym; exact HPm3' | apply in_or_app; right; exact Hn2]]. }
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_free_col_hash_table.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ3 AG EE.
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
assert (HB305 : bv_unsigned (ew Ex 305) = tb) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite Rtb; apply unsigned_lit_small; exact Htb_rng);
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 305%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 305 tb cs lo hi wlo whi 0 8%N (SOff 615 0) fq HRc HB305 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rf) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hrfq) ltac:(cbn; lia)) as Vfq;
pose proof (field_of_region Ex _ 305 tb cs lo hi wlo whi 8 8%N (SOff 616 0) hh HRc HB305 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rh) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hrhh) ltac:(cbn; lia)) as Vhh;
pose proof (field_of_region Ex _ 305 tb cs lo hi wlo whi 16 8%N (SOff 617 0) uu HRc HB305 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ru) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hruu) ltac:(cbn; lia)) as Vuu;
pose proof (field_of_region Ex _ 305 tb cs lo hi wlo whi 24 8%N (SOff 618 0) pp HRc HB305 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rp) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hrpp) ltac:(cbn; lia)) as Vpp;
pose proof (field_of_region Ex _ 305 tb cs lo hi wlo whi 32 8%N (SOff 619 0) xx HRc HB305 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rx) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hrxx) ltac:(cbn; lia)) as Vxx;
idtac end end.
rewrite Z.add_0_r in Vfq. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vfq, Vhh, Vuu, Vpp, Vxx. clear HRc.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS Hsegs W3 Ex ssX msX TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k
TFREECHT_STK (ablocks_fp fpl) EV_FREECHT
(-576) (ew Ex 2) (Z_to_bv 64 0x8490c) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) (ablocks B ly S ++ [(blk, fmt * N); (fim, N)])) HS eq_refl HJ3);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| ga_evalE AG
| reflexivity
| clear; lia
| unfold TFREECHT_STK, ASTACK; clear; lia
| rewrite FFS; unfold TFREECHT_STK, ASTACK; clear; lia
| rewrite Rgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| rewrite unsigned_lit_small by (clear; lia); clear; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -576) with (spZ regs - 576) by (clear; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (FREECHT ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) tb fq hh uu pp xx (4 * Tsz) (3 * Tsz) Tsz (3 * Tsz) (4 * Tsz)
(ablocks B ly S ++ [(blk, fmt * N); (fim, N)]) HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc];
let v := eval vm_compute in A_free_col_hash_table in change (w64 A_free_col_hash_table) with (Z_to_bv 64 v) in CALL;
apply CALL; clear CALL;
[ unfold raZ at 1; rewrite Rra, unsigned_lit_small by (clear; lia); cbn [spine map fst snd]; fold (spine ch); rewrite <- ?Hra88; destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; rewrite <- ?Hra88; tauto
| rewrite Ra0; cbn [sv_denot]; ga_evalE0 AG; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | exact Rtb | rewrite Rtb; reflexivity]
| exact Vfq | exact Vhh | exact Vuu | exact Vpp | exact Vxx
| exact Hrfq | exact Hrhh | exact Hruu | exact Hrpp | exact Hrxx
| change CHT_SIZE with 48; eapply Permutation_trans; [exact HPm3'|]; subst fpl; rewrite app_assoc; eapply Permutation_trans; [apply Permutation_app_comm|]; cbn [app]; rewrite <- !app_assoc; apply Permutation_refl
| unfold EV_FREECHT in *; rga_room Hev Hbud; (clear - Hk0 HEVv HEA; rga_lia) ]
| cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJc & HPc & HK7);
exists ly7, S7, regs7, mem7, md7; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc | exact HK7] ]
| intros a Ha; right; destruct (inFP_ablocks_fp_inv _ _ Ha) as (b & n & Hbn & Hrg); exists b, n;
destruct (HFPlive b n Hbn) as (Hn2 & Hlv); split; [exact Hlv|]; split; [|exact Hrg];
intros Hin0; pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (b, n) (b, n) HAR3 HPm3' Hin0 Hn2) as Hdj;
unfold zdisjoint, block_rng in Hdj; cbn [fst snd] in Hdj; clear - Hdj Hrg; lia ]
| ] end end.
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc & HP7 & HK7).
pose proof HJc as (_ & _ & _ & _ & _ & _ & (_ & Hd7) & _).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0 Vfq Vhh Vuu Vpp Vxx.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs7 & _). cbn [app] in Hfrs7.
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (eapply Permutation_in; [apply Permutation_sym; exact HK7 | apply in_or_app; left; exact Hrin]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HnoF : forall a, F <= a < F + 8192 -> ~ inFP (ablocks_fp fpl) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (_ & Hlv).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ b n 7 fpos HAR3 Hlv Hfin3) as Dd.
rewrite EFA3 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hrg. lia. }
assert (HnoS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ inFP (ablocks_fp fpl) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (_ & Hlv).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b n HAR3 Hlv) as (_ & (_ & Hbz) & _). clear - Ha Hrg Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
assert (HnoR : forall a, r <= a < r + 64 -> ~ inFP (ablocks_fp fpl) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (Hn2 & _).
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (b, n) HAR3 HPm3' Hrin Hn2) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. change (req_size 64) with 64 in Dd. clear - Dd Ha Hrg. lia. }
assert (HnoC : forall a, cfp <= a < cfp + 24 -> ~ inFP (ablocks_fp fpl) a).
{ intros a Ha Hn. destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg). destruct (HFPlive b n Hbn) as (_ & Hlv).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ b n cid pos HAR3 Hlv HfinS3) as Dd.
rewrite EFA3 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hrg Hflo Hfhi. lia. }
reseat HS HJ7 HP7 [1; 2; 3; 4; 5; 6]%nat AG
ltac:(idtac; first
[ m_keptJ HJc HJ7 AG Usp FFS RF E67 E10n E11n Hfin3 HfinS3 Hrin3 Hrin7 EFA3 F HFpres7 HnoF HnoS HnoR HnoC LAWS ltac:(fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x843fc.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_XCa 1100%nat rga_deads_XCa ltac:(idtac).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RC HS HJ7 (k + EV_FREECHT); [rga_E_tac HEE7 | ].
exists blk, fim. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HK7|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]
| split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]].
Qed.
End e.
End d.

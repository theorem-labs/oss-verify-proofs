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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC59 YC5a YC5b YP16 YI0f YI09 YC68.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC4b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCap YCad YC90 YC9d YC9r YCam YCaf YCag YCah YCan YCai YCaj YCak.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC67 YC5z YC62 YC66 YC65 YCae YCal YC5u YCab.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_q7 : rga_fromA B ss_QE (fun _ => INV_QE B) -> rga_from B ss_Q5N (INV_Q4 B).
Proof.
intros RC. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & Tt & cnt & flt & tr & Hk0 & Hnodes & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rflt & Tflt & Aflt) & Rcnt & RT & Rha & Hha &
(av & Rav & Hav) & HTch & Hcnt & Rroot & Htree & Hfull & Hth & Hwft).
destruct Hk0 as [Hk0 Hbud].
unfold ss_Q5N in HS.
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
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as (_ & _ & _ & _ & _ & _ & _ & [_ R42v] & [_ R44v] & _).
cbn [fst snd N.to_nat Z.of_N] in R42v, R44v.
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
assert (HN31 : 0 <= Hd * Wd < 2 ^ 31) by (rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia).
assert (HWd1 : 1 <= Wd /\ 1 <= Hd) by (rewrite <- HcW, <- HcH; clear - HW1 HH1; lia).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x840e4.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
set (Mq := fmt * N).
assert (HMq : 3 <= Mq <= 40000) by (subst Mq; clear - HfN; unfold RGB_NMAX in HfN; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tt ++ tree_blocks tr ++ [(flt, 4 * (fmt * N))])))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; YI0g.perm_tac).
assert (HoffT : forall b sz, In (b, sz) (tree_blocks tr) -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha.
pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 ltac:(apply in_or_app; right; cbn [cht_blocks app]; do 7 right; apply in_or_app; left; exact Hb) Hfin3 a Ha) as Hq.
rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree0 : tree_at trasegs (mrestrict (w_H W3) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) (ms_mem ms3) _ tr Htree). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN0; assumption. }
assert (Hflt_in3 : In (flt, 4 * Mq) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app; right. cbn [cht_blocks app]. do 8 right. apply in_or_app. right. left. reflexivity. }
assert (Hfim_in3 : In (fim, N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; right; left; reflexivity]).
assert (Htr_in3 : forall b, In b (tree_blocks tr) -> In b (ablocks B ly3 S3)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app; right. cbn [cht_blocks app]. do 8 right. apply in_or_app. left. exact Hb. }
pose proof Hrgb as Hrgb''. cbn [obj_at LAY_Rgb] in Hrgb''.
destruct Hrgb'' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [_ R48v] & [_ R56v] & _).
cbn [fst snd N.to_nat Z.of_N] in R48v, R56v. change (2 ^ (8 * 8)) with (2 ^ 64) in R48v. change (2 ^ (8 * 4)) with (2 ^ 32) in R56v.
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Hsprng : alloc_ceiling + 25088 <= spZ regs /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 FFS; lia).
assert (E2n : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (AG 2%nat) by lia; rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ flt (4 * Mq) HAR3 Hflt_in3) as (Hflt4096 & Hfltzone & Hfltceil & Hflt16).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fim N HAR3 Hfim_in3) as (Hfim4096 & Hfimzone & Hfimceil & Hfim16).
pose proof (req_size_pos (4 * Mq) ltac:(clear - HMq; lia)) as Hrqflt. pose proof (req_size_pos N ltac:(clear - HN1; lia)) as Hrqfim.
assert (Hroot_rng : 4096 <= troot tr /\ troot tr + 56 <= alloc_ceiling).
{ destruct tr as [|nd|nd tl tr']; [exfalso; exact Hfull | |];
(assert (Hb : In (tn_addr nd, NODE_SIZE) (ablocks B ly3 S3)) by (apply Htr_in3; cbn [tree_blocks]; left; reflexivity);
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ _ _ HAR3 Hb) as (Hb4096 & _ & Hbceil & _); change (req_size NODE_SIZE) with 56 in Hbceil; cbn [troot]; clear - Hb4096 Hbceil; lia). }
assert (Hha_rng : 0 <= ha < 2 ^ 64) by (clear - Hha; lia).
rregU HS (10%bv : bv 5) ha ltac:(apply (U_atom _ 604 ha Rha); exact Hha_rng) G10.
rregU HS (29%bv : bv 5) fmt ltac:(apply (U_sext32_small E 46 fmt E46); clear - Hfmt; lia) G29.
rregU HS (13%bv : bv 5) N ltac:(rewrite HNhw; apply (U_HW E 40 39 Hd Wd E40 E39); [clear - R44v; cbn in R44v; lia | clear - R42v; cbn in R42v; lia | exact HN31]) G13.
rregU HS (25%bv : bv 5) SB ltac:(apply (U_atom _ 44 SB E44); unfold SB; clear; lia) G25.
rregU HS (9%bv : bv 5) (spZ regs - 512) ltac:(rewrite (U_atom_off E 2 (spZ regs) (-512) E2n) by (clear - Hsprng C1; lia); clear; lia) G9.
rregU HS (31%bv : bv 5) flt ltac:(apply (U_atom _ 872 flt Rflt); clear - Hflt4096 Hfltceil Hrqflt C1; lia) G31.
pose proof (fun off e v => hlg_slot_of_state E _ _ (w_H W3) 7%nat _ _ _ _ _ (spZ regs) off e v HS eq_refl) as SL0.
lazymatch type of SL0 with forall off e v, In _ ?cs -> _ =>
assert (SL : forall off e v, In (YQ0b.mkChunk (off - 512) (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) (spZ regs - 512 + off) 8 v)
by (intros off e v Hin He Hv; exact (SL0 off e v Hin U2 He Hv)) end.
clear SL0.
set (bfmtv := bv_unsigned (sv_denot E (SExt true 32 (SOff 42 0)))).
assert (Hbfmtv : bef <> 0 -> bfmtv = beffmt).
{ intros Hb0. subst bfmtv. rewrite (hlg_denot_sext32 E 42 beffmt E42 ltac:(clear - Hbef Hb0; lia)). apply unsigned_lit_small. clear - Hbef Hb0. lia. }
pose proof (SL 176 (SOff 41 0) bef ltac:(cbn; repeat first [left; reflexivity | right]) (hlg_denot_off0 E 41 bef E41 R48v) R48v) as V176.
pose proof (SL 240 (SOff 765 0) (troot tr) ltac:(cbn; repeat first [left; reflexivity | right]) (hlg_denot_off0 E 765 (troot tr) Rroot ltac:(clear - Hroot_rng C1; lia)) ltac:(clear - Hroot_rng C1; lia)) as V240.
pose proof (SL 256 (SExt true 32 (SOff 42 0)) bfmtv ltac:(cbn; repeat first [left; reflexivity | right]) ltac:(subst bfmtv; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(subst bfmtv; pose proof (bv_unsigned_in_range 64 (sv_denot E (SExt true 32 (SOff 42 0)))) as Hq; unfold bv_modulus in Hq; exact Hq)) as V256.
pose proof (SL 376 (SOff 184 0) fim ltac:(cbn; repeat first [left; reflexivity | right]) (hlg_denot_off0 E 184 fim Rfim ltac:(clear - Hfim4096 Hfimceil Hrqfim C1; lia)) ltac:(clear - Hfim4096 Hfimceil Hrqfim C1; lia)) as V376.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 540900) with (Z_to_bv 64 QNS_HEAD).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (q_nd_setup B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 (spZ regs - 512)
ltac:(rewrite FFS; clear; lia) ltac:(clear; lia) fx (ms_regs msX) (ms_mem msX) mdX N (troot tr)) end.
- split; [exact HJ3|]. split; [exact Hfrm|]. split; [exact G25 | exact G9].
- exact G13.
- clear - Hroot_rng. lia. - clear - Hroot_rng C1. lia. - clear - HN1 HN; unfold RGB_NMAX in HN; lia.
- exact V240. }
cbv beta. intros W5 c5 _ (-> & fx5 & regs5 & mem5 & md5 & -> & (HJ5 & Hfrm5 & G25s & G9s) & (G14s & G15s & G11s & G17s & G16s) & HK5 & HM5 & HP5).
assert (VK : forall a (n : nat) v, spZ regs - 512 <= a -> a + Z.of_nat n <= spZ regs -> val_mem trasegs (mrestrict (w_H W3) (ms_mem ms)) a n v -> val_mem trasegs (mrestrict (w_H W3) mem5) a n v).
{ intros a n v Ha1 Ha2 V. apply (YC04.val_mem_kept trasegs (w_H W3) (w_H W3) (ms_mem ms) mem5 a n v); [|exact V].
intros kk Hkk. apply HM5. clear - Ha1 Ha2 Hkk Hsprng C1. lia. }
assert (Htree5 : tree_at trasegs (mrestrict (w_H W3) mem5) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W3) (ms_mem ms) _ tr Htree0). intros b sz Hb i Hi.
destruct (HoffT b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & _). apply HM5. exact Hq1. }
assert (HfN29 : 3 <= fmt < 2 ^ 29 /\ 0 < N <= 2 ^ 29 /\ fmt * N <= 2 ^ 29) by (clear - Hfmt HN1 HN HMq; subst Mq; unfold RGB_NMAX in HN; lia).
assert (HPflt : Permutation (ablocks B ly3 S3) ((flt, 4 * Mq) :: (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ tree_blocks tr)))
by (eapply Permutation_trans; [exact HPm3|]; unfold Mq; YI0g.perm_tac).
change (Z_to_bv 64 QNS_EXIT) with (Z_to_bv 64 LNP_HEAD).
eapply SRr_bind.
{ eapply (rga_lnd_loop B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] k ly3 S3 W3 flt (4 * Mq) (spZ regs - 512) ha fmt N bef bfmtv
bef (beffmt * N) fim fim N tr 0 fx5 regs5 mem5 md5 HJ5 Hfrm5 Hflt_in3).
- rewrite FFS. clear. lia.
- clear. lia.
- exact Hha_rng.
- clear - HfN29. lia.
- exact (proj1 (proj2 HfN29)). - exact (proj2 (proj2 HfN29)).
- exact R48v.
- intros Hh. split; [subst Mq; clear; lia | clear - Hha Hh; lia].
- subst Mq. clear - Hfmt. destruct Hfmt as [-> | ->]; lia.
- intros Hh0 Hb0. rewrite (Hbfmtv Hb0).
assert (Hbf34 : beffmt = 3 \/ beffmt = 4) by (clear - Hbef Hb0; tauto).
assert (Hbin : In (bef, beffmt * N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. unfold trgb_own. cbn [app]. right. apply in_or_app. left. apply in_or_app. right.
unfold optb. destruct (Z.eqb_spec bef 0) as [Hq|Hq]; [contradiction | left; reflexivity]. }
split; [clear - Hbf34; lia|]. split; [clear - Hbf34 HN1 HN; unfold RGB_NMAX in HN; lia|].
split; [eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hbin]|].
split; [clear; lia|]. split; [clear - Hbf34 HN1; lia|].
intros Heq. injection Heq as Hq1 Hq2.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (bef, beffmt * N) HAR3 HPflt ltac:(apply in_or_app; left; exact Hbin)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd.
pose proof (req_size_pos (beffmt * N) ltac:(clear - Hbf34 HN1; lia)) as Hrqb. clear - Dd Hq1 Hrqb Hrqflt. lia.
- exact Hfim_in3.
- clear. lia. - clear. lia.
- exact Afim.
- exact Hfull. - exact Hwft. - exact Htr_in3.
- intros b Hb Heq. subst b. apply tree_blocks_in_nodes in Hb. destruct Hb as (nd & _ & Hq). injection Hq as _ Hq. unfold NODE_SIZE in Hq. subst Mq. clear - Hq Hfmt. destruct Hfmt as [-> | ->]; lia.
- intros b Hb Heq. subst b.
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt)) (tree_blocks tr ++ [(flt, 4 * (fmt * N))]) (fim, N) (fim, N) HAR3
ltac:(eapply Permutation_trans; [exact HPm3|]; YI0g.perm_tac)
ltac:(apply in_or_app; right; right; left; reflexivity) ltac:(apply in_or_app; left; exact Hb)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. clear - Dd Hrqfim. lia.
- exact Htree5.
- apply VK; [clear; lia | cbn; clear; lia | exact V176].
- apply VK; [clear; lia | cbn; clear; lia | exact V240].
- apply VK; [clear; lia | cbn; clear; lia | exact V256].
- apply VK; [clear; lia | cbn; clear; lia | exact V376].
- clear - HN1. lia.
- exact G14s. - exact G15s.
- rewrite (HK5 (10%bv : bv 5) ltac:(cbv; tauto)). exact G10.
- rewrite (HK5 (29%bv : bv 5) ltac:(cbv; tauto)). exact G29.
- exact G11s. - exact G17s. - exact G16s.
- rewrite (HK5 (31%bv : bv 5) ltac:(cbv; tauto)). exact G31.
- exact G25s. - exact G9s. }
cbv beta. intros W7 c7 _ (-> & fx7 & regs7 & mem7 & md7 & -> & Hfrm7 & HJ7 & HK7 & _ & _ & Htree7 & Hfr7 & Hpres7).
assert (Hsame : forall r0 : bv 5, reg_in r0 [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv = false -> getr regs7 r0 = getr (ms_regs ms) r0).
{ intros r0 Hr0. pose proof (all_regs_in r0) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [ rewrite !getr_zero; reflexivity | vm_compute in Hr0; discriminate
| lazymatch goal with |- getr regs7 ?rr = _ => rewrite (HK7 rr ltac:(vm_compute; reflexivity)); apply (HK5 rr); cbv; tauto end ] |]). destruct Hin. }
pose proof (proj1 HJ7) as HAR7.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 Hrin3) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 Htb_in3) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
set (rq := req_size (4 * Mq)) in *. set (rqi := req_size N) in *.
assert (SEPF : forall b sz, In (b, sz) (ablocks B ly3 S3) -> (b, sz) <> (flt, 4 * Mq) -> b + req_size sz <= flt \/ flt + rq <= b).
{ intros b sz Hb Hne. pose proof (sep_blocks trasegs B LAWS ly3 S3 _ _ _ b sz flt (4 * Mq) HAR3 Hb Hflt_in3 Hne) as Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. exact Dd. }
assert (SEPI : forall b sz, In (b, sz) (ablocks B ly3 S3) -> (b, sz) <> (fim, N) -> b + req_size sz <= fim \/ fim + rqi <= b).
{ intros b sz Hb Hne. pose proof (sep_blocks trasegs B LAWS ly3 S3 _ _ _ b sz fim N HAR3 Hb Hfim_in3 Hne) as Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. exact Dd. }
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ flt (4 * Mq) 7 fpos HAR3 Hflt_in3 Hfin3) as HdF_flt.
unfold zdisjoint in HdF_flt. cbn [fst snd] in HdF_flt. change (fs_frame_bytes 7) with 8192 in HdF_flt. rewrite EFA3 in HdF_flt. fold F rq in HdF_flt.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ flt (4 * Mq) cid pos HAR3 Hflt_in3 HfinS3) as HdC_flt.
unfold zdisjoint in HdC_flt. cbn [fst snd] in HdC_flt. rewrite EFA3 in HdC_flt. fold rq in HdC_flt.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ fim N 7 fpos HAR3 Hfim_in3 Hfin3) as HdF_fim.
unfold zdisjoint in HdF_fim. cbn [fst snd] in HdF_fim. change (fs_frame_bytes 7) with 8192 in HdF_fim. rewrite EFA3 in HdF_fim. fold F rqi in HdF_fim.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ fim N cid pos HAR3 Hfim_in3 HfinS3) as HdC_fim.
unfold zdisjoint in HdC_fim. cbn [fst snd] in HdC_fim. rewrite EFA3 in HdC_fim. fold rqi in HdC_fim.
assert (HPfim : Permutation (ablocks B ly3 S3) ((fim, N) :: (ablocks B ly S ++ [(blk, fmt * N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ tree_blocks tr ++ [(flt, 4 * (fmt * N))])))
by (eapply Permutation_trans; [exact HPm3|]; YI0g.perm_tac).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (r, 64) HAR3 HPflt ltac:(apply in_or_app; left; exact Hrin)) as HdR_flt.
unfold zdisjoint, block_rng in HdR_flt. cbn [fst snd] in HdR_flt. change (req_size 64) with 64 in HdR_flt. fold rq in HdR_flt.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (flt, 4 * Mq) _ (tb, 48) HAR3 HPflt ltac:(apply in_or_app; right; right; right; left; reflexivity)) as HdT_flt.
unfold zdisjoint, block_rng in HdT_flt. cbn [fst snd] in HdT_flt. change (req_size 48) with 48 in HdT_flt. fold rq in HdT_flt.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (fim, N) _ (r, 64) HAR3 HPfim ltac:(apply in_or_app; left; exact Hrin)) as HdR_fim.
unfold zdisjoint, block_rng in HdR_fim. cbn [fst snd] in HdR_fim. change (req_size 64) with 64 in HdR_fim. fold rqi in HdR_fim.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (fim, N) _ (tb, 48) HAR3 HPfim ltac:(apply in_or_app; right; right; left; reflexivity)) as HdT_fim.
unfold zdisjoint, block_rng in HdT_fim. cbn [fst snd] in HdT_fim. change (req_size 48) with 48 in HdT_fim. fold rqi in HdT_fim.
assert (HRNG7 : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (flt + rq <= F \/ F + 8192 <= flt) /\ (fim + rqi <= F \/ F + 8192 <= fim)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (flt + rq <= r \/ r + 64 <= flt) /\ (fim + rqi <= r \/ r + 64 <= fim)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (flt + rq <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= flt) /\
(fim + rqi <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= fim) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid) /\
(4096 <= tb /\ tb + 48 <= alloc_ceiling /\ (flt + rq <= tb \/ tb + 48 <= flt) /\ (fim + rqi <= tb \/ tb + 48 <= fim)) /\
(4096 <= flt /\ flt + rq <= alloc_ceiling /\ 4 * Mq <= rq /\ (flt + rq <= 2147446784 \/ 17594333495296 <= flt)) /\
(4096 <= fim /\ fim + rqi <= alloc_ceiling /\ N <= rqi /\ (fim + rqi <= 2147446784 \/ 17594333495296 <= fim)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25088 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25088 /\ SB = 2147450880).
{ split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HdF_flt HdF_fim; lia|]. split; [clear - Hr4096 Hrceil HdR_flt HdR_fim; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi HdC_flt HdC_fim; lia|]. split; [clear - Htb4096 Htbceil Hrqtb HdT_flt HdT_fim; lia|].
split; [destruct Hfltzone as [_ Hz2]; clear - Hflt4096 Hfltceil Hrqflt Hz2; lia|].
split; [destruct Hfimzone as [_ Hz2]; clear - Hfim4096 Hfimceil Hrqfim Hz2; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
assert (Hfr75 : forall a, 0 <= a < 2 ^ 64 -> ~ fim <= a < fim + N -> aview trasegs (w_H W3) mem7 a = aview trasegs (w_H W3) (ms_mem ms) a).
{ intros a Ha1 Ha3. rewrite (Hfr7 a Ha1 ltac:(clear - Ha3; lia)). exact (HM5 a Ha1). }
m_reseatF HS HJ7 fx7 regs7 ([5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv : list (bv 5)) 541700 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG Hsame
ltac:(idtac; first
[ q_keptP Hfr75 HRNG7 HJ7 AG Usp RF E67 E10n E11n Rtb F HFpres7 Hrpres7 Htbpres7
ltac:(idtac; m_keptE_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
assert (Hflt_rng : 0 <= flt < 2 ^ 64) by (destruct HRNG7 as (_ & _ & _ & _ & (Hq1 & Hq2 & Hq3 & _) & _); clear - Hq1 Hq2 Hq3 C1 Hrqflt; lia).
rregU HS (31%bv : bv 5) flt ltac:(apply (U_atom _ 872 flt Rflt); exact Hflt_rng) G31x.
slot_val HS (Some 2%nat) (-512) (-272) (Z_to_bv 64 (troot tr)) ltac:(exact (hlg_denot_off0 _ 765 (troot tr) Rroot ltac:(clear - Hroot_rng C1; lia))) QSroot.
ra_join_slots HS ss_QE2 2000%nat rga_deads_QE2 [(Some 2%nat, (-512), (-344)); (Some 2%nat, (-512), (-272))]
ltac:(idtac; ga_join_val HS 2000%nat 19%nat G31x E2019; ga_join_val HS 2000%nat 21%nat QSroot E2021;
ga_join_fact HS 2019%nat (mkAF 4096 140737479966720 4)
ltac:(rewrite E2019; rewrite unsigned_lit_small by exact Hflt_rng; change (2 ^ 4) with 16; split; [clear - Hflt4096 Hfltceil Hrqflt C1; lia|]; split; [exact Hflt16 | clear; lia])).
unfold ss_QE2 in HS.
rregU HS (31%bv : bv 5) flt ltac:(apply (U_atom _ 2019 flt E2019); exact Hflt_rng) G31y.
slot_val HS (Some 2%nat) (-512) (-272) (Z_to_bv 64 (troot tr)) ltac:(exact (hlg_denot_off0 _ 2021 (troot tr) E2021 ltac:(clear - Hroot_rng C1; lia))) QSroot2.
m_join_slots_win HS ss_QE 900%nat rga_deads_QE [(Some 2%nat, (-512), (-344)); (Some 2%nat, (-512), (-272))]
ltac:(idtac; ga_join_val HS 900%nat 19%nat G31y N919; ga_join_val HS 900%nat 21%nat QSroot2 N921;
ga_join_fact HS 919%nat (mkAF 4096 140737479966720 4)
ltac:(rewrite N919; rewrite unsigned_lit_small by exact Hflt_rng; change (2 ^ 4) with 16; split; [clear - Hflt4096 Hfltceil Hrqflt C1; lia|]; split; [exact Hflt16 | clear; lia])).
rga_hand RC HS HJ7 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, flt, (4 * (fmt * N)), Tt, tr.
split; [split; [clear - Hk0 Hnodes HEVv; rewrite HEVv; (let v := eval vm_compute in EV_ADDFRAME in change EV_ADDFRAME with v); unfold EV_HD, EV_FREECHT in *; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia|].
split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx|].
split; [split; [exact N919 | split; [exact Tflt | exact Aflt]]|].
split; [clear - HMq; subst Mq; lia|].
split; [exact N921|].
split; [exact Htree7 | exact Hth].
Qed.
End d.
End c.

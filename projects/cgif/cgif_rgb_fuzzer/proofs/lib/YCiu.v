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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCq8 YCqb YClx YCm2 YCqc YCjo YCpm YCly YCpn.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_B2b : rga_fromFA B ss_EPI (fun _ => INV_X B) -> rga_fromA B ss_AF (fun _ => INV_AF B) -> rga_from B ss_M2 (INV_M2 B).
Proof.
intros RX RC. rga_prelude. unfold ss_M2 in HS.
destruct HINV as (blk & Hk0 & Hfmt & Eab3 & Rblk & Tblk & Ablk).
destruct Hk0 as [Hk0 Hbud].
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hrin).
assert (Hblk_in : In (blk, fmt * N) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (E39n : ew E 39 = Z_to_bv 64 Wd) by exact E39. assert (E40n : ew E 40 = Z_to_bv 64 Hd) by exact E40.
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as Hrq.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ blk (fmt * N) HAR3 Hblk_in) as (Hb4096 & Hbzone & Hbceil & Hb16).
assert (Hne_br : (blk, fmt * N) <> (r, 64)).
{ intros Heq. injection Heq as Hb1 Hb2. pose proof Hrin as Hrin'. apply in_split in Hrin' as (l1 & l2 & El). rewrite El, <- app_assoc in Eab3. cbn [app] in Eab3.
pose proof (sep_blocks_pos trbsegs B LAWS ly3 S3 _ _ _ (r, 64) (blk, fmt * N) l1 l2 [] HAR3 Eab3) as Hsp.
unfold zdisjoint, block_rng in Hsp. cbn [fst snd] in Hsp. change (req_size 64) with 64 in Hsp. rewrite Hb1 in Hsp. clear - Hsp Hrq. lia. }
pose proof (sep_blocks trbsegs B LAWS ly3 S3 _ _ _ blk (fmt * N) r 64 HAR3 Hblk_in Hrin3 Hne_br) as HdBR.
unfold zdisjoint in HdBR. cbn [fst snd] in HdBR. change (req_size 64) with 64 in HdBR.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ blk (fmt * N) 7 fpos HAR3 Hblk_in Hfin3) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (fs_frame_bytes 7) with 8192 in HdBF. rewrite EFA3 in HdBF. fold F in HdBF.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ blk (fmt * N) cid pos HAR3 Hblk_in HfinS3) as HdBC.
unfold zdisjoint in HdBC. cbn [fst snd] in HdBC. rewrite EFA3 in HdBC.
assert (HnRf : forall a, r <= a < r + 64 -> ~ (blk <= a < blk + req_size (fmt * N))) by (intros a Ha Hin; clear - HdBR Ha Hin; lia).
assert (HnCf : forall a, cfp <= a < cfp + 24 -> ~ (blk <= a < blk + req_size (fmt * N))) by (intros a Ha Hin; clear - HdBC Ha Hin Hflo Hfhi; lia).
assert (HnFf : forall a, F <= a < F + 8192 -> ~ (blk <= a < blk + req_size (fmt * N))) by (intros a Ha Hin; clear - HdBF Ha Hin; lia).
assert (HnSf : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (blk <= a < blk + req_size (fmt * N)))
by (intros a Ha Hin; destruct Hbzone as [_ Hbz]; clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) N
ltac:(rewrite HNhw; apply (U_HW64 _ 40 39 Hd Wd);
[ rewrite ?ew_ewset_other by lia; exact E40 | rewrite ?ew_ewset_other by lia; exact E39 | exact R44v | exact R42v ]) Ha0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_atD trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k N (-576) (Z_to_bv 64 0x821f0) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ha0.
- unfold MALLOC_MAX. clear - HN1 HN. unfold RGB_NMAX in *. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. clear - Hlive HfN HN1 HN. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX in *. lia.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv; rga_lia).
- assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & fim & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hd7 & Hres7).
apply rga_d_malloc in Hd7; [|clear - HN1 HN; unfold RGB_NMAX in *; lia].
clear Ha0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
destruct (mres_kept B ly3 S3 W3 _ W7 mem7 ly7 S7 _ _ fim N Hres7) as (HK7 & HBin7 & HfimIn).
pose proof (mres_range B LAWS ly7 S7 W7 mem7 md7 ly3 S3 fim N _ _ (proj1 HJ7) Hres7) as Hrng7.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (EFL7 : forall c p, flag_addr ly7 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; pose proof (EFA7 c p) as X; unfold frame_addr in X; lia).
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (apply HBin7; exact Hrin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
assert (HnF7 : forall a, F <= a < F + 8192 -> ~ (fim <> 0 /\ fim <= a < fim + req_size N)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ fim N 7 fpos HAR7 (HfimIn Hnz) Hfin7) as Dd.
rewrite EFA7 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hin. lia. }
assert (HnC7 : forall a, cfp <= a < cfp + 24 -> ~ (fim <> 0 /\ fim <= a < fim + req_size N)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ fim N cid pos HAR7 (HfimIn Hnz) HfinS7) as Dd.
rewrite EFA7 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin Hflo Hfhi. lia. }
assert (HnR7 : forall a, r <= a < r + 64 -> ~ (fim <> 0 /\ fim <= a < fim + req_size N)).
{ intros a Ha [Hnz Hin].
assert (Hne : (fim, N) <> (r, 64)).
{ intros Heq. injection Heq as Hb1 Hb2. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exact (Hnz Hz)|].
pose proof (sep_blocks_pos trbsegs B LAWS ly7 S7 W7 mem7 md7 (r, 64) (fim, N)) as Hsp.
pose proof Hrin3 as Hrin3c. apply in_split in Hrin3c as (l1 & l2 & El). rewrite El, <- app_assoc in Ebl7. cbn [app] in Ebl7.
specialize (Hsp l1 l2 [] HAR7 Ebl7). unfold zdisjoint, block_rng in Hsp. cbn [fst snd] in Hsp. change (req_size 64) with 64 in Hsp. rewrite Hb1 in Hsp. clear - Hsp Ha Hin. lia. }
pose proof (sep_blocks trbsegs B LAWS ly7 S7 W7 mem7 md7 fim N r 64 HAR7 (HfimIn Hnz) Hrin7 Hne) as Dd.
unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (req_size 64) with 64 in Dd. clear - Dd Ha Hin. lia. }
assert (HnS7 : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (fim <> 0 /\ fim <= a < fim + req_size N)).
{ intros a Ha [Hnz Hin]. destruct Hrng7 as [Hz | (Hb4096' & [_ Hbz] & _)]; [exact (Hnz Hz)|]. clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (Hblk_in7 : In (blk, fmt * N) (ablocks B ly7 S7)) by (apply HBin7; exact Hblk_in).
destruct Hrng7 as [Hfim0 | (Hfi4096 & Hfizone & Hficeil & Hfi16 & HfiIn)].
{
subst fim.
assert (Ebl7 : ablocks B ly7 S7 = ablocks B ly3 S3) by (destruct Hres7 as [(_ & Eb & _) | (Hnz & _)]; [exact Eb | exfalso; clear - Hnz; lia]).
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK7 HJ7 AG Usp Hrin3 Hrin7 HfinS3 Hfin3 HFpres7 HFSpres7 HnR7 HnC7 HnF7 HnS7 EFA3 F Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha07; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
ga_ra_frame HS AG HFq F 644 644 4 HRAcfg.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan A_wrap_free.
all: try (unfold GBx; ga_obl_F HRAcfg RF E44).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ7 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ7 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & Hnev7 & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly7 S7 _ (k + 1) blk (fmt * N) (-576) (Z_to_bv 64 0x84414) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ7 Hblk_in7) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact Rblk | rewrite Rblk; reflexivity].
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv; rga_lia).
- assert (Etop7 : ly_top ly7 = ly_top ly) by (destruct (proj1 (proj2 HJ7)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
apply (achain_chain_pre ly7 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly7 _ _ _ _ Etop7 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- exact Tblk. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1 & l2 & El1 & Eab8) & Hfrs8 & Hd8 & HK8).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ8 as (HAR8 & Hly8 & _).
assert (EFA8 : forall c p, frame_addr ly8 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin8 : In (7, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin7).
assert (HfinS8 : In (cid, pos) (frames S8)) by (rewrite Hfrs8; exact HfinS7).
assert (Hrin8 : In (r, 64) (ablocks B ly8 S8)).
{ rewrite Eab8. apply (in_app_remove _ (r, 64) (blk, fmt * N)); [rewrite <- El1; exact Hrin7 | intros Heq; apply Hne_br; symmetry; exact Heq]. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8.
change (8192 / 8) with 1024 in HFSpres8. rewrite EFA8 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK8 HJ8 AG Usp Hrin7 Hrin8 HfinS7 Hfin7 HFpres8 HFSpres8 HnRf HnCf HnFf HnSf EFA7 F Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot8 into Kgot0. rename Kcell8 into Kcell0. rename Kguar8 into Kguar0. rename Kuar8 into Kuar0. rename Vgr8 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
ga_relow HS AG E10 E11 E10n E11n.
clear HEE7. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE8 end.
pose proof (EFA8 7 fpos) as EFA87. fold F in EFA87.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ8 SHOK GBspan 0x84428.
all: try (unfold GBx; ga_obl_blk HJ8 E10n E44 Hrin8).
1: ga_awrR AG fpos F EFA8 54%nat 67%nat.
clear HF HFr HG.
assert (HkX8 : k + 1 + 1 <= EV_RGBADD) by (rewrite HEVv; clear - Hk0; lia).
assert (Hfrs8' : frames S8 = (7, fpos) :: frames S) by (rewrite Hfrs8, Hfrs7; exact Hfrs3).
assert (HP8' : Permutation (ablocks B ly8 S8) (ablocks B ly S)).
{ rewrite Eab8. apply (perm_after_free_last (blk, fmt * N) (ablocks B ly S) (ablocks B ly7 S7) l1 l2); [rewrite Ebl7; exact Eab3 | exact El1]. }
lazymatch goal with |- ?g => idtac "OK-X4-BEFORE-EXIT" end.
rga_exit_same RX HS HJ8 (k + 1 + 1) HkX8 HP8' HEE8 HBASE0 LAWS. }
destruct Hres7 as [(Hz7 & _) | (_ & Ebl7 & _)]; [exfalso; clear - Hz7 Hfi4096; lia|].
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fim N HJ3 HAR7 Ebl7 ltac:(clear - HN1; lia)) as Tfim.
assert (Afim : forall blc lyq ownq i, In (fim, N) blc -> 0 <= i < req_size N ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (fim + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fim N blc i lyq ownq HJ3 HAR7 Ebl7 ltac:(clear - HN1; lia) Hbl Hi). }
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK7 HJ7 AG Usp Hrin3 Hrin7 HfinS3 Hfin3 HFpres7 HFSpres7 HnR7 HnC7 HnF7 HnS7 EFA3 F Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
rreg HS (10%bv : bv 5) Rfim. cbn [ms_regs] in Rfim. rewrite Ha07 in Rfim. symmetry in Rfim. unfold w64 in Rfim.
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as HrqN.
assert (Hfim_rng : 4096 <= fim <= 140737479966720) by (clear - Hfi4096 Hficeil C1 HrqN; lia).
lazymatch type of Rfim with ew ?Ex ?nx = _ =>
idtac "FIM-ATOM" nx;
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rfim, unsigned_lit_small by (clear - Hfim_rng; lia); change (2 ^ 4) with 16;
clear - Hfim_rng Hfi16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
ga_ra_frame HS AG HFq F 644 644 4 HRAcfg.
reshok_bx HS 44%nat.
aj_run_tok trbtbl_lib_ok HS HJ7 SHOK GBspan.
all: try (unfold GBx; ga_obl_F HRAcfg RF E44).
all: try (unfold GBx; ga_obl_cfp HJ7 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x82250.
all: try (unfold GBx; ga_obl_F HRAcfg RF E44).
all: try (unfold GBx; ga_obl_cfp HJ7 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
rreg HS (10%bv : bv 5) Qa0.
ga_join HS ss_AF 300%nat [10%bv : bv 5] ltac:(idtac; ga_join_val HS 300%nat 0%nat Qa0 E300).
rga_hand RC HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists blk, fim, 1. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [rewrite Ebl7, Eab3, <- app_assoc; reflexivity|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]] |].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]] |].
split; [exact E300 | clear; lia].
-
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x82250.
all: try (unfold GBx; ga_obl_F HRAcfg RF E44).
all: try (unfold GBx; ga_obl_cfp HJ7 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
rreg HS (10%bv : bv 5) Qa0.
ga_join HS ss_AF 300%nat [10%bv : bv 5] ltac:(idtac; ga_join_val HS 300%nat 0%nat Qa0 E300).
rga_hand RC HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists blk, fim, 9. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [rewrite Ebl7, Eab3, <- app_assoc; reflexivity|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]] |].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]] |].
split; [exact E300 | clear; lia].
Qed.
End d.
End b.

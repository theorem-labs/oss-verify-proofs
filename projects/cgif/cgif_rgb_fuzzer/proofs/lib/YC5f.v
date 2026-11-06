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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk
YC7e YC7j YCbl YC6e YCav.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_B2a : rga_fromFA B ss_EPI (fun _ => INV_X B) -> rga_fromA B ss_M2 (fun _ => INV_M2 B) -> rga_from B ss_E1b (INV_0 B 0).
Proof.
intros RX RC. rga_prelude.
destruct HINV as (Hk0 & Eab3 & Hbb3).
destruct Hk0 as [Hk0 Hbud].
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hrin).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_tok tratbl_lib_ok HS HJ3 SHOK GBspan.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
all: try (unfold GBx; ga_obl_cfp HJ3 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
assert (HkX : k <= EV_RGBADD) by (assert (0 <= EV_RGBADD) by (vm_compute; discriminate); lia).
assert (HP3 : Permutation (ablocks B ly3 S3) (ablocks B ly S)) by (rewrite Eab3; apply Permutation_refl).
srr_branch_tok tratbl_lib_ok HS SHOK GBspan.
-
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan 0x83b18.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
rga_exit_same RX HS HJ3 k HkX HP3 HEE0 HBASE0 LAWS.
-
rewrite branch_ltu_U in Hc.
pose proof Hcfg as Hcfg'. cbn [obj_at LAY_RgbFrameConfig] in Hcfg'.
destruct Hcfg' as ([_ Rimg] & [_ Rfmt] & [_ Rfattr] & [_ Rfgen] & [_ Rdelay] & _).
cbn [fst snd N.to_nat Z.of_N] in Rimg, Rfmt, Rfattr, Rfgen, Rdelay.
lazymatch type of Hc with context [U ?Ex (SLit 1)] =>
assert (E46x : ew Ex 46 = Z_to_bv 64 fmt) by (rewrite ?ew_ewset_other by lia; exact E46);
pose proof (fmt_test_false Ex 46 fmt E46x Rfmt Hc) as Hfmt end.
clear Hc E46x.
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan A_wrap_malloc.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
all: try (unfold GBx; ga_obl_cfp HJ3 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
assert (Hra88 : 0x81368 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x80ea8])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (E39n : ew E 39 = Z_to_bv 64 Wd) by exact E39. assert (E40n : ew E 40 = Z_to_bv 64 Hd) by exact E40.
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) (fmt * N)
ltac:(rewrite HNhw; apply (U_fN _ 46 40 39 fmt Hd Wd);
[ rewrite ?ew_ewset_other by lia; exact E46 | rewrite ?ew_ewset_other by lia; exact E40 | rewrite ?ew_ewset_other by lia; exact E39
| clear - Hfmt; lia | exact R44v | exact R42v | rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia
| rewrite <- HNhw; clear - HfN; unfold RGB_NMAX in *; lia ]) Ha0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340228) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_atD trasegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k (fmt * N) (-512) (Z_to_bv 64 0x82248) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ha0.
- unfold MALLOC_MAX. clear - HfN. unfold RGB_NMAX in *. lia.
- rewrite Hbb3. clear - Hlive HfN. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX in *. lia.
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
apply (achain_chain_pre ly3 _ (spZ regs - 512) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. apply (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & blk & -> & HJ5 & HP5 & Ha05 & Hfrs5 & Hd5 & Hres5).
apply rga_d_malloc in Hd5; [|clear - HfN; unfold RGB_NMAX in *; lia].
clear Ha0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
destruct (mres_kept B ly3 S3 W3 _ W5 mem5 ly5 S5 _ _ blk (fmt * N) Hres5) as (HK5 & HBin5 & HblkIn).
pose proof (mres_range B LAWS ly5 S5 W5 mem5 md5 ly3 S3 blk (fmt * N) _ _ (proj1 HJ5) Hres5) as Hrng.
pose proof HJ5 as (HAR5 & Hly5 & _).
assert (EFA5 : forall c p, frame_addr ly5 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly5 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (EFL5 : forall c p, flag_addr ly5 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; pose proof (EFA5 c p) as X; unfold frame_addr in X; lia).
assert (Hfin5 : In (7, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin3).
assert (HfinS5 : In (cid, pos) (frames S5)) by (rewrite Hfrs5; exact HfinS3).
assert (Hrin5 : In (r, 64) (ablocks B ly5 S5)) by (apply HBin5; exact Hrin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 7) with 8192 in HFpres5, HFSpres5.
change (8192 / 8) with 1024 in HFSpres5. rewrite EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
assert (HnF : forall a, F <= a < F + 8192 -> ~ (blk <> 0 /\ blk <= a < blk + req_size (fmt * N))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ blk (fmt * N) 7 fpos HAR5 (HblkIn Hnz) Hfin5) as Dd.
rewrite EFA5 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hin. lia. }
assert (HnC : forall a, cfp <= a < cfp + 24 -> ~ (blk <> 0 /\ blk <= a < blk + req_size (fmt * N))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ blk (fmt * N) cid pos HAR5 (HblkIn Hnz) HfinS5) as Dd.
rewrite EFA5 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin Hflo Hfhi. lia. }
assert (HnR : forall a, r <= a < r + 64 -> ~ (blk <> 0 /\ blk <= a < blk + req_size (fmt * N))).
{ intros a Ha [Hnz Hin].
assert (Hne : (blk, fmt * N) <> (r, 64)).
{ intros Heq. injection Heq as Hb1 Hb2. destruct Hres5 as [(Hz & _) | (_ & Ebl5 & _)]; [exact (Hnz Hz)|].
pose proof (sep_blocks_pos trasegs B LAWS ly5 S5 W5 mem5 md5 (r, 64) (blk, fmt * N)) as Hsp.
apply in_split in Hrin3 as (l1 & l2 & El). rewrite El, <- app_assoc in Ebl5. cbn [app] in Ebl5.
specialize (Hsp l1 l2 [] HAR5 Ebl5). unfold zdisjoint, block_rng in Hsp. cbn [fst snd] in Hsp. change (req_size 64) with 64 in Hsp. rewrite Hb1 in Hsp. clear - Hsp Ha Hin. lia. }
pose proof (sep_blocks trasegs B LAWS ly5 S5 W5 mem5 md5 blk (fmt * N) r 64 HAR5 (HblkIn Hnz) Hrin5 Hne) as Dd.
unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (req_size 64) with 64 in Dd. clear - Dd Ha Hin. lia. }
assert (HnS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (blk <> 0 /\ blk <= a < blk + req_size (fmt * N))).
{ intros a Ha [Hnz Hin]. destruct Hrng as [Hz | (Hb4096 & [_ Hbz] & _)]; [exact (Hnz Hz)|]. clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
destruct Hrng as [Hblk0 | (Hb4096 & Hbzone & Hbceil & Hb16 & HbIn)].
{
subst blk.
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK5 HJ5 AG Usp Hrin3 Hrin5 HfinS3 Hfin3 HFpres5 HFSpres5 HnR HnC HnF HnS EFA3 F Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
pose proof (st_ok_pin_reg' trasegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha05; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE5 end.
pose proof (EFA5 7 fpos) as EFA57. fold F in EFA57.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK GBspan 0x83b18.
all: try (unfold GBx; ga_obl_blk HJ5 E10n E44 Hrin5).
1: ga_awrR AG fpos F EFA5 54%nat 67%nat.
clear HF HFr HG.
assert (HkX5 : k + 1 <= EV_RGBADD) by (rewrite HEVv; clear - Hk0; lia).
assert (Hfrs5' : frames S5 = (7, fpos) :: frames S) by (rewrite Hfrs5; exact Hfrs3).
assert (HP5' : Permutation (ablocks B ly5 S5) (ablocks B ly S)).
{ destruct Hres5 as [(_ & Ebl5 & _) | (Hnz & _)]; [rewrite Ebl5, Eab3; apply Permutation_refl | exfalso; clear - Hnz; lia]. }
rga_exit_same RX HS HJ5 (k + 1) HkX5 HP5' HEE5 HBASE0 LAWS. }
destruct Hres5 as [(Hz5 & _) | (_ & Ebl5 & _)]; [exfalso; clear - Hz5 Hb4096; lia|].
assert (Hblk_in : In (blk, fmt * N) (ablocks B ly5 S5)) by exact HbIn.
pose proof (aftok_new_block trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ blk (fmt * N) HJ3 HAR5 Ebl5 ltac:(clear - HfN; lia)) as Tblk.
assert (Ablk : forall blc lyq ownq i, In (blk, fmt * N) blc -> 0 <= i < req_size (fmt * N) ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (blk + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ blk (fmt * N) blc i lyq ownq HJ3 HAR5 Ebl5 ltac:(clear - HfN; lia) Hbl Hi). }
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK5 HJ5 AG Usp Hrin3 Hrin5 HfinS3 Hfin3 HFpres5 HFSpres5 HnR HnC HnF HnS EFA3 F Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
rreg HS (10%bv : bv 5) Rblk. cbn [ms_regs] in Rblk. rewrite Ha05 in Rblk. symmetry in Rblk. unfold w64 in Rblk.
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as Hrq.
assert (Hblk_rng : 4096 <= blk <= 140737479966720) by (clear - Hb4096 Hbceil C1 Hrq; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trasegs Ev _ _ 152 (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rblk, unsigned_lit_small by (clear - Hblk_rng; lia); change (2 ^ 4) with 16;
clear - Hblk_rng Hb16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE5 end.
pose proof (EFA5 7 fpos) as EFA57. fold F in EFA57.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK GBspan A_asan_memcpy.
all: try (unfold GBx; ga_obl_blk HJ5 E10n E44 Hrin5).
all: try (unfold GBx; ga_obl_cfp HJ5 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA5 54%nat 67%nat.
clear HF HFr HG.
assert (Himg_in : In (img, fmt * N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. left.
unfold timg_block, tfmt_okb. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himg5 : In (img, fmt * N) (ablocks B ly5 S5)) by (apply HBin5; rewrite Eab3; exact Himg_in).
pose proof (proj1 HJ5) as HARm.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) HARm Himg5) as (_ & Hi4096 & Hiceil & _ & Hipres & _).
assert (Hne_bi : (blk, fmt * N) <> (img, fmt * N)).
{ intros Heq. injection Heq as Hb1. apply in_split in Himg_in as (l1 & l2 & El). rewrite <- Eab3 in El. rewrite El, <- app_assoc in Ebl5. cbn [app] in Ebl5.
pose proof (sep_blocks_pos trasegs B LAWS ly5 S5 W5 mem5 md5 (img, fmt * N) (blk, fmt * N) l1 l2 [] HAR5 Ebl5) as Hsp.
unfold zdisjoint, block_rng in Hsp. cbn [fst snd] in Hsp. rewrite Hb1 in Hsp. clear - Hsp Hrq. lia. }
pose proof (sep_blocks trasegs B LAWS ly5 S5 _ _ _ blk (fmt * N) img (fmt * N) HARm Hblk_in Himg5 Hne_bi) as HdBI.
unfold zdisjoint in HdBI. cbn [fst snd] in HdBI.
pose proof (sep_block_frame trasegs B LAWS ly5 S5 _ _ _ blk (fmt * N) 7 fpos HARm Hblk_in Hfin5) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (fs_frame_bytes 7) with 8192 in HdBF. rewrite EFA5 in HdBF. fold F in HdBF.
pose proof (sep_block_frame trasegs B LAWS ly5 S5 _ _ _ blk (fmt * N) cid pos HARm Hblk_in HfinS5) as HdBC.
unfold zdisjoint in HdBC. cbn [fst snd] in HdBC. rewrite EFA5 in HdBC.
assert (Hne_br : (blk, fmt * N) <> (r, 64)).
{ intros Heq. injection Heq as Hb1 Hb2. apply in_split in Hrin3 as (l1 & l2 & El). rewrite El, <- app_assoc in Ebl5. cbn [app] in Ebl5.
pose proof (sep_blocks_pos trasegs B LAWS ly5 S5 W5 mem5 md5 (r, 64) (blk, fmt * N) l1 l2 [] HAR5 Ebl5) as Hsp.
unfold zdisjoint, block_rng in Hsp. cbn [fst snd] in Hsp. change (req_size 64) with 64 in Hsp. rewrite Hb1 in Hsp. clear - Hsp Hrq. lia. }
pose proof (sep_blocks trasegs B LAWS ly5 S5 _ _ _ blk (fmt * N) r 64 HARm Hblk_in Hrin5 Hne_br) as HdBR.
unfold zdisjoint in HdBR. cbn [fst snd] in HdBR. change (req_size 64) with 64 in HdBR.
gboxh HdBI. gboxh HdBF. gboxh HdBC. gboxh HdBR. gboxh Hbzone.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (12%bv : bv 5) (fmt * N)
ltac:(rewrite HNhw; apply (U_fN _ 46 40 39 fmt Hd Wd);
[ rewrite ?ew_ewset_other by lia; exact E46 | rewrite ?ew_ewset_other by lia; exact E40 | rewrite ?ew_ewset_other by lia; exact E39
| clear - Hfmt; lia | exact R44v | exact R42v | rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia
| rewrite <- HNhw; clear - HfN; unfold RGB_NMAX in *; lia ]) Ra2.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ5 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly5 S5 _ _ blk img (fmt * N) (-512) (Z_to_bv 64 0x822ac) HJ5) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact Rblk | rewrite Rblk; reflexivity].
- rewrite Ra1. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact E45 | rewrite E45; reflexivity].
- exact Ra2.
- clear - HfN. unfold RGB_NMAX in *. lia.
- clear - Hb4096. lia.
- clear - Hbceil Hrq C1. lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (blk + (a - blk)) by lia; apply Ablk; [exact Hblk_in | clear - Ha Hrq; lia] | unfold ESTACK; clear - Ha Hbceil Hrq Hceil Hslo FFS; lia].
- apply (amem_range_of_block trasegs B LAWS ly5 S5 _ _ _ blk (fmt * N) blk (fmt * N) HARm Hblk_in); [lia | clear - Hrq; lia].
- apply (range_addressable_of_block trasegs B LAWS ly5 S5 _ _ _ blk (fmt * N) blk (fmt * N) HARm Hblk_in); [lia | clear - Hrq; lia].
- intros _. apply (shadow_hull_vis_of_block trasegs B LAWS ly5 S5 _ _ _ blk (fmt * N) blk (fmt * N) HARm Hblk_in); [lia | clear - Hrq; lia | clear - HfN; lia].
- split; [clear - Hi4096; lia|]. split; [clear - Hiceil Hrq C1; lia|]. split.
{ intros a Ha. assert (Ha' : img <= a < img + req_size (fmt * N)) by (destruct Hrq as [_ Hrq2]; clear - Ha Hrq2; lia).
split; [apply (aview_some_of_apresent trasegs); exact (proj1 (Hipres a Ha')) | unfold spZ; rewrite Rsp; ga_evalE0 AG; unfold ESTACK; clear - Ha' Hiceil Hceil Hslo FFS; lia]. }
split; [unfold gbox in HdBI; clear - HdBI Hrq; lia|]. split.
{ apply (amem_range_of_block trasegs B LAWS ly5 S5 _ _ _ img (fmt * N) img (fmt * N) HARm Himg5); [lia | clear - Hrq; lia]. }
split; [apply (range_addressable_of_block trasegs B LAWS ly5 S5 _ _ _ img (fmt * N) img (fmt * N) HARm Himg5); [lia | clear - Hrq; lia]|].
intros _. apply (shadow_hull_vis_of_block trasegs B LAWS ly5 S5 _ _ _ img (fmt * N) img (fmt * N) HARm Himg5); [lia | clear - Hrq; lia | clear - HfN; lia]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Ha06 & Heff6 & Hfr6 & Hpres6).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptI3 Hfr6 Hpres6 AG HdBF HdBC HdBR Hbzone Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
ga_relow HS AG E10 E11 E10n E11n.
clear HEE5. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE5 end.
ga_ra_frame HS AG HFq F 644 644 4 HRAcfg.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ6 SHOK GBspan A_wrap_malloc.
all: try (unfold GBx; ga_obl_blk HJ6 E10n E44 Hrin5).
all: try (unfold GBx; ga_obl_F HRAcfg RF E44).
all: try (unfold GBx; ga_obl_cfp HJ6 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp).
1: ga_awrR AG fpos F EFA5 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_M2 200%nat (@nil (bv 5)) ltac:(idtac).
assert (Hfrs5' : frames S5 = (7, fpos) :: frames S) by (rewrite Hfrs5; exact Hfrs3).
rga_hand RC HS HJ6 (k + 1); [rga_E_tac HEE5 | ].
exists blk. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [rewrite Ebl5, Eab3; reflexivity|].
split; [ | split; [exact Tblk | exact Ablk]].
repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]. exact Rblk.
Qed.
End d.
End b.

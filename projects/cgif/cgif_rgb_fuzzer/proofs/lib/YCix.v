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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpo YCpq YClz YCqd YCpr.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_E2b : rga_fromA B ss_A3 (fun _ => INV_N B 3 news_A2) -> rga_from B ss_A2 (INV_N B 3 news_A2).
Proof.
intros RC. rga_prelude. unfold ss_A2 in HS.
destruct HINV as (bs & Hk0 & Hfmt & Eab3 & Hnews & av & E300 & Hav).
destruct Hk0 as [Hk0 Hbud].
unfold news_A2, news_A1 in Eab3, Hnews. rga_cbn_cx Eab3. rga_cbn_cx Hnews. cbn [app] in Eab3, Hnews.
cbn [rga_news] in Hnews. destruct bs as [|blk bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rblk & Tblk & Ablk) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|fim bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rfim & Tfim & Afim) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|tb bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rtb & Ttb & Atb) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|? ?]; [|contradiction]. clear Hnews. cbn [combine map snd] in Eab3.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hrin).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; right; right; left; reflexivity).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (tb, 48) HAR3 ltac:(rewrite Eab3; apply Permutation_refl) Hrin ltac:(right; right; left; reflexivity)) as HzR_tb.
unfold zdisjoint, block_rng in HzR_tb. cbn [fst snd] in HzR_tb. change (req_size 64) with 64 in HzR_tb.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb (48) HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ tb (48) 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ tb (48) cid pos HAR3 Htb_in3 HfinS3) as HdC_tb.
unfold zdisjoint in HdC_tb. cbn [fst snd] in HdC_tb. rewrite EFA3 in HdC_tb.
assert (HnR_tb : forall a, r <= a < r + 64 -> ~ (tb <= a < tb + req_size (48))) by (intros a Ha Hin; clear - HzR_tb Ha Hin; lia).
assert (HnC_tb : forall a, cfp <= a < cfp + 24 -> ~ (tb <= a < tb + req_size (48))) by (intros a Ha Hin; clear - HdC_tb Ha Hin Hflo Hfhi; lia).
assert (HnF_tb : forall a, F <= a < F + 8192 -> ~ (tb <= a < tb + req_size (48))) by (intros a Ha Hin; clear - HdF_tb Ha Hin; lia).
assert (HnS_tb : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (tb <= a < tb + req_size (48)))
by (intros a Ha Hin; destruct Htbzone as [_ Hbz]; clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1; lia).
gboxh HdF_tb. gboxh HdC_tb. gboxh HzR_tb. gboxh Htbzone.
idtac "T-BEFORE-MEMSET".
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 _ _ tb 0 (48) (-576) (Z_to_bv 64 0x822a8) HJ3) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact Rtb | rewrite Rtb; reflexivity].
- exact Ra1.
- exact Ra2.
- clear; lia.
- clear - Htb4096. lia.
- clear - Htbceil Hrqtb C1. lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (tb + (a - tb)) by lia; apply Atb; [exact Htb_in3 | clear - Ha Hrqtb; lia] | unfold ESTACK; clear - Ha Htbceil Hrqtb Hceil Hslo FFS; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ tb (48) tb (48) HAR3 Htb_in3); [lia | clear - Hrqtb; lia].
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ tb (48) tb (48) HAR3 Htb_in3); [lia | clear - Hrqtb; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ tb (48) tb (48) HAR3 Htb_in3); [lia | clear - Hrqtb; lia | clear; lia].
- exact I. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Ha06 & Heff6 & Hfr6 & Hpres6).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptI3 Hfr6 Hpres6 AG HdF_tb HdC_tb HzR_tb Htbzone Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
ga_relow HS AG E10 E11 E10n E11n.
try clear HEEc. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEEc end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb (48) (proj1 HJ6) Htb_in3) as (_ & _ & _ & _ & Htbpres6 & _).
assert (ZBtb : forall off (nn : nat), 0 <= off -> off + Z.of_nat nn <= 48 -> val_mem trbsegs (mrestrict (w_H W3) mem6) (tb + off) nn 0).
{ intros off nn Ho1 Ho2. apply rg_val_mem_zero. intros i Hi. replace (tb + off + i) with (tb + (off + i)) by lia. rewrite (Heff6 (off + i)) by lia. reflexivity. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 305%nat) 0 48 0 48 [YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0)); YQ0b.mkChunk 16 (CVal 8 (SLit 0)); YQ0b.mkChunk 24 (CVal 8 (SLit 0)); YQ0b.mkChunk 32 (CVal 8 (SLit 0)); YQ0b.mkChunk 40 (CVal 4 (SLit 0)); YQ0b.mkChunk 44 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
ga_evalE0 AG; split; [clear - Htb4096; lia|]; split; [clear - Htbceil Hrqtb C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Htbpres6 (tb + o) ltac:(clear - Ho Hrqtb; lia)))
| repeat (apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ tb _ _ (SLit 0) 0); [reflexivity | zside | zside | apply ZBtb; cbn; clear; lia] |]); apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_disj_blk F r cfp HdF_tb HdC_tb HzR_tb Htbzone | match goal with |- ?g => idtac "DISJ-BLK" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch goal with |- ?g => idtac "OK-REGION" end.
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ6 SHOK GBspan A_wrap_malloc.
all: try (unfold GBx; ga_obl_blk HJ6 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_A3 400%nat (@nil (bv 5)) ltac:(idtac).
rga_hand RC HS HJ6 k; [rga_E_tac HEEc | ].
exists [blk; fim; tb]. split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [unfold news_A2, news_A1; rga_cbn_cx_goal; cbn [app combine map snd]; exact Eab3|].
split; [ unfold news_A2, news_A1; rga_cbn_cx_goal; cbn [app rga_news];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]] | exact I] |].
exists av. split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E300 | exact Hav].
Qed.
End c.
End b.

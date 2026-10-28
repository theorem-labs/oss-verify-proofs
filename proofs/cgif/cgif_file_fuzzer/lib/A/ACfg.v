(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YC20 YC7x YC21 YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YE00 YE01 YE02 YE03 YO08 YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACel ACer ACfm ACf5 ACf9 ACf7 ACf8 ACf6 ACfh ACf4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACf5 ACf9 ACf7 ACf6 ACf4 ACfh ACfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Variable XN : xnums.
Variable XL : Z -> Z.
Variables (wfn : Z).
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis AUNLINKX : aunlink_x tfibsegs B tfib_K 0x9c9cc.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma lx_U_aux : True -> forall fsU : Fs.Fs, rt_fromX B MT XL (PT fsU) ss_U (INV_U B fsU).
Proof.
intros _ fsU. rt_preludeX.
pose proof HINV as (HkU & HaccU & HPermU & HSNKU & EfsU & HsoU). cbn [c_T c_ly c_S] in HaccU, HPermU.
assert (HnFPs : forall a, 1 <= a -> ~ inFP RTFP a) by (intros a Ha (r & [<-|[]] & Hr); cbn in Hr; clear - Ha Hr; lia).
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80a80) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HPREu : afn_pre tfibsegs B AUNLINK_STK ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ eapply (afn_pre_at tfibsegs B LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem msX) mdX _ (ms_regs msX) AUNLINK_STK (sp1 - spZ regs));
[ exact HJ3
| rewrite EspX; clear; lia
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| unfold AUNLINK_STK; clear; lia
| unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia
| rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
| rewrite EraX; clear; lia
| rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
| rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
| rewrite Es0X, EspX; exact Hch1 ]
| ] end.
apply SRr_ret. intros HAIu. cbn [cfg_model] in HAIu.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc x_K].
replace fsU with (m_fs md3) by exact EfsU.
unfold ff_unl.
lazymatch goal with |- srealizes _ (mkCfg (mkst ?rg _ ?mm _) ?mdX) (unlink_shape _ ?TA ?TB) =>
pose proof (AUNLINKX W3 ly3 S3 rg mm mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) TA TB HAIu HPREu) as CALL end.
unfold cfg_at in CALL. change (w64 641484) with (Z_to_bv 64 641484) in CALL.
apply CALL; clear CALL.
{ rewrite Ra0. reflexivity. }
{ exact HSNKU. }
{
intros W6 c6 Hwle6 HAI6 HpostU. unfold aunlink_postA in HpostU.
destruct HpostU as (regs6 & mem6 & md6 & eno & -> & HJu & HP6 & Ha06 & HSNK6 & Efds6 & Efs6 & Heno & Herr).
eapply (srz_enter tfibsegs W6); [exact HAI6|]. clear HAI6. rewrite Rra.
rewrite EspX in HJu.
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HJu
ltac:(unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia) ltac:(intros a Ha; left; exact Ha)) as HJ6. cbn [app] in HJ6.
replace (k + 0) with k in HJ6 by (clear; lia).
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin3) as (_ & _ & HFpres6 & HFSpres6).
change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6. change (256 / 8) with 32 in HFSpres6. rewrite !EFA3 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
aconstsF HJ6 Kgot6 Kcell6 Kguar6 Kuar6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres6 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJu | exact HJ6 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJu | exact HJ6 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot6 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell6 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar6 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar6 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RTBspan 0x80878.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into Himgv.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) (fun _ _ => _ -> srealizes _ _ (ff_leaf _ ?fsL)) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HSNKF : asink_none tfibsegs tfib_K (mrestrict (w_H Wg) (ms_mem msF)) mdF) by (eapply (asink_none_imgv B AIL); [exact Himgv | destruct md6; reflexivity | exact HSNK6]);
assert (EfsF : m_fs mdF = fsL) by (transitivity (m_fs md6); [destruct md6; reflexivity | exact Efs6]);
assert (PXKH : forall lyq bl (Wq : world tfibsegs) (m m' : word -> option byte) (mdq : Model) matq,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wq) m' a = aview tfibsegs (w_H Wq) m a) ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m mdq ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m' (with_vm_backing (m_vm_lazy mdq) matq mdq))
by (clear - AIL; intros lyq bl Wq m m' mdq matq Hv (Hsn & Hfs & Hso & Hbl); split; [|split; [destruct mdq; exact Hfs | split; [exact Hso | exact Hbl]]];
eapply (asink_none_imgv B AIL); [exact Hv | destruct mdq; reflexivity | exact Hsn]);
eapply SRr_mono;
[ eapply (rt_XP B MT MTL RTFP TL LAWS ML ASF FFL MTF (rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL) PXKH
(mkRTCX ly S W regs mem md p n fpos sp1 E0 T) Ev _ _ ly3 S3 Wg msF mdF HBASE0)
| ] end end.
{ lazymatch goal with |- rt_E _ ?Ev => idtac end.
repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end).
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1]. split; [assumption|]; repeat (split; [eassumption|]); eassumption. }
{ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ6. }
{ cbn [c_fpos]. exact Hfrs3. }
{ cbn [c_S]. exact HMLE. }
{   split; [clear - HkU; lia|].
split; [cbn [c_T]; exact HaccU|].
split; [cbn [c_ly c_S]; exact HPermU|].
split; [exact HSNKF|]. split; [exact EfsF|]. split; [|cbn [c_ly c_S]; exact HPermU].
rewrite <- EfsF. eapply (ajournal_sorted tfibsegs B); [exact HJ6 | exact HSORT0]. }
{ exact HS. }
cbv beta. intros W7 c7 Hwle7 (ly' & S' & regs' & mem' & md' & k' & -> & HJ7 & Hk7 & HP7 & Ha07 & HPl & HMLE7 & (HSNK7 & Efs7 & Hso7 & HPerm7)) HAI7.
lazymatch goal with |- srealizes _ _ (ff_leaf _ ?fsL) =>
unfold ff_leaf; apply (HLEAF (LL 0 fsL []) W7); cbn [c_W c_ly c_S c_regs c_mem c_md c_p c_n] end.
{ pose proof HJ7 as (_ & _ & _ & Hwle07 & _). exact Hwle07. }
{ exact HAI7. }
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T] in HJ7, HMLE7, HPerm7.
change ACfn.LLVMF_STK with LLVMF_STK. change ACfn.EV_LIB with EV_LIB. fold RTFP.
split; [exact HJ7|]. split; [exact Hk7|]. split; [exact HP7|]. split; [exact Ha07|].
split; [exact HPerm7|].
split; [exact (ajournal_fds_restored tfibsegs B tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HSNK0 HSNK7)|].
split; [exact Efs7|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hso7|].
split; [exact HSNK7|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HAM0)|].
split; [rewrite <- HTX; exact HMLE7|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply HnFPs. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & _). clear - Hi Hp4096. lia.
}
{
intros W6 c6 Hwle6 HAI6 HpostU. unfold aunlink_postB in HpostU.
destruct HpostU as (regs6 & mem6 & md6 & -> & HJu & HP6 & Ha06 & HSNK6 & Efds6 & Efs6 & Hlk).
eapply (srz_enter tfibsegs W6); [exact HAI6|]. clear HAI6. rewrite Rra.
rewrite EspX in HJu.
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HJu
ltac:(unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia) ltac:(intros a Ha; left; exact Ha)) as HJ6. cbn [app] in HJ6.
replace (k + 0) with k in HJ6 by (clear; lia).
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin3) as (_ & _ & HFpres6 & HFSpres6).
change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6. change (256 / 8) with 32 in HFSpres6. rewrite !EFA3 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
aconstsF HJ6 Kgot6 Kcell6 Kguar6 Kuar6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres6 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJu | exact HJ6 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJu | exact HJ6 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot6 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell6 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar6 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar6 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RTBspan 0x80878.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into Himgv.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) (fun _ _ => _ -> srealizes _ _ (ff_leaf _ ?fsL)) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HSNKF : asink_none tfibsegs tfib_K (mrestrict (w_H Wg) (ms_mem msF)) mdF) by (eapply (asink_none_imgv B AIL); [exact Himgv | destruct md6; reflexivity | exact HSNK6]);
assert (EfsF : m_fs mdF = fsL) by (transitivity (m_fs md6); [destruct md6; reflexivity | exact Efs6]);
assert (PXKH : forall lyq bl (Wq : world tfibsegs) (m m' : word -> option byte) (mdq : Model) matq,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wq) m' a = aview tfibsegs (w_H Wq) m a) ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m mdq ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m' (with_vm_backing (m_vm_lazy mdq) matq mdq))
by (clear - AIL; intros lyq bl Wq m m' mdq matq Hv (Hsn & Hfs & Hso & Hbl); split; [|split; [destruct mdq; exact Hfs | split; [exact Hso | exact Hbl]]];
eapply (asink_none_imgv B AIL); [exact Hv | destruct mdq; reflexivity | exact Hsn]);
eapply SRr_mono;
[ eapply (rt_XP B MT MTL RTFP TL LAWS ML ASF FFL MTF (rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL) PXKH
(mkRTCX ly S W regs mem md p n fpos sp1 E0 T) Ev _ _ ly3 S3 Wg msF mdF HBASE0)
| ] end end.
{ lazymatch goal with |- rt_E _ ?Ev => idtac end.
repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end).
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1]. split; [assumption|]; repeat (split; [eassumption|]); eassumption. }
{ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ6. }
{ cbn [c_fpos]. exact Hfrs3. }
{ cbn [c_S]. exact HMLE. }
{   split; [clear - HkU; lia|].
split; [cbn [c_T]; exact HaccU|].
split; [cbn [c_ly c_S]; exact HPermU|].
split; [exact HSNKF|]. split; [exact EfsF|]. split; [|cbn [c_ly c_S]; exact HPermU].
rewrite <- EfsF. eapply (ajournal_sorted tfibsegs B); [exact HJ6 | exact HSORT0]. }
{ exact HS. }
cbv beta. intros W7 c7 Hwle7 (ly' & S' & regs' & mem' & md' & k' & -> & HJ7 & Hk7 & HP7 & Ha07 & HPl & HMLE7 & (HSNK7 & Efs7 & Hso7 & HPerm7)) HAI7.
lazymatch goal with |- srealizes _ _ (ff_leaf _ ?fsL) =>
unfold ff_leaf; apply (HLEAF (LL 0 fsL []) W7); cbn [c_W c_ly c_S c_regs c_mem c_md c_p c_n] end.
{ pose proof HJ7 as (_ & _ & _ & Hwle07 & _). exact Hwle07. }
{ exact HAI7. }
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T] in HJ7, HMLE7, HPerm7.
change ACfn.LLVMF_STK with LLVMF_STK. change ACfn.EV_LIB with EV_LIB. fold RTFP.
split; [exact HJ7|]. split; [exact Hk7|]. split; [exact HP7|]. split; [exact Ha07|].
split; [exact HPerm7|].
split; [exact (ajournal_fds_restored tfibsegs B tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HSNK0 HSNK7)|].
split; [exact Efs7|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hso7|].
split; [exact HSNK7|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HAM0)|].
split; [rewrite <- HTX; exact HMLE7|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply HnFPs. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & _). clear - Hi Hp4096. lia.
}
Qed.
Definition lx_U := lx_U_aux I.
End c.
End b.

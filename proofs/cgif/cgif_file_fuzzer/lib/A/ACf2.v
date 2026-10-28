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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACer ACfm ACf5 ACf9 ACf7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.
Ltac gcfg_rewin HS wlo whi ptac :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := eval vm_compute in (idx_of (fun r => match YP09.r_base r with Some 75%nat => Z.eqb (YP09.r_lo r) 32 | _ => false end) rs) in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r wlo whi (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; ptac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FP0 : FP = [].
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B MT.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_C_aux : rt_from B MT FP POST ss_X (INV_X B MT) -> rt_from B MT FP POST ss_D (INV_D B MT FP) -> rt_from B MT FP POST ss_C (INV_C B MT).
Proof.
intros RX RD. rt_prelude.
pose proof HINV as (Hk0 & Hacc & Eab3 & attr & gen & w16 & h16 & ngp & cur & r & HGC & Hattr4 & Hcur14 & E193).
pose proof HGC as (E185 & E186 & E187 & E188 & E189 & E190 & Rattr & Rgen & Rw & Rh & Rngp & Rcur & Rr & Hr14 & Vp & Vn & Vc & Hprov & Hwhy).
cbn [c_n c_sp1 c_p] in Rcur, Hr14, Vp, Vn, Vc, Hwhy. clear Vp Vn Vc.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
pose proof (proj1 (proj2 HJ3)) as Hly3. pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (B75 : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (HpR : 4096 <= p /\ p + n <= alloc_ceiling).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
- rewrite HpE, Hn0. unfold A_EMPTY. clear - C1. lia.
- assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hp3) as (_ & Hq4096 & Hqceil & _).
pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - Hq4096 Hqceil Hrq. lia. }
assert (HSPB : alloc_ceiling <= spZ regs - LLVMF_STK /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
assert (HNGP : 0 <= 3 * ngp <= 3 * 65535) by (clear - Rngp; lia).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256 \/ sp1 <= a < sp1 + 32).
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
{ awrRT AG fpos F EFA3. }
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear_frames.
clear UN1.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = RT_malloc_ra) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; unfold RT_malloc_ra; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (3 * ngp)) (rt_denot_mul3 Ev 189 ngp ltac:(ewpeel; exact E189) ltac:(clear - Rngp; lia)) Ra0 end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Xra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
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
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Xra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : st_nev S3 < EV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk0; lia).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338224 with (pc_wrap_malloc (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (AMALLOC4 W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k (3 * ngp) (sp1 - spZ regs) (Z_to_bv 64 RT_malloc_ra) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ3) end.
- exact Ra0.
- unfold MALLOC_MAX. clear - HNGP. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_LIB in Hlive. clear - Hlive HNGP. lia.
- rewrite EspX. clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1; lia.
- rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
- exact Rra.
- apply ret_ok_even. vm_compute. reflexivity.
- exact HEVc.
- apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; unfold RT_malloc_ra; clear; lia].
- replace (pc_malloc_ra0 (as_code B)) with 0x52bcc by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52bcc 0x80818); [exact Hra | exact EraX | right; right; right; right; split; reflexivity].
-
apply (mok_station MT S S3 T acc (mo_malloc MT (3 * ngp)) MTL HMOK HMLE); [apply (mo_malloc_nonneg MT MTL); clear - HNGP; lia|].
pose proof (mo_malloc_mono MT MTL (3 * ngp) 196605 ltac:(clear - HNGP; lia)) as Hmm. unfold ACC0, RT_NEED1, ACC_pal in *. pose proof (mo_free_nonneg MT MTL). clear - Hacc HNEED Hmm H; lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres4096 & Eab4 & HK & HMLE4c).
pose proof (mle_station MT S S3 S4 acc (mo_malloc MT (3 * ngp)) MTL HMLE HMLE4c) as HMLE4.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
pose proof (proj1 HJ4) as HAR4.
clear HUP. assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W4) mem4 a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
pose proof (proj1 (proj2 HJ4)) as Hly4. pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo4 & Ehi4 & _).
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (Hres_in : In (res, 3 * ngp) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (3 * ngp) HAR4 Hres_in) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR4 Hres_in) as Hph_img.
pose proof (le_req_size (3 * ngp) ltac:(clear - HNGP; lia)) as Hrq1. pose proof (req_size_le1 (3 * ngp) ltac:(clear - HNGP; lia)) as Hrq2.
pose proof (aftok_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * ngp) HJ3 HAR4 Eab4 ltac:(clear - HNGP; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, 3 * ngp) blc -> 0 <= i < req_size (3 * ngp) ->
awr_byte LLVMF_STK (spZ regs) FP (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq ii Hbl Hiq. exact (awr_new_block_any tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * ngp) blc ii lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HNGP; lia) Hbl Hiq). }
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ [(res, 3 * ngp)])) by (rewrite Eab4, Eab3; apply Permutation_refl).
pose proof (sep_block_frame tfibsegs B LAWS ly4 S4 _ _ _ res (3 * ngp) 2 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 2) with 256 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
assert (Hdsrc : res + 3 * ngp <= p \/ p + n <= res).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
- rewrite HpE, Hn0. unfold A_EMPTY. clear - Hph_img Hrq1 HNGP. unfold off_img in Hph_img. lia.
- pose proof (sep_tmp_entry B LAWS ly4 S4 W4 mem4 md4 (ablocks B ly S) res (3 * ngp) p n HAR4 HPerm4 Hin) as D.
pose proof (le_req_size n ltac:(clear - Hnr; lia)) as Hrqn. clear - D Hrq1 Hrqn. lia. }
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hx; clear - Ha Hx Hph Hph_ia Hph_img Hrq1 Hrq2 HNGP HF8c HF8lo HF8hi HFceil C1 C3; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hx; clear - Ha Hx HdPF Hrq1 HNGP; lia
| intros a Ha; first [exfalso; clear - Ha; lia | apply (proj1 (HFpres4 a ltac:(clear - Ha; lia)))] ] end
| keptRT HK HJ4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 ltac:(idtac; fail) ltac:(idtac; fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (@BV 5 10 I) Rres. rewrite Ha04 in Rres. symmetry in Rres. unfold w64 in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact tfibsegs Ex _ _ nx (HPTR 4) HS
ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres; rewrite unsigned_lit_small by (clear - Hph Hpceil Hrq1 HNGP C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia);
change (2 ^ 4) with 16; clear - Hph Hpceil Hp16 Hrq1 HNGP C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
rebv HS E70 RF B70 B75.
gcfg_rewin HS 32 40 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(clear - Ho; lia)))).
reshok HS.
clear Zsm. set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256 \/ F + 32 <= a < F + 40 \/ sp1 <= a < sp1 + 32).
aj_run_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan.
{ awrRT AG fpos F EFA4. }
unrunRD HFr Zsm Usp B70 Hsp1 UN2. clear_frames. clear UN2.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
relowRT HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
all: hc_bool Hc ltac:(fun H => hc_atom H 11%nat n E11n ltac:(clear - Hn26; lia);
lazymatch type of H with context [U ?E' (SAlu ALU_ADD (SMd M_MUL (SOff 189 0) (SLit 3)) (SOff 193 0))] =>
rewrite (U_3x_add E' 189 193 ngp cur ltac:(ewpeel; exact E189) ltac:(ewpeel; exact E193) ltac:(clear - Rngp; lia) ltac:(clear - Rcur Hn26; lia)) in H end).
all: hc_prop Hc.
-
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan A_asan_memcpy.
{ awrRT AG fpos F EFA4. }
unrunRD HFr Zsm Usp B70 Hsp1 UN2. clear_frames. clear UN2.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly4 S4 W4 (ms_mem msX) _ _ |- _ => pose proof HJc as HJcall end;
assert (HppresB : forall a, p + cur <= a < p + cur + 3 * ngp -> apresent (w_H W4) (ms_mem msX) a);
[ destruct Hpn as [[Hn0 _] | [Hnr Hin]];
[ intros a Ha; exfalso; clear - Ha Hn0 Hc Rcur HNGP; lia
| assert (Hin4 : In (p, n) (ablocks B ly4 S4)) by (rewrite Eab4, Eab3; apply in_app_iff; left; exact Hin);
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJcall) Hin4) as (_ & _ & _ & _ & HPp & _);
pose proof (le_req_size n ltac:(clear - Hnr; lia)) as Hrqn;
intros a Ha; apply (proj1 (HPp a ltac:(clear - Ha Hc Rcur Hrqn HNGP; lia))) ]
| assert (HsrcA : amem_range (p + cur) (3 * ngp));
[ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]];
[ rewrite HpE; unfold amem_range, A_EMPTY; left; clear - Hn0 Hc Rcur HNGP C5; lia
| assert (Hin4 : In (p, n) (ablocks B ly4 S4)) by (rewrite Eab4, Eab3; apply in_app_iff; left; exact Hin);
pose proof (le_req_size n ltac:(clear - Hnr; lia)) as Hrqn;
apply (amem_range_of_block tfibsegs B LAWS ly4 S4 W4 _ _ p n _ _ (proj1 HJcall) Hin4); clear - Hc Rcur Hrqn HNGP; lia ]
| assert (HsrcR : range_addressable (aview tfibsegs (w_H W4) (ms_mem msX)) SHADOW_OFF (p + cur) (3 * ngp));
[ destruct Hpn as [[Hn0 _] | [Hnr Hin]];
[ apply range_addressable_nil; clear - Hn0 Hc Rcur HNGP; lia
| assert (Hin4 : In (p, n) (ablocks B ly4 S4)) by (rewrite Eab4, Eab3; apply in_app_iff; left; exact Hin);
pose proof (le_req_size n ltac:(clear - Hnr; lia)) as Hrqn;
apply (range_addressable_of_block tfibsegs B LAWS ly4 S4 W4 _ _ p n _ _ (proj1 HJcall) Hin4); clear - Hc Rcur Hrqn HNGP; lia ]
| assert (HsrcH : 0 < 3 * ngp -> shadow_hull_vis (aview tfibsegs (w_H W4) (ms_mem msX)) (p + cur) (3 * ngp));
[ destruct Hpn as [[Hn0 _] | [Hnr Hin]];
[ intros Hn1; exfalso; clear - Hn1 Hn0 Hc Rcur HNGP; lia
| assert (Hin4 : In (p, n) (ablocks B ly4 S4)) by (rewrite Eab4, Eab3; apply in_app_iff; left; exact Hin);
pose proof (le_req_size n ltac:(clear - Hnr; lia)) as Hrqn;
intros Hn1; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly4 S4 W4 _ _ p n _ _ (proj1 HJcall) Hin4); clear - Hc Rcur Hrqn HNGP Hn1; lia ]
| ] ] ] ] end.
rreg HS (10%bv : bv 5) Xa0. rreg HS (1%bv : bv 5) Yra. rreg HS (2%bv : bv 5) Xsp. rreg HS (3%bv : bv 5) Xgp. rreg HS (4%bv : bv 5) Xtp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 12 I) (Z_to_bv 64 (3 * ngp)) (rt_denot_mul3 Ev 189 ngp ltac:(ewpeel; exact E189) ltac:(clear - Rngp; lia)) Xa2;
rreg_by HS (@BV 5 11 I) (Z_to_bv 64 (p + cur)) (denot_add2 Ev 10 193 p cur E10n ltac:(ewpeel; exact E193) ltac:(clear - HpR; lia) ltac:(clear - Rcur; lia)
ltac:(clear - HpR Hc Rcur HNGP C1; lia)) Xa1 end.
lazymatch type of Xsp with getr ?rg 2 = _ =>
assert (EspC : spZ rg = sp1) by (unfold spZ; rewrite Xsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite ?E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) end.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at_io B LAWS OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)] ly4 S4 _ (k + 1)
res (p + cur) (3 * ngp) (sp1 - spZ regs) (Z_to_bv 64 RT_rdpal_ra) HJcall);
[ rewrite Xa0; ewpeel; rewrite Rres; reflexivity
| exact Xa1
| exact Xa2
| clear - HNGP; lia
| clear - Hph; lia
| clear - Hpceil Hrq1 HNGP C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| rewrite EspC; clear; lia
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| rewrite FFS; unfold ESTACK; clear - Hsp1; lia
| rewrite Xgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Xtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Yra
| vm_compute; reflexivity
| intros a Ha; split; [replace a with (res + (a - res)) by (clear; lia); apply (Ares _ _ _ (a - res) Hres_in); clear - Ha Hrq1; lia | unfold ESTACK; clear - Ha Hpceil Hrq1 HNGP Hceil Hslo Hsp1 FFS C1; lia]
| apply (amem_range_of_block tfibsegs B LAWS ly4 S4 W4 _ _ res (3 * ngp) _ _ HAR4 Hres_in); clear - Hrq1 HNGP; lia
| apply (range_addressable_of_block tfibsegs B LAWS ly4 S4 W4 _ _ res (3 * ngp) _ _ (proj1 HJcall) Hres_in); clear - Hrq1 HNGP; lia
| intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly4 S4 W4 _ _ res (3 * ngp) _ _ (proj1 HJcall) Hres_in); clear - Hrq1 Hn0; lia
| split; [clear - HpR Rcur; lia|]; split; [clear - HpR Hc Rcur HNGP C1; lia|]; split;
[ intros a Ha; split; [apply (aview_some_of_apresent tfibsegs); exact (HppresB a Ha) | rewrite EspC; unfold ESTACK; clear - Ha HpR Hc Rcur HNGP Hceil Hslo Hsp1 FFS C1; lia]
| split; [clear - Hdsrc Hc Rcur HNGP; lia|];
split; [exact HsrcA|]; split; [exact HsrcR | exact HsrcH] ] ] end. }
cbv beta. intros W5_ c5_ _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Hcopy5 & Hfr5 & Hpres5 & Hio5).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr5 by (clear; lia).
clear Xa0 Xa1 Xa2 Yra Xsp Xgp Xtp EspC HppresB HsrcA HsrcR HsrcH.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJcall Kgot3 Kcell3 Kguar3 Kuar3. clear Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ5 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| eapply region_kept_aview;
[ evalE AG
| intros a Ha; apply Hfr5; clear - Ha HF4096 HFceil HFhigh HFhigh_img HdPF Hph Hph_ia Hph_img Hpceil Hrq1 Hrq2 HNGP Hceil Hslo Hshi H47 Hstk0 Hsp1 HF8lo HF8hi HF8c FFS C1 C2 C3; unfold ESTACK, SB in *; zone_lia
| exact Hpres5 ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kgot4 Kcell4 Kguar4 Kuar4 Hpres5.
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RTBspan 0x80854.
{ awrRT AG fpos F EFA4. }
unrunRD HFr Zsm Usp B70 Hsp1 UN3. clear_frames.
lazymatch type of UN3 with forall a, _ -> _ -> aview _ ?H2 ?m2 a = aview _ _ ?m1 a =>
assert (Hpalv : forall i, 0 <= i < 3 * ngp -> aview tfibsegs H2 m2 (res + i) = aview tfibsegs H2 m1 (res + i))
by (intros i Hi; apply UN3; [clear - Hi Hph Hpceil Hrq1 HSPB FFS C1; lia | subst Zsm; cbn beta; clear - Hi HdPF Hpceil Hrq1 HSPB Hsp1 FFS C1; lia]) end.
clear UN3.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
relowRT HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
let rr := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i rr HS ltac:(vm_compute; reflexivity)) as HR70; cbn [ms_mem restrict] in HR70 end.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 8 8 (SOff 10 0) p HR70 B70 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E10n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - HpR C1 Hn26; lia) ltac:(cbn; clear; lia)) as Vp.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 16 8 (SOff 11 0) n HR70 B70 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E11n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - Hn26; lia) ltac:(cbn; clear; lia)) as Vn.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 24 8 (SAlu ALU_ADD (SMd M_MUL (SOff 189 0) (SLit 3)) (SOff 193 0)) (3 * ngp + cur) HR70 B70 ltac:(cbn; tauto)
ltac:(apply denot_3x_add; [ewpeel; exact E189 | ewpeel; exact E193 | clear - Rngp; lia | clear - Rcur Hn26; lia]) ltac:(cbn; clear - Rngp Rcur Hn26; lia) ltac:(cbn; clear; lia)) as Vc.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp, Vn, Vc. clear HR70.
replace (sp1 + 16) with (sp1 + 8 + 8) in Vn by (clear; lia). replace (sp1 + 24) with (sp1 + 8 + 16) in Vc by (clear; lia).
rreg HS (24%bv : bv 5) Q24.
add_atom_win HS 191%nat (Z_to_bv 64 res) E191. add_atom_win HS 192%nat (Z_to_bv 64 r) E192.
ws_pin HS (24%bv : bv 5) (SOff 192 0) Q24 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E192; symmetry; ewpeel;
first [exact E190 | rewrite E190; exact (eq_trans (alu_or_lits 0 r ltac:(clear; lia) Rr) (f_equal (Z_to_bv 64) (Z.lor_0_l r))) | match goal with |- ?g => idtac "PIN24S" g end; fail]).
rechunk_at HS 75%nat 32 (SOff 191 0) ltac:(rewrite !sv_denot_SOff0; ewpeel; rewrite E191; symmetry; first [exact Rres | match goal with |- ?g => idtac "PAL-RECHUNK" g end; fail]).
ra_join_win HS ss_D 400%nat rt_C_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RD HS.
split; [clear - Hk0; lia|]. split; [macc|].
exists attr, gen, w16, h16, ngp, (3 * ngp + cur), r, res.
split.
{ unfold rt_gc. cbn [c_n c_sp1 c_p]. ewpeel.
repeat match goal with |- _ /\ _ => split end;
first [ exact E185 | exact E186 | exact E187 | exact E188 | exact E189 | exact E192 | exact Vp | exact Vn | exact Vc | exact Hr14 | exact Hprov | exact Hwhy
| clear - Rattr Rgen Rw Rh Rngp Rcur Rr Hc; lia ]. }
split; [ewpeel; exact E191|].
split; [clear - Hp4096 Hpceil Hrq1 HNGP C1; lia|].
right. split; [exact Hattr4|]. split; [clear - Hp4096; lia|].
split.
{ unfold rt_newblk. cbn [c_ly c_S c_regs].
split; [split; [exact Hph | apply zone2_of_app; [exact Hph_ia | exact Hph_img]]|]. split; [clear - Hpceil C1; lia|]. split; [exact Hp16|].
split; [rewrite Eab4, Eab3; reflexivity|].
split; [exact Ares | exact Tres]. }
intros Hr0. pose proof (Hcur14 Hr0) as H14.
split; [rewrite H14; clear; lia|].
destruct Hpn as [[Hn0 Hp0] | [Hnpos Hpin]]; [exfalso; pose proof (Hr14 Hr0) as Hn14; clear - Hn0 Hn14; lia|].
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0) as [He|Hne]; [exfalso; clear - Hnpos He; lia | reflexivity]).
pose proof HJcall as HJc6n. rewrite FP0 in HJc6n.
lazymatch type of Hpalv with forall i, _ -> aview _ _ ?mN _ = aview _ _ ?m5 _ =>
eapply (pal_prov_intro B _ (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) _ _ _ _ _ _ _ m5 mN res ngp LAWS HAR HJc6n Hpin) end.
+ cbn [c_p c_n]. rewrite Eab4, Eab3. apply in_app_iff. left. exact Hpin.
+ cbn [c_n]. exact Hrq.
+ clear - Rngp; lia.
+ cbn [c_n]. clear - Hc H14; lia.
+ intros i Hi. cbn [c_p]. replace (p + 14 + i) with (p + cur + i) by (rewrite H14; clear; lia). apply Hcopy5. exact Hi.
+ exact Hpalv.
-
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan 0x80854.
{ awrRT AG fpos F EFA4. }
unrunRD HFr Zsm Usp B70 Hsp1 UN3. clear_frames. clear UN3.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
relowRT HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
let rr := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i rr HS ltac:(vm_compute; reflexivity)) as HR70; cbn [ms_mem restrict] in HR70 end.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 8 8 (SOff 10 0) p HR70 B70 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E10n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - HpR C1 Hn26; lia) ltac:(cbn; clear; lia)) as Vp.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 16 8 (SOff 11 0) n HR70 B70 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E11n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - Hn26; lia) ltac:(cbn; clear; lia)) as Vn.
pose proof (field_of_region _ _ 70%nat sp1 _ _ _ _ _ 24 8 (SOff 11 0) n HR70 B70 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E11n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - Hn26; lia) ltac:(cbn; clear; lia)) as Vc.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp, Vn, Vc. clear HR70.
replace (sp1 + 16) with (sp1 + 8 + 8) in Vn by (clear; lia). replace (sp1 + 24) with (sp1 + 8 + 16) in Vc by (clear; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 18446744073709551615) (eq_trans (denot_lit_U Ev (SAlu ALU_OR (SLit 18446744073709551615) (SOff 190 0)))
(f_equal (Z_to_bv 64) (U_or_litm1 Ev (SOff 190 0)))) Q24 end.
add_atom_win HS 191%nat (Z_to_bv 64 res) E191. add_atom_win HS 192%nat (Z_to_bv 64 18446744073709551615) E192.
ws_pin HS (24%bv : bv 5) (SOff 192 0) Q24 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E192).
rechunk_at HS 75%nat 32 (SOff 191 0) ltac:(rewrite !sv_denot_SOff0; ewpeel; rewrite E191; symmetry; first [exact Rres | match goal with |- ?g => idtac "PAL-RECHUNK" g end; fail]).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let dl := eval cbv in rt_C_deads_bv in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win tfibsegs 500 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS 500%nat vals' 0%nat dl end.
norm_ss HS.
ra_join_win HS ss_D 400%nat rt_C_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RD HS.
split; [clear - Hk0; lia|]. split; [macc|].
exists attr, gen, w16, h16, ngp, n, 18446744073709551615, res.
split.
{ unfold rt_gc. cbn [c_n c_sp1 c_p]. ewpeel.
repeat match goal with |- _ /\ _ => split end;
first [ exact E185 | exact E186 | exact E187 | exact E188 | exact E189 | exact E192 | exact Vp | exact Vn | exact Vc
| intros Hz; exfalso; clear - Hz; lia
| intros _; destruct (Z.eq_dec r 0) as [Hr0|Hr0];
[ right; split; [exact Hattr4|]; split; [exact (Hprov Hr0)|]; pose proof (Hcur14 Hr0) as H14; clear - Hc H14; lia | exact (Hwhy Hr0) ]
| clear - Rattr Rgen Rw Rh Rngp Hn26; lia ]. }
split; [ewpeel; exact E191|].
split; [clear - Hp4096 Hpceil Hrq1 HNGP C1; lia|].
right. split; [exact Hattr4|]. split; [clear - Hp4096; lia|].
split.
{ unfold rt_newblk. cbn [c_ly c_S c_regs].
split; [split; [exact Hph | apply zone2_of_app; [exact Hph_ia | exact Hph_img]]|]. split; [clear - Hpceil C1; lia|]. split; [exact Hp16|].
split; [rewrite Eab4, Eab3; reflexivity|].
split; [exact Ares | exact Tres]. }
intros Hz. exfalso. clear - Hz. lia.
Qed.
Lemma rt_C : rt_from B MT FP POST ss_X (INV_X B MT) -> rt_from B MT FP POST ss_D (INV_D B MT FP) -> rt_from B MT FP POST ss_C (INV_C B MT).
Proof. exact rt_C_aux. Qed.
End c.
End b.

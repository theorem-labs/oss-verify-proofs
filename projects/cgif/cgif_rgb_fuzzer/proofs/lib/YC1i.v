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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z YC1y YC27 YC23 YC28 YC1w YC24 YC26 YC20 YC21 YC29 YC1x YC2r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Lemma denot_and_ffff : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v <= 65535 ->
sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 65535)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536. rewrite (Z.mod_small v) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win trasegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win trasegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma fl_D1_aux : fl_from B ss_X (INV_X B) -> fl_from B ss_T0 (INV_T0 B) -> fl_from B ss_D1 (INV_D1 B).
Proof.
intros RX RT0. fl_prelude.
pose proof HINV as (Hk3 & Eab3 & (gen & E180 & Rgen) & E184 & (fb & Hfb & EB) & (w & h & top & left & E446 & E447 & E448 & E449 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth)).
cbn [c_i c_s] in Hfb. cbn [c_s] in Hlw, Hth.
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
assert (HW65 : cg_W s <= 65535) by (clear - R7; lia).
assert (HH65 : cg_H s <= 65535) by (clear - R8; lia).
assert (Hw65 : w <= 65535) by (clear - Hw1 Hl0 Hlw HW65; lia). assert (Hh65 : h <= 65535) by (clear - Hh1 Ht0 Hth HH65; lia).
assert (Hwh1 : 1 <= w * h) by (clear - Hw1 Hh1; nia).
assert (HwhN : w * h <= N) by (rewrite HN; clear - Hw1 Hh1 Hl0 Hlw Ht0 Hth; nia).
assert (HWH : 1 <= w * h <= 100000000) by (clear - Hwh1 HwhN HNle; lia).
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (rewrite Eab3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hbef_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x8759c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 23 I) (Z_to_bv 64 w) (denot_and_ffff Ev 446 w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E446) ltac:(clear - Hw1 Hw65; lia)) R23;
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 h) (denot_and_ffff Ev 447 h ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E447) ltac:(clear - Hh1 Hh65; lia)) R18 end.
ws_pin HS (@BV 5 23 I) (SOff 446 0) R23 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E446).
ws_pin HS (@BV 5 10 I) (SOff 447 0) R18 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E447).
clear R23 R18. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x53104.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x875a4) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (h * w))
(denot_mul_hw Ev 447 446 h w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E447) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E446)
ltac:(clear - Hh1 Hh65; lia) ltac:(clear - Hw1 Hw65; lia)) Ra0 end.
replace (h * w) with (w * h) in Ra0 by (apply Z.mul_comm).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trasegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Htop32; lia) ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : vev S3 < VEV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk3; lia).
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340228 with (pc_wrap_malloc (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_malloc_at trasegs B LAWS tra_segs_low errno_low ML AMALLOC W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k (w * h) (sp1 - spZ regs) (Z_to_bv 64 0x875a4) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- unfold MALLOC_MAX. clear - HWH. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_FLUSH in Hlive. clear - Hlive HWH. lia.
- rewrite EspX. clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1; lia.
- rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
- exact Rra.
- apply ret_ok_even. vm_compute. reflexivity.
- exact HEVc.
- apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
- replace (pc_malloc_ra0 (as_code B)) with 0x533a4 by (rewrite HBcode; reflexivity). apply (tl_universe B TL).
apply (fl_trace_in 0x533a4 0x875a4); [exact Hctx | exact EraX | right; left; split; reflexivity]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hres by (clear; lia).
pose proof (proj1 HJ4) as HAR4.
clear HUP. assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W4) mem4 a = aview trasegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (2, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
destruct Hres as [(Hres0 & Eab4 & HK) | (Hres4096 & Eab4 & HK)].
+
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hbef3).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rewrite Hres0 in Ha04.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pin_reg' trasegs Ev ssv msv (@BV 5 10 I) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK FLBspan 0x87a18.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
rreg HS (@BV 5 19 I) Q19;
ra_join HS ss_X 520%nat fl_X_deads_bv ltac:(idtac; ra_join_val HS 520%nat 0%nat Q19 E520); fl_hand RX HS end.
split; [rewrite HEV; clear - Hk3; lia|].
split; [exists 2; split; [exact E520 | clear; lia]|].
cbn [c_ly c_S]. rewrite Eab4, Eab3. apply Permutation_refl.
+
assert (Hrq : req_size (w * h) = w * h) by (unfold req_size; destruct (Z.eqb_spec (w * h) 0); [exfalso; clear - HWH e; lia | reflexivity]).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [exfalso; clear - HWH HwhN e; lia | reflexivity]).
assert (Hres_in : In (res, w * h) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hbef3).
assert (Himg4 : In (fr_img f, N) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Himg3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (w * h) HAR4 Hres_in) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph. rewrite Hrq in Hpceil, Hppres.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR4 Hres_in) as Hph_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N HAR4 Himg4) as (_ & _ & _ & _ & Hipres4 & _). rewrite HrqN in Hipres4.
pose proof (aftok_new_block trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (w * h) HJ3 HAR4 Eab4 ltac:(clear - HWH; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, w * h) blc -> 0 <= i < w * h ->
awr_byte TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq ii Hbl Hiq. exact (awr_new_block_any trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (w * h) blc ii lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HWH; lia) Hbl ltac:(rewrite Hrq; exact Hiq)). }
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ [(res, w * h)])) by (rewrite Eab4, Eab3; apply Permutation_refl).
pose proof (sep_block_frame trasegs B LAWS ly4 S4 _ _ _ res (w * h) 2 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 2) with 256 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) g CGIF_SIZE HAR4 HPerm4 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG. rewrite Hrq in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_ptr f) FRAME_SIZE HAR4 HPerm4 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC. rewrite Hrq in HdPC.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_ptr fb) FRAME_SIZE HAR4 HPerm4 Hbef_in) as HdPB. change (req_size FRAME_SIZE) with 40 in HdPB. rewrite Hrq in HdPB.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_img f) N HAR4 HPerm4 Himg_in) as HdPI. rewrite Hrq, HrqN in HdPI.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPB Hrq; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; clear - Ha Hn Hph Hph_ia Hrq HF8lo HF8c HFceil C1 C3; ceil; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; clear - Ha Hn HdPF Hrq; lia
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPG Hrq; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPC Hrq; lia ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (@BV 5 10 I) Rres. rewrite Ha04 in Rres. symmetry in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ nx (HPTR 4) HS
ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres; unfold w64; rewrite unsigned_lit_small by (clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia);
change (2 ^ 4) with 16; clear - Hph Hpceil Hp16 HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK FLBspan 0x87608.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HSx : st_ok _ _ _ _ |- _ => rename HSx into HS end.
rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp.
rreg HS (@BV 5 18 I) R19. rreg HS (@BV 5 23 I) R23. rreg HS (@BV 5 24 I) R26. rreg HS (@BV 5 27 I) R27.
rewrite E446 in R23. rewrite E40 in R26. rewrite Rres in R27.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 20 I) (Z_to_bv 64 h) (denot_and_ffff Ev 447 h E447 ltac:(clear - Hh1 Hh65; lia)) R18;
rreg_by HS (@BV 5 19 I) (Z_to_bv 64 w) (denot_and_ffff Ev 446 w E446 ltac:(clear - Hw1 Hw65; lia)) R19s;
rreg_by HS (@BV 5 21 I) (Z_to_bv 64 (fr_img f + left)) (denot_add_atoms Ev 51 449 (fr_img f) left E51 E449 ltac:(clear - Hi4096; lia) Hl0 ltac:(rewrite HrqN in Hiceil; clear - Hiceil Hl0 Hlw Hw1 HW65 C1 HWH HwhN; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) R20;
rreg_by HS (@BV 5 22 I) (Z_to_bv 64 (top * cg_W s)) (denot_mul_hw Ev 448 40 top (cg_W s) E448 E40 ltac:(clear - Ht0 Hth Hh1 HH65; lia) ltac:(clear - HW1 HW65; lia)) R21 end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspL : spZ rg = sp1) by (unfold spZ; rewrite Rsp; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (fl_cpy B LAWS AMEMCPY (Z.to_nat h) 0 W4 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 _ ly S W mem md ly4 S4 _ fpos
res (fr_img f) N w h top left (cg_W s) (cg_H s)) end.
- rewrite Z2Nat.id by (clear - Hh1; lia). clear; lia.
- clear - Hh1; lia.
- exact Hw1. - exact Hl0. - exact Hlw. - exact Hh1. - exact Ht0. - exact Hth.
- clear - HW1 HW65; lia. - exact HH65. - symmetry; exact HN. - exact HNle.
- exact HJ4.
- exact Hres_in. - exact Himg4.
- intros blc lyq ownq a Hbl Ha. replace a with (res + (a - res)) by (clear; lia). apply (Ares blc lyq ownq (a - res) Hbl). clear - Ha; lia.
- rewrite Hrq, HrqN. clear - HdPI; lia.
- exact EspL. - exact Hsp1. - exact Hsp1al16.
- rewrite Rgp. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
- rewrite Rtp. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
- rewrite R18. f_equal. clear; lia.
- exact R19.
- exact R20.
- rewrite R21. f_equal. clear; lia.
- exact R23. - exact R26.
- rewrite R27. unfold w64. f_equal. clear; lia.
- exact R19s. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & Hout5 & Hpres5).
clear Rsp Rgp Rtp R18 R19 R19s R20 R21 R23 R26 R27 EspL.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch_keep HS kk regs5 (mrestrict (w_H W4) mem5) CPY_CLOB 0x8762c [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= res \/ res + w * h <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r) /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= sp1 - ESTACK \/ sp1 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?RF, ?E70, ?E88; rewrite ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 12%nat), ?(AG 32%nat) by lia; rewrite ?Usp, ?E10, ?E11, ?E12, ?E32;
rewrite ?unsigned_lit_small by (unfold SB; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 C1 C3 HFceil HFhigh HF8lo HF8hi Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, FRAME_SIZE, SB, ESTACK;
clear - HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hshi H47 Hsp1 Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2 Hbceil C1 C2 C3 C4 C5 FFS Hp4096 Hph Hph_img Hph_ia Hrq Hpceil HWH HdPG HdPC HdPB HdPF;
unbox; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; first [zone_lia | match goal with |- ?g => idtac "HRK-FAIL" g; fail end]
| specialize (HS2 HK5 (regions_kept_out2 Ev (w_H W4) (ms_mem msX) mem5 res (res + w * h) (sp1 - ESTACK) sp1 _ Hout5 Hpres5 HRK)) ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
lazymatch type of HUP with forall a, _ -> aview _ _ ?m4 a = _ =>
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W4) mem5 a = aview trasegs (w_H W) mem a)
by (intros a Ha; rewrite (Hout5 a); [apply HUP; exact Ha | clear - Ha Hbot Hslo Hceil Hstk0 C1 FFS; lia | clear - Ha Hpceil HWH C1 Hceil Hslo Hstk0 FFS; lia | clear - Ha Hsp1; unfold ESTACK; lia]) end.
clear HUP. rename HUP5 into HUP.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
clear Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ5 Kgot4 Kcell4 Kguar4 Kuar4.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK FLBspan 0x87674.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (23%bv : bv 5) Q23; rreg HS (27%bv : bv 5) Q27;
rewrite Rres in Q23; rewrite E447 in Q27;
add_atom_win HS 238%nat (Z_to_bv 64 w) E238;
rechunk_off HS 70%nat 168 (SOff 238 0) ltac:(rewrite !sv_denot_SOff0; rewrite E238; rewrite ?ew_havoc_above by nat_side; first [rewrite E446; reflexivity | match goal with |- ?g => idtac "RC168" g; fail end]) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom_win HS 239%nat (Z_to_bv 64 left) E239;
rechunk_off HS 70%nat 144 (SOff 239 0) ltac:(rewrite !sv_denot_SOff0; rewrite E239; rewrite ?ew_havoc_above by nat_side; first [rewrite E449; reflexivity | match goal with |- ?g => idtac "RC144" g; fail end]) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom_win HS 240%nat (Z_to_bv 64 top) E240;
rechunk_off HS 70%nat 152 (SOff 240 0) ltac:(rewrite !sv_denot_SOff0; rewrite E240; rewrite ?ew_havoc_above by nat_side; first [rewrite E448; reflexivity | match goal with |- ?g => idtac "RC152" g; fail end]) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join_win HS ss_T0 241%nat fl_T0_deads_bv ltac:(idtac;
ra_join_val HS 241%nat 0%nat Q23 E241; ra_join_val HS 241%nat 2%nat Q27 E243;
ra_join_fact HS 238%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E238; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hw1 Hw65; lia); clear - Hw1 Hw65; lia);
ra_join_fact HS 239%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E239; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hl0 Hlw Hw1 HW65; lia); clear - Hl0 Hlw Hw1 HW65; lia);
ra_join_fact HS 240%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E240; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Ht0 Hth Hh1 HH65; lia); clear - Ht0 Hth Hh1 HH65; lia);
ra_join_fact HS 243%nat (mkAF 1 65535 0) ltac:(rewrite E243; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hh1 Hh65; lia); clear - Hh1 Hh65; lia));
fl_hand RT0 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; repeat (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists res, w, h, top, left. cbn [c_s c_ly c_S c_regs c_f].
split; [rewrite E241; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E238; reflexivity|].
split; [rewrite E243; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E240; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E239; reflexivity|].
split; [clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
right. split; [clear - Hph C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [first [clear - Hk3; lia | match goal with |- ?g => idtac "KGOAL" g end]|].
unfold fl_tmpblk, fl_FP. cbn [c_ly c_S c_regs c_f c_s].
split; [split; [exact Hph | rewrite <- Hrq; exact (zone2_of_app _ _ Hph_ia Hph_img)]|]. split; [clear - Hpceil HWH C1; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [exact Hp16|].
split; [first [rewrite Eab4, Eab3; reflexivity | match goal with |- ?g => idtac "D-ABL" g end]|].
split; [exact Ares | exact Tres].
Qed.
Lemma fl_D1 : fl_from B ss_X (INV_X B) -> fl_from B ss_T0 (INV_T0 B) -> fl_from B ss_D1 (INV_D1 B).
Proof. exact fl_D1_aux. Qed.
End c.
End b.

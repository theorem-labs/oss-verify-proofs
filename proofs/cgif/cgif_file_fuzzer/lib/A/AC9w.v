(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACan ACag.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Variable CTXL : list (list Z).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Hypothesis HXM : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xm_lzw XN N idl + 2 * mo_free MT <= xm_rawadd XN N.
Hypothesis HXN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xn_lzw XN N idl + 2 * mo_free MT <= xn_rawadd XN N.
Hypothesis HXMN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> 0 <= xn_lzw XN N idl <= xm_lzw XN N idl.
Hypothesis TLZWX : tlzw_specX SEGS B MT XN (BASE + AF_asan3_LZW_GenerateStream) CTXL pa_relro_lo pa_relro_hi.
Hypothesis HCTXL1 : forall l, In l CTX -> In ((BASE + 0xaf4) :: l) CTXL.
Hypothesis HCTXL2 : forall l, In l CTX -> In ((BASE + 0xd94) :: l) CTXL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma ra_PX_aux : ra_fromX0 KS MT XN B CTX ss_T0X (INV_T0X MT XN B) -> ra_fromX0 KS MT XN B CTX ss_TfX (INV_TfX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_PX (INV_PX MT B).
Proof.
intros RT0 RTF. ra_preludeX.
pose proof HINV as ((Hk3 & Eab3 & K1 & EK & HK1r & HK1s) & HXC & (((E661 & HXK) & EICL) & EIDL & EICL2) & HIL & MLE0).
xk1 HXK EK HK1r HK1v.
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x1444.
all: try (oblFAX HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem SEGS Ex ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of HRstk with region_ok _ _ _ ?rfull =>
let rlo := eval vm_compute in (trim_region rfull (-320) (-120)) in
pose proof (st_ok_pi_add_region Ev _ _ rlo HS eq_refl
ltac:(apply (region_ok_sub SEGS Ev _ rfull); [subregion_tac | cbn; lia | exact HRstk])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRstk; rename HS3 into HS end | st_ok _ ?Ev _ _ =>
lazymatch type of HRstk with region_ok _ _ _ ?rfull =>
let rlo := eval vm_compute in (trim_region rfull (-320) (-120)) in
pose proof (st_ok_pi_add_region Ev _ _ rlo HS eq_refl
ltac:(apply (region_ok_sub SEGS Ev _ rfull); [subregion_tac | cbn; lia | exact HRstk])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRstk; rename HS3 into HS end  end.
norm_ss HS.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3. prreg HS (14%bv : bv 5) Ra4.
rewrite E42 in Ra2.
fact_of HS 814%nat F355. fact_of HS 815%nat F356.
set (idl := bv_unsigned (ew E 814)) in F355. set (icl := bv_unsigned (ew E 815)) in F356.
assert (E814 : ew E 814 = Z_to_bv 64 idl) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (E815 : ew E 815 = Z_to_bv 64 icl) by (symmetry; apply Z_to_bv_bv_unsigned).
lazymatch goal with |- SRr _ _ _ (ra_postX _ _ _ _ ?cxv _) =>
pose proof (rx_iclen_bounds cxv) as Hiclb;
assert (Hicl : icl = rx_iclen cxv) by (subst icl; rewrite EICL2; apply unsigned_lit_small; clear - Hiclb; lia);
assert (Hidl : idl = rx_idl cxv) by (subst idl; rewrite EIDL; apply unsigned_lit_small; unfold rx_idl; clear - Hiclb;
split; [apply Z.pow_nonneg; lia | apply (Z.le_lt_trans _ (2 ^ 17)); [apply Z.pow_le_mono_r; lia | reflexivity]]) end.
clear EIDL EICL2.
rewrite E814 in Ra3. rewrite E815 in Ra4.
assert (HnP31 : h * w < 2 ^ 31) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mulw_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia) HnP31) Ra1 | st_ok _ ?Ev _ _ =>
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mulw_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia) HnP31) Ra1  end.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (Hchne : ch <> []) by (intros Hn; pose proof (HDEEP _ Hctx) as Hdeep; rewrite Hn in Hdeep; cbn in Hdeep; clear - Hdeep; lia).
pose proof Hch as Hch'. destruct Hch' as [(_ & Hn) | (Qs0lo & Qs0hi & Qs0al & _ & _)]; [exfalso; exact (Hchne Hn)|].
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base_lo rs 2%nat (-104) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear - PBASE PBLO; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base_lo rs 2%nat (-104) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear - PBASE PBLO; lia))
| ]  end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (TLZWX TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(spZ regs - 120) (h * w) img idl icl img Nimg ((spZ regs, raZ regs, s0Z regs) :: ch) IMG HJ3) as CALL end.
unfold cfg_at in CALL. change (w64 (BASE + AF_asan3_LZW_GenerateStream)) with (Z_to_bv 64 (BASE + 0x1444)) in CALL. apply CALL; clear CALL.
- exact (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROD).
- rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia). clear - PBASE PBLO; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- rewrite Ra0. unfold w64. f_equal. rewrite Usp3. clear; lia.
- exact Ra1.
- exact Ra2.
- exact Ra3.
- exact Ra4.
- unfold spZ at 1. unfold s0Z. rewrite Rsp, Rs0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia.
rewrite Usp3, !unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). replace (spZ regs + -320) with (spZ regs - 320) by (clear - PBASE PBLO; lia). exact Hch1.
- unfold raZ at 1. rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia). cbn [spine map fst snd]. apply HCTXL1. exact Hctx.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia).
pose proof (Z.div_mod (spZ regs) 32 ltac:(clear - PBASE PBLO; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) + -320) with ((2 * (spZ regs / 32) - 20) * 16) by (clear - PBASE PBLO; lia). apply Z_mod_mult.
- unfold spZ at 2. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). rewrite FFS. unfold LZW_TSTK, ASTACK. clear; lia.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- pose proof (Z.div_mod (spZ regs) 32 ltac:(clear - PBASE PBLO; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) - 120) with ((4 * (spZ regs / 32) - 15) * 8) by (clear - PBASE PBLO; lia). apply Z_mod_mult.
- left. unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- clear - Hceil Hslo Hstk0 FFS C1. lia.
- clear - Hshi H47. lia.
- intros a Ha. split; [left; rewrite FFS; clear - Ha; lia | apply Hpres3'; rewrite FFS; clear - Ha; lia].
- right. destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SL & SH & _). rewrite SL, SH. clear - Hslo Hshi FFS. lia.
- clear - HnP HnP1. lia.
- clear - F355. lia.
- clear - F356. lia.
- rewrite Eab3. exact Himg_in.
- clear; lia.
- pose proof (req_size_pos Nimg ltac:(clear - HnPN HnP1; lia)) as [_ Hq]. clear - HnPN Hq. lia.
-
assert (HPi : Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (img, Nimg) :: (g, CGIF_SIZE) :: rest)) by (eapply Permutation_trans; [exact HPerm|]; apply perm_skip; apply perm_swap).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (raw, RAW_SIZE) (img, Nimg) _ HAR HPi) as Sri.
unfold zdisjoint, block_rng in Sri. cbn [fst snd] in Sri. change (req_size RAW_SIZE) with 48 in Sri.
pose proof (req_size_pos Nimg ltac:(clear - HnPN HnP1; lia)) as [_ Hq]. xunwrap HIMGlen.
eapply (garr8_journal_block_x _ B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ img Nimg img IMG HJ3);
[exact Himg_in | rewrite Eab3; exact Himg_in | clear; lia | clear - HIMGlen HnPN Hq; lia | | exact HIMG].
intros a Ha (r & [<- | []] & Hr). cbn [fst snd] in Hr. clear - Ha Hr Sri HIMGlen HnPN Hq. lia.
- xunwrap HIMGlen. clear - HIMGlen. lia.
- rewrite HEV in Hev. unfold LZW_EV. clear - Hnev3 Hk3 Hev. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_RAWADD in Hlive. clear - Hlive. lia.
-
assert (Hidlr : 2 <= idl <= 256) by (clear - F355; lia).
eapply (mok_station MT S S3 _ 0); [exact MLAW | exact HMOK | exact MLE0 | pose proof (HXMN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr); rewrite (Z.mul_comm h w); clear - H; lia |].
pose proof (HXM (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Hb. pose proof (mo_malloc_nonneg MT MLAW (w * h) ltac:(clear - Hw Hh; nia)). pose proof (mo_free_nonneg MT MLAW).
rewrite (Z.mul_comm h w). clear - Hb H H0. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & MLE4 & Hres).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = spZ regs - 320) by (unfold spZ at 1; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear; lia) end.
rewrite EspX in Hres. rewrite Rra.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1 Ra2 Ra3 Ra4 Vra Vs0 Hch1 Hchne Qs0lo Qs0hi Qs0al Qtop64 Qra Qs0 Qal8 HLY3 Hnev3 Hpres3'.
pose proof (proj1 HJ4) as HAR4.
pose proof HJ4 as (_ & HLY4 & _ & _ & _ & _ & Hnev4 & _ & _ & _ & _ & _ & _ & Hpres4' & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR HLY4) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (1, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
frame_pres HJ4 Hfin4 EFA4 F HFpres4 HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct Hres as [(Hres0 & bb & Lbb & M & HPerm4 & Hbb4096 & HM & HM2 & Abb & Tbb & Vbb & VM & HVOK & HK) | (Hres5 & HPerm4 & HVNONE & HK & HpR)].
+
rewrite Eab3 in HPerm4.
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; right; exact Hraw_in).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; right; exact Hing).
assert (Hbb4 : In (bb, Lbb) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; left; reflexivity).
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR4 ltac:(eapply Permutation_trans; [exact HPerm4 | apply perm_skip; exact HPerm])) as HdBR.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bb, Lbb) (g, CGIF_SIZE) _ HAR4
ltac:(eapply Permutation_trans; [exact HPerm4 | apply perm_skip; eapply Permutation_trans; [exact HPerm | apply perm_swap]])) as HdBG.
unfold zdisjoint, block_rng in HdBR, HdBG. cbn [fst snd] in HdBR, HdBG. change (req_size RAW_SIZE) with 48 in HdBR. change (req_size CGIF_SIZE) with 96 in HdBG.
box HdBR. box HdBG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR4 Hraw4) as (_ & _ & _ & _ & Hrpres4 & _). change (req_size RAW_SIZE) with 48 in Hrpres4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR4 Hbb4) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR4 Hbb4) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
destruct HVOK as (out & Hls & HGout & HMout).
assert (HML : xfacts (Z.of_nat (length out) <= req_size Lbb)) by (apply xfacts_i; clear - HMout HM HLbb; lia).
xbb_facts Hbb4 HAR4 Hfin4 EFA4 Hbb4096 Hbbceil Hbbh_ia HdBR XBB Hpf_in.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ keptLZW HK AG Hpres4' Hfin3 HfinS3 EFA3 F HFpres4 Hraw3 Hing3 Hrpres4
ltac:(intros a Ha Hx; clear - Ha Hx HdBR; unbox; lia) ltac:(intros a Ha Hx; clear - Ha Hx HdBG; unbox; lia)
Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1059 Ev ssv msv [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] HS ltac:(vm_compute; reflexivity)) as HS3 | st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1059 Ev ssv msv [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] HS ltac:(vm_compute; reflexivity)) as HS3  end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E1059 : ew Ev 1059 = Z_to_bv 64 bb) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E1060 : ew Ev 1060 = Z_to_bv 64 (M mod 2 ^ 32)) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev _ _ =>
assert (E1059 : ew Ev 1059 = Z_to_bv 64 bb) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E1060 : ew Ev 1060 = Z_to_bv 64 (M mod 2 ^ 32)) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 2%nat) (-120) (-104) (-120) (-104) [YP09.mkChunk (-120) (CVal 8 (SOff 1059 0)); YP09.mkChunk (-112) (CVal 4 (SOff 1060 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply Hpres4'; rewrite FFS; lia
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-120) 8 _ bb);
[cbn [sv_denot]; rewrite E1059, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (spZ regs + -120) with (spZ regs - 120) by lia; exact Vbb]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-112) 4 _ (M mod 2 ^ 32));
[cbn [sv_denot]; rewrite E1060, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)); zside | zside
| replace (spZ regs + -112) with (spZ regs - 120 + 8) by lia; apply val_mem_mod4; exact VM]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 2%nat) (-120) (-104) (-120) (-104) [YP09.mkChunk (-120) (CVal 8 (SOff 1059 0)); YP09.mkChunk (-112) (CVal 4 (SOff 1060 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply Hpres4'; rewrite FFS; lia
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-120) 8 _ bb);
[cbn [sv_denot]; rewrite E1059, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (spZ regs + -120) with (spZ regs - 120) by lia; exact Vbb]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-112) 4 _ (M mod 2 ^ 32));
[cbn [sv_denot]; rewrite E1060, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)); zside | zside
| replace (spZ regs + -112) with (spZ regs - 120 + 8) by lia; apply val_mem_mod4; exact VM]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
rewrite Hres0 in Ha04.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_pin_reg' Ev ssv msv (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3 | st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_pin_reg' Ev ssv msv (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3  end.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ4 SHOK RABspan 0xdb8; [awrRA AG fpos F EFA4|].
xblk_stretch HFr HGout.
clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_T0X 1061%nat ra_deads_T0 ltac:(idtac).
ra_handX RT0 HS.
split; [| split; [exact HXC | split; [| split]]].
{ split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists bb, Lbb, M. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E1059|]. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E1060|].
split; [exact HPerm4|]. split; [exact Hbb4096|]. split; [exact HM|]. split; [exact Abb | exact Tbb]. }
{   split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1v Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{   unfold rx_pix. cbn [c_fattr c_w c_h]. rewrite HIL, <- Hidl, <- Hicl. exists out. split; [exact Hls|].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E1059, E1060. rewrite (Z.mod_small M) by (clear - HM HM2 HnP; lia).
rewrite !unsigned_lit_small by (first [clear - HM HM2 HnP; lia | clear - Hbb4096 Hbbceil HLbb HM C1; lia]).
split; [exact HGout | split; [exact HMout | clear - HM2 HMout; nia]]. }
{   exists (xn_lzw XN (h * w) idl). split; [exact (mle_station MT _ _ _ _ _ MLAW MLE0 MLE4) || (pose proof (mle_station MT _ _ _ _ _ MLAW MLE0 MLE4) as Q; rewrite Z.add_0_l in Q; exact Q)|].
assert (Hidlr : 2 <= idl <= 256) by (clear - F355; lia).
pose proof (HXMN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q1. pose proof (HXM (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q2. pose proof (HXN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q3.
pose proof (mo_malloc_nonneg MT MLAW (w * h) ltac:(clear - Hw Hh; nia)) as Q4. pose proof (mo_free_nonneg MT MLAW) as Q5.
cbn [c_w c_h]. rewrite (Z.mul_comm h w). clear - Q1 Q2 Q3 Q4 Q5. lia. }
+
rewrite Eab3 in HPerm4.
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hraw_in).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hing).
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR4 Hraw4) as (_ & _ & _ & _ & Hrpres4 & _). change (req_size RAW_SIZE) with 48 in Hrpres4.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ keptLZW HK AG Hpres4' Hfin3 HfinS3 EFA3 F HFpres4 Hraw3 Hing3 Hrpres4
ltac:(intros a Ha Hx; exact Hx) ltac:(intros a Ha Hx; exact Hx)
Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
prreg HS (10%bv : bv 5) Qa0. rewrite Ha04 in Qa0. symmetry in Qa0. unfold w64 in Qa0.
lazymatch type of Qa0 with ew ?Ev ?n = _ =>
pose proof (st_ok_pi_add_fact Ev _ _ n (mkAF 2 5 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Qa0, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Hres5; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ4 SHOK RABspan 0xdb8; [awrRA AG fpos F EFA4|]. clear_frames.
fact_of HS 820%nat F361.
prreg HS (21%bv : bv 5) Qs5. (first [rewrite Qa0 in Qs5 | rewrite <- Qa0 in Qs5]); rewrite Hres5 in Qs5.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_TfX 1061%nat ra_deads_Tf
ltac:(idtac; ra_join_val HS 1061%nat 16%nat Qs5 Eres;
ra_join_fact HS 1077%nat (mkAF 2 5 0) ltac:(rewrite Eres, unsigned_lit_small by (clear; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear; lia)).
ra_handX RTF HS.
split; [| split; [exact HXC | split; [| split]]].
{ split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exact HPerm4. }
{   exact Eres. }
{ unfold rx_pix. cbn [c_fattr c_w]. rewrite HIL, <- Hidl, <- Hicl. exact HVNONE. }
{ exists (xn_lzw XN (h * w) idl). split; [exact (mle_station MT _ _ _ _ _ MLAW MLE0 MLE4) || (pose proof (mle_station MT _ _ _ _ _ MLAW MLE0 MLE4) as Q; rewrite Z.add_0_l in Q; exact Q)|].
assert (Hidlr : 2 <= idl <= 256) by (clear - F355; lia).
pose proof (HXMN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q1. pose proof (HXM (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q2. pose proof (HXN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q3.
pose proof (mo_malloc_nonneg MT MLAW (w * h) ltac:(clear - Hw Hh; nia)) as Q4. pose proof (mo_free_nonneg MT MLAW) as Q5.
cbn [c_w c_h]. rewrite (Z.mul_comm h w). clear - Q1 Q2 Q3 Q4 Q5. lia. }
Qed.
Lemma ra_PX : ra_fromX0 KS MT XN B CTX ss_T0X (INV_T0X MT XN B) -> ra_fromX0 KS MT XN B CTX ss_TfX (INV_TfX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_PX (INV_PX MT B).
Proof. exact ra_PX_aux. Qed.
End e.
End d.
End b.

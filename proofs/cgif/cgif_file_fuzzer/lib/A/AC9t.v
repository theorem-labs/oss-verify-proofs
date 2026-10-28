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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACal ACan ACag ACac.
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
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
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
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis HTR : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0xda0) \/ (pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0x10ac) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0xb08)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma ra_IX_aux : ra_fromX0 KS MT XN B CTX ss_LX (INV_LX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_IX (INV_IX MT B).
Proof.
intros RL. ra_preludeX.
pose proof HINV as ((Hk3 & Eab3 & K1 & EK & HK1r & HK1s) & HXC & (((E661 & HXK) & EICL) & EIDL & EICL2) & HIL & MLE0).
xk1 HXK EK HK1r HK1v.
lazymatch type of EIDL with _ = Z_to_bv 64 ?iv => pose proof (rx_idl_range _ : 4 <= iv <= 2 ^ 17) as Hidlr17 end.
fact_of HS 814%nat Fidl. rewrite EIDL, unsigned_lit_small in Fidl by (clear - Hidlr17; lia).
xnums_for Fidl QM QN QMN.
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. clear HF HFr HG.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
assert (HnP32 : h * w < 2 ^ 32) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mul_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia)) Ra0 | st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mul_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia)) Ra0  end.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (Hchne : ch <> []) by (intros Hn; pose proof (HDEEP _ Hctx) as Hdeep; rewrite Hn in Hdeep; cbn in Hdeep; clear - Hdeep; lia).
pose proof Hch as Hch'. destruct Hch' as [(_ & Hn) | (Qs0lo & Qs0hi & Qs0al & _ & _)]; [exfalso; exact (Hchne Hn)|].
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
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
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear - PBASE PBLO; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
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
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear - PBASE PBLO; lia))
| ]  end.
pmkst HS.
ppcs.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (AMALLOC4 W3 (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)]
ly3 S3 mdX k (h * w) (-320) (Z_to_bv 64 (BASE + 0xb08)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- rewrite HMM. clear - HnP HnP1. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_RAWADD in Hlive. clear - Hlive HnP. lia.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- reflexivity. - clear; lia. - rewrite FFS. unfold ASTACK. clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite HEV in Hev. clear - Hnev3 Hk3 Hev. lia.
- apply (achain_chain_pre ly3 _ (spZ regs - 320) (spZ regs) _ _ Hch1);
[ unfold spZ at 1 2; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear - Hceil Hslo Hstk0 FFS C1; lia
| unfold s0Z; rewrite Rs0; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp3
| unfold raZ; rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia); clear - PBASE PBLO; lia ].
- apply (HTR (pc_malloc_ra0 (as_code B)) (BASE + 0xb08)); [exact Hctx | unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE PBLO; lia | right; right; split; reflexivity].
-
eapply (mok_station MT S S3 _ 0); [exact MLAW | exact HMOK | exact MLE0 | apply (mo_malloc_nonneg MT MLAW); clear - HnP1; lia |].
pose proof (mo_free_nonneg MT MLAW) as Hf0. rewrite (Z.mul_comm h w). clear - QM QMN Hf0. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hnz4 & Eab4' & HK4' & MLE4).
mresX Hnz4 Eab4' HK4' Hres. clear Eab4' HK4'.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 Hchne Qs0lo Qs0hi Qs0al Qtop64 Qra Qs0 Qal8.
unfold ASTACK in Hres. replace (spZ regs + -320 - 16384) with (spZ regs - 16704) in Hres by lia. replace (spZ regs + -320) with (spZ regs - 320) in Hres by lia.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (1, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
frame_pres HJ4 Hfin4 EFA4 F HFp4 HFSp4.
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct Hres as [(Hres0 & Eab4 & HK) | (Hres4096 & Eab4 & HK)].
-   exfalso. clear - Hres0 Hnz4. lia.
-
assert (Hrq : req_size (h * w) = h * w) by (unfold req_size; destruct (Z.eqb_spec (h * w) 0); [exfalso; clear - HnP1 e; lia | reflexivity]).
assert (Hres_in : In (res, h * w) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hraw3).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hing3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (h * w) HAR4 Hres_in) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & Hnpres & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR4 Hres_in) as Hnh_img.
rewrite Hrq in Hnceil, Hnpres, Hnh_ia.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (h * w) HJ3 HAR4 Eab4 ltac:(clear - HnP1; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, h * w) blc -> 0 <= i < h * w ->
awr_byte TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (h * w) blc i lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HnP1; lia) Hbl ltac:(rewrite Hrq; exact Hi)). }
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ res (h * w) 1 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ res (h * w) cid pos HAR4 Hres_in HfinS4) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite Hrq in HdPC. rewrite EFA4 in HdPC.
assert (HPerm4 : Permutation (ablocks B ly4 S4) ((res, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)).
{ rewrite Eab4, Eab3. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]. apply perm_skip. exact HPerm. }
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (res, h * w) (raw, RAW_SIZE) _ HAR4 HPerm4) as HdPR.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (res, h * w) (g, CGIF_SIZE) _ HAR4 ltac:(eapply Permutation_trans; [exact HPerm4 | apply perm_skip; apply perm_swap])) as HdPG.
unfold zdisjoint, block_rng in HdPR, HdPG. cbn [fst snd] in HdPR, HdPG. rewrite Hrq in HdPR, HdPG.
change (req_size RAW_SIZE) with 48 in HdPR. change (req_size CGIF_SIZE) with 96 in HdPG.
box HdPF. box HdPC. box HdPR. box HdPG.
assert (HEr : forall a, F <= a < F + 128 -> ~ (res <= a < res + req_size (h * w))) by (rewrite Hrq; intros a Ha; clear - Ha HdPF HnP1; unbox; lia).
assert (HErS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ (res <= a < res + req_size (h * w))) by (rewrite Hrq; intros a Ha; clear - Ha Hnh Hnh_ia Hrq HF8lo HFceil HFq HF8 C1 C3; unfold SB in *; zone_lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
ltac:(idtac; first [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj SEGS _); [exact HK | evalE AG | exact HfinS3 | rwEFA; lia | rwEFA; lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPC Hflo Hfhi; unbox; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | evalE AG | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPG; unbox; lia] end
| keptRA HK HJ4 AG Usp E11 E32 HfinS3 Hing3 Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| keptFA2 HK AG RF E529 Hfin3 HFp4 HFSp4 HEr HErS F
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact HK | exact HAR4 | exact Hraw4 | evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPR; unbox; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 859 Ev ssv msv [Z_to_bv 64 res] HS ltac:(vm_compute; reflexivity)) as HS3 | st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 859 Ev ssv msv [Z_to_bv 64 res] HS ltac:(vm_compute; reflexivity)) as HS3  end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E859 : ew Ev 859 = Z_to_bv 64 res) by (rewrite HEv; exact (ew_havoc_new _ 859 [Z_to_bv 64 res] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev _ _ =>
assert (E859 : ew Ev 859 = Z_to_bv 64 res) by (rewrite HEv; exact (ew_havoc_new _ 859 [Z_to_bv 64 res] 0 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (10%bv : bv 5) (SOff 859 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E859, Z.add_0_r, Ha04; unfold w64; rewrite unsigned_lit_small by (clear - Hn4096 Hnceil C1 HnP1; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS Ev ssx msx (10%bv : bv 5) (SOff 859 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E859, Z.add_0_r, Ha04; unfold w64; rewrite unsigned_lit_small by (clear - Hn4096 Hnceil C1 HnP1; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 859%nat (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E859, unsigned_lit_small by (clear - Hn4096 Hnceil C1 HnP1; lia); change (2 ^ 4) with 16; clear - Hn16 Hnh Hnceil HnP1 C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 859%nat (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E859, unsigned_lit_small by (clear - Hn4096 Hnceil C1 HnP1; lia); change (2 ^ 4) with 16; clear - Hn16 Hnh Hnceil HnP1 C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ4 SHOK RABspan 0xb64.
all: try (oblFAX HJ4 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA4.
clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_LX 861%nat ra_deads_L ltac:(idtac).
ra_handX RL HS.
split; [| split; [exact HXC | split; [| split; [exact HIL|]]]].
2: {
split; [split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); pose proof HK1v as HK1w; unfold xfacts in HK1w; rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]|].
split; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); [exact EIDL | exact EICL2]. }
2: {   exists (0 + mo_malloc MT (h * w)). split; [exact (mle_station MT _ _ _ _ _ MLAW MLE0 MLE4)|].
cbn [c_w c_h].
pose proof (mo_malloc_nonneg MT MLAW (w * h) ltac:(clear - Hw Hh; nia)) as Q4. pose proof (mo_free_nonneg MT MLAW) as Q5.
rewrite (Z.mul_comm h w). clear - QM QN QMN Q4 Q5. lia. }
split; [clear - Hk3; lia|].
split; [exists K1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists res. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E859|]. split; [exact Hres4096|].
split; [rewrite Eab4, Eab3; reflexivity|]. split; [exact Ares | exact Tres].
Qed.
Lemma ra_IX : ra_fromX0 KS MT XN B CTX ss_LX (INV_LX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_IX (INV_IX MT B).
Proof. exact ra_IX_aux. Qed.
End f.
End d.
End b.

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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw YCgl YChb YChm YChi YChj YChk YChn YChg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis TLZW : tlzw_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_P_aux : ra_from B ss_T0 (INV_T0 B) -> ra_from B ss_Tf (INV_Tf B) -> ra_from B ss_P (INV_D B).
Proof.
intros RT0 RTF. ra_prelude.
pose proof HINV as (Hk3 & Eab3 & K1 & EK & HK1r & HK1s).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan A_LZW.
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem trbsegs Ex ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HRstk with region_ok _ _ _ ?rfull =>
let rlo := eval vm_compute in (trim_region rfull (-320) (-120)) in
pose proof (ast_ok_add_region trbsegs Ev _ _ rlo HS eq_refl
ltac:(apply (region_ok_sub trbsegs Ev _ rfull); [subregion_tac | cbn; lia | exact HRstk])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRstk; rename HS3 into HS end end.
norm_ss HS.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (12%bv : bv 5) Ra2. rreg HS (13%bv : bv 5) Ra3. rreg HS (14%bv : bv 5) Ra4.
rewrite E42 in Ra2.
fact_of HS 355%nat F355. fact_of HS 356%nat F356.
set (idl := bv_unsigned (ew E 355)) in F355. set (icl := bv_unsigned (ew E 356)) in F356.
assert (E355 : ew E 355 = Z_to_bv 64 idl) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (E356 : ew E 356 = Z_to_bv 64 icl) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite E355 in Ra3. rewrite E356 in Ra4.
assert (HnP31 : h * w < 2 ^ 31) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mulw_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia) HnP31) Ra1 end.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Hchne : ch <> []) by (intros Hn; rewrite Hn in Hctx; cbn in Hctx; clear - Hctx; intuition discriminate).
pose proof Hch as Hch'. destruct Hch' as [(_ & Hn) | (Qs0lo & Qs0hi & Qs0al & _ & _)]; [exfalso; exact (Hchne Hn)|].
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base_lo rs 2%nat (-104) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trbsegs (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear; lia))
| ] end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (TLZW TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(spZ regs - 120) (h * w) img idl icl img Nimg ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) as CALL end.
unfold cfg_at in CALL. change (w64 A_LZW) with (Z_to_bv 64 566356) in CALL. apply CALL; clear CALL.
- eapply arodata_ok_journal; [exact HJ3 | exact HROD].
- rewrite Rra. apply ret_ok_even. vm_compute. reflexivity.
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear; lia). clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- rewrite Ra0. unfold w64. f_equal. rewrite Usp3. clear; lia.
- exact Ra1.
- exact Ra2.
- exact Ra3.
- exact Ra4.
- unfold spZ at 1. unfold s0Z. rewrite Rsp, Rs0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia.
rewrite Usp3, !unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). replace (spZ regs + -320) with (spZ regs - 320) by (clear; lia). exact Hch1.
- unfold raZ at 1. rewrite Rra, unsigned_lit_small by (clear; lia). cbn [spine map fst snd]. apply ctx_lzw1. exact Hctx.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia).
pose proof (Z.div_mod (spZ regs) 32 ltac:(clear; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) + -320) with ((2 * (spZ regs / 32) - 20) * 16) by (clear; lia). apply Z_mod_mult.
- unfold spZ at 2. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). rewrite FFS. unfold LZW_TSTK, ASTACK. clear; lia.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- pose proof (Z.div_mod (spZ regs) 32 ltac:(clear; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) - 120) with ((4 * (spZ regs / 32) - 15) * 8) by (clear; lia). apply Z_mod_mult.
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
- rewrite HEV in Hev. unfold LZW_EV. clear - Hnev3 Hk3 Hev. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_RAWADD in Hlive. clear - Hlive. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres).
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
destruct Hres as [(Hres0 & bb & Lbb & M & HPerm4 & Hbb4096 & HM & Abb & Tbb & Vbb & VM & HK) | (Hres25 & HPerm4 & HK & HpR)].
+
rewrite Eab3 in HPerm4.
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; right; exact Hraw_in).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; right; exact Hing).
assert (Hbb4 : In (bb, Lbb) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; left; reflexivity).
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR4 ltac:(eapply Permutation_trans; [exact HPerm4 | apply perm_skip; exact HPerm])) as HdBR.
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ (bb, Lbb) (g, CGIF_SIZE) _ HAR4
ltac:(eapply Permutation_trans; [exact HPerm4 | apply perm_skip; eapply Permutation_trans; [exact HPerm | apply perm_swap]])) as HdBG.
unfold zdisjoint, block_rng in HdBR, HdBG. cbn [fst snd] in HdBR, HdBG. change (req_size RAW_SIZE) with 48 in HdBR. change (req_size CGIF_SIZE) with 96 in HdBG.
box HdBR. box HdBG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR4 Hraw4) as (_ & _ & _ & _ & Hrpres4 & _). change (req_size RAW_SIZE) with 48 in Hrpres4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR4 Hbb4) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR4 Hbb4) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ keptLZW HK AG Hpres4' Hfin3 HfinS3 EFA3 F HFpres4 Hraw3 Hing3 Hrpres4
ltac:(intros a Ha Hx; clear - Ha Hx HdBR; unbox; lia) ltac:(intros a Ha Hx; clear - Ha Hx HdBG; unbox; lia)
Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trbsegs 600 Ev (havoc Ev 600 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)]) ssv msv HS
(env_agree_havoc_ge 600 600 Ev Ev _ ltac:(lia) (env_agree_refl 600 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E600 : ew Ev 600 = Z_to_bv 64 bb) by (rewrite HEv; exact (ew_havoc_new _ 600 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E601 : ew Ev 601 = Z_to_bv 64 (M mod 2 ^ 32)) by (rewrite HEv; exact (ew_havoc_new _ 600 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 2%nat) (-120) (-104) (-120) (-104) [YQ0b.mkChunk (-120) (CVal 8 (SOff 600 0)); YQ0b.mkChunk (-112) (CVal 4 (SOff 601 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply Hpres4'; rewrite FFS; lia
| apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (spZ regs) (-120) 8 _ bb);
[cbn [sv_denot]; rewrite E600, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (spZ regs + -120) with (spZ regs - 120) by lia; exact Vbb]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (spZ regs) (-112) 4 _ (M mod 2 ^ 32));
[cbn [sv_denot]; rewrite E601, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)); zside | zside
| replace (spZ regs + -112) with (spZ regs - 120 + 8) by lia; apply val_mem_mod4; exact VM]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
rewrite Hres0 in Ha04.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pin_reg' trbsegs Ev ssv msv (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RABspan 0x89db8; [awrRA AG fpos F EFA4|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_T0 602%nat ra_deads_T0 ltac:(idtac).
ra_hand RT0 HS. split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists bb, Lbb, M. split; [rewrite ew_havoc_old by (clear; lia); exact E600|]. split; [rewrite ew_havoc_old by (clear; lia); exact E601|].
split; [exact HPerm4|]. split; [exact Hbb4096|]. split; [exact HM|]. split; [exact Abb | exact Tbb].
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
rreg HS (10%bv : bv 5) Qa0. rewrite Ha04 in Qa0. symmetry in Qa0. unfold w64 in Qa0.
lazymatch type of Qa0 with ew ?Ev ?n = _ =>
pose proof (st_ok_add_fact trbsegs Ev _ _ n (mkAF 2 5 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Qa0, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Hres25; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RABspan 0x89db8; [awrRA AG fpos F EFA4|]. clear_frames.
fact_of HS 361%nat F361.
rreg HS (21%bv : bv 5) Qs5.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_Tf 602%nat ra_deads_Tf
ltac:(idtac; ra_join_val HS 602%nat 16%nat Qs5 Eres;
ra_join_fact HS 618%nat (mkAF 2 5 0) ltac:(rewrite Eres; clear - F361; lia)).
ra_hand RTF HS. split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exact HPerm4.
Qed.
Lemma ra_P : ra_from B ss_T0 (INV_T0 B) -> ra_from B ss_Tf (INV_Tf B) -> ra_from B ss_P (INV_D B).
Proof. exact ra_P_aux. Qed.
End d.
End b.

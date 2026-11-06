(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YG0y YG0z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF64 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition SF_ENTRY {imgk : img} : Z := (0x3d354 + D_2c4).
Definition FS_B : Z := 8192.
Definition SF_WIN : Z := 96.
Definition sf_ranges {imgk : img} : list (Z * nat) := [((0x3d354 + D_2c4), 20%nat); ((0x3d3a4 + D_2c4), 28%nat); ((0x542ec + D_2c4), 233%nat)].
Definition tbl_sf {imgk : img} : ctable := ltac:(img_eval_sel (fun imgk : img => (build_ranges sf_ranges TEmpty))).
Lemma tbl_sf_eq {imgk : img} : tbl_sf = build_ranges sf_ranges TEmpty. Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl ctable l_) end. Qed.
Lemma tbl_sf_ok {imgk : img} : table_ok tfxsegs tbl_sf.
Proof. img_destruct imgk. all: rewrite tbl_sf_eq. all: img_apply build_ranges_ok; [img_try (unfold sf_ranges; repeat constructor; cbn; discriminate) | img_try (img_apply table_ok_empty)]. Qed.
Definition sf_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) :=
[((0xa2158 + D_10f0), 40, [(0, 8%N, (0xa79b8 + D_10c0)); (8, 8%N, (0xaa1b8 + D_10c0)); (16, 8%N, (0xaaea8 + D_10c0)); (24, 8%N, (0xaaeb0 + D_10c0)); (32, 8%N, (0xaaea0 + D_10c0))]);
((0xaa1b8 + D_10c0), 8, [(0, 8%N, 0x7fff8000)]); ((0xaaea0 + D_10c0), 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
((0xa4000 + D_10f0), 8, [(0, 8%N, (0x9b894 + D_10ec))]); ((0xa9a1c + D_10c0), 1, [(0, 1%N, 1)]); ((0xa2180 + D_10f0), 8, [(0, 8%N, (0xa4000 + D_10f0))])].
Lemma sf_rodata_chk {imgk : img} : forall ly, rodata_chk ly sf_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition aFLG : nat := 32.
Definition stk : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- SF_WIN) 0 (- SF_WIN) 0 [].
Definition rFF : YQ0b.region := YQ0b.mkRegion (Some 10%nat) (FS_B - 8) FS_B (FS_B - 8) (FS_B - 8) [YQ0b.mkChunk (FS_B - 8) (CVal 8 (SOff aFLG 0))].
Definition rFLG : YQ0b.region := YQ0b.mkRegion (Some aFLG) 0 1 0 1 [].
Definition ffLO (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition ffHI (hi : bool) : Z := if hi then CEIL_MAX - FS_B else kLowShadowBeg - FS_B.
Definition sf_facts (hi : bool) : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + SF_WIN) kHighMemEnd 4); (10%nat, mkAF (ffLO hi) (ffHI hi) 5); (11%nat, mkAF 8 FS_B 3); (aFLG, mkAF 4096 (CEIL_MAX - 1) 0)].
Definition sf_mem {imgk : img} : smem := stk :: rFF :: rFLG :: map ro_region sf_rodata.
Definition ss0 {imgk : img} (hi : bool) : sstate := mkSS SF_ENTRY sr_atoms sf_mem None (mkFacts (sf_facts hi) [] []).
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_sf FUEL s.
Definition eH {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ss0 true))))).
Definition eL {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ss0 false))))).
Definition e1 {imgk : img} (hi : bool) : sstate := if hi then eH else eL.
Lemma r_sf {imgk : img} : forall hi, RUN (ss0 hi) = (e1 hi, RS_stopped SR_fetch). Proof. intros [|]; (img_case; vm_compute); img_refl. Qed.
Definition a0e : sv := SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff 10 0) (SLit 3)).
Definition a2e {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs eH) 12%bv))).
Definition keep_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sf_shape {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? tfx_A_musl_memset) && (match ss_resv ss with None => true | _ => false end) &&
sv_eqb (sr_get (ss_regs ss) 10%bv) a0e && sv_eqb (sr_get (ss_regs ss) 11%bv) (SLit 0xf5) && sv_eqb (sr_get (ss_regs ss) 12%bv) a2e &&
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep_regs.
Lemma shape_sf {imgk : img} : forall hi, sf_shape (e1 hi) = true. Proof. intros [|]; (img_case; vm_compute); img_refl. Qed.
Lemma e1_stk {imgk : img} : forall hi, exists cs, nth_error (ss_mem (e1 hi)) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- SF_WIN) 0 (- SF_WIN) 0 cs).
Proof. intros [|]; eexists; (img_case; vm_compute); img_refl. Qed.
Lemma e1_flg {imgk : img} : forall hi, nth_error (ss_mem (e1 hi)) 2 = Some (YQ0b.mkRegion (Some aFLG) 0 1 0 1 [YQ0b.mkChunk 0 (CVal 1 (SLit 0))]).
Proof. intros [|]; (img_case; vm_compute); img_refl. Qed.
Lemma a2e_eq {imgk : img} : a2e = SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff 10 0) (SLit 3))) (SLit 0).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma a0e_denot : forall E FF, bv_unsigned (ew E 10) = FF -> 0 <= FF < 2 ^ 64 -> sv_denot E a0e = Z_to_bv 64 (SHADOW_OFF + FF / 8).
Proof.
intros E FF HFF Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a0e)). f_equal.
img_change (bv_unsigned (sv_denot E a0e)) with (U E a0e). rewrite (U_zev E a0e) by (img_try ((img_case; vm_compute); img_refl)).
unfold a0e. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, !Z.add_0_r. img_change (Z.land (zcanon 3) 63) with 3. img_change (zcanon SHADOW_OFF) with SHADOW_OFF.
rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 3) with 8. unfold SHADOW_OFF.
pose proof (Z.div_pos FF 8 ltac:(img_lia) ltac:(img_lia)). pose proof (Z.div_lt_upper_bound FF 8 (2 ^ 61) ltac:(img_lia) ltac:(img_lia)).
rewrite (zcanon_small FF) by img_lia. rewrite (zcanon_small (FF / 8)) by img_lia. img_apply zcanon_small. img_lia.
Qed.
Lemma a2e_denot {imgk : img} : forall E FF n, bv_unsigned (ew E 10) = FF -> bv_unsigned (ew E 11) = n ->
8 <= FF -> FF + n <= 2 ^ 63 -> FF mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> sv_denot E a2e = Z_to_bv 64 (n / 8).
Proof.
intros E FF n HFF Hn H8 Hhi Hm1 Hm2 Hn8. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a2e)). f_equal.
img_change (bv_unsigned (sv_denot E a2e)) with (U E a2e). rewrite (U_zev E a2e) by (img_try ((img_case; vm_compute); img_refl)).
rewrite a2e_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, Hn, !Z.add_0_r. img_change (Z.land (zcanon 3) 63) with 3.
assert (Eq1 : FF = 8 * (FF / 8)) by (img_try (pose proof (Z.div_mod FF 8 ltac:(img_lia)); img_lia)).
assert (Eq2 : n = 8 * (n / 8)) by (img_try (pose proof (Z.div_mod n 8 ltac:(img_lia)); img_lia)).
set (f := FF / 8) in *. set (m := n / 8) in *.
assert (Hf : 1 <= f) by img_lia. assert (Hm : 1 <= m) by img_lia.
rewrite !Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 3) with 8.
rewrite (zcanon_small (FF + -8)) by img_lia. rewrite (zcanon_small n) by img_lia. rewrite (zcanon_small (FF + -8 + n)) by img_lia.
rewrite (zcanon_small FF) by img_lia. img_change (zcanon 1) with 1.
replace ((FF + -8 + n) / 8) with (f + m - 1) by (img_try (rewrite Eq1, Eq2; replace (8 * f + -8 + 8 * m) with ((f + m - 1) * 8) by img_lia; rewrite Z_div_mult by img_lia; img_refl)).
replace (FF / 8) with f by img_refl.
rewrite (zcanon_small (f + m - 1)) by img_lia. rewrite (zcanon_small (f + m - 1 + 1)) by img_lia. rewrite (zcanon_small f) by img_lia.
replace (f + m - 1 + 1 - f) with m by img_lia. rewrite (zcanon_small m) by img_lia. img_apply zcanon_small. img_lia.
Qed.
Lemma sf_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> sym_runN tfxsegs tbl_sf FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tbl_sf tbl_sf_ok YF8r.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|]. split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Section d. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Theorem tfx_stack_free_7 : astack_free_realizes tfxsegs B SF_ENTRY 7.
Proof.
intros ly S W regs mem md pos n HPRE Hin G10 G11 Hn Hn8 HTR.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF8r.Hwx_tfa as Hwx.
set (H := w_H W) in *. set (sp0 := spZ regs) in *.
img_change (fs_frame_bytes 7) with 8192 in *.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (HES : ESTACK = 4096) by img_refl.
pose proof (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (ZF : zone3 (ly_F ly) kFakeStackSize).
{ pose proof (proj1 (Forall_forall _ _) (lo_app ly HLY) (ly_F ly, kFakeStackSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as IA. cbv beta in IA.
assert (D9 : zdisjoint (ly_F ly, kFakeStackSize) (ly_img ly)).
{ pose proof (lo_disj ly HLY) as PD.
img_exact (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(img_try (unfold static_extents; rewrite <- app_assoc; img_refl)) PD ltac:(img_try (img_apply in_app_iff; left; unfold owned_extents; cbn; tauto)) ltac:(img_try (left; img_refl))). }
img_exact (zone3_intro ly (ly_F ly) kFakeStackSize IMG ltac:(img_try (unfold kFakeStackSize; img_lia)) IA D9). }
destruct ZF as (HF1 & HF2 & HFz).
pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as CR. pose proof CR as CR0. unfold YG0h.ASAN_CEIL in CR0.
unfold ASAN_CEIL, kFakeStackSize in HF1, HF2.
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in HFz.
assert (ZONE : exists hi : bool, if hi then 17594333495296 <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling else (6287360 + D_1000) <= ly_F ly /\ ly_F ly + 11571200 <= 2147446784).
{ destruct HFz as [X|[X|X]]; [img_try (exfalso; clear - X HF1; img_lia) | img_try (exists false; img_exact X) | img_try (exists true; img_exact X)]. }
destruct ZONE as [hi HZ].
assert (HPOS : 0 <= pos < 128).
{ pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf B ly S _ M))) (7, pos) Hin) as [_ X]. cbn [fst snd] in X. img_exact X. }
set (fa := frame_addr ly 7 pos) in *. set (fl := flag_addr ly 7 pos) in *.
assert (Efa : fa = ly_F ly + 7376896 + pos * 8192).
{ unfold fa, frame_addr, fs_frame_off. img_change kFakeFramesOff with 36864. img_change (Z.shiftl 1 kStackSizeLog) with 1048576. img_change (fs_frame_bytes 7) with 8192. img_lia. }
assert (Efl : fl = ly_F ly + 36608 + pos).
{ unfold fl, flag_addr, fs_flag_off. img_change kFakeFlagsOff with 4096. img_change (fs_flags_off 7) with 32512. img_lia. }
destruct (al_frames _ _ LAWS ly S W mem md 7 pos HAR Hin) as (Hal32 & _ & Hfr & Hsh). fold fa in Hal32, Hfr, Hsh. change (fs_frame_bytes 7) with 8192 in Hfr, Hsh. img_change (8192 / 8) with 1024 in Hsh.
destruct (al_flag _ _ LAWS ly S W mem md 7 pos HAR Hin) as (Hflp & Hflo & _ & _). fold fl in Hflp, Hflo.
pose proof (lo_stk_ceil ly HLY) as SC. unfold ASAN_CEIL in SC.
assert (RFA : (6287360 + D_1000) <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling) by (img_try (destruct hi; img_lia)).
assert (Hsp : kHighMemBeg + 4096 <= sp0 <= 2 ^ 47 /\ alloc_ceiling + 4096 <= sp0) by (img_try (unfold kHighMemBeg, kHighMemEnd, sp0 in *; img_lia)).
set (E := Ereg regs [w64 fl]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) by (img_try (intros; (subst E; cbv beta); img_apply ew_Ereg_nat; assumption)).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (img_try (rewrite (EEreg 2%nat 2%bv eq_refl); img_refl)).
assert (E10 : bv_unsigned (ew E 10) = fa) by (img_try (rewrite (EEreg 10%nat 10%bv eq_refl), G10; img_apply unsigned_lit_small; img_lia)).
assert (E11 : bv_unsigned (ew E 11) = n) by (img_try (rewrite (EEreg 11%nat 11%bv eq_refl), G11; img_apply unsigned_lit_small; img_lia)).
assert (E32 : ew E 32 = w64 fl) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (U32 : bv_unsigned (ew E 32) = fl) by (img_try (rewrite E32; img_apply unsigned_lit_small; img_lia)).
assert (HS0 : st_ok tfxsegs E (ss0 hi) (restrict H (mkst regs (Z_to_bv 64 SF_ENTRY) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss0, sf_mem. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [w64 fl]) with E.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_change (stk :: rFF :: rFLG :: map ro_region sf_rodata) with ([stk; rFF; rFLG] ++ map ro_region sf_rodata).
img_apply Forall_app. split; [|img_try (img_exact (rodata_ok B TB sf_rodata ly S H mem E (sf_rodata_chk ly) M))].
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ unfold stk, SF_WIN. img_apply (region_ok_stack tfxsegs E _ 2 sp0 (- 96)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply YE0v.apresent_writable. img_apply HpresE. fold sp0. img_lia.
+ unfold rFF, aFLG, FS_B, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite E10.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E _ fa (8192 - 8) 8%N (SOff 32 0) fl); [img_try (cbn [sv_denot]; rewrite U32, Z.add_0_r; img_refl) | img_try (cbn; img_lia) | img_try (cbn; img_lia) |].
replace (fa + (8192 - 8)) with (fa + 8192 - 8) by img_lia. img_exact (YE0v.val_mem_of_rdword H mem _ _ HTR).
+ unfold rFLG, aFLG, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U32.
split; [img_lia|]. split; [img_lia|]. split; [|img_try (img_apply Forall_nil)]. intros o Ho. replace (fl + o) with fl by img_lia. img_exact (YE0v.apresent_writable H mem fl Hflp).
- img_apply pairwise_disjoint_of_extents. unfold stk, rFF, rFLG, aFLG, sf_rodata, ro_region, extent_of_region, SF_WIN, FS_B.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E10, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok sf_facts]. unfold afact_ok, aFLG. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, U32. unfold ffLO, ffHI, SF_WIN, FS_B, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
img_change (2 ^ 4) with 16. img_change (2 ^ 5) with 32. img_change (2 ^ 3) with 8. img_change (2 ^ 0) with 1.
repeat split; first [img_exact Hal16 | img_exact Hal32 | img_exact Hn8 | img_apply Z.mod_1_r | destruct hi; img_lia]. }
unfold cfg_at. img_change (w64 SF_ENTRY) with (Z_to_bv 64 SF_ENTRY).
eapply SRr_bind; [img_try (img_apply (sf_phase W E _ _ _ _ _ HS0 (r_sf hi)))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1).
assert (MEQ1 : forall z : word, ~ (sp0 - 96 <= bv_unsigned z < sp0) -> bv_unsigned z <> fl -> ms_mem ms1 z = mem z).
{ intros z Hz1 Hz2. img_apply HFm1. intros Hw. destruct (in_wrange_windows E _ _ Hw) as (b & lo & hi' & Ht & Hb).
unfold ss0, sf_mem in Ht. cbn [ss_mem] in Ht. cbn in Ht.
destruct Ht as [Hq|[Hq|[Hq|Ht]]]; try (injection Hq as <- <- <-; cbn [base_val] in Hb; rewrite ?E2, ?E10, ?U32 in Hb; unfold SF_WIN, FS_B, aFLG in *; img_lia).
repeat (destruct Ht as [Hq|Ht]; [img_try (injection Hq as <- <- <-; cbn [base_val] in Hb; img_lia)|]). destruct Ht. }
clear HFm1 HFrm1.
pose proof (shape_sf hi) as Hshape. unfold sf_shape in Hshape. apply andb_prop in Hshape as [Hshape KR]. apply andb_prop in Hshape as [Hshape S12].
apply andb_prop in Hshape as [Hshape S11]. apply andb_prop in Hshape as [Hshape S10]. apply andb_prop in Hshape as [Spc Srv].
apply Z.eqb_eq in Spc. assert (Hrv : ss_resv (e1 hi) = None) by (img_try (destruct (ss_resv (e1 hi)); [img_try (discriminate) | img_refl])).
apply sv_eqb_eq in S10. apply sv_eqb_eq in S11. apply sv_eqb_eq in S12. rewrite forallb_forall in KR.
pose proof (st_ok_restrict_mkst tfxsegs H E _ _ HS1 Hrv) as Hshape1. rewrite Spc in Hshape1.
set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
assert (KEEP1 : forall r, In r keep_regs -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold regs1. rewrite (st_ok_restrict_reg tfxsegs H E (e1 hi) ms1 _ HS1). specialize (KR r Hr). apply sv_eqb_eq in KR. rewrite KR.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_apply EEreg.
unfold keep_regs in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [img_refl|]). destruct Hr. }
set (sh := shadow_addr fa) in *. set (cnt := n / 8).
assert (Hfa8 : 0 <= fa / 8 <= 17592184995840) by (img_try (split; [img_try (img_apply Z.div_pos; img_lia) | img_try (img_apply Z.div_le_upper_bound; img_lia)])).
assert (Hcnt : 1 <= cnt <= 1024) by (img_try (unfold cnt; split; [img_try (img_apply Z.div_le_lower_bound; img_lia) | img_try (img_apply Z.div_le_upper_bound; img_lia)])).
assert (Esh : sh = SHADOW_OFF + fa / 8) by img_refl. unfold SHADOW_OFF in Esh.
assert (A10 : getr regs1 10 = w64 sh).
{ unfold regs1. rewrite (st_ok_restrict_reg tfxsegs H E (e1 hi) ms1 10%bv HS1), S10. rewrite (a0e_denot E fa E10 ltac:(img_lia)). img_refl. }
assert (A11 : getr regs1 11 = w64 0xf5) by (img_try (unfold regs1; rewrite (st_ok_restrict_reg tfxsegs H E (e1 hi) ms1 11%bv HS1), S11; img_refl)).
assert (A12 : getr regs1 12 = w64 cnt).
{ unfold regs1. rewrite (st_ok_restrict_reg tfxsegs H E (e1 hi) ms1 12%bv HS1), S12.
assert (Hfa8m : fa mod 8 = 0).
{ pose proof (Z.div_mod fa 32 ltac:(img_lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (fa / 32)) with ((4 * (fa / 32)) * 8) by img_lia. img_apply Z_mod_mult. }
rewrite (a2e_denot E fa n E10 E11 ltac:(img_lia) ltac:(img_lia) Hfa8m Hn8 ltac:(img_lia)). img_refl. }
assert (A1 : getr regs1 1 = getr regs 1) by (img_try (img_exact (KEEP1 1 ltac:(unfold keep_regs; cbn [In]; tauto)))).
destruct (e1_stk hi) as (cs & Hstk). pose proof (e1_flg hi) as Hflg.
assert (PW1 : forall a, sp0 - 96 <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. img_apply (st_ok_window_apresent H E (e1 hi) ms1 0 _ a HS1 Hstk); [img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite E2; unfold SF_WIN; img_lia) | img_try (unfold TFX_IMG_END, kHighMemBeg in *; img_lia)]. }
assert (FL1 : aview tfxsegs H mem1 fl = Some 0).
{ pose proof (st_ok_mem_ok tfxsegs E (e1 hi) _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hflg)) as (_ & _ & _ & Hcs).
cbn [YQ0b.r_base YQ0b.r_chunks base_val] in Hcs. unfold aFLG in Hcs. rewrite U32 in Hcs.
pose proof (val_of_chunk_ok tfxsegs E _ fl 0 1%N (SLit 0) 0 (Forall_inv Hcs) eq_refl ltac:(img_try (cbn; img_lia)) ltac:(img_try (cbn; img_lia))) as V.
specialize (V 0%nat ltac:(img_try (cbn; img_lia))). rewrite !Z.add_0_r in V. unfold aview. fold mem1 H in V. rewrite V. img_refl. }
assert (PRS : forall a, sh <= a < sh + cnt -> apresent H mem a /\ ~ aowned B ly S a).
{ intros a Ha. replace a with (sh + (a - sh)) by img_lia. img_apply Hsh. img_lia. }
assert (NSTK : forall a, sh <= a < sh + cnt -> ~ (sp0 - 96 <= a < sp0) /\ a <> fl).
{ intros a Ha. split; [img_lia|]. intros ->. img_exact (proj2 (PRS fl Ha) Hflo). }
assert (DW : forall a, sh <= a < sh + cnt -> writable_at tfxsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (PRS a Ha) as [[Hh [b Hb]] _]. split; [|img_try (img_exact Hh)].
img_apply YE0v.apresent_writable. split; [img_try (img_exact Hh)|]. exists b. unfold mem1. rewrite MEQ1; [img_try (img_exact Hb) | |]; rewrite unsigned_lit_small by img_lia; img_apply (NSTK a Ha). }
set (nn := Z.to_nat cnt). assert (Hnn : Z.of_nat nn = cnt) by (img_try ((subst nn; cbv beta); img_lia)).
assert (SOK : store_ok tfxsegs (mrestrict H mem1) (w64 sh) nn = true).
{ img_apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by img_lia; [img_lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(img_lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. img_exact Wz. }
destruct (tfx_memset (w64 sh) (w64 0xf5) (w64 cnt) nn (mrestrict H mem1) (seg_rom tfxsegs) regs1 A10 A11 A12
ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)) SOK ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)))
as (regs2 & Hms & B10 & Hkeep).
rewrite A1, Hra in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 0xf5) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 sh) (repeat cb nn)) in Hms.
set (mem2 := munrestrict H mem1 m2r).
rewrite Hshape1. fold regs1 mem1.
eapply (SRr_msteps tfxsegs Hwx W); [img_try (rewrite restrict_mkst_fx; img_exact Hms)|].
intros model' Hsbm _.
pose proof (same_but_materialized_trans _ _ _ (with_vm_backing_same md mat1) Hsbm) as HSBM.
img_change (unrestrict H mem1 (mkst regs2 (getr regs 1) m2r (seg_rom tfxsegs))) with (mkst regs2 (getr regs 1) mem2 (seg_rom tfxsegs)).
assert (LEN : Z.of_nat (length (repeat cb nn)) = cnt) by (img_try (rewrite repeat_length; img_exact Hnn)).
assert (M2out : forall z : word, ~ (sh <= bv_unsigned z < sh + cnt) -> mem2 z = mem1 z).
{ intros z Hz. (subst mem2 m2r; cbv beta). unfold munrestrict. destruct (H z) eqn:Hh; [img_refl|].
assert (Ew : wbytes m1r (w64 sh) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) sh) as [L|L].
- img_apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by img_lia; img_lia.
- img_apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by img_lia. img_lia. }
rewrite Ew. (subst m1r; cbv beta). unfold mrestrict. rewrite Hh. img_refl. }
assert (M2in : forall i, 0 <= i < cnt -> mem2 (Z_to_bv 64 (sh + i)) = Some cb).
{ intros i Hi. (subst mem2; cbv beta). unfold munrestrict. rewrite (proj2 (DW (sh + i) ltac:(img_lia))).
(subst m2r; cbv beta). rewrite (wbytes_inside (repeat cb nn) m1r (w64 sh) (Z_to_bv 64 (sh + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by img_lia; [|img_lia|img_lia].
replace (Z.to_nat (sh + i - sh)) with (Z.to_nat i) by img_lia. img_apply nth_error_repeat. img_lia. }
assert (CB : bv_unsigned cb = 0xf5) by (img_try ((subst cb; cbv beta); (img_case; vm_compute); img_refl)).
assert (AVin : forall i, 0 <= i < cnt -> aview tfxsegs H mem2 (sh + i) = Some 0xf5).
{ intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (sh + i) ltac:(img_lia))), (M2in i Hi). cbn [option_map]. rewrite CB. img_refl. }
assert (AVout : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + cnt) -> ~ (sp0 - 96 <= a < sp0) -> a <> fl -> aview tfxsegs H mem2 a = aview tfxsegs H mem a).
{ intros a Hr Ha Hs Hf. img_apply aview_same. rewrite M2out by (img_try (rewrite unsigned_lit_small by img_lia; img_exact Ha)).
img_apply MEQ1; rewrite unsigned_lit_small by img_lia; assumption. }
assert (FL2 : aview tfxsegs H mem2 fl = Some 0).
{ rewrite <- FL1. img_apply aview_same. img_apply M2out. rewrite unsigned_lit_small by img_lia. intros Ha. img_exact (proj2 (NSTK fl Ha) eq_refl). }
assert (PW2 : forall a, sp0 - 96 <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. destruct (PW1 a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite M2out; [img_try (img_exact Hb)|]. rewrite unsigned_lit_small by img_lia. img_lia. }
img_apply SRr_ret. split; [img_refl|]. exists regs2, mem2, model'.
pose proof (same_but_materialized_frame md model' HSBM) as MF.
split; [img_try (unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; img_refl)|].
split; [|img_try (split; [|split; [img_exact HSBM|split; [|split]]])].
-
img_apply (astack_free_law_ok tfxsegs B ly S W mem md mem2 model' 7 pos HAR Hin).
+ img_exact FL2.
+ intros a Hr Hown Hnf. img_apply AVout; [img_try (img_exact Hr) | | | img_try (img_exact Hnf)].
* intros Ha. img_exact (proj2 (PRS a Ha) Hown).
* intros Ha. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hvw. fold H in Hvw |- *. rewrite (YE0v.aview_mod _ mem2 a). rewrite (YE0v.aview_mod _ mem a) in Hvw.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z.eq_dec a' fl) as [Ea|Hnf]; [img_try (rewrite Ea, FL2; discriminate)|].
destruct (Z_lt_le_dec a' sh) as [L1|L1]; [| img_try (destruct (Z_lt_le_dec a' (sh + cnt)) as [L2|L2])].
2:{ replace a' with (sh + (a' - sh)) by img_lia. rewrite AVin by img_lia. discriminate. }
all: destruct (Z_lt_le_dec a' (sp0 - 96)) as [L3|L3]; [img_try (rewrite AVout by img_lia; img_exact Hvw)|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [| img_try (rewrite AVout by img_lia; img_exact Hvw)].
all: img_apply aview_some_of_apresent; img_apply PW2; img_lia.
+ img_apply MF. + img_apply MF. + img_apply MF.
+ intros a Hb Hh. img_change (w_H W (w64 a)) with (H (Z_to_bv 64 a)) in Hh. pose proof (YE0v.in_band_rw_u64 a Hb) as Hr.
unfold w64. rewrite M2out.
* img_apply MEQ1; rewrite unsigned_lit_small by img_lia.
-- intros Ha. destruct (PW1 a Ha) as [Hh' _]. rewrite Hh' in Hh. discriminate.
-- intros ->. pose proof (proj1 Hflp) as Hf0. unfold H in Hh, Hf0. rewrite Hf0 in Hh. discriminate.
* rewrite unsigned_lit_small by img_lia. intros Ha. rewrite (proj2 (DW a Ha)) in Hh. discriminate.
-
intros r Hr.
assert (NE : forall x : bv 5, 11 <= bv_unsigned x <= 16 -> Z_to_bv 5 r <> x).
{ intros x Hx Ex. rewrite <- Ex in Hx. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx. img_change (bv_modulus 5) with 32 in Hx.
unfold acallee_saved in Hr. rewrite Z.mod_small in Hx by img_lia. img_lia. }
rewrite Hkeep; [img_try (img_apply KEEP1; unfold acallee_saved in Hr; unfold keep_regs; cbn [In]; img_lia) | | | | | |]; img_apply NE; (split; img_apply Z.leb_le; img_refl).
-
intros i Hi. fold sh. img_apply AVin. fold cnt in Hi. img_exact Hi.
-
intros a Hr Ha Hnf Hs. fold sh in Ha. fold cnt in Ha. img_apply AVout; [img_try (img_exact Hr) | img_try (img_exact Ha) | | img_try (img_exact Hnf)]. fold sp0 in Hs. rewrite HES in Hs. img_lia.
-
intros a Ha. fold sp0 in Ha. rewrite HES in Ha. destruct (Z_lt_le_dec a (sp0 - 96)) as [L|L]; [|img_try (img_apply PW2; img_lia)].
destruct (HpresE a ltac:(img_try (fold sp0; img_lia))) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b.
rewrite M2out by (img_try (rewrite unsigned_lit_small by img_lia; img_lia)). rewrite MEQ1; [img_try (img_exact Hb) | |]; rewrite unsigned_lit_small by img_lia; [img_lia|].
intros ->. img_exact (al_stack _ _ LAWS ly S W mem md fl HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hflo).
Qed.
End d.
End c.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF09 YF0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8t YF3v YF4q YF8g YF8f YF3w YF8i YF3i YF8j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (img_try (unfold M64; img_lia))
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := img_ev (Z.land a b) in img_change (Z.land a b) with c
end.
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; img_lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFX_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ img_refl | img_refl | cbn [base_val YQ0b.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := img_ev constr:(p) in img_change p with q end
| cbn; img_lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := img_ev (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
end.
Section h. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pr := (@YF8f.Pr ly c).
Local Abbreviation RGv := (@YF8f.RGv ly c).
Local Abbreviation RBv := (@YF8f.RBv ly c).
Local Abbreviation FAv := (@YF8f.FAv ly c).
Local Abbreviation SHBv := (@YF8f.SHBv).
Local Abbreviation SRCv := (@YF8f.SRCv ly c n nf).
Local Abbreviation DSTv := (@YF8f.DSTv ly c).
Local Abbreviation AR5 f := (f j64 jna jnf jsm jm1 jm2) (only parsing).
Local Abbreviation XWR := (AR5 (@YF8f.XWR ly c maxc n nf mf au mu csz)).
Local Abbreviation AR0 f := (f ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2) (only parsing).
Local Abbreviation E0 := (AR0 (@YF8f.E0)).
Local Abbreviation EaT := (AR0 (@YF8f.EaT)).
Local Abbreviation EaC := (AR0 (@YF8f.EaC)).
Local Abbreviation EaSB := (AR0 (@YF8f.EaSB)).
Local Abbreviation EaTOP := (AR0 (@YF8f.EaTOP)).
Local Abbreviation EaCL := (AR0 (@YF8f.EaCL)).
Local Abbreviation EaP := (AR0 (@YF8f.EaP)).
Local Abbreviation EaMAX := (AR0 (@YF8f.EaMAX)).
Local Abbreviation EaN := (AR0 (@YF8f.EaN)).
Local Abbreviation EaCSZ := (AR0 (@YF8f.EaCSZ)).
Local Abbreviation EaRG := (AR0 (@YF8f.EaRG)).
Local Abbreviation EaRB := (AR0 (@YF8f.EaRB)).
Local Abbreviation EaFA := (AR0 (@YF8f.EaFA)).
Local Abbreviation EaNF := (AR0 (@YF8f.EaNF)).
Local Abbreviation EaMF := (AR0 (@YF8f.EaMF)).
Local Abbreviation EaAU := (AR0 (@YF8f.EaAU)).
Local Abbreviation EaMU := (AR0 (@YF8f.EaMU)).
Local Abbreviation EaSHB := (AR0 (@YF8f.EaSHB)).
Local Abbreviation Er := (AR0 (@YF8f.Er)).
Local Abbreviation E2 := (AR0 (@YF8f.E2)).
Local Abbreviation E1 := (AR0 (@YF8f.E1)).
Local Abbreviation E8 := (AR0 (@YF8f.E8)).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HcR : 1 <= c <= 31.
Hypothesis Hmax : maxc = max_cached c.
Hypothesis Hn : n = maxc / 2.
Hypothesis Hcsz : csz = class_size c.
Hypothesis Hnf : 0 <= nf /\ 4 * nf <= mf.
Hypothesis Hmf : 0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0.
Hypothesis Hmu : 0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0.
Hypotheses (Hj64 : 0 <= j64 < 2 ^ 32) (Hjna : 0 <= jna < 2 ^ 64) (Hjnf : 0 <= jnf < 2 ^ 64)
(Hjsm : 0 <= jsm < 2 ^ 64) (Hjm1 : 0 <= jm1 < 2 ^ 64) (Hjm2 : 0 <= jm2 < 2 ^ 64).
Hypothesis Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Htp : getr regs0 4 = w64 TFX_TP.
Hypothesis Ha0 : getr regs0 10 = w64 (T + t_cache).
Hypothesis Ha1 : getr regs0 11 = w64 Pr.
Hypothesis Ha2 : getr regs0 12 = w64 A_ALLOCATOR.
Hypothesis Ha3 : getr regs0 13 = w64 c.
Local Abbreviation AR6 f := (f ly regs0 c) (only parsing).
Local Abbreviation class_facts := ((AR6 (@YF8f.class_facts)) maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation AR2 f := (f ly regs0 maxc mf au mu) (only parsing).
Local Abbreviation high_factsR := ((AR2 (@YF8f.high_factsR _ imgk)) LY IMG Hmf Hmu).
Local Abbreviation off_T := ((AR2 (@YF8f.off_T _ imgk)) LY IMG Hmf Hmu).
Local Abbreviation off_C := ((AR2 (@YF8f.off_C _ imgk)) LY IMG Hmf Hmu).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation AR1 f := (f _ imgk ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation derived_rangesR := (AR1 (@YF8f.derived_rangesR)).
Local Abbreviation WINR0 := (AR6 (@YF8f.WINR0)).
Local Abbreviation WINR := ((AR6 (@YF8f.WINR)) n).
Local Abbreviation WINR0_WINR := ((AR6 (@YF8f.WINR0_WINR)) n).
Local Abbreviation WSKELR := (@YF8f.WSKELR).
Local Abbreviation win_sub := (@YF8f.win_sub).
Local Abbreviation win_sub_sound := ((AR6 (@YF8f.win_sub_sound)) maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation AR3 f := (AR0 f LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation WSKELR_WINR0 := (AR3 (@YF8f.WSKELR_WINR0 _ imgk)).
Local Abbreviation windows_WINR0 := (AR3 (@YF8f.windows_WINR0 _ imgk)).
Local Abbreviation frame_WINR0 := (AR3 (@YF8f.frame_WINR0 _ imgk)).
Ltac frame_accR HE :=
match goal with
| MEQ : (forall x : word, ~ WINR0 (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WINR0 (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WINR0 E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation AR4 f := (f _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz) (only parsing).
Local Abbreviation at_R := (AR5 (AR4 (@YF8f.at_R))).
Local Abbreviation at_RC := (AR5 (AR4 (@YF8f.at_RC))).
Local Abbreviation at_RET2 := (AR4 (@YF8f.at_RET2)).
Local Abbreviation all_disjoint_of_forall := (@YF8f.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (AR2 (@YF8f.kept_of_frame imgk W)).
Local Abbreviation SKEL_TAILR := (@YF8f.SKEL_TAILR imgk).
Local Abbreviation RFACTSR := (AR6 (@YF8f.RFACTSR imgk)).
Local Abbreviation stack_ivsR := ((AR2 (@YF8f.stack_ivsR _)) LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := ((AR1 (@YF8f.zone_litR)) Hsp).
Local Abbreviation zone_TR := ((AR6 (@YF8f.zone_TR _ imgk)) maxc mf au mu LY IMG Hmf Hmu Hsp).
Local Abbreviation zone_CR := ((AR1 (@YF8f.zone_CR)) Hsp).
Local Abbreviation zone_RGR := ((AR1 (@YF8f.zone_RGR)) Hsp).
Local Abbreviation slots_not_WINR0 := ((AR1 (@YF8f.slots_not_WINR0)) Hsp).
Local Abbreviation fa_not_WINR0 := ((AR1 (@YF8f.fa_not_WINR0)) Hsp).
Local Abbreviation tail_ext_okR := ((AR3 (@YF8f.tail_ext_okR _ imgk)) Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R RJ2 W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := ((AR2 (@YF8f.rdn_of_presentR imgk)) Hmf Hmu).
Local Abbreviation store_ok_of_presentR := ((AR2 (@YF8f.store_ok_of_presentR imgk)) Hmf Hmu).
Local Abbreviation cpy4_stretch := ((AR5 ((AR6 (@YF8f.cpy4_stretch _ imgk W)) maxc nf mf au mu)) HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfxSyms B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Hypothesis HARm : ARm B ly S (aview tfxsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hchunks : pc_chunks (cache S c) = [].
Hypothesis Hnf_def : nf = fa_len (rg_free (reg S c)).
Hypothesis Hmf_def : mf = rg_mapped_fa (reg S c).
Hypothesis Hau_def : au = rg_alloc_user (reg S c).
Hypothesis Hmu_def : mu = rg_mapped_user (reg S c).
Hypothesis Hj64v : val_mem tfxsegs (mrestrict (w_H W) mem0) (RGv + 64) 4 j64.
Hypothesis Hjnav : val_mem tfxsegs (mrestrict (w_H W) mem0) (RGv + 72) 8 jna.
Hypothesis Hjnfv : val_mem tfxsegs (mrestrict (w_H W) mem0) (RGv + 80) 8 jnf.
Hypothesis Hjsmv : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2792) 8 jsm.
Hypothesis Hjm1v : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1.
Hypothesis Hjm2v : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2.
Hypothesis HQL : qloose S.
Local Abbreviation Pr_is := (@YF8f.Pr_is ly c).
Local Abbreviation RGv_is := (@YF8f.RGv_is ly c).
Local Abbreviation FAv_is := (@YF8f.FAv_is ly c HcR).
Local Abbreviation RBv_is := (@YF8f.RBv_is ly c HcR).
Local Ltac addr_tac :=
cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFX_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; img_refl
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| img_refl ].
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let m0 := mrestrict (w_H W) mem0.
Ltac clean := try clear SEEDJ; try clear Hpres0R; try clear HslotPres; try clear HfaPres; try clear Hnf; try clear Hmf; try clear Hmu;
try clear Hj64; try clear Hjna; try clear Hjnf; try clear Hjsm; try clear Hjm1; try clear Hjm2;
try clear Hj64v; try clear Hjnav; try clear Hjnfv; try clear Hjsmv; try clear Hjm1v; try clear Hjm2v.
Lemma cls_wfR : cls_ok c (reg S c) (cache S c) true (chunk_offs S c) (batch_offs S c).
Proof. clean. pose proof (wf_classes _ _ _ _ _ WF c HcR) as C0. unfold wf_class in C0. rewrite Hinited in C0. img_exact C0. Qed.
Lemma cls_wf0 : cls_ok c (reg S c) (cache S c) (st_cache_inited S) (chunk_offs S c) (batch_offs S c).
Proof. clean. try clear Hinited. img_exact (wf_classes _ _ _ _ _ WF c HcR). Qed.
Lemma reg_facts0 :
(0 <= nf /\ 4 * nf <= mf) /\ (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) /\
(0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) /\
runs_ok (rg_free (reg S c)).
Proof. clean. try clear Hinited.
pose proof cls_wf0 as CL. pose proof (class_ok c HcR) as (K1 & K2 & _).
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_mapped_al _ _ _ _ _ _ CL) as A2. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as A3.
pose proof (wr_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as F3. pose proof (wr_fa_len _ _ _ _ _ _ CL) as F4.
pose proof (wr_runs _ _ _ _ _ _ CL) as RU.
pose proof (fa_len_nonneg _ RU) as F0.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF HcR) as MB. unfold kUserMapSize, EV_MAX in MB.
rewrite <- Hnf_def in *. rewrite <- Hmf_def in *. rewrite <- Hau_def in *. rewrite <- Hmu_def in *.
assert (A16 : au mod 16 = 0).
{ apply Z.mod_divide in A3 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in K2 as [r Hr]; [|img_try (zlia)]. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q * (r * 2)). zlia. }
unfold kFreeArrayOffset, kUserMapSize in *. repeat split; try assumption; zlia.
Qed.
Lemma reg_facts :
(0 <= nf /\ 4 * nf <= mf) /\ (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) /\
(0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) /\
pc_max (cache S c) = maxc /\ runs_ok (rg_free (reg S c)).
Proof. clean.
pose proof cls_wfR as CL. pose proof (proj1 (wr_cache _ _ _ _ _ _ CL)) as PM. rewrite Hmax. pose proof reg_facts0 as X. tauto.
Qed.
Lemma Hnf' : 0 <= nf /\ 4 * nf <= mf. Proof. clean. try clear Hinited. pose proof reg_facts0; tauto. Qed.
Lemma Hmf' : 0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0. Proof. clean. try clear Hinited. pose proof reg_facts0; tauto. Qed.
Lemma Hmu' : 0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0. Proof. clean. try clear Hinited. pose proof reg_facts0; tauto. Qed.
Ltac clean2 := clean; pose proof Hnf' as Hnf; pose proof Hmf' as Hmf; pose proof Hmu' as Hmu.
Lemma vis_present : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent (w_H W) mem0 a.
Proof. clean. try clear Hinited.
intros e len a Hin Ha Hhi.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [img_try (img_exact (proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) _ Hin)) | img_try (img_exact (proj1 (Forall_forall _ _) (am_areas B ly S rd0 HARm) _ Hin))]. }
destruct (range_vis_mbyte B ly (w_H W) mem0 e len (a - aeval B ly e) RV ltac:(img_try (zlia))) as [b Hb].
replace (aeval B ly e + (a - aeval B ly e)) with a in Hb by zlia. img_exact (mbyte_off_apresent (w_H W) mem0 a b Hhi Hb).
Qed.
Lemma thread_present : forall a, T <= a < T + kThreadObjSize -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof high_factsR as (F1 & F2 & _).
img_apply (vis_present (AT 0) kThreadObjSize).
- right. unfold aareas. do 3 (img_apply in_or_app; right). do 3 right. left. img_refl.
- cbn [aeval]. unfold T in *. zlia.
- off_by ltac:(img_try (clear - Ha F1 F2; numconst; unfold T in *; zlia)).
Qed.
Lemma rinfo_present : forall a, RGv <= a < RGv + 128 -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof derived_rangesR as DR.
img_apply (vis_present (ASp kRegionInfoOff) 4096).
- right. unfold aareas. do 3 (img_apply in_or_app; right). do 4 right. left. img_refl.
- cbn [aeval]. unfold RGv, SB in *. clear - Ha HcR. numconst. zlia.
- clear - Ha DR. numconst. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *. zlia.
Qed.
Lemma HslotPres' : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Proof. clean2. intros a Ha. pose proof derived_rangesR as DR. img_apply thread_present. unfold DSTv in *. clear - Ha DR. numconst. zlia. Qed.
Lemma HfaPres' : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof Hmf as [[M0 M1] _].
img_apply (vis_present (ASp (region_off c + kFreeArrayOffset)) (rg_mapped_fa (reg S c))).
- right. unfold aareas. img_apply in_or_app; left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; zlia)|]. right; left; img_refl.
- cbn [aeval]. rewrite <- Hmf_def. pose proof FAv_is as E. unfold fa_base in E. clear - Ha E. zlia.
- clear - Ha DR F1 F2 F3 F4 F5 F6 M0 M1. numconst. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *. zlia.
Qed.
Lemma word_of_present : forall a, (forall i, 0 <= i < 8 -> apresent (w_H W) mem0 (a + i)) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfxsegs m0 a 8 w.
Proof. clean. try clear Hinited.
intros a PR.
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte tfxsegs m0 (a + Z.of_nat k) = Some b).
{ intros k Hk. img_apply apresent_mbyte. img_apply PR. zlia. }
destruct (BY 0%nat ltac:(img_try (zlia))) as [b0 B0]. destruct (BY 1%nat ltac:(img_try (zlia))) as [b1 B1]. destruct (BY 2%nat ltac:(img_try (zlia))) as [b2 B2]. destruct (BY 3%nat ltac:(img_try (zlia))) as [b3 B3].
destruct (BY 4%nat ltac:(img_try (zlia))) as [b4 B4]. destruct (BY 5%nat ltac:(img_try (zlia))) as [b5 B5]. destruct (BY 6%nat ltac:(img_try (zlia))) as [b6 B6]. destruct (BY 7%nat ltac:(img_try (zlia))) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
split; [img_try (zlia)|].
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YG0h.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YG0h.le_byte. rewrite Z.shiftr_div_pow2 by zlia.
rewrite (Z.mod_small z) by (img_try (img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); zlia)).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(img_try (left; img_exact Hr)) Hz).
symmetry. img_apply (Z.mod_unique _ 256 q b); zlia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfxsegs m0 (a + Z.of_nat kk) = Some bk -> YG0h.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfxsegs m0 (a + Z.of_nat kk) = Some (Z_to_bv 8 (YP0g.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. img_refl. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|img_try (zlia)];
[ img_try (img_apply (GOAL b0 0%nat B0)) | img_try (img_apply (GOAL b1 1%nat B1)) | img_try (img_apply (GOAL b2 2%nat B2)) | img_try (img_apply (GOAL b3 3%nat B3))
| img_try (img_apply (GOAL b4 4%nat B4)) | img_try (img_apply (GOAL b5 5%nat B5)) | img_try (img_apply (GOAL b6 6%nat B6)) | img_try (img_apply (GOAL b7 7%nat B7)) ]; (subst WW; cbv beta).
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 0)) with 1; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 0)) with 1; zlia) | img_try (zlia)].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 1)) with 256; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 1)) with 256; zlia) | img_try (zlia)].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia) | img_try (zlia)].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia) | img_try (zlia)].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia) | img_try (zlia)].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia) | img_try (zlia)].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia) | img_try (zlia)].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia) | img_try (img_change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia) | img_try (zlia)].
Qed.
Lemma val_mem_lo4 : forall m a w, 0 <= w < 2 ^ 64 -> val_mem tfxsegs m a 8 w -> val_mem tfxsegs m a 4 (w mod 2 ^ 32).
Proof. clean. try clear Hinited.
intros m a w Hw H k Hk. rewrite (H k ltac:(img_try (zlia))). do 2 f_equal. rewrite <- (le_byte_eq w). rewrite <- (le_byte_eq (w mod 2 ^ 32)).
rewrite <- (le_byte_split_lo (w mod 2 ^ 32) (w / 2 ^ 32) k); [| img_try (pose proof (Z.mod_pos_bound w (2 ^ 32)); zlia) | img_try (split; [img_apply Z.div_pos; zlia | img_apply Z.div_lt_upper_bound; zlia]) | img_try (img_exact Hk)].
f_equal. pose proof (Z.div_mod w (2 ^ 32) ltac:(img_try (zlia))). zlia.
Qed.
Lemma junk_valuesR : exists j64' jna' jnf' jsm' jm1' jm2',
(0 <= j64' < 2 ^ 32 /\ val_mem tfxsegs m0 (RGv + 64) 4 j64') /\ (0 <= jna' < 2 ^ 64 /\ val_mem tfxsegs m0 (RGv + 72) 8 jna') /\
(0 <= jnf' < 2 ^ 64 /\ val_mem tfxsegs m0 (RGv + 80) 8 jnf') /\ (0 <= jsm' < 2 ^ 64 /\ val_mem tfxsegs m0 (T + 2792) 8 jsm') /\
(0 <= jm1' < 2 ^ 64 /\ val_mem tfxsegs m0 (T + 2872) 8 jm1') /\ (0 <= jm2' < 2 ^ 64 /\ val_mem tfxsegs m0 (T + 2880) 8 jm2').
Proof. clean. try clear Hinited.
destruct (word_of_present (RGv + 64)) as (w0 & R0 & V0); [img_try (intros i Hi; img_apply rinfo_present; zlia)|].
destruct (word_of_present (RGv + 72)) as (w1 & R1 & V1); [img_try (intros i Hi; img_apply rinfo_present; zlia)|].
destruct (word_of_present (RGv + 80)) as (w2 & R2 & V2); [img_try (intros i Hi; img_apply rinfo_present; zlia)|].
destruct (word_of_present (T + 2792)) as (w3 & R3 & V3); [img_try (intros i Hi; img_apply thread_present; numconst; zlia)|].
destruct (word_of_present (T + 2872)) as (w4 & R4 & V4); [img_try (intros i Hi; img_apply thread_present; numconst; zlia)|].
destruct (word_of_present (T + 2880)) as (w5 & R5 & V5); [img_try (intros i Hi; img_apply thread_present; numconst; zlia)|].
exists (w0 mod 2 ^ 32), w1, w2, w3, w4, w5.
pose proof (Z.mod_pos_bound w0 (2 ^ 32) ltac:(img_try (zlia))).
repeat split; try zlia; try assumption. img_apply val_mem_lo4; [img_try (img_exact R0) | img_try (img_exact V0)].
Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfx_const ly) e = Some (ACell e w (AV e')) -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. clean. try clear Hinited. intros e w e' E. img_exact (tfx_const_lookup_sym B TS ly S (w_H W) mem0 e w e' HARm E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfxsegs m0 a w x.
Proof. clean. try clear Hinited. intros a w x E. img_exact (tfx_const_lookup B TS ly S (w_H W) mem0 a w x HARm E). Qed.
Lemma cell_state : forall cc e (w : nat) x, In cc (acells B ly S) -> cc = ACell e w (AV (ANum x)) -> val_mem tfxsegs m0 (aeval B ly e) w x.
Proof. clean. try clear Hinited.
intros cc e w x Hin ->. img_apply (cell_holds_val_mem B ly (w_H W) mem0 e w (ANum x)).
img_exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm) _ Hin).
Qed.
Lemma In_acells_cache : forall cc, In cc (cache_cells S c) -> In cc (acells B ly S).
Proof. clean. try clear Hinited.
intros cc Hc. unfold acells. img_apply in_or_app. right. img_apply in_or_app. left. img_apply in_flat_map. exists c.
split; [img_try (img_apply In_zseq; zlia) | img_try (img_exact Hc)].
Qed.
Lemma In_acells_region : forall cc, In cc (region_cells S c) -> In cc (acells B ly S).
Proof. clean. try clear Hinited.
intros cc Hc. unfold acells. img_apply in_or_app. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; zlia) | img_try (img_exact Hc)].
Qed.
Lemma cache_valsR : val_mem tfxsegs m0 Pr 4 0 /\ val_mem tfxsegs m0 (Pr + 4) 4 maxc /\ val_mem tfxsegs m0 (Pr + 8) 8 csz.
Proof. clean.
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c)) d) = Pr + d) by (img_try (intros d; cbn; unfold Pr; zlia)).
assert (EP0 : aeval B ly (AT (t_cache + 80 * c)) = Pr) by (img_try (cbn; unfold Pr; zlia)).
split; [|img_try (split)].
- rewrite <- EP0. eapply cell_state; [img_try (img_apply In_acells_cache; unfold cache_cells; rewrite Hinited; left; img_refl)|].
rewrite Hchunks. img_refl.
- rewrite <- (EP 4). eapply cell_state; [img_try (img_apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; left; img_refl)|].
rewrite Hmax. img_refl.
- rewrite <- (EP 8). eapply cell_state; [img_try (img_apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; left; img_refl)|].
rewrite Hcsz. img_refl.
Qed.
Lemma In_acells_cache_i : forall i cc, 1 <= i <= 31 -> In cc (cache_cells S i) -> In cc (acells B ly S).
Proof. clean. try clear Hinited.
intros i cc Hi Hc. unfold acells. img_apply in_or_app. right. img_apply in_or_app. left. img_apply in_flat_map. exists i.
split; [img_try (img_apply In_zseq; zlia) | img_try (img_exact Hc)].
Qed.
Lemma cache_valsU : st_cache_inited S = false -> forall i, 1 <= i <= 31 ->
val_mem tfxsegs m0 (T + 208 + 80 * i) 4 0 /\ val_mem tfxsegs m0 (T + 212 + 80 * i) 4 0 /\ val_mem tfxsegs m0 (T + 216 + 80 * i) 8 0.
Proof. clean. try clear Hinited.
intros HU i Hi.
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * i)) d) = T + 208 + 80 * i + d) by (img_try (intros d; cbn; unfold T, t_cache; zlia)).
assert (EP0 : aeval B ly (AT (t_cache + 80 * i)) = T + 208 + 80 * i) by (img_try (cbn; unfold T, t_cache; zlia)).
split; [|img_try (split)].
- rewrite <- EP0. eapply cell_state; [img_try (img_apply (In_acells_cache_i i); [img_exact Hi|]; unfold cache_cells; rewrite HU; left; img_refl) | img_refl].
- replace (T + 212 + 80 * i) with (T + 208 + 80 * i + 4) by zlia. rewrite <- (EP 4).
eapply cell_state; [img_try (img_apply (In_acells_cache_i i); [img_exact Hi|]; unfold cache_cells; rewrite HU; right; left; img_refl) | img_refl].
- replace (T + 216 + 80 * i) with (T + 208 + 80 * i + 8) by zlia. rewrite <- (EP 8).
eapply cell_state; [img_try (img_apply (In_acells_cache_i i); [img_exact Hi|]; unfold cache_cells; rewrite HU; right; right; left; img_refl) | img_refl].
Qed.
Lemma region_valsR :
val_mem tfxsegs m0 RGv 8 0 /\ val_mem tfxsegs m0 (RGv + 8) 8 0 /\ val_mem tfxsegs m0 (RGv + 16) 8 nf /\ val_mem tfxsegs m0 (RGv + 24) 8 mf /\
val_mem tfxsegs m0 (RGv + 32) 8 au /\ val_mem tfxsegs m0 (RGv + 40) 8 0 /\ val_mem tfxsegs m0 (RGv + 48) 8 mu /\ val_mem tfxsegs m0 (RGv + 56) 8 0 /\
val_mem tfxsegs m0 (RGv + 68) 1 0.
Proof. clean. try clear Hinited.
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = RGv + d) by (img_try (intros d; cbn; unfold RGv, SB; zlia)).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = RGv) by (img_try (cbn; unfold RGv, SB; zlia)).
repeat split.
- rewrite <- ER0. eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; left; img_refl) | img_refl].
- rewrite <- (ER 8). eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 1 right; left; img_refl) | img_refl].
- rewrite <- (ER 16), Hnf_def. eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 2 right; left; img_refl) | img_refl].
- rewrite <- (ER 24), Hmf_def. eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 3 right; left; img_refl) | img_refl].
- rewrite <- (ER 32), Hau_def. eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 4 right; left; img_refl) | img_refl].
- rewrite <- (ER 40). eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 5 right; left; img_refl) | img_refl].
- rewrite <- (ER 48), Hmu_def. eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 6 right; left; img_refl) | img_refl].
- rewrite <- (ER 56). eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 7 right; left; img_refl) | img_refl].
- rewrite <- (ER 68). eapply cell_state; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 8 right; left; img_refl) | img_refl].
Qed.
Lemma chunk_lit : forall a (nn : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal nn (SLit x))).
Proof. clean. try clear Hinited. intros a nn x H Hx Hnn. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hnn) | img_try (rewrite Z.add_0_l; img_exact H)]. Qed.
Lemma chunk_lit_at : forall base a (nn : BinNums.N) x, val_mem tfxsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal nn (SLit x))).
Proof. clean. try clear Hinited. intros base a nn x H Hx Hnn. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hnn) | img_try (img_exact H)]. Qed.
Lemma chunk_atom : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal nn (SOff k d))).
Proof. clean. try clear Hinited.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hnn) | img_try (img_exact H)].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [img_try (zlia)|]; split; [img_try (zlia)|]; split; [img_try (intros o Ho; zlia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; zlia | cbn; zlia]) |]); img_apply Forall_nil.
Lemma REG0R_ok_but35 : forall hd, region_ok tfxsegs E0 m0 hd -> Forall (region_ok tfxsegs E0 m0) (replAt 35 hd REG0R).
Proof. try clear Hinited. intros hd Hhd.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
pose proof region_valsR as (RV0 & RV1 & RV2 & RV3 & RV4 & RV5 & RV6 & RV7 & RV8).
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hnf as [N0 N1]. pose proof Hmf as [[M0 M1] M2]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7, K4, M0, M1, U1, U2.
unfold replAt, REG0R, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE. cbn [firstn skipn app map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold rSB, rSHB, rC, rT, rTOP, rCL, rP, rMAX, rN, rCSZ, rRG, rRB, rFA, rNF, rMF, rAU, rMU, rJ64, rJNA, rJNF, rJSM, rJM1, rJM2.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- 1024)); [img_try (rewrite E2; img_refl) | img_try (zlia) | img_try (zlia) |].
intros a Ha. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia)) | img_try (img_apply Hpres0R; unfold RSTACK; zlia)]. }
do 5 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 34%nat 0 SB); [img_try (rewrite EaSB; unfold w64; f_equal; zlia) | img_try (unfold SB; zlia) | | img_try (unfold SB; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (682872 + D_10c0) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst B TS); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; unfold SB; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 34%nat 137438953472 (SB + 137438953472)); [img_try (rewrite EaSB; unfold w64; f_equal; zlia) | img_try (unfold SB; zlia) | | img_try (unfold SB; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (682888 + D_10c0) with (aeval B ly (AInst o_rinfo)) by (img_try (cbn; rewrite (ts_inst B TS); img_refl)).
replace (SB + 137438953472) with (aeval B ly (ASp kRegionInfoOff)) by (img_try (cbn; unfold SB, kRegionInfoOff; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
do 15 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 48%nat 0 SHBv); [img_refl | img_try (unfold SHBv; zlia) | | img_try (unfold SHBv; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. img_apply cell_lit. img_case; vm_compute. all: img_refl. }
do 4 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. pose proof (cell_lit (0x5dd160 + D_10c0) 8 0 ltac:(img_try ((img_case; vm_compute); img_refl))) as H8.
intros k Hk. rewrite (H8 k ltac:(img_try (zlia))). rewrite !le_byte_zero. img_refl. }
img_apply Forall_cons; [img_try (lit_region)|].
img_apply Forall_cons. {   reg_intro. unfold TFX_TP. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (unfold TFX_TSD; cbn; zlia) | img_try (cbn; zlia)].
replace ((6148432 + D_10c0) - 88) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TS); img_refl)).
replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; unfold TFX_TSD; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. unfold TFX_TSD. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)).
replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 32%nat 0 T); [img_try (rewrite EaT; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; unfold T; zlia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. img_apply thread_present. unfold kThreadObjSize, T in *. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 52%nat 0 jsm); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (img_exact Hjsmv) | img_try (cbn; zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. img_apply thread_present. unfold kThreadObjSize, T in *. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom _ _ 8 53%nat 0 jm1); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (img_exact Hjm1v) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 54%nat 0 jm2); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (img_exact Hjm2v) | img_try (cbn; zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons; [img_try (img_exact Hhd)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. {   reg_intro. rewrite EaRG. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. img_apply rinfo_present. zlia. }
repeat (img_apply Forall_cons; [|img_try (try img_apply Forall_nil)]).
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. rewrite Z.add_0_r. img_exact RV0.
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. img_exact RV1.
- img_apply (chunk_atom _ _ 8 44%nat 0 nf); [img_try (rewrite Z.sub_0_r; img_exact EaNF) | img_try (zlia) | img_try (img_exact RV2) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 45%nat 0 mf); [img_try (rewrite Z.sub_0_r; img_exact EaMF) | img_try (zlia) | img_try (img_exact RV3) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 46%nat 0 au); [img_try (rewrite Z.sub_0_r; img_exact EaAU) | img_try (zlia) | img_try (img_exact RV4) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. img_exact RV5.
- img_apply (chunk_atom _ _ 8 47%nat 0 mu); [img_try (rewrite Z.sub_0_r; img_exact EaMU) | img_try (zlia) | img_try (img_exact RV6) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. img_exact RV7.
- img_apply (chunk_atom _ _ 4 49%nat 0 j64); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (img_exact Hj64v) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. img_exact RV8.
- img_apply (chunk_atom _ _ 8 50%nat 0 jna); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (img_exact Hjnav) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 51%nat 0 jnf); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (img_exact Hjnfv) | img_try (cbn; zlia) | img_try (cbn; zlia)]. }
Qed.
Lemma REG0R_ok : Forall (region_ok tfxsegs E0 m0) REG0R.
Proof.
pose proof derived_rangesR as DR. pose proof high_factsR as (hf1 & hf2 & _). pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof cache_valsR as (CV1 & CV2 & CV3).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, kMaxSize in hf1, hf2, DR, K4.
img_change REG0R with (replAt 35 (YQ0b.mkRegion (Some rP) 0 16 0 16 [YQ0b.mkChunk 0 (CVal 4 (SLit 0)); YQ0b.mkChunk 4 (CVal 4 (SOff rMAX 0)); YQ0b.mkChunk 8 (CVal 8 (SOff rCSZ 0))]) REG0R).
img_apply REG0R_ok_but35. reg_intro. unfold rP. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. img_apply thread_present. unfold kThreadObjSize, T in *. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. rewrite Z.add_0_r. img_exact CV1.
- img_apply (chunk_atom _ _ 4 38%nat 0 maxc); [img_try (rewrite Z.sub_0_r; img_exact EaMAX) | img_try (zlia) | img_try (img_exact CV2) | img_try (cbn; zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 40%nat 0 csz); [img_try (rewrite Z.sub_0_r; img_exact EaCSZ) | img_try (zlia) | img_try (img_exact CV3) | img_try (cbn; zlia) | img_try (cbn; zlia)].
Qed.
Lemma REG0U_ok : st_cache_inited S = false -> Forall (region_ok tfxsegs E0 m0) (replAt 35 headc0 REG0R).
Proof. try clear Hinited. intros HU.
pose proof derived_rangesR as DR. pose proof high_factsR as (hf1 & hf2 & _). pose proof (cache_valsU HU c HcR) as (CV1 & CV2 & CV3).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, kMaxSize in hf1, hf2, DR.
img_apply REG0R_ok_but35. unfold headc0. reg_intro. unfold rP. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + 208 + 80 * c) by (img_try (unfold Pr, T, t_cache; zlia)) end. img_exact CV1.
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + 212 + 80 * c) by (img_try (unfold Pr, T, t_cache; zlia)) end. img_exact CV2.
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + 216 + 80 * c) by (img_try (unfold Pr, T, t_cache; zlia)) end. img_exact CV3.
Qed.
Lemma PAIRSR_ok : pairwise_disjoint E0 REG0R.
Proof.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
img_apply pairwise_disjoint_of_extents. unfold REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold rSB, rSHB, rC, rT, rTOP, rP, rRG.
rewrite E2, EaT, EaC, EaP, EaRG. unfold w64. rewrite !unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT.
pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC. unfold zdisjoint in CT, PT, PC. cbn [fst snd] in CT, PT, PC.
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR SI1 SI2 SI3 SI4 SI5 CT PT PC HcR.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_TP, TFX_TSD, RSTACK, kThreadObjSize, kPrimResvSize, kHighMemBeg, kHighMemEnd in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold t_cache, kRegionInfoOff in *.
repeat split; zlia.
Qed.
Lemma SPAN_disj : all_disjoint E0 (YQ0b.mkRegion (Some rT) 292 2704 0 0 []) (dropAt 35 REG0R).
Proof.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
img_apply all_disjoint_of_extents. unfold dropAt, REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE. cbn [firstn skipn app map].
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold rSB, rSHB, rC, rT, rTOP, rP, rRG.
rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG. unfold w64. rewrite !unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT.
pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC. unfold zdisjoint in CT, PT, PC. cbn [fst snd] in CT, PT, PC.
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR SI1 SI2 SI3 SI4 SI5 CT PT PC HcR.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_TP, TFX_TSD, RSTACK, kThreadObjSize, kPrimResvSize, kHighMemBeg, kHighMemEnd in *. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold t_cache, kRegionInfoOff in *.
repeat split; zlia.
Qed.
Lemma FACTSR_ok : atoms_ok E0 (f_atoms FR).
Proof.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hnf as [N0 N1]. pose proof Hmf as [[M0 M1] M2]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7, K4, M0, M1, M2, U1, U2, U3.
pose proof (lo_space_al ly LY) as SAL. pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL. unfold page_aligned in TAL.
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; zlia. }
cbn [FR f_atoms atoms_ok]. unfold rSB, rSHB, rC, rT, rTOP, rCL, rP, rMAX, rN, rCSZ, rRG, rRB, rFA, rNF, rMF, rAU, rMU, rJ64, rJNA, rJNF, rJSM, rJM1, rJM2.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |].
all: pose proof (u64_range (getr regs0 2)) as U; clear - U S1 S3 S4 T4 T7; unfold RSTACK in *; first [zlia | replace (2 ^ 4) with 16 by img_refl; img_exact S4]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact EaT)| | | |]. all: clear - hf1 hf2 TAL; first [zlia | img_exact TAL]. }
split. { img_apply (AF 33%nat (ly_C ly)); [img_try (img_exact EaC)| | | |]. all: clear - hf7 hf8 CAL; first [zlia | img_exact CAL]. }
split. { img_apply (AF 34%nat SB); [img_try (img_exact EaSB)| | | |]. all: unfold SB; clear - hf3 hf4 hf5 hf6 SAL; first [zlia | img_exact SAL]. }
split. { img_apply (AF 35%nat (ly_top ly)); [img_try (img_exact EaTOP)| | | |]. all: clear - T1 T2 T3 T4 T7; first [zlia | img_exact T3]. }
split. { img_apply (AF 36%nat c); [img_try (img_exact EaCL)| | | |]. all: clear - HcR; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat Pr); [img_try (img_exact EaP)| | | |]. all: clear - DR hf1 hf2; first [zlia | replace (2 ^ 4) with 16 by img_refl; tauto]. }
split. { img_apply (AF 38%nat maxc); [img_try (img_exact EaMAX)| | | |]. all: clear - K1 K2; first [zlia | replace (2 ^ 1) with 2 by img_refl; img_exact K2]. }
split. { img_apply (AF 39%nat n); [img_try (img_exact EaN)| | | |]. all: clear - K3; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat csz); [img_try (img_exact EaCSZ)| | | |]. all: clear - K4 K5; first [zlia | replace (2 ^ 4) with 16 by img_refl; img_exact K5]. }
split. { img_apply (AF 41%nat RGv); [img_try (img_exact EaRG)| | | |]. all: clear - DR; first [zlia | replace (2 ^ 7) with 128 by img_refl; tauto]. }
split. { img_apply (AF 42%nat RBv); [img_try (img_exact EaRB)| | | |]. all: clear - DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 16) with 65536 by img_refl; tauto]. }
split. { img_apply (AF 43%nat FAv); [img_try (img_exact EaFA)| | | |]. all: clear - DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 12) with 4096 by img_refl; tauto]. }
split. { img_apply (AF 44%nat nf); [img_try (img_exact EaNF)| | | |]. all: clear - N0 N1 M0 M1; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 45%nat mf); [img_try (img_exact EaMF)| | | |]. all: clear - M0 M1 M2; first [zlia | replace (2 ^ 18) with 262144 by img_refl; img_exact M2]. }
split. { img_apply (AF 46%nat au); [img_try (img_exact EaAU)| | | |]. all: clear - U0 U1 U2 U4; first [zlia | replace (2 ^ 4) with 16 by img_refl; img_exact U4]. }
split. { img_apply (AF 47%nat mu); [img_try (img_exact EaMU)| | | |]. all: clear - U0 U1 U2 U3; first [zlia | replace (2 ^ 18) with 262144 by img_refl; img_exact U3]. }
split. { img_apply (AF 48%nat SHBv); [img_try (img_exact EaSHB)| | | |]. all: clear; unfold SHBv; first [zlia | img_refl]. }
split. { img_apply (AF 49%nat j64); [img_refl| | | |]. all: clear - Hj64; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 50%nat jna); [img_refl| | | |]. all: clear - Hjna; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 51%nat jnf); [img_refl| | | |]. all: clear - Hjnf; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 52%nat jsm); [img_refl| | | |]. all: clear - Hjsm; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 53%nat jm1); [img_refl| | | |]. all: clear - Hjm1; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 54%nat jm2); [img_refl| | | |]. all: clear - Hjm2; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
Qed.
Lemma SEEDR_ok : st_ok tfxsegs E0 SS0R (restrict (w_H W) (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs))).
Proof.
rewrite restrict_mkst_fx. unfold SS0R, REGS0R, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_change (ew (Ereg regs0 XWR) rCL) with (ew E0 36); rewrite EaCL, Ha3; unfold w64; rewrite unsigned_lit_small by zlia; f_equal; zlia)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact Ha2)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_change (ew (Ereg regs0 XWR) rP) with (ew E0 37); rewrite EaP, Ha1; unfold w64; rewrite unsigned_lit_small by (pose proof derived_rangesR; pose proof high_factsR; numconst; unfold T; zlia); f_equal; zlia)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_change (ew (Ereg regs0 XWR) rT) with (ew E0 32); rewrite EaT, Ha0; unfold w64; rewrite unsigned_lit_small by (pose proof high_factsR; numconst; unfold T; zlia); f_equal; unfold T; zlia)].
img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact Htp)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0R_ok.
- img_exact PAIRSR_ok.
- split; [img_try (img_exact FACTSR_ok) | img_try (split; img_exact I)].
Qed.
Lemma PAIRSU_ok : pairwise_disjoint E0 REG0U2.
Proof. img_apply (pairwise_disjoint_ext3 E0 REG0R); [img_try ((img_case; vm_compute); img_refl) | img_try (img_exact PAIRSR_ok)]. Qed.
Lemma SEEDU_ok : st_cache_inited S = false -> st_ok tfxsegs E0 SS0U2 (restrict (w_H W) (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs))).
Proof. try clear Hinited. intros HU.
rewrite restrict_mkst_fx. unfold SS0U2, REGS0R, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_change (ew (Ereg regs0 XWR) rCL) with (ew E0 36); rewrite EaCL, Ha3; unfold w64; rewrite unsigned_lit_small by zlia; f_equal; zlia)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact Ha2)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_change (ew (Ereg regs0 XWR) rP) with (ew E0 37); rewrite EaP, Ha1; unfold w64; rewrite unsigned_lit_small by (pose proof derived_rangesR; pose proof high_factsR; numconst; unfold T; zlia); f_equal; zlia)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_change (ew (Ereg regs0 XWR) rT) with (ew E0 32); rewrite EaT, Ha0; unfold w64; rewrite unsigned_lit_small by (pose proof high_factsR; numconst; unfold T; zlia); f_equal; unfold T; zlia)].
img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact Htp)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact (REG0U_ok HU).
- img_exact PAIRSU_ok.
- split; [img_try (img_exact FACTSR_ok) | img_try (split; img_exact I)].
Qed.
End h.
End g.

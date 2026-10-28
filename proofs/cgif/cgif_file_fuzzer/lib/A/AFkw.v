(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AF0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFl1 AFhy AFis AFkp AFko AFhz AFkr AFhm AFks.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; lia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFIB_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := eval vm_compute in (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
eq_refl eq_refl ltac:(vm_compute; reflexivity)) as HS2; clear HS; rename HS2 into HS
end.
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pr := (@AFko.Pr ly c).
Local Abbreviation RGv := (@AFko.RGv ly c).
Local Abbreviation RBv := (@AFko.RBv ly c).
Local Abbreviation FAv := (@AFko.FAv ly c).
Local Abbreviation SHBv := (@AFko.SHBv).
Local Abbreviation SRCv := (@AFko.SRCv ly c n nf).
Local Abbreviation DSTv := (@AFko.DSTv ly c).
Local Abbreviation XWR := (@AFko.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E0 := (@AFko.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaT := (@AFko.EaT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaC := (@AFko.EaC ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaSB := (@AFko.EaSB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaTOP := (@AFko.EaTOP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaCL := (@AFko.EaCL ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaP := (@AFko.EaP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaMAX := (@AFko.EaMAX ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaN := (@AFko.EaN ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaCSZ := (@AFko.EaCSZ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaRG := (@AFko.EaRG ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaRB := (@AFko.EaRB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaFA := (@AFko.EaFA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaNF := (@AFko.EaNF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaMF := (@AFko.EaMF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaAU := (@AFko.EaAU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaMU := (@AFko.EaMU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaSHB := (@AFko.EaSHB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation Er := (@AFko.Er ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E2 := (@AFko.E2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E1 := (@AFko.E1 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E8 := (@AFko.E8 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
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
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Ha0 : getr regs0 10 = w64 (T + t_cache).
Hypothesis Ha1 : getr regs0 11 = w64 Pr.
Hypothesis Ha2 : getr regs0 12 = w64 A_ALLOCATOR.
Hypothesis Ha3 : getr regs0 13 = w64 c.
Local Abbreviation class_facts := (@AFko.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@AFko.high_factsR _ ly regs0 maxc mf au mu LY IMG Hmf Hmu).
Local Abbreviation off_T := (@AFko.off_T _ ly regs0 maxc mf au mu LY IMG Hmf Hmu).
Local Abbreviation off_C := (@AFko.off_C _ ly regs0 maxc mf au mu LY IMG Hmf Hmu).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation derived_rangesR := (@AFko.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation WINR0 := (@AFko.WINR0 ly regs0 c).
Local Abbreviation WINR := (@AFko.WINR ly regs0 c n).
Local Abbreviation WINR0_WINR := (@AFko.WINR0_WINR ly regs0 c n).
Local Abbreviation WSKELR := (@AFko.WSKELR).
Local Abbreviation win_sub := (@AFko.win_sub).
Local Abbreviation win_sub_sound := (@AFko.win_sub_sound ly regs0 c maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (@AFko.WSKELR_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation windows_WINR0 := (@AFko.windows_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_WINR0 := (@AFko.frame_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Ltac frame_accR HE :=
match goal with
| MEQ : (forall x : word, ~ WINR0 (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WINR0 (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WINR0 E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation at_R := (@AFko.at_R _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation at_RC := (@AFko.at_RC _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation at_RET2 := (@AFko.at_RET2 _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz).
Local Abbreviation all_disjoint_of_forall := (@AFko.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFko.kept_of_frame W ly regs0 maxc mf au mu).
Local Abbreviation SKEL_TAILR := (@AFko.SKEL_TAILR).
Local Abbreviation RFACTSR := (@AFko.RFACTSR ly regs0 c).
Local Abbreviation stack_ivsR := (@AFko.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := (@AFko.zone_litR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_TR := (@AFko.zone_TR _ ly regs0 c maxc mf au mu LY IMG Hmf Hmu Hsp).
Local Abbreviation zone_CR := (@AFko.zone_CR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_RGR := (@AFko.zone_RGR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation slots_not_WINR0 := (@AFko.slots_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation fa_not_WINR0 := (@AFko.fa_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation tail_ext_okR := (@AFko.tail_ext_okR _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R RJ2 W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := (@AFko.rdn_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation store_ok_of_presentR := (@AFko.store_ok_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation cpy4_stretch := (@AFko.cpy4_stretch _ W ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hchunks : pc_chunks (cache S c) = [].
Hypothesis Hnf_def : nf = fa_len (rg_free (reg S c)).
Hypothesis Hmf_def : mf = rg_mapped_fa (reg S c).
Hypothesis Hau_def : au = rg_alloc_user (reg S c).
Hypothesis Hmu_def : mu = rg_mapped_user (reg S c).
Hypothesis Hj64v : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 64) 4 j64.
Hypothesis Hjnav : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 72) 8 jna.
Hypothesis Hjnfv : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 80) 8 jnf.
Hypothesis Hjsmv : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2792) 8 jsm.
Hypothesis Hjm1v : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1.
Hypothesis Hjm2v : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2.
Hypothesis HQL : qloose S.
Local Abbreviation Pr_is := (@AFko.Pr_is ly c).
Local Abbreviation RGv_is := (@AFko.RGv_is ly c).
Local Abbreviation FAv_is := (@AFko.FAv_is ly c HcR).
Local Abbreviation RBv_is := (@AFko.RBv_is ly c HcR).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Lemma seg2J : forall mat, st_ok tfibsegs E0 SS0R (restrict (w_H W) (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) (at_R RJ2).
Proof.
intros mat HS. pose proof Hwx_tfa as Hwx.
assert (HEn0 : forall k, (k < aHAV)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
assert (MEQ : forall x : word, ~ WINR0 (bv_unsigned x) -> mem0 x = mem0 x) by (intros; reflexivity).
srr_run_to_sh tfibtbl_rtA_ok HS 0x36124. frame_accR HEn0.
match type of HS with st_ok _ _ ?ss (restrict _ ?msx) => rename msx into msJ'; set (ssJ := ss) in HS end.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists ms mt E', mkCfg _ (with_vm_backing _ ?matx _) = _ /\ _ => exists msJ', matx, (havoc E0 hJ0 (map (getr (ms_regs msJ')) CLOB_INIT)) end.
split; [reflexivity|].
split; [intros k Hk; unfold hJ0; rewrite ew_havoc_old by exact Hk; reflexivity|].
split.
{ pose proof (st_ok_forget hJ0 E0 ssJ (w_H W) msJ' CLOB_INIT HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as X'.
rewrite <- (st_ok_restrict_mkst tfibsegs (w_H W) E0 ssJ msJ' HS eq_refl) in X'.
apply (st_ok_prune _ _ _ _ [] []) in X'. match type of X' with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in X' end. exact X'. }
split; [exact MEQ|]. intros a Ha. pose proof Hsp as (Hlo & Hhi & Hal). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof high_factsR as LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha; numconst; try unfold sp0 in *; zlia
| off_by ltac:(pose proof stack_ivsR as SI; clear - Ha Hlo Hhi LF Usp T7 SI; numconst; try unfold sp0 in *; zlia) ].
Qed.
Lemma segB2 : n <= nf -> SRr tfibsegs W cfg0 at_RET2.
Proof.
intros Hnn. pose proof Hwx_tfa as Hwx.
destruct SEEDJ as (_ & msJ' & matJ & EJ & EcJ & HEnJ & HS & MEQ & PRS0). rewrite EcJ.
pose proof Hsp as (Hlo & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_rangesR as DR. pose proof high_factsR as LF. pose proof class_facts as (CF1 & CF2 & CF3 & CF4 & CF5).
pose proof Hnf as [NF1 NF2]. pose proof Hmf as [MF1 MF2]. pose proof Hmu as (MU1 & MU2 & MU3 & MU4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in DR, LF.
pose proof HEnJ as HEn0.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
srr_run_to_sh tfibtbl_rtA_ok HS 0x36128. frame_accR HEn0.
apply (st_ok_pin_regU _ _ _ 9%bv (SOff rN 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - CF1 CF2 CF3 Hn HEnJ. pin_zev. unfold rN, rMAX. rewrite !HEnJ by (cbv; zlia). rewrite EaN, EaMAX. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (maxc + 0)) by (unfold M64; zlia). rewrite (zcanon_id 1) by (unfold M64; zlia). rewrite (zcanon_id (n + 0)) by (unfold M64; zlia).
rewrite (Z.mod_small (maxc + 0)) by zlia. change (Z.land (1 mod 2 ^ 32) 31) with 1.
rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 1) with 2. rewrite !Z.add_0_r, <- Hn.
rewrite bv_swrap_small. 2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2) with 2147483648. zlia. }
rewrite bv_wrap_small. 2:{ unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. zlia. } reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x36284. frame_accR HEn0.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff rRG 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - SB DR LF HcR HEnJ. pin_zev. unfold rRG, rSB, rCL. rewrite !HEnJ by (cbv; zlia). rewrite EaRG, EaSB, EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 7) with 128. zcanon_simp. unfold RGv, kRegionInfoOff in *. unfold SB in *. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 20%bv (SOff rFA 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - SB DR LF HcR HEnJ. pin_zev. unfold rFA, rSB, rCL. rewrite !HEnJ by (cbv; zlia). rewrite EaFA, EaSB, EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. zcanon_simp. unfold FAv, RBv, kFreeArrayOffset in *. unfold SB in *. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtA_ok HS. frame_accR HEn0.
assert (ENF : U EJ (SOff 44 0) = nf) by (clear - NF1 NF2 MF1 HEnJ; apply U_atom; [rewrite (HEnJ 44%nat ltac:(cbv; zlia)); exact EaNF | unfold kFreeArrayMax in *; zlia]).
assert (ENN : U EJ (SOff 39 0) = n) by (clear - CF3 HEnJ; apply U_atom; [rewrite (HEnJ 39%nat ltac:(cbv; zlia)); exact EaN | zlia]).
srr_branch_sh tfibtbl_rtA_ok HS.
{ exfalso. clear - Hc ENF ENN Hnn. rewrite branch_ltu_U, ENF, ENN in Hc. apply Z.ltb_lt in Hc. zlia. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_accR HEn0.
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
assert (DPRES : forall a, DSTv <= a < DSTv + 4 * n -> apresent (w_H W) (ms_mem msC) a).
{ intros a Ha. apply (apresent_same (w_H W) mem0); [apply MEQ|apply HslotPres; clear - Ha CF3; zlia]. rewrite unsigned_lit_small by (clear - Ha DR CF3 LF; zlia).
apply slots_not_WINR0. clear - Ha CF3. zlia. }
assert (SPRES : forall a, SRCv <= a < SRCv + 4 * n -> apresent (w_H W) (ms_mem msC) a).
{ intros a Ha. apply (apresent_same (w_H W) mem0); [apply MEQ|apply HfaPres; clear - Ha DR Hnn; zlia]. rewrite unsigned_lit_small by (clear - Ha DR CF3 LF Hnn NF2 MF1; numconst; zlia).
apply fa_not_WINR0. clear - Ha DR Hnn NF2 MF1 CF3. unfold kFreeArrayMax in *. zlia. }
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
assert (DJ : DSTv + 4 * n <= SRCv \/ SRCv + 4 * n <= DSTv) by (clear - T SB DR LF Hnn NF2 MF1 CF3 PT; numconst; unfold T, SB in *; zlia).
assert (BD : 0 <= DSTv /\ DSTv + 4 * n < 2 ^ 64 /\ 0 <= SRCv /\ SRCv + 4 * n < 2 ^ 64)
by (clear - T SB DR LF Hnn NF2 MF1 CF3; numconst; unfold T, SB in *; zlia).
destruct BD as (BD1 & BD2 & BD3 & BD4).
assert (VSRC : sv_denot EJ (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit 18446744073709551612)) (SOff 43 0)) (SAlu ALU_SLL (SOff 44 0) (SLit 2))) = Z_to_bv 64 SRCv).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot EJ _)).
lazymatch goal with |- Z_to_bv 64 (bv_unsigned (sv_denot ?E ?t)) = _ => change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
apply Z_to_bv64_eq_mod. cbn [zev zalu_raw zmd_raw]. unfold rho_of. rewrite !HEnJ by (cbv; zlia). rewrite EaN, EaFA, EaNF. unfold w64. rewrite !unsigned_lit_small by (clear - DR LF CF3 NF1 NF2 MF1; numconst; zlia).
rewrite (zcanon_id (n + 0)), (zcanon_id 18446744073709551612), (zcanon_id (FAv + 0)), (zcanon_id (nf + 0)), (zcanon_id 2) by (clear - DR LF CF3 NF1 NF2 MF1; numconst; unfold M64; zlia).
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4. unfold zcanon, M64.
rewrite Z.mod_mod by zlia. rewrite (Zplus_mod_idemp_l (_ * 18446744073709551612)). rewrite <- (Z.add_mod _ _ (2 ^ 64)) by zlia.
replace ((n + 0) * 18446744073709551612 + (FAv + 0) + (nf + 0) * 4) with (SRCv + n * 2 ^ 64) by (clear - DR; zlia).
rewrite Z_mod_plus_full. reflexivity. }
cbn [sv_denot] in VSRC. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in VSRC.
assert (VEND : sv_denot EJ (SAlu ALU_ADD (SOff rP 16) (SAlu ALU_SLL (SOff rN 0) (SLit 2))) = Z_to_bv 64 (DSTv + 4 * n)).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot EJ _)).
lazymatch goal with |- Z_to_bv 64 (bv_unsigned (sv_denot ?E ?t)) = _ => change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
apply Z_to_bv64_eq_mod. cbn [zev zalu_raw zmd_raw]. unfold rho_of, rP, rN. rewrite !HEnJ by (cbv; zlia). rewrite EaN, EaP. unfold w64. rewrite !unsigned_lit_small by (clear - DR LF CF3; numconst; zlia).
rewrite (zcanon_id (Pr + 16)), (zcanon_id (n + 0)), (zcanon_id 2) by (clear - DR LF CF3; numconst; unfold M64; zlia).
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4. rewrite (zcanon_id ((n + 0) * 4)) by (clear - CF3; unfold M64; zlia).
unfold zcanon, M64. rewrite Z.mod_mod by zlia. f_equal. clear - DR; zlia. }
cbn [sv_denot] in VEND. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in VEND.
eapply (cpy4_stretch hCP2 EJ _ _ _ DSTv SRCv (4 * n));
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| rreg HS (20%bv : bv 5) R; rewrite R; exact VSRC
| rreg HS (13%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite (HEnJ 37%nat ltac:(cbv; zlia)), EaP; unfold w64; rewrite Zbv_add_unsigned; reflexivity
| rreg HS (11%bv : bv 5) R; rewrite R; exact VEND
| clear - CF3; zlia | clear - CF3; rewrite Z.mul_comm; apply Z_mod_mult
| exact BD1 | exact BD2 | exact BD3 | exact BD4 | exact DJ
| exact DPRES | exact SPRES
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|Hr];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; pose proof stack_ivsR as SI; rewrite (HEnJ 2%nat (ltHAV 2 eq_refl)); clear - DR LF Hlo Hhi Usp SI DJ BD1 BD2 BD3 BD4 CF3 T SB HEnJ;
rewrite E2; numconst; try unfold sp0 in *; unfold T, SB in *; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILR in Hr by (vm_compute; reflexivity) end;
pose proof (tail_ext_okR EJ r HEnJ Hr) as (X1 & X2 & X3 & X4 & X5); clear - DR LF X1 X2 X3 X4 X5 CF3; numconst; zlia ].
intros regs3 mem3 mat3 HS3 Hfr3 Hpr3 Hcp3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En := E) in HS; let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (HEn : forall k, (k < aHAV)%nat -> ew En k = ew E0 k) by (intros k Hk; subst En; unfold hCP2; rewrite ew_havoc_old by (clear - Hk; unfold aHAV in Hk; zlia); exact (HEnJ k Hk)).
rename MEQ into MEQC.
assert (MEQ : forall x : word, ~ WINR0 (bv_unsigned x) -> mem3 x = mem3 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_accR HEn.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W En); [exact HS | reflexivity | vm_compute; reflexivity |].
intros matZ. match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
assert (CH : forall x : word, ~ WINR0 (bv_unsigned x) -> ~ (DSTv <= bv_unsigned x < DSTv + 4 * n) -> ms_mem msZ x = mem0 x).
{ intros x NA NB. rewrite (MEQ x NA), (Hfr3 x NB). apply MEQC. exact NA. }
assert (PCH : forall a, 0 <= a < 2 ^ 64 -> ~ WINR0 a -> apresent (w_H W) (ms_mem msC) a -> apresent (w_H W) (ms_mem msZ) a).
{ intros a Ra NA Hp. apply (apresent_same (w_H W) mem3); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact NA|]. apply Hpr3. exact Hp. }
split; [reflexivity|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [reflexivity|].
split. { rreg HS (10%bv : bv 5) R; rewrite R. reflexivity. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
first [ rewrite (HEn k (ltHAV k eq_refl)); symmetry; exact (Er k r eq_refl) | symmetry; exact Htp ] end. }
split. { intros x NW. apply CH; intros H1; apply NW; [left; exact H1 | right; exact H1]. }
split. {   intros a Ha.
eapply (st_ok_window_apresent_off (w_H W) En _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; clear - Ha; numconst; try unfold sp0 in *; zlia | off_by ltac:(pose proof stack_ivsR as SI; clear - Ha Hlo Hhi LF Usp T7 SI; numconst; try unfold sp0 in *; zlia) ]. }
split. {   intros a Ha. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- eapply (st_ok_window_apresent_off (w_H W) En _ _ 35 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rP; rewrite (HEn 37%nat (ltHAV 37 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Ha DR LF; numconst; zlia) ].
- apply PCH; [clear - Ha DR LF CF3; numconst; zlia | apply slots_not_WINR0; clear - Ha CF3; zlia | apply DPRES; exact Ha].
- eapply (st_ok_window_apresent_off (w_H W) En _ _ 36 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rRG; rewrite (HEn 41%nat (ltHAV 41 eq_refl)), EaRG; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Ha DR LF; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En _ _ 33 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rT; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - T DR LF; numconst; unfold T in *; zlia); unfold T in *; zlia | off_by ltac:(clear - T Ha DR LF; numconst; unfold T in *; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En _ _ 34 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rT; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - T DR LF; numconst; unfold T in *; zlia); unfold T in *; zlia | off_by ltac:(clear - T Ha DR LF; numconst; unfold T in *; zlia) ]. }
split. {   intros k Hk. unfold w64. rewrite (MEQ (Z_to_bv 64 (DSTv + k))).
2:{ rewrite unsigned_lit_small by (clear - Hk DR LF CF3; numconst; zlia). apply slots_not_WINR0. clear - Hk CF3; zlia. }
pose proof (Hcp3 k Hk) as CP. unfold w64 in CP. rewrite CP. apply MEQC. rewrite unsigned_lit_small by (clear - Hk DR LF CF3 Hnn NF2 MF1; numconst; zlia).
apply fa_not_WINR0. clear - Hk DR Hnn NF2 MF1 CF3; numconst; zlia. }
cbv zeta.
assert (RP : 0 <= Pr /\ Pr + 16 < 2 ^ 64) by (clear - DR LF; numconst; zlia).
assert (RR : 0 <= RGv /\ RGv + 128 < 2 ^ 64) by (clear - DR LF; numconst; zlia).
Ltac memvP HS HEn j := memv HS 35%nat j; [cbn [base_val YP09.r_base]; unfold rP; rewrite (HEn 37%nat (ltHAV 37 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by zlia; zlia | | ].
Ltac memvR HS HEn j := memv HS 36%nat j; [cbn [base_val YP09.r_base]; unfold rRG; rewrite (HEn 41%nat (ltHAV 41 eq_refl)), EaRG; unfold w64; rewrite unsigned_lit_small by zlia; zlia | | ].
split. { memvP HS HEn 0%nat; [cbn [sv_denot]; unfold rN; rewrite (HEn 39%nat (ltHAV 39 eq_refl)), EaN; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity | clear - CF3; zlia]. }
split. { memvP HS HEn 1%nat; [cbn [sv_denot]; unfold rMAX; rewrite (HEn 38%nat (ltHAV 38 eq_refl)), EaMAX; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity | clear - CF1; zlia]. }
split. { memvP HS HEn 2%nat; [cbn [sv_denot]; unfold rCSZ; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaCSZ; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity | clear - CF4; numconst; zlia]. }
split. { memvR HS HEn 0%nat; [reflexivity | zlia]. }
split. { memvR HS HEn 3%nat; [reflexivity | zlia]. }
split. { memvR HS HEn 2%nat; [| clear - Hnn NF1 NF2 MF1 CF3; numconst; zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw zmd_raw]. unfold rho_of. rewrite (HEn 39%nat (ltHAV 39 eq_refl)), (HEn 44%nat (ltHAV 44 eq_refl)), EaN, EaNF. unfold w64.
rewrite !unsigned_lit_small by (clear - CF3 NF1 NF2 MF1; numconst; zlia).
rewrite (zcanon_id (n + 0)), (zcanon_id (nf + 0)) by (clear - CF3 NF1 NF2 MF1; numconst; unfold M64; zlia).
unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite (Zplus_mod_idemp_l ((n + 0) * (2 ^ 64 - 1))). replace ((n + 0) * (2 ^ 64 - 1) + (nf + 0)) with ((nf - n) + n * 2 ^ 64) by zlia.
rewrite Z_mod_plus_full. apply Z.mod_small. clear - Hnn CF3 NF1 NF2 MF1; numconst; zlia. }
split. { memvR HS HEn 4%nat; [cbn [sv_denot]; unfold rMF; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaMF; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity | clear - MF1; numconst; zlia]. }
split. { memvR HS HEn 5%nat; [cbn [sv_denot]; unfold rAU; rewrite (HEn 46%nat (ltHAV 46 eq_refl)), EaAU; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity | clear - MU1 MU2; numconst; zlia]. }
split. { memvR HS HEn 6%nat; [reflexivity | zlia]. }
split. { memvR HS HEn 7%nat; [cbn [sv_denot]; unfold rMU; rewrite (HEn 47%nat (ltHAV 47 eq_refl)), EaMU; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity | clear - MU1 MU2; numconst; zlia]. }
split. { memvR HS HEn 8%nat; [reflexivity | zlia]. }
memvR HS HEn 10%nat; [reflexivity | zlia].
Qed.
End e.
End d.

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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFl1 AFhy AFis AFkp AFko AFhz AFkr AFhm AFks AFkx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
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
Section z.
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
Local Abbreviation cls_wfR := (@AFkx.cls_wfR _ W ly mem0 c HcR B S HARm Hinited).
Local Abbreviation cls_wf0 := (@AFkx.cls_wf0 _ W ly mem0 c HcR B S HARm).
Local Abbreviation reg_facts0 := (@AFkx.reg_facts0 _ W ly regs0 mem0 c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_facts := (@AFkx.reg_facts _ W ly regs0 mem0 c maxc nf mf au mu HcR Hmax Hsp B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (@AFkx.Hnf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmf' := (@AFkx.Hmf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmu' := (@AFkx.Hmu' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation vis_present := (@AFkx.vis_present _ W ly regs0 mem0 maxc B S HARm).
Local Abbreviation thread_present := (@AFkx.thread_present _ W ly regs0 mem0 c maxc nf mf au mu LY IMG HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation rinfo_present := (@AFkx.rinfo_present _ W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HslotPres' := (@AFkx.HslotPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HfaPres' := (@AFkx.HfaPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation word_of_present := (@AFkx.word_of_present W ly regs0 mem0 maxc).
Local Abbreviation val_mem_lo4 := (@AFkx.val_mem_lo4 ly regs0 maxc).
Local Abbreviation junk_valuesR := (@AFkx.junk_valuesR _ W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation cell_sym := (@AFkx.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@AFkx.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@AFkx.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_cache := (@AFkx.In_acells_cache ly regs0 c maxc HcR B S).
Local Abbreviation In_acells_region := (@AFkx.In_acells_region ly regs0 c maxc HcR B S).
Local Abbreviation cache_valsR := (@AFkx.cache_valsR _ W ly regs0 mem0 c maxc csz HcR Hmax Hcsz B S HARm Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@AFkx.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (@AFkx.cache_valsU _ W ly regs0 mem0 maxc B S HARm).
Local Abbreviation region_valsR := (@AFkx.region_valsR _ W ly regs0 mem0 c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation chunk_lit := (@AFkx.chunk_lit W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation chunk_lit_at := (@AFkx.chunk_lit_at W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation chunk_atom := (@AFkx.chunk_atom W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation REG0R_ok_but35 := (@AFkx.REG0R_ok_but35 _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0R_ok := (@AFkx.REG0R_ok _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0U_ok := (@AFkx.REG0U_ok _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSR_ok := (@AFkx.PAIRSR_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SPAN_disj := (@AFkx.SPAN_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation FACTSR_ok := (@AFkx.FACTSR_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Local Abbreviation SEEDR_ok := (@AFkx.SEEDR_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSU_ok := (@AFkx.PAIRSU_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEEDU_ok := (@AFkx.SEEDU_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
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
Local Open Scope am_scope.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let m0 := mrestrict (w_H W) mem0.
Lemma zrange_dec : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. clear.
intros lo hi a. destruct (Z_le_dec lo a) as [H1|H1]; [destruct (Z_lt_dec a hi) as [H2|H2]; [left; exact (conj H1 H2) | right; intros [_ H]; exact (H2 H)] | right; intros [H _]; exact (H1 H)].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. clear. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; exact H. Qed.
Lemma val_mem_cell : forall mem e (w : nat) e',
val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview tfibsegs (w_H W) mem) (ACell e w (AV e')).
Proof.
intros mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [reflexivity|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. zlia.
Qed.
Lemma val_mem_at : forall (m : word -> option byte) a a' (w : nat) x, a = a' -> val_mem tfibsegs m a' w x -> val_mem tfibsegs m a w x.
Proof. clear. intros m a a' w x -> H. exact H. Qed.
Lemma nth_error_run_elems : forall m lo sz j, (j < m)%nat -> nth_error (run_elems lo sz m) j = Some (lo + Z.of_nat j * sz).
Proof. clear.
induction m as [|m IH]; intros lo sz j Hj; [zlia|]. cbn [run_elems]. destruct j as [|j]; cbn [nth_error]; [f_equal; zlia|].
rewrite IH by zlia. f_equal. zlia.
Qed.
Lemma fa_nth_elems : forall sz fl j, runs_ok fl -> 0 <= j -> fa_nth sz fl j = nth_error (fa_elems sz fl) (Z.to_nat j).
Proof. clear.
intros sz fl. induction fl as [|[lo k|o] t IH]; intros j Hr Hj.
- cbn. destruct (Z.to_nat j); reflexivity.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_run.
destruct (Z.ltb_spec j k).
+ rewrite nth_error_app1 by (rewrite run_elems_length; zlia). rewrite nth_error_run_elems by zlia. f_equal. rewrite Z2Nat.id by zlia. reflexivity.
+ rewrite nth_error_app2 by (rewrite run_elems_length; zlia). rewrite run_elems_length. rewrite IH by (assumption || zlia). f_equal. zlia.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_one. destruct (Z.eqb_spec j 0) as [->|Hne]; [reflexivity|].
replace (Z.to_nat j) with (Datatypes.S (Z.to_nat (j - 1))) by zlia. cbn [nth_error]. apply IH; [assumption | zlia].
Qed.
Lemma in_combine_seq : forall (l0 : list Z) (s i : nat) vv, In (i, vv) (combine (seq s (length l0)) l0) -> (s <= i)%nat /\ nth_error l0 (i - s) = Some vv.
Proof. clear.
induction l0 as [|y t IH]; intros s i vv H; [destruct H|]. cbn [length combine seq] in H. destruct H as [H|H].
- injection H as <- <-. split; [zlia|]. rewrite Nat.sub_diag. reflexivity.
- destruct (IH _ _ _ H) as [H1 H2]. split; [zlia|]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by zlia. cbn [nth_error]. exact H2.
Qed.
Lemma flat_map_ext_in {X Y} : forall (f g : X -> list Y) (l0 : list X), (forall x, In x l0 -> f x = g x) -> flat_map f l0 = flat_map g l0.
Proof. clear.
intros f g l0. induction l0 as [|x t IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.
Lemma nth_error_rev : forall (l0 : list Z) i, (i < length l0)%nat -> nth_error (rev l0) i = nth_error l0 (length l0 - 1 - i).
Proof. clear.
intros l0 i Hi. rewrite (nth_error_nth' (rev l0) 0) by (rewrite length_rev; exact Hi). rewrite (nth_error_nth' l0 0) by zlia.
f_equal. rewrite rev_nth by exact Hi. f_equal. zlia.
Qed.
Definition r_new (rest : list fseg) : region := mkRegion mu au mf rest (rg_holes (reg S c)).
Definition SRf (tops : list Z) (rest : list fseg) : astate := upd_pc c (mkPC maxc (rev tops)) (upd_reg c (r_new rest) S).
Lemma len_facts : length (st_regions S) = 32%nat /\ length (st_cache S) = 32%nat /\ (Z.to_nat c < 32)%nat.
Proof. pose proof (wf_len_regions _ _ _ _ _ WF). pose proof (wf_len_cache _ _ _ _ _ WF). repeat split; try assumption. zlia. Qed.
Lemma refill_B2_model : n <= nf -> exists tops rest,
fa_pop_n 10000 (class_size c) n (rg_free (reg S c)) [] = Some (tops, rest) /\
refill_tree c S = IRet (tt, SRf tops rest) /\
Wf (as_universe B) (SRf tops rest) /\
fa_elems (class_size c) (rg_free (reg S c)) = tops ++ fa_elems (class_size c) rest /\
Z.of_nat (length tops) = n /\ fa_len rest = nf - n /\ runs_ok rest.
Proof.
intros Hle. pose proof reg_facts as (_ & _ & _ & PM & RU). pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof len_facts as (L1 & L2 & L3).
destruct (fa_pop_n_some 10000 (class_size c) n (rg_free (reg S c)) [] RU ltac:(rewrite <- Hnf_def; zlia) ltac:(change (Z.of_nat 10000) with 10000; zlia)) as (tops & rest & EP).
destruct (fa_pop_n_spec 10000 (class_size c) n (rg_free (reg S c)) [] tops rest RU ltac:(zlia) EP) as (E1 & E2 & E3 & E4). cbn [rev app length] in E1, E4. rewrite <- Hnf_def in E2.
exists tops, rest. split; [exact EP|]. split; [|split; [|repeat split; try assumption; zlia]].
-
unfold refill_tree. unfold bind at 1. unfold init_cache_if_needed, bind, get. cbn [ibind]. rewrite Hinited. unfold ret at 1. cbn [ibind].
unfold refill_if_empty. unfold bind at 1. unfold get_pc, bind at 1, get, ret at 1. cbn [ibind].
change (znth pclass0 c (st_cache S)) with (cache S c). rewrite Hchunks. rewrite PM, <- Hn. unfold bind at 1.
unfold get_from_allocator. unfold bind at 1. unfold get_region at 1. unfold bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite <- Hnf_def.
replace (nf <? n) with false by (symmetry; apply Z.ltb_ge; zlia). unfold bind at 1, ret at 1. cbn [ibind negb].
unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind]. change (znth region0 c (st_regions S)) with (reg S c). rewrite <- Hnf_def.
replace (nf <? n) with false by (symmetry; apply Z.ltb_ge; zlia). rewrite EP.
unfold bind, set_region, modify, ret. cbn [ibind]. unfold set_pc, modify. unfold SRf, upd_pc, upd_reg, r_new, cache_fill_order.
rewrite Hmu_def, Hau_def, Hmf_def. reflexivity.
-
pose proof cls_wfR as C0.
unfold SRf. eapply (WfP_set_region_pc (as_universe B) 0 0 0 S c); [exact WF | exact HcR | | zlia | | |].
+ rewrite Hinited. eapply (cls_ok_repart c (reg S c) (cache S c) true _ _ (r_new rest) _ true _ _ []); try exact C0; try reflexivity.
* unfold r_new. cbn. exact Hmu_def.
* unfold r_new. cbn. exact Hau_def.
* unfold r_new. cbn. exact Hmf_def.
* exact E3.
* unfold r_new. cbn [rg_free]. rewrite <- Hmf_def. pose proof Hnf as [_ N2]. zlia.
* cbn [pc_max pc_chunks]. split; [exact Hmax|]. rewrite length_rev, <- Hmax. assert (n <= maxc) by (rewrite Hn; apply Z.div_le_upper_bound; zlia). zlia.
* unfold r_new. cbn [rg_free pc_chunks]. rewrite E1, Hchunks. exact (perm_cache_refill (fa_elems (class_size c) rest) [] (chunk_offs S c) (batch_offs S c) tops).
+ unfold r_new. cbn [rg_mapped_user]. rewrite <- Hmu_def. pose proof (wf_prim_ev _ _ _ _ _ WF). zlia.
+
pose proof (wf_fa_room _ _ _ _ _ WF c HcR) as RM. unfold class_elems in RM. rewrite E1, Hchunks in RM.
rewrite <- Hau_def, <- Hmf_def in RM. unfold r_new. cbn [rg_alloc_user rg_mapped_fa rg_free pc_chunks].
eapply fa_room_xfer; [exact RM | rewrite !length_app, length_rev; cbn [length]; zlia | apply Z.le_refl].
+
apply (regime_cap_keep (as_universe B) 0 0 0 S c _ WF HcR); unfold r_new; cbn [rg_alloc_user rg_mapped_fa]; [exact Hau_def | rewrite <- Hmf_def; zlia].
Qed.
Lemma SR_parts : forall tops rest,
(forall c', 0 <= c' -> c' <> c -> reg (SRf tops rest) c' = reg S c') /\ reg (SRf tops rest) c = r_new rest /\
st_cache_inited (SRf tops rest) = st_cache_inited S /\
(forall c', 0 <= c' -> c' <> c -> cache (SRf tops rest) c' = cache S c') /\ cache (SRf tops rest) c = mkPC maxc (rev tops) /\
st_chunks (SRf tops rest) = st_chunks S /\ st_secs (SRf tops rest) = st_secs S /\ frames (SRf tops rest) = frames S /\
st_qthread (SRf tops rest) = st_qthread S /\ st_qglobal (SRf tops rest) = st_qglobal S /\ st_fs (SRf tops rest) = st_fs S /\
st_internal_inited (SRf tops rest) = st_internal_inited S /\ st_sec_arr (SRf tops rest) = st_sec_arr S /\
st_sec_reserved (SRf tops rest) = st_sec_reserved S /\ st_depot (SRf tops rest) = st_depot S /\ st_nev (SRf tops rest) = st_nev S.
Proof.
intros tops rest. pose proof len_facts as (L1 & L2 & L3). unfold SRf, upd_pc, upd_reg. repeat split; try reflexivity.
- intros c' Hc' Hne. unfold reg. cbn. apply znth_zupd_other; [zlia | exact Hc' | congruence].
- unfold reg. cbn. apply znth_zupd_same; [zlia | rewrite L1; exact L3].
- intros c' Hc' Hne. unfold cache. cbn. apply znth_zupd_other; [zlia | exact Hc' | congruence].
- unfold cache. cbn. apply znth_zupd_same; [zlia | rewrite L2; exact L3].
Qed.
Lemma SR_sec_extents : forall tops rest, sec_extents ly (SRf tops rest) = sec_extents ly S.
Proof. intros. reflexivity. Qed.
Lemma SR_ledger : forall tops rest md, ALedger tfibsegs ly S md -> ALedger tfibsegs ly (SRf tops rest) md.
Proof.
intros tops rest md L. pose proof (SR_parts tops rest) as (Rreg & Rc & _). assert (Rnev : st_nev (SRf tops rest) = st_nev S) by (unfold SRf, upd_pc, upd_reg; reflexivity). destruct L as [L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10].
assert (RGEQ : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg (SRf tops rest) c') = rg_mapped_user (reg S c') /\
rg_mapped_fa (reg (SRf tops rest) c') = rg_mapped_fa (reg S c') /\ rg_holes (reg (SRf tops rest) c') = rg_holes (reg S c')).
{ intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite Rc; unfold r_new; cbn; rewrite <- Hmu_def, <- Hmf_def; repeat split; reflexivity | rewrite (Rreg c') by zlia; repeat split; reflexivity]. }
assert (CUT : forall x, cut_ok ly (SRf tops rest) x <-> cut_ok ly S x).
{ intros x. unfold cut_ok. split; (intros [H|[H|(c' & Hc' & H)]]; [left; exact H | right; left; exact H | right; right; exists c'; split; [exact Hc'|]]);
destruct (RGEQ c' Hc') as (Q1 & Q2 & Q3); [rewrite <- Q1, <- Q2 | rewrite Q1, Q2]; exact H. }
assert (HOLE : forall a, prim_hole_at ly (SRf tops rest) a <-> prim_hole_at ly S a).
{ intros a. unfold prim_hole_at. split; intros (c' & h & Hc' & Hin & H); exists c', h; destruct (RGEQ c' Hc') as (Q1 & Q2 & Q3);
[rewrite <- Q3 | rewrite Q3]; (split; [exact Hc' | split; [exact Hin | exact H]]). }
assert (PC : prim_committed (SRf tops rest) = prim_committed S).
{ pose proof len_facts as (L1' & _ & L3'). unfold SRf, upd_pc, upd_reg.
match goal with |- context [prim_committed (set_cache ?x ?s)] => change (prim_committed (set_cache x s)) with (prim_committed s) end.
rewrite prim_committed_set_region by (zlia || (rewrite L1'; exact L3')). unfold r_new. cbn [rg_mapped_user rg_mapped_fa]. rewrite <- Hmu_def, <- Hmf_def. zlia. }
constructor; try assumption.
- destruct L3 as (pieces & (Q1 & Q2 & Q3) & P2). exists pieces. split; [|exact P2]. split; [|split; [exact Q2|]].
+ apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) Q1 p Hp) as (A1 & A2 & A3). split; [exact A1|]. split; apply CUT; assumption.
+ intros a Ha. rewrite (Q3 a Ha). rewrite HOLE. tauto.
- rewrite PC. exact L8.
Qed.
Section a0.
Variables (tops : list Z) (rest : list fseg) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Let rd' : reader := aview tfibsegs (w_H W) mem'.
Let m' := mrestrict (w_H W) mem'.
Local Notation SR := (SRf tops rest).
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis Hnle : n <= nf.
Hypothesis WFR : Wf (as_universe B) SR.
Hypothesis E_elems : fa_elems (class_size c) (rg_free (reg S c)) = tops ++ fa_elems (class_size c) rest.
Hypothesis E_len : Z.of_nat (length tops) = n.
Hypothesis E_rest : fa_len rest = nf - n.
Hypothesis E_runs : runs_ok rest.
Hypothesis MEQ : forall x : word, ~ WINR (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis PRS : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem' a.
Hypothesis PRW : forall a, (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 4 * n) \/ (RGv <= a < RGv + 128) \/
(T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) mem' a.
Hypothesis CPY : forall k, 0 <= k < 4 * n -> mem' (w64 (DSTv + k)) = mem0 (w64 (SRCv + k)).
Hypotheses (V1 : val_mem tfibsegs m' Pr 4 n) (V2 : val_mem tfibsegs m' (Pr + 4) 4 maxc) (V3 : val_mem tfibsegs m' (Pr + 8) 8 csz)
(V4 : val_mem tfibsegs m' RGv 8 0) (V5 : val_mem tfibsegs m' (RGv + 8) 8 0) (V6 : val_mem tfibsegs m' (RGv + 16) 8 (nf - n))
(V7 : val_mem tfibsegs m' (RGv + 24) 8 mf) (V8 : val_mem tfibsegs m' (RGv + 32) 8 au) (V9 : val_mem tfibsegs m' (RGv + 40) 8 0)
(V10 : val_mem tfibsegs m' (RGv + 48) 8 mu) (V11 : val_mem tfibsegs m' (RGv + 56) 8 0) (V12 : val_mem tfibsegs m' (RGv + 68) 1 0).
Let MA : ARm B ly S rd0 := proj1 HAR.
Definition XC (a : Z) : Prop :=
(Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 4 * n) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888).
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - RSTACK <= a < sp0) -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ra N1 N2. unfold rd', rd0. apply aview_same. apply MEQ. rewrite unsigned_lit_small by exact Ra.
unfold WINR, WINR0. unfold XC in N2. intros [[Hw|[Hw|[Hw|[Hw|Hw]]]]|Hw]; tauto.
Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfibsegs B ly S W mem0 md0 a HAR Ho) as Ra.
ceil.
pose proof (AR_stack_law_ok tfibsegs B ly S W mem0 md0 a HAR) as NS. destruct Hsp as (S1 & S3 & S4).
apply AGREE0; [clear - Ra; zlia | | exact Hx].
intros Hs. apply NS; [|exact Ho]. clear - Hs S1 S3. unfold RSTACK, sp0 in *. zlia.
Qed.
Lemma XC_where : forall a, XC a -> (T <= a < T + kThreadObjSize /\ T + t_cache + 80 * c <= a) \/ (RGv <= a < RGv + 128).
Proof.
intros a Hx. pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). unfold XC, DSTv in Hx.
clear - Hx DR K3. unfold Pr in *. numconst. unfold T in *. decompose [or] Hx; clear Hx; first [right; zlia | left; zlia].
Qed.
Lemma Z_low : forall a, (0x10000 <= a < 0x5fb000 \/ 0x7fff7000 <= a < 0x10007fff8000) -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & _). pose proof derived_rangesR as DR.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH.
clear - Ha Hx TI TH DR. numconst. unfold T in *. zlia.
Qed.
Lemma Z_T : forall a, T <= a < T + kThreadObjSize -> (a < T + t_cache + 80 * c \/ Pr + 16 + 4 * n <= a) -> ~ (T + 2768 <= a < T + 2800) -> ~ (T + 2872 <= a < T + 2888) -> ~ XC a.
Proof.
intros a Ha H1 H2 H3 Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof class_facts as (_ & _ & K3 & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold XC, DSTv in Hx. clear - Ha H1 H2 H3 Hx DR F1 F2 F3 F4 F5 F6 PT K3. unfold Pr in *. numconst. unfold T in *. zlia.
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (RGv <= a < RGv + 128) -> ~ XC a.
Proof.
intros a Ha HR Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
clear - Ha HR Hx F1 PT. numconst. unfold T in *. zlia.
Qed.
Lemma Z_high : forall a, ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) -> ~ XC a.
Proof.
intros a NT NP Hx. apply XC_where in Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
clear - NT NP Hx DR F5. numconst. zlia.
Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6)%nat ->
fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros i e a He Hi Ha. pose proof (lo_app ly LY) as HI. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ i _ HI He) as IH. cbv beta in IH. unfold in_app in IH.
assert (D : forall j e', nth_error (owned_extents ly) j = Some e' -> (j = 0 \/ j = 2)%nat -> zdisjoint e e').
{ intros j e' He' Hj. unfold static_extents in HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto).
destruct (Nat.lt_ge_cases i j) as [L|L].
- replace j with (i + Datatypes.S (j - i - 1))%nat in He' by zlia. exact (pairwise_ij _ _ _ _ _ _ HD' He He').
- apply zdisjoint_sym. assert (j <> i) by (intros ->; zlia). replace i with (j + Datatypes.S (i - j - 1))%nat in He by zlia. exact (pairwise_ij _ _ _ _ _ _ HD' He' He). }
pose proof (D 0%nat _ eq_refl ltac:(zlia)) as D0. pose proof (D 2%nat _ eq_refl ltac:(zlia)) as D2.
unfold zdisjoint in D0, D2. cbn [fst snd] in D0, D2.
apply Z_high; unfold T in *; clear - Ha D0 D2; numconst; zlia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros e a He Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (owned_extents ly) -> zdisjoint e e').
{ intros e' He'. exact (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He ltac:(unfold static_extents; apply in_app_iff; left; exact He')). }
pose proof (D (ly_prim ly, kPrimResvSize) ltac:(unfold owned_extents; cbn; tauto)) as D0.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as D2.
unfold zdisjoint in D0, D2. cbn [fst snd] in D0, D2.
apply Z_high; unfold T in *; clear - Ha D0 D2; numconst; zlia.
Qed.
Lemma Z_user : forall c' x a, 1 <= c' <= 31 -> 0 <= x -> x <= 2 ^ 32 -> region_base ly c' <= a < region_base ly c' + x -> ~ XC a.
Proof.
intros c' x a Hc' Hx0 Hx Ha. pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _). pose proof derived_rangesR as DR.
apply Z_prim.
- clear - Hx0 Hx Ha R1 R2. zlia.
- unfold region_base in Ha. rewrite region_off_eq in Ha by zlia. unfold RGv, SB in *. clear - Hc' Hx0 Hx Ha HcR. numconst. zlia.
Qed.
Lemma PRES_MONO : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem' a.
Proof.
assert (G : forall u, 0 <= u < 2 ^ 64 -> apresent (w_H W) mem0 u -> apresent (w_H W) mem' u).
{ clear - MEQ PRS PRW T. intros u Ru Hp.
destruct (zrange_dec (sp0 - RSTACK) sp0 u) as [D0|D0]; [apply PRS; exact D0|].
destruct (zrange_dec Pr (Pr + 16) u) as [D1|D1]; [apply PRW; tauto|].
destruct (zrange_dec DSTv (DSTv + 4 * n) u) as [D2|D2]; [apply PRW; tauto|].
destruct (zrange_dec RGv (RGv + 128) u) as [D3|D3]; [apply PRW; tauto|].
destruct (zrange_dec (T + 2768) (T + 2800) u) as [D4|D4]; [apply PRW; tauto|].
destruct (zrange_dec (T + 2872) (T + 2888) u) as [D5|D5]; [apply PRW; tauto|].
eapply apresent_same; [|exact Hp]. apply MEQ. rewrite unsigned_lit_small by exact Ru. unfold WINR, WINR0. tauto. }
intros a Hp. apply (proj2 (apresent_word _ _ a)). apply G; [pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R|].
apply (proj1 (apresent_word _ _ a)). exact Hp.
Qed.
Lemma BANDKEEP : forall a, 0 <= a < 2 ^ 64 -> mem' (w64 a) = mem0 (w64 a) \/ apresent (w_H W) mem' a.
Proof.
clear - MEQ PRS PRW T. intros a Ra.
destruct (zrange_dec (sp0 - RSTACK) sp0 a) as [D0|D0]; [right; exact (PRS a D0)|].
destruct (zrange_dec Pr (Pr + 16) a) as [D1|D1]; [right; apply PRW; tauto|].
destruct (zrange_dec DSTv (DSTv + 4 * n) a) as [D2|D2]; [right; apply PRW; tauto|].
destruct (zrange_dec RGv (RGv + 128) a) as [D3|D3]; [right; apply PRW; tauto|].
destruct (zrange_dec (T + 2768) (T + 2800) a) as [D4|D4]; [right; apply PRW; tauto|].
destruct (zrange_dec (T + 2872) (T + 2888) a) as [D5|D5]; [right; apply PRW; tauto|].
left. apply MEQ. unfold w64. rewrite unsigned_lit_small by exact Ra. unfold WINR, WINR0. tauto.
Qed.
Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a HV. unfold rd', rd0, aview, mbyte in *.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H W) mem' (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp : apresent (w_H W) mem0 a).
{ unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [exfalso; apply HV; reflexivity|].
split; [reflexivity|]. destruct (mem0 (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply HV; reflexivity]. }
destruct (PRES_MONO a Hp) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma apresent_vis : forall a, apresent (w_H W) mem' a -> rd' a <> None.
Proof. intros a [Hh [b Hb]]. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma aview_copy : forall a b, apresent (w_H W) mem' a -> apresent (w_H W) mem0 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
mem' (w64 a) = mem0 (w64 b) -> rd' a = rd0 b.
Proof.
intros a b [Ha _] [Hb [xb Hxb]] Ra Rb E. unfold rd', rd0, aview, mbyte, mrestrict. unfold w64 in E. rewrite Ha, Hb, E, Hxb. reflexivity.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun cc => lo <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. apply Forall_forall. intros cc Hc.
pose proof (proj1 (Forall_forall _ _) RNG cc Hc) as [R1 R2]. cbv beta in R1, R2.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc))|].
intros k Hk. apply AGX.
- exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- apply LOC. zlia.
Qed.
Lemma keep_cell : forall cc lo len, loc_ok lo len -> In cc (acells B ly S) ->
lo <= aeval B ly (c_at cc) -> aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len -> cell_holds B ly rd' cc.
Proof.
intros cc lo len LOC Hc R1 R2. exact (proj1 (Forall_forall _ _) (keep_cells [cc] lo len LOC ltac:(intros x [<-|[]]; exact Hc) ltac:(constructor; [split; assumption | constructor])) cc (or_introl eq_refl)).
Qed.
Ltac fcons' := apply Forall_cons; [cbn; zlia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells SR) (zseq 1 31)).
Proof.
pose proof (SR_parts tops rest) as (Rreg & Rc & _). apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof derived_rangesR as DR.
destruct (Z.eq_dec c' c) as [->|Hne].
-
unfold region_cells. rewrite Rc. unfold r_new. cbn [rg_free rg_mapped_fa rg_alloc_user rg_mapped_user]. rewrite E_rest.
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = RGv + d) by (intros d; cbn; unfold RGv, SB; zlia).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = RGv + 0) by (cbn; unfold RGv, SB; zlia).
repeat (apply Forall_cons; [apply val_mem_cell; rewrite ?ER, ?ER0; cbn [aeval];
first [ exact (val_mem_at m' _ _ _ _ (Z.add_0_r RGv) V4) | exact V5 | exact V6 | exact V7 | exact V8 | exact V9 | exact V10 | exact V11 | exact V12 ] |]).
apply Forall_nil.
- replace (region_cells SR c') with (region_cells S c') by (unfold region_cells; rewrite (Rreg c') by zlia; reflexivity).
apply (keep_cells _ (ly_space ly + kRegionInfoOff + 128 * c') 128).
+ intros a Ha. apply Z_prim; unfold RGv, SB in *; clear - Ha Hc' Hne F3 F4 F5 DR; numconst; zlia.
+ intros x Hx. unfold acells. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; zlia | exact Hx].
+ unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
Lemma slot_cell : forall (i : nat) vv, In (i, vv) (combine (seq 0 (length (rev tops))) (rev tops)) ->
cell_holds B ly rd' (z4 (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat i)) (vv / 16)).
Proof.
intros i vv Hin. apply in_combine_seq in Hin as [_ Hnth]. rewrite Nat.sub_0_r in Hnth.
assert (Hi : (i < length tops)%nat). { rewrite <- (length_rev tops). apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
rewrite nth_error_rev in Hnth by exact Hi.
pose proof reg_facts as (_ & _ & _ & _ & RU). pose proof class_facts as (_ & _ & K3 & _). pose proof Hnf as [N0 _].
assert (FN : fa_nth (class_size c) (rg_free (reg S c)) (fa_len (rg_free (reg S c)) - 1 - (nf - n + Z.of_nat i)) = Some vv).
{ rewrite <- Hnf_def. rewrite fa_nth_elems by (exact RU || zlia). rewrite E_elems. rewrite nth_error_app1 by zlia.
replace (Z.to_nat (nf - 1 - (nf - n + Z.of_nat i))) with (length tops - 1 - i)%nat by zlia. exact Hnth. }
pose proof (am_fa _ _ _ _ MA c (nf - n + Z.of_nat i) vv HcR ltac:(rewrite <- Hnf_def; zlia) FN) as RD. rewrite <- FAv_is in RD.
unfold cell_holds. cbn [c_at c_val c_w aeval aoff z4 c4]. intros k Hk. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & _). pose proof Hmf as [[_ M1] _].
rewrite (aview_copy (ly_T ly + (t_cache + 80 * c + (16 + 4 * Z.of_nat i)) + Z.of_nat k) (SRCv + 4 * Z.of_nat i + Z.of_nat k)).
- rewrite <- (RD k Hk). unfold rd0. f_equal. clear - Hk. unfold SRCv. zlia.
- apply PRW. right; left. clear - Hi E_len Hk K3. unfold DSTv, Pr. zlia.
- apply HfaPres. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DR)))))))))))))))))))) as SR3.
cbv beta in SR3. destruct (proj1 SR3 Hnle) as [X1 X2].     clear - X1 X2 Hi Hk E_len K3. unfold SRCv in *. zlia.
- clear - DR F1 F2 Hi E_len Hk K3. unfold Pr in *. numconst. zlia.
- clear - DR Hi E_len Hk M1 Hnle N0 K3. numconst. unfold SRCv. zlia.
- replace (ly_T ly + (t_cache + 80 * c + (16 + 4 * Z.of_nat i)) + Z.of_nat k) with (DSTv + (4 * Z.of_nat i + Z.of_nat k)) by (unfold DSTv, Pr, T; zlia).
replace (SRCv + 4 * Z.of_nat i + Z.of_nat k) with (SRCv + (4 * Z.of_nat i + Z.of_nat k)) by zlia. apply CPY. zlia.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells SR) (zseq 1 31)).
Proof.
pose proof (SR_parts tops rest) as (_ & _ & Rinit & Rother & Rcl & _). apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof derived_rangesR as DR. pose proof class_facts as (K1 & K2 & K3 & K4 & K5).
destruct (Z.eq_dec c' c) as [->|Hne].
-
unfold cache_cells. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks pc_max].
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c)) d) = Pr + d) by (intros d; cbn; unfold Pr; zlia).
constructor. { apply val_mem_cell. cbn [aeval]. apply (val_mem_at m' _ Pr); [unfold Pr; zlia|]. rewrite length_rev, E_len. exact V1. }
constructor. { apply val_mem_cell. rewrite EP. cbn [aeval]. rewrite <- Hmax. exact V2. }
constructor. { apply val_mem_cell. rewrite EP. cbn [aeval]. rewrite <- Hcsz. exact V3. }
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv). cbn [fst snd]. exact (slot_cell i vv Hiv).
-
replace (cache_cells SR c') with (cache_cells S c') by (unfold cache_cells; rewrite Rinit, (Rother c') by zlia; reflexivity).
apply (keep_cells _ (T + t_cache + 80 * c') 80).
+ intros a Ha. apply Z_T; unfold Pr in *; unfold T in *; clear - Ha Hc' Hne HcR DR K3; numconst; nia.
+ intros x Hx. unfold acells. apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; zlia | exact Hx].
+ unfold cache_cells. pose proof (wf_classes _ _ _ _ _ WF c' ltac:(zlia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c' ltac:(zlia)) as (_ & _ & _ & K4' & _). unfold T.
destruct (st_cache_inited S).
* destruct WC as [PM PL]. unfold t_cache. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. clear - Hiv PL K4'. zlia.
* unfold t_cache. repeat fcons'. apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks SR)).
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & Rch & _). rewrite Rch.
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(zlia)) as (Q1 & Q2 & Q3).
apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
+ intros a Ha. destruct (ck_beg k) as [|o|r o|c'' p] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
apply (Z_user (prim_class o) (rg_alloc_user (reg S (prim_class o)))); [zlia | zlia | zlia | zlia].
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _). apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Hin | cbn [fst snd]; clear - Ha X2 X3 G8 Q2 G5; unfold kPage in *; zlia].
+ intros x Hx. unfold acells. do 2 (apply in_app_iff; right). apply in_app_iff; left. apply in_flat_map. exists k. split; [exact Hk | exact Hx].
+ assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p]; try solve [destruct GG]; cbn; zlia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p]; try solve [destruct GG]; cbn; zlia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
* repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia|]). apply Forall_nil.
* destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|zlia]. zlia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia|]). apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells SR).
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & Rch & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
replace (sec_cells SR) with (sec_cells S) by (unfold sec_cells; rewrite Rres, Rarr, Rch; reflexivity).
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok 0x10000 0x5eb000) by (intros a Ha; apply Z_low; zlia).
unfold sec_cells in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_reserved; zlia | cbn; rewrite EI; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, o_sec_reserved, kHighMemBeg; zlia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_n; zlia | cbn; rewrite EI; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, o_sec_n, kHighMemBeg; zlia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_mutex; zlia | cbn; rewrite EI; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, o_sec_mutex, kHighMemBeg; zlia]|].
apply Forall_app. split.
- apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
+ intros a Ha. apply (Z_ext 1 (ly_Q ly, kPtrArrayResv)); [reflexivity | zlia | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. left. exact Hx.
+ apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zlia.
- apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(zlia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
+ intros a Ha. apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Gin | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. rewrite Eb. split; [exact Hk | exact Hx].
+ unfold kPage in *. repeat fcons'. apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; zlia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; zlia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
intros a Ha. apply (Z_user kBatchClass (rg_alloc_user (reg S kBatchClass) + 8192)); [unfold kBatchClass; zlia | zlia | unfold kUserMapSize, EV_MAX in MB; zlia |].
unfold region_base. subst x. unfold kBatchBytes in Ha. zlia. }
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; right; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_app. split.
- apply (keep_cells _ _ _ LOC).
+ intros y Hy. apply INC. do 3 right. apply in_app_iff. left. exact Hy.
+ apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. zlia.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells SR).
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells SR) with (quar_cells S) by (unfold quar_cells; rewrite Rqt, Rqg; reflexivity).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI. pose proof derived_rangesR as DR.
assert (LOCI : loc_ok 0x10000 0x5eb000) by (intros a Ha; apply Z_low; zlia).
assert (LOCT : loc_ok (T + t_qc) 32) by (intros a Ha; apply Z_T; unfold t_qc in *; unfold T in *; clear - Ha DR HcR; numconst; zlia).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; zlia | cbn; rewrite EI; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, kHighMemBeg; zlia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; zlia | cbn; rewrite EI; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, kHighMemBeg; zlia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOCT); [apply INC; right; right; apply in_app_iff; left; cbn; tauto | cbn; unfold T; zlia | cbn; unfold T; zlia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; right; apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; unfold TFIB_INST; zlia | cbn; rewrite EI; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, kHighMemBeg; zlia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells SR).
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells SR) with (fs_cells S) by (unfold fs_cells; rewrite Rfs; reflexivity).
apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | zlia | cbn [fst snd]; exact Ha].
- intros x Hx. unfold acells. do 5 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. zlia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly SR).
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
replace (depot_cells ly SR) with (depot_cells ly S) by (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; reflexivity).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
apply (keep_cells _ 0x10000 0x5eb000).
- intros a Ha. apply Z_low. zlia.
- intros x Hx. unfold acells. do 6 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold depot_cells. repeat (apply Forall_cons; [cbn; rewrite ?ED, ?ES; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_DEPOT, TFIB_STORE, d_nuniq, d_map1, s_total, s_block0, kHighMemBeg; zlia|]). apply Forall_nil.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B SR).
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B SR) with (ialloc_cells B S) by (unfold ialloc_cells; rewrite Rii; reflexivity).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
apply (keep_cells _ 0x10000 0x5eb000).
- intros a Ha. apply Z_low. zlia.
- intros x Hx. unfold acells. do 7 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_FLAG.
repeat (apply Forall_cons; [cbn; rewrite ?E1, ?E3; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IAL_LO, TFIB_IAL_FLAG, kHighMemBeg; zlia|]). apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). unfold thread_cells.
constructor; [|apply Forall_nil]. apply (keep_cell _ (T + t_unwinding) 1).
- intros a Ha. apply Z_T; unfold t_unwinding in *; unfold T in *; clear - Ha DR HcR K3; numconst; zlia.
- unfold acells. do 8 (apply in_app_iff; right). left. reflexivity.
- cbn. unfold T. zlia.
- cbn. unfold T. zlia.
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly SR).
Proof.
unfold acells.
apply Forall_app; split; [exact cells_regions|]. apply Forall_app; split; [exact cells_caches|]. apply Forall_app; split; [exact cells_chunks|].
apply Forall_app; split; [exact cells_sec|]. apply Forall_app; split; [exact cells_quar|]. apply Forall_app; split; [exact cells_fs|].
apply Forall_app; split; [exact cells_depot|]. apply Forall_app; split; [exact cells_ialloc | exact cells_thread].
Qed.
Lemma fa_final : fa_entries_ok ly rd' SR.
Proof.
pose proof (SR_parts tops rest) as (Rreg & Rc & _). pose proof reg_facts as (_ & _ & _ & _ & RU). intros c' i vv Hc' Hi HV k Hk.
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _).
assert (GEO : forall i0 kk, 0 <= i0 -> 4 * i0 + kk < kFreeArrayMax -> 0 <= kk ->
~ XC (fa_base ly c' + 4 * i0 + kk) /\ aowned B ly S (fa_base ly c' + 4 * i0 + kk)).
{ intros i0 kk H0 H1 H2. split.
- apply Z_prim.
+ unfold fa_base. unfold region_base in R1, R2. clear - H0 H1 H2 R1 R2. numconst. zlia.
+ unfold fa_base, RGv, SB. rewrite region_off_eq by zlia. clear - H0 H1 H2 Hc' HcR. numconst. zlia.
- eapply own_fa; [exact MA | exact Hc' | clear - H0 H1 H2; numconst; zlia]. }
assert (LOC : 0 <= i < fa_len (rg_free (reg S c')) -> 4 * i + Z.of_nat k < kFreeArrayMax ->
fa_nth (class_size c') (rg_free (reg S c')) (fa_len (rg_free (reg S c')) - 1 - i) = Some vv -> rd' (fa_base ly c' + 4 * i + Z.of_nat k) = Some (le_byte (vv / 16) 4 k)).
{ intros Hi0 Hb FN. destruct (GEO i (Z.of_nat k) ltac:(zlia) Hb ltac:(zlia)) as [NX OW].
rewrite AGX; [exact (am_fa _ _ _ _ MA c' i vv Hc' Hi0 FN k Hk) | exact OW | exact NX]. }
destruct (Z.eq_dec c' c) as [->|Hne].
- rewrite Rc in Hi, HV. unfold r_new in Hi, HV. cbn [rg_free] in Hi, HV. rewrite E_rest in Hi, HV.
pose proof Hnf as [N1 N2]. pose proof Hmf as [[M1 M2] _]. pose proof class_facts as (_ & _ & K3 & _).
apply LOC; [rewrite <- Hnf_def; clear - Hi K3; zlia | clear - Hi Hk N1 N2 M1 M2 K3; zlia |].
rewrite <- Hnf_def. rewrite fa_nth_elems by (exact RU || zlia). rewrite fa_nth_elems in HV by (exact E_runs || zlia).
rewrite E_elems. rewrite nth_error_app2 by zlia. rewrite <- HV. f_equal. zlia.
- rewrite (Rreg c') in Hi, HV by zlia. apply LOC; [exact Hi | clear - Hi Hk FL FB; zlia | exact HV].
Qed.
Lemma flags_final : fs_flags_ok ly rd' SR.
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & _ & _ & Rfr & _). intros cid pos Hc Hp. rewrite Rfr.
pose proof (flag_off_bounds cid pos Hc Hp) as FB.
rewrite AGX; [exact (am_flags _ _ _ _ MA cid pos Hc Hp) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact MA | zlia] |].
apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | zlia | cbn [fst snd]].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. zlia.
Qed.
Lemma depot_ids_boundR : depot_ids S <= 4097.
Proof.
pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). zlia.
Qed.
Lemma depot_final : depot_ok B ly rd' SR.
Proof.
pose proof (SR_parts tops rest) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
pose proof depot_ids_boundR as IDB. pose proof (ts_depot B TS) as ED.
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. apply AGX.
- destruct Ha as [Ha|Ha].
+ apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa5850, 0x5c8650 - 0xa5850). split; [cbn; tauto|]. unfold in_zr; cbn. unfold TFIB_DEPOT, d_tab_words in Ha. zlia.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [unfold core_extents; cbn; tauto | cbn [fst snd]; zlia].
- destruct Ha as [Ha|Ha]; [apply Z_low; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_DEPOT, d_tab_words, kHighMemBeg in *; zlia|].
apply (Z_ext 4 (ly_NB ly, kNodesBlockSize)); [reflexivity | zlia | cbn [fst snd]; zlia]. }
unfold depot_ok, depot_ids, depot_traces in *. rewrite Rdep.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|]. left. rewrite ED. unfold d_tab_words in *. zlia.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
+ intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. right. unfold kNodesBlockSize. zlia.
+ intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. right. unfold kNodesBlockSize. zlia.
Qed.
Lemma shadow_final : shadow_ok B ly rd' SR.
Proof.
pose proof (SR_parts tops rest) as (Rreg & Rc & _ & _ & _ & Rch & _).
assert (FPR : forall g, in_rangesb g (fa_poison_ranges ly SR) = in_rangesb g (fa_poison_ranges ly S)).
{ intros g. unfold fa_poison_ranges. rewrite Rch.
assert (E : flat_map (fun c0 : Z => [(region_base ly c0, rg_mapped_user (reg SR c0)); (fa_base ly c0, rg_mapped_fa (reg SR c0))]) (zseq 1 31) =
flat_map (fun c0 : Z => [(region_base ly c0, rg_mapped_user (reg S c0)); (fa_base ly c0, rg_mapped_fa (reg S c0))]) (zseq 1 31)).
{ apply flat_map_ext_in. intros c' Hc'. apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
- rewrite Rc. unfold r_new. cbn [rg_mapped_user rg_mapped_fa]. rewrite <- Hmu_def, <- Hmf_def. reflexivity.
- rewrite (Rreg c') by zlia. reflexivity. }
rewrite E. reflexivity. }
intros g vv Hg8 HV. unfold ashadow in HV. rewrite Rch, FPR in HV.
assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; exact HV).
rewrite AGX; [exact (am_shadow _ _ _ _ MA g vv Hg8 A0) | exact (ashadow_owned B ly S rd0 g vv MA A0) |].
apply Z_low. right. pose proof (am_shadow _ _ _ _ MA g vv Hg8 A0) as RD.
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
pose proof (Z.div_mod g 8 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(zlia)) as M1.
unfold shadow_addr. clear - Hg0 C1 C2 D1 M1. numconst. unfold SHADOW_OFF. zlia.
- unfold ashadow in A0. rewrite F0 in A0. destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|discriminate].
apply in_rangesb_true in IR as (lo & len & Hin & Hlo). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(zlia)) as (R1 & R2 & R3 & R4 & R5). pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(zlia)) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(zlia)) as MB.
pose proof (Z.div_mod g 8 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(zlia)) as M1.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold shadow_addr, fa_base in *; unfold region_base in R1, R2, Hlo; rewrite region_off_eq in Hlo by zlia; rewrite region_off_eq in R1 by zlia; rewrite region_off_eq in R2 by zlia;
clear - Hlo R1 R2 F3 F6 FA1 FB MB Hc' D1 M1; numconst; unfold SHADOW_OFF, EV_MAX in *; zlia.
+ apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p]; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). pose proof (Z.div_mod g 8 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(zlia)) as M1.
unfold shadow_addr. clear - Hlo C1 C2 Gbase Gext D1 M1. numconst. unfold SHADOW_OFF, kPage in *. zlia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi) | eapply own_shadow_zero; [exact MA | exact Hr | exact Hi] |].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
apply Z_low. right. unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst snd] in *. unfold shadow_addr. pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(zlia)) as D1.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(zlia)) as D2. pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(zlia)) as M2.
pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(zlia)) as M1.
clear - Hi T1 T2 T4 T7 D1 D2 M1 M2. numconst. unfold SHADOW_OFF. zlia.
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
unfold shadow_addr. unfold kLowMemEnd in Z5. pose proof (Z.div_mod (fst r) 8 ltac:(zlia)) as D1. pose proof (Z.div_mod (snd r) 8 ltac:(zlia)) as D2.
clear - Hi Z1 Z2 Z3 Z4 Z5 D1 D2. numconst. unfold SHADOW_OFF. zlia.
Qed.
Lemma cell_vis : forall cc k, In cc (acells B ly S) -> (exists e, c_val cc = AV e) -> (k < c_w cc)%nat -> rd0 (aeval B ly (c_at cc) + Z.of_nat k) <> None.
Proof.
intros cc k Hc [e He] Hk. pose proof (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc Hc) as CH. unfold cell_holds in CH. rewrite He in CH.
rewrite (CH k Hk). discriminate.
Qed.
Lemma vis_keep : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]); [exact (am_junk _ _ _ _ MA) | exact (am_areas _ _ _ _ MA) | exact (am_client _ _ _ _ MA)].
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly SR) /\ Forall (range_vis B ly rd') (aareas SR) /\ Forall (range_vis B ly rd') (aclient SR).
Proof.
pose proof (SR_parts tops rest) as (Rreg & Rc & Rinit & Rother & Rcl & Rch & Rsecs & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rnev).
pose proof derived_rangesR as DR. pose proof class_facts as (K1 & K2 & K3 & K4 & K5).
split; [|split].
-
unfold ajunk. rewrite Rch.
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. reflexivity. }
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. reflexivity. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
-
unfold cache_junk. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks]. rewrite length_rev, E_len.
constructor; [|apply Forall_nil]. intros i Hi. cbn [fst snd aeval] in *. apply VIS_MONO.
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ MA) (AT (t_cache + 80 * c + 16 + 4 * 0), 64 - 4 * 0)
ltac:(unfold ajunk; do 2 right; apply in_app_iff; right; apply in_app_iff; left; apply in_flat_map; exists c; split; [apply In_zseq; zlia|];
unfold cache_junk; rewrite Hinited, Hchunks; cbn [length Z.of_nat]; left; reflexivity)) as RV.
specialize (RV (4 * n + i) ltac:(cbn [snd]; zlia)). cbn [fst snd aeval] in RV.
replace (ly_T ly + (t_cache + 80 * c + 16 + 4 * n) + i) with (ly_T ly + (t_cache + 80 * c + 16 + 4 * 0) + (4 * n + i)) by zlia. exact RV.
- apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. apply in_app_iff; right. apply in_app_iff; left. apply in_flat_map. exists c'. split; [apply In_zseq; zlia|].
unfold cache_junk in *. rewrite Rinit, (Rother c') in Hx by zlia. exact Hx. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; do 2 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left.
unfold sec_junk in *. rewrite Rarr, Rres, Rch in Hx. exact Hx. }
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 4 (apply in_app_iff; right). apply in_app_iff; left.
unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 5 (apply in_app_iff; right). exact Hx.
-
replace (aareas SR) with (aareas S); [apply vis_keep; right; left; intros x Hx; exact Hx|].
unfold aareas. rewrite Rres, Rch. f_equal. apply flat_map_ext_in. intros c' Hc'. apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
+ rewrite Rc. unfold r_new. cbn [rg_mapped_user rg_mapped_fa]. rewrite <- Hmu_def, <- Hmf_def. reflexivity.
+ rewrite (Rreg c') by zlia. reflexivity.
-
replace (aclient SR) with (aclient S); [apply vis_keep; right; right; intros x Hx; exact Hx|].
unfold aclient. rewrite Rfr, Rch. reflexivity.
Qed.
Definition abs_cell_okR (cc : acell) : bool :=
match c_at cc with
| ANum a => ((0x10000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x5fb000)) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x80050000))
| _ => false
end.
Lemma abs_cells_okR : forallb abs_cell_okR (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros cc Hin.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin)|].
intros k Hk. apply AGX; [exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin k Hk)|].
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC.
pose proof (pairwise_ij _ _ 2 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DT. pose proof (pairwise_ij _ _ 0 6 _ _ (lo_disj ly LY) eq_refl eq_refl) as DP.
pose proof (Forall_nth' _ _ 7 _ (lo_app ly LY) eq_refl) as DH. cbv beta in DH. unfold in_app in DH. unfold zdisjoint in DT, DP. cbn [fst snd] in DT, DP, DH.
unfold zdisjoint in CT, PC. cbn [fst snd] in CT, PC.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD in *;
first [ apply Z_low; clear - Hk; unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks; numconst; zlia
| apply Z_T; unfold T in *; clear - Hk DR F1 F2 HcR; unfold kStackSpan in *; numconst; zlia
| apply Z_high; unfold T in *; clear - Hk DR F1 F2 F3 F4 F5 F6 F7 F8 CT PC DT DP DH; numconst; zlia ] |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okR cc Hin) as Hc. unfold abs_cell_okR in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbn [aeval].
apply Bool.orb_prop in Hc as [Hc|Hc]; apply andb_prop in Hc as [Hz Hc]; apply Z.leb_le in Hz; apply Z.leb_le in Hc; apply Z_low; zlia.
Qed.
Lemma AR_transport : AR tfibsegs B ly SR W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
pose proof (SR_parts tops rest) as (Rreg & Rc & Rinit & Rother & Rcl & Rch & Rsecs & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rnev).
split; [|split; [|split; [|split]]].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ exact WFR.
+ exact Mun.
+ exact Msy.
+ exact Mly.
+ unfold sec_placed in *. rewrite SR_sec_extents. exact Mpl.
+ exact const_final.
+ exact Mcow.
+ exact cells_final.
+ exact fa_final.
+ exact flags_final.
+ exact depot_final.
+ exact shadow_final.
+ exact zshadow_final.
+ exact (proj1 vis_final).
+ exact (proj1 (proj2 vis_final)).
+ exact (proj2 (proj2 vis_final)).
+
apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact MA | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zlia.
* apply Z_low. unfold TFIB_IMG_LO. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, kHighMemBeg in *; zlia.
+ exact Mts.
+   exact Msi.
- exact (SR_ledger tops rest _ (ALedger_same tfibsegs ly S md0 _ L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) ltac:(unfold eager_used; rewrite m_vmmaps_wvb, m_vm_lazy_wvb; reflexivity))).
-   destruct BUD as [BUD PIN]. split; [| intros e He; rewrite SR_sec_extents in He; exact (PIN e He)].
unfold abudget, sec_hulls in *. rewrite Rnev, Rsecs  . unfold sec_live_bytes in *. rewrite Rch. zlia.
-   exact (amwf_same md0 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW).
-   destruct HS0 as [HS0 HZ0]. split.
+ intros a Ha NC HV.
assert (NC0 : ~ aclient_byte B ly S a).
{ intros CL. apply NC. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)]; [left; exists k; rewrite Rch; exact (conj Hk (conj Hst Hr)) | right; exists cp; rewrite Rfr; exact (conj Hcp Hr)]. }
pose proof (HS0 a Ha NC0 HV) as X0.
destruct (BANDKEEP a ltac:(clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; zlia)) as [E | [_ [b Hb]]];
[unfold w64 in E; unfold YG0n.w64 in X0 |- *; rewrite E; exact X0 | unfold w64 in Hb; unfold YG0n.w64; rewrite Hb; discriminate].
+
apply (ahz_keep_same ly S SR mem0 mem'); [unfold sec_extents; rewrite Rch; reflexivity | | exact HZ0].
intros a Ha. pose proof high_factsR as (F1 & F2 & _). pose proof derived_rangesR as (DR1 & _ & _ & _ & DR5 & _).
unfold w64. apply MEQ. rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; zlia).
pose proof Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
intros HW. unfold WINR, WINR0, DSTv in HW.
pose proof class_facts as (_ & _ & Kn & _). clear - Ha HW F1 DR1 DR5 S1 T7 HcR Kn. unfold in_band_rw, kLowShadowEnd, zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, RSTACK, Pr, t_cache in *. try unfold T in *. zlia.
Qed.
Lemma WR_owned : forall a, 0 <= a < 2 ^ 64 -> WINR a -> (sp0 - RSTACK <= a < sp0) \/ aowned B ly S a.
Proof.
intros a Ra Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & _). pose proof class_facts as (_ & _ & K3 & _).
assert (OT : forall b, T <= b < T + kThreadObjSize -> aowned B ly S b).
{ intros b Hb. apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) b MA); [unfold core_extents; cbn; tauto | cbn [fst snd]; unfold T in Hb; exact Hb]. }
unfold WINR, WINR0, DSTv in Hw. destruct Hw as [[Hw|[Hw|[Hw|[Hw|Hw]]]]|Hw]; [left; exact Hw | right | right | right | right | right].
- apply OT. clear - Hw DR. numconst. zlia.
- apply (own_rinfo B ly S rd0 a MA). unfold RGv, SB in Hw. clear - Hw HcR. numconst. zlia.
- apply OT. clear - Hw. numconst. zlia.
- apply OT. clear - Hw. numconst. zlia.
- apply OT. clear - Hw DR K3. numconst. zlia.
Qed.
End a0.
Lemma LEAF_B2 : AR tfibsegs B ly S W mem0 md0 -> n <= nf -> forall tops rest W' c',
Wf (as_universe B) (SRf tops rest) ->
fa_elems (class_size c) (rg_free (reg S c)) = tops ++ fa_elems (class_size c) rest -> Z.of_nat (length tops) = n -> fa_len rest = nf - n -> runs_ok rest ->
at_RET2 W' c' -> refill_leaf B ly S W regs0 mem0 md0 c (tt, SRf tops rest) W' c'.
Proof.
intros HAR Hnle tops rest W' c' WFR E1 E2 E3 E4 HR.
destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & MEQ' & PRS & PRW & CPY & VALS).
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12).
exists regs', mem', (with_vm_backing (m_vm_lazy md0) mat md0).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
cbn [fst snd]. split.
- split; [eapply (AR_transport tops rest); eassumption|].
split; [apply layout_le_refl|].
split; [apply wle_refl|].
split. { intros r Hr. apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - RCS H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(zlia) 2%bv eq_refl) | rewrite (E5 3 ltac:(zlia) 3%bv eq_refl) | rewrite (E5 4 ltac:(zlia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(zlia) 8%bv eq_refl) | rewrite (E5 9 ltac:(zlia) 9%bv eq_refl) | rewrite (E5 18 ltac:(zlia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(zlia) 19%bv eq_refl) | rewrite (E5 20 ltac:(zlia) 20%bv eq_refl) | rewrite (E5 21 ltac:(zlia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(zlia) 22%bv eq_refl) | rewrite (E5 23 ltac:(zlia) 23%bv eq_refl) | rewrite (E5 24 ltac:(zlia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(zlia) 25%bv eq_refl) | rewrite (E5 26 ltac:(zlia) 26%bv eq_refl) | rewrite (E5 27 ltac:(zlia) 27%bv eq_refl) ];
cbn [In]; tauto. }
split. { unfold same_io. destruct md0; cbn; repeat split; reflexivity. }
split.
+
intros a Ra NO NO' NS NE. apply aview_same. apply MEQ'. rewrite unsigned_lit_small by exact Ra.
intros Hw. destruct (WR_owned HAR a Ra Hw) as [Hs|Ho]; [|exact (NO Ho)].
apply NS. unfold ascratch, spZ. left. exact Hs.
+ intros a Ha. exact (PRS a Ha).
- rewrite R10. pose proof (SR_parts tops rest) as (_ & _ & _ & _ & Rcl & _). rewrite Rcl. cbn [pc_chunks].
pose proof class_facts as (_ & _ & K3 & _).
destruct (rev tops) as [|x t] eqn:Er; [|reflexivity]. exfalso. apply (f_equal (@length Z)) in Er. rewrite length_rev in Er. cbn in Er. zlia.
Qed.
End z.
End l.

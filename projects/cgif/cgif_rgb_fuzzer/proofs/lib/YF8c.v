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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8t YF3v YF4q YF8g YF7x YF7w YF3w YF7z YF7y YF66 YF65.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3i YF81.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; img_lia ].
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
Section g. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Variables (need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pr := (@YF7w.Pr ly c).
Local Abbreviation RGv := (@YF7w.RGv ly c).
Local Abbreviation RBv := (@YF7w.RBv ly c).
Local Abbreviation FAv := (@YF7w.FAv ly c).
Local Abbreviation SHBv := (@YF7w.SHBv).
Local Abbreviation SRCv := (@YF7w.SRCv ly c n nf).
Local Abbreviation DSTv := (@YF7w.DSTv ly c).
Local Abbreviation AR0 f := (f c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug) (only parsing).
Local Abbreviation XWR := (AR0 (@YF7w.XWR ly)).
Local Abbreviation E0 := (AR0 (@YF7w.E0 ly regs0)).
Local Abbreviation EaT := (AR0 (@YF7w.EaT ly regs0)).
Local Abbreviation EaC := (AR0 (@YF7w.EaC ly regs0)).
Local Abbreviation EaSB := (AR0 (@YF7w.EaSB ly regs0)).
Local Abbreviation EaTOP := (AR0 (@YF7w.EaTOP ly regs0)).
Local Abbreviation EaCL := (AR0 (@YF7w.EaCL ly regs0)).
Local Abbreviation EaP := (AR0 (@YF7w.EaP ly regs0)).
Local Abbreviation EaMAX := (AR0 (@YF7w.EaMAX ly regs0)).
Local Abbreviation EaN := (AR0 (@YF7w.EaN ly regs0)).
Local Abbreviation EaCSZ := (AR0 (@YF7w.EaCSZ ly regs0)).
Local Abbreviation EaRG := (AR0 (@YF7w.EaRG ly regs0)).
Local Abbreviation EaRB := (AR0 (@YF7w.EaRB ly regs0)).
Local Abbreviation EaFA := (AR0 (@YF7w.EaFA ly regs0)).
Local Abbreviation EaNF := (AR0 (@YF7w.EaNF ly regs0)).
Local Abbreviation EaMF := (AR0 (@YF7w.EaMF ly regs0)).
Local Abbreviation EaAU := (AR0 (@YF7w.EaAU ly regs0)).
Local Abbreviation EaMU := (AR0 (@YF7w.EaMU ly regs0)).
Local Abbreviation EaSHB := (AR0 (@YF7w.EaSHB ly regs0)).
Local Abbreviation EaNEED := (AR0 (@YF7w.EaNEED ly regs0)).
Local Abbreviation EaTOT := (AR0 (@YF7w.EaTOT ly regs0)).
Local Abbreviation EaADR := (AR0 (@YF7w.EaADR ly regs0)).
Local Abbreviation EaSHA := (AR0 (@YF7w.EaSHA ly regs0)).
Hypothesis IMG : img_cover ly.
Local Abbreviation EaMU2 := (AR0 (@YF7w.EaMU2 ly regs0)).
Local Abbreviation EaNCe := (AR0 (@YF7w.EaNCe ly regs0)).
Local Abbreviation EaNCg := (AR0 (@YF7w.EaNCg ly regs0)).
Local Abbreviation EaNFe := (AR0 (@YF7w.EaNFe ly regs0)).
Local Abbreviation EaNFg := (AR0 (@YF7w.EaNFg ly regs0)).
Local Abbreviation EaFADR := (AR0 (@YF7w.EaFADR ly regs0)).
Local Abbreviation EaSHF := (AR0 (@YF7w.EaSHF ly regs0)).
Local Abbreviation EaMF2 := (AR0 (@YF7w.EaMF2 ly regs0)).
Local Abbreviation EaAUe := (AR0 (@YF7w.EaAUe ly regs0)).
Local Abbreviation EaAUg := (AR0 (@YF7w.EaAUg ly regs0)).
Local Abbreviation Er := (AR0 (@YF7w.Er ly regs0)).
Local Abbreviation E2 := (AR0 (@YF7w.E2 ly regs0)).
Local Abbreviation E1 := (AR0 (@YF7w.E1 ly regs0)).
Local Abbreviation E8 := (AR0 (@YF7w.E8 ly regs0)).
Hypothesis LY : layout_ok ly.
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
Hypothesis Hnlt : nf < n.
Hypothesis Hcarved : mu - au < kUserMapSize + kMaxSize.
Hypothesis Hau_al : au mod csz = 0.
Hypothesis Hneed : need = n - nf.
Hypothesis Htot : tot = au + need * csz.
Hypothesis Hadr : adr = RBv + mu.
Hypothesis Hsha : sha = SHBv + adr / 8.
Hypothesis Hmu2 : mu2 = mu + kUserMapSize.
Hypothesis Hnce : nce = (mu - au) / csz.
Hypothesis Hncg : ncg = (mu2 - au) / csz.
Hypothesis Hnfe : nfe = nf + nce.
Hypothesis Hnfg : nfg = nf + ncg.
Hypothesis Hfadr : fadr = FAv + mf.
Hypothesis Hshf : shf = SHBv + fadr / 8.
Hypothesis Hmf2 : mf2 = mf + kFreeArrayMapSize.
Hypothesis Haue : aue = au + nce * csz.
Hypothesis Haug : aug = au + ncg * csz.
Ltac clear3 := try clear Hnlt Hcarved Hau_al Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug.
Local Abbreviation class_facts := (@YF7w.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation AR2 f := (f imgk ly regs0) (only parsing).
Local Abbreviation AR5 f := (AR2 f maxc mf au mu) (only parsing).
Local Abbreviation high_factsR := ((AR5 (@YF7w.high_factsR _)) IMG LY Hmf Hmu).
Local Abbreviation off_T := ((AR5 (@YF7w.off_T _)) IMG LY Hmf Hmu).
Local Abbreviation off_C := ((AR5 (@YF7w.off_C _)) IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation AR1 f := (f IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation AR3 f := (AR2 f c maxc n nf mf au mu csz) (only parsing).
Local Abbreviation derived_rangesR := (AR1 (AR3 (@YF7w.derived_rangesR _))).
Local Abbreviation WINR0 := (@YF7w.WINR0 ly regs0 c).
Local Abbreviation WINR := (@YF7w.WINR ly regs0 c n).
Local Abbreviation WINR0_WINR := (@YF7w.WINR0_WINR ly regs0 c n).
Local Abbreviation WSKELR := (@YF7w.WSKELR).
Local Abbreviation win_sub := (@YF7w.win_sub).
Local Abbreviation win_sub_sound := (@YF7w.win_sub_sound ly regs0 c maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (AR1 (AR0 (AR2 (@YF7w.WSKELR_WINR0 _)))).
Local Abbreviation windows_WINR0 := (AR1 (AR0 (AR2 (@YF7w.windows_WINR0 _)))).
Local Abbreviation frame_WINR0 := (AR1 (AR0 (AR2 (@YF7w.frame_WINR0 _)))).
Local Abbreviation frame_X := (AR1 (AR0 (AR2 (@YF7w.frame_X _)))).
Ltac frame_acc3 HX HE :=
match goal with
| MEQ : (forall x : word, ~ ?X (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ X (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_X X E rs m1 m2 HX HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation W_DST := (@YF7w.W_DST ly c n).
Local Abbreviation W_FE := (@YF7w.W_FE ly c nf).
Local Abbreviation W_UW := (@YF7w.W_UW adr).
Local Abbreviation W_USH := (@YF7w.W_USH sha).
Local Abbreviation W_FW := (@YF7w.W_FW fadr).
Local Abbreviation W_FSH := (@YF7w.W_FSH shf).
Local Abbreviation at_R3 := (AR0 ((AR2 (@YF7w.at_R3 _)) mem0)).
Local Abbreviation at_N3 := (AR0 ((AR2 (@YF7w.at_N3 _)) mem0)).
Local Abbreviation at_RET3 := (@YF7w.at_RET3 _ regs0 mem0 imgk).
Local Abbreviation P_cells := (@YF7w.P_cells imgk ly c maxc csz).
Local Abbreviation chunk_index := (@YF7w.chunk_index).
Local Abbreviation pstable := (@YF7w.pstable ly regs0 c).
Local Abbreviation all_disjoint_of_forall := (@YF7w.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (AR5 (@YF7w.kept_of_frame)).
Local Abbreviation kept_of_frame2 := (AR5 (@YF7w.kept_of_frame2)).
Local Abbreviation SKEL_TAILR := (@YF7w.SKEL_TAILR imgk).
Local Abbreviation RFACTSR := ((AR2 (@YF7w.RFACTSR)) c).
Local Abbreviation stack_ivsR := (@YF7w.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := ((AR1 (AR3 (@YF7w.zone_litR _))) Hsp).
Local Abbreviation zone_TR := ((AR2 (@YF7w.zone_TR _)) c maxc mf au mu IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := ((AR1 (AR3 (@YF7w.zone_CR _))) Hsp).
Local Abbreviation zone_RGR := ((AR1 (AR3 (@YF7w.zone_RGR _))) Hsp).
Local Abbreviation slots_not_WINR0 := ((AR1 (AR3 (@YF7w.slots_not_WINR0 _))) Hsp).
Local Abbreviation fa_not_WINR0 := ((AR1 (AR3 (@YF7w.fa_not_WINR0 _))) Hsp).
Local Abbreviation tail_ext_okR := ((AR1 (AR0 (AR2 (@YF7w.tail_ext_okR _)))) Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := ((AR5 (@YF7w.rdn_of_presentR)) Hmf Hmu).
Local Abbreviation store_ok_of_presentR := ((AR5 (@YF7w.store_ok_of_presentR)) Hmf Hmu).
Local Abbreviation AR4 f := (AR2 f c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp) (only parsing).
Local Abbreviation cpy4_stretch := (AR4 (@YF7w.cpy4_stretch _)).
Local Abbreviation facts3 := ((AR1 ((AR3 (@YF7w.facts3 _)) need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug)) Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation RFACTS3 := ((AR2 (@YF7w.RFACTS3)) c).
Local Abbreviation tail_ext_ok3 := ((AR1 (AR0 (AR2 (@YF7w.tail_ext_ok3 _)))) Hsp).
Local Abbreviation stack_ext_ok3 := ((AR1 (AR3 (@YF7w.stack_ext_ok3 _))) Hsp).
Local Abbreviation scratch_headed := (@YF7w.scratch_headed).
Local Abbreviation mem_ok_scratch_present := ((AR0 (AR2 (@YF7w.mem_ok_scratch_present _))) LY Hmf Hmu Hsp).
Local Abbreviation at_R3_run := ((AR1 (AR0 ((AR2 (@YF7w.at_R3_run _ _)) mem0))) Hsp).
Local Abbreviation at_R3_run_ecall := ((AR1 (AR0 ((AR2 (@YF7w.at_R3_run_ecall _ _)) mem0))) Hsp).
Local Abbreviation at_R3_pin := (AR0 ((AR2 (@YF7w.at_R3_pin _)) mem0)).
Local Abbreviation at_R3_arm := (AR0 ((AR2 (@YF7w.at_R3_arm _)) mem0)).
Local Abbreviation at_R3_forget := (AR0 ((AR2 (@YF7w.at_R3_forget _)) mem0)).
Local Abbreviation at_R3_noconds := (AR0 ((AR2 (@YF7w.at_R3_noconds _)) mem0)).
Local Abbreviation at_R3_weaken := (AR0 ((AR2 (@YF7w.at_R3_weaken _)) mem0)).
Local Abbreviation at_R3_facts := (AR0 ((AR2 (@YF7w.at_R3_facts _)) mem0)).
Local Abbreviation at_R3_strengthen := (AR0 ((AR2 (@YF7w.at_R3_strengthen _)) mem0)).
Local Abbreviation at_R3_eq := (AR0 ((AR2 (@YF7w.at_R3_eq _)) mem0)).
Local Abbreviation CSAVED := (@YF7w.CSAVED).
Local Abbreviation sv_denot_SOff0 := (@YF7w.sv_denot_SOff0).
Local Abbreviation at_R3_ret := ((AR0 ((AR2 (@YF7w.at_R3_ret _)) mem0)) HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp).
Local Abbreviation at_N3_cont := ((AR1 (AR0 ((AR2 (@YF7w.at_N3_cont _ _)) mem0))) Hsp).
Local Abbreviation memset_stretch3 := (AR4 (@YF7w.memset_stretch3 _)).
Local Abbreviation nth_Z_to_le_bytes4 := (@YF7w.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (AR4 (@YF7w.popfree_stretch _)).
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
Hypothesis HAR : AR tfxsegs B ly S W mem0 md0.
Local Abbreviation Pr_is := (@YF7w.Pr_is ly c).
Local Abbreviation RGv_is := (@YF7w.RGv_is ly c).
Local Abbreviation FAv_is := (@YF7w.FAv_is ly c HcR).
Local Abbreviation RBv_is := (@YF7w.RBv_is ly c HcR).
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
Ltac r3_station HR ss' :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_R3_eq Wx md X P ss ss' W' c' HR ltac:(img_try ((img_case; vm_compute); img_refl))) as H2; clear HR; rename H2 into HR end.
Ltac r3_run HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
let cs := img_ev (match nth_error (ss_mem ss') 0 with Some r => YQ0b.r_chunks r | None => [] end) in
eapply SRr_bind;
[ img_try (eapply (at_R3_run Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | exists cs; (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Ltac pin_zev3 := img_apply U_eq_by_zev; [img_refl | img_refl |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac r3_pin HR r e :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let t := img_ev (sr_get (ss_regs ss) r) in
let HU := fresh "HU" in
assert (HU : U E0 e = U E0 t);
[ | img_try (let H2 := fresh "HR" in
pose proof (at_R3_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) HU) as H2;
clear HU HR; rename H2 into HR) ] end.
Ltac r3_arm HR cnd tk a b :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HB := fresh "HB" in
assert (HB : branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk);
[ | img_try (let H2 := fresh "HR" in
pose proof (at_R3_arm Wx md X P ss W' c' cnd tk a b HR ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) HB) as H2;
clear HB HR; rename H2 into HR) ] end.
Ltac r3_forget HR k clob :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_R3_forget Wx md X P ss W' c' k clob HR ltac:(img_try (unfold aHAV3; (img_case; cbv); zlia)) eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))) as H2;
clear HR; rename H2 into HR end.
Ltac r3_noconds HR :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in pose proof (at_R3_noconds Wx md X P ss W' c' HR) as H2; clear HR; rename H2 into HR end.
Ltac arm_zev3 := rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U;
rewrite !U_zev by (img_try ((img_case; vm_compute); img_refl)); cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac rregS HS r R :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := img_ev (sr_get (ss_regs ss) r) in
pose proof (st_ok_reg_denot H E ss ms r HS) as R; img_change (sr_get (ss_regs ss) r) with e in R end.
Ltac memv3 HS HEn ss i off :=
let j := img_ev (chunk_index (match nth_error (ss_mem ss) i with Some r => YQ0b.r_chunks r | None => [] end) off) in
memv HS i j;
[ img_try (cbn [base_val YQ0b.r_base]; first [ unfold rP; rewrite (HEn 37%nat ltac:((img_case; cbv); zlia)), EaP | unfold rRG; rewrite (HEn 41%nat ltac:((img_case; cbv); zlia)), EaRG ];
unfold w64; rewrite unsigned_lit_small by zlia; zlia) | | ].
Ltac val_atom HEn :=
first [ img_refl
| lazymatch goal with |- sv_denot _ (SOff ?k _) = _ =>
cbn [sv_denot]; rewrite (HEn k ltac:(img_try ((img_case; cbv); zlia)));
rewrite ?EaN, ?EaMAX, ?EaCSZ, ?EaNF, ?EaMF, ?EaAU, ?EaMU, ?EaNFe, ?EaNFg, ?EaMF2, ?EaAUe, ?EaAUg;
unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl end ].
Ltac cells3 HS HEn ss RP RR DR F1' F2 :=
unfold P_cells; cbv zeta;
split; [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; destruct Ha as [Ha|[Ha|[Ha|Ha]]];
[ img_try (eapply (st_ok_window_apresent_off _ _ _ _ 35 _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold rP; rewrite (HEn 37%nat ltac:((img_case; cbv); zlia)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - RP; zlia); clear - Ha; zlia | off_by ltac:(clear - Ha RP DR; numconst; zlia) ])
| img_try (eapply (st_ok_window_apresent_off _ _ _ _ 36 _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold rRG; rewrite (HEn 41%nat ltac:((img_case; cbv); zlia)), EaRG; unfold w64; rewrite unsigned_lit_small by (clear - RR; zlia); clear - Ha; zlia | off_by ltac:(clear - Ha RR DR; numconst; zlia) ])
| img_try (eapply (st_ok_window_apresent_off _ _ _ _ 33 _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold rT; rewrite (HEn 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - F1' F2; numconst; try unfold T in *; zlia); try unfold T in *; clear - Ha; zlia | off_by ltac:(clear - Ha F1' F2; numconst; try unfold T in *; zlia) ])
| img_try (eapply (st_ok_window_apresent_off _ _ _ _ 34 _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold rT; rewrite (HEn 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - F1' F2; numconst; try unfold T in *; zlia); try unfold T in *; clear - Ha; zlia | off_by ltac:(clear - Ha F1' F2; numconst; try unfold T in *; zlia) ]) ]
| repeat match goal with |- _ /\ _ => split end;
[ img_try (memv3 HS HEn ss 35%nat 0) | img_try (memv3 HS HEn ss 35%nat 4) | img_try (memv3 HS HEn ss 35%nat 8)
| img_try (memv3 HS HEn ss 36%nat 0) | img_try (memv3 HS HEn ss 36%nat 8) | img_try (memv3 HS HEn ss 36%nat 16) | img_try (memv3 HS HEn ss 36%nat 24)
| img_try (memv3 HS HEn ss 36%nat 32) | img_try (memv3 HS HEn ss 36%nat 40) | img_try (memv3 HS HEn ss 36%nat 48) | img_try (memv3 HS HEn ss 36%nat 56) | img_try (memv3 HS HEn ss 36%nat 68) ];
try val_atom HEn; try (clear; zlia) ].
Local Notation SSU := SS0U3. Local Notation REG0U := REG0U3. Local Notation REG0X := REG0R3.
Local Notation SU1 := R3_U1. Local Notation SU2 := R3_U2. Local Notation SU3 := R3_U3. Local Notation SU4 := R3_U4. Local Notation SU5 := R3_U5.
Local Notation SJ := R3_J. Local Notation HAVJ := aHAV3. Local Notation NREG := 41%nat.
Local Notation SU1_35 := R3_U1_35. Local Notation SU1_ext := R3_U1_ext. Local Notation SU1_len := R3_U1_len.
Local Notation SU2_eq := R3_U2_eq. Local Notation SU3_split := R3_U3_split. Local Notation SU3_35 := R3_U3_35'.
Local Notation SU3_ext := R3_U3_ext. Local Notation SU3_len := R3_U3_len. Local Notation SU4_eq := R3_U4_eq. Local Notation SU4_mem := R3_U4_mem.
Local Notation SUJ := R3_UJ.
Definition WINU (a : Z) : Prop :=
(sp0 - RSTACK <= a < sp0) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888).
Definition WSKELU : list (option nat * Z * Z) := [(Some 2%nat, - RSTACK, 0); (Some rRG, 0, 128); (Some rT, 2768, 2800); (Some rT, 2872, 2888)].
Lemma WINU_WINR0 : forall a, WINU a -> WINR0 a.
Proof. clear3. intros a H. unfold WINU, WINR0 in *. tauto. Qed.
Lemma WSKELU_WINU : forall (E : env) a t,
(forall k, (k < HAVJ)%nat -> ew E k = ew E0 k) -> In t WSKELU ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINU a.
Proof. clear3.
intros E a t HE Hin Hr. unfold WSKELU in Hin. cbn [In] in Hin. unfold WINU.
pose proof derived_rangesR as DR. pose proof high_factsR as HF. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize in DR, HF.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [img_try (cbn [fst snd base_val] in Hr; unfold rRG, rT in Hr; rewrite HE in Hr by (unfold aHAV3; zlia);
rewrite ?E2, ?EaT, ?EaRG in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by zlia; unfold sp0 in *; zlia) |]
| False => destruct Hin
end.
Qed.
Lemma windows_WINU : forall (E : env) rs a,
(forall k, (k < HAVJ)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELU || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINU a.
Proof. clear3.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). img_exact (WSKELU_WINU E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Lemma frame_WINU : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < HAVJ)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELU || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINU (bv_unsigned x) -> m' x = m x.
Proof. clear3. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WINU E rs _ HE Hb Hw). Qed.
Definition POSTU (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
env_agree HAVJ E0 E' /\
st_ok tfxsegs E' SJ (restrict (w_H W) ms) /\
(forall x : word, ~ WINR0 (bv_unsigned x) -> ~ TABW T (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) (ms_mem ms)) T i) /\
(forall a, TABW T a -> apresent (w_H W) (ms_mem ms) a).
Lemma headcnt_TBLS0 : all_disjoint E0 headcnt TBLS0.
Proof. clear3.
img_apply all_disjoint_of_In. intros r Hr. destruct (In_TBLS0 r Hr) as (i & Hi & ->).
unfold extent_disjoint, headcnt, tblr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. unfold rP, rT. rewrite EaP, EaT.
pose proof derived_rangesR as (D1 & D2 & _). pose proof high_factsR as (F1 & F2 & _).
unfold w64. rewrite !unsigned_lit_small by (img_try (clear - D1 D2 F1 F2; numconst; try unfold T in *; zlia)).
unfold Pr in *; try unfold T in *; clear - Hi HcR. numconst. assert (i < c \/ i = c \/ c < i) by zlia. zlia.
Qed.
Lemma sepU :
(forall a, T + 292 <= a < T + 2704 -> ~ WINU a) /\
(forall a, Pr <= a < Pr + 4 -> ~ WINU a /\ ~ TABW T a) /\
(forall i a, 1 <= i <= 31 -> i <> c -> T + 212 + 80 * i <= a < T + 224 + 80 * i -> ~ WINR0 a) /\
(forall a, WINU a \/ TABW T a \/ (Pr <= a < Pr + 4) -> 0 <= a < 2 ^ 64) /\
(0 <= Pr /\ Pr + 16 <= 2 ^ 64 /\ Pr = T + 208 + 80 * c /\ 4096 <= T   /\ T + kThreadObjSize <= 2 ^ 64).
Proof. clear3.
pose proof derived_rangesR as (D1 & D2 & _ & _ & D5 & D6 & _ & D8 & _ & _ & _ & _ & _ & _ & _ & _ & D17 & D18 & _).
pose proof high_factsR as (F1 & F2 & _ & _ & F5 & _). pose proof Hsp as (Hlo & Hhi & _). pose proof stack_ivsR as (SI & _ & _ & SI4).
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINU, WINR0, TABW. unfold Pr, RGv in *. try unfold T in *. try unfold SB in *. try unfold sp0 in *. numconst. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END.
assert (NRG : forall a, ly_T ly <= a < ly_T ly + 4096 -> ~ (ly_space ly + 137438953472 + 128 * c <= a < ly_space ly + 137438953472 + 128 * c + 128))
by (img_try (clear - D8 D17 F5 PT; intros a Ha X; zlia)).
assert (NST : forall a, ly_T ly <= a < ly_T ly + 4096 -> ~ (bv_unsigned (getr regs0 2) - 1024 <= a < bv_unsigned (getr regs0 2))) by (img_try (clear - SI; intros a Ha X; zlia)).
clear D8 D17 F5 PT SI.
split; [|img_try (split; [|split; [|split]])].
- intros a Ha [X|[X|[X|X]]]; [img_try (img_exact (NST a ltac:(clear - Ha; zlia) X)) | img_try (img_exact (NRG a ltac:(clear - Ha; zlia) X)) | img_try (clear - Ha X; zlia) | img_try (clear - Ha X; zlia)].
- intros a Ha. split.
+ intros [X|[X|[X|X]]]; [img_try (img_exact (NST a ltac:(clear - Ha HcR; zlia) X)) | img_try (img_exact (NRG a ltac:(clear - Ha HcR; zlia) X)) | img_try (clear - Ha X HcR; zlia) | img_try (clear - Ha X HcR; zlia)].
+ intros (j & Hj & Hr). clear - Ha Hj Hr HcR. assert (j < c \/ j = c \/ c < j) by zlia. zlia.
- intros i a Hi Hic Ha. intros [X|[X|[X|[X|X]]]]; [img_try (img_exact (NST a ltac:(clear - Ha Hi; zlia) X)) | | img_try (img_exact (NRG a ltac:(clear - Ha Hi; zlia) X)) | img_try (clear - Ha Hi X; zlia) | img_try (clear - Ha Hi X; zlia)].
clear - Hi Hic Ha X. assert (i < c \/ c < i) by zlia. zlia.
- intros a [[X|[X|[X|X]]]|[(j & Hj & Hr)|X]]; [img_try (clear - X Usp SI4; zlia) | img_try (clear - X D5 D6; zlia) | img_try (clear - X F1 F2; zlia) | img_try (clear - X F1 F2; zlia) | img_try (clear - Hj Hr F1 F2; zlia) | img_try (clear - X F1 F2 HcR; zlia)].
- clear - D1 D2 F1 F2 HcR. zlia.
Qed.
Lemma segU : forall mat,
(forall a, T <= a < T + kThreadObjSize -> apresent (w_H W) mem0 a) ->
all_disjoint E0 (YQ0b.mkRegion (Some rT) 292 2704 0 0 []) (dropAt 35 REG0X) ->
st_ok tfxsegs E0 SSU (restrict (w_H W) (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs))) ->
SRr tfxsegs W (mkCfg (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) POSTU.
Proof.
intros mat HTP HSPAN HS. pose proof Hwx_tfa as Hwx.
pose proof sepU as (Zspan & Zcnt & Ztab & Z64 & (P0 & P16 & EPr & TI & TE)).
pose proof class_facts as (CF1 & CF2 & CF3 & CF4 & CF5).
assert (HEn0 : forall k, (k < HAVJ)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
assert (ET : bv_unsigned (ew E0 32) = T) by (img_try (rewrite EaT; unfold w64; img_apply unsigned_lit_small; clear - TI TE; numconst; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in TI; zlia)).
assert (EP : bv_unsigned (ew E0 37) = Pr) by (img_try (rewrite EaP; unfold w64; img_apply unsigned_lit_small; clear - P0 P16; zlia)).
assert (HDJ : all_disjoint E0 headc0 (dropAt 35 REG0X)).
{ pose proof (st_ok_mem_ok tfxsegs E0 SSU _ HS) as (_ & _ & PW). cbn [ss_mem SSU] in PW.
img_change (dropAt 35 REG0X) with (dropAt 35 REG0U). img_apply (pairwise_disjoint_pick E0 REG0U 35 headc0 PW). img_case; vm_compute. all: img_refl. }
srr_run_to_sh tfxtbl_rtA_ok HS (0x36768 + D_150).
match type of HS with st_ok _ _ ?ss (restrict _ ?msx) => img_change ss with SU1 in HS; set (m1 := ms_mem msx) in *; rename msx into ms1 end.
assert (MEQ1 : forall x : word, ~ WINU (bv_unsigned x) -> m1 x = mem0 x)
by (img_try (intros x Hx; img_exact (frame_WINU E0 (ss_mem SSU) _ _ HEn0 ltac:((img_case; vm_compute); img_refl) HF x Hx))).
clear HF HFr.
assert (PRES1 : forall a, T <= a < T + kThreadObjSize -> ~ WINU a -> apresent (w_H W) m1 a).
{ intros a Ha Hw. img_apply (apresent_same (w_H W) mem0); [| img_try (img_exact (HTP a Ha))]. img_apply MEQ1. rewrite unsigned_lit_small; [img_try (img_exact Hw)|]. clear - Ha TI TE. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in TI. zlia. }
assert (HS2 : st_ok tfxsegs E0 SU2 (restrict (w_H W) ms1)).
{ rewrite SU2_eq. img_apply (st_ok_mem_surgery E0 SU1 (restrict (w_H W) ms1) _ HS). cbn [ms_mem restrict]. fold m1. intros HM.
img_apply mem_ok_app.
- eapply (mem_ok_replAt E0 _ _ 35 headc0 headcnt HM SU1_35).
+ unfold subregion, headcnt, headc0. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
split; [img_refl|]. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (left; zlia)|]. intros ch Hch. destruct Hch as [<-|[]]. left. img_refl.
+ img_refl.
- img_exact TBLS0_wf.
- img_apply TBLS0_ok; unfold rT; [img_try (rewrite ET; clear - TI TE; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in TI; zlia) | img_try (rewrite ET; clear - TI TE; numconst; zlia) |].
intros a Ha. unfold rT in Ha. rewrite ET in Ha. img_apply apresent_writable_off; [img_try (off_by ltac:(clear - Ha TI TE; numconst; zlia)) |].
img_apply PRES1; [img_try (clear - Ha; numconst; zlia) | img_try (img_exact (Zspan a Ha))].
- img_apply TBLS0_pairwise.
- intros r Hr. img_apply (all_disjoint_replAt E0 r 35 headcnt (ss_mem SU1)); [img_try (rewrite SU1_len; zlia) | |].
+ img_apply extent_disjoint_sym. img_exact (all_disjoint_In E0 headcnt TBLS0 r headcnt_TBLS0 Hr).
+ img_apply (TBLS0_disjoint E0 r _ Hr). img_exact (all_disjoint_ext3 E0 _ _ _ (eq_sym SU1_ext) HSPAN). }
clear HS. rename HS2 into HS.
srr_run_to_sh tfxtbl_rtA_ok HS (0x36804 + D_150).
match type of HS with st_ok _ _ ?ss (restrict _ ?msx) => img_change ss with SU3 in HS; set (m3 := ms_mem msx) in *; rename msx into ms3 end.
assert (MEQ3 : forall x : word, ~ WINU (bv_unsigned x) -> ~ TABW T (bv_unsigned x) -> m3 x = m1 x).
{ intros x Hx Ht. img_apply HF. rewrite SU2_eq. cbn [ss_mem]. intros Hw. apply in_wrange_app in Hw as [Hw|Hw].
- img_exact (Hx (windows_WINU E0 (replAt 35 headcnt (ss_mem SU1)) _ HEn0 ltac:(img_try ((img_case; vm_compute); img_refl)) Hw)).
- img_apply Ht. pose proof (in_wrange_TBLS0 E0 _ Hw) as Hw'. cbn [base_val] in Hw'. unfold rT in Hw'. rewrite ET in Hw'. img_exact Hw'. }
clear HF HFr.
pose proof (st_ok_mem_ok tfxsegs E0 SU3 _ HS) as HM3. cbn [ms_mem restrict] in HM3. fold m3 in HM3. rewrite SU3_split in HM3.
pose proof (mem_ok_TBLSF E0 _ _ HM3) as TBF. unfold rT in TBF. rewrite ET in TBF.
assert (CNT : val_mem tfxsegs (mrestrict (w_H W) m3) Pr 4 0).
{ rewrite <- (Z.add_0_r Pr), <- EP. eapply (chunk_val_at (w_H W) E0 SU3 _ 35 0 _ _ 4%N _ 0 _ HS); [img_try (img_exact SU3_35) | img_refl | img_refl | img_refl | img_try (cbn; zlia) | img_try (cbn; zlia)]. }
assert (HS4 : st_ok tfxsegs E0 SU4 (restrict (w_H W) ms3)).
{ rewrite SU4_eq. img_apply (st_ok_mem_surgery E0 SU3 (restrict (w_H W) ms3) _ HS). cbn [ms_mem restrict]. fold m3. intros _.
rewrite (replAt_insAt 35 headcJ _ ltac:(img_try (rewrite SU3_len; zlia))). img_apply mem_ok_insAt.
- img_apply mem_ok_dropAt. img_exact (mem_ok_app_l E0 _ _ _ HM3).
- img_refl.
-
unfold region_ok, headcJ. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold rP. rewrite EP.
split; [img_try (clear - P0; zlia)|]. split; [img_try (clear - P16; zlia)|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 4) as [Ho4|Ho4].
- img_apply apresent_writable_off; [img_try (off_by ltac:(clear - Ho P0 P16 EPr TI HcR; numconst; zlia)) |]. destruct (Zcnt (Pr + o) ltac:(img_try (clear - Ho Ho4; zlia))) as [Hw Ht].
img_apply (apresent_same (w_H W) m1); [| img_try (img_apply PRES1; [clear - Ho Ho4 EPr HcR; numconst; zlia | img_exact Hw])].
img_apply MEQ3; rewrite unsigned_lit_small by (img_try (clear - Ho P0 P16; zlia)); [img_try (img_exact Hw) | img_try (img_exact Ht)].
- replace (Pr + o) with (T + 212 + 80 * c + (o - 4)) by (img_try (clear - Ho EPr; zlia)). img_apply (proj2 (TBF c HcR)). clear - Ho Ho4; zlia. }
pose proof (proj1 (TBF c HcR)) as [TM TSZ].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
+ eapply chunk_ok_val; [img_refl | img_try (cbn; zlia) | img_try (cbn; zlia) | img_try (rewrite Z.add_0_r; img_exact CNT)].
+ eapply chunk_ok_val; [img_try (cbn [sv_denot]; unfold rMAX; rewrite EaMAX, Hmax; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; img_refl)
| img_try (pose proof (max_cached_range c HcR); cbn; zlia) | img_try (cbn; zlia) |].
replace (Pr + 4) with (T + 212 + 80 * c) by (img_try (clear - EPr; zlia)). img_exact TM.
+ eapply chunk_ok_val; [img_try (cbn [sv_denot]; unfold rCSZ; rewrite EaCSZ, Hcsz; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; img_refl)
| img_try (rewrite <- Hcsz; cbn; clear - CF4; numconst; zlia) | img_try (cbn; zlia) |].
replace (Pr + 8) with (T + 216 + 80 * c) by (img_try (clear - EPr; zlia)). img_exact TSZ.
- img_apply (all_disjoint_head_ext3 E0 headc0 headcJ); [img_refl|]. img_exact (all_disjoint_ext3 E0 _ _ _ (eq_sym SU3_ext) HDJ). }
clear HS. rename HS4 into HS.
srr_run_to_sh tfxtbl_rtA_ok HS (0x3672c + D_150).
match type of HS with st_ok _ _ ?ss (restrict _ ?msx) => img_change ss with SU5 in HS; set (m5 := ms_mem msx) in *; rename msx into ms5 end.
assert (MEQ5 : forall x : word, ~ WINR0 (bv_unsigned x) -> m5 x = m3 x)
by (img_try (intros x Hx; img_exact (frame_WINR0 E0 (ss_mem SU4) _ _ HEn0 ltac:((img_case; vm_compute); img_refl) HF x Hx))).
clear HF HFr.
img_apply SRr_ret. split; [img_refl|].
lazymatch goal with |- exists ms' mt E', mkCfg _ (with_vm_backing _ ?matx _) = _ /\ _ => exists ms5, matx, (havoc E0 hJ0 (map (getr (ms_regs ms5)) CLOB_INIT)) end.
split; [img_try ((subst m5; cbv beta); img_refl)|].
split; [img_try (img_exact (env_agree_havoc_ge HAVJ hJ0 E0 E0 _ ltac:(unfold hJ0; zlia) (env_agree_refl HAVJ E0)))|].
split.
{ pose proof (st_ok_forget hJ0 E0 SU5 (w_H W) ms5 CLOB_INIT HS eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))) as X'.
rewrite <- (st_ok_restrict_mkst tfxsegs (w_H W) E0 SU5 ms5 HS eq_refl) in X'.
apply (st_ok_prune _ _ _ _ [] []) in X'. rewrite <- SUJ. unfold noconds, forget. img_exact X'. }
assert (MEQ : forall x : word, ~ WINR0 (bv_unsigned x) -> ~ TABW T (bv_unsigned x) -> m5 x = mem0 x).
{ intros x Hx Ht. rewrite (MEQ5 x Hx). assert (Hu : ~ WINU (bv_unsigned x)) by (img_try (intros Hu; img_exact (Hx (WINU_WINR0 _ Hu)))).
rewrite (MEQ3 x Hu Ht). img_exact (MEQ1 x Hu). }
split; [img_try ((subst m5; cbv beta); img_exact MEQ)|].
split.
{   intros a Ha. pose proof Hsp as (Hlo & Hhi & Hal). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof high_factsR as LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite E2; clear - Ha; numconst; try unfold sp0 in *; zlia)
| img_try (off_by ltac:(pose proof stack_ivsR as SI; clear - Ha Hlo Hhi LF Usp T7 SI; numconst; try unfold sp0 in *; zlia)) ]. }
assert (OWN : forall o, 4 <= o < 16 -> apresent (w_H W) m5 (Pr + o)).
{ intros o Ho. eapply (st_ok_window_apresent_off (w_H W) E0 SU5 _ 35 _ (Pr + o) HS); [img_try ((img_case; vm_compute); img_refl) | | img_try (off_by ltac:(clear - Ho P0 P16 EPr TI HcR; numconst; zlia)) ].
cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]. rewrite EP. clear - Ho. zlia. }
assert (OTH : forall i a, 1 <= i <= 31 -> i <> c -> T + 212 + 80 * i <= a < T + 224 + 80 * i -> m5 (Z_to_bv 64 a) = m3 (Z_to_bv 64 a)).
{ intros i a Hi Hic Ha. img_apply MEQ5. rewrite unsigned_lit_small; [img_try (img_exact (Ztab i a Hi Hic Ha))|]. img_apply Z64. right. left. exists i. split; [img_try (img_exact Hi) | img_try (img_exact Ha)]. }
split.
{ intros i Hi. destruct (Z.eq_dec i c) as [->|Hic].
- split.
+ replace (T + 212 + 80 * c) with (bv_unsigned (ew E0 37) + 4) by (img_try (clear - EP EPr; rewrite EP; zlia)).
eapply (chunk_val_at (w_H W) E0 SU5 _ 35 1 _ _ 4%N _ (max_cached c) _ HS); [img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | img_refl
| img_try (cbn [sv_denot]; unfold rMAX; rewrite EaMAX, Hmax; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; img_refl) | img_try (pose proof (max_cached_range c HcR); cbn; zlia) | img_try (cbn; zlia)].
+ replace (T + 216 + 80 * c) with (bv_unsigned (ew E0 37) + 8) by (img_try (clear - EP EPr; rewrite EP; zlia)).
eapply (chunk_val_at (w_H W) E0 SU5 _ 35 2 _ _ 8%N _ (class_size c) _ HS); [img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | img_refl
| img_try (cbn [sv_denot]; unfold rCSZ; rewrite EaCSZ, Hcsz; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; img_refl) | img_try (rewrite <- Hcsz; cbn; clear - CF4; numconst; zlia) | img_try (cbn; zlia)].
- destruct (proj1 (TBF i Hi)) as [TM TSZ]. split.
+ eapply val_mem_frame; [|img_try (img_exact TM)]. intros k Hk. img_apply (OTH i); [img_try (img_exact Hi) | img_try (img_exact Hic) | img_try (clear - Hk; zlia)].
+ eapply val_mem_frame; [|img_try (img_exact TSZ)]. intros k Hk. img_apply (OTH i); [img_try (img_exact Hi) | img_try (img_exact Hic) | img_try (clear - Hk; zlia)]. }
intros a (i & Hi & Ha). destruct (Z.eq_dec i c) as [->|Hic].
- replace a with (Pr + (a - Pr)) by zlia. img_apply OWN. clear - Ha EPr. zlia.
- img_apply (apresent_same (w_H W) m3); [img_try (img_exact (OTH i a Hi Hic Ha))|].
img_apply writable_off_apresent; [img_try (off_by ltac:(clear - Ha Hi TI TE; numconst; zlia)) |].
replace a with (T + 212 + 80 * i + (a - (T + 212 + 80 * i))) by zlia. img_apply (proj2 (TBF i Hi)). clear - Ha. zlia.
Qed.
End g.
End d.

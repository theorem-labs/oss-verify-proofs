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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3i YF81 YF8b.
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
Local Abbreviation ARg f := (f ly regs0 c) (only parsing).
Local Abbreviation class_facts := ((ARg (@YF7w.class_facts)) maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation AR2 f := (f imgk ly regs0) (only parsing).
Local Abbreviation ARa f := (AR2 f maxc mf au mu) (only parsing).
Local Abbreviation high_factsR := ((ARa (@YF7w.high_factsR _)) IMG LY Hmf Hmu).
Local Abbreviation off_T := ((ARa (@YF7w.off_T _)) IMG LY Hmf Hmu).
Local Abbreviation off_C := ((ARa (@YF7w.off_C _)) IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation AR1 f := (f IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation AR4 f := (f c maxc n nf mf au mu csz) (only parsing).
Local Abbreviation derived_rangesR := (AR1 (AR4 (AR2 (@YF7w.derived_rangesR _)))).
Local Abbreviation WINR0 := (ARg (@YF7w.WINR0)).
Local Abbreviation WINR := ((ARg (@YF7w.WINR)) n).
Local Abbreviation WINR0_WINR := ((ARg (@YF7w.WINR0_WINR)) n).
Local Abbreviation WSKELR := (@YF7w.WSKELR).
Local Abbreviation win_sub := (@YF7w.win_sub).
Local Abbreviation win_sub_sound := ((ARg (@YF7w.win_sub_sound)) maxc n mf au mu Hmax Hn Hmf Hmu).
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
Local Abbreviation pstable := (ARg (@YF7w.pstable)).
Local Abbreviation all_disjoint_of_forall := (@YF7w.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (ARa (@YF7w.kept_of_frame)).
Local Abbreviation kept_of_frame2 := (ARa (@YF7w.kept_of_frame2)).
Local Abbreviation SKEL_TAILR := (@YF7w.SKEL_TAILR imgk).
Local Abbreviation RFACTSR := ((AR2 (@YF7w.RFACTSR)) c).
Local Abbreviation stack_ivsR := (@YF7w.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := ((AR1 (AR4 (AR2 (@YF7w.zone_litR _)))) Hsp).
Local Abbreviation zone_TR := ((AR2 (@YF7w.zone_TR _)) c maxc mf au mu IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := ((AR1 (AR4 (AR2 (@YF7w.zone_CR _)))) Hsp).
Local Abbreviation zone_RGR := ((AR1 (AR4 (AR2 (@YF7w.zone_RGR _)))) Hsp).
Local Abbreviation slots_not_WINR0 := ((AR1 (AR4 (AR2 (@YF7w.slots_not_WINR0 _)))) Hsp).
Local Abbreviation fa_not_WINR0 := ((AR1 (AR4 (AR2 (@YF7w.fa_not_WINR0 _)))) Hsp).
Local Abbreviation tail_ext_okR := ((AR1 (AR0 (AR2 (@YF7w.tail_ext_okR _)))) Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := ((ARa (@YF7w.rdn_of_presentR)) Hmf Hmu).
Local Abbreviation store_ok_of_presentR := ((ARa (@YF7w.store_ok_of_presentR)) Hmf Hmu).
Local Abbreviation AR5 f := (f Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp) (only parsing).
Local Abbreviation AR8 f := (f c maxc nf mf au mu) (only parsing).
Local Abbreviation ARc f := (AR8 f j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu) (only parsing).
Local Abbreviation cpy4_stretch := (AR5 (ARc (AR2 (@YF7w.cpy4_stretch _)))).
Local Abbreviation AR7 f := (f Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug) (only parsing).
Local Abbreviation facts3 := (AR7 (AR1 ((AR4 (AR2 (@YF7w.facts3 _))) need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug))).
Local Abbreviation RFACTS3 := ((AR2 (@YF7w.RFACTS3)) c).
Local Abbreviation tail_ext_ok3 := ((AR1 (AR0 (AR2 (@YF7w.tail_ext_ok3 _)))) Hsp).
Local Abbreviation stack_ext_ok3 := ((AR1 (AR4 (AR2 (@YF7w.stack_ext_ok3 _)))) Hsp).
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
Local Abbreviation at_R3_ret := ((AR5 ((AR0 ((AR2 (@YF7w.at_R3_ret _)) mem0)) HcR Hnf Hmf Hmu)) Hra Htp).
Local Abbreviation at_N3_cont := ((AR1 (AR0 ((AR2 (@YF7w.at_N3_cont _ _)) mem0))) Hsp).
Local Abbreviation memset_stretch3 := (AR5 (ARc (AR2 (@YF7w.memset_stretch3 _)))).
Local Abbreviation nth_Z_to_le_bytes4 := (@YF7w.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (AR5 (ARc (AR2 (@YF7w.popfree_stretch _)))).
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
Local Abbreviation ARe f := (f _ imgk W ly mem0) (only parsing).
Local Abbreviation ARf f := (f B S HARm) (only parsing).
Local Abbreviation cls_wfR := ((ARf ((ARe (@YF8b.cls_wfR)) c HcR)) Hinited).
Local Abbreviation cls_wf0 := (ARf ((ARe (@YF8b.cls_wf0)) c HcR)).
Local Abbreviation AR3 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation AR6 f := (f B S HARm Hnf_def Hmf_def Hau_def Hmu_def) (only parsing).
Local Abbreviation reg_facts0 := (AR6 ((AR8 (AR3 (@YF8b.reg_facts0 _))) HcR)).
Local Abbreviation reg_facts := ((ARf ((AR8 (AR3 (@YF8b.reg_facts _))) HcR Hmax Hsp)) Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (AR6 ((AR8 (AR3 (@YF8b.Hnf' _))) HcR Hsp)).
Local Abbreviation Hmf' := (AR6 ((AR8 (AR3 (@YF8b.Hmf' _))) HcR Hsp)).
Local Abbreviation Hmu' := (AR6 ((AR8 (AR3 (@YF8b.Hmu' _))) HcR Hsp)).
Local Abbreviation Hcarved' := ((ARf ((ARe (@YF8b.Hcarved')) c au mu HcR)) Hau_def Hmu_def).
Local Abbreviation Hau_al' := ((ARf ((ARe (@YF8b.Hau_al')) c au csz HcR Hcsz)) Hau_def).
Local Abbreviation vis_present := (ARf ((AR3 (@YF8b.vis_present _)) maxc)).
Local Abbreviation thread_present := (AR6 ((AR8 (AR3 (@YF8b.thread_present _))) csz IMG LY HcR Hcsz Hsp)).
Local Abbreviation ARb f := (AR4 f IMG LY HcR Hmax Hn Hcsz Hsp) (only parsing).
Local Abbreviation rinfo_present := (AR6 (ARb (AR3 (@YF8b.rinfo_present _)))).
Local Abbreviation HslotPres' := (AR6 (ARb (AR3 (@YF8b.HslotPres' _)))).
Local Abbreviation HfaPres' := (AR6 (ARb (AR3 (@YF8b.HfaPres' _)))).
Local Abbreviation word_of_present := ((AR3 (@YF8b.word_of_present)) maxc).
Local Abbreviation val_mem_lo4 := ((AR2 (@YF8b.val_mem_lo4)) maxc).
Local Abbreviation junk_valuesR := (AR6 (ARb (AR3 (@YF8b.junk_valuesR _)))).
Local Abbreviation cell_sym := ((ARe (@YF8b.cell_sym)) B S TS HARm).
Local Abbreviation cell_lit := ((ARe (@YF8b.cell_lit)) B S TS HARm).
Local Abbreviation cell_state := (ARf (ARe (@YF8b.cell_state))).
Local Abbreviation In_acells_cache := ((ARg (@YF8b.In_acells_cache)) maxc HcR B S).
Local Abbreviation In_acells_region := ((ARg (@YF8b.In_acells_region)) maxc HcR B S).
Local Abbreviation cache_valsR := ((ARf ((AR3 (@YF8b.cache_valsR _)) c maxc csz HcR Hmax Hcsz)) Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@YF8b.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (ARf ((AR3 (@YF8b.cache_valsU _)) maxc)).
Local Abbreviation region_valsR := (AR6 ((AR8 (AR3 (@YF8b.region_valsR _))) HcR)).
Local Abbreviation chunk_lit := (AR0 (AR3 (@YF8b.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR3 (@YF8b.chunk_lit_at))).
Local Abbreviation chunk_atom := (AR0 (AR3 (@YF8b.chunk_atom))).
Local Abbreviation AR9 f := (f Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) (only parsing).
Local Abbreviation ARd f := (f Hpres0R B S TS HTSD HARm) (only parsing).
Local Abbreviation REG0R3_ok_but35 := (AR9 (ARd (AR5 (AR1 (AR0 (AR3 (@YF8b.REG0R3_ok_but35 _))))))).
Local Abbreviation REG0R3_ok := (AR9 ((ARd (AR5 (AR1 (AR0 (AR3 (@YF8b.REG0R3_ok _)))))) Hinited Hchunks)).
Local Abbreviation REG0U3_ok := (AR9 (ARd (AR5 (AR1 (AR0 (AR3 (@YF8b.REG0U3_ok _))))))).
Local Abbreviation PAIRSR3_ok := ((AR1 (AR0 (AR2 (@YF8b.PAIRSR3_ok _)))) Hsp).
Local Abbreviation SPAN3_disj := ((AR1 (AR0 (AR2 (@YF8b.SPAN3_disj _)))) Hsp).
Local Abbreviation FACTSR3_ok := (AR7 (AR5 (AR1 (AR0 (AR2 (@YF8b.FACTSR3_ok _)))))).
Local Abbreviation SEEDR3_ok := (AR9 ((ARd (AR7 ((AR5 (AR1 (AR0 (AR3 (@YF8b.SEEDR3_ok _ _))))) Htp Ha0 Ha1 Ha2 Ha3))) Hinited Hchunks)).
Local Abbreviation PAIRSU3_ok := ((AR1 (AR0 (AR2 (@YF8b.PAIRSU3_ok _)))) Hsp).
Local Abbreviation SEEDU3_ok := (AR9 (ARd (AR7 ((AR5 (AR1 (AR0 (AR3 (@YF8b.SEEDU3_ok _ _))))) Htp Ha0 Ha1 Ha2 Ha3)))).
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
Local Open Scope am_scope.
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition fr : list fseg := rg_free (reg S c).
Definition hol : list (Z * Z) := rg_holes (reg S c).
Lemma len_facts3 : length (st_regions S) = 32%nat /\ length (st_cache S) = 32%nat /\ (Z.to_nat c < 32)%nat.
Proof. pose proof (wf_len_regions _ _ _ _ _ WF). pose proof (wf_len_cache _ _ _ _ _ WF). repeat split; try assumption. clear - HcR. zlia. Qed.
Lemma reg_S : reg S c = mkRegion mu au mf fr hol.
Proof. rewrite Hmu_def, Hau_def, Hmf_def. unfold fr, hol. destruct (reg S c); img_refl. Qed.
Lemma reg_upd3 : forall r', reg (upd_reg c r' S) c = r'.
Proof. intros r'. pose proof len_facts3 as (L1 & _ & L3). img_apply reg_upd_reg; [img_try (clear - HcR; zlia) | img_try (rewrite L1; img_exact L3)]. Qed.
Lemma cache_upd3 : forall r' p', cache (upd_pc c p' (upd_reg c r' S)) c = p'.
Proof. intros r' p'. pose proof len_facts3 as (_ & L2 & L3). img_apply cache_upd_pc; [img_try (clear - HcR; zlia) | img_try (unfold upd_reg; cbn; rewrite L2; img_exact L3)]. Qed.
Lemma PM3 : pc_max (cache S c) = maxc.
Proof. pose proof (wf_classes _ _ _ _ _ WF c HcR) as C. unfold wf_class in C. rewrite Hinited in C. rewrite Hmax. img_exact (proj1 (wr_cache _ _ _ _ _ _ C)). Qed.
Lemma WF1 : prim_user_mapped S + kUserMapSize <= kUserMapSize * st_nev S -> WfP (as_universe B) 1 0 0 S.
Proof.
intros Hpum. destruct WF as [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16].
constructor; try assumption; try (clear; zlia); (unfold kUserMapSize in *; clear - Hpum X8; zlia).
Qed.
Definition rUp : region := mkRegion mu2 au mf fr (del_hole mu hol).
Definition rUm : region := mkRegion mu au mf fr (add_hole (mu, kUserMapSize) hol).
Definition SUp : astate := upd_reg c rUp S.
Definition SUm : astate := upd_reg c rUm S.
Definition MU1 (xg : bool) : Z := if xg then mu2 else mu.
Definition HO1 (xg : bool) : list (Z * Z) := if xg then del_hole mu hol else hol.
Definition NC1 (xg : bool) : Z := if xg then ncg else nce.
Definition NF1 (xg : bool) : Z := if xg then nfg else nfe.
Definition AU1 (xg : bool) : Z := if xg then aug else aue.
Definition rg1 (xg : bool) : region := mkRegion (MU1 xg) au mf fr (HO1 xg).
Definition St1 (xg : bool) : astate := if xg then SUp else S.
Definition rFp (xg : bool) : region := mkRegion (MU1 xg) au mf2 fr (del_hole (kFreeArrayOffset + mf) (HO1 xg)).
Definition rFm (xg : bool) : region := mkRegion (MU1 xg) au mf fr (add_hole (kFreeArrayOffset + mf, kFreeArrayMapSize) (HO1 xg)).
Definition SFp (xg : bool) : astate := upd_reg c (rFp xg) S.
Definition SFm (xg : bool) : astate := upd_reg c (rFm xg) S.
Definition MF2 (yg : bool) : Z := if yg then mf2 else mf.
Definition HO2 (xg yg : bool) : list (Z * Z) := if yg then del_hole (kFreeArrayOffset + mf) (HO1 xg) else HO1 xg.
Definition rg2 (xg yg : bool) : region := mkRegion (MU1 xg) au (MF2 yg) fr (HO2 xg yg).
Definition St2 (xg yg : bool) : astate := if yg then SFp xg else St1 xg.
Definition rP (xg yg : bool) : region := mkRegion (MU1 xg) (AU1 xg) (MF2 yg) (FRun au (NC1 xg) :: fr) (HO2 xg yg).
Definition rQ (xg yg : bool) (rest : list fseg) : region := mkRegion (MU1 xg) (AU1 xg) (MF2 yg) rest (HO2 xg yg).
Definition SQ (xg yg : bool) (tops : list Z) (rest : list fseg) : astate := upd_pc c (mkPC maxc (rev tops)) (upd_reg c (rQ xg yg rest) S).
Lemma S1_eq : forall (xg : bool), St1 xg = upd_reg c (rg1 xg) S.
Proof.
intros [|]; unfold St1, rg1, MU1, HO1; [img_refl|].
pose proof len_facts3 as (L1 & _ & L3). rewrite <- reg_S. symmetry. img_apply upd_reg_same; [img_try (clear - HcR; zlia) | img_try (rewrite L1; img_exact L3)].
Qed.
Lemma reg_S1 : forall (xg : bool), reg (St1 xg) c = rg1 xg.
Proof. intros xg. rewrite S1_eq. img_apply reg_upd3. Qed.
Lemma S2_eq : forall (xg yg : bool), St2 xg yg = upd_reg c (rg2 xg yg) S.
Proof. intros xg [|]; unfold St2, rg2, MF2, HO2; [img_refl | img_try (rewrite S1_eq; img_refl)]. Qed.
Lemma reg_S2 : forall (xg yg : bool), reg (St2 xg yg) c = rg2 xg yg.
Proof. intros xg yg. rewrite S2_eq. img_apply reg_upd3. Qed.
Lemma upd_S1 : forall (xg : bool) r', upd_reg c r' (St1 xg) = upd_reg c r' S.
Proof. intros xg r'. rewrite S1_eq. img_apply upd_reg_upd_reg. Qed.
Lemma upd_S2 : forall (xg yg : bool) r', upd_reg c r' (St2 xg yg) = upd_reg c r' S.
Proof. intros xg yg r'. rewrite S2_eq. img_apply upd_reg_upd_reg. Qed.
Definition XC3 (xg : bool) : Prop := if xg then mu < tot /\ mu + kUserMapSize <= kFreeArrayOffset else tot <= mu.
Lemma factsX3 : forall (xg : bool), XC3 xg ->
0 <= NC1 xg < 2 ^ 16 /\ NF1 xg = nf + NC1 xg /\ AU1 xg = au + NC1 xg * csz /\
NC1 xg * csz <= MU1 xg - au < NC1 xg * csz + csz /\ need <= NC1 xg /\ 0 <= MU1 xg - au /\ MU1 xg <= kFreeArrayOffset /\
(MU1 xg - au) / csz = NC1 xg.
Proof.
intros xg HC. unfold XC3 in HC. pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 &
G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32 & G33 & G34 & G35 & G36 & G37).
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
destruct xg; cbn [NC1 NF1 AU1 MU1].
- destruct HC as [HC HR3]. destruct G19 as [G19a G19b].
assert (L : need * csz < ncg * csz + csz) by (img_try (clear - HC G3 G5 G15 G19b U0 U1; unfold kMaxSize, kUserMapSize in *; zlia)).
assert (NN : need <= ncg) by (img_try (clear - L K4 G1 G18; nia)).
repeat split; first [ assumption | clear - G21; zlia | rewrite G15; clear - U0 U1; unfold kUserMapSize; zlia | rewrite G15; img_exact HR3 | rewrite Hncg; img_refl ].
- destruct G17 as [G17a G17b].
assert (L : need * csz < nce * csz + csz) by (img_try (clear - HC G5 G17b; zlia)).
assert (NN : need <= nce) by (img_try (clear - L K4 G1 G16; nia)).
repeat split; first [ assumption | clear - G20; zlia | clear - U0 U1 G17a G16 K4; nia | clear - U2; zlia | rewrite Hnce; img_refl ].
Qed.
Lemma round_user : mu < tot -> round_up (tot - mu) kUserMapSize = kUserMapSize.
Proof.
intros HC. pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & _). pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
rewrite <- (Z.add_0_l kUserMapSize) at 2. img_apply round_up_step; [img_try (unfold kUserMapSize; clear; zlia) | img_try (clear; img_refl) |].
clear - HC G3 G5 U0 U1. unfold kMaxSize, kUserMapSize in *. zlia.
Qed.
Lemma round_fa : forall (xg : bool), XC3 xg ->
mf < 4 * NF1 xg -> round_up (4 * NF1 xg) kFreeArrayMapSize = mf2.
Proof.
intros xg HC Hlt. pose proof (factsX3 xg HC) as ([N0 N1] & N2 & _). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] M2].
rewrite Hmf2. img_apply round_up_step; [img_try (unfold kFreeArrayMapSize; clear; zlia) | img_try (img_exact M2) |]. clear - N0 N1 N2 F0 F1 Hlt. unfold kFreeArrayMapSize. zlia.
Qed.
Lemma runs_ok_new : forall (xg : bool), XC3 xg -> runs_ok (FRun au (NC1 xg) :: fr).
Proof.
intros xg HC. pose proof (factsX3 xg HC) as (_ & _ & _ & _ & NN & _). pose proof facts3 as (G1 & _).
constructor; [img_try (clear - NN G1; zlia)|]. unfold fr. img_exact (wr_runs _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c HcR)).
Qed.
Lemma pop_new : forall (xg : bool), XC3 xg ->
exists tops rest, fa_pop_n 10000 csz n (FRun au (NC1 xg) :: fr) [] = Some (tops, rest) /\
fa_elems csz (FRun au (NC1 xg) :: fr) = tops ++ fa_elems csz rest /\ fa_len rest = NF1 xg - n /\ runs_ok rest /\ Z.of_nat (length tops) = n.
Proof.
intros xg HC. pose proof (runs_ok_new xg HC) as RU. pose proof (factsX3 xg HC) as ([N0 N1] & N2 & _ & _ & NN & _). pose proof class_facts as (_ & _ & K3 & _).
pose proof Hnf as [F0 _].
assert (FL : fa_len (FRun au (NC1 xg) :: fr) = NF1 xg) by (img_try (cbn [fa_len]; unfold fr; rewrite <- Hnf_def; clear - N2; zlia)).
destruct (fa_pop_n_some 10000 csz n (FRun au (NC1 xg) :: fr) [] RU ltac:(img_try (rewrite FL; clear - N2 N0 NN K3 F0 Hneed; zlia)) ltac:(img_try (img_change (Z.of_nat 10000) with 10000; clear - K3; zlia))) as (tops & rest & EP).
destruct (fa_pop_n_spec 10000 csz n _ [] tops rest RU ltac:(img_try (clear - K3; zlia)) EP) as (E1 & E2 & E3 & E4). cbn [rev app length] in E1, E4.
exists tops, rest. rewrite FL in E2. repeat split; try assumption; clear - E4; zlia.
Qed.
Lemma E_mmu_e : tot <= mu -> map_more_user c need S = IRet (true, S).
Proof.
intros HC. unfold map_more_user. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with false by (img_try (symmetry; img_apply Z.ltb_ge; img_exact HC)). img_refl.
Qed.
Lemma E_mmu_g : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset ->
exists K, map_more_user c need S = IAsk (KMapUser c mu kUserMapSize) S K /\
K 1 = IRet (true, SUp) /\ K 2 = IRet (false, SUm) /\ (forall z, z <> 1 -> z <> 2 -> K z = IRet (false, S)).
Proof.
intros HC HR. unfold map_more_user. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_exact HC)). rewrite (round_user HC).
unfold mcheck. replace (mu + kUserMapSize <=? kFreeArrayOffset) with true by (img_try (symmetry; img_apply Z.leb_le; img_exact HR)).
unfold bind at 1. unfold ret at 1. cbn [ibind]. unfold bind at 1. unfold askz. cbn [ibind].
eexists. split; [img_refl|]. split; [|img_try (split)].
- cbn [aGranted Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SUp, rUp, upd_reg. rewrite Hmu2. img_refl.
- cbn [aGranted aDestroyed Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SUm, rUm, upd_reg. img_refl.
- intros z Z1 Z2. unfold aGranted, aDestroyed. rewrite (proj2 (Z.eqb_neq z 1) Z1), (proj2 (Z.eqb_neq z 2) Z2). unfold bind, ret. cbn [ibind]. img_refl.
Qed.
Lemma E_mmu_fail : mu < tot -> kFreeArrayOffset < mu + kUserMapSize -> exists f, map_more_user c need S = IFail f.
Proof.
intros HC HR. unfold map_more_user. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_exact HC)). rewrite (round_user HC).
unfold mcheck. replace (mu + kUserMapSize <=? kFreeArrayOffset) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact HR)).
unfold bind at 1. unfold fail. cbn [ibind]. eexists. img_refl.
Qed.
Lemma E_efa_e : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg ->
4 * NF1 xg <= mf -> ensure_free_array c (NF1 xg) false s1 = IRet (true, s1).
Proof.
intros xg s1 HC R1 Hle. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. cbn [rg_mapped_fa rg1].
replace (4 * NF1 xg <=? mf) with true by (img_try (symmetry; img_apply Z.leb_le; img_exact Hle)). img_refl.
Qed.
Lemma E_efa_g : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg -> (forall r', upd_reg c r' s1 = upd_reg c r' S) ->
mf < 4 * NF1 xg -> mf2 <= kFreeArrayMax ->
exists K, ensure_free_array c (NF1 xg) false s1 = IAsk (KMapFreeArray c mf kFreeArrayMapSize) s1 K /\
K 1 = IRet (true, SFp xg) /\ K 2 = IRet (false, SFm xg) /\ (forall z, z <> 1 -> z <> 2 -> K z = IRet (false, s1)).
Proof.
intros xg s1 HC R1 U1 Hlt Hmax2. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. cbn [rg_mapped_fa rg_mapped_user rg_alloc_user rg_free rg_holes rg1].
replace (4 * NF1 xg <=? mf) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact Hlt)). rewrite (round_fa xg HC Hlt).
unfold mcheck. replace (mf2 <=? kFreeArrayMax) with true by (img_try (symmetry; img_apply Z.leb_le; img_exact Hmax2)).
unfold bind at 1. unfold ret at 1. cbn [ibind]. unfold bind at 1. unfold askz. cbn [ibind].
replace (mf2 - mf) with kFreeArrayMapSize by (img_try (rewrite Hmf2; clear; zlia)).
eexists. split; [img_refl|]. split; [|img_try (split)].
- cbn [aGranted Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SFp. rewrite <- (U1 (rFp xg)). img_refl.
- cbn [aGranted aDestroyed Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SFm. rewrite <- (U1 (rFm xg)). img_refl.
- intros z Z1 Z2. unfold aGranted, aDestroyed. rewrite (proj2 (Z.eqb_neq z 1) Z1), (proj2 (Z.eqb_neq z 2) Z2). unfold bind, ret. cbn [ibind]. img_refl.
Qed.
Lemma E_efa_fail : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg ->
mf < 4 * NF1 xg -> kFreeArrayMax < mf2 -> exists f, ensure_free_array c (NF1 xg) false s1 = IFail f.
Proof.
intros xg s1 HC R1 Hlt Hmax2. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. cbn [rg_mapped_fa rg_mapped_user rg_alloc_user rg_free rg_holes rg1].
replace (4 * NF1 xg <=? mf) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact Hlt)). rewrite (round_fa xg HC Hlt).
unfold mcheck. replace (mf2 <=? kFreeArrayMax) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact Hmax2)).
unfold bind at 1. unfold fail. cbn [ibind]. eexists. img_refl.
Qed.
Lemma E_tail : forall (xg yg : bool) (s2 : astate) tops rest, XC3 xg -> reg s2 c = rg2 xg yg -> (forall r', upd_reg c r' s2 = upd_reg c r' S) ->
fa_pop_n 10000 csz n (FRun au (NC1 xg) :: fr) [] = Some (tops, rest) ->
(r0 <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r0) (rg_alloc_user r0 + NC1 xg * class_size c) (rg_mapped_fa r0) (FRun (rg_alloc_user r0) (NC1 xg) :: rg_free r0) (rg_holes r0)) ;;
ret true) s2 = IRet (true, upd_reg c (rP xg yg) S) /\
(r3 <- get_region c ;;
if fa_len (rg_free r3) <? n then ret None
else match fa_pop_n 10000 (class_size c) n (rg_free r3) [] with
| None => fail (FModel 1)
| Some (tops0, rest0) => set_region c (mkRegion (rg_mapped_user r3) (rg_alloc_user r3) (rg_mapped_fa r3) rest0 (rg_holes r3)) ;; ret (Some tops0)
end) (upd_reg c (rP xg yg) S) = IRet (Some tops, upd_reg c (rQ xg yg rest) S) /\
set_pc c (mkPC maxc (cache_fill_order tops)) (upd_reg c (rQ xg yg rest) S) = IRet (tt, SQ xg yg tops rest).
Proof.
intros xg yg s2 tops rest HC R2 U2 EP. pose proof (factsX3 xg HC) as ([N0 N1] & N2 & N3 & _ & NN & _). pose proof Hnf as [F0 _].
split; [|img_try (split)].
- unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions s2)) with (reg s2 c). rewrite R2. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes rg2].
unfold bind, set_region, modify, ret. cbn [ibind]. rewrite <- (U2 (rP xg yg)). unfold upd_reg, rP. rewrite N3, <- Hcsz. img_refl.
- unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions (upd_reg c (rP xg yg) S))) with (reg (upd_reg c (rP xg yg) S) c). rewrite reg_upd3. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes rP].
replace (fa_len (FRun au (NC1 xg) :: fr) <? n) with false by (img_try (symmetry; img_apply Z.ltb_ge; cbn [fa_len]; unfold fr; rewrite <- Hnf_def; clear - N2 NN Hneed F0; zlia)).
rewrite <- Hcsz, EP. unfold bind, set_region, modify, ret. cbn [ibind]. rewrite <- (upd_reg_upd_reg c (rP xg yg) (rQ xg yg rest) S). img_refl.
- unfold set_pc, modify, SQ, upd_pc, cache_fill_order. img_refl.
Qed.
Lemma E_tree :
refill_tree c S = (got <- get_from_allocator c n ;; match got with None => ret tt | Some tops => set_pc c (mkPC maxc (cache_fill_order tops)) end) S /\
get_from_allocator c n S =
(ok <- populate c need ;;
if negb ok then ret None
else (r3 <- get_region c ;;
if fa_len (rg_free r3) <? n then ret None
else match fa_pop_n 10000 (class_size c) n (rg_free r3) [] with
| None => fail (FModel 1)
| Some (tops0, rest0) => set_region c (mkRegion (rg_mapped_user r3) (rg_alloc_user r3) (rg_mapped_fa r3) rest0 (rg_holes r3)) ;; ret (Some tops0)
end)) S.
Proof.
split.
- unfold refill_tree. unfold bind at 1. unfold init_cache_if_needed, bind at 1, get. cbn [ibind]. rewrite Hinited. unfold ret at 1. cbn [ibind].
unfold refill_if_empty. unfold bind at 1. unfold get_pc, bind at 1, get, ret at 1. cbn [ibind].
img_change (znth pclass0 c (st_cache S)) with (cache S c). rewrite Hchunks, PM3, <- Hn. img_refl.
- unfold get_from_allocator. unfold bind at 1. unfold get_region at 1. unfold bind at 1, get, ret at 1. cbn [ibind].
img_change (znth region0 c (st_regions S)) with (reg S c). rewrite <- Hnf_def.
replace (nf <? n) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_exact Hnlt)). rewrite <- Hneed. img_refl.
Qed.
Lemma E_pop : populate c need S =
(ok <- map_more_user c need ;;
if negb ok then ret false
else (r0 <- get_region c ;;
ok2 <- ensure_free_array c (fa_len (rg_free r0) + (rg_mapped_user r0 - rg_alloc_user r0) / class_size c) false ;;
if negb ok2 then ret false
else (r4 <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r4) (rg_alloc_user r4 + (rg_mapped_user r0 - rg_alloc_user r0) / class_size c * class_size c) (rg_mapped_fa r4)
(FRun (rg_alloc_user r4) ((rg_mapped_user r0 - rg_alloc_user r0) / class_size c) :: rg_free r4) (rg_holes r4)) ;;
ret true))) S.
Proof. img_refl. Qed.
Lemma E_getreg1 : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg ->
get_region c s1 = IRet (rg1 xg, s1) /\
fa_len (rg_free (rg1 xg)) + (rg_mapped_user (rg1 xg) - rg_alloc_user (rg1 xg)) / class_size c = NF1 xg /\
(rg_mapped_user (rg1 xg) - rg_alloc_user (rg1 xg)) / class_size c = NC1 xg /\ rg_alloc_user (rg1 xg) = au.
Proof.
intros xg s1 HC R1. pose proof (factsX3 xg HC) as (_ & N2 & _ & _ & _ & _ & _ & DV). split; [|img_try (split; [|split])].
- unfold get_region, bind, get, ret. cbn [ibind]. img_change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. img_refl.
- cbn [rg1 rg_free rg_mapped_user rg_alloc_user]. rewrite <- Hcsz, DV. unfold fr. rewrite <- Hnf_def. clear - N2; zlia.
- cbn [rg1 rg_mapped_user rg_alloc_user]. rewrite <- Hcsz. img_exact DV.
- img_refl.
Qed.
Lemma reg_e : reg S c = rg1 false. Proof. rewrite reg_S. img_refl. Qed.
Lemma reg_g : reg SUp c = rg1 true. Proof. unfold SUp. rewrite reg_upd3. img_refl. Qed.
Lemma upd_e : forall r', upd_reg c r' S = upd_reg c r' S. Proof. img_refl. Qed.
Lemma upd_g : forall r', upd_reg c r' SUp = upd_reg c r' S. Proof. intros r'. unfold SUp. img_apply upd_reg_upd_reg. Qed.
Lemma reg_ee : reg S c = rg2 false false. Proof. rewrite reg_S. img_refl. Qed.
Lemma reg_ge : reg SUp c = rg2 true false. Proof. unfold SUp. rewrite reg_upd3. img_refl. Qed.
Lemma reg_xg : forall xg : bool, reg (SFp xg) c = rg2 xg true. Proof. intros xg. unfold SFp. rewrite reg_upd3. img_refl. Qed.
Lemma upd_xg : forall (xg : bool) r', upd_reg c r' (SFp xg) = upd_reg c r' S. Proof. intros xg r'. unfold SFp. img_apply upd_reg_upd_reg. Qed.
End g.
End d.

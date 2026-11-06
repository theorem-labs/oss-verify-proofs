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
pose proof (st_ok_forget2 k E ss ss' H ms clob HS ltac:(img_eqrefl)
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_try ((img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
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
pose proof (at_R3_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:(img_exact HU)) as H2;
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
pose proof (at_R3_forget Wx md X P ss W' c' k clob HR ltac:(img_try (unfold aHAV3; (img_case; cbv); zlia)) ltac:(img_eqrefl)
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
Definition PT : (word -> option byte) -> Prop := fun _ => True.
Lemma pstable_PT : pstable PT. Proof. clear3. intros m m' _ _. img_exact I. Qed.
Lemma WX0 : forall a, WINR0 a -> WINR0 a. Proof. clear3. intros a H; img_exact H. Qed.
Lemma at_R3_init : at_R3 W md0 WINR0 PT R3_J W cfg0.
Proof. img_exact SEEDJ. Qed.
Lemma seg3J : forall mat, st_ok tfxsegs E0 SS0R3 (restrict (w_H W) (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs))) ->
SRr tfxsegs W (mkCfg (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) (at_R3 W md0 WINR0 PT R3_J).
Proof.
intros mat SEED0. pose proof pstable_PT as HP.
assert (HR : at_R3 W md0 WINR0 PT SS0R3 W (mkCfg (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0))).
{ clear - SEED0 Hpres0R. split; [img_refl|]. exists (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)), mat, E0. split; [img_refl|].
split; [img_try (split; [intros; img_refl | img_refl])|]. split; [img_try (img_exact SEED0)|]. split; [img_try (intros; img_refl)|]. split; [img_try (img_exact Hpres0R) | img_try (img_exact I)]. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x3672c + D_150) (runto (0x3672c + D_150) SS0R3) WX0 HP.
r3_forget HR hJ0 CLOB_INIT. r3_noconds HR. r3_station HR R3_J.
img_apply SRr_ret. img_exact HR.
Qed.
Lemma land_hi0 : forall x, 0 <= x < 2 ^ 18 -> Z.land x (2 ^ 64 - 2 ^ 18) = 0.
Proof. clear.
intros x Hx. replace (2 ^ 64 - 2 ^ 18) with (Z.ldiff (Z.ones 64) (Z.ones 18)) by img_refl.
img_apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
destruct (Z_lt_le_dec i 18) as [L|L].
- rewrite (Z.ones_spec_low 18 i) by zlia. cbn [negb]. rewrite !Bool.andb_false_r. img_refl.
- rewrite (Z.bits_above_log2 x i); [img_refl | img_try (zlia) |]. destruct (Z.eq_dec x 0) as [->|NZ]; [img_try (cbn; zlia)|].
img_apply (Z.lt_le_trans _ 18); [|img_try (zlia)]. img_apply Z.log2_lt_pow2; zlia.
Qed.
Lemma seg3P : SRr tfxsegs W cfg0 (at_R3 W md0 WINR0 PT R3_P).
Proof.
pose proof at_R3_init as HR. pose proof pstable_PT as HP.
pose proof class_facts as (CF1 & CF2 & CF3 & CF4 & CF5). pose proof derived_rangesR as DR. pose proof high_factsR as LF.
pose proof Hnf as [NF1 NF2]. pose proof Hmf as [MF1 MF2]. pose proof Hmu as (MU1 & MU2 & MU3 & MU4). pose proof facts3 as (G1 & _).
clear Hcarved Hau_al Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in DR, LF.
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36730 + D_150) R3_10 WX0 HP.
r3_pin HR (9%bv : bv 5) (SOff rN 0).
{ clear - CF1 CF2 CF3 Hn. pin_zev3. unfold rN, rMAX. rewrite EaN, EaMAX. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (maxc + 0)) by (img_try (unfold M64; zlia)). rewrite (zcanon_id 1) by (img_try (unfold M64; zlia)). rewrite (zcanon_id (n + 0)) by (img_try (unfold M64; zlia)).
rewrite (Z.mod_small (maxc + 0)) by zlia. img_change (Z.land (1 mod 2 ^ 32) 31) with 1.
rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 1) with 2. rewrite !Z.add_0_r, <- Hn.
rewrite bv_swrap_small. 2:{ unfold bv_half_modulus, bv_modulus. img_change (2 ^ Z.of_N 32 / 2) with 2147483648. zlia. }
rewrite bv_wrap_small. 2:{ unfold bv_modulus. img_change (2 ^ Z.of_N 64) with 18446744073709551616. zlia. } img_refl. }
r3_station HR R3_1.
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x3688c + D_150) R3_A0 WX0 HP.
r3_pin HR (8%bv : bv 5) (SOff rRG 0).
{ clear - SB DR LF HcR. pin_zev3. unfold rRG, rSB, rCL. rewrite EaRG, EaSB, EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 7) with 128. zcanon_simp. unfold RGv, kRegionInfoOff in *. unfold SB in *. zlia. }
r3_pin HR (20%bv : bv 5) (SOff rFA 0).
{ clear - SB DR LF HcR. pin_zev3. unfold rFA, rSB, rCL. rewrite EaFA, EaSB, EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. zcanon_simp. unfold FAv, RBv, kFreeArrayOffset in *. unfold SB in *. zlia. }
r3_station HR R3_A.
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36960 + D_150) R3_B WX0 HP.
r3_arm HR BC_LTU true (SOff rNF 0) (SOff rN 0).
{ clear - NF1 NF2 MF1 CF3 Hnlt. rewrite branch_ltu_U. unfold rNF, rN. rewrite (U_atom E0 44 nf EaNF), (U_atom E0 39 n EaN); [|img_try (zlia)| img_try (unfold kFreeArrayMax in *; zlia)]. img_apply Z.ltb_lt. img_exact Hnlt. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36b4c + D_150) R3_P0 WX0 HP.
r3_pin HR (14%bv : bv 5) (SOff rNEED 0).
{ clear - NF1 NF2 MF1 CF3 Hnlt G1 Hneed. pin_zev3. unfold rNEED, rN, rNF. rewrite EaNEED, EaN, EaNF. unfold w64. rewrite !unsigned_lit_small by (img_try (unfold kFreeArrayMax in *; zlia)).
rewrite (zcanon_id (need + 0)), (zcanon_id (n + 0)), (zcanon_id (nf + 0)) by (img_try (unfold M64, kFreeArrayMax in *; zlia)).
unfold zcanon, M64. img_change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite Zplus_mod_idemp_r.
replace (n + 0 + (nf + 0) * (2 ^ 64 - 1)) with (need + nf * 2 ^ 64) by (img_try (rewrite Hneed; zlia)).
rewrite Z_mod_plus_full. rewrite Z.add_0_r. symmetry. img_apply Z.mod_small. zlia. }
r3_station HR R3_P. img_apply SRr_ret. img_exact HR.
Qed.
Definition T16 : sv := SAlu ALU_SLL (SOff 36 0) (SLit 5).
Definition TMID : sv :=
SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SOff 36 0) (SLit 63)) (SLit 63)) (SAlu ALU_SRL (SAlu ALU_SLL (SLit 512) (SAlu ALU_SRL (SOff 36 (-16)) (SLit 1))) (SLit 1)))
(SAlu ALU_SLL (SLit 512) (SAlu ALU_SRL (SOff 36 (-16)) (SLit 1))).
Lemma U_csz : U E0 (SOff rCSZ 0) = csz.
Proof. clear3. pose proof class_facts as (_ & _ & _ & K4 & _). unfold rCSZ. img_apply (U_atom E0 40 csz EaCSZ). unfold kMaxSize in K4. zlia. Qed.
Lemma U_csz31 : c = 31 -> U E0 (SLit 64) = csz.
Proof. clear3. intros E. rewrite Hcsz, E. img_refl. Qed.
Lemma U_csz16 : c <= 16 -> c <> 31 -> U E0 T16 = csz.
Proof. clear3.
intros L N. rewrite (U_zev E0 T16 ltac:(img_eqrefl)). cbn [zev zalu_raw zmd_raw T16]. unfold rho_of. rewrite EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (c + 0)), (zcanon_id 5) by (img_try (unfold M64; zlia)). img_change (Z.land 5 63) with 5. rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 5) with 32.
rewrite zcanon_id by (img_try (unfold M64; zlia)). rewrite Hcsz. unfold class_size.
replace (c =? 31) with false by (img_try (symmetry; img_apply Z.eqb_neq; img_exact N)). replace (c <=? 16) with true by (img_try (symmetry; img_apply Z.leb_le; img_exact L)). zlia.
Qed.
Lemma U_cszmid : 17 <= c <= 30 -> U E0 TMID = csz.
Proof. clear3.
intros R. rewrite (U_zev E0 TMID ltac:(img_eqrefl)). cbn [zev zalu_raw zmd_raw TMID]. unfold rho_of. rewrite EaCL. unfold w64. rewrite !unsigned_lit_small by zlia. rewrite Hcsz.
clear - R. assert (H : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by zlia.
clear R. destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]; rewrite E; (img_case; vm_compute); img_refl.
Qed.
Lemma U_tot_of : forall t, U E0 t = csz -> svpure t = true ->
U E0 (SOff rTOT 0) = U E0 (SAlu ALU_ADD (SOff 46 0) (SMd M_MUL t (SOff 55 0))).
Proof.
intros t Ht Hp. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof Hmu as ([U0 U1] & U2 & _). pose proof class_facts as (_ & _ & _ & K4 & _). clear3.
rewrite (U_zev E0 (SAlu ALU_ADD (SOff 46 0) (SMd M_MUL t (SOff 55 0)))) by (img_try (cbn [svpure andb]; rewrite Hp; img_refl)).
cbn [zev zalu_raw zmd_raw]. rewrite <- (U_zev E0 t Hp), Ht. unfold rho_of, rTOT. rewrite EaAU, EaNEED.
rewrite (U_atom E0 56 tot EaTOT) by (img_try (unfold kMaxSize, kFreeArrayOffset in *; nia)).
unfold w64. rewrite !unsigned_lit_small by (img_try (unfold kFreeArrayOffset in *; zlia)).
rewrite (zcanon_id (au + 0)), (zcanon_id (need + 0)) by (img_try (unfold M64, kFreeArrayOffset in *; zlia)).
rewrite (zcanon_id (csz * (need + 0))) by (img_try (unfold M64, kMaxSize in *; nia)). rewrite zcanon_id by (img_try (unfold M64, kMaxSize, kFreeArrayOffset in *; nia)). rewrite G5. zlia.
Qed.
Lemma U_tot31 : c = 31 -> U E0 (SOff rTOT 0) = U E0 (SAlu ALU_ADD (SOff 46 0) (SAlu ALU_SLL (SOff 55 0) (SLit 6))).
Proof.
intros E. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof Hmu as ([U0 U1] & U2 & _).
assert (C64 : csz = 64) by (img_try (rewrite Hcsz, E; img_refl)). clear3.
pin_zev3. unfold rTOT. rewrite EaAU, EaNEED, EaTOT. unfold w64. rewrite !unsigned_lit_small by (img_try (unfold kMaxSize, kFreeArrayOffset in *; nia)).
rewrite (zcanon_id (au + 0)), (zcanon_id (need + 0)), (zcanon_id 6) by (img_try (unfold M64, kFreeArrayOffset in *; zlia)). img_change (Z.land 6 63) with 6.
rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 6) with 64. rewrite (zcanon_id ((need + 0) * 64)) by (img_try (unfold M64; zlia)).
rewrite !zcanon_id by (img_try (unfold M64, kFreeArrayOffset in *; zlia)). rewrite G5, C64. zlia.
Qed.
Lemma U_rb : U E0 (SOff rRB 0) = U E0 (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 36 0) (SLit 32))).
Proof. clear3.
pose proof derived_rangesR as DR. pose proof high_factsR as (_ & _ & F3 & F4 & F5 & F6 & _).
pin_zev3. unfold rRB. rewrite EaRB, EaSB, EaCL. unfold w64. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize in *.
rewrite !unsigned_lit_small by (img_try (unfold SB; zlia)).
rewrite (zcanon_id (c + 0)), (zcanon_id 32), (zcanon_id (ly_space ly + 0)) by (img_try (unfold M64; zlia)). img_change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2 by zlia. rewrite (zcanon_id ((c + 0) * 2 ^ 32)) by (img_try (unfold M64; zlia)).
rewrite !zcanon_id by (img_try (unfold M64, RBv, SB in *; zlia)). unfold RBv, SB. zlia.
Qed.
Lemma seg3Q31 : c = 31 -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfxsegs W' c' (at_R3 W md0 WINR0 PT R3_Q31).
Proof.
intros E W' c' HR. pose proof pstable_PT as HP.
r3_arm HR BC_EQ true (SOff rCL 0) (SLit 31).
{ rewrite branch_eq_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (img_try (clear - HcR; zlia)). img_apply Z.eqb_eq. rewrite E. img_refl. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36d68 + D_150) R3_Q31a WX0 HP.
r3_pin HR (21%bv : bv 5) (SOff rCSZ 0). { rewrite U_csz. symmetry. img_exact (U_csz31 E). }
r3_pin HR (19%bv : bv 5) (SOff rTOT 0). { img_exact (U_tot31 E). }
r3_pin HR (18%bv : bv 5) (SOff rRB 0). { img_exact U_rb. }
r3_station HR R3_Q31. img_apply SRr_ret. img_exact HR.
Qed.
Lemma seg3Q16 : c <= 16 -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfxsegs W' c' (at_R3 W md0 WINR0 PT R3_Q16).
Proof.
intros L W' c' HR. pose proof pstable_PT as HP. assert (N : c <> 31) by (img_try (clear - L; zlia)).
r3_arm HR BC_EQ false (SOff rCL 0) (SLit 31).
{ rewrite branch_eq_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (img_try (clear - HcR; zlia)). img_apply Z.eqb_neq. rewrite (U_zev E0 (SLit 31) ltac:(img_eqrefl)). img_change (zev (rho_of E0) (SLit 31)) with 31. img_exact N. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36b54 + D_150) R3_Pn31 WX0 HP.
r3_arm HR BC_LTU false (SLit 16) (SOff rCL 0).
{ rewrite branch_ltu_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (img_try (clear - HcR; zlia)). rewrite (U_zev E0 (SLit 16) ltac:(img_eqrefl)). img_change (zev (rho_of E0) (SLit 16)) with 16. img_apply Z.ltb_ge. img_exact L. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36b70 + D_150) R3_Q16a WX0 HP.
r3_pin HR (21%bv : bv 5) (SOff rCSZ 0). { rewrite U_csz. symmetry. img_exact (U_csz16 L N). }
r3_pin HR (19%bv : bv 5) (SOff rTOT 0). { img_exact (U_tot_of T16 (U_csz16 L N) ltac:(img_eqrefl)). }
r3_pin HR (18%bv : bv 5) (SOff rRB 0). { img_exact U_rb. }
r3_station HR R3_Q16. img_apply SRr_ret. img_exact HR.
Qed.
Lemma seg3Qmid : 17 <= c <= 30 -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfxsegs W' c' (at_R3 W md0 WINR0 PT R3_Qmid).
Proof.
intros R W' c' HR. pose proof pstable_PT as HP. assert (N : c <> 31) by (img_try (clear - R; zlia)).
r3_arm HR BC_EQ false (SOff rCL 0) (SLit 31).
{ rewrite branch_eq_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (img_try (clear - HcR; zlia)). img_apply Z.eqb_neq. rewrite (U_zev E0 (SLit 31) ltac:(img_eqrefl)). img_change (zev (rho_of E0) (SLit 31)) with 31. img_exact N. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36b54 + D_150) R3_Pn31 WX0 HP.
r3_arm HR BC_LTU true (SLit 16) (SOff rCL 0).
{ rewrite branch_ltu_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (img_try (clear - HcR; zlia)). rewrite (U_zev E0 (SLit 16) ltac:(img_eqrefl)). img_change (zev (rho_of E0) (SLit 16)) with 16. img_apply Z.ltb_lt. clear - R; zlia. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36bb0 + D_150) R3_Qmida WX0 HP.
r3_pin HR (21%bv : bv 5) (SOff rCSZ 0). { rewrite U_csz. symmetry. img_exact (U_cszmid R). }
r3_pin HR (19%bv : bv 5) (SOff rTOT 0). { img_exact (U_tot_of TMID (U_cszmid R) ltac:(img_eqrefl)). }
r3_pin HR (18%bv : bv 5) (SOff rRB 0). { img_exact U_rb. }
r3_station HR R3_Qmid. img_apply SRr_ret. img_exact HR.
Qed.
Lemma U_mu : U E0 (SOff rMU 0) = mu.
Proof. clear3. pose proof Hmu as ([U0 U1] & U2 & _). unfold rMU. img_apply (U_atom E0 47 mu EaMU). unfold kFreeArrayOffset in *; zlia. Qed.
Lemma U_tot : U E0 (SOff rTOT 0) = tot.
Proof. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof Hmu as ([U0 U1] & U2 & _). pose proof class_facts as (_ & _ & _ & K4 & _). unfold rTOT. img_apply (U_atom E0 56 tot EaTOT). clear - G1 G3 G5 U0 U1 U2 K4. unfold kMaxSize, kFreeArrayOffset in *; nia. Qed.
Lemma seg3Q_map : mu < tot -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfxsegs W' c' (at_R3 W md0 WINR0 PT R3_M).
Proof.
intros Hlt W' c' HR. pose proof pstable_PT as HP.
assert (BT : branch_taken BC_LTU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = true) by (img_try (rewrite branch_ltu_U, U_mu, U_tot; img_apply Z.ltb_lt; img_exact Hlt)).
assert (BF : branch_taken BC_GEU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = false) by (img_try (rewrite branch_geu_U, U_mu, U_tot; rewrite (proj2 (Z.ltb_lt mu tot) Hlt); img_refl)).
destruct (Z.eq_dec c 31) as [E|N]; [|img_try (destruct (Z_le_dec c 16) as [L|G])].
- eapply SRr_bind; [img_try (img_exact (seg3Q31 E W' c' HR))|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU true (SOff rMU 0) (SOff rTOT 0); [img_try (img_exact BT)|].
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36bb4 + D_150) (runto (0x36bb4 + D_150) (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q31)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. r3_station HR R3_M. img_apply SRr_ret. img_exact HR.
- eapply SRr_bind; [img_try (img_exact (seg3Q16 L W' c' HR))|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU true (SOff rMU 0) (SOff rTOT 0); [img_try (img_exact BT)|].
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36bb4 + D_150) (runto (0x36bb4 + D_150) (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q16)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_M_16 in HR. img_apply SRr_ret. img_exact HR.
- eapply SRr_bind; [img_try (img_exact (seg3Qmid ltac:(zlia) W' c' HR))|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_GEU false (SOff rMU 0) (SOff rTOT 0); [img_try (img_exact BF)|].
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36bb4 + D_150) (runto (0x36bb4 + D_150) (arm BC_GEU false (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_M_mid in HR. img_apply SRr_ret. img_exact HR.
Qed.
Lemma seg3Q_ok : tot <= mu -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfxsegs W' c' (at_R3 W md0 WINR0 PT R3_Ke).
Proof.
intros Hge W' c' HR. pose proof pstable_PT as HP.
assert (BF : branch_taken BC_LTU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = false) by (img_try (rewrite branch_ltu_U, U_mu, U_tot; img_apply Z.ltb_ge; zlia)).
assert (BT : branch_taken BC_GEU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = true) by (img_try (rewrite branch_geu_U, U_mu, U_tot; rewrite (proj2 (Z.ltb_ge mu tot) Hge); img_refl)).
destruct (Z.eq_dec c 31) as [E|N]; [|img_try (destruct (Z_le_dec c 16) as [L|G])].
- eapply SRr_bind; [img_try (img_exact (seg3Q31 E W' c' HR))|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU false (SOff rMU 0) (SOff rTOT 0); [img_try (img_exact BF)|].
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36c88 + D_150) (runto (0x36c88 + D_150) (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q31)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. r3_station HR R3_Ke. img_apply SRr_ret. img_exact HR.
- eapply SRr_bind; [img_try (img_exact (seg3Q16 L W' c' HR))|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU false (SOff rMU 0) (SOff rTOT 0); [img_try (img_exact BF)|].
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36c88 + D_150) (runto (0x36c88 + D_150) (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q16)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_Ke_16 in HR. img_apply SRr_ret. img_exact HR.
- eapply SRr_bind; [img_try (img_exact (seg3Qmid ltac:(zlia) W' c' HR))|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_GEU true (SOff rMU 0) (SOff rTOT 0); [img_try (img_exact BT)|].
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36c88 + D_150) (runto (0x36c88 + D_150) (arm BC_GEU true (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_Ke_mid in HR. img_apply SRr_ret. img_exact HR.
Qed.
Lemma seg3M : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset ->
forall W' c', at_R3 W md0 WINR0 PT R3_M W' c' -> SRr tfxsegs W' c' (at_N3 W md0 WINR0 PT R3_NU).
Proof.
intros Hlt Hroom W' c' HR. pose proof pstable_PT as HP. pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & _).
pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
assert (J2 : SRr tfxsegs W' c' (at_R3 W md0 WINR0 PT R3_M2)).
{ destruct (Z.eq_dec mu 0) as [Z0|NZ].
- r3_arm HR BC_EQ true (SOff rMU 0) (SLit 0). { rewrite branch_eq_U, U_mu. img_apply Z.eqb_eq. rewrite Z0. img_refl. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36bb8 + D_150) R3_M2z WX0 HP.
r3_pin HR (20%bv : bv 5) (SOff rMU 0). { rewrite U_mu, Z0. img_refl. }
r3_forget HR hJ2 [11%bv : bv 5]. r3_noconds HR. rewrite R3_M2_z in HR. img_apply SRr_ret. img_exact HR.
- r3_arm HR BC_EQ false (SOff rMU 0) (SLit 0). { rewrite branch_eq_U, U_mu. img_apply Z.eqb_neq. img_change (U E0 (SLit 0)) with 0. img_exact NZ. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36bb8 + D_150) (runto (0x36bb8 + D_150) (arm BC_EQ false (SOff rMU 0) (SLit 0) R3_M)) WX0 HP.
r3_forget HR hJ2 [11%bv : bv 5]. r3_noconds HR. r3_station HR R3_M2. img_apply SRr_ret. img_exact HR. }
clear HR. eapply SRr_bind; [img_try (img_exact J2)|]. clear J2. intros W2 c2 _ HR.
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36bd4 + D_150) (runto (0x36bd4 + D_150) R3_M2) WX0 HP.
r3_pin HR (19%bv : bv 5) (SLit 262144).
{ pin_zev3. rewrite EaTOT, EaMU. unfold w64. rewrite !unsigned_lit_small by (img_try (clear - G3 G4 G5 U0 U1 U2; unfold kMaxSize, kFreeArrayOffset in *; zlia)).
clear - imgk G3 G4 G5 U0 U1 U2 Hlt. unfold kMaxSize, kFreeArrayOffset in *.
rewrite (zcanon_id (tot + 0)), (zcanon_id (mu + 0)) by (img_try (unfold M64; zlia)). img_change (zcanon (-1)) with (2 ^ 64 - 1). img_change (zcanon (-262144)) with (2 ^ 64 - 2 ^ 18).
rewrite lxor_ones64 by zlia. rewrite (zcanon_id (2 ^ 64 - 1 - (mu + 0))) by (img_try (unfold M64; zlia)).
replace (zcanon (tot + 0 + (2 ^ 64 - 1 - (mu + 0)))) with (tot - mu - 1).
2:{ unfold zcanon, M64. replace (tot + 0 + (2 ^ 64 - 1 - (mu + 0))) with ((tot - mu - 1) + 1 * 2 ^ 64) by zlia. rewrite Z_mod_plus_full. symmetry. img_apply Z.mod_small. zlia. }
rewrite land_hi0 by zlia. img_refl. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36be8 + D_150) R3_M4 WX0 HP.
r3_arm HR BC_GEU false (SOff rMU 262144) (SLit 3758096385).
{ rewrite branch_geu_U. unfold rMU. rewrite (U_atom_off E0 47 mu 262144 EaMU) by (img_try (clear - U0 U1 U2 Hroom; unfold kFreeArrayOffset, kUserMapSize in *; zlia)).
img_change (U E0 (SLit 3758096385)) with 3758096385. rewrite (proj2 (Z.ltb_lt _ _)); [img_refl|]. clear - Hroom. unfold kFreeArrayOffset, kUserMapSize in *. zlia. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x6ebd4 + D_2c4) R3_M5a WX0 HP.
assert (UADR : U E0 (SOff rADR 0) = U E0 (SAlu ALU_ADD (SOff 42 0) (SOff 47 0))).
{ pin_zev3. unfold rADR. rewrite EaADR, EaRB, EaMU. unfold w64. pose proof derived_rangesR as DR. pose proof high_factsR as (_ & _ & F3 & F4 & F5 & F6 & _).
clear - G6 G7 G10 U0 U1 U2 DR F3 F4 F5 F6. numconst.
rewrite (unsigned_lit_small adr), (unsigned_lit_small RBv), (unsigned_lit_small mu) by zlia.
rewrite (zcanon_id (adr + 0)), (zcanon_id (RBv + 0)), (zcanon_id (mu + 0)) by (img_try (unfold M64; zlia)). rewrite zcanon_id by (img_try (unfold M64; zlia)). zlia. }
r3_pin HR (11%bv : bv 5) (SOff rADR 0). { img_exact UADR. }
r3_pin HR (20%bv : bv 5) (SOff rADR 0). { img_exact UADR. }
r3_station HR R3_M5.
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W4 ?c4 =>
let cs := img_ev (match nth_error (ss_mem R3_NU) 0 with Some r => YQ0b.r_chunks r | None => [] end) in
eapply (at_R3_run_ecall Wx tfxtbl_rtC tfxtbl_rtC_ok 0x7ffffff0 md X P ss R3_NU W4 c4 HR);
[ img_try ((img_case; vm_compute); img_refl) | img_refl | img_try (img_exact WX0) | img_try ((img_case; vm_compute); img_refl) | img_try (img_exact HP) | img_try (exists cs; (img_case; vm_compute); img_refl) ] end.
Qed.
End g.
End d.

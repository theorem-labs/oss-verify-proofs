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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3i YF81 YF80 YF8b YF82.
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
Local Abbreviation AR4 f := (f imgk ly regs0) (only parsing).
Local Abbreviation ARa f := (AR4 f maxc mf au mu) (only parsing).
Local Abbreviation high_factsR := ((ARa (@YF7w.high_factsR _)) IMG LY Hmf Hmu).
Local Abbreviation off_T := ((ARa (@YF7w.off_T _)) IMG LY Hmf Hmu).
Local Abbreviation off_C := ((ARa (@YF7w.off_C _)) IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation AR1 f := (f IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation AR5 f := (f c maxc n nf mf au mu csz) (only parsing).
Local Abbreviation derived_rangesR := (AR1 (AR5 (AR4 (@YF7w.derived_rangesR _)))).
Local Abbreviation WINR0 := (ARg (@YF7w.WINR0)).
Local Abbreviation WINR := ((ARg (@YF7w.WINR)) n).
Local Abbreviation WINR0_WINR := ((ARg (@YF7w.WINR0_WINR)) n).
Local Abbreviation WSKELR := (@YF7w.WSKELR).
Local Abbreviation win_sub := (@YF7w.win_sub).
Local Abbreviation win_sub_sound := ((ARg (@YF7w.win_sub_sound)) maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (AR1 (AR0 (AR4 (@YF7w.WSKELR_WINR0 _)))).
Local Abbreviation windows_WINR0 := (AR1 (AR0 (AR4 (@YF7w.windows_WINR0 _)))).
Local Abbreviation frame_WINR0 := (AR1 (AR0 (AR4 (@YF7w.frame_WINR0 _)))).
Local Abbreviation frame_X := (AR1 (AR0 (AR4 (@YF7w.frame_X _)))).
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
Local Abbreviation at_R3 := (AR0 ((AR4 (@YF7w.at_R3 _)) mem0)).
Local Abbreviation at_N3 := (AR0 ((AR4 (@YF7w.at_N3 _)) mem0)).
Local Abbreviation at_RET3 := (@YF7w.at_RET3 _ regs0 mem0 imgk).
Local Abbreviation P_cells := (@YF7w.P_cells imgk ly c maxc csz).
Local Abbreviation chunk_index := (@YF7w.chunk_index).
Local Abbreviation pstable := (ARg (@YF7w.pstable)).
Local Abbreviation all_disjoint_of_forall := (@YF7w.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (ARa (@YF7w.kept_of_frame)).
Local Abbreviation kept_of_frame2 := (ARa (@YF7w.kept_of_frame2)).
Local Abbreviation SKEL_TAILR := (@YF7w.SKEL_TAILR imgk).
Local Abbreviation RFACTSR := ((AR4 (@YF7w.RFACTSR)) c).
Local Abbreviation stack_ivsR := (@YF7w.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation ARc f := (AR1 f Hsp) (only parsing).
Local Abbreviation zone_litR := (ARc (AR5 (AR4 (@YF7w.zone_litR _)))).
Local Abbreviation zone_TR := ((AR4 (@YF7w.zone_TR _)) c maxc mf au mu IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := (ARc (AR5 (AR4 (@YF7w.zone_CR _)))).
Local Abbreviation zone_RGR := (ARc (AR5 (AR4 (@YF7w.zone_RGR _)))).
Local Abbreviation slots_not_WINR0 := (ARc (AR5 (AR4 (@YF7w.slots_not_WINR0 _)))).
Local Abbreviation fa_not_WINR0 := (ARc (AR5 (AR4 (@YF7w.fa_not_WINR0 _)))).
Local Abbreviation tail_ext_okR := (ARc (AR0 (AR4 (@YF7w.tail_ext_okR _)))).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := ((ARa (@YF7w.rdn_of_presentR)) Hmf Hmu).
Local Abbreviation store_ok_of_presentR := ((ARa (@YF7w.store_ok_of_presentR)) Hmf Hmu).
Local Abbreviation AR6 f := (f Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp) (only parsing).
Local Abbreviation AR8 f := (f c maxc nf mf au mu) (only parsing).
Local Abbreviation ARd f := (AR8 f j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu) (only parsing).
Local Abbreviation cpy4_stretch := (AR6 (ARd (AR4 (@YF7w.cpy4_stretch _)))).
Local Abbreviation AR2 f := (f Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug) (only parsing).
Local Abbreviation facts3 := (AR2 (AR1 ((AR5 (AR4 (@YF7w.facts3 _))) need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug))).
Local Abbreviation RFACTS3 := ((AR4 (@YF7w.RFACTS3)) c).
Local Abbreviation tail_ext_ok3 := (ARc (AR0 (AR4 (@YF7w.tail_ext_ok3 _)))).
Local Abbreviation stack_ext_ok3 := (ARc (AR5 (AR4 (@YF7w.stack_ext_ok3 _)))).
Local Abbreviation scratch_headed := (@YF7w.scratch_headed).
Local Abbreviation mem_ok_scratch_present := ((AR0 (AR4 (@YF7w.mem_ok_scratch_present _))) LY Hmf Hmu Hsp).
Local Abbreviation at_R3_run := (ARc (AR0 ((AR4 (@YF7w.at_R3_run _ _)) mem0))).
Local Abbreviation at_R3_run_ecall := (ARc (AR0 ((AR4 (@YF7w.at_R3_run_ecall _ _)) mem0))).
Local Abbreviation at_R3_pin := (AR0 ((AR4 (@YF7w.at_R3_pin _)) mem0)).
Local Abbreviation at_R3_arm := (AR0 ((AR4 (@YF7w.at_R3_arm _)) mem0)).
Local Abbreviation at_R3_forget := (AR0 ((AR4 (@YF7w.at_R3_forget _)) mem0)).
Local Abbreviation at_R3_noconds := (AR0 ((AR4 (@YF7w.at_R3_noconds _)) mem0)).
Local Abbreviation at_R3_weaken := (AR0 ((AR4 (@YF7w.at_R3_weaken _)) mem0)).
Local Abbreviation at_R3_facts := (AR0 ((AR4 (@YF7w.at_R3_facts _)) mem0)).
Local Abbreviation at_R3_strengthen := (AR0 ((AR4 (@YF7w.at_R3_strengthen _)) mem0)).
Local Abbreviation at_R3_eq := (AR0 ((AR4 (@YF7w.at_R3_eq _)) mem0)).
Local Abbreviation CSAVED := (@YF7w.CSAVED).
Local Abbreviation sv_denot_SOff0 := (@YF7w.sv_denot_SOff0).
Local Abbreviation at_R3_ret := ((AR6 ((AR0 ((AR4 (@YF7w.at_R3_ret _)) mem0)) HcR Hnf Hmf Hmu)) Hra Htp).
Local Abbreviation at_N3_cont := (ARc (AR0 ((AR4 (@YF7w.at_N3_cont _ _)) mem0))).
Local Abbreviation memset_stretch3 := (AR6 (ARd (AR4 (@YF7w.memset_stretch3 _)))).
Local Abbreviation nth_Z_to_le_bytes4 := (@YF7w.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (AR6 (ARd (AR4 (@YF7w.popfree_stretch _)))).
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
Local Abbreviation ARf f := (f _ imgk W ly mem0) (only parsing).
Local Abbreviation ARh f := (f B S HARm) (only parsing).
Local Abbreviation cls_wfR := ((ARh ((ARf (@YF8b.cls_wfR)) c HcR)) Hinited).
Local Abbreviation cls_wf0 := (ARh ((ARf (@YF8b.cls_wf0)) c HcR)).
Local Abbreviation AR3 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation AR7 f := (f B S HARm Hnf_def Hmf_def Hau_def Hmu_def) (only parsing).
Local Abbreviation reg_facts0 := (AR7 ((AR8 (AR3 (@YF8b.reg_facts0 _))) HcR)).
Local Abbreviation reg_facts := ((ARh ((AR8 (AR3 (@YF8b.reg_facts _))) HcR Hmax Hsp)) Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (AR7 ((AR8 (AR3 (@YF8b.Hnf' _))) HcR Hsp)).
Local Abbreviation Hmf' := (AR7 ((AR8 (AR3 (@YF8b.Hmf' _))) HcR Hsp)).
Local Abbreviation Hmu' := (AR7 ((AR8 (AR3 (@YF8b.Hmu' _))) HcR Hsp)).
Local Abbreviation Hcarved' := ((ARh ((ARf (@YF8b.Hcarved')) c au mu HcR)) Hau_def Hmu_def).
Local Abbreviation Hau_al' := ((ARh ((ARf (@YF8b.Hau_al')) c au csz HcR Hcsz)) Hau_def).
Local Abbreviation vis_present := (ARh ((AR3 (@YF8b.vis_present _)) maxc)).
Local Abbreviation thread_present := (AR7 ((AR8 (AR3 (@YF8b.thread_present _))) csz IMG LY HcR Hcsz Hsp)).
Local Abbreviation ARb f := (AR5 f IMG LY HcR Hmax Hn Hcsz Hsp) (only parsing).
Local Abbreviation rinfo_present := (AR7 (ARb (AR3 (@YF8b.rinfo_present _)))).
Local Abbreviation HslotPres' := (AR7 (ARb (AR3 (@YF8b.HslotPres' _)))).
Local Abbreviation HfaPres' := (AR7 (ARb (AR3 (@YF8b.HfaPres' _)))).
Local Abbreviation word_of_present := ((AR3 (@YF8b.word_of_present)) maxc).
Local Abbreviation val_mem_lo4 := ((AR4 (@YF8b.val_mem_lo4)) maxc).
Local Abbreviation junk_valuesR := (AR7 (ARb (AR3 (@YF8b.junk_valuesR _)))).
Local Abbreviation cell_sym := ((ARf (@YF8b.cell_sym)) B S TS HARm).
Local Abbreviation cell_lit := ((ARf (@YF8b.cell_lit)) B S TS HARm).
Local Abbreviation cell_state := (ARh (ARf (@YF8b.cell_state))).
Local Abbreviation In_acells_cache := ((ARg (@YF8b.In_acells_cache)) maxc HcR B S).
Local Abbreviation In_acells_region := ((ARg (@YF8b.In_acells_region)) maxc HcR B S).
Local Abbreviation cache_valsR := ((ARh ((AR3 (@YF8b.cache_valsR _)) c maxc csz HcR Hmax Hcsz)) Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@YF8b.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (ARh ((AR3 (@YF8b.cache_valsU _)) maxc)).
Local Abbreviation region_valsR := (AR7 ((AR8 (AR3 (@YF8b.region_valsR _))) HcR)).
Local Abbreviation chunk_lit := (AR0 (AR3 (@YF8b.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR3 (@YF8b.chunk_lit_at))).
Local Abbreviation chunk_atom := (AR0 (AR3 (@YF8b.chunk_atom))).
Local Abbreviation AR9 f := (f Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) (only parsing).
Local Abbreviation ARe f := (f Hpres0R B S TS HTSD HARm) (only parsing).
Local Abbreviation REG0R3_ok_but35 := (AR9 (ARe (AR6 (AR1 (AR0 (AR3 (@YF8b.REG0R3_ok_but35 _))))))).
Local Abbreviation REG0R3_ok := (AR9 ((ARe (AR6 (AR1 (AR0 (AR3 (@YF8b.REG0R3_ok _)))))) Hinited Hchunks)).
Local Abbreviation REG0U3_ok := (AR9 (ARe (AR6 (AR1 (AR0 (AR3 (@YF8b.REG0U3_ok _))))))).
Local Abbreviation PAIRSR3_ok := (ARc (AR0 (AR4 (@YF8b.PAIRSR3_ok _)))).
Local Abbreviation SPAN3_disj := (ARc (AR0 (AR4 (@YF8b.SPAN3_disj _)))).
Local Abbreviation FACTSR3_ok := (AR2 (AR6 (AR1 (AR0 (AR4 (@YF8b.FACTSR3_ok _)))))).
Local Abbreviation SEEDR3_ok := (AR9 ((ARe (AR2 ((AR6 (AR1 (AR0 (AR3 (@YF8b.SEEDR3_ok _ _))))) Htp Ha0 Ha1 Ha2 Ha3))) Hinited Hchunks)).
Local Abbreviation PAIRSU3_ok := (ARc (AR0 (AR4 (@YF8b.PAIRSU3_ok _)))).
Local Abbreviation SEEDU3_ok := (AR9 (ARe (AR2 ((AR6 (AR1 (AR0 (AR3 (@YF8b.SEEDU3_ok _ _))))) Htp Ha0 Ha1 Ha2 Ha3)))).
Local Abbreviation PT := (@YF82.PT).
Local Abbreviation pstable_PT := (ARg (@YF82.pstable_PT)).
Local Abbreviation WX0 := (ARg (@YF82.WX0)).
Local Abbreviation at_R3_init := ((AR0 ((AR3 (@YF82.at_R3_init _)) md0)) mat0 msJ SEEDJ).
Local Abbreviation seg3J := ((ARc (AR0 ((AR3 (@YF82.seg3J _ _)) md0))) Hpres0R).
Local Abbreviation land_hi0 := (@YF82.land_hi0).
Local Abbreviation seg3P := ((AR2 (ARc (AR0 ((AR3 (@YF82.seg3P _ _)) md0)))) mat0 msJ SEEDJ).
Local Abbreviation T16 := (@YF82.T16).
Local Abbreviation TMID := (@YF82.TMID).
Local Abbreviation U_csz := ((AR0 (@YF82.U_csz ly regs0)) HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation U_csz31 := ((AR0 (@YF82.U_csz31 ly regs0)) Hcsz).
Local Abbreviation U_csz16 := ((AR0 (@YF82.U_csz16 ly regs0)) HcR Hcsz Hmf Hmu).
Local Abbreviation U_cszmid := ((AR0 (@YF82.U_cszmid ly regs0)) HcR Hcsz).
Local Abbreviation U_tot_of := (AR2 (AR1 (AR0 (AR4 (@YF82.U_tot_of _))))).
Local Abbreviation U_tot31 := (AR2 (AR1 (AR0 (AR4 (@YF82.U_tot31 _))))).
Local Abbreviation U_rb := (AR1 (AR0 (AR4 (@YF82.U_rb _)))).
Local Abbreviation seg3Q31 := (AR2 (ARc (AR0 ((AR3 (@YF82.seg3Q31 _ _)) md0)))).
Local Abbreviation seg3Q16 := (AR2 (ARc (AR0 ((AR3 (@YF82.seg3Q16 _ _)) md0)))).
Local Abbreviation seg3Qmid := (AR2 (ARc (AR0 ((AR3 (@YF82.seg3Qmid _ _)) md0)))).
Local Abbreviation U_mu := ((AR0 (@YF82.U_mu ly regs0)) Hmf Hmu).
Local Abbreviation U_tot := (AR2 (AR1 (AR0 (AR4 (@YF82.U_tot _))))).
Local Abbreviation seg3Q_map := (AR2 (ARc (AR0 ((AR3 (@YF82.seg3Q_map _ _)) md0)))).
Local Abbreviation seg3Q_ok := (AR2 (ARc (AR0 ((AR3 (@YF82.seg3Q_ok _ _)) md0)))).
Local Abbreviation seg3M := (AR2 (ARc (AR0 ((AR3 (@YF82.seg3M _ _)) md0)))).
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
Definition XCOND_ge : Prop := mu < tot /\ mu + kUserMapSize <= kFreeArrayOffset.
Definition MUX_ge : Z := (mu + kUserMapSize).
Definition MFY_ge : Z := mf.
Definition YCOND_ge : Prop := 4 * nfg <= mf.
Definition SRC3_ge : Z := FAv + 4 * (nfg - n).
Ltac get_facts3 :=
pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 &
G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32 & G33 & G34 & G35 & G36 & G37).
Lemma factsX_ge : XCOND_ge ->
0 <= ncg < 2 ^ 16 /\ nfg = nf + ncg /\ aug = au + ncg * csz /\ aug mod 16 = 0 /\
ncg * csz <= MUX_ge - au < ncg * csz + csz /\ need <= ncg /\ 0 <= MUX_ge - au < 2 ^ 32 /\ MUX_ge <= kFreeArrayOffset.
Proof.
intros HC. get_facts3. pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). unfold XCOND_ge, MUX_ge in *.
split; [img_try (clear - G18 G21; zlia)|]. split; [img_try (img_exact G23)|]. split; [img_try (img_exact G35)|]. split; [img_try (img_exact G37)|]. split; [img_try (rewrite <- G15; img_exact G19)|].
destruct HC as [HC HR3]. split; [| img_try (clear - U0 U1 U2 HR3; numconst; unfold kUserMapSize in *; zlia)].
assert (L : need * csz < ncg * csz + csz) by (img_try (clear - HC G3 G5 G15 G19 U0 U1; unfold kMaxSize, kUserMapSize in *; zlia)).
clear - L K4 G1 G18. nia.   Qed.
Lemma factsY_ge : XCOND_ge -> YCOND_ge -> 4 * nfg <= MFY_ge /\ MFY_ge <= kFreeArrayMax /\ 0 <= MFY_ge.
Proof.
intros HC HY. pose proof (factsX_ge HC) as ([N0 N1] & N2 & _). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] M2]. unfold YCOND_ge, MFY_ge in *.
clear - HY N0 N1 N2 F0 F1 M0 M1. zlia.       Qed.
Ltac sv_zev :=
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t ltac:(img_eqrefl));
cbn [zev zalu_raw zmd_raw]; unfold rho_of end.
Lemma val_mem_frame_ge : forall (Hh : word -> bool) (m m' : word -> option byte) a (k : nat) v,
(forall t, (t < k)%nat -> m' (Z_to_bv 64 (a + Z.of_nat t)) = m (Z_to_bv 64 (a + Z.of_nat t))) ->
val_mem tfxsegs (mrestrict Hh m) a k v -> val_mem tfxsegs (mrestrict Hh m') a k v.
Proof. clear3. intros Hh m m' a k v Hfr Hv t Ht. rewrite <- (Hv t Ht). img_apply mbyte_mrestrict_same. img_apply Hfr. img_exact Ht. Qed.
Definition P_fill_ge (Wx : world tfxsegs) (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ forall i, 0 <= i < ncg -> val_mem tfxsegs (mrestrict (w_H Wx) m) (FAv + 4 * nfg - 4 - 4 * i) 4 ((au + i * csz) / 16).
Lemma pstable_fill_ge : XCOND_ge -> YCOND_ge -> forall Wx P, pstable P -> pstable (P_fill_ge Wx P).
Proof.
intros HC HY Wx P HP m m' Hfr [H1 H2]. pose proof (factsX_ge HC) as ([N0 N1] & N2 & _). pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR.
split; [img_try (img_exact (HP m m' Hfr H1))|].
intros i Hi. img_apply (val_mem_frame_ge (w_H Wx) m m'); [|img_try (img_exact (H2 i Hi))]. intros t Ht. img_apply Hfr.
rewrite unsigned_lit_small by (img_try (clear - Hi Ht N0 N1 N2 F0 F1 Y1 Y2 DR; numconst; unfold kFreeArrayMax in *; zlia)).
img_apply fa_not_WINR0. clear - Hi Ht N0 N1 N2 F0 F1 Y1 Y2; unfold kFreeArrayMax in *; zlia.
Qed.
Lemma segE1_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfxsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
(forall m, P m -> forall a, W_FE nfg a -> apresent (w_H Wx) m a) ->
(forall m m' : word -> option byte, (forall x : word, ~ W_FE nfg (bv_unsigned x) -> m' x = m x) -> (forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P m -> P m') ->
at_R3 Wx md X P R3_FILLge W' c' ->
SRr tfxsegs W' c' (at_R3 Wx md (fun a => X a \/ W_FE nfg a) (P_fill_ge Wx P) R3_Tge0).
Proof.
intros HC HY Wx md X P W' c' HX HP HPfe HPu HR. get_facts3. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9).
pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). unfold MUX_ge in *.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (S1 & S2 & S3 & S4 & S5).
pose proof stack_ext_ok3 as [SX1 SX2].
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
rreg HS (10%bv : bv 5) R10. rregS HS (11%bv : bv 5) R11. rreg HS (12%bv : bv 5) R12. rreg HS (21%bv : bv 5) R21. rreg HS (19%bv : bv 5) R19.
rewrite (HEn 46%nat ltac:(img_try ((img_case; cbv); zlia))), EaAU in R12. rewrite (HEn 40%nat ltac:(img_try ((img_case; cbv); zlia))), EaCSZ in R21. rewrite (HEn 61%nat ltac:(img_try ((img_case; cbv); zlia))), EaNCg in R19.
assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 (FAv + 4 * nfg)).
{ rewrite R11. sv_zev. rewrite (HEn 42%nat ltac:(img_try ((img_case; cbv); zlia))), (HEn 63%nat ltac:(img_try ((img_case; cbv); zlia))), EaRB, EaNFg. unfold w64.
clear - N0 N1 N2 F0 F1 Y1 Y2 DR. numconst. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small RBv), (unsigned_lit_small nfg) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id (RBv + 3758096384)), (zcanon_id nfg) by (img_try (unfold M64; zlia)). img_change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 2) with 4. rewrite (zcanon_id (nfg * 4)) by (img_try (unfold M64; zlia)). rewrite zcanon_id by (img_try (unfold M64; zlia)). zlia. }
eapply (popfree_stretch Wx hPF E' R3_FILLge ms _ (FAv + 4 * nfg) au csz ncg);
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (img_exact R10) | img_try (img_exact R11') | img_try (img_exact R12) | img_try (img_exact R21) | img_try (img_exact R19)
| img_try (clear - N7 G1; zlia) | img_try (clear - N0 N2 F0 DR; numconst; zlia) | img_try (clear - N0 N1 N2 F0 F1 Y1 Y2 DR; numconst; unfold kFreeArrayMax in *; zlia)
| img_try (clear - U0; zlia) | img_try (clear - K4; zlia) | img_try (clear - N5 N9 U0 U1; numconst; nia) | img_try (clear - N0 N2 F0 DR; numconst; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)
| img_try (intros a Ha; img_apply (HPfe _ HPm a); unfold W_FE; clear - Ha N2; zlia)
| img_try (intros r Hr) | img_try (intros r a Hr) | ].
1-2: cbn [ss_mem] in Hr; destruct Hr as [<-|Hr];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2;
clear - N0 N1 N2 F0 F1 Y1 Y2 DR S4 S5 SX1 SX2; numconst; unfold kFreeArrayMax in *; try unfold sp0 in *; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILR in Hr by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7); clear - N0 N1 N2 F0 F1 Y1 Y2 DR X1 X2 X3 X4 X5 X6 X7; numconst; unfold kFreeArrayMax in *; zlia ].
intros regs3 mem3 mat3 HS3 Hfr3 Hpr3 Hval3. rewrite wvb_collapse.
replace (FAv + 4 * nfg - 4 * ncg) with (FAv + 4 * nf) in Hfr3 by (img_try (clear - N2; zlia)).
assert (HR : at_R3 Wx md (fun a => X a \/ W_FE nfg a) (P_fill_ge Wx P) R3_Tge0 Wx
(mkCfg (mkst regs3 (Z_to_bv 64 (0x36cf0 + D_150)) mem3 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat3 md))).
{ split; [img_refl|]. exists (mkst regs3 (Z_to_bv 64 (0x36cf0 + D_150)) mem3 (seg_rom tfxsegs)), mat3, (havoc E' hPF (map (getr regs3) CLOB_PF)).
split; [img_refl|]. split; [img_try (img_exact (env_agree_havoc_ge aHAV3 hPF E0 E' _ ltac:(unfold aHAV3, hPF; zlia) HE))|].
split; [img_try (img_exact HS3)|]. cbn [ms_mem mkst]. split; [|img_try (split)].
- intros x Hx. rewrite (Hfr3 x) by (img_try (intros Hw; img_apply Hx; right; img_exact Hw)). img_apply MEQ. intros H; img_apply Hx; left; img_exact H.
- intros a Ha. img_apply Hpr3. img_exact (PRS a Ha).
- split; [img_try (img_exact (HPu (ms_mem ms) mem3 Hfr3 Hpr3 HPm)) | img_try (img_exact Hval3)]. }
img_apply SRr_ret. img_exact HR.
Qed.
Lemma segE2_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfxsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P R3_Tge0 W' c' -> SRr tfxsegs W' c' (at_R3 Wx md X P R3_Cge0).
Proof.
intros HC HY Wx md X P W' c' HX HP HR. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9). unfold MUX_ge in *.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] _].
pose proof facts3 as (G1 & _).
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36d00 + D_150) (runto (0x36d00 + D_150) R3_Tge0) HX HP.
r3_pin HR (13%bv : bv 5) (SOff rAUg 0).
{ pin_zev3. unfold rAUg, rAU, rNCg, rCSZ. rewrite EaAUg, EaAU, EaNCg, EaCSZ. unfold w64. clear - N0 N1 N3 N5 N8 N9 K4 U0 U1. numconst. unfold kMaxSize in *.
rewrite (unsigned_lit_small aug), (unsigned_lit_small au), (unsigned_lit_small ncg), (unsigned_lit_small csz) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id aug), (zcanon_id au), (zcanon_id ncg), (zcanon_id csz) by (img_try (unfold M64; zlia)).
rewrite (zcanon_id (ncg * csz)) by (img_try (unfold M64; nia)). rewrite zcanon_id by (img_try (unfold M64; zlia)). zlia. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36d04 + D_150) (runto (0x36d04 + D_150) R3_Tge1) HX HP.
r3_pin HR (10%bv : bv 5) (SOff rNFg 0).
{ pin_zev3. unfold rNFg, rNF, rNCg. rewrite EaNFg, EaNF, EaNCg. unfold w64.
clear - N0 N1 N2 F0 F1 M0 M1. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small nfg), (unsigned_lit_small nf), (unsigned_lit_small ncg) by zlia.
rewrite !Z.add_0_r. rewrite (zcanon_id nfg), (zcanon_id nf), (zcanon_id ncg) by (img_try (unfold M64; zlia)). rewrite zcanon_id by (img_try (unfold M64; zlia)). zlia. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36d0c + D_150) R3_Tge3 HX HP.
r3_arm HR BC_LTU false (SOff rMU 262144) (SOff rAUg 0).     { arm_zev3. unfold rMU, rAUg. rewrite EaMU, EaAUg. unfold w64. clear - N0 K4 N3 N5 N8 N9 U0 U1 U2. numconst.
rewrite (unsigned_lit_small mu), (unsigned_lit_small aug) by nia. rewrite ?Z.add_0_r.
rewrite !zcanon_id by (img_try (unfold M64; nia)). img_apply Z.ltb_ge. nia. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36ad4 + D_150) (runto (0x36ad4 + D_150) (arm BC_LTU false (SOff rMU 262144) (SOff rAUg 0) R3_Tge3)) HX HP.     r3_arm HR BC_LTU false (SOff rNFg 0) (SOff rN 0).
{ arm_zev3. unfold rNFg, rN. rewrite EaNFg, EaN. unfold w64. clear - N0 N1 N2 N7 F0 F1 M0 M1 K3 Hneed. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small nfg), (unsigned_lit_small n) by zlia. rewrite ?Z.add_0_r.
rewrite !zcanon_id by (img_try (unfold M64; zlia)). img_apply Z.ltb_ge. zlia. }
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok (0x36980 + D_150) R3_Cge0 HX HP.
img_apply SRr_ret. img_exact HR.
Qed.
Definition P_cpy_ge (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ forall j, 0 <= j < 4 * n -> m (w64 (DSTv + j)) = m (w64 (SRC3_ge + j)).
Lemma pstable_cpy_ge : XCOND_ge -> YCOND_ge -> forall P, pstable P -> pstable (P_cpy_ge P).
Proof.
intros HC HY P HP m m' Hfr [H1 H2]. pose proof (factsX_ge HC) as ([N0 N1] & N2 & _ & _ & _ & N7 & _). pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). pose proof high_factsR as (F1' & F2 & _).
split; [img_try (img_exact (HP m m' Hfr H1))|].
intros j Hj. unfold w64, SRC3_ge in *. rewrite !Hfr; [img_try (img_exact (H2 j Hj)) | |].
- rewrite unsigned_lit_small by (img_try (clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed; numconst; unfold kFreeArrayMax in *; zlia)).
img_apply fa_not_WINR0. clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 K3 Hneed; unfold kFreeArrayMax in *; zlia.
- rewrite unsigned_lit_small by (img_try (clear - Hj DR K3 F2; numconst; zlia)). img_apply slots_not_WINR0. clear - Hj K3; zlia.
Qed.
Lemma segE3_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfxsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
(forall m, P m -> forall a, SRC3_ge <= a < SRC3_ge + 4 * n -> apresent (w_H Wx) m a) ->
(forall m, P m -> forall a, W_DST a -> apresent (w_H Wx) m a) ->
(forall m m' : word -> option byte, (forall x : word, ~ W_DST (bv_unsigned x) -> m' x = m x) -> (forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P m -> P m') ->
at_R3 Wx md X P R3_Cge0 W' c' ->
SRr tfxsegs W' c' (at_R3 Wx md (fun a => X a \/ W_DST a) (P_cpy_ge P) R3_Cge).
Proof.
intros HC HY Wx md X P W' c' HX HP HPfe HPdst HPu HR. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9).
pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). unfold MUX_ge in *.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (S1 & S2 & S3 & S4 & S5).
pose proof stack_ext_ok3 as [SX1 SX2].
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
rregS HS (20%bv : bv 5) R20. rreg HS (13%bv : bv 5) R13. rregS HS (11%bv : bv 5) R11.
assert (R20' : getr (ms_regs ms) 20 = Z_to_bv 64 SRC3_ge).
{ rewrite R20. sv_zev. rewrite (HEn 39%nat ltac:(img_try ((img_case; cbv); zlia))), (HEn 43%nat ltac:(img_try ((img_case; cbv); zlia))), (HEn 63%nat ltac:(img_try ((img_case; cbv); zlia))), EaN, EaFA, EaNFg. unfold w64, SRC3_ge.
clear - N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed. numconst. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small n), (unsigned_lit_small FAv), (unsigned_lit_small nfg) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id n), (zcanon_id FAv), (zcanon_id nfg) by (img_try (unfold M64; zlia)). img_change (zcanon 18446744073709551612) with (2 ^ 64 - 4).
img_change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 2) with 4. rewrite (zcanon_id (nfg * 4)) by (img_try (unfold M64; zlia)).
unfold zcanon, M64. rewrite (Zplus_mod_idemp_l (n * (2 ^ 64 - 4))), Zplus_mod_idemp_l.
replace (n * (2 ^ 64 - 4) + FAv + nfg * 4) with ((FAv + nfg * 4 - 4 * n) + n * 2 ^ 64) by zlia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by zlia. zlia. }
assert (R13' : getr (ms_regs ms) 13 = Z_to_bv 64 DSTv).
{ rewrite R13, (HEn 37%nat ltac:(img_try ((img_case; cbv); zlia))), EaP. unfold w64, DSTv. rewrite Zbv_add_unsigned. img_refl. }
assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 (DSTv + 4 * n)).
{ rewrite R11. sv_zev. rewrite (HEn 37%nat ltac:(img_try ((img_case; cbv); zlia))), (HEn 39%nat ltac:(img_try ((img_case; cbv); zlia))), EaP, EaN. unfold w64, DSTv.
clear - DR K3 F2. numconst. rewrite (unsigned_lit_small Pr), (unsigned_lit_small n) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id (Pr + 16)), (zcanon_id n) by (img_try (unfold M64; zlia)). img_change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 2) with 4.
rewrite (zcanon_id (n * 4)) by (img_try (unfold M64; zlia)). rewrite zcanon_id by (img_try (unfold M64; zlia)). zlia. }
eapply (cpy4_stretch Wx hCP E' R3_Cge0 ms _ DSTv SRC3_ge (4 * n));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (img_exact R20') | img_try (img_exact R13') | img_try (img_exact R11')
| img_try (clear - K3; zlia) | img_try (clear - K3; rewrite Z.mul_comm; img_apply Z_mod_mult)
| img_try (clear - DR; unfold DSTv in *; numconst; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia) | img_try (clear - DR K3 F2; unfold DSTv in *; numconst; zlia)
| img_try (clear - N0 N2 N7 F0 DR Hneed; unfold SRC3_ge in *; numconst; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia) | img_try (clear - N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed; unfold SRC3_ge in *; numconst; unfold kFreeArrayMax in *; zlia)
| img_try (clear - N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed F1' F2 F4 F5 TP S1; unfold SRC3_ge, DSTv, Pr in *; numconst; unfold kFreeArrayMax in *; try unfold T in *; try unfold SB in *; zlia)
| img_try (intros a Ha; img_apply (HPdst _ HPm a); unfold W_DST; img_exact Ha)
| img_try (intros a Ha; img_exact (HPfe _ HPm a Ha))
| img_try (intros r Hr) | img_try (intros r a Hr) | img_try (intros r a Hr) | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|Hr];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2;
clear - DR K3 F1' F2 S1 S4 S5; unfold DSTv, Pr in *; numconst; try unfold sp0 in *; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILR in Hr by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7); clear - DR K3 F2 X1 X2 X3 X4 X5 X6 X7; numconst; zlia ].
intros regs3 mem3 mat3 HS3 Hfr3 Hpr3 Hcp3. rewrite wvb_collapse.
assert (HR : at_R3 Wx md (fun a => X a \/ W_DST a) (P_cpy_ge P) R3_Cge Wx
(mkCfg (mkst regs3 (Z_to_bv 64 (0x36994 + D_150)) mem3 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat3 md))).
{ split; [img_refl|]. exists (mkst regs3 (Z_to_bv 64 (0x36994 + D_150)) mem3 (seg_rom tfxsegs)), mat3, (havoc E' hCP (map (getr regs3) CLOB_CP3)).
split; [img_refl|]. split; [img_try (img_exact (env_agree_havoc_ge aHAV3 hCP E0 E' _ ltac:(unfold aHAV3, hCP; zlia) HE))|].
split; [img_try (img_exact HS3)|]. cbn [ms_mem mkst]. split; [|img_try (split)].
- intros x Hx. rewrite (Hfr3 x) by (img_try (intros Hw; img_apply Hx; right; img_exact Hw)). img_apply MEQ. intros H; img_apply Hx; left; img_exact H.
- intros a Ha. img_apply Hpr3. img_exact (PRS a Ha).
- split; [img_try (img_exact (HPu (ms_mem ms) mem3 Hfr3 Hpr3 HPm)) |].
intros j Hj. rewrite (Hcp3 j Hj). symmetry. img_apply Hfr3. unfold w64, W_DST.
rewrite unsigned_lit_small by (img_try (clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed; unfold SRC3_ge in *; numconst; unfold kFreeArrayMax in *; zlia)).
clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed F1' F2 F4 F5 TP S1; unfold SRC3_ge, DSTv, Pr in *; numconst; unfold kFreeArrayMax in *; try unfold T in *; try unfold SB in *; zlia. }
img_apply SRr_ret. img_exact HR.
Qed.
Lemma segE4_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfxsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P R3_Cge W' c' -> SRr tfxsegs W' c' (at_RET3 Wx 1 md X (fun m => P m /\ P_cells Wx n (nfg - n) MFY_ge aug MUX_ge m)).
Proof.
intros HC HY Wx md X P W' c' HX HP HR. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9).
pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). get_facts3.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] _].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
r3_run HR tfxtbl_rtA tfxtbl_rtA_ok 0x7ffffff0 R3_RETge HX HP.
eapply (at_R3_ret Wx md X _ R3_RETge _ _ 1); [| img_refl | img_refl | img_refl | img_refl | img_refl
| img_try (unfold CSAVED; repeat (img_apply Forall_cons; [(img_case; vm_compute); img_refl|]); img_apply Forall_nil) ].
img_apply (at_R3_facts Wx md X P _ R3_RETge _ _ HR). clear HR.
intros E' ms HE HS. assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
assert (RP : 0 <= Pr /\ Pr + 16 < 2 ^ 64) by (img_try (clear - DR F2; numconst; zlia)).
assert (RR : 0 <= RGv /\ RGv + 128 < 2 ^ 64) by (img_try (clear - DR; numconst; zlia)).
unfold MUX_ge, MFY_ge. cells3 HS HEn R3_RETge RP RR DR F1' F2.
all: lazymatch goal with
| |- sv_denot _ _ = _ =>
first [
sv_zev; rewrite (HEn 39%nat ltac:(img_try ((img_case; cbv); zlia))), (HEn 63%nat ltac:(img_try ((img_case; cbv); zlia))), EaN, EaNFg; unfold w64;
clear - N0 N1 N2 N7 F0 F1 M0 M1 K3 Hneed; unfold kFreeArrayMax in *;
rewrite (unsigned_lit_small n), (unsigned_lit_small nfg) by zlia; rewrite !Z.add_0_r; rewrite (zcanon_id n), (zcanon_id nfg) by (img_try (unfold M64; zlia));
img_change (zcanon (-1)) with (2 ^ 64 - 1); unfold zcanon, M64;
rewrite (Zplus_mod_idemp_l (n * (2 ^ 64 - 1))); replace (n * (2 ^ 64 - 1) + nfg) with ((nfg - n) + n * 2 ^ 64) by zlia;
rewrite Z_mod_plus_full; img_apply Z.mod_small; zlia
|
cbn [sv_denot]; rewrite (HEn 66%nat ltac:(img_try ((img_case; cbv); zlia))), EaMF2, G33; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl ]
| |- _ => first [ clear - K3; zlia | clear - K1; zlia | clear - K4; numconst; zlia
| clear - N0 N1 N2 N7 F0 F1 M0 M1 K3 Hneed; numconst; unfold kFreeArrayMax in *; zlia
| clear - Y2 Y3; unfold MFY_ge, kFreeArrayMax, kFreeArrayMapSize in *; zlia
| clear - N9 U0 U1 U2; unfold MUX_ge in *; numconst; zlia
| clear - N3 N5 N8 N9 U0 U1 N0 K4; numconst; nia ]
end.
Qed.
End g.
End d.

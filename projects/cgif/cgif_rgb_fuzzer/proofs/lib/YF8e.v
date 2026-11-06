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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF09 YF0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8t YF3v YF4q YF8g YF7x YF7w YF3w YF7z YF7y YF66 YF65.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3i YF81 YF40 YF80 YF8b YF82 YF83 YF84 YF85 YF86 YF87 YF88 YF89 YF8a YF8d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0b YG0j YG0v YG08 YK0v YA05 YA09 YG0l YG0c YG0k YG0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
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
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
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
Local Abbreviation ARo f := (f ly c n) (only parsing).
Local Abbreviation SRCv := ((ARo (@YF7w.SRCv)) nf).
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
Local Abbreviation ARa f := (f mf au mu) (only parsing).
Local Abbreviation ARp f := (f ly regs0 c) (only parsing).
Local Abbreviation class_facts := ((ARa ((ARp (@YF7w.class_facts)) maxc n)) csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation AR6 f := (f imgk ly regs0) (only parsing).
Local Abbreviation high_factsR := ((ARa ((AR6 (@YF7w.high_factsR _)) maxc)) IMG LY Hmf Hmu).
Local Abbreviation off_T := ((ARa ((AR6 (@YF7w.off_T _)) maxc)) IMG LY Hmf Hmu).
Local Abbreviation off_C := ((ARa ((AR6 (@YF7w.off_C _)) maxc)) IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation AR7 f := (f c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz) (only parsing).
Local Abbreviation derived_rangesR := ((AR7 (AR6 (@YF7w.derived_rangesR _))) Hnf Hmf Hmu).
Local Abbreviation WINR0 := (ARp (@YF7w.WINR0)).
Local Abbreviation WINR := ((ARp (@YF7w.WINR)) n).
Local Abbreviation WINR0_WINR := ((ARp (@YF7w.WINR0_WINR)) n).
Local Abbreviation WSKELR := (@YF7w.WSKELR).
Local Abbreviation win_sub := (@YF7w.win_sub).
Local Abbreviation win_sub_sound := ((ARa ((ARp (@YF7w.win_sub_sound)) maxc n)) Hmax Hn Hmf Hmu).
Local Abbreviation AR3 f := (AR0 f IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation WSKELR_WINR0 := (AR3 (AR6 (@YF7w.WSKELR_WINR0 _))).
Local Abbreviation windows_WINR0 := (AR3 (AR6 (@YF7w.windows_WINR0 _))).
Local Abbreviation frame_WINR0 := (AR3 (AR6 (@YF7w.frame_WINR0 _))).
Local Abbreviation frame_X := (AR3 (AR6 (@YF7w.frame_X _))).
Ltac frame_acc3 HX HE :=
match goal with
| MEQ : (forall x : word, ~ ?X (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ X (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_X X E rs m1 m2 HX HE ltac:((try img_inst; img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation W_DST := (ARo (@YF7w.W_DST)).
Local Abbreviation W_FE := (@YF7w.W_FE ly c nf).
Local Abbreviation W_UW := (@YF7w.W_UW adr).
Local Abbreviation W_USH := (@YF7w.W_USH sha).
Local Abbreviation W_FW := (@YF7w.W_FW fadr).
Local Abbreviation W_FSH := (@YF7w.W_FSH shf).
Local Abbreviation ARc f := (AR6 f mem0) (only parsing).
Local Abbreviation at_R3 := (AR0 (ARc (@YF7w.at_R3 _))).
Local Abbreviation at_N3 := (AR0 (ARc (@YF7w.at_N3 _))).
Local Abbreviation at_RET3 := (@YF7w.at_RET3 _ regs0 mem0 imgk).
Local Abbreviation P_cells := (@YF7w.P_cells imgk ly c maxc csz).
Local Abbreviation chunk_index := (@YF7w.chunk_index).
Local Abbreviation pstable := (ARp (@YF7w.pstable)).
Local Abbreviation all_disjoint_of_forall := (@YF7w.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (ARa ((AR6 (@YF7w.kept_of_frame)) maxc)).
Local Abbreviation kept_of_frame2 := (ARa ((AR6 (@YF7w.kept_of_frame2)) maxc)).
Local Abbreviation SKEL_TAILR := (@YF7w.SKEL_TAILR imgk).
Local Abbreviation RFACTSR := ((AR6 (@YF7w.RFACTSR)) c).
Local Abbreviation stack_ivsR := ((ARa (@YF7w.stack_ivsR _ ly regs0 maxc)) LY Hmf Hmu Hsp).
Local Abbreviation ARl f := (AR7 f Hnf Hmf Hmu Hsp) (only parsing).
Local Abbreviation zone_litR := (ARl (AR6 (@YF7w.zone_litR _))).
Local Abbreviation zone_TR := ((ARa ((AR6 (@YF7w.zone_TR _)) c maxc)) IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := (ARl (AR6 (@YF7w.zone_CR _))).
Local Abbreviation zone_RGR := (ARl (AR6 (@YF7w.zone_RGR _))).
Local Abbreviation slots_not_WINR0 := (ARl (AR6 (@YF7w.slots_not_WINR0 _))).
Local Abbreviation fa_not_WINR0 := (ARl (AR6 (@YF7w.fa_not_WINR0 _))).
Local Abbreviation ARd f := (AR3 f Hsp) (only parsing).
Local Abbreviation tail_ext_okR := (ARd (AR6 (@YF7w.tail_ext_okR _))).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := ((ARa ((AR6 (@YF7w.rdn_of_presentR)) maxc)) Hmf Hmu).
Local Abbreviation store_ok_of_presentR := ((ARa ((AR6 (@YF7w.store_ok_of_presentR)) maxc)) Hmf Hmu).
Local Abbreviation ARg f := (ARa f j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp) (only parsing).
Local Abbreviation ARk f := (f c maxc nf) (only parsing).
Local Abbreviation cpy4_stretch := (ARg (ARk (AR6 (@YF7w.cpy4_stretch _)))).
Local Abbreviation AR1 f := (f c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation AR2 f := (f Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug) (only parsing).
Local Abbreviation facts3 := (AR2 (AR1 (AR6 (@YF7w.facts3 _)))).
Local Abbreviation RFACTS3 := ((AR6 (@YF7w.RFACTS3)) c).
Local Abbreviation tail_ext_ok3 := (ARd (AR6 (@YF7w.tail_ext_ok3 _))).
Local Abbreviation stack_ext_ok3 := (ARl (AR6 (@YF7w.stack_ext_ok3 _))).
Local Abbreviation scratch_headed := (@YF7w.scratch_headed).
Local Abbreviation mem_ok_scratch_present := ((AR0 (AR6 (@YF7w.mem_ok_scratch_present _))) LY Hmf Hmu Hsp).
Local Abbreviation at_R3_run := (ARd (ARc (@YF7w.at_R3_run _ _))).
Local Abbreviation at_R3_run_ecall := (ARd (ARc (@YF7w.at_R3_run_ecall _ _))).
Local Abbreviation at_R3_pin := (AR0 (ARc (@YF7w.at_R3_pin _))).
Local Abbreviation at_R3_arm := (AR0 (ARc (@YF7w.at_R3_arm _))).
Local Abbreviation at_R3_forget := (AR0 (ARc (@YF7w.at_R3_forget _))).
Local Abbreviation at_R3_noconds := (AR0 (ARc (@YF7w.at_R3_noconds _))).
Local Abbreviation at_R3_weaken := (AR0 (ARc (@YF7w.at_R3_weaken _))).
Local Abbreviation at_R3_facts := (AR0 (ARc (@YF7w.at_R3_facts _))).
Local Abbreviation at_R3_strengthen := (AR0 (ARc (@YF7w.at_R3_strengthen _))).
Local Abbreviation at_R3_eq := (AR0 (ARc (@YF7w.at_R3_eq _))).
Local Abbreviation CSAVED := (@YF7w.CSAVED).
Local Abbreviation sv_denot_SOff0 := (@YF7w.sv_denot_SOff0).
Local Abbreviation at_R3_ret := ((AR0 (ARc (@YF7w.at_R3_ret _))) HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp).
Local Abbreviation at_N3_cont := (ARd (ARc (@YF7w.at_N3_cont _ _))).
Local Abbreviation memset_stretch3 := (ARg (ARk (AR6 (@YF7w.memset_stretch3 _)))).
Local Abbreviation nth_Z_to_le_bytes4 := (@YF7w.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (ARg (ARk (AR6 (@YF7w.popfree_stretch _)))).
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
Local Abbreviation AR8 f := (f B S HARm) (only parsing).
Local Abbreviation ARb f := (f _ imgk W ly mem0 c) (only parsing).
Local Abbreviation cls_wfR := ((AR8 ((ARb (@YF8b.cls_wfR)) HcR)) Hinited).
Local Abbreviation cls_wf0 := (AR8 ((ARb (@YF8b.cls_wf0)) HcR)).
Local Abbreviation AR4 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation AR9 f := (f Hnf_def Hmf_def Hau_def Hmu_def) (only parsing).
Local Abbreviation reg_facts0 := (AR9 (AR8 ((ARa (ARk (AR4 (@YF8b.reg_facts0 _)))) HcR))).
Local Abbreviation reg_facts := (AR9 ((AR8 ((ARa (ARk (AR4 (@YF8b.reg_facts _)))) HcR Hmax Hsp)) Hinited)).
Local Abbreviation Hnf' := (AR9 (AR8 ((ARa (ARk (AR4 (@YF8b.Hnf' _)))) HcR Hsp))).
Local Abbreviation Hmf' := (AR9 (AR8 ((ARa (ARk (AR4 (@YF8b.Hmf' _)))) HcR Hsp))).
Local Abbreviation Hmu' := (AR9 (AR8 ((ARa (ARk (AR4 (@YF8b.Hmu' _)))) HcR Hsp))).
Local Abbreviation Hcarved' := ((AR8 ((ARb (@YF8b.Hcarved')) au mu HcR)) Hau_def Hmu_def).
Local Abbreviation Hau_al' := ((AR8 ((ARb (@YF8b.Hau_al')) au csz HcR Hcsz)) Hau_def).
Local Abbreviation vis_present := (AR8 ((AR4 (@YF8b.vis_present _)) maxc)).
Local Abbreviation thread_present := (AR9 (AR8 ((ARa (ARk (AR4 (@YF8b.thread_present _)))) csz IMG LY HcR Hcsz Hsp))).
Local Abbreviation rinfo_present := (AR9 (AR8 ((AR7 (AR4 (@YF8b.rinfo_present _))) Hsp))).
Local Abbreviation HslotPres' := (AR9 (AR8 ((AR7 (AR4 (@YF8b.HslotPres' _))) Hsp))).
Local Abbreviation HfaPres' := (AR9 (AR8 ((AR7 (AR4 (@YF8b.HfaPres' _))) Hsp))).
Local Abbreviation word_of_present := ((AR4 (@YF8b.word_of_present)) maxc).
Local Abbreviation val_mem_lo4 := ((AR6 (@YF8b.val_mem_lo4)) maxc).
Local Abbreviation junk_valuesR := (AR9 (AR8 ((AR7 (AR4 (@YF8b.junk_valuesR _))) Hsp))).
Local Abbreviation ARh f := (f B S TS) (only parsing).
Local Abbreviation cell_sym := ((ARh (@YF8b.cell_sym _ imgk W ly mem0)) HARm).
Local Abbreviation cell_lit := ((ARh (@YF8b.cell_lit _ imgk W ly mem0)) HARm).
Local Abbreviation cell_state := (AR8 (@YF8b.cell_state _ imgk W ly mem0)).
Local Abbreviation In_acells_cache := ((ARp (@YF8b.In_acells_cache)) maxc HcR B S).
Local Abbreviation In_acells_region := ((ARp (@YF8b.In_acells_region)) maxc HcR B S).
Local Abbreviation cache_valsR := ((AR8 ((AR4 (@YF8b.cache_valsR _)) c maxc csz HcR Hmax Hcsz)) Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@YF8b.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (AR8 ((AR4 (@YF8b.cache_valsU _)) maxc)).
Local Abbreviation region_valsR := (AR9 (AR8 ((ARa (ARk (AR4 (@YF8b.region_valsR _)))) HcR))).
Local Abbreviation chunk_lit := (AR0 (AR4 (@YF8b.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR4 (@YF8b.chunk_lit_at))).
Local Abbreviation chunk_atom := (AR0 (AR4 (@YF8b.chunk_atom))).
Local Abbreviation AR5 f := (AR3 f Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp) (only parsing).
Local Abbreviation ARi f := (AR9 f Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) (only parsing).
Local Abbreviation REG0R3_ok_but35 := (ARi ((ARh ((AR5 (AR4 (@YF8b.REG0R3_ok_but35 _))) Hpres0R)) HTSD HARm)).
Local Abbreviation REG0R3_ok := (ARi ((ARh ((AR5 (AR4 (@YF8b.REG0R3_ok _))) Hpres0R)) HTSD HARm Hinited Hchunks)).
Local Abbreviation REG0U3_ok := (ARi ((ARh ((AR5 (AR4 (@YF8b.REG0U3_ok _))) Hpres0R)) HTSD HARm)).
Local Abbreviation PAIRSR3_ok := (ARd (AR6 (@YF8b.PAIRSR3_ok _))).
Local Abbreviation SPAN3_disj := (ARd (AR6 (@YF8b.SPAN3_disj _))).
Local Abbreviation FACTSR3_ok := (AR2 (AR5 (AR6 (@YF8b.FACTSR3_ok _)))).
Local Abbreviation SEEDR3_ok := (ARi ((ARh ((AR2 ((AR5 (AR4 (@YF8b.SEEDR3_ok _ _))) Htp Ha0 Ha1 Ha2 Ha3)) Hpres0R)) HTSD HARm Hinited Hchunks)).
Local Abbreviation PAIRSU3_ok := (ARd (AR6 (@YF8b.PAIRSU3_ok _))).
Local Abbreviation SEEDU3_ok := (ARi ((ARh ((AR2 ((AR5 (AR4 (@YF8b.SEEDU3_ok _ _))) Htp Ha0 Ha1 Ha2 Ha3)) Hpres0R)) HTSD HARm)).
Local Abbreviation PT := (@YF82.PT).
Local Abbreviation pstable_PT := (ARp (@YF82.pstable_PT)).
Local Abbreviation WX0 := (ARp (@YF82.WX0)).
Local Abbreviation ARe f := (AR4 f md0) (only parsing).
Local Abbreviation at_R3_init := ((AR0 (ARe (@YF82.at_R3_init _))) mat0 msJ SEEDJ).
Local Abbreviation seg3J := ((ARd (ARe (@YF82.seg3J _ _))) Hpres0R).
Local Abbreviation land_hi0 := (@YF82.land_hi0).
Local Abbreviation seg3P := ((AR2 (ARd (ARe (@YF82.seg3P _ _)))) mat0 msJ SEEDJ).
Local Abbreviation T16 := (@YF82.T16).
Local Abbreviation TMID := (@YF82.TMID).
Local Abbreviation U_csz := ((AR0 (@YF82.U_csz ly regs0)) HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation U_csz31 := ((AR0 (@YF82.U_csz31 ly regs0)) Hcsz).
Local Abbreviation U_csz16 := ((AR0 (@YF82.U_csz16 ly regs0)) HcR Hcsz Hmf Hmu).
Local Abbreviation U_cszmid := ((AR0 (@YF82.U_cszmid ly regs0)) HcR Hcsz).
Local Abbreviation U_tot_of := (AR2 (AR3 (AR6 (@YF82.U_tot_of _)))).
Local Abbreviation U_tot31 := (AR2 (AR3 (AR6 (@YF82.U_tot31 _)))).
Local Abbreviation U_rb := (AR3 (AR6 (@YF82.U_rb _))).
Local Abbreviation seg3Q31 := (AR2 (ARd (ARe (@YF82.seg3Q31 _ _)))).
Local Abbreviation seg3Q16 := (AR2 (ARd (ARe (@YF82.seg3Q16 _ _)))).
Local Abbreviation seg3Qmid := (AR2 (ARd (ARe (@YF82.seg3Qmid _ _)))).
Local Abbreviation U_mu := ((AR0 (@YF82.U_mu ly regs0)) Hmf Hmu).
Local Abbreviation U_tot := (AR2 (AR3 (AR6 (@YF82.U_tot _)))).
Local Abbreviation seg3Q_map := (AR2 (ARd (ARe (@YF82.seg3Q_map _ _)))).
Local Abbreviation seg3Q_ok := (AR2 (ARd (ARe (@YF82.seg3Q_ok _ _)))).
Local Abbreviation seg3M := (AR2 (ARd (ARe (@YF82.seg3M _ _)))).
Local Abbreviation seg3_Ur := (ARd (ARc (@YF83.seg3_Ur _ _))).
Local Abbreviation seg3_URe := (ARd (ARc (@YF83.seg3_URe _ _))).
Local Abbreviation seg3_URx := (ARd (ARc (@YF83.seg3_URx _ _))).
Local Abbreviation seg3_URg := ((AR5 (ARc (@YF83.seg3_URg _ _))) Hra Htp).
Local Abbreviation seg3_Ug := (AR2 (ARd (ARc (@YF83.seg3_Ug _ _)))).
Local Abbreviation P_ush := (@YF83.P_ush sha).
Local Abbreviation ARn f := (AR1 f Hsp) (only parsing).
Local Abbreviation pstable_ush := (AR2 (ARn (AR6 (@YF83.pstable_ush _)))).
Local Abbreviation seg3_Ums := (AR2 (AR5 (ARc (@YF83.seg3_Ums _ _)))).
Local Abbreviation XCOND_e := (@YF84.XCOND_e mu tot).
Local Abbreviation MUX_e := (@YF84.MUX_e mu).
Local Abbreviation factsX_e := (AR2 (AR1 (AR6 (@YF84.factsX_e _)))).
Local Abbreviation segC1_e := (AR2 (ARd (ARc (@YF84.segC1_e _ _)))).
Local Abbreviation segC2e_e := (AR2 (ARd (ARc (@YF84.segC2e_e _ _)))).
Local Abbreviation segC2g_e := (AR2 (ARd (ARc (@YF84.segC2g_e _ _)))).
Local Abbreviation segD_r_e := (ARd (ARc (@YF84.segD_r_e _ _))).
Local Abbreviation segD_re_e := (ARd (ARc (@YF84.segD_re_e _ _))).
Local Abbreviation segD_rx_e := (ARd (ARc (@YF84.segD_rx_e _ _))).
Local Abbreviation segD_rg_e := ((AR5 (ARc (@YF84.segD_rg_e _ _))) Hra Htp).
Local Abbreviation segD_g_e := (AR2 (ARd (ARc (@YF84.segD_g_e _ _)))).
Local Abbreviation P_fsh_e := (@YF84.P_fsh_e shf).
Local Abbreviation pstable_fsh_e := (AR2 (ARn (AR6 (@YF84.pstable_fsh_e _)))).
Local Abbreviation segD_ms_e := (AR2 (AR5 (ARc (@YF84.segD_ms_e _ _)))).
Local Abbreviation XCOND_g := (@YF85.XCOND_g mu tot).
Local Abbreviation MUX_g := (@YF85.MUX_g mu).
Local Abbreviation factsX_g := (AR2 (AR1 (AR6 (@YF85.factsX_g _)))).
Local Abbreviation segC1_g := (AR2 (ARd (ARc (@YF85.segC1_g _ _)))).
Local Abbreviation segC2e_g := (AR2 (ARd (ARc (@YF85.segC2e_g _ _)))).
Local Abbreviation segC2g_g := (AR2 (ARd (ARc (@YF85.segC2g_g _ _)))).
Local Abbreviation segD_r_g := (ARd (ARc (@YF85.segD_r_g _ _))).
Local Abbreviation segD_re_g := (ARd (ARc (@YF85.segD_re_g _ _))).
Local Abbreviation segD_rx_g := (ARd (ARc (@YF85.segD_rx_g _ _))).
Local Abbreviation segD_rg_g := ((AR5 (ARc (@YF85.segD_rg_g _ _))) Hra Htp).
Local Abbreviation segD_g_g := (AR2 (ARd (ARc (@YF85.segD_g_g _ _)))).
Local Abbreviation P_fsh_g := (@YF85.P_fsh_g shf).
Local Abbreviation pstable_fsh_g := (AR2 (ARn (AR6 (@YF85.pstable_fsh_g _)))).
Local Abbreviation segD_ms_g := (AR2 (AR5 (ARc (@YF85.segD_ms_g _ _)))).
Local Abbreviation XCOND_ee := (@YF86.XCOND_ee mu tot).
Local Abbreviation MUX_ee := (@YF86.MUX_ee mu).
Local Abbreviation MFY_ee := (@YF86.MFY_ee mf).
Local Abbreviation YCOND_ee := (@YF86.YCOND_ee mf nfe).
Local Abbreviation SRC3_ee := ((ARo (@YF86.SRC3_ee)) nfe).
Local Abbreviation factsX_ee := (AR2 (AR1 (AR6 (@YF86.factsX_ee _)))).
Local Abbreviation factsY_ee := (AR2 (AR1 (AR6 (@YF86.factsY_ee _)))).
Local Abbreviation val_mem_frame_ee := (@YF86.val_mem_frame_ee imgk).
Local Abbreviation P_fill_ee := (@YF86.P_fill_ee imgk ly c au csz nce nfe).
Local Abbreviation pstable_fill_ee := (AR2 (ARn (AR6 (@YF86.pstable_fill_ee _)))).
Local Abbreviation segE1_ee := (AR2 (AR5 (ARc (@YF86.segE1_ee _ _)))).
Local Abbreviation segE2_ee := (AR2 (ARd (ARc (@YF86.segE2_ee _ _)))).
Local Abbreviation P_cpy_ee := ((ARo (@YF86.P_cpy_ee)) nfe).
Local Abbreviation pstable_cpy_ee := (AR2 (ARn (AR6 (@YF86.pstable_cpy_ee _)))).
Local Abbreviation segE3_ee := (AR2 (AR5 (ARc (@YF86.segE3_ee _ _)))).
Local Abbreviation segE4_ee := (AR2 ((AR5 (ARc (@YF86.segE4_ee _ _))) Hra Htp)).
Local Abbreviation XCOND_eg := (@YF87.XCOND_eg mu tot).
Local Abbreviation MUX_eg := (@YF87.MUX_eg mu).
Local Abbreviation MFY_eg := (@YF87.MFY_eg mf).
Local Abbreviation YCOND_eg := (@YF87.YCOND_eg mf nfe).
Local Abbreviation SRC3_eg := ((ARo (@YF87.SRC3_eg)) nfe).
Local Abbreviation factsX_eg := (AR2 (AR1 (AR6 (@YF87.factsX_eg _)))).
Local Abbreviation factsY_eg := (AR2 (AR1 (AR6 (@YF87.factsY_eg _)))).
Local Abbreviation val_mem_frame_eg := (@YF87.val_mem_frame_eg imgk).
Local Abbreviation P_fill_eg := (@YF87.P_fill_eg imgk ly c au csz nce nfe).
Local Abbreviation pstable_fill_eg := (AR2 (ARn (AR6 (@YF87.pstable_fill_eg _)))).
Local Abbreviation segE1_eg := (AR2 (AR5 (ARc (@YF87.segE1_eg _ _)))).
Local Abbreviation segE2_eg := (AR2 (ARd (ARc (@YF87.segE2_eg _ _)))).
Local Abbreviation P_cpy_eg := ((ARo (@YF87.P_cpy_eg)) nfe).
Local Abbreviation pstable_cpy_eg := (AR2 (ARn (AR6 (@YF87.pstable_cpy_eg _)))).
Local Abbreviation segE3_eg := (AR2 (AR5 (ARc (@YF87.segE3_eg _ _)))).
Local Abbreviation segE4_eg := (AR2 ((AR5 (ARc (@YF87.segE4_eg _ _))) Hra Htp)).
Local Abbreviation XCOND_ge := (@YF88.XCOND_ge mu tot).
Local Abbreviation MUX_ge := (@YF88.MUX_ge mu).
Local Abbreviation MFY_ge := (@YF88.MFY_ge mf).
Local Abbreviation YCOND_ge := (@YF88.YCOND_ge mf nfg).
Local Abbreviation SRC3_ge := ((ARo (@YF88.SRC3_ge)) nfg).
Local Abbreviation factsX_ge := (AR2 (AR1 (AR6 (@YF88.factsX_ge _)))).
Local Abbreviation factsY_ge := (AR2 (AR1 (AR6 (@YF88.factsY_ge _)))).
Local Abbreviation val_mem_frame_ge := (@YF88.val_mem_frame_ge imgk).
Local Abbreviation P_fill_ge := (@YF88.P_fill_ge imgk ly c au csz ncg nfg).
Local Abbreviation pstable_fill_ge := (AR2 (ARn (AR6 (@YF88.pstable_fill_ge _)))).
Local Abbreviation segE1_ge := (AR2 (AR5 (ARc (@YF88.segE1_ge _ _)))).
Local Abbreviation segE2_ge := (AR2 (ARd (ARc (@YF88.segE2_ge _ _)))).
Local Abbreviation P_cpy_ge := ((ARo (@YF88.P_cpy_ge)) nfg).
Local Abbreviation pstable_cpy_ge := (AR2 (ARn (AR6 (@YF88.pstable_cpy_ge _)))).
Local Abbreviation segE3_ge := (AR2 (AR5 (ARc (@YF88.segE3_ge _ _)))).
Local Abbreviation segE4_ge := (AR2 ((AR5 (ARc (@YF88.segE4_ge _ _))) Hra Htp)).
Local Abbreviation XCOND_gg := (@YF89.XCOND_gg mu tot).
Local Abbreviation MUX_gg := (@YF89.MUX_gg mu).
Local Abbreviation MFY_gg := (@YF89.MFY_gg mf).
Local Abbreviation YCOND_gg := (@YF89.YCOND_gg mf nfg).
Local Abbreviation SRC3_gg := ((ARo (@YF89.SRC3_gg)) nfg).
Local Abbreviation factsX_gg := (AR2 (AR1 (AR6 (@YF89.factsX_gg _)))).
Local Abbreviation factsY_gg := (AR2 (AR1 (AR6 (@YF89.factsY_gg _)))).
Local Abbreviation val_mem_frame_gg := (@YF89.val_mem_frame_gg imgk).
Local Abbreviation P_fill_gg := (@YF89.P_fill_gg imgk ly c au csz ncg nfg).
Local Abbreviation pstable_fill_gg := (AR2 (ARn (AR6 (@YF89.pstable_fill_gg _)))).
Local Abbreviation segE1_gg := (AR2 (AR5 (ARc (@YF89.segE1_gg _ _)))).
Local Abbreviation segE2_gg := (AR2 (ARd (ARc (@YF89.segE2_gg _ _)))).
Local Abbreviation P_cpy_gg := ((ARo (@YF89.P_cpy_gg)) nfg).
Local Abbreviation pstable_cpy_gg := (AR2 (ARn (AR6 (@YF89.pstable_cpy_gg _)))).
Local Abbreviation segE3_gg := (AR2 (AR5 (ARc (@YF89.segE3_gg _ _)))).
Local Abbreviation segE4_gg := (AR2 ((AR5 (ARc (@YF89.segE4_gg _ _))) Hra Htp)).
Local Abbreviation fr := (@YF8a.fr c S).
Local Abbreviation hol := (@YF8a.hol c S).
Local Abbreviation len_facts3 := (AR8 ((ARb (@YF8a.len_facts3)) HcR)).
Local Abbreviation reg_S := (AR9 ((ARa (@YF8a.reg_S c nf)) S)).
Local Abbreviation reg_upd3 := (AR8 ((ARb (@YF8a.reg_upd3)) HcR)).
Local Abbreviation cache_upd3 := (AR8 ((ARb (@YF8a.cache_upd3)) HcR)).
Local Abbreviation PM3 := ((AR8 ((ARb (@YF8a.PM3)) maxc HcR Hmax)) Hinited).
Local Abbreviation WF1 := (AR8 (@YF8a.WF1 _ imgk W ly mem0)).
Local Abbreviation ARj f := (ARa f mu2) (only parsing).
Local Abbreviation rUp := ((ARj (@YF8a.rUp c)) S).
Local Abbreviation rUm := ((ARa (@YF8a.rUm c)) S).
Local Abbreviation SUp := ((ARj (@YF8a.SUp c)) S).
Local Abbreviation SUm := ((ARa (@YF8a.SUm c)) S).
Local Abbreviation MU1 := (@YF8a.MU1 mu mu2).
Local Abbreviation HO1 := (@YF8a.HO1 c mu S).
Local Abbreviation NC1 := (@YF8a.NC1 nce ncg).
Local Abbreviation NF1 := (@YF8a.NF1 nfe nfg).
Local Abbreviation AU1 := (@YF8a.AU1 aue aug).
Local Abbreviation rg1 := ((ARj (@YF8a.rg1 c)) S).
Local Abbreviation St1 := ((ARj (@YF8a.St1 c)) S).
Local Abbreviation rFp := ((ARj (@YF8a.rFp c)) mf2 S).
Local Abbreviation rFm := ((ARj (@YF8a.rFm c)) S).
Local Abbreviation SFp := ((ARj (@YF8a.SFp c)) mf2 S).
Local Abbreviation SFm := ((ARj (@YF8a.SFm c)) S).
Local Abbreviation MF2 := (@YF8a.MF2 mf mf2).
Local Abbreviation HO2 := (@YF8a.HO2 c mf mu S).
Local Abbreviation rg2 := ((ARj (@YF8a.rg2 c)) mf2 S).
Local Abbreviation St2 := ((ARj (@YF8a.St2 c)) mf2 S).
Local Abbreviation rP := ((ARj (@YF8a.rP c)) nce ncg mf2 aue aug S).
Local Abbreviation rQ := (@YF8a.rQ c mf mu mu2 mf2 aue aug S).
Local Abbreviation SQ := (@YF8a.SQ c maxc mf mu mu2 mf2 aue aug S).
Local Abbreviation S1_eq := (AR9 (AR8 ((ARj ((ARb (@YF8a.S1_eq)) nf)) HcR))).
Local Abbreviation reg_S1 := (AR9 (AR8 ((ARj ((ARb (@YF8a.reg_S1)) nf)) HcR))).
Local Abbreviation S2_eq := (AR9 (AR8 ((ARj ((ARb (@YF8a.S2_eq)) nf)) mf2 HcR))).
Local Abbreviation reg_S2 := (AR9 (AR8 ((ARj ((ARb (@YF8a.reg_S2)) nf)) mf2 HcR))).
Local Abbreviation upd_S1 := (AR9 (AR8 ((ARj ((ARb (@YF8a.upd_S1)) nf)) HcR))).
Local Abbreviation upd_S2 := (AR9 (AR8 ((ARj ((ARb (@YF8a.upd_S2)) nf)) mf2 HcR))).
Local Abbreviation XC3 := (@YF8a.XC3 mu tot).
Local Abbreviation factsX3 := (AR2 (AR1 (AR6 (@YF8a.factsX3 _)))).
Local Abbreviation round_user := (AR2 (AR1 (AR6 (@YF8a.round_user _)))).
Local Abbreviation round_fa := (AR2 (AR1 (AR6 (@YF8a.round_fa _)))).
Local Abbreviation runs_ok_new := (AR8 (AR2 (AR1 (AR4 (@YF8a.runs_ok_new _))))).
Local Abbreviation pop_new := ((AR8 (AR2 (AR1 (AR4 (@YF8a.pop_new _))))) Hnf_def).
Local Abbreviation E_mmu_e := (AR9 ((ARa (@YF8a.E_mmu_e c nf)) csz need tot Hcsz Htot S)).
Local Abbreviation E_mmu_g := (AR9 ((AR2 (AR1 (AR6 (@YF8a.E_mmu_g _)))) S)).
Local Abbreviation E_mmu_fail := (AR9 ((AR2 (AR1 (AR6 (@YF8a.E_mmu_fail _)))) S)).
Local Abbreviation E_efa_e := ((ARa (@YF8a.E_efa_e c)) tot mu2 nfe nfg S).
Local Abbreviation E_efa_g := ((AR2 (AR1 (AR6 (@YF8a.E_efa_g _)))) S).
Local Abbreviation E_efa_fail := ((AR2 (AR1 (AR6 (@YF8a.E_efa_fail _)))) S).
Local Abbreviation E_tail := ((AR8 (AR2 (AR1 (AR4 (@YF8a.E_tail _))))) Hnf_def).
Local Abbreviation E_tree := ((AR8 ((ARb (@YF8a.E_tree)) maxc n nf need HcR Hmax Hn Hnlt Hneed)) Hinited Hchunks Hnf_def).
Local Abbreviation E_pop := (@YF8a.E_pop c need S).
Local Abbreviation E_getreg1 := ((AR2 (AR1 (AR6 (@YF8a.E_getreg1 _)))) S Hnf_def).
Local Abbreviation reg_e := (AR9 ((ARj (@YF8a.reg_e c nf)) S)).
Local Abbreviation reg_g := (AR8 ((ARj (ARb (@YF8a.reg_g))) HcR)).
Local Abbreviation upd_e := (@YF8a.upd_e c S).
Local Abbreviation upd_g := ((ARj (@YF8a.upd_g c)) S).
Local Abbreviation reg_ee := (AR9 ((ARj (@YF8a.reg_ee c nf)) mf2 S)).
Local Abbreviation reg_ge := (AR8 ((ARj (ARb (@YF8a.reg_ge))) mf2 HcR)).
Local Abbreviation reg_xg := (AR8 ((ARj (ARb (@YF8a.reg_xg))) mf2 HcR)).
Local Abbreviation upd_xg := ((ARj (@YF8a.upd_xg c)) mf2 S).
Local Abbreviation zrange_dec := (@YF8d.zrange_dec).
Local Abbreviation apresent_word := (@YF8d.apresent_word).
Local Abbreviation val_mem_cell := (@YF8d.val_mem_cell imgk ly B).
Local Abbreviation val_mem_at := (@YF8d.val_mem_at imgk).
Local Abbreviation nth_error_run_elems := (@YF8d.nth_error_run_elems).
Local Abbreviation fa_nth_elems := (@YF8d.fa_nth_elems).
Local Abbreviation in_combine_seq := (@YF8d.in_combine_seq).
Local Abbreviation flat_map_ext_in := (@YF8d.flat_map_ext_in).
Local Abbreviation nth_error_rev := (@YF8d.nth_error_rev).
Local Abbreviation AU := (@YF8d.AU au csz).
Local Abbreviation NF' := (@YF8d.NF' nf).
Local Abbreviation NT := (@YF8d.NT).
Local Abbreviation rG := (@YF8d.rG au csz).
Local Abbreviation SG := (@YF8d.SG c maxc au csz S).
Local Abbreviation len_factsG := (AR8 ((ARb (@YF8d.len_factsG)) HcR)).
Local Abbreviation SG_parts := (AR8 ((ARb (@YF8d.SG_parts)) maxc au csz HcR)).
Local Abbreviation SG_sec_extents := (@YF8d.SG_sec_extents ly c maxc au csz S).
Local Abbreviation W_FEn := (@YF8d.W_FEn ly c nf).
Local Abbreviation ARf f := (f c nf adr sha mu2 fadr shf mf2) (only parsing).
Local Abbreviation XC := (ARf (@YF8d.XC ly)).
Local Abbreviation geo := (AR2 (AR1 (AR6 (@YF8d.geo _)))).
Local Abbreviation AGREE0 := (ARf (AR4 (@YF8d.AGREE0))).
Local Abbreviation AGX := ((ARf (ARe (@YF8d.AGX _))) Hsp B S HAR).
Local Abbreviation XC_where := (AR2 (AR1 (AR6 (@YF8d.XC_where _)))).
Local Abbreviation Z_img := (AR2 (AR1 (AR6 (@YF8d.Z_img _)))).
Local Abbreviation Z_band := (AR2 (AR1 (AR6 (@YF8d.Z_band _)))).
Local Abbreviation Z_T := (AR2 (AR1 (AR6 (@YF8d.Z_T _)))).
Local Abbreviation Z_prim := (AR2 (AR1 (AR6 (@YF8d.Z_prim _)))).
Local Abbreviation Z_high := (AR2 (AR1 (AR6 (@YF8d.Z_high _)))).
Local Abbreviation Z_out := (AR2 (AR1 (AR6 (@YF8d.Z_out _)))).
Local Abbreviation Z_ext := (AR2 (AR5 (AR6 (@YF8d.Z_ext _)))).
Local Abbreviation Z_sec := ((AR2 (AR5 (ARe (@YF8d.Z_sec _)))) B S HAR).
Local Abbreviation Z_user := ((AR8 (AR2 (AR1 (AR4 (@YF8d.Z_user _))))) Hmu_def).
Local Abbreviation UW_uncommitted := ((AR8 (AR2 (AR1 (AR4 (@YF8d.UW_uncommitted _))))) Hmu_def).
Local Abbreviation FW_uncommitted := ((AR8 (AR2 (AR1 (AR4 (@YF8d.FW_uncommitted _))))) Hmf_def).
Local Abbreviation VIS_MONO := (@YF8d.VIS_MONO imgk W mem0 mf mu adr fadr).
Local Abbreviation apresent_vis := (@YF8d.apresent_vis imgk).
Local Abbreviation aview_copy := (@YF8d.aview_copy imgk).
Local Abbreviation vis_keep := ((AR8 (AR2 (AR1 (ARe (@YF8d.vis_keep _))))) Hmf_def Hmu_def HAR).
Local Abbreviation loc_ok := (ARf (@YF8d.loc_ok ly)).
Local Abbreviation keep_cells := ((ARf (ARe (@YF8d.keep_cells _))) Hsp B S HAR).
Local Abbreviation keep_cell := ((ARf (ARe (@YF8d.keep_cell _))) Hsp B S HAR).
Local Abbreviation PCv := ((ARk (@YF8d.PCv imgk ly)) au csz).
Local Abbreviation PRW := ((ARk (@YF8d.PRW imgk ly)) au csz).
Local Abbreviation EL := (@YF8d.EL c au csz S).
Local Abbreviation EL_len := ((AR8 ((ARb (@YF8d.EL_len)) nf au csz HcR)) Hinited Hnf_def).
Local Abbreviation entry_rd := ((AR9 ((AR8 (AR2 (ARn (ARe (@YF8d.entry_rd _))))) Hinited)) HAR).
Local Abbreviation cells_regions := ((AR8 (AR2 (ARn (ARe (@YF8d.cells_regions _))))) HAR).
Local Abbreviation slot_cell := ((AR9 ((AR8 (AR2 (ARn (ARe (@YF8d.slot_cell _))))) Hinited)) HAR).
Local Abbreviation cells_caches := ((AR9 ((AR8 (AR2 (ARn (ARe (@YF8d.cells_caches _))))) Hinited)) HAR).
Local Abbreviation cells_chunks := ((AR8 (AR2 (AR5 (ARe (@YF8d.cells_chunks _))))) Hmu_def HAR).
Local Abbreviation cells_sec := ((ARh (AR2 (AR5 (ARe (@YF8d.cells_sec _))))) HARm HAR).
Local Abbreviation keep_batches := ((AR8 (AR2 (AR5 (ARe (@YF8d.keep_batches _))))) Hmu_def HAR).
Local Abbreviation cells_quar := ((ARh (AR2 (AR5 (ARe (@YF8d.cells_quar _))))) HARm Hmu_def HAR).
Local Abbreviation cells_fs := ((AR8 (AR2 (AR5 (ARe (@YF8d.cells_fs _))))) HAR).
Local Abbreviation cells_depot := ((ARh (AR2 (ARn (ARe (@YF8d.cells_depot _))))) HARm HAR).
Local Abbreviation cells_ialloc := ((ARh (AR2 (ARn (ARe (@YF8d.cells_ialloc _))))) HARm HAR).
Local Abbreviation cells_thread := ((AR2 (ARn (ARe (@YF8d.cells_thread _)))) B S HAR).
Local Abbreviation cells_final := ((AR9 ((ARh (AR2 (AR5 (ARe (@YF8d.cells_final _))))) HARm Hinited)) HAR).
Local Abbreviation fa_final := ((AR9 ((AR8 (AR2 (ARn (ARe (@YF8d.fa_final _))))) Hinited)) HAR).
Local Abbreviation flags_final := ((AR8 (AR2 (AR5 (ARe (@YF8d.flags_final _))))) HAR).
Local Abbreviation depot_ids_boundG := ((ARh ((ARa ((AR4 (@YF8d.depot_ids_boundG _)) maxc)) Hmf Hmu)) HARm).
Local Abbreviation depot_final := ((ARh (AR2 (AR5 (ARe (@YF8d.depot_final _))))) HARm HAR).
Local Abbreviation shadow_in_USH := (AR2 (AR1 (AR6 (@YF8d.shadow_in_USH _)))).
Local Abbreviation shadow_in_FSH := (AR2 (AR1 (AR6 (@YF8d.shadow_in_FSH _)))).
Local Abbreviation UQ2 := (AR2 (AR1 (AR6 (@YF8d.UQ2 _)))).
Local Abbreviation FQ2 := (AR2 (AR1 (AR6 (@YF8d.FQ2 _)))).
Local Abbreviation committed_shadow_old := ((AR8 (AR2 (AR5 (ARe (@YF8d.committed_shadow_old _))))) Hmf_def Hmu_def HAR).
Local Abbreviation shadow_final := ((AR8 (AR2 (AR5 (ARe (@YF8d.shadow_final _))))) Hmf_def Hmu_def HAR).
Local Abbreviation zshadow_final := ((AR2 (ARn (ARe (@YF8d.zshadow_final _)))) B S HAR).
Local Abbreviation vis_final := ((AR8 (AR2 (AR1 (ARe (@YF8d.vis_final _))))) Hinited Hmf_def Hmu_def HAR).
Local Abbreviation abs_cell_okG := (@YF8d.abs_cell_okG imgk).
Local Abbreviation abs_cells_okG := (@YF8d.abs_cells_okG imgk).
Local Abbreviation const_final := ((ARh (AR2 (ARn (ARe (@YF8d.const_final _))))) HTSD HAR).
Local Abbreviation AR_transportG := ((AR9 ((ARh (AR2 (AR5 (ARe (@YF8d.AR_transportG _))))) HTSD HARm Hinited)) HAR).
Local Abbreviation XC_owned := ((AR8 (AR2 (AR5 (ARe (@YF8d.XC_owned _))))) Hau_def Hmu_def HAR).
Local Abbreviation LEAF_G := ((AR9 ((ARh (AR2 (AR5 (ARe (@YF8d.LEAF_G _ _))))) HTSD HARm Hinited)) HAR).
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
pose proof (at_R3_eq Wx md X P ss ss' W' c' HR ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as H2; clear HR; rename H2 into HR end.
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
pose proof (at_R3_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:(img_exact HU)) as H2;
clear HU HR; rename H2 into HR) ] end.
Ltac r3_arm HR cnd tk a b :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HB := fresh "HB" in
assert (HB : branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk);
[ | img_try (let H2 := fresh "HR" in
pose proof (at_R3_arm Wx md X P ss W' c' cnd tk a b HR ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) HB) as H2;
clear HB HR; rename H2 into HR) ] end.
Ltac r3_forget HR k clob :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_R3_forget Wx md X P ss W' c' k clob HR ltac:(img_try (unfold aHAV3; (img_case; cbv); zlia)) ltac:(img_eqrefl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as H2;
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
Let WF := am_wf B ly S _ HARm.
Hypothesis Hpum : refill_reg S c.
Hypothesis Hslack : A_bytes (w_A W) + EV_A <= abudget S.
Hypothesis Hql : qloose S.
Lemma NZ0 : forall q, In q (vm_maps (m_vmmaps md0)) -> 0 < bv_unsigned (snd q).
Proof. img_exact (proj2 (proj1 (proj2 (proj2 (proj2 HAR))))). Qed.
Lemma SRr_with_AI : forall (Wx : world tfxsegs) cx (Q : world tfxsegs -> config -> Prop),
SRr tfxsegs Wx cx Q -> SRr tfxsegs Wx cx (fun W' c' => AI tfxsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. clear. intros Wx cx Q H b HI T HK. img_apply (H b HI T). intros W' c' Hle HI' HQ. img_exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Lemma lit_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1). Proof. clear. img_apply bv_eq. img_refl. Qed.
Lemma lit_enomem : Z_to_bv 64 ENOMEM_RET = errno_ret ENOMEM. Proof. clear. unfold errno_ret, ENOMEM, ENOMEM_RET. img_apply bv_eq. img_refl. Qed.

Lemma Hcut_out : forall (Hh : word -> bool) lo hi (a : word), ~ (lo <= bv_unsigned a < hi) -> Hcut Hh lo hi a = Hh a.
Proof.
clear. intros Hh lo hi a Ha. unfold Hcut. destruct (Z.leb_spec lo (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) hi); cbn [andb negb]; try (exfalso; zlia);
rewrite ?andb_true_r, ?andb_false_r; try img_refl; exfalso; img_apply Ha; zlia.
Qed.
Lemma apresent_hmono : forall (Ha Hb : word -> bool) m a, (forall y, Ha y = false -> Hb y = false) -> apresent Ha m a -> apresent Hb m a.
Proof. clear. intros Ha Hb m a Hm [H1 H2]. split; [img_try (img_exact (Hm _ H1)) | img_try (img_exact H2)]. Qed.

Lemma aview_high_apresent : forall (Hh : word -> bool) mem a, TFX_IMG_END <= a < 2 ^ 64 -> aview tfxsegs Hh mem a <> None -> apresent Hh mem a.
Proof.
clear. intros Hh mem a Ha HV. unfold aview in HV. destruct (mbyte tfxsegs (mrestrict Hh mem) a) as [b|] eqn:E; [|img_try (exfalso; img_exact (HV ltac:(img_eqrefl)))].
img_exact (mbyte_high_apresent Hh mem a b Ha E).
Qed.
Lemma ALedger_shape : forall S1 S2 md,
(forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S2 c') = rg_mapped_user (reg S1 c') /\ rg_mapped_fa (reg S2 c') = rg_mapped_fa (reg S1 c') /\ rg_holes (reg S2 c') = rg_holes (reg S1 c')) ->
sec_extents ly S2 = sec_extents ly S1 -> sec_live_bytes S2 = sec_live_bytes S1 -> prim_committed S2 = prim_committed S1 ->
st_nev S2 = st_nev S1 -> st_sec_reserved S2 = st_sec_reserved S1 ->
ALedger tfxsegs ly S1 md -> ALedger tfxsegs ly S2 md.
Proof.
clear. intros S1 S2 md RGEQ SE SL PC NEV SR L. destruct L as [L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
assert (CUT : forall x, cut_ok ly S2 x <-> cut_ok ly S1 x).
{ intros x. unfold cut_ok. split; (intros [H|[H|(c' & Hc' & H)]]; [img_try (left; img_exact H) | img_try (right; left; img_exact H) | img_try (right; right; exists c'; split; [img_exact Hc'|])]);
destruct (RGEQ c' Hc') as (Q1 & Q2 & Q3); [img_try (rewrite <- Q1, <- Q2) | img_try (rewrite Q1, Q2)]; img_exact H. }
assert (HOLE : forall a, prim_hole_at ly S2 a <-> prim_hole_at ly S1 a).
{ intros a. unfold prim_hole_at. split; intros (c' & h & Hc' & Hin & H); exists c', h; destruct (RGEQ c' Hc') as (Q1 & Q2 & Q3);
[img_try (rewrite <- Q3) | img_try (rewrite Q3)]; (split; [img_try (img_exact Hc') | img_try (split; [img_exact Hin | img_exact H])]). }
constructor; try assumption.
- destruct L3 as (pieces & (Q1 & Q2 & Q3) & P2). exists pieces. split; [|img_try (img_exact P2)]. split; [|img_try (split; [img_exact Q2|])].
+ img_apply Forall_forall. intros p' Hp. pose proof (proj1 (Forall_forall _ _) Q1 p' Hp) as (A1 & A2 & A3). split; [img_try (img_exact A1)|]. split; img_apply CUT; assumption.
+ intros a Ha. rewrite (Q3 a Ha). rewrite HOLE. tauto.
- rewrite SE. img_exact L6.
- rewrite SE. img_exact L7.
- rewrite PC, SE, SR. img_exact L8.
-   rewrite SE. img_exact L11.
Qed.
Definition FL50 : word := Z_to_bv 64 50.
Lemma nores50 : mmap_noreserve_b FL50 = false. Proof. clear. img_refl. Qed.
Lemma core50 : mmap_flags_core FL50 = 50. Proof. clear. img_refl. Qed.
Lemma grant_piece_shape : forall (a n : word) md,
vm_maps (m_vmmaps (grant_md false FL50 a n md)) = vm_maps (m_vmmaps md) /\
vm_reserved (m_vmmaps (grant_md false FL50 a n md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (grant_md false FL50 a n md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (grant_md false FL50 a n md)) = vm_mmap_base (m_vmmaps md) /\
vm_init_sp (m_vmmaps (grant_md false FL50 a n md)) = vm_init_sp (m_vmmaps md).
Proof. clear. intros a n md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite nores50. cbn. destruct md as [fd [maps lazy mat] io fs pr lim tm]. cbn. destruct maps; cbn. repeat split; img_refl. Qed.
Lemma grant_hole_shape : forall (a n : word) md,
vm_maps (m_vmmaps (grant_md true FL50 a n md)) = (a, n) :: vm_maps (m_vmmaps md) /\
vm_reserved (m_vmmaps (grant_md true FL50 a n md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (grant_md true FL50 a n md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (grant_md true FL50 a n md)) = vm_mmap_base (m_vmmaps md) /\
vm_init_sp (m_vmmaps (grant_md true FL50 a n md)) = vm_init_sp (m_vmmaps md).
Proof. clear. intros a n md. unfold grant_md, with_mmap_backing, mmap_model. rewrite nores50. destruct md as [fd [maps lazy mat] io fs pr lim tm]. cbn. destruct maps; cbn. repeat split; img_refl. Qed.
Lemma ROOM3 : rg_mapped_user (reg S c) + kUserMapSize <= kUserMapSize * EV_MAX /\
(st_nev S <= EV_MAX \/ rg_alloc_user (reg S c) <= class_size c * (65536 - 10240)).
Proof.
pose proof class_facts as (C1 & C2 & C3 & C4 & C5).
img_apply (preg_room (as_universe B) 1 0 0 S S c n (WF1 (proj1 Hpum)) HcR (Z.le_refl 1) Hinited (regs_only_refl S) ltac:(img_eqrefl) Hchunks ltac:(img_try (clear - C3; zlia)) (proj1 (proj2 Hpum))).
rewrite <- Hnf_def. img_exact Hnlt.
Qed.
Lemma refill_tree_ok : forall ns, atok ns (refill_tree c S) (fun _ r => Wf (as_universe B) (snd r)).
Proof.
intros ns. pose proof (WF1 (proj1 Hpum)) as W1. pose proof (class_ok c HcR) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs). pose proof class_facts as (C1 & C2 & C3 & C4 & C5).
assert (HL : (Z.to_nat c < length (st_regions S))%nat) by (img_try (eapply WfP_len_regions; [img_try (img_exact W1) | img_try (clear - HcR; zlia)])).
assert (HLc : (Z.to_nat c < length (st_cache S))%nat) by (img_try (eapply WfP_len_cache; [img_try (img_exact W1) | img_try (clear - HcR; zlia)])).
unfold refill_tree. img_apply atok_bind. unfold init_cache_if_needed. img_apply atok_bind. img_apply atok_get. cbn [fst snd]. rewrite Hinited. img_apply atok_ret. cbn [fst snd].
unfold refill_if_empty. img_apply atok_bind. img_apply atok_get_pc. cbn [fst snd]. rewrite Hchunks, PM3, <- Hn.
img_apply atok_bind.
eapply atok_mono; [|img_try (img_apply (get_from_allocator_ok (as_universe B) 1 0 0 S c n ns W1 HcR (Z.le_refl 1)); [clear - C3; zlia | rewrite Hn, Hmax; img_exact Kmcs | clear - C3; zlia | intros _; img_exact ROOM3])].
intros ns1 [got s2] Hg. cbn [fst snd]. destruct got as [tops|].
- destruct Hg as (r2 & rest & W2 & -> & Hruns & Hel & Hlen & Hfl). img_apply atok_set_pc. cbn [snd].
set (r' := mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)).
rewrite <- (upd_reg_upd_reg c r2 r' S).
pose proof (wf_classes _ _ _ _ _ W2 c HcR) as C0. unfold wf_class in C0.
rewrite reg_upd_reg in C0 by (img_try ((clear - HcR; zlia) || img_exact HL)). img_change (cache (upd_reg c r2 S) c) with (cache S c) in C0.
img_change (st_cache_inited (upd_reg c r2 S)) with (st_cache_inited S) in C0. rewrite Hinited in C0.
unfold Wf. eapply (WfP_set_region_pc (as_universe B) 0 0 0 (upd_reg c r2 S) c); [img_try (img_exact W2) | img_try (img_exact HcR) | | img_try (clear; zlia) | | |].
+ img_change (st_cache_inited (upd_reg c r2 S)) with (st_cache_inited S). rewrite Hinited.
img_change (chunk_offs (upd_reg c r2 S) c) with (chunk_offs S c). img_change (batch_offs (upd_reg c r2 S) c) with (batch_offs S c).
eapply (cls_ok_repart c r2 (cache S c) true _ _ r' _ true _ _ []); try img_exact C0; try img_refl.
* img_exact Hruns.
* (subst r'; cbv beta). cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]. pose proof (wr_fa_len _ _ _ _ _ _ C0). clear - H Hfl Hlen C3. zlia.
* cbn [pc_max pc_chunks]. split; [img_try (rewrite Hmax; img_refl)|]. unfold cache_fill_order. rewrite length_rev, <- Hmax. pose proof (Z.div_mod maxc 2 ltac:(img_try (clear; zlia))) as DM. pose proof (Z.mod_pos_bound maxc 2 ltac:(img_try (clear; zlia))) as MB. clear - Hlen C1 C3 Hn DM MB. zlia.
* (subst r'; cbv beta). cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]. rewrite Hel, Hchunks. unfold cache_fill_order. cbn [pc_chunks app].
img_change (chunk_offs (upd_reg c r2 S) c) with (chunk_offs S c). img_change (batch_offs (upd_reg c r2 S) c) with (batch_offs S c).
pose proof (perm_cache_refill (fa_elems (class_size c) rest) [] (chunk_offs S c) (batch_offs S c) tops) as PP. cbn [app] in PP. img_exact PP.
+ rewrite reg_upd_reg by (img_try ((clear - HcR; zlia) || img_exact HL)). (subst r'; cbv beta). cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]. pose proof (wf_prim_ev _ _ _ _ _ W2) as PE.
unfold kUserMapSize in *. clear - PE. zlia.
+
pose proof (wf_fa_room _ _ _ _ _ W2 c HcR) as RM. unfold class_elems in RM. rewrite !reg_upd_reg in RM by (img_try ((clear - HcR; zlia) || img_exact HL)).
img_change (cache (upd_reg c r2 S) c) with (cache S c) in RM. rewrite Hel, Hchunks in RM.
change (chunk_offs (upd_reg c r2 S) c) with (chunk_offs S c) in RM |- *. change (batch_offs (upd_reg c r2 S) c) with (batch_offs S c) in RM |- *.
change (st_nev (upd_reg c r2 S)) with (st_nev S) in RM |- *.
(subst r'; cbv beta). cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd pc_chunks]. unfold cache_fill_order.
eapply fa_room_xfer; [img_try (img_exact RM) | img_try (rewrite !length_app, length_rev; cbn [length]; clear; zlia) | img_try (img_apply Z.le_refl)].
+
img_apply (regime_cap_keep (as_universe B) 0 0 0 (upd_reg c r2 S) c _ W2 HcR); rewrite reg_upd_reg by (img_try ((clear - HcR; zlia) || img_exact HL)); (subst r'; cbv beta); cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]; [img_refl | img_try (clear; zlia)].
- destruct Hg as (r' & -> & W2 & NS). img_apply atok_ret. cbn [snd]. unfold Wf. eapply WfP_weaken; [img_try (img_exact W2) | | |]; clear; zlia.
Qed.
Definition RANGE (addr : Z) (a : Z) : Prop := addr <= a < addr + kUserMapSize.
Definition SHR (sh : Z) (a : Z) : Prop := sh <= a < sh + 32768.
Definition P_grant {imgk : img} (W3 : world tfxsegs) (addr sh : Z) (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ (forall a, RANGE addr a -> apresent (w_H W3) m a /\ m (w64 a) = Some (Z_to_bv 8 0)) /\
(forall a, SHR sh a -> apresent (w_H W3) m a).
Lemma fo_dead_commit3 : forall regs pc mem md (I : Type) (nx : I -> config) (j i : I) (a : word) mj memj mi memi,
getr regs 17 = Z_to_bv 64 222 ->
node_ok tfxsegs (mkCfg (pend_at regs pc mem (seg_rom tfxsegs)) md) I (fun _ => []) nx ->
nx j = mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) memj (seg_rom tfxsegs)) mj ->
bv_unsigned a < 2 ^ 64 - 4095 ->
nx i = mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) memi (seg_rom tfxsegs)) mi ->
fo_dead tfxsegs (mkCfg (pend_at regs pc mem (seg_rom tfxsegs)) md) (nx i).
Proof.
clear. intros regs pc mem md I nx j i a mj memj mi memi H17 Hnode Hj Ha Hi.
assert (H222 : bv_unsigned (getr regs 17) = 222) by (rewrite H17; img_apply unsigned_lit_small; clear; zlia).
assert (RG : forall v, reg_get (regupd regs 10 v) (Z_to_bv 5 10) = v).
{ intros v. unfold regupd, reg_get. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (img_apply bv_eq; img_refl). rewrite bvmap_get_set_same. img_refl. }
img_apply (fo_dead_node tfxsegs (pend_at regs pc mem (seg_rom tfxsegs)) md (getr regs 17) I (fun _ => []) nx j i Hnode eq_refl (injected_family_off_mmap tfxsegs _ _ H222)).
- rewrite Hj. img_refl.
- rewrite Hj. cbn [cfg_ms ms_regs YK11.mkst]. rewrite RG. img_apply mmap_grant_not_refusal; [img_exact H222 | img_exact Ha].
- rewrite Hi. img_refl.
- rewrite Hi. cbn [cfg_ms ms_regs YK11.mkst]. rewrite RG. img_apply mmap_enomem_refusal. img_exact H222.
Qed.
Lemma node3 : forall (q : kreq) (sN : astate) (K : Z -> itree astate (unit * astate)) (Q : unit * astate -> world tfxsegs -> config -> Prop)
(Wx : world tfxsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (c1 : config)
(ea : sv) (addr sh : Z) (hole : bool) (cs : list YQ0b.chunk),
at_N3 Wx md X P ss Wx c1 -> AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c1) ->
ss_pc ss = (0x64c88 + D_2c4) ->
sr_get (ss_regs ss) 17%bv = SLit 222 -> sr_get (ss_regs ss) 10%bv = ea -> sv_atoms_lt aHAV3 ea = true -> U E0 ea = addr ->
sr_get (ss_regs ss) 11%bv = SLit 262144 -> sr_get (ss_regs ss) 12%bv = SLit 3 -> sr_get (ss_regs ss) 13%bv = SLit 50 ->
sr_get (ss_regs ss) 14%bv = SLit 18446744073709551615 -> sr_get (ss_regs ss) 15%bv = SLit 0 ->
no_cdata (ss_mem ss) = true -> nth_error (ss_mem ss) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs) ->
map skel (tl (ss_mem ss)) = SKEL_TAILR ->
addr mod 65536 = 0 -> RBv <= addr -> addr + kUserMapSize <= RBv + 2 ^ 32 ->
sh = SHBv + addr / 8 -> sh mod 4096 = 0 -> kHighShadowBeg <= sh -> sh + 32768 <= kHighShadowEnd ->
(if hole then region_free (vm_reserved (m_vmmaps (cfg_model c1)) ++ vm_maps (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = true
else region_free (vm_reserved (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = true /\
map_contains (vm_maps (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = true) ->
amwf (cfg_model c1) ->
YN05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
eager_used (cfg_model c1) + A_bytes (w_A Wx) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps (cfg_model c1)) ->
refusable q = true -> (forall z, z = 0 \/ z = 1 -> aok sN q z) ->
(forall m m' : word -> option byte, (forall x : word, ~ RANGE addr (bv_unsigned x) -> m' x = m x) -> P m -> P m') ->
(forall a, SHR sh a -> ~ X a) -> (forall a, SHR sh a -> mem0 (w64 a) <> None) ->
hole = false ->
(forall c', at_R3 Wx (cfg_model c1) X P (resume ss (SLit ENOMEM_RET) (ss_mem ss) (ss_facts ss)) Wx c' ->
AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c') -> srealizesM tfxsegs false c' t_nil) ->
(forall c', let md3 := fixedin_destroyed_model (w64 addr) (w64 kUserMapSize) (cfg_model c1) in
AI tfxsegs (w_H Wx) (w_A Wx) md3 -> amwf md3 -> same_io md0 md3 -> eager_used md3 <= eager_used (cfg_model c1) ->
at_R3 Wx md3 (fun a => X a \/ RANGE addr a) P (resume ss (SLit ENOMEM_RET) (ss_mem ss) (ss_facts ss)) Wx c' ->
amrealE tfxsegs (K 0) Wx c' Q) ->
(forall (W3 : world tfxsegs) c', let md2 := grant_md hole FL50 (w64 addr) (w64 kUserMapSize) (cfg_model c1) in
wle Wx W3 -> w_A W3 = (sh, sh + 32768) :: (addr, addr + kUserMapSize) :: w_A Wx -> hsub (w_H W3) (w_H Wx) ->
(forall a : word, w_H Wx a = false -> w_H W3 a = false) ->
AI tfxsegs (w_H W3) (w_A W3) md2 -> amwf md2 -> same_io md0 md2 -> eager_used md2 <= eager_used (cfg_model c1) + kUserMapSize ->
(forall a : word, ~ RANGE addr (bv_unsigned a) -> ~ SHR sh (bv_unsigned a) -> w_H W3 a = w_H Wx a) ->
A_bytes (w_A W3) = A_bytes (w_A Wx) + kUserMapSize + 32768 ->
at_R3 W3 md2 (fun a => X a \/ RANGE addr a) (P_grant W3 addr sh P) (resume ss ea (ss_mem ss) (ss_facts ss)) W3 c' ->
amreal tfxsegs (K 1) W3 c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfxsegs c1 I (fun _ => []) nx /\
(forall i, AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c1) -> AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(refusable q = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model (nx i)) -> srealizesM tfxsegs false (nx i) t_nil) /\
(forall i, (sp i = true \/ bit i <> 1) -> fo_dead tfxsegs c1 (nx i)) /\
(forall i, sp i = false -> if Z.eqb (bit i) 1 then amreal tfxsegs (K (bit i)) Wx (nx i) Q else amrealE tfxsegs (K (bit i)) Wx (nx i) Q).
Proof.
intros q sN K Q Wx md X P ss c1 ea addr sh hole cs HN HAI Hpc H17 H10 Hea Uea H11 H12 H13 H14 H15 Hnc Hhd Hsk
Hal HaRB HaHI Hsh Hshal Hshlo Hshhi PLACE MWn HTOP SLACK Hrq Haok HPu HXsh H0sh HOLEF KEEP DESTR GRANT IO0.
pose proof stack_ext_ok3 as [SX1 SX2]. pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & _). pose proof stack_ivsR as (_ & _ & _ & S4 & S5).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (EcM : cfg_model c1 = mdN) by (img_try (rewrite Ec; img_refl)). rewrite EcM in *.
destruct (st_ok_ecall_shape_r tfxsegs (w_H Wx) E' ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
rewrite Hpc in Hms.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
assert (A0 : 0 <= addr /\ addr + kUserMapSize < 2 ^ 63) by (img_try (clear - HaRB HaHI DR; numconst; unfold kUserMapSize in *; zlia)).
assert (A4096 : addr mod 4096 = 0) by (img_try (clear - Hal; apply Z.mod_divide in Hal as [q' Hq]; [|img_try (zlia)]; rewrite Hq; img_apply Z.mod_divide; [img_try (zlia)|]; exists (q' * 16); zlia)).
assert (Uaddr : bv_unsigned (w64 addr) = addr) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - A0; unfold kUserMapSize in A0; zlia)).
assert (Un : bv_unsigned (w64 kUserMapSize) = kUserMapSize) by (img_try (unfold w64; img_apply unsigned_lit_small; unfold kUserMapSize; clear; zlia)).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (img_try (rewrite (Hregs 17%bv), H17; img_refl)).
assert (R10 : getr regs 10 = w64 addr).
{ rewrite (Hregs 10%bv), H10. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' ea)). f_equal.
img_change (bv_unsigned (sv_denot E' ea)) with (U E' ea). rewrite (U_agree aHAV3 E0 E' ea HE Hea). img_exact Uea. }
assert (R11 : getr regs 11 = Z_to_bv 64 262144) by (img_try (rewrite (Hregs 11%bv), H11; img_refl)).
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (img_try (rewrite (Hregs 12%bv), H12; img_refl)).
assert (R13 : getr regs 13 = FL50) by (img_try (rewrite (Hregs 13%bv), H13; img_refl)).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (img_try (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; img_apply lit_m1)).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 15%bv), H15; img_refl)).
assert (MWF0 : MWF mdN) by (img_try (img_apply (proj1 (amwf_MWF mdN)); img_exact (proj1 MWn))).
pose proof (commit_nonempty hole FL50 (w64 addr) (w64 kUserMapSize) mdN ltac:(img_try (rewrite Un; unfold kUserMapSize; clear; zlia)) (proj2 MWn)) as NZg.
assert (CEIL : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_ceiling).
{ rewrite Uaddr. img_change (page_round_up_Z 262144) with 262144. clear - HaHI DR. numconst. unfold kUserMapSize in *. zlia. }
assert (CEILT : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_top (m_vmmaps mdN)).
{ eapply Z.le_trans; [img_try (img_exact CEIL) | img_try (img_apply YN05.ceil_le_top; img_exact HTOP)]. }
assert (PLACE' : if hole then region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = true
else region_free (vm_reserved (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = true /\
map_contains (vm_maps (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = true).
{ img_change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize). img_exact PLACE. }
assert (SL1 : eager_used mdN + A_bytes (w_A Wx) + page_round_up_Z 262144 <= vm_limit (m_vmmaps mdN)).
{ img_change (page_round_up_Z 262144) with 262144. clear - SLACK. unfold kUserMapSize in SLACK. zlia. }
pose proof (commit_AI tfxsegs (w_H Wx) (w_A Wx) mdN hole FL50 (w64 addr) 262144 HAI MWF0 nores50
ltac:(img_try (rewrite Uaddr; unfold page_size; img_exact A4096)) ltac:(img_try (clear; zlia)) CEILT PLACE' SL1) as [CG BUD].
pose proof (commit_eager tfxsegs (w_H Wx) (w_A Wx) mdN hole FL50 (w64 addr) 262144 HAI MWF0 nores50
ltac:(img_try (rewrite Uaddr; unfold page_size; img_exact A4096)) ltac:(img_try (clear; zlia)) CEILT PLACE' SL1) as EG.
change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in CG, BUD, EG.
img_change (page_round_up_Z 262144) with 262144 in EG.
pose proof (destroyed_AI tfxsegs (w_H Wx) (w_A Wx) mdN (w64 addr) 262144 HAI MWF0
ltac:(img_try (rewrite Uaddr; unfold page_size; img_exact A4096)) ltac:(img_try (clear; zlia)) CEILT) as [CD EGD].
change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in CD, EGD.
destruct (commit_node3 tfxsegs hole regs (Z_to_bv 64 (0x64c88 + D_2c4)) mem (seg_rom tfxsegs) mdN FL50 (w64 addr) 262144
(AI_halted _ _ _ _ HAI) R17 R10 ltac:(img_try (rewrite Uaddr; unfold page_size; img_exact A4096)) ltac:(img_try (rewrite Uaddr; clear - HaRB DR; numconst; zlia))
R11 ltac:(img_try (clear; zlia)) CEILT R12 R13 core50 R14 R15 PLACE' BUD) as (I & nx & bit & i0 & i1 & NODE & Bi0 & Bi1 & Bi2 & OUT).
img_change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in OUT.
destruct (Bi2 HOLEF) as (i2 & Bi2').
destruct Hmem as (Hwf & _ & _).
assert (REXT : forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r ->
~ RANGE addr a /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. destruct (ss_mem ss) as [|r0 tl0] eqn:Em; [img_try (destruct Hr)|]. try rewrite Em in Hhd; try rewrite Em in Hsk. cbn [nth_error] in Hhd. injection Hhd as Hr0. cbn [List.tl] in Hsk.
destruct Hr as [<-|Hr].
- rewrite Hr0 in Ha. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha. rewrite (HEn 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2 in Ha.
unfold RANGE. clear - Ha SX1 S4 S5 HaRB HaHI. numconst. unfold kUserMapSize in *. try unfold sp0 in *. zlia.
- apply (in_map skel) in Hr. rewrite Hsk in Hr. pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7).
unfold RANGE. clear - Ha X2 X3 X6 HaRB HaHI. unfold kUserMapSize in *. zlia. }
assert (RWIN : forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_whi r ->
~ RANGE addr a /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. pose proof (region_wf_facts r (regions_wf_In _ r Hwf Hr)) as (_ & WW & _). img_apply (REXT r a Hr). clear - Ha WW. zlia. }
assert (SCR : forall a, sp0 - RSTACK <= a < sp0 -> ~ RANGE addr a) by (img_try (intros a Ha; unfold RANGE; clear - Ha SX1 HaRB HaHI; unfold kUserMapSize in *; zlia)).
assert (LIMg : vm_limit (m_vmmaps (grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN)) = vm_limit (m_vmmaps mdN)).
{ destruct hole; [img_try (img_exact (proj1 (proj2 (proj2 (grant_hole_shape _ _ _))))) | img_try (img_exact (proj1 (proj2 (proj2 (grant_piece_shape _ _ _)))))]. }
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, (fun i => if bit i =? 1 then 1 else 0), (fun i => bit i =? 0), i0.
split. { rewrite Ec, Hms. img_exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & [[_ [-> ->]] | [[_ [-> ->]] | [_ [_ [-> ->]]]]]); cbn [cfg_model];
[img_try (img_exact HAI) | img_try (img_exact (proj1 CG)) | img_try (img_exact (proj1 CD))]. }
split. { intros i. img_apply Haok. destruct (bit i =? 1); [img_try (right) | img_try (left)]; img_refl. }
split; [img_try (rewrite Bi0; img_refl)|]. split; [img_try (rewrite Bi0; img_refl)|]. split; [img_try (intros _; exists i2; rewrite Bi2'; split; img_refl)|].
split.
{
intros i Ei HAIi. apply Z.eqb_eq in Ei. destruct (OUT i) as (md_i & Hh_i & IO_i & [[Bv [NX MD]] | [[Bv _] | [Bv _]]]); [| img_try (rewrite Bv in Ei; discriminate Ei) | img_try (rewrite Bv in Ei; discriminate Ei)].
rewrite NX in HAIi |- *. rewrite MD in HAIi |- *. img_apply KEEP; [| img_try (img_exact HAIi)].
pose proof (at_N3_cont Wx Wx mdN X P ss (SLit ENOMEM_RET) (errno_ret ENOMEM) (fun _ => False) mem ms E' HE HS Hrv MEQ PRS (hsub_refl _)
ltac:(img_try (cbn [sv_denot]; img_apply lit_enomem)) Hnc ltac:(img_try (intros x _; rewrite Hms; img_refl))
(fun r a Hr Ha => conj (fun f : False => f) (proj2 (REXT r a Hr Ha)))
(fun r a Hr Ha => conj (fun f : False => f) (proj2 (RWIN r a Hr Ha)))
(fun a _ (f : False) => f) ltac:(img_try (rewrite Hms in HPm; img_exact HPm))) as C.
rewrite Hms in C. cbn [ms_regs pend_at] in C. rewrite Hpc in C.
eapply at_R3_weaken; [img_try (img_exact C) | img_try (intros a [Ha|[]]; img_exact Ha) | img_try (intros m Hm; img_exact Hm)]. }
split.
{ intros i Hi. cbv beta in Hi.
assert (Bn1 : bit i <> 1).
{ intros E1. destruct Hi as [Hi|Hi]; [apply Z.eqb_eq in Hi; rewrite E1 in Hi; discriminate Hi | apply Hi; rewrite E1; img_refl]. }
destruct (OUT i0) as (md_0 & _ & _ & [[B0 _] | [[_ [NX0 _]] | [B0 _]]]); [exfalso; rewrite Bi0 in B0; discriminate B0 | | exfalso; rewrite Bi0 in B0; discriminate B0].
rewrite Ec, Hms.
destruct (OUT i) as (md_i & _ & _ & [[_ [NXi _]] | [[Bv _] | [_ [_ [NXi _]]]]]); [| exfalso; exact (Bn1 Bv) |];
(eapply (fo_dead_commit3 regs _ mem mdN I nx i0 i (w64 addr)); [img_exact R17 | img_exact NODE | img_exact NX0 | rewrite Uaddr; clear - A0; unfold kUserMapSize in A0; zlia | img_exact NXi]). }
intros i Ei. apply Z.eqb_neq in Ei. destruct (OUT i) as (md_i & Hh_i & IO_i & [[Bv _] | [[Bv [NX MD]] | [Bv [_ [NX MD]]]]]); [img_try (exfalso; img_exact (Ei Bv)) | | ]; rewrite Bv, NX; rewrite MD in IO_i |- *; cbn [Z.eqb Pos.eqb].
2:{
set (md3 := fixedin_destroyed_model (w64 addr) (w64 kUserMapSize) mdN) in *.
assert (FRu : forall x : word, ~ RANGE addr (bv_unsigned x) -> unfill (w64 addr) (w64 kUserMapSize) mem x = mem x).
{ intros x Hx. img_apply unfill_out. rewrite Uaddr, Un. unfold RANGE in Hx. clear - Hx. zlia. }
img_apply DESTR; [img_try (img_exact (proj1 CD)) | img_try (split; [img_apply (proj2 (amwf_MWF md3)); img_exact (proj2 CD) | img_exact (destroyed_nonempty (w64 addr) (w64 kUserMapSize) mdN (proj2 MWn))]) | img_try (img_exact (IOtr _ IO_i)) | img_try (img_exact EGD) |].
pose proof (at_N3_cont Wx Wx md3 X P ss (SLit ENOMEM_RET) (errno_ret ENOMEM) (RANGE addr) (unfill (w64 addr) (w64 kUserMapSize) mem) ms E'
HE HS Hrv MEQ PRS (hsub_refl _) ltac:(img_try (cbn [sv_denot]; img_apply lit_enomem)) Hnc
ltac:(img_try (intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; img_exact (FRu x Hx))) REXT RWIN SCR) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc in C. rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm.
img_apply C. img_exact (HPu mem _ FRu HPm). }
-
set (md2 := grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN) in *.
assert (AL1 : addr <= addr + kUserMapSize) by (img_try (unfold kUserMapSize; clear; zlia)).
assert (AL2 : addr mod page_size = 0) by (img_try (unfold page_size; img_exact A4096)).
assert (AL3 : (addr + kUserMapSize) mod page_size = 0).
{ unfold page_size. clear - A4096. apply Z.mod_divide in A4096 as [q' Hq]; [|img_try (zlia)]. rewrite Hq. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q' + 64). unfold kUserMapSize. zlia. }
destruct (allow_expose tfxsegs Wx md2 addr (addr + kUserMapSize) AL1 AL2 AL3 (proj1 CG) ltac:(img_try (rewrite LIMg; clear - EG SLACK; unfold kUserMapSize in *; zlia)))
as (LE2 & A2 & AB2 & VIS2 & MON2 & AI2).
set (W2 := wallow tfxsegs Wx addr (addr + kUserMapSize) AL1 AL2 AL3) in *.
assert (SL1' : sh <= sh + 32768) by (img_try (clear; zlia)).
assert (SL2 : sh mod page_size = 0) by (img_try (unfold page_size; img_exact Hshal)).
assert (SL3 : (sh + 32768) mod page_size = 0).
{ unfold page_size. clear - Hshal. apply Z.mod_divide in Hshal as [q' Hq]; [|img_try (zlia)]. rewrite Hq. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q' + 8). zlia. }
destruct (allow_expose tfxsegs W2 md2 sh (sh + 32768) SL1' SL2 SL3 AI2 ltac:(img_try (rewrite LIMg, AB2; clear - EG SLACK; unfold kUserMapSize in *; zlia)))
as (LE3 & A3 & AB3 & VIS3 & MON3 & AI3).
set (W3 := wallow tfxsegs W2 sh (sh + 32768) SL1' SL2 SL3) in *.
assert (MON : forall a : word, w_H Wx a = false -> w_H W3 a = false) by (img_try (intros a Ha; apply MON3, MON2, Ha)).
assert (SUB : hsub (w_H W3) (w_H Wx)).
{ intros a Ha. destruct (w_H Wx a) eqn:Ex; [img_refl|]. rewrite (MON a Ex) in Ha. discriminate Ha. }
eapply (amreal_world_le tfxsegs _ Wx W3); [img_try (img_exact (wle_trans _ _ _ _ LE2 LE3)) | img_try (intros _; img_exact AI3) |].
img_apply (GRANT W3); [img_try (img_exact (wle_trans _ _ _ _ LE2 LE3)) | img_try (rewrite A3, A2; img_refl) | img_try (img_exact SUB) | img_try (img_exact MON) | img_try (img_exact AI3)
| img_try (split; [img_apply (proj2 (amwf_MWF md2)); img_exact (proj2 CG) | img_exact NZg]) | img_try (img_exact (IOtr _ IO_i)) | img_try (img_exact EG)
| img_try (intros a N1 N2; unfold W3, W2, wallow; cbn [w_H]; rewrite (Hcut_out _ sh (sh + 32768) a) by img_exact N2; img_apply Hcut_out; unfold RANGE in N1; img_exact N1)
| img_try (rewrite AB3, AB2; clear; unfold kUserMapSize; zlia) |].
assert (FRz : forall x : word, ~ RANGE addr (bv_unsigned x) -> zfill (w64 addr) (w64 kUserMapSize) mem x = mem x).
{ intros x Hx. img_apply zfill_out. rewrite Uaddr, Un. unfold RANGE in Hx. clear - Hx. zlia. }
pose proof (at_N3_cont Wx W3 md2 X (P_grant W3 addr sh P) ss ea (w64 addr) (RANGE addr) (zfill (w64 addr) (w64 kUserMapSize) mem) ms E'
HE HS Hrv MEQ PRS SUB ltac:(img_try (rewrite <- R10; symmetry; rewrite <- H10; img_exact (Hregs 10%bv))) Hnc
ltac:(img_try (intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; img_exact (FRz x Hx))) REXT RWIN SCR) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc in C. rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm.
img_apply C. split; [img_try (img_exact (HPu mem _ FRz HPm))|]. split.
+ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (unfold RANGE in Ha; clear - Ha A0; unfold kUserMapSize in *; zlia)).
assert (Z0 : zfill (w64 addr) (w64 kUserMapSize) mem (w64 a) = Some (Z_to_bv 8 0)).
{ img_apply zfill_in. rewrite Uaddr, Un. unfold w64. rewrite unsigned_lit_small by img_exact Ra. img_exact Ha. }
split; [|img_try (img_exact Z0)]. split; [|img_try (exists (Z_to_bv 8 0); img_exact Z0)].
img_apply MON3. img_apply VIS2. unfold w64. rewrite unsigned_lit_small by img_exact Ra. img_exact Ha.
+ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (unfold SHR in Ha; clear - Ha Hshlo Hshhi; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)).
split; [img_try (img_apply VIS3; unfold w64; rewrite unsigned_lit_small by img_exact Ra; img_exact Ha)|].
assert (NR : ~ RANGE addr a) by (img_try (unfold RANGE, SHR in *; clear - Ha Hshhi HaRB DR; numconst; unfold kHighShadowEnd in *; zlia)).
pose proof (FRz (w64 a) ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_exact Ra; img_exact NR))) as E.
assert (NZ : mem (w64 a) <> None).
{ pose proof (MEQ (w64 a) ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_exact Ra; img_exact (HXsh a Ha)))) as EQm. rewrite Hms in EQm. cbn [ms_mem pend_at] in EQm. rewrite EQm. img_exact (H0sh a Ha). }
unfold w64 in E, NZ |- *. rewrite E.
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (NZ ltac:(img_eqrefl)))].
Qed.
Definition FLR : word := Z_to_bv 64 0x104022.
Lemma noresR : mmap_noreserve_b FLR = true. Proof. clear. img_refl. Qed.
Lemma coreR : noreplace_core (mmap_flags_core FLR). Proof. clear. left. img_refl. Qed.
Lemma lit_eexist : Z_to_bv 64 EEXIST_RET = errno_ret EEXIST. Proof. clear. unfold errno_ret, EEXIST, EEXIST_RET. img_apply bv_eq. img_refl. Qed.
Lemma allowed_head : forall (A : list (Z * Z)) slo shi (w : word), slo mod 4096 = 0 -> shi mod 4096 = 0 -> slo <= bv_unsigned w < shi ->
page_allowedb ((slo, shi) :: A) (page_base w) = true.
Proof.
clear. intros A slo shi w H2 H3 [L1 L2]. unfold page_allowedb. cbn [existsb fst snd]. img_apply orb_true_iff. left.
pose proof (u64_range w) as Rw.
assert (PB : bv_unsigned (page_base w) = bv_unsigned w / 4096 * 4096).
{ unfold page_base, page_base_of, page_size. img_apply unsigned_lit_small. split; [img_try (img_apply Z.mul_nonneg_nonneg; [img_apply Z.div_pos; img_lia | img_lia]) |].
pose proof (Z.mul_div_le (bv_unsigned w) 4096 ltac:(img_lia)). img_lia. }
rewrite PB. unfold page_size. img_apply andb_true_iff. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.leb_le)].
- apply Z.mod_divide in H2 as [q Hq]; [|img_lia]. rewrite Hq in L1 |- *. assert (q <= bv_unsigned w / 4096) by (img_try (img_apply Z.div_le_lower_bound; img_lia)). nia.
- apply Z.mod_divide in H3 as [r Hr]; [|img_lia]. rewrite Hr in L2 |- *. assert (bv_unsigned w / 4096 < r) by (img_try (img_apply Z.div_lt_upper_bound; img_lia)). nia.
Qed.
Lemma node3r : forall {RT : Type} (t : itree astate RT) (Q : RT -> world tfxsegs -> config -> Prop)
(Wx : world tfxsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (c1 : config)
(ea : sv) (addr : Z) (cs : list YQ0b.chunk),
at_N3 Wx md X P ss Wx c1 -> AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c1) ->
ss_pc ss = (0x64c88 + D_2c4) ->
sr_get (ss_regs ss) 17%bv = SLit 222 -> sr_get (ss_regs ss) 10%bv = ea -> sv_atoms_lt aHAV3 ea = true -> U E0 ea = addr ->
sr_get (ss_regs ss) 11%bv = SLit 262144 -> sr_get (ss_regs ss) 12%bv = SLit 0 -> sr_get (ss_regs ss) 13%bv = SLit 0x104022 ->
sr_get (ss_regs ss) 14%bv = SLit 18446744073709551615 -> sr_get (ss_regs ss) 15%bv = SLit 0 ->
no_cdata (ss_mem ss) = true -> nth_error (ss_mem ss) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs) ->
map skel (tl (ss_mem ss)) = SKEL_TAILR ->
addr mod 65536 = 0 -> RBv <= addr -> addr + kUserMapSize <= RBv + 2 ^ 32 ->
region_free (vm_reserved (m_vmmaps (cfg_model c1)) ++ vm_maps (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = true ->
amwf (cfg_model c1) ->
YN05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
eager_used (cfg_model c1) + A_bytes (w_A Wx) + kUserMapSize <= vm_limit (m_vmmaps (cfg_model c1)) ->
(forall m m' : word -> option byte, (forall x : word, ~ RANGE addr (bv_unsigned x) -> m' x = m x) -> P m -> P m') ->
(forall c', at_R3 Wx (cfg_model c1) X P (resume ss (SLit ENOMEM_RET) (ss_mem ss) (ss_facts ss)) Wx c' ->
AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c') -> srealizesM tfxsegs false c' t_nil) ->
(forall (W4 : world tfxsegs) c', let md4 := restore_md FLR (w64 addr) (w64 kUserMapSize) (cfg_model c1) in
wle Wx W4 -> w_A W4 = (addr, addr + kUserMapSize) :: w_A Wx -> hsub (w_H W4) (w_H Wx) ->
(forall a : word, w_H Wx a = false -> w_H W4 a = false) ->
(forall a : word, ~ RANGE addr (bv_unsigned a) -> w_H W4 a = w_H Wx a) ->
AI tfxsegs (w_H W4) (w_A W4) md4 -> amwf md4 -> same_io md0 md4 -> eager_used md4 <= eager_used (cfg_model c1) ->
A_bytes (w_A W4) = A_bytes (w_A Wx) + kUserMapSize ->
at_R3 W4 md4 (fun a => X a \/ RANGE addr a) P (resume ss ea (ss_mem ss) (ss_facts ss)) W4 c' ->
amrealE tfxsegs t W4 c' Q) ->
same_io md0 (cfg_model c1) ->
amrealE tfxsegs t Wx c1 Q.
Proof.
intros RT t Q Wx md X P ss c1 ea addr cs HN HAI Hpc H17 H10 Hea Uea H11 H12 H13 H14 H15 Hnc Hhd Hsk
Hal HaRB HaHI PLACE MWn HTOP SLACK HPu ERR GRANT IO0.
pose proof stack_ext_ok3 as [SX1 SX2]. pose proof derived_rangesR as DR. pose proof stack_ivsR as (_ & _ & _ & S4 & S5).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (EcM : cfg_model c1 = mdN) by (img_try (rewrite Ec; img_refl)). rewrite EcM in *.
destruct (st_ok_ecall_shape_r tfxsegs (w_H Wx) E' ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
rewrite Hpc in Hms.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
assert (A0 : 0 <= addr /\ addr + kUserMapSize < 2 ^ 63) by (img_try (clear - HaRB HaHI DR; numconst; unfold kUserMapSize in *; zlia)).
assert (A4096 : addr mod 4096 = 0) by (img_try (clear - Hal; apply Z.mod_divide in Hal as [q' Hq]; [|img_try (zlia)]; rewrite Hq; img_apply Z.mod_divide; [img_try (zlia)|]; exists (q' * 16); zlia)).
assert (Uaddr : bv_unsigned (w64 addr) = addr) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - A0; unfold kUserMapSize in A0; zlia)).
assert (Un : bv_unsigned (w64 kUserMapSize) = kUserMapSize) by (img_try (unfold w64; img_apply unsigned_lit_small; unfold kUserMapSize; clear; zlia)).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (img_try (rewrite (Hregs 17%bv), H17; img_refl)).
assert (R10 : getr regs 10 = w64 addr).
{ rewrite (Hregs 10%bv), H10. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' ea)). f_equal.
img_change (bv_unsigned (sv_denot E' ea)) with (U E' ea). rewrite (U_agree aHAV3 E0 E' ea HE Hea). img_exact Uea. }
assert (R11 : getr regs 11 = Z_to_bv 64 262144) by (img_try (rewrite (Hregs 11%bv), H11; img_refl)).
assert (R12 : getr regs 12 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 12%bv), H12; img_refl)).
assert (R13 : getr regs 13 = FLR) by (img_try (rewrite (Hregs 13%bv), H13; img_refl)).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (img_try (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; img_apply lit_m1)).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 15%bv), H15; img_refl)).
assert (MWF0 : MWF mdN) by (img_try (img_apply (proj1 (amwf_MWF mdN)); img_exact (proj1 MWn))).
assert (CEIL : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_ceiling).
{ rewrite Uaddr. img_change (page_round_up_Z 262144) with 262144. clear - HaHI DR. numconst. unfold kUserMapSize in *. zlia. }
assert (CEILT : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_top (m_vmmaps mdN)).
{ eapply Z.le_trans; [img_try (img_exact CEIL) | img_try (img_apply YN05.ceil_le_top; img_exact HTOP)]. }
assert (PLACE' : region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = true).
{ img_change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize). img_exact PLACE. }
assert (AL1 : addr <= addr + kUserMapSize) by (img_try (unfold kUserMapSize; clear; zlia)).
assert (AL2 : addr mod page_size = 0) by (img_try (unfold page_size; img_exact A4096)).
assert (AL3 : (addr + kUserMapSize) mod page_size = 0).
{ unfold page_size. clear - A4096. apply Z.mod_divide in A4096 as [q' Hq]; [|img_try (zlia)]. rewrite Hq. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q' + 64). unfold kUserMapSize. zlia. }
destruct (allow_expose tfxsegs Wx mdN addr (addr + kUserMapSize) AL1 AL2 AL3 HAI ltac:(img_try (clear - SLACK; unfold kUserMapSize in *; zlia)))
as (LE4 & A4 & AB4 & VIS4 & MON4 & AI4).
set (W4 := wallow tfxsegs Wx addr (addr + kUserMapSize) AL1 AL2 AL3) in *.
assert (SUB4 : hsub (w_H W4) (w_H Wx)).
{ intros a Ha. destruct (w_H Wx a) eqn:Ex; [img_refl|]. rewrite (MON4 a Ex) in Ha. discriminate Ha. }
pose proof (restore_AI tfxsegs (w_H W4) (w_A W4) mdN FLR (w64 addr) 262144 AI4 MWF0 noresR
ltac:(img_try (rewrite Uaddr; unfold page_size; img_exact A4096)) ltac:(img_try (clear; zlia)) CEILT PLACE'
ltac:(img_try (intros w Hw _; rewrite A4; img_apply allowed_head; [img_try (img_exact A4096) | img_try (unfold page_size in AL3; img_exact AL3) | img_try (rewrite Uaddr in Hw; img_change (page_round_up_Z 262144) with 262144 in Hw; unfold kUserMapSize; img_exact Hw)]))) as [CR EGR].
change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in CR, EGR.
destruct (restore_node tfxsegs true regs (Z_to_bv 64 (0x64c88 + D_2c4)) mem (seg_rom tfxsegs) mdN FLR (w64 addr) 262144
(AI_halted _ _ _ _ HAI) R17 R10 ltac:(img_try (rewrite Uaddr; unfold page_size; img_exact A4096)) ltac:(img_try (rewrite Uaddr; clear - HaRB DR; numconst; zlia))
R11 ltac:(img_try (clear; zlia)) CEILT R12 R13 coreR R14 R15 PLACE') as (I & nx & ok & i1 & NODE & Oi1 & Oi0 & OUT).
img_change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in OUT.
destruct (Oi0 ltac:(img_eqrefl)) as (i0 & Oi0').
destruct Hmem as (Hwf & _ & _).
assert (REXT : forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r ->
~ RANGE addr a /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. destruct (ss_mem ss) as [|r0 tl0] eqn:Em; [img_try (destruct Hr)|]. try rewrite Em in Hhd; try rewrite Em in Hsk. cbn [nth_error] in Hhd. injection Hhd as Hr0. cbn [List.tl] in Hsk.
destruct Hr as [<-|Hr].
- rewrite Hr0 in Ha. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha. rewrite (HEn 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2 in Ha.
unfold RANGE. clear - Ha SX1 S4 S5 HaRB HaHI. numconst. unfold kUserMapSize in *. try unfold sp0 in *. zlia.
- apply (in_map skel) in Hr. rewrite Hsk in Hr. pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7).
unfold RANGE. clear - Ha X2 X3 X6 HaRB HaHI. unfold kUserMapSize in *. zlia. }
assert (RWIN : forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_whi r ->
~ RANGE addr a /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. pose proof (region_wf_facts r (regions_wf_In _ r Hwf Hr)) as (_ & WW & _). img_apply (REXT r a Hr). clear - Ha WW. zlia. }
assert (SCR : forall a, sp0 - RSTACK <= a < sp0 -> ~ RANGE addr a) by (img_try (intros a Ha; unfold RANGE; clear - Ha SX1 HaRB HaHI; unfold kUserMapSize in *; zlia)).
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
img_apply (amrealE_silent_node tfxsegs t Wx c1 I nx (fun i => negb (ok i)) (fun i => if ok i then W4 else Wx) i0 Q).
- rewrite Ec, Hms. img_exact NODE.
- intros i _. destruct (OUT i) as (md_i & _ & _ & [[Ok [MD (e & _ & NX)]] | [Ok [_ [NX MD]]]]); rewrite Ok, NX; cbn [cfg_model]; rewrite MD.
+ split; [img_try (img_apply wle_refl) | img_try (img_exact HAI)].
+ split; [img_try (img_exact LE4) | img_try (img_exact (proj1 CR))].
- rewrite Oi0'. img_refl.
-
intros i Ei HAIi. apply negb_true_iff in Ei. destruct (OUT i) as (md_i & Hh_i & IO_i & [[Ok [MD (e & [He|[Hf _]] & NX)]] | [Ok _]]); [| img_try (discriminate Hf) | img_try (rewrite Ei in Ok; discriminate Ok)].
rewrite Ei in HAIi. (subst e; cbv beta). rewrite NX in HAIi |- *. rewrite MD in HAIi |- *. img_apply ERR; [| img_try (img_exact HAIi)].
pose proof (at_N3_cont Wx Wx mdN X P ss (SLit ENOMEM_RET) (errno_ret ENOMEM) (fun _ => False) mem ms E' HE HS Hrv MEQ PRS (hsub_refl _)
ltac:(img_try (cbn [sv_denot]; img_apply lit_enomem)) Hnc ltac:(img_try (intros x _; rewrite Hms; img_refl))
(fun r a Hr Ha => conj (fun f : False => f) (proj2 (REXT r a Hr Ha)))
(fun r a Hr Ha => conj (fun f : False => f) (proj2 (RWIN r a Hr Ha)))
(fun a _ (f : False) => f) ltac:(img_try (rewrite Hms in HPm; img_exact HPm))) as C.
rewrite Hms in C. cbn [ms_regs pend_at] in C. rewrite Hpc in C.
eapply at_R3_weaken; [img_try (img_exact C) | img_try (intros a [Ha|[]]; img_exact Ha) | img_try (intros m Hm; img_exact Hm)].
-
intros i Ei. apply negb_false_iff in Ei. destruct (OUT i) as (md_i & Hh_i & IO_i & [[Ok _] | [Ok [_ [NX MD]]]]); [img_try (rewrite Ei in Ok; discriminate Ok)|].
rewrite Ei, NX. rewrite MD in IO_i |- *.
set (md4 := restore_md FLR (w64 addr) (w64 kUserMapSize) mdN) in *.
assert (FRu : forall x : word, ~ RANGE addr (bv_unsigned x) -> unfill (w64 addr) (w64 kUserMapSize) mem x = mem x).
{ intros x Hx. img_apply unfill_out. rewrite Uaddr, Un. unfold RANGE in Hx. clear - Hx. zlia. }
img_apply (GRANT W4); [img_try (img_exact LE4) | img_try (img_exact A4) | img_try (img_exact SUB4) | img_try (img_exact MON4)
| img_try (intros a N1; unfold W4, wallow; cbn [w_H]; img_apply Hcut_out; unfold RANGE in N1; img_exact N1)
| img_try (img_exact (proj1 CR))
| img_try (split; [img_apply (proj2 (amwf_MWF md4)); img_exact (proj2 CR) | img_exact (restore_nonempty FLR (w64 addr) (w64 kUserMapSize) mdN ltac:(rewrite Un; unfold kUserMapSize; clear; zlia) (proj2 MWn))])
| img_try (img_exact (IOtr _ IO_i)) | img_try (img_exact EGR) | img_try (rewrite AB4; clear; unfold kUserMapSize; zlia) |].
pose proof (at_N3_cont Wx W4 md4 X P ss ea (w64 addr) (RANGE addr) (unfill (w64 addr) (w64 kUserMapSize) mem) ms E'
HE HS Hrv MEQ PRS SUB4 ltac:(img_try (rewrite <- R10; symmetry; rewrite <- H10; img_exact (Hregs 10%bv))) Hnc
ltac:(img_try (intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; img_exact (FRu x Hx))) REXT RWIN SCR) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc in C. rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm.
img_apply C. img_exact (HPu mem _ FRu HPm).
Qed.
Lemma node3k : forall (Wx : world tfxsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (c1 : config)
(ea : sv) (addr : Z) (cs : list YQ0b.chunk),
at_N3 Wx md X P ss Wx c1 -> AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c1) ->
ss_pc ss = (0x64c88 + D_2c4) ->
sr_get (ss_regs ss) 17%bv = SLit 222 -> sr_get (ss_regs ss) 10%bv = ea -> sv_atoms_lt aHAV3 ea = true -> U E0 ea = addr ->
sr_get (ss_regs ss) 11%bv = SLit 262144 -> sr_get (ss_regs ss) 12%bv = SLit 0 -> sr_get (ss_regs ss) 13%bv = SLit 0x104022 ->
sr_get (ss_regs ss) 14%bv = SLit 18446744073709551615 -> sr_get (ss_regs ss) 15%bv = SLit 0 ->
no_cdata (ss_mem ss) = true -> nth_error (ss_mem ss) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs) ->
map skel (tl (ss_mem ss)) = SKEL_TAILR ->
addr mod 65536 = 0 -> RBv <= addr -> addr + kUserMapSize <= RBv + 2 ^ 32 ->
region_free (vm_reserved (m_vmmaps (cfg_model c1)) ++ vm_maps (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = false ->
YN05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
(forall c', at_R3 Wx (cfg_model c1) X P (resume ss (SLit ENOMEM_RET) (ss_mem ss) (ss_facts ss)) Wx c' ->
AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c') -> srealizesM tfxsegs false c' t_nil) ->
(forall c', at_R3 Wx (cfg_model c1) X P (resume ss (SLit EEXIST_RET) (ss_mem ss) (ss_facts ss)) Wx c' ->
AI tfxsegs (w_H Wx) (w_A Wx) (cfg_model c') -> srealizesM tfxsegs false c' t_nil) ->
srealizesM tfxsegs false c1 t_nil.
Proof.
intros Wx md X P ss c1 ea addr cs HN HAI Hpc H17 H10 Hea Uea H11 H12 H13 H14 H15 Hnc Hhd Hsk Hal HaRB HaHI PLACE HTOP ERRE ERRX.
pose proof stack_ext_ok3 as [SX1 SX2]. pose proof derived_rangesR as DR. pose proof stack_ivsR as (_ & _ & _ & S4 & S5).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (EcM : cfg_model c1 = mdN) by (img_try (rewrite Ec; img_refl)). rewrite EcM in *.
destruct (st_ok_ecall_shape_r tfxsegs (w_H Wx) E' ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
rewrite Hpc in Hms.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
assert (A0 : 0 <= addr /\ addr + kUserMapSize < 2 ^ 63) by (img_try (clear - HaRB HaHI DR; numconst; unfold kUserMapSize in *; zlia)).
assert (A4096 : addr mod 4096 = 0) by (img_try (clear - Hal; apply Z.mod_divide in Hal as [q' Hq]; [|img_try (zlia)]; rewrite Hq; img_apply Z.mod_divide; [img_try (zlia)|]; exists (q' * 16); zlia)).
assert (Uaddr : bv_unsigned (w64 addr) = addr) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - A0; unfold kUserMapSize in A0; zlia)).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (img_try (rewrite (Hregs 17%bv), H17; img_refl)).
assert (R10 : getr regs 10 = w64 addr).
{ rewrite (Hregs 10%bv), H10. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' ea)). f_equal.
img_change (bv_unsigned (sv_denot E' ea)) with (U E' ea). rewrite (U_agree aHAV3 E0 E' ea HE Hea). img_exact Uea. }
assert (R11 : getr regs 11 = Z_to_bv 64 262144) by (img_try (rewrite (Hregs 11%bv), H11; img_refl)).
assert (R12 : getr regs 12 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 12%bv), H12; img_refl)).
assert (R13 : getr regs 13 = FLR) by (img_try (rewrite (Hregs 13%bv), H13; img_refl)).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (img_try (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; img_apply lit_m1)).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 15%bv), H15; img_refl)).
assert (CEIL : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_ceiling).
{ rewrite Uaddr. img_change (page_round_up_Z 262144) with 262144. clear - HaHI DR. numconst. unfold kUserMapSize in *. zlia. }
assert (CEILT : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_top (m_vmmaps mdN)).
{ eapply Z.le_trans; [img_try (img_exact CEIL) | img_try (img_apply YN05.ceil_le_top; img_exact HTOP)]. }
assert (PLACE' : region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = false).
{ img_change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize). img_exact PLACE. }
destruct (restore_node tfxsegs false regs (Z_to_bv 64 (0x64c88 + D_2c4)) mem (seg_rom tfxsegs) mdN FLR (w64 addr) 262144
(AI_halted _ _ _ _ HAI) R17 R10 ltac:(img_try (rewrite Uaddr; unfold page_size; img_exact A4096)) ltac:(img_try (rewrite Uaddr; clear - HaRB DR; numconst; zlia))
R11 ltac:(img_try (clear; zlia)) CEILT R12 R13 coreR R14 R15 PLACE') as (I & nx & ok & i1 & NODE & Oi1 & _ & OUT).
destruct Hmem as (Hwf & _ & _).
assert (REXT : forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. destruct (ss_mem ss) as [|r0 tl0] eqn:Em; [img_try (destruct Hr)|]. try rewrite Em in Hhd; try rewrite Em in Hsk. cbn [nth_error] in Hhd. injection Hhd as Hr0. cbn [List.tl] in Hsk.
destruct Hr as [<-|Hr].
- rewrite Hr0 in Ha. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha. rewrite (HEn 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2 in Ha.
clear - Ha SX1 S4 S5. numconst. try unfold sp0 in *. zlia.
- apply (in_map skel) in Hr. rewrite Hsk in Hr. pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7).
clear - Ha X2 X3 X6. zlia. }
assert (RWIN : forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_whi r -> 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. pose proof (region_wf_facts r (regions_wf_In _ r Hwf Hr)) as (_ & WW & _). img_apply (REXT r a Hr). clear - Ha WW. zlia. }
assert (CONT : forall (e : sv) (v : word), sv_denot E' e = v ->
at_R3 Wx mdN X P (resume ss e (ss_mem ss) (ss_facts ss)) Wx (mkCfg (mkst (regupd regs 10%bv v) (v_addi (Z_to_bv 64 (0x64c88 + D_2c4)) 4) mem (seg_rom tfxsegs)) mdN)).
{ intros e v Hev.
pose proof (at_N3_cont Wx Wx mdN X P ss e v (fun _ => False) mem ms E' HE HS Hrv MEQ PRS (hsub_refl _) Hev Hnc ltac:(img_try (intros x _; rewrite Hms; img_refl))
(fun r a Hr Ha => conj (fun f : False => f) (REXT r a Hr Ha))
(fun r a Hr Ha => conj (fun f : False => f) (RWIN r a Hr Ha))
(fun a _ (f : False) => f) ltac:(img_try (rewrite Hms in HPm; img_exact HPm))) as C.
rewrite Hms in C. cbn [ms_regs pend_at] in C. rewrite Hpc in C.
eapply at_R3_weaken; [img_try (img_exact C) | img_try (intros a [Ha|[]]; img_exact Ha) | img_try (intros m Hm; img_exact Hm)]. }
img_apply (node_all_spin tfxsegs Wx c1 I nx i1); [img_try (rewrite Ec, Hms; img_exact NODE) | | | img_try (rewrite EcM; img_exact HAI)].
- intros i _. destruct (OUT i) as (md_i & _ & _ & [[_ [MD (e & _ & NX)]] | [_ [Hf _]]]); [| img_try (discriminate Hf)]. rewrite NX. cbn [cfg_model]. rewrite MD. img_exact HAI.
- intros i HAIi. destruct (OUT i) as (md_i & _ & _ & [[_ [MD (e & [He|[_ He]] & NX)]] | [_ [Hf _]]]); [| | img_try (discriminate Hf)]; (subst e; cbv beta); rewrite NX in HAIi |- *; rewrite MD in HAIi |- *.
+ img_apply ERRE; [| img_try (img_exact HAIi)]. img_apply CONT. cbn [sv_denot]. img_apply lit_enomem.
+ img_apply ERRX; [| img_try (img_exact HAIi)]. img_apply CONT. cbn [sv_denot]. img_apply lit_eexist.
Qed.
Definition LEAFQ : unit * astate -> world tfxsegs -> config -> Prop := refill_leaf B ly S W regs0 mem0 md0 c.
Lemma VIS64 : forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r -> 0 <= aeval B ly (fst r) + i < 2 ^ 64.
Proof.
intros r i Hr Hi.
pose proof (vis_lists_u64 B ly S _ (proj1 HAR) ltac:(img_try (intros r' Hr'; destruct (ts_junk B TS ly r' Hr') as (z & E & Z1 & Z2); exists z; split; [img_try (img_exact E)|]; unfold kImgEnd; clear - Z1 Z2; zlia)) r i Hr Hi) as X.
ceil; unfold ASAN_CEIL in X. clear - X. zlia.
Qed.
Definition PF (Wd : world tfxsegs) (NC MU MF : Z) (TOPS : list Z) (m : word -> option byte) : Prop :=
(forall a, FAv <= a < FAv + mf -> apresent (w_H Wd) m a) /\
(forall a, DSTv <= a < DSTv + 64 -> apresent (w_H Wd) m a) /\
(MU = mu2 -> forall a, adr <= a < adr + kUserMapSize -> apresent (w_H Wd) m a) /\
(MU = mu2 -> forall x : word, W_USH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250) /\ w_H Wd x = false) /\
(MF = mf2 -> forall a, fadr <= a < fadr + kFreeArrayMapSize -> apresent (w_H Wd) m a) /\
(MF = mf2 -> forall x : word, W_FSH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250) /\ w_H Wd x = false) /\
(forall i, 0 <= i < NC -> val_mem tfxsegs (mrestrict (w_H Wd) m) (FAv + 4 * (nf + NC) - 4 - 4 * i) 4 ((au + i * csz) / 16)) /\
(forall j, 0 <= j < 4 * Z.of_nat (length TOPS) -> m (w64 (DSTv + j)) = m (w64 (FAv + 4 * (nf + NC - Z.of_nat (length TOPS)) + j))).
Lemma or_dec : forall A B : Prop, (A \/ ~ A) -> (B \/ ~ B) -> (A \/ B) \/ ~ (A \/ B).
Proof. clear. intros A B [a|a] [b|b]; try (left; tauto); right; tauto. Qed.
Lemma and_dec : forall A B : Prop, (A \/ ~ A) -> (B \/ ~ B) -> (A /\ B) \/ ~ (A /\ B).
Proof. clear. intros A B [a|a] [b|b]; try (right; tauto); left; tauto. Qed.
Lemma zr_dec : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. clear. intros lo hi a. destruct (zrange_dec lo hi a); [img_try (left)|img_try (right)]; assumption. Qed.
Lemma beq_dec : forall b : bool, b = true \/ ~ (b = true).
Proof. clear. intros [|]; [img_try (left; img_refl) | img_try (right; discriminate)]. Qed.
Lemma zeq_dec : forall x y : Z, x = y \/ ~ (x = y).
Proof. clear. intros x y. destruct (Z.eq_dec x y); [img_try (left)|img_try (right)]; assumption. Qed.
Lemma zle_dec : forall x y : Z, x <= y \/ ~ (x <= y).
Proof. clear. intros x y. destruct (Z_le_dec x y); [img_try (left)|img_try (right)]; assumption. Qed.
Lemma zlt_dec : forall x y : Z, x < y \/ ~ (x < y).
Proof. clear. intros x y. destruct (Z_lt_dec x y); [img_try (left)|img_try (right)]; assumption. Qed.
Lemma XC_dec : forall NC MU MF (uq fq : bool) a, XC NC MU MF uq fq a \/ ~ XC NC MU MF uq fq a.
Proof.
clear. intros NC MU MF uq fq a. unfold YF8d.XC, YF8d.W_FEn, W_UW, W_USH, W_FW, W_FSH.
repeat first [img_apply zr_dec | img_apply or_dec | img_apply and_dec | img_apply beq_dec | img_apply zeq_dec | img_apply zle_dec | img_apply zlt_dec].
Qed.
Lemma LEAF_std : forall (NC MU MF : Z) (TOPS : list Z) (FL : list fseg) (HO : list (Z * Z)) (uq fq : bool)
(Wd : world tfxsegs) (mdf : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (v cnt nfv auv : Z) W' c',
at_RET3 Wd v mdf X (fun m => P m /\ P_cells Wd cnt nfv MF auv MU m) W' c' ->
v = (if (length TOPS =? 0)%nat then 0 else 1) -> cnt = Z.of_nat (length TOPS) -> nfv = nf + NC - cnt -> auv = au + NC * csz ->
(forall m, P m -> PF Wd NC MU MF TOPS m) ->
(forall a, X a -> (sp0 - RSTACK <= a < sp0) \/ XC NC MU MF uq fq a) ->
(forall x : word, ~ XC NC MU MF uq fq (bv_unsigned x) -> w_H Wd x = w_H W x) ->
hsub (w_H Wd) (w_H W) -> wle W Wd -> A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20 -> (forall i, In i (w_A W) -> In i (w_A Wd))   -> same_io md0 mdf -> amwf mdf ->
ALedger tfxsegs ly (SG NC MU MF TOPS FL HO) mdf -> Wf (as_universe B) (SG NC MU MF TOPS FL HO) ->
0 <= NC < 2 ^ 16 -> (uq = true -> mu < tot /\ mu2 <= kFreeArrayOffset) -> (fq = true -> mf2 <= kFreeArrayMax) ->
(MU = mu /\ NC * csz <= mu - au) \/ (MU = mu2 /\ uq = true /\ NC * csz <= mu2 - au) ->
MF = mf \/ (MF = mf2 /\ fq = true) -> 4 * (nf + NC) <= MF ->
(TOPS = [] /\ NC = 0) \/ (Z.of_nat (length TOPS) = n /\ need <= NC) ->
run_elems au csz (Z.to_nat NC) ++ fa_elems csz fr = TOPS ++ fa_elems csz FL -> runs_ok FL -> fa_len FL = nf + NC - Z.of_nat (length TOPS) ->
LEAFQ (tt, SG NC MU MF TOPS FL HO) W' c'.
Proof.
intros NC MU MF TOPS FL HO uq fq Wd mdf X P v cnt nfv auv W' c' HRET Ev Ecnt Enfv Eauv HPF HX HVIS HSUB LE HBUD HINC IO HMW HL WFG HNC HUQ HFQ HMU HMF HNF HNT E_elems E_runs E_rest.
destruct HRET as (EW & regs' & mem' & mat & Ec & R10 & RCS & MEQ0 & PRS & HP & PC).
pose proof (HPF mem' HP) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
pose proof (geo NC MU MF TOPS HNC uq fq HUQ HFQ HMU HMF HNT) as GE. pose proof derived_rangesR as DR. pose proof high_factsR as (Y1 & Y2 & Y3 & Y4 & Y5 & _).
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _ & _ & _ & _ & G15 & _ & _ & _ & _ & _ & _ & _ & _ & G24 & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
pose proof (proj1 HAR) as MA.
assert (MEQ : forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) -> ~ XC NC MU MF uq fq (bv_unsigned x) -> mem' x = mem0 x).
{ intros x N1 N2. img_apply MEQ0. intros Hx. destruct (HX _ Hx) as [H|H]; [img_try (img_exact (N1 H)) | img_try (img_exact (N2 H))]. }
assert (FAP : forall a, FAv <= a < FAv + MF -> apresent (w_H Wd) mem' a).
{ intros a Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [L|L]; [img_try (img_apply F1; clear - Ha L; zlia)|].
destruct HMF as [EM|[EM _]]; [img_try (exfalso; clear - Ha L EM; zlia)|]. img_apply (F5 EM). clear - Ha L EM G24 G33; unfold kFreeArrayMapSize in *; zlia. }
assert (UWP : MU = mu2 -> forall a, RBv <= a < RBv + mu2 -> apresent (w_H Wd) mem' a).
{ intros EM a Ha. destruct (Z_lt_le_dec a (RBv + mu)) as [L|L].
-
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (ASp (region_off c), mu)
ltac:(img_try (unfold aareas; img_apply in_app_iff; left; img_apply in_flat_map; exists c; split; [img_try (img_apply In_zseq; clear - HcR; zlia) | img_try (left; rewrite <- Hmu_def; img_refl)]))
(a - RBv) ltac:(img_try (cbn [snd]; clear - Ha L; zlia))) as RV.
cbn [fst aeval] in RV. replace (ly_space ly + region_off c + (a - RBv)) with a in RV by (img_try (rewrite RBv_is; unfold region_base; clear; zlia)).
assert (Ra : TFX_IMG_END <= a < 2 ^ 64) by (img_try (clear - Ha L Q1 Q2 Y3 Y5 GE; numconst; zlia)).
destruct (aview_high_apresent _ _ _ Ra RV) as [Hh [b Hb]].
assert (NX : ~ XC NC MU MF uq fq a) by (img_try (img_apply (Z_user NC MU MF TOPS HNC uq fq HUQ HFQ HMU HMF HNF HNT c mu a HcR); [img_try (clear - GE; zlia) | img_try (rewrite <- Hmu_def; clear; zlia) | img_try (rewrite <- RBv_is; clear - Ha L; zlia)])).
assert (NS : ~ (sp0 - RSTACK <= a < sp0)).
{ intros Hs. pose proof high_factsR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NOSTK). destruct Hsp as (S1 & S3 & _).
img_apply (proj2 (NOSTK a ltac:(img_try (clear - Hs S1 S3; unfold RSTACK in *; zlia)))). clear - Ha L Q1 Q2 GE; numconst; zlia. }
split.
+ rewrite (HVIS (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by (clear - Ra; numconst; zlia); img_exact NX)). img_exact Hh.
+ exists b. rewrite (MEQ (Z_to_bv 64 a)); [img_try (img_exact Hb) | |]; rewrite unsigned_lit_small by (img_try (clear - Ra; numconst; zlia)); [img_try (img_exact NS) | img_try (img_exact NX)].
- img_apply (F3 EM). clear - Ha L GE; zlia. }
assert (NOREM : forall x : word, mem0 x <> None -> mem' x <> None \/ (MU = mu /\ uq = true /\ W_UW (bv_unsigned x)) \/ (MF = mf /\ fq = true /\ W_FW (bv_unsigned x))).
{ intros x Hx0.
assert (PRES : forall a, apresent (w_H Wd) mem' a -> bv_unsigned x = a -> mem' x <> None).
{ clear. intros a [_ [b Hb]] <-. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
destruct (zrange_dec (sp0 - RSTACK) sp0 (bv_unsigned x)) as [Ds|Ds]; [img_try (left; img_exact (PRES _ (PRS _ Ds) ltac:(img_eqrefl)))|].
destruct (XC_dec NC MU MF uq fq (bv_unsigned x)) as [Dx|Dx]; [| img_try (left; rewrite (MEQ x Ds Dx); img_exact Hx0)].
pose proof PC as [PRW _].
unfold YF8d.XC, YF8d.W_FEn in Dx.
destruct Dx as [D|[D|[D|[D|[D|[D|[[EQ D]|[[EM D]|[[EQ D]|[EM D]]]]]]]]]].
+ left. img_apply (PRES _ (PRW _ (or_introl D)) ltac:(img_eqrefl)).
+ left. img_apply (PRES _ (F2 _ D) ltac:(img_eqrefl)).
+ left. apply (PRES _ (PRW _ (or_intror (or_introl D))) ltac:(img_eqrefl)).
+ left. apply (PRES _ (PRW _ (or_intror (or_intror (or_introl D)))) ltac:(img_eqrefl)).
+ left. apply (PRES _ (PRW _ (or_intror (or_intror (or_intror D)))) ltac:(img_eqrefl)).
+ left. img_apply (PRES (bv_unsigned x) (FAP (bv_unsigned x) ltac:(img_try (unfold YF8d.NF' in D; pose proof Hnf as [F0 _]; clear - D HNF F0; zlia))) ltac:(img_eqrefl)).
+ destruct HMU as [[EM _]|(EM & _ & _)]; [img_try (right; left; img_exact (conj EM (conj EQ D)))|]. left. img_apply (PRES (bv_unsigned x) (UWP EM (bv_unsigned x) ltac:(img_try (unfold W_UW in D; clear - D GE; zlia))) ltac:(img_eqrefl)).
+ left. destruct (F4 EM x D) as [V _]. rewrite V. discriminate.
+ destruct HMF as [EM|[EM _]]; [img_try (right; right; img_exact (conj EM (conj EQ D)))|]. left. img_apply (PRES (bv_unsigned x) (F5 EM (bv_unsigned x) ltac:(img_try (unfold W_FW in D; img_exact D))) ltac:(img_eqrefl)).
+ left. destruct (F6 EM x D) as [V _]. rewrite V. discriminate. }
assert (VISLOC : forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
0 <= aeval B ly (fst r) + i < 2 ^ 64 /\ (ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize -> prim_committed_at ly S (aeval B ly (fst r) + i))).
{ intros r i Hr Hi. split; [img_try (img_exact (VIS64 r i Hr Hi))|]. img_apply (vis_lists_committed B ly S _ MA); [|img_try (img_exact Hr)|img_try (img_exact Hi)].
intros r' Hr'. destruct (ts_junk B TS ly r' Hr') as (z & E & Z1 & Z2). exists z. split; [img_try (img_exact E)|]. unfold kImgEnd. clear - Z1 Z2. zlia. }
assert (PC' : P_cells Wd (NT TOPS) (NF' NC - NT TOPS) MF (AU NC) MU mem').
{ unfold YF8d.NT, YF8d.NF', YF8d.AU. rewrite <- Ecnt, <- Eauv. replace (nf + NC - cnt) with nfv by (img_try (clear - Enfv; zlia)). img_exact PC. }
rewrite EW. unfold LEAFQ.
img_apply (LEAF_G NC MU MF TOPS FL HO Wd mdf regs' mem' mat WFG HNC uq fq HUQ HFQ HMU HMF
ltac:(img_try (unfold YF8d.NF'; img_exact HNF)) ltac:(img_try (unfold YF8d.NT; img_exact HNT)) E_elems E_runs
ltac:(img_try (unfold YF8d.NF', YF8d.NT; img_exact E_rest)) HSUB HBUD HINC Hslack HL HMW MEQ HVIS NOREM PRS FAP F2 UWP PC'
ltac:(img_try (unfold YF8d.NT, YF8d.NF'; img_exact F8)) ltac:(img_try (unfold YF8d.NF'; img_exact F7)) F4 F6 VISLOC Wd c' P Ec ltac:(img_eqrefl));
[img_try (rewrite <- Ev; img_exact R10) | img_try (img_exact RCS) | img_try (img_exact LE) | img_try (img_exact IO)].
Qed.
Definition LEAFW : unit * astate -> world tfxsegs -> config -> Prop :=
fun r W' c' => (exists ns' : bool, Wf (as_universe B) (snd r)) -> LEAFQ r W' c'.
Lemma amreal_ask : forall (q : kreq) (sN : astate) (Kc : Z -> itree astate (unit * astate)) (Wx : world tfxsegs) (cx : config)
(Q : unit * astate -> world tfxsegs -> config -> Prop),
match q with KDepot _ => False | _ => True end ->
SRr tfxsegs Wx cx (fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfxsegs c1 I (fun _ => []) nx /\
(forall i, AI tfxsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfxsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(refusable q = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AI tfxsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizesM tfxsegs false (nx i) t_nil) /\
(forall i, (sp i = true \/ bit i <> 1) -> fo_dead tfxsegs c1 (nx i)) /\
(forall i, sp i = false -> if Z.eqb (bit i) 1 then amreal tfxsegs (Kc (bit i)) W1 (nx i) Q else amrealE tfxsegs (Kc (bit i)) W1 (nx i) Q)) ->
amreal tfxsegs (IAsk q sN Kc) Wx cx Q.
Proof. clear. intros q sN Kc Wx cx Q Hq H. destruct q; try (destruct Hq); cbn [amreal]; img_exact H. Qed.
Lemma pairwise_In_any {A0 : Type} : forall (R : A0 -> A0 -> Prop) (l : list A0) x y, pairwise R l -> In x l -> In y l -> x = y \/ R x y \/ R y x.
Proof.
clear. intros R l. induction l as [|z l IH]; intros x y P Hx Hy; [img_try (destruct Hx)|]. cbn in P. destruct P as [F P].
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [img_try (left; img_refl) | img_try (right; left; img_exact (proj1 (Forall_forall _ _) F y Hy)) | img_try (right; right; img_exact (proj1 (Forall_forall _ _) F x Hx)) | img_try (img_exact (IH x y P Hx Hy))].
Qed.
Lemma SEPS_of : forall md, amwf md -> forall e1 e2, In e1 (vm_maps (m_vmmaps md)) -> In e2 (vm_maps (m_vmmaps md)) ->
e1 = e2 \/ uw (fst e1) + uw (snd e1) <= uw (fst e2) \/ uw (fst e2) + uw (snd e2) <= uw (fst e1).
Proof.
clear. intros md [(_ & _ & _ & PW & _) _] e1 e2 H1 H2. unfold uw.     destruct (pairwise_In_any _ _ e1 e2 PW H1 H2) as [E|[X|X]]; [img_try (left; img_exact E) | img_try (right; img_exact X) | img_try (right; clear - X; zlia)].
Qed.
Definition cs_NU {imgk : img} : list YQ0b.chunk := match nth_error (ss_mem R3_NU) 0 with Some r => YQ0b.r_chunks r | None => [] end.
Lemma NU_facts : ss_pc R3_NU = (0x64c88 + D_2c4) /\ sr_get (ss_regs R3_NU) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NU) 10%bv = SOff rADR 0 /\ sv_atoms_lt aHAV3 (SOff rADR 0) = true /\
sr_get (ss_regs R3_NU) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NU) 12%bv = SLit 3 /\ sr_get (ss_regs R3_NU) 13%bv = SLit 50 /\
sr_get (ss_regs R3_NU) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NU) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NU) = true /\ nth_error (ss_mem R3_NU) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NU) /\
map skel (tl (ss_mem R3_NU)) = SKEL_TAILR /\
resume R3_NU (SLit ENOMEM_RET) (ss_mem R3_NU) (ss_facts R3_NU) = R3_NUr /\ resume R3_NU (SOff rADR 0) (ss_mem R3_NU) (ss_facts R3_NU) = R3_NUg.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Definition cs_NFe {imgk : img} : list YQ0b.chunk := match nth_error (ss_mem R3_NFe) 0 with Some r => YQ0b.r_chunks r | None => [] end.
Lemma NFe_facts : ss_pc R3_NFe = (0x64c88 + D_2c4) /\ sr_get (ss_regs R3_NFe) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NFe) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NFe) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NFe) 12%bv = SLit 3 /\ sr_get (ss_regs R3_NFe) 13%bv = SLit 50 /\
sr_get (ss_regs R3_NFe) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NFe) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NFe) = true /\ nth_error (ss_mem R3_NFe) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NFe) /\
map skel (tl (ss_mem R3_NFe)) = SKEL_TAILR /\
resume R3_NFe (SLit ENOMEM_RET) (ss_mem R3_NFe) (ss_facts R3_NFe) = R3_NFer /\ resume R3_NFe (SOff rFADR 0) (ss_mem R3_NFe) (ss_facts R3_NFe) = R3_NFeg.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Definition cs_NFg {imgk : img} : list YQ0b.chunk := match nth_error (ss_mem R3_NFg) 0 with Some r => YQ0b.r_chunks r | None => [] end.
Lemma NFg_facts : ss_pc R3_NFg = (0x64c88 + D_2c4) /\ sr_get (ss_regs R3_NFg) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NFg) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NFg) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NFg) 12%bv = SLit 3 /\ sr_get (ss_regs R3_NFg) 13%bv = SLit 50 /\
sr_get (ss_regs R3_NFg) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NFg) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NFg) = true /\ nth_error (ss_mem R3_NFg) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NFg) /\
map skel (tl (ss_mem R3_NFg)) = SKEL_TAILR /\
resume R3_NFg (SLit ENOMEM_RET) (ss_mem R3_NFg) (ss_facts R3_NFg) = R3_NFgr /\ resume R3_NFg (SOff rFADR 0) (ss_mem R3_NFg) (ss_facts R3_NFg) = R3_NFgg.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma U_adr : U E0 (SOff rADR 0) = adr.
Proof. pose proof facts3 as (_ & _ & _ & _ & _ & G6 & G7 & _). pose proof derived_rangesR as DR. unfold rADR. img_apply (U_atom E0 57 adr EaADR). clear - G6 G7 DR. numconst. unfold kUserMapSize in *. zlia. Qed.
Lemma U_fadr : U E0 (SOff rFADR 0) = fadr.
Proof. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G31 & G32 & _). pose proof derived_rangesR as DR. unfold rFADR. img_apply (U_atom E0 64 fadr EaFADR). clear - G31 G32 DR. numconst. unfold kFreeArrayMapSize in *. zlia. Qed.
Lemma band_not_WINR0 : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ WINR0 a.
Proof.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _).
pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof class_facts as (_ & _ & Kn & _).
unfold WINR0 in Hw. clear - Ha Hw DR TH T7 S1 HcR Kn. numconst. unfold Pr, t_cache in *. try unfold T in *. unfold RSTACK in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; zlia.
Qed.
Lemma H0sh_of : forall sh x0, x0 mod 8 = 0 -> region_base ly c <= x0 -> x0 + 262144 <= region_base ly c + 2 ^ 32 -> sh = SHBv + x0 / 8 ->
kHighShadowBeg <= sh -> sh + 32768 <= kHighShadowEnd -> forall a, SHR sh a -> mem0 (w64 a) <> None.
Proof.
intros sh x0 Hx8 Hlo Hhi Hsh B1 B2 a Ha. pose proof HAR as (MA & _ & _ & _ & [HS0 _]). unfold SHR in Ha.
apply Z.mod_divide in Hx8 as [q Hq]; [|img_try (clear; zlia)].
set (x := (q + (a - sh)) * 8).
assert (Ex : shadow_addr x = a).
{ unfold shadow_addr. (subst x; cbv beta). rewrite Z.div_mul by (img_try (clear; zlia)). rewrite Hq, Z.div_mul in Hsh by (img_try (clear; zlia)). unfold SHBv in Hsh. unfold SHADOW_OFF. clear - Hsh; zlia. }
assert (Rx : region_base ly c <= x < region_base ly c + 2 ^ 32) by (img_try ((subst x; cbv beta); clear - Hlo Hhi Ha Hq; zlia)).
rewrite <- Ex. img_apply (HS0 (shadow_addr x)); [img_try (rewrite Ex; clear - Ha B1 B2; zlia) | img_try (img_exact (prim_shadow_not_client B ly S _ c x MA HcR Rx)) | img_try (right; img_exact (prim_shadow_not_vis0 ly c x LY HcR Rx))].
Qed.
Definition zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}. Proof. clear. decide equality; img_apply Z.eq_dec. Defined.
Definition holeU : bool := if in_dec zz_eq_dec (mu, kUserMapSize) hol then true else false.
Definition holeF (xg : bool) : bool := if in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) (HO1 xg) then true else false.
Lemma K3U_p : YG0j.SUp S c = SUp.
Proof. unfold YG0j.SUp, YG0j.rUp, YG0j.offU, YF8a.SUp, YF8a.rUp. rewrite reg_S. cbn. rewrite Hmu2. img_refl. Qed.

Lemma K3U_addr : YG0j.addrU ly S c = adr.
Proof. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _). unfold YG0j.addrU, YG0j.offU. rewrite <- Hmu_def, <- RBv_is. symmetry. img_exact G10. Qed.
Lemma K3F_p : forall xg : bool, YG0j.SFp (St1 xg) c = SFp xg.
Proof. intros xg. unfold YG0j.SFp, YG0j.rFp, YG0j.offF, YF8a.SFp, YF8a.rFp. rewrite reg_S1, S1_eq, upd_reg_upd_reg. unfold rg1. cbn. rewrite Hmf2. img_refl. Qed.

Lemma K3F_addr : forall xg : bool, YG0j.addrF ly (St1 xg) c = fadr.
Proof. intros xg. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G24 & _). unfold YG0j.addrF, YG0j.offF. rewrite reg_S1, <- RBv_is. unfold rg1. cbn [rg_mapped_fa]. rewrite G24. unfold FAv. clear. zlia. Qed.
Lemma place_F : forall (xg : bool) (pp : Z) (mdN : Model), mf + kFreeArrayMapSize <= kFreeArrayMax ->
WfP (as_universe B) pp 0 0 (St1 xg) -> ALedger tfxsegs ly (St1 xg) mdN -> (forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) ->
if holeF xg then region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 fadr) (w64 kUserMapSize) = true
else region_free (vm_reserved (m_vmmaps mdN)) (w64 fadr) (w64 kUserMapSize) = true /\ map_contains (vm_maps (m_vmmaps mdN)) (w64 fadr) (w64 kUserMapSize) = true.
Proof.
intros xg pp mdN Ymax WP L NZ. pose proof (proj1 HAR) as MA.
assert (HFA : rg_mapped_fa (reg (St1 xg) c) + kUserMapSize <= kFreeArrayMax) by (img_try (rewrite reg_S1; unfold rg1; cbn; img_exact Ymax)).
assert (PL : sec_placed ly (St1 xg)) by (img_try (rewrite S1_eq; unfold sec_placed; rewrite (YG0j.sec_extents_upd ly S c); img_exact (am_placed _ _ _ _ MA))).
unfold holeF. destruct (in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) (HO1 xg)) as [Hin|Hnin].
- pose proof (ALedger_fa_place_hole tfxsegs (as_universe B) pp 0 0 ly (St1 xg) mdN c LY WP HcR L HFA ltac:(img_try (unfold YG0j.offF; rewrite reg_S1; unfold rg1; cbn; img_exact Hin)) PL NZ) as X.
rewrite K3F_addr in X. img_exact X.
- pose proof (ALedger_fa_place_piece tfxsegs (as_universe B) pp 0 0 ly (St1 xg) mdN c LY WP HcR L HFA ltac:(img_try (unfold YG0j.offF; rewrite reg_S1; unfold rg1; cbn; img_exact Hnin))) as X.
rewrite K3F_addr in X. img_exact X.
Qed.
Lemma COV_prim : forall (hole : bool) (addr : Z) (mdN : Model), amwf mdN ->
ly_prim ly <= addr -> addr + kUserMapSize <= ly_prim ly + kPrimResvSize ->
forall x, ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize) ->
YK0h.covered (vm_noaccess (m_vmmaps (grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN)) ++ m_vm_lazy (grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN)) x
= YK0h.covered (vm_noaccess (m_vmmaps mdN) ++ m_vm_lazy mdN) x.
Proof.
clear - LY. intros hole addr mdN [(A1 & A2 & A3 & _ & A5) _] H1 H2 x Hx.
pose proof (lo_high ly LY) as HI. destruct HI as [HP1 HP2].
assert (U1 : bv_unsigned (w64 addr) = addr) by (img_try (unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [img_refl | img_try (ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, bv_modulus, kHighMemBeg, ASAN_CEIL, kPrimResvSize, kUserMapSize in *; zlia)])).
assert (U2 : bv_unsigned (w64 kUserMapSize) = kUserMapSize) by (img_try (unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [img_refl | img_try (unfold bv_modulus, kUserMapSize; zlia)])).
img_apply (YG0l.cov_grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN x).
- unfold YK0h.model_ivs_wf. split; [|img_try (split; [|split; [|img_exact A5]])]; intros q Hq; [img_try (img_exact (A1 q Hq)) | img_try (img_exact (A2 q Hq)) | img_try (img_exact (A3 q Hq))].
- rewrite U1, U2. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPrimResvSize, kUserMapSize in *. zlia.
- rewrite U1, U2. intros Hin. img_apply Hx. zlia.
Qed.
Lemma ledger_F_grant : forall (xg : bool) (pp : Z) (mdN : Model), mf + kFreeArrayMapSize <= kFreeArrayMax ->
WfP (as_universe B) pp 0 0 (St1 xg) -> ALedger tfxsegs ly (St1 xg) mdN -> amwf mdN   ->
eager_used (grant_md (holeF xg) FL50 (w64 fadr) (w64 kUserMapSize) mdN) <= eager_used mdN + kUserMapSize ->
ALedger tfxsegs ly (SFp xg) (grant_md (holeF xg) FL50 (w64 fadr) (w64 kUserMapSize) mdN).
Proof.
intros xg pp mdN Ymax WP L MWN EG. rewrite <- K3F_p.
assert (HFA : rg_mapped_fa (reg (St1 xg) c) + kUserMapSize <= kFreeArrayMax) by (img_try (rewrite reg_S1; unfold rg1; cbn; img_exact Ymax)).
assert (PL : sec_placed ly (St1 xg)) by (img_try (rewrite S1_eq; unfold sec_placed; rewrite (YG0j.sec_extents_upd ly S c); img_exact (am_placed _ _ _ _ (proj1 HAR)))).
pose proof (YG0j.prim_boundsF (as_universe B) pp 0 0 ly (St1 xg) c LY WP HcR HFA) as (PB1 & PB2 & PB3 & PB4 & PB5). rewrite K3F_addr in PB3.
assert (PB6 : region_base ly c <= fadr) by (img_try (rewrite <- (K3F_addr xg); unfold YG0j.addrF; clear - PB5; unfold kFreeArrayOffset in *; zlia)).
pose proof (COV_prim (holeF xg) fadr mdN MWN ltac:(img_try (clear - PB2 PB6; zlia)) ltac:(img_try (clear - PB3 PB4; zlia))) as COV.
unfold holeF in *. destruct (in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) (HO1 xg)) as [Hin|Hnin].
- pose proof (grant_hole_shape (w64 fadr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
img_apply (ALedger_fa_granted_hole tfxsegs (as_universe B) pp 0 0 ly (St1 xg) mdN _ c LY WP HcR L RES LIM ISP PL COV (YG0i.naf_grant_md _ _ mdN _ _ MWN) HFA ltac:(img_try (unfold YG0j.offF; rewrite reg_S1; unfold rg1; cbn; img_exact Hin))); [|img_try (img_exact EG)].
rewrite K3F_addr. unfold wiv. cbn [fst snd]. img_exact VM.
- pose proof (grant_piece_shape (w64 fadr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
img_apply (ALedger_fa_granted_piece tfxsegs (as_universe B) pp 0 0 ly (St1 xg) mdN _ c WP HcR L RES LIM ISP PL COV (YG0i.naf_grant_md _ _ mdN _ _ MWN) ltac:(img_try (unfold YG0j.offF; rewrite reg_S1; unfold rg1; cbn; img_exact Hnin)) VM EG).
Qed.
Lemma WfP_SUp : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset -> WfP (as_universe B) 0 0 0 SUp.
Proof.
intros HC HR3. pose proof (WF1 (proj1 Hpum)) as W1P. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof class_facts as (_ & _ & K3 & K4 & _).
pose proof (map_more_user_ok (as_universe B) 1 0 0 S c need true W1P HcR (Z.le_refl 1) ltac:(img_try (rewrite <- Hcsz; clear - G1 G3 K4; nia)) (proj1 ROOM3)  ) as AT.
destruct (E_mmu_g HC HR3) as (K & EK & K1 & _). rewrite EK in AT. cbn [atok] in AT. destruct AT as [_ AT].
specialize (AT 1 ltac:(img_try (right; img_refl))). rewrite K1 in AT. cbn [atok] in AT. destruct AT as (r1 & _ & W1 & _). img_exact W1.
Qed.

Lemma place_U : forall mdN : Model, ALedger tfxsegs ly S mdN -> (forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) ->
if holeU then region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 adr) (w64 kUserMapSize) = true
else region_free (vm_reserved (m_vmmaps mdN)) (w64 adr) (w64 kUserMapSize) = true /\ map_contains (vm_maps (m_vmmaps mdN)) (w64 adr) (w64 kUserMapSize) = true.
Proof.
intros mdN L NZ. pose proof (proj1 HAR) as MA. pose proof (WF1 (proj1 Hpum)) as W1P.
unfold holeU. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol) as [Hin|Hnin].
- pose proof (ALedger_user_place_hole tfxsegs (as_universe B) 1 0 0 ly S mdN c LY W1P HcR L ltac:(img_try (unfold YG0j.offU; rewrite reg_S; cbn; img_exact Hin)) (am_placed _ _ _ _ MA) NZ) as X.
rewrite K3U_addr in X. img_exact X.
- pose proof (ALedger_user_place_piece tfxsegs (as_universe B) 1 0 0 ly S mdN c LY W1P HcR L ltac:(img_try (unfold YG0j.offU; rewrite reg_S; cbn; img_exact Hnin))) as X.
rewrite K3U_addr in X. img_exact X.
Qed.
Lemma ledger_U_grant : forall mdN : Model, ALedger tfxsegs ly S mdN -> amwf mdN   ->
eager_used (grant_md holeU FL50 (w64 adr) (w64 kUserMapSize) mdN) <= eager_used mdN + kUserMapSize ->
ALedger tfxsegs ly SUp (grant_md holeU FL50 (w64 adr) (w64 kUserMapSize) mdN).
Proof.
intros mdN L MWN EG. rewrite <- K3U_p. pose proof (WF1 (proj1 Hpum)) as W1P.
pose proof (am_placed _ _ _ _ (proj1 HAR)) as PL.
pose proof (YG0j.prim_bounds (as_universe B) 1 0 0 ly S c LY W1P HcR) as (PB1 & PB2 & PB3 & PB4 & PB5). rewrite K3U_addr in PB3.
assert (PB6 : region_base ly c <= adr) by (img_try (rewrite <- K3U_addr; unfold YG0j.addrU; clear - PB5; zlia)).
pose proof (COV_prim holeU adr mdN MWN ltac:(img_try (clear - PB2 PB6; zlia)) ltac:(img_try (clear - PB3 PB4; unfold kFreeArrayOffset, kFreeArrayMax, kPrimResvSize in *; zlia))) as COV.
unfold holeU in *. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol) as [Hin|Hnin].
- pose proof (grant_hole_shape (w64 adr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
img_apply (ALedger_user_granted_hole tfxsegs (as_universe B) 1 0 0 ly S mdN _ c LY W1P HcR L RES LIM ISP PL COV (YG0i.naf_grant_md _ _ mdN _ _ MWN) ltac:(img_try (unfold YG0j.offU; rewrite reg_S; cbn; img_exact Hin))); [|img_try (img_exact EG)].
rewrite K3U_addr. unfold wiv. cbn [fst snd]. img_exact VM.
- pose proof (grant_piece_shape (w64 adr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
img_apply (ALedger_user_granted_piece tfxsegs (as_universe B) 1 0 0 ly S mdN _ c W1P HcR L RES LIM ISP PL COV (YG0i.naf_grant_md _ _ mdN _ _ MWN) ltac:(img_try (unfold YG0j.offU; rewrite reg_S; cbn; img_exact Hnin)) VM EG).
Qed.
Lemma slack_at : forall md (Wx : world tfxsegs) k, ALedger tfxsegs ly S md0 -> vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) ->
eager_used md <= eager_used md0 + k -> A_bytes (w_A Wx) <= A_bytes (w_A W) + k -> 0 <= k <= 2 ^ 20 ->
eager_used md + A_bytes (w_A Wx) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md).
Proof.
intros md Wx k L LIM EG AB Hk. pose proof (vm_budget_slack _ S WF (proj2 (proj2 Hpum)) Hql) as VB. unfold VM_SLACK in VB.   pose proof (al_eager _ _ _ _ _ WF L) as AE  . pose proof (al_limit _ _ _ _ L) as AL.
rewrite LIM, AL. clear - VB AE EG AB Hk Hslack. unfold EV_A, kUserMapSize in *. zlia.
Qed.
Definition cs_NR {imgk : img} : list YQ0b.chunk := match nth_error (ss_mem R3_NR) 0 with Some r => YQ0b.r_chunks r | None => [] end.
Lemma NR_facts : ss_pc R3_NR = (0x64c88 + D_2c4) /\ sr_get (ss_regs R3_NR) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NR) 10%bv = SOff rADR 0 /\ sv_atoms_lt aHAV3 (SOff rADR 0) = true /\
sr_get (ss_regs R3_NR) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NR) 12%bv = SLit 0 /\ sr_get (ss_regs R3_NR) 13%bv = SLit 0x104022 /\
sr_get (ss_regs R3_NR) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NR) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NR) = true /\ nth_error (ss_mem R3_NR) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NR) /\
map skel (tl (ss_mem R3_NR)) = SKEL_TAILR /\
resume R3_NR (SLit ENOMEM_RET) (ss_mem R3_NR) (ss_facts R3_NR) = R3_NRe /\ resume R3_NR (SLit EEXIST_RET) (ss_mem R3_NR) (ss_facts R3_NR) = R3_NRx /\
resume R3_NR (SOff rADR 0) (ss_mem R3_NR) (ss_facts R3_NR) = R3_NRg.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Definition cs_NRFe {imgk : img} : list YQ0b.chunk := match nth_error (ss_mem R3_NRFe) 0 with Some r => YQ0b.r_chunks r | None => [] end.
Lemma NRFe_facts : ss_pc R3_NRFe = (0x64c88 + D_2c4) /\ sr_get (ss_regs R3_NRFe) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NRFe) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NRFe) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NRFe) 12%bv = SLit 0 /\ sr_get (ss_regs R3_NRFe) 13%bv = SLit 0x104022 /\
sr_get (ss_regs R3_NRFe) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NRFe) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NRFe) = true /\ nth_error (ss_mem R3_NRFe) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NRFe) /\
map skel (tl (ss_mem R3_NRFe)) = SKEL_TAILR /\
resume R3_NRFe (SLit ENOMEM_RET) (ss_mem R3_NRFe) (ss_facts R3_NRFe) = R3_NRFee /\ resume R3_NRFe (SLit EEXIST_RET) (ss_mem R3_NRFe) (ss_facts R3_NRFe) = R3_NRFex /\
resume R3_NRFe (SOff rFADR 0) (ss_mem R3_NRFe) (ss_facts R3_NRFe) = R3_NRFeg.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Definition cs_NRFg {imgk : img} : list YQ0b.chunk := match nth_error (ss_mem R3_NRFg) 0 with Some r => YQ0b.r_chunks r | None => [] end.
Lemma NRFg_facts : ss_pc R3_NRFg = (0x64c88 + D_2c4) /\ sr_get (ss_regs R3_NRFg) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NRFg) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NRFg) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NRFg) 12%bv = SLit 0 /\ sr_get (ss_regs R3_NRFg) 13%bv = SLit 0x104022 /\
sr_get (ss_regs R3_NRFg) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NRFg) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NRFg) = true /\ nth_error (ss_mem R3_NRFg) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NRFg) /\
map skel (tl (ss_mem R3_NRFg)) = SKEL_TAILR /\
resume R3_NRFg (SLit ENOMEM_RET) (ss_mem R3_NRFg) (ss_facts R3_NRFg) = R3_NRFge /\ resume R3_NRFg (SLit EEXIST_RET) (ss_mem R3_NRFg) (ss_facts R3_NRFg) = R3_NRFgx /\
resume R3_NRFg (SOff rFADR 0) (ss_mem R3_NRFg) (ss_facts R3_NRFg) = R3_NRFgg.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma hol_nil : hol = [].
Proof. unfold YF8a.hol. img_exact (wf_noholes _ _ _ _ S c (WF1 (proj1 Hpum)) HcR). Qed.
Lemma holeU_false : holeU = false.
Proof. unfold holeU. rewrite hol_nil. destruct (in_dec zz_eq_dec (mu, kUserMapSize) []) as [[]|]; img_refl. Qed.
Lemma holeF_false : forall xg : bool, holeF xg = false.
Proof.
intros xg. unfold holeF, YF8a.HO1. rewrite hol_nil. destruct xg; cbn [del_hole List.filter];
(destruct (in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) []) as [[]|]; img_refl).
Qed.
Definition same_led (md md' : Model) : Prop := m_vmmaps md' = m_vmmaps md /\ m_vm_lazy md' = m_vm_lazy md.
Lemma occupied_of_place : forall (mdN mdK : Model) (a : Z), same_led mdN mdK ->
map_contains (vm_maps (m_vmmaps mdN)) (w64 a) (w64 kUserMapSize) = true ->
region_free (vm_reserved (m_vmmaps mdK) ++ vm_maps (m_vmmaps mdK)) (w64 a) (w64 kUserMapSize) = false.
Proof.
clear. intros mdN mdK a [E _] MC. rewrite E. img_apply kept_occupied; [| img_try (img_exact MC)].
unfold w64. rewrite unsigned_lit_small; unfold kUserMapSize; zlia.
Qed.
Lemma free_of_destroyed : forall (mdN mdD : Model) (a : Z), YN05.ceil_of_top (alloc_top (m_vmmaps mdN)) ->
0 <= a -> a + kUserMapSize <= alloc_ceiling ->
same_led (fixedin_destroyed_model (w64 a) (w64 kUserMapSize) mdN) mdD ->
region_free (vm_reserved (m_vmmaps mdN)) (w64 a) (w64 kUserMapSize) = true ->
region_free (vm_reserved (m_vmmaps mdD) ++ vm_maps (m_vmmaps mdD)) (w64 a) (w64 kUserMapSize) = true /\
alloc_top (m_vmmaps mdD) = alloc_top (m_vmmaps mdN).
Proof.
clear. intros mdN mdD a HTOP Ha Hceil [E _] RF. rewrite E.
pose proof (YN05.ceil_le_top _ HTOP) as CT.
pose proof (alloc_top_room (m_vmmaps mdN)) as Hcv. unfold two_pow_64, stack_max_size in Hcv.
assert (Ua : bv_unsigned (w64 a) = a) by (img_try (unfold w64; img_apply unsigned_lit_small; unfold kUserMapSize in *; zlia)).
img_exact (destroyed_free (w64 a) 262144 mdN ltac:(img_try (zlia)) ltac:(img_try (rewrite Ua; img_change (page_round_up_Z 262144) with 262144; unfold kUserMapSize in Hceil; zlia)) RF).
Qed.
Lemma ledger_restored : forall (S' : astate) (pp : Z) (lo : Z) (mdN mdD : Model),
WfP (as_universe B) pp 0 0 S' -> sec_placed ly S' -> ALedger tfxsegs ly S' mdN -> amwf mdN ->
(ly_prim ly <= lo /\ lo < lo + kUserMapSize /\ lo + kUserMapSize <= ly_prim ly + kPrimResvSize) ->
cut_ok ly S' lo -> cut_ok ly S' (lo + kUserMapSize) -> (forall x, cut_ok ly S' x -> ~ (lo < x < lo + kUserMapSize)) -> lo mod 4096 = 0 ->
same_led (fixedin_destroyed_model (w64 lo) (w64 kUserMapSize) mdN) mdD ->
eager_used (restore_md FLR (w64 lo) (w64 kUserMapSize) mdD) <= eager_used mdN ->
ALedger tfxsegs ly S' (restore_md FLR (w64 lo) (w64 kUserMapSize) mdD).
Proof.
intros S' pp lo mdN mdD WP PL L MWN WIN CUTlo CUThi NOCUT LOAL [EV EL] EG.
pose proof (lo_high ly LY) as HP. unfold in_high in HP. cbn [fst snd] in HP. pose proof (YG0j.prim_hi ly LY) as [C1 C2].
assert (Ulo : bv_unsigned (w64 lo) = lo) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - WIN HP C1 C2; unfold kHighMemBeg, kUserMapSize in *; zlia)).
assert (Un : bv_unsigned (w64 kUserMapSize) = kUserMapSize) by (img_try (unfold w64; img_apply unsigned_lit_small; unfold kUserMapSize; clear; zlia)).
destruct (destroyed_shape (w64 lo) (w64 kUserMapSize) mdN) as (DM & DN & DR & DL & DB & DS & DLz & _). rewrite Ulo, Un in DM, DN, DLz.
destruct (restore_shape FLR (w64 lo) (w64 kUserMapSize) mdD) as (RM & RN & RR & RL & RB & RS & _ & RLz). rewrite noresR in RLz.
assert (LI : lazy_interior (w64 lo) (w64 kUserMapSize) = [(w64 lo, w64 kUserMapSize)]).
{ img_apply lazy_interior_aligned; rewrite ?Ulo, ?Un; unfold page_size;
first [img_exact LOAL | unfold kUserMapSize; img_refl | clear - WIN C1 C2; unfold kUserMapSize in *; zlia]. }
rewrite LI in RLz. cbn [app] in RLz. rewrite EV in RM, RN, RR, RL, RS. rewrite EL in RLz.
destruct MWN as [(A1 & A2 & A3 & PW & A5) NZ].
assert (W64 : wiv (lo, lo + kUserMapSize - lo) = (w64 lo, w64 kUserMapSize)) by (img_try (unfold wiv; cbn [fst snd]; replace (lo + kUserMapSize - lo) with kUserMapSize by (clear; zlia); img_refl)).
apply (ALedger_restored tfxsegs (as_universe B) pp 0 0 ly S' mdN _ LY WP L) with (lo := lo) (hi := lo + kUserMapSize).
- rewrite RR, DR. img_refl.
- rewrite RL, DL. img_refl.
- rewrite RS, DS. img_refl.
- img_exact PL.
- img_exact WIN.
- img_exact CUTlo.
- img_exact CUThi.
- img_exact NOCUT.
- intros e He. unfold uw. img_exact (NZ e He).
- img_exact (SEPS_of mdN (conj (conj A1 (conj A2 (conj A3 (conj PW A5)))) NZ)).
- img_exact A2.
- rewrite RM, DM, W64. img_refl.
- rewrite RN, DN, W64. img_refl.
-
intros x Hx. rewrite RN, RLz, DN, DLz.
assert (NR : YK0h.in_rng lo (lo + kUserMapSize) x = false).
{ unfold YK0h.in_rng. img_apply andb_false_iff. destruct (Z_lt_le_dec x lo); [img_try (left; img_apply Z.leb_gt; assumption) | img_try (right; img_apply Z.ltb_ge; clear - WIN Hx l; zlia)]. }
destruct (YK0h.maps_subtract_sem (vm_noaccess (m_vmmaps mdN)) lo (lo + kUserMapSize) ltac:(img_try (intros q Hq; img_exact (A2 q Hq))) ltac:(img_try (unfold kUserMapSize; clear; zlia))) as (_ & _ & Cn).
destruct (YK0h.maps_subtract_sem (m_vm_lazy mdN) lo (lo + kUserMapSize) ltac:(img_try (intros q Hq; img_exact (A3 q Hq))) ltac:(img_try (unfold kUserMapSize; clear; zlia))) as (_ & _ & Cl).
rewrite !YK0h.covered_app.
change (YK0h.covered ((w64 lo, w64 kUserMapSize) :: ?l) x) with (YK0h.in_iv (w64 lo, w64 kUserMapSize) x || YK0h.covered l x).
assert (IV : YK0h.in_iv (w64 lo, w64 kUserMapSize) x = false) by (img_try (unfold YK0h.in_iv, YK0h.B, YK0h.S; cbn [fst snd]; rewrite Ulo, Un; img_exact NR)).
unfold YK0h.covered at 1 3. cbn [existsb]. rewrite IV. cbn [orb].
fold (YK0h.covered (maps_subtract (vm_noaccess (m_vmmaps mdN)) lo (lo + kUserMapSize)) x). fold (YK0h.covered (maps_subtract (m_vm_lazy mdN) lo (lo + kUserMapSize)) x).
rewrite Cn, Cl, NR. cbn [negb]. rewrite !andb_true_r. img_refl.
- img_exact EG.
Qed.
Lemma LEAF_fail : forall (MU : Z) (HO : list (Z * Z)) (uq fq : bool) (Wd : world tfxsegs) mdf X P W' c' (s' : astate),
s' = SG 0 MU mf [] fr HO ->
at_RET3 Wd 0 mdf X (fun m => P m /\ P_cells Wd 0 nf mf au MU m) W' c' ->
(forall m, P m -> PF Wd 0 MU mf [] m) ->
(forall a, X a -> (sp0 - RSTACK <= a < sp0) \/ XC 0 MU mf uq fq a) ->
(forall x : word, ~ XC 0 MU mf uq fq (bv_unsigned x) -> w_H Wd x = w_H W x) ->
hsub (w_H Wd) (w_H W) -> wle W Wd -> A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20 -> (forall i, In i (w_A W) -> In i (w_A Wd))   -> same_io md0 mdf -> amwf mdf ->
ALedger tfxsegs ly s' mdf -> (MU = mu \/ (MU = mu2 /\ uq = true)) ->
(uq = true -> mu < tot /\ mu2 <= kFreeArrayOffset) -> (fq = true -> mf2 <= kFreeArrayMax) ->
LEAFW (tt, s') W' c'.
Proof.
intros MU HO uq fq Wd mdf X P W' c' s' -> HRET HPF HX HVIS HSUB LE HBUD HINC IO HMW HL HMU HUQ HFQ [ns' WFQ]. cbn [snd] in WFQ.
pose proof Hnf as [F0 F1]. pose proof Hmu as ([U0 U1] & _). pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _).
img_apply (LEAF_std 0 MU mf [] fr HO uq fq Wd mdf X P 0 0 nf au W' c' HRET); try assumption.
- img_refl.
- img_refl.
- clear; zlia.
- clear; zlia.
- clear; zlia.
- destruct HMU as [EM|[EM EQ]]; [img_try (left; split; [img_exact EM | clear - U0 U1; zlia]) | img_try (right; split; [img_exact EM | split; [img_exact EQ | rewrite G15; clear - U0 U1; unfold kUserMapSize; zlia]])].
- left. img_refl.
- clear - F1; zlia.
- left. split; img_refl.
- img_refl.
- unfold fr. img_exact (wr_runs _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c HcR)).
- unfold fr. rewrite <- Hnf_def. cbn. clear; zlia.
Qed.
Lemma SG_S : SG 0 mu mf [] fr hol = S.
Proof.
pose proof len_facts3 as (L1 & L2 & L3). unfold YF8d.SG, YF8d.rG, YF8d.AU. cbn [rev]. rewrite Z.mul_0_l, Z.add_0_r.
rewrite <- reg_S. rewrite upd_reg_same by (img_try ((clear - HcR; zlia) || (rewrite L1; img_exact L3))).
rewrite <- PM3. rewrite <- Hchunks. replace (mkPC (pc_max (cache S c)) (pc_chunks (cache S c))) with (cache S c) by (img_try (destruct (cache S c); img_refl)).
img_apply upd_pc_same; [img_try (clear - HcR; zlia) | img_try (rewrite L2; img_exact L3)].
Qed.
Lemma SG_upd : forall MU HO, SG 0 MU mf [] fr HO = upd_reg c (mkRegion MU au mf fr HO) S.
Proof.
intros MU HO. pose proof len_facts3 as (L1 & L2 & L3). unfold YF8d.SG, YF8d.rG, YF8d.AU. cbn [rev]. rewrite Z.mul_0_l, Z.add_0_r.
rewrite <- PM3. rewrite <- Hchunks. replace (mkPC (pc_max (cache S c)) (pc_chunks (cache S c))) with (cache S c) by (img_try (destruct (cache S c); img_refl)).
img_change (cache S c) with (cache (upd_reg c (mkRegion MU au mf fr HO) S) c).
img_apply upd_pc_same; [img_try (clear - HcR; zlia) | img_try (unfold upd_reg; cbn; rewrite L2; img_exact L3)].
Qed.
Lemma SQ_SG : forall (xg yg : bool) tops rest, XC3 xg -> SQ xg yg tops rest = SG (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg).
Proof.
intros xg yg tops rest XC. pose proof (factsX3 xg XC) as (_ & _ & N3 & _).
unfold SQ, YF8d.SG, rQ, YF8d.rG, YF8d.AU. rewrite N3. img_refl.
Qed.
Lemma SG_ledger : forall (xg yg : bool) tops rest md, XC3 xg ->
ALedger tfxsegs ly (St2 xg yg) md -> ALedger tfxsegs ly (SG (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg)) md.
Proof.
intros xg yg tops rest md XC L. pose proof len_facts3 as (L1 & L2 & L3).
pose proof (SG_parts (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg)) as (Rreg & Rc & _ & _ & _ & Rch & _).
img_apply (ALedger_shape (St2 xg yg)); [| | | | | img_try (rewrite S2_eq; img_refl) | img_try (img_exact L)].
- intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite Rc, reg_S2. unfold YF8d.rG, rg2. cbn. repeat split; img_refl.
+ rewrite (Rreg c') by (img_try (clear - Hc' NE; zlia)). rewrite S2_eq. unfold upd_reg, reg. cbn [st_regions set_regions].
rewrite znth_zupd_other; [img_try (repeat split; img_refl) | img_try (clear - HcR; zlia) | img_try (clear - Hc'; zlia) | img_try (congruence)].
- rewrite S2_eq. img_refl.
- rewrite S2_eq. img_refl.
- rewrite S2_eq. unfold YF8d.SG, upd_pc, upd_reg.
match goal with |- prim_committed (set_cache ?x ?st) = _ => img_change (prim_committed (set_cache x st)) with (prim_committed st) end.
rewrite !prim_committed_set_region by (img_try ((clear - HcR; zlia) || (rewrite L1; img_exact L3))). unfold YF8d.rG, rg2. cbn [rg_mapped_user rg_mapped_fa]. img_refl.
- rewrite S2_eq. img_refl.
Qed.
Lemma LEAF_arm : forall (xg yg : bool) tops rest (Wd : world tfxsegs) mdf X (P : (word -> option byte) -> Prop) W' c',
XC3 xg -> (yg = true -> mf < 4 * NF1 xg /\ mf2 <= kFreeArrayMax) -> (yg = false -> 4 * NF1 xg <= mf) ->
fa_pop_n 10000 csz n (FRun au (NC1 xg) :: fr) [] = Some (tops, rest) ->
at_RET3 Wd 1 mdf X (fun m => P m /\ P_cells Wd n (NF1 xg - n) (MF2 yg) (AU1 xg) (MU1 xg) m) W' c' ->
(forall m, P m -> PF Wd (NC1 xg) (MU1 xg) (MF2 yg) tops m) ->
(forall a, X a -> (sp0 - RSTACK <= a < sp0) \/ XC (NC1 xg) (MU1 xg) (MF2 yg) xg yg a) ->
(forall x : word, ~ XC (NC1 xg) (MU1 xg) (MF2 yg) xg yg (bv_unsigned x) -> w_H Wd x = w_H W x) ->
hsub (w_H Wd) (w_H W) -> wle W Wd -> A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20 -> (forall i, In i (w_A W) -> In i (w_A Wd))   -> same_io md0 mdf -> amwf mdf ->
ALedger tfxsegs ly (St2 xg yg) mdf ->
LEAFW (tt, SQ xg yg tops rest) W' c'.
Proof.
intros xg yg tops rest Wd mdf X P W' c' XC Yg Ye EP HRET HPF HX HVIS HSUB LE HBUD HINC IO HMW HL [ns' WFQ]. cbn [snd] in WFQ.
pose proof (factsX3 xg XC) as ([N0 N1] & N2 & N3 & N4 & NN & N6 & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct (fa_pop_n_spec 10000 csz n _ [] tops rest (runs_ok_new xg XC) ltac:(img_try (clear - K3; zlia)) EP) as (Eel & Erest & Eruns & Elen). cbn [rev app length Z.of_nat] in Eel, Elen.
rewrite (SQ_SG xg yg tops rest XC) in WFQ |- *.
assert (Elen' : Z.of_nat (length tops) = n) by (img_try (clear - Elen; zlia)).
img_apply (LEAF_std (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg) xg yg Wd mdf X P 1 n (NF1 xg - n) (AU1 xg) W' c' HRET).
- destruct (length tops); [img_try (exfalso; clear - Elen' K3; cbn in Elen'; zlia) | img_refl].
- symmetry. img_exact Elen'.
- rewrite N2. clear - Elen'; zlia.
- img_exact N3.
- img_exact HPF.
- img_exact HX.
- img_exact HVIS.
- img_exact HSUB.
- img_exact LE.
- img_exact HBUD.
- img_exact HINC.
- img_exact IO.
- img_exact HMW.
- img_exact (SG_ledger xg yg tops rest mdf XC HL).
- img_exact WFQ.
- img_exact (conj N0 N1).
- intros ->. unfold XC3 in XC. rewrite G15. img_exact XC.
- intros ->. img_exact (proj2 (Yg ltac:(img_eqrefl))).
- destruct xg; [img_try (right; split; [img_refl | split; [img_refl | img_exact (proj1 N4)]]) | img_try (left; split; [img_refl | img_exact (proj1 N4)])].
- destruct yg; [img_try (right; split; img_refl) | img_try (left; img_refl)].
- rewrite <- N2. destruct yg; cbn [MF2]; [| img_try (img_exact (Ye ltac:(img_eqrefl)))]. destruct (Yg ltac:(img_eqrefl)) as [Y1 Y2]. rewrite G33. rewrite N2 in Y1 |- *. unfold kFreeArrayMapSize. clear - Y1 N1 F1; zlia.
- right. img_exact (conj Elen' NN).
- rewrite <- fa_elems_cons_run. img_exact Eel.
- img_exact Eruns.
- rewrite Elen', <- N2. cbn [fa_len] in Erest. unfold fr in Erest |- *. rewrite <- Hnf_def in Erest. clear - Erest N2; zlia.
Qed.
Definition P1 (Wx : world tfxsegs) : (word -> option byte) -> Prop :=
fun m => (forall a, FAv <= a < FAv + mf -> apresent (w_H Wx) m a) /\ (forall a, DSTv <= a < DSTv + 64 -> apresent (w_H Wx) m a).
Lemma P1_of_frame : forall (Wx : world tfxsegs) (m : word -> option byte),
hsub (w_H Wx) (w_H W) -> (forall x : word, ~ WINR0 (bv_unsigned x) -> m x = mem0 x) -> P1 Wx m.
Proof.
intros Wx m Hs MEQ. pose proof derived_rangesR as DR. pose proof Hmf as [[M0 M1] _]. pose proof high_factsR as (F1' & F2 & _).
assert (G : forall a, 0 <= a < 2 ^ 64 -> ~ WINR0 a -> apresent (w_H W) mem0 a -> apresent (w_H Wx) m a).
{ intros a Ra Hw [Hh Hb]. split.
- destruct (w_H Wx (Z_to_bv 64 a)) eqn:E; [|img_refl]. rewrite (Hs _ E) in Hh. discriminate Hh.
- rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_exact Ra; img_exact Hw)). img_exact Hb. }
split.
- intros a Ha. img_apply G; [img_try (clear - Ha DR M0 M1; numconst; unfold kFreeArrayMax in *; zlia) | img_try (img_apply fa_not_WINR0; clear - Ha M1; unfold kFreeArrayMax in *; zlia) | img_try (img_exact (HfaPres a Ha))].
- intros a Ha. img_apply G; [img_try (clear - Ha DR F2; numconst; zlia) | img_try (img_apply slots_not_WINR0; img_exact Ha) | img_try (img_exact (HslotPres a Ha))].
Qed.
Lemma P1_mono : forall (Wx : world tfxsegs) (m m' : word -> option byte),
(forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P1 Wx m -> P1 Wx m'.
Proof. clear. intros Wx m m' Hm [PA PB]. split; intros a Ha; img_apply Hm; auto. Qed.
Lemma P1_frame : forall (Wx : world tfxsegs) (R : Z -> Prop) (m m' : word -> option byte),
(forall x : word, ~ R (bv_unsigned x) -> m' x = m x) ->
(forall a, FAv <= a < FAv + mf -> ~ R a) -> (forall a, DSTv <= a < DSTv + 64 -> ~ R a) -> P1 Wx m -> P1 Wx m'.
Proof.
intros Wx R m m' Hfr HA HB [PA PB]. pose proof derived_rangesR as DR. pose proof Hmf as [[M0 M1] _]. pose proof high_factsR as (F1' & F2 & _).
split; intros a Ha.
- eapply apresent_same; [|img_try (img_exact (PA a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by (img_try (clear - Ha DR M0 M1; numconst; unfold kFreeArrayMax in *; zlia)). img_exact (HA a Ha).
- eapply apresent_same; [|img_try (img_exact (PB a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by (img_try (clear - Ha DR F2; numconst; zlia)). img_exact (HB a Ha).
Qed.
Lemma pstable_P1 : forall Wx : world tfxsegs, pstable (P1 Wx).
Proof.
intros Wx m m' Hfr HP. pose proof Hmf as [[M0 M1] _].
img_apply (P1_frame Wx WINR0 m m' Hfr); [img_try (intros a Ha; img_apply fa_not_WINR0; clear - Ha M1; unfold kFreeArrayMax in *; zlia) | img_try (intros a Ha; img_apply slots_not_WINR0; img_exact Ha) | img_try (img_exact HP)].
Qed.
Theorem refill_B3_ee : tot <= mu -> 4 * nfe <= mf -> amreal tfxsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
intros Xe Ye.
assert (XC : XC3 false) by img_exact Xe.
destruct (pop_new false XC) as (tops & rest & EP & Eel & Erest & Eruns & Elen).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. rewrite (E_mmu_e Xe). cbn [ibind negb].
destruct (E_getreg1 false S XC reg_e) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
unfold bind at 1. rewrite (E_efa_e false S XC reg_e Ye). cbn [ibind negb].
destruct (E_tail false false S tops rest XC reg_ee upd_e EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
eapply SRr_bind; [img_try (img_exact seg3P)|]. intros W1 c1 _ HR1.
eapply SRr_bind; [img_try (img_exact (seg3Q_ok Xe W1 c1 HR1))|]. intros W2 c2 _ HR2.
eapply SRr_bind; [img_try (img_exact (segC1_e Xe W md0 WINR0 PT W2 c2 WX0 pstable_PT HR2))|]. intros W3 c3 _ HR3.
eapply SRr_bind; [img_try (img_exact (segC2e_e Xe Ye W md0 WINR0 PT W3 c3 WX0 pstable_PT HR3))|]. intros W4 c4 _ HR4.
apply (at_R3_strengthen W md0 WINR0 PT (P1 W)) in HR4; [| img_try (intros m MEQ _ _; img_exact (P1_of_frame W m (hsub_refl _) MEQ))].
pose proof (factsX3 false XC) as ([N0 N1] & N2 & _ & _ & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _).
assert (YC : if false then mf < 4 * NF1 false /\ mf2 <= kFreeArrayMax else 4 * NF1 false <= mf) by img_exact Ye.
eapply SRr_bind.
{ img_apply (segE1_ee Xe Ye W md0 WINR0 (P1 W) W4 c4 WX0 (pstable_P1 W)); [| | img_try (img_exact HR4)].
- intros m [PA _] a Ha. img_apply PA. unfold W_FE in Ha. cbn [NF1] in Ye. clear - Ha Ye F0; zlia.
- intros m m' _ Hm. img_exact (P1_mono W m m' Hm). }
intros W5 c5 _ HR5.
eapply SRr_bind; [img_try (img_exact (segE2_ee Xe Ye W md0 _ _ W5 c5 (fun a (Ha : WINR0 a) => (or_introl Ha : WINR0 a \/ W_FE (NF1 false) a)) (pstable_fill_ee Xe Ye W (P1 W) (pstable_P1 W)) HR5))|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ apply (segE3_ee Xe Ye W md0 _ _ W6 c6 (fun a (Ha : WINR0 a) => (or_introl Ha : WINR0 a \/ W_FE (NF1 false) a)) (pstable_fill_ee Xe Ye W (P1 W) (pstable_P1 W))); [| | | img_try (img_exact HR6)].
- intros m [[PA _] _] a Ha. img_apply PA. unfold SRC3_ee in Ha. cbn [NF1] in Ye, N2, N7. clear - Ha Ye F0 N2 N0 N7 K3 Hneed; zlia.
- intros m [[_ PB] _] a Ha. img_apply PB. unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [HPm HV]. split; [img_try (img_exact (P1_mono W m m' Hm HPm))|].
intros i Hi. img_apply (val_mem_frame_ee (w_H W) m m'); [|img_try (img_exact (HV i Hi))]. intros t Ht. img_apply Hfr. unfold W_DST.
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _). pose proof Hmf as [[M0 M1] _].
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (img_try (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR; numconst; unfold kFreeArrayMax in *; zlia)).
unfold DSTv, Pr in *. cbn [NF1] in Ye. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR Ye. numconst. unfold kFreeArrayMax in *. try unfold T in *. try unfold SB in *. zlia. }
intros W7 c7 _ HR7.
eapply SRr_mono; [img_try (img_exact (segE4_ee Xe Ye W md0 _ _ W7 c7 (fun a (Ha : WINR0 a) => or_introl (or_introl Ha : WINR0 a \/ W_FE (NF1 false) a) : (WINR0 a \/ W_FE (NF1 false) a) \/ W_DST a) (pstable_cpy_ee Xe Ye _ (pstable_fill_ee Xe Ye W (P1 W) (pstable_P1 W))) HR7))|].
intros W' c' _ HRET.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _ & _ & _ & _ & _ & _ & G22 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
img_apply (LEAF_arm false false tops rest W md0 _ _ W' c' XC ltac:(img_try (intros E; discriminate E)) (fun _ => Ye) EP HRET).
-
intros m [[[PA PB] PFI] PCP]. cbn [NC1 MU1 MF2].
split; [img_try (img_exact PA)|]. split; [img_try (img_exact PB)|]. split; [img_try (intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia)|]. split; [img_try (intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia)|].
split; [img_try (intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia)|]. split; [img_try (intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia)|].
split.
+ intros i Hi. replace (nf + nce) with nfe by (img_try (clear - G22; zlia)). img_exact (PFI i Hi).
+ intros j Hj. rewrite Elen in Hj |- *. replace (nf + nce - n) with (nfe - n) by (img_try (clear - G22; zlia)). img_exact (PCP j Hj).
-
intros a [[Hw|Hw]|Hw]; unfold YF8d.XC, YF8d.W_FEn, YF8d.NF'; cbn [NC1 MU1 MF2].
+ unfold WINR0 in Hw. clear - Hw. tauto.
+ right. do 5 right. left. unfold W_FE in Hw. rewrite <- G22. img_exact Hw.
+ right. right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
- intros x _. img_refl.
- img_apply hsub_refl.
- img_apply wle_refl.
- clear. zlia.
- intros i Hi; img_exact Hi.
- img_apply same_io_refl.
- img_exact (proj1 (proj2 (proj2 (proj2 HAR)))).
- cbn [St2 St1]. img_exact (proj1 (proj2 HAR)).
Qed.
Lemma P1_hmono : forall (Wx Wy : world tfxsegs) (m : word -> option byte),
(forall y, w_H Wx y = false -> w_H Wy y = false) -> P1 Wx m -> P1 Wy m.
Proof. clear. intros Wx Wy m Hm [PA PB]. split; intros a Ha; [img_try (img_exact (apresent_hmono _ _ m a Hm (PA a Ha))) | img_try (img_exact (apresent_hmono _ _ m a Hm (PB a Ha)))]. Qed.
Lemma pres_keepW : forall (Wx Wy : world tfxsegs) (m m' : word -> option byte) a,
(forall y, w_H Wx y = false -> w_H Wy y = false) -> (apresent (w_H Wy) m a -> apresent (w_H Wy) m' a) -> apresent (w_H Wx) m a -> apresent (w_H Wx) m' a.
Proof. clear. intros Wx Wy m m' a Hm Hp [Hh Hb]. destruct (Hp (conj (Hm _ Hh) Hb)) as [_ Hb']. img_exact (conj Hh Hb'). Qed.
Definition P_pres {imgk : img} (W3 : world tfxsegs) (addr sh : Z) (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ (forall a, RANGE addr a -> apresent (w_H W3) m a) /\ (forall a, SHR sh a -> apresent (w_H W3) m a).
Lemma P_grant_pres : forall W3 addr sh P m, P_grant W3 addr sh P m -> P_pres W3 addr sh P m.
Proof. clear. intros W3 addr sh P m (HP & HG1 & HG2). split; [img_try (img_exact HP)|]. split; [img_try (intros a Ha; img_exact (proj1 (HG1 a Ha))) | img_try (img_exact HG2)]. Qed.
Lemma P_pres_keep : forall (W5 : world tfxsegs) addr sh (m m' : word -> option byte),
(forall y, w_H W y = false -> w_H W5 y = false) ->
(forall a, apresent (w_H W5) m a -> apresent (w_H W5) m' a) ->
P_pres W5 addr sh (P1 W) m -> P_pres W5 addr sh (P1 W) m'.
Proof.
clear. intros W5 addr sh m m' MON Hm (HP & HG1 & HG2). split; [|img_try (split)].
- img_exact (P1_mono W m m' (fun a Ha' => pres_keepW W W5 m m' a MON (Hm a) Ha') HP).
- intros a Ha. img_exact (Hm a (HG1 a Ha)).
- intros a Ha. img_exact (Hm a (HG2 a Ha)).
Qed.
Lemma PF_fail : forall (Wd : world tfxsegs) (m : word -> option byte) (MU : Z),
P1 Wd m ->
(MU = mu2 -> (forall a, adr <= a < adr + kUserMapSize -> apresent (w_H Wd) m a) /\ (forall x : word, W_USH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250) /\ w_H Wd x = false)) ->
PF Wd 0 MU mf [] m.
Proof.
intros Wd m MU [PA PB] HU. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold PF. split; [img_try (img_exact PA)|]. split; [img_try (img_exact PB)|]. split; [img_try (intros E; img_exact (proj1 (HU E)))|]. split; [img_try (intros E; img_exact (proj2 (HU E)))|].
split; [img_try (intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia)|]. split; [img_try (intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia)|].
split; [img_try (intros i Hi; exfalso; clear - Hi; zlia)|]. intros j Hj. exfalso. clear - Hj. cbn in Hj. zlia.
Qed.
Theorem refill_B3_eg : tot <= mu -> mf < 4 * nfe -> mf + kFreeArrayMapSize <= kFreeArrayMax -> amreal tfxsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
intros Xe Ylt Ymax.
assert (XC : XC3 false) by img_exact Xe.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _ & _ & _ & _ & _ & _ & G22 & _ & G24 & G25 & _ & G27 & G28 & G29 & G30 & _ & _ & G33 & _).
pose proof (factsX3 false XC) as ([N0 N1] & N2 & _ & _ & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _). pose proof Hmf as [[M0 M1] _].
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2. pose proof derived_rangesR as DR.
assert (Ymax2 : mf2 <= kFreeArrayMax) by (img_try (rewrite G33; img_exact Ymax)).
assert (Ylt' : mf < 4 * NF1 false) by img_exact Ylt.
pose proof HAR as (MA & L & BUD & MW & HS0).
destruct (pop_new false XC) as (tops & rest & EP & Eel & Erest & Eruns & Elen).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. rewrite (E_mmu_e Xe). cbn [ibind negb].
destruct (E_getreg1 false S XC reg_e) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
unfold bind at 1. destruct (E_efa_g false S XC reg_e upd_e Ylt' Ymax2) as (K & EK & K1 & K2 & K0). rewrite EK. cbn [ibind negb].
img_apply amreal_ask; [img_try (img_exact I)|].
eapply SRr_bind; [img_try (img_exact seg3P)|]. intros W1 c1 _ HR1.
eapply SRr_bind; [img_try (img_exact (seg3Q_ok Xe W1 c1 HR1))|]. intros W2 c2 _ HR2.
apply (at_R3_strengthen W md0 WINR0 PT (P1 W)) in HR2; [| img_try (intros m MEQ _ _; img_exact (P1_of_frame W m (hsub_refl _) MEQ))].
eapply SRr_bind; [img_try (img_exact (segC1_e Xe W md0 WINR0 (P1 W) W2 c2 WX0 (pstable_P1 W) HR2))|]. intros W3 c3 _ HR3.
eapply SRr_mono; [img_try (img_exact (SRr_with_AI _ _ _ (segC2g_e Xe Ylt Ymax W md0 WINR0 (P1 W) W3 c3 WX0 (pstable_P1 W) HR3)))|].
intros W4 c4 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW4. (subst W4; cbv beta).
pose proof NFe_facts as (Fpc & F17 & F10 & Fea & F11 & F12 & F13 & F14 & F15 & Fnc & Fhd & Fsk & Fres_r & Fres_g).
destruct HN as (HNw & msN & matN & EN & EcN & HNrest).
set (mdN := with_vm_backing (m_vm_lazy md0) matN md0) in *.
assert (EcM : cfg_model c4 = mdN) by (img_try (rewrite EcN; img_refl)).
assert (LN : ALedger tfxsegs ly S mdN) by (img_try (img_exact (ALedger_same tfxsegs ly S md0 mdN L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)))).
assert (MWN : amwf mdN) by (img_try (img_exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW))).
assert (NZN : forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) by (img_try (intros e He; unfold uw; img_apply NZ0; unfold mdN in He; rewrite m_vmmaps_wvb in He; img_exact He)).
pose proof (WF1 (proj1 Hpum)) as W1P.
lazymatch goal with |- context [ibind (ibind (ibind (K _) ?g1) ?g2) ?g3] =>
eapply (node3 (KMapFreeArray c mf kFreeArrayMapSize) S (fun z => ibind (ibind (ibind (K z) g1) g2) g3) LEAFW W md0 WINR0 (P1 W) R3_NFe c4 (SOff rFADR 0) fadr shf (holeF false) cs_NFe
(conj HNw (ex_intro _ msN (ex_intro _ matN (ex_intro _ EN (conj EcN HNrest))))) HAI Fpc F17 F10 Fea U_fadr F11 F12 F13 F14 F15 Fnc Fhd Fsk) end.
- img_exact G25.
- clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia.
- clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
- img_exact G27.
- img_exact G28.
- unfold kHighShadowBeg; clear - G29; zlia.
- unfold kHighShadowEnd; clear - G30; zlia.
-   rewrite EcM. img_exact (place_F false 1 mdN Ymax W1P LN NZN).
- rewrite EcM. img_exact MWN.
-   rewrite EcM. img_exact (al_top _ _ _ _ LN).
- rewrite EcM. img_apply (slack_at mdN W 0 L); [img_try (unfold mdN; rewrite m_vmmaps_wvb; img_refl) | img_try (unfold mdN; rewrite eager_used_wvb; clear; zlia) | img_try (clear; zlia) | img_try (clear; zlia)].
- img_refl.
- intros z Hz. img_exact Hz.
-   intros m m' Hfr HP. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
img_apply (P1_frame W (RANGE fadr) m m' Hfr); [| | img_try (img_exact HP)]; intros a Ha; unfold RANGE.
+ clear - Ha G24; zlia.
+ unfold DSTv, Pr in Ha. clear - Ha G24 M0 G33 Ymax2 DR TP Q1 Q2 HcR. try unfold T in *. numconst. unfold kFreeArrayMapSize, kUserMapSize in *. zlia.
-   intros a Ha. img_apply band_not_WINR0. unfold SHR in Ha. clear - Ha G29 G30; numconst; zlia.
-   img_apply (H0sh_of shf fadr); [img_try (clear - G25; apply Z.mod_divide in G25 as [q Hq]; [|zlia]; rewrite Hq; img_apply Z.mod_divide; [zlia|]; exists (q * 8192); zlia)
| img_try (rewrite <- RBv_is; clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia) | img_try (rewrite <- RBv_is; clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *; zlia)
| img_try (img_exact G27) | img_try (unfold kHighShadowBeg; clear - G29; zlia) | img_try (unfold kHighShadowEnd; clear - G30; zlia)].
-   img_exact (holeF_false false).
-
intros cpk_q. rewrite EcM. intros HRk_q HAIk_q. rewrite Fres_r in HRk_q.
pose proof (place_F false 1 mdN Ymax W1P LN NZN) as PLk_q. rewrite (holeF_false false) in PLk_q.
img_apply (SRr_tnil tfxsegs W cpk_q _ (segD_r_e W mdN WINR0 (P1 W) W cpk_q WX0 (pstable_P1 W) HRk_q)); [| img_try (img_exact HAIk_q)].
intros Wk_q ck_q _ HNk_q HAIck_q. pose proof (proj1 HNk_q) as EWk_q. (subst Wk_q; cbv beta).
pose proof NRFe_facts as (Rpc_q & R17_q & R10_q & Rea_q & R11_q & R12_q & R13_q & R14_q & R15_q & Rnc_q & Rhd_q & Rsk_q & Rres_e_q & Rres_x_q & Rres_g_q).
destruct HNk_q as (HNwk_q & msRk_q & matRk_q & ERk_q & EcRk_q & HNrestk_q).
set (mdK_q := with_vm_backing (m_vm_lazy mdN) matRk_q mdN) in *.
assert (EcK_q : cfg_model ck_q = mdK_q) by (img_try (rewrite EcRk_q; img_refl)).
apply (node3k W mdN WINR0 (P1 W) R3_NRFe ck_q (SOff rFADR 0) fadr cs_NRFe (conj HNwk_q (ex_intro _ msRk_q (ex_intro _ matRk_q (ex_intro _ ERk_q (conj EcRk_q HNrestk_q))))) HAIck_q Rpc_q R17_q R10_q Rea_q U_fadr R11_q R12_q R13_q R14_q R15_q Rnc_q Rhd_q Rsk_q).
+ img_exact G25.
+ clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia.
+ clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
+ rewrite EcK_q. img_exact (occupied_of_place mdN mdK_q fadr (conj (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _)) (proj2 PLk_q)).
+ rewrite EcK_q. unfold mdK_q. rewrite m_vmmaps_wvb. img_exact (al_top _ _ _ _ LN).
+ intros c3_q. rewrite EcK_q, Rres_e_q. intros HR3_q HAI3_q. img_exact (segD_re_e W mdK_q WINR0 (P1 W) W c3_q WX0 (pstable_P1 W) HR3_q HAI3_q).
+ intros c3_q. rewrite EcK_q, Rres_x_q. intros HR3_q HAI3_q. img_exact (segD_rx_e W mdK_q WINR0 (P1 W) W c3_q WX0 (pstable_P1 W) HR3_q HAI3_q).
-
intros cpd_q. rewrite EcM. intros md3_q AI3_q MW3_q IO3_q EG3_q HRd_q. cbv beta. rewrite (K0 0 ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia))). cbn [ibind negb].
rewrite Fres_r in HRd_q.
pose proof (place_F false 1 mdN Ymax W1P LN NZN) as PLd_q. rewrite (holeF_false false) in PLd_q.
set (XD_q := fun a => WINR0 a \/ RANGE fadr a) in *.
assert (HXD_q : forall a, WINR0 a -> XD_q a) by (img_try (intros a Ha; left; img_exact Ha)).
assert (GEO3_q : fadr mod 65536 = 0 /\ RBv <= fadr /\ fadr + kUserMapSize <= RBv + 2 ^ 32).
{ split; [img_try (img_exact G25)|]. split; [img_try (clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia) | img_try (clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia)]. }
assert (HPuF_q : forall m m' : word -> option byte, (forall x : word, ~ RANGE fadr (bv_unsigned x) -> m' x = m x) -> P1 W m -> P1 W m').
{ intros m m' Hfr HP. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
img_apply (P1_frame W (RANGE fadr) m m' Hfr); [| | img_try (img_exact HP)]; intros a Ha; unfold RANGE.
+ clear - Ha G24; zlia.
+ unfold DSTv, Pr in Ha. clear - Ha G24 M0 G33 Ymax2 DR TP Q1 Q2 HcR. try unfold T in *. numconst. unfold kFreeArrayMapSize, kUserMapSize in *. zlia. }
eapply amrealE_SRr_pre; [img_try (img_apply SRr_F; img_exact (SRr_with_AI _ _ _ (segD_r_e W md3_q XD_q (P1 W) W cpd_q HXD_q (pstable_P1 W) HRd_q)))|].
intros Wd_q cd_q _ [HAId_q HNd_q]. pose proof (proj1 HNd_q) as EWd_q. (subst Wd_q; cbv beta).
pose proof NRFe_facts as (Rpc_q & R17_q & R10_q & Rea_q & R11_q & R12_q & R13_q & R14_q & R15_q & Rnc_q & Rhd_q & Rsk_q & Rres_e_q & Rres_x_q & Rres_g_q).
destruct HNd_q as (HNwd_q & msRd_q & matRd_q & ERd_q & EcRd_q & HNrestd_q).
set (mdD_q := with_vm_backing (m_vm_lazy md3_q) matRd_q md3_q) in *.
assert (EcD_q : cfg_model cd_q = mdD_q) by (img_try (rewrite EcRd_q; img_refl)).
assert (SLD_q : same_led md3_q mdD_q) by (img_try (split; unfold mdD_q; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb)])).
destruct (free_of_destroyed mdN mdD_q fadr (al_top _ _ _ _ LN)
ltac:(img_try (destruct GEO3_q as (_ & GA & GB); clear - GA GB DR; numconst; unfold kUserMapSize in *; zlia))
ltac:(img_try (destruct GEO3_q as (_ & GA & GB); clear - GA GB DR; numconst; unfold kUserMapSize in *; zlia))
SLD_q (proj1 PLd_q)) as [FREEd_q TOPd_q].
assert (DLIM_q : vm_limit (m_vmmaps md3_q) = vm_limit (m_vmmaps mdN)) by (img_try (img_exact (proj1 (proj2 (proj2 (proj2 (destroyed_shape (w64 fadr) (w64 kUserMapSize) mdN))))))).
eapply (node3r _ LEAFW W md3_q XD_q (P1 W) R3_NRFe cd_q (SOff rFADR 0) fadr cs_NRFe (conj HNwd_q (ex_intro _ msRd_q (ex_intro _ matRd_q (ex_intro _ ERd_q (conj EcRd_q HNrestd_q))))) HAId_q Rpc_q R17_q R10_q Rea_q U_fadr R11_q R12_q R13_q R14_q R15_q Rnc_q Rhd_q Rsk_q).
+ img_exact (proj1 GEO3_q).
+ img_exact (proj1 (proj2 GEO3_q)).
+ img_exact (proj2 (proj2 GEO3_q)).
+ rewrite EcD_q. img_exact FREEd_q.
+ rewrite EcD_q. img_exact (amwf_same md3_q mdD_q (proj1 SLD_q) (proj2 SLD_q) MW3_q).
+ rewrite EcD_q, TOPd_q. img_exact (al_top _ _ _ _ LN).
+ rewrite EcD_q. pose proof (slack_at mdN W 0 L ltac:(img_try (unfold mdN; rewrite m_vmmaps_wvb; img_refl)) ltac:(img_try (unfold mdN; rewrite eager_used_wvb; clear; zlia)) ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia))) as SLK_q.
unfold mdD_q. rewrite eager_used_wvb, m_vmmaps_wvb, DLIM_q. clear - SLK_q EG3_q. unfold kUserMapSize in *. zlia.
+ img_exact HPuF_q.
+ intros c3_q. rewrite EcD_q, Rres_e_q. intros HR3_q HAI3_q. img_exact (segD_re_e W mdD_q XD_q (P1 W) W c3_q HXD_q (pstable_P1 W) HR3_q HAI3_q).
+
intros W4_q c3_q. rewrite EcD_q. intros md4_q LE4_q A4_q SUB4_q MON4_q HEQ4_q AI4_q MW4_q IO4_q EG4_q AB4_q HR4_q. rewrite Rres_g_q in HR4_q. cbn [amrealE].
set (XG4_q := fun a => XD_q a \/ RANGE fadr a) in *.
assert (HXG4_q : forall a, WINR0 a -> XG4_q a) by (img_try (intros a Ha; left; left; img_exact Ha)).
eapply SRrF_mono; [img_try (img_apply SRr_F; img_exact (segD_rg_e W4_q md4_q XG4_q (P1 W) W4_q c3_q HXG4_q (pstable_P1 W) HR4_q))|]. intros W' c'' _ HRET.
unfold MUX_e in HRET.
img_apply (LEAF_fail mu hol false true W4_q md4_q XG4_q (P1 W) W' c'' S (eq_sym SG_S) HRET).
* intros m HPm. img_apply (PF_fail W4_q m mu (P1_hmono W W4_q m MON4_q HPm)). intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia.
* intros a [[Hw|Hw]|Hw]; unfold YF8d.XC; [img_try (unfold WINR0 in Hw; clear - Hw; tauto) | |];
(do 9 right; left; split; [img_refl | img_try (unfold W_FW, RANGE, kFreeArrayMapSize, kUserMapSize in *; img_exact Hw)]).
* intros x NX. img_apply HEQ4_q. intros Hw. img_apply NX. unfold YF8d.XC. do 8 right. left. split; [img_refl | img_try (unfold W_FW, RANGE, kFreeArrayMapSize, kUserMapSize in *; img_exact Hw)].
* img_exact SUB4_q.
* img_exact LE4_q.
* rewrite AB4_q. clear. unfold kUserMapSize. zlia.
* intros i Hi. rewrite A4_q. right. img_exact Hi.
* img_exact IO4_q.
* img_exact MW4_q.
*
assert (HFA_q : rg_mapped_fa (reg S c) + kUserMapSize <= kFreeArrayMax) by (img_try (rewrite reg_S; cbn; img_exact Ymax)).
destruct (fa_window (as_universe B) 1 0 0 ly S c LY W1P HcR HFA_q) as (WINw_q & CUTl_q & CUTh_q & NOCUTw_q).
pose proof (K3F_addr false) as KA_q. cbn [St1] in KA_q. rewrite KA_q in WINw_q, CUTl_q, CUTh_q, NOCUTw_q.
refine (ledger_restored S 1 fadr mdN mdD_q W1P (am_placed _ _ _ _ (proj1 HAR)) LN MWN WINw_q CUTl_q CUTh_q NOCUTw_q _ SLD_q _).
-- clear - G25. apply Z.mod_divide in G25 as [q Hq]; [|img_try (zlia)]. rewrite Hq. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q * 16). zlia.
-- eapply Z.le_trans; [img_try (img_exact EG4_q)|]. unfold mdD_q. rewrite eager_used_wvb. img_exact EG3_q.
* left; img_refl.
* intros E; discriminate E.
* intros _; img_exact Ymax2.
+   rewrite EcD_q. img_exact (same_io_trans _ _ _ IO3_q (same_io_with_vm_backing _ _ _)).
-
intros W5 c'. rewrite EcM. intros md2 LE5 A5 SUB5 MON5 AI5 MW5 IO5 EG5 HEQ5 AB5 HR. cbv beta. rewrite K1. cbn [ibind negb].
destruct (E_tail false true (SFp false) tops rest XC (reg_xg false) (upd_xg false) EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
rewrite Fres_g in HR.
assert (YC : 4 * nfe <= mf2) by (img_try (rewrite G33; rewrite G22; unfold kFreeArrayMapSize; clear - F1 N1 N0; cbn [NC1] in *; zlia)).
set (X5 := fun a => WINR0 a \/ RANGE fadr a) in *.
assert (HX5 : forall a, WINR0 a -> X5 a) by (img_try (intros a Ha; left; img_exact Ha)).
apply (at_R3_weaken W5 md2 X5 X5 _ (P_pres W5 fadr shf (P1 W))) in HR; [| img_try (intros a Ha; img_exact Ha) | img_try (intros m Hm; img_exact (P_grant_pres _ _ _ _ _ Hm))].
set (P5 := P_pres W5 fadr shf (P1 W)) in *.
pose proof high_factsR as (_ & _ & _ & _ & _ & Y6 & _). pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G31 & G32 & _).
assert (RNG : forall a, RANGE fadr a -> 0 <= a < 2 ^ 64 /\ FAv <= a < FAv + 2 ^ 29).
{ intros a Ha. unfold RANGE in Ha. clear - Ha G24 G31 G32 G33 Ymax2 M0 Q2 Y6. numconst. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayMax in *. zlia. }
assert (SNG : forall a, SHR shf a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg).
{ intros a Ha. unfold SHR in Ha. clear - Ha G29 G30. numconst. zlia. }
assert (PS5 : pstable P5).
{ intros m m' Hfr (HP & HG1 & HG2). split; [img_try (img_exact (pstable_P1 W m m' Hfr HP))|]. split.
- intros a Ha. destruct (RNG a Ha) as [Ra Fa]. eapply apresent_same; [|img_try (img_exact (HG1 a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra. img_apply fa_not_WINR0. img_exact Fa.
- intros a Ha. destruct (SNG a Ha) as [Ra Ba]. eapply apresent_same; [|img_try (img_exact (HG2 a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra. img_apply band_not_WINR0. img_exact Ba. }
eapply SRr_bind; [img_try (img_exact (segD_g_e W5 md2 X5 P5 W5 c' HX5 PS5 HR))|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ img_apply (segD_ms_e Xe W5 md2 X5 P5 W6 c6 HX5 PS5); [| | img_try (img_exact HR6)].
- intros m (_ & _ & HG2) a Ha. img_apply HG2. unfold SHR. unfold W_FSH in Ha. img_change (kFreeArrayMapSize / 8) with 32768 in Ha. img_exact Ha.
- intros m m' Hfr Hm HP. img_exact (P_pres_keep W5 fadr shf m m' MON5 Hm HP). }
intros W7 c7 _ HR7.
assert (YCg : YCOND_eg) by (img_try (split; [img_try (img_exact Ylt) | img_try (img_exact Ymax)])).
set (X7 := fun a => X5 a \/ W_FSH a) in *.
assert (HX7 : forall a, WINR0 a -> X7 a) by (img_try (intros a Ha; left; left; img_exact Ha)).
set (P7 := P_fsh_e P5) in *.
assert (PS7 : pstable P7) by img_exact (pstable_fsh_e P5 PS5).
eapply SRr_bind.
{ img_apply (segE1_eg Xe YCg W5 md2 X7 P7 W7 c7 HX7 PS7); [| | img_try (img_exact HR7)].
-
intros m ((HP & HG1 & HG2) & _) a Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ img_apply (apresent_hmono (w_H W) (w_H W5) m a MON5). img_apply (proj1 HP). unfold W_FE in Ha. clear - Ha Lo F0 F1; zlia.
+ img_apply (HG1 a). unfold RANGE. unfold W_FE in Ha. clear - Ha Hi YC G24 G33; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m m' Hfr Hm [HP HF]. split; [img_try (img_exact (P_pres_keep W5 fadr shf m m' MON5 Hm HP))|].
intros x Hx. rewrite (Hfr x); [img_try (img_exact (HF x Hx))|]. intros Hw. unfold W_FE in Hw. unfold W_FSH in Hx. img_change (kFreeArrayMapSize / 8) with 32768 in Hx.
clear - Hw Hx G29 G30 DR F0. numconst. zlia. }
intros W8 c8 _ HR8.
set (X8 := fun a => X7 a \/ W_FE nfe a) in *. set (P8 := P_fill_eg W5 P7) in *.
assert (HX8 : forall a, WINR0 a -> X8 a) by (img_try (intros a Ha; left; img_exact (HX7 a Ha))).
assert (PS8 : pstable P8) by img_exact (pstable_fill_eg Xe YCg W5 P7 PS7).
eapply SRr_bind; [img_try (img_exact (segE2_eg Xe YCg W5 md2 X8 P8 W8 c8 HX8 PS8 HR8))|]. intros W9 c9 _ HR9.
eapply SRr_bind.
{ img_apply (segE3_eg Xe YCg W5 md2 X8 P8 W9 c9 HX8 PS8); [| | | img_try (img_exact HR9)].
- intros m [[(HP & HG1 & HG2) _] _] a Ha. unfold SRC3_eg in Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ img_apply (apresent_hmono (w_H W) (w_H W5) m a MON5). img_apply (proj1 HP). clear - Ha Lo F0 F1 N2 N7 N0 K3 Hneed; cbn [NF1 NC1] in *; zlia.
+ img_apply (HG1 a). unfold RANGE. clear - Ha Hi YC G24 G33 K3; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m [[(HP & _ & _) _] _] a Ha. img_apply (apresent_hmono (w_H W) (w_H W5) m a MON5). img_apply (proj2 HP). unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [[HP HF] HV]. split; [img_try (split; [img_exact (P_pres_keep W5 fadr shf m m' MON5 Hm HP)|])|].
+ intros x Hx. rewrite (Hfr x); [img_try (img_exact (HF x Hx))|]. intros Hw. unfold W_DST in Hw. unfold W_FSH in Hx. img_change (kFreeArrayMapSize / 8) with 32768 in Hx.
pose proof high_factsR as (Fz & _). clear - Hw Hx G29 G30 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros i Hi. img_apply (val_mem_frame_eg (w_H W5) m m'); [|img_try (img_exact (HV i Hi))]. intros t Ht. img_apply Hfr. unfold W_DST.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _).
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (img_try (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR G33 Ymax2; numconst; unfold kFreeArrayMax, kFreeArrayMapSize in *; zlia)).
unfold DSTv, Pr in *. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR YC G33 Ymax2. numconst. unfold kFreeArrayMax, kFreeArrayMapSize in *. try unfold T in *. try unfold SB in *. zlia. }
intros W10 c10 _ HR10.
eapply SRr_mono; [img_try (img_exact (segE4_eg Xe YCg W5 md2 (fun a => X8 a \/ W_DST a) (P_cpy_eg P8) W10 c10 (fun a Ha => or_introl (HX8 a Ha)) (pstable_cpy_eg Xe YCg _ PS8) HR10))|].
intros W' c'' _ HRET.
unfold MUX_eg, MFY_eg in HRET. rewrite <- G33 in HRET.
img_apply (LEAF_arm false true tops rest W5 md2 _ _ W' c'' XC (fun _ => conj Ylt Ymax2) ltac:(img_try (intros E; discriminate E)) EP HRET).
+
intros m [[[(HP & HG1 & HG2) HF] HV] HC]. cbn [NC1 MU1 MF2].
split; [img_try (intros a Ha; img_exact (apresent_hmono (w_H W) (w_H W5) m a MON5 (proj1 HP a Ha)))|].
split; [img_try (intros a Ha; img_exact (apresent_hmono (w_H W) (w_H W5) m a MON5 (proj2 HP a Ha)))|].
split; [img_try (intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia)|]. split; [img_try (intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia)|].
split; [img_try (intros _ a Ha; img_apply HG1; unfold RANGE, kUserMapSize, kFreeArrayMapSize in *; img_exact Ha)|].
split. { intros _ x Hx. split; [img_try (img_exact (HF x Hx))|]. pose proof (proj1 (HG2 (bv_unsigned x) ltac:(img_try (unfold SHR; unfold W_FSH in Hx; img_change (kFreeArrayMapSize / 8) with 32768 in Hx; img_exact Hx)))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. img_exact Hh. }
split.
* intros i Hi. replace (nf + nce) with nfe by (img_try (clear - G22; zlia)). img_exact (HV i Hi).
* intros j Hj. rewrite Elen in Hj |- *. unfold SRC3_eg in HC. replace (nf + nce - n) with (nfe - n) by (img_try (clear - G22; zlia)). img_exact (HC j Hj).
+
intros a [[[[Hw|Hw]|Hw]|Hw]|Hw]; unfold YF8d.XC, YF8d.W_FEn, YF8d.NF'; cbn [NC1 MU1 MF2].
* unfold WINR0 in Hw. clear - Hw. tauto.
* do 9 right. left. split; [img_refl|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. img_exact Hw.
* do 10 right. split; [img_refl | img_try (img_exact Hw)].
* do 6 right. left. unfold W_FE in Hw. rewrite <- G22. img_exact Hw.
* do 2 right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
+
intros x NX. img_apply HEQ5; intros Hw; img_apply NX; unfold YF8d.XC; cbn [NC1 MU1 MF2].
* do 8 right. left. split; [img_refl|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. img_exact Hw.
* do 9 right. split; [img_refl|]. unfold W_FSH, SHR in *. img_change (kFreeArrayMapSize / 8) with 32768. img_exact Hw.
+ img_exact SUB5.
+ img_exact LE5.
+ rewrite AB5. clear. unfold kUserMapSize. zlia.
+ intros i Hi. rewrite A5. do 2 right. img_exact Hi.
+ img_exact IO5.
+ img_exact MW5.
+ cbn [St2]. img_exact (ledger_F_grant false 1 mdN Ymax W1P LN MWN EG5).
-   rewrite EcM. img_apply same_io_with_vm_backing.
Qed.
Lemma P1_of_frameX : forall (Wx : world tfxsegs) (X : Z -> Prop) (m : word -> option byte),
hsub (w_H Wx) (w_H W) -> (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) ->
(forall a, FAv <= a < FAv + mf -> ~ X a) -> (forall a, DSTv <= a < DSTv + 64 -> ~ X a) -> P1 Wx m.
Proof.
intros Wx X m Hs MEQ NA NB. pose proof derived_rangesR as DR. pose proof Hmf as [[M0 M1] _]. pose proof high_factsR as (F1' & F2 & _).
assert (G : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> apresent (w_H W) mem0 a -> apresent (w_H Wx) m a).
{ intros a Ra Hw [Hh Hb]. split.
- destruct (w_H Wx (Z_to_bv 64 a)) eqn:E; [|img_refl]. rewrite (Hs _ E) in Hh. discriminate Hh.
- rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_exact Ra; img_exact Hw)). img_exact Hb. }
split.
- intros a Ha. img_apply G; [img_try (clear - Ha DR M0 M1; numconst; unfold kFreeArrayMax in *; zlia) | img_try (img_exact (NA a Ha)) | img_try (img_exact (HfaPres a Ha))].
- intros a Ha. img_apply G; [img_try (clear - Ha DR F2; numconst; zlia) | img_try (img_exact (NB a Ha)) | img_try (img_exact (HslotPres a Ha))].
Qed.
Theorem refill_B3_g : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset -> amreal tfxsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
intros Xlt XR3.
assert (XC : XC3 true) by img_exact (conj Xlt XR3). assert (XCg : XCOND_g) by img_exact (conj Xlt XR3).
pose proof facts3 as (_ & _ & _ & _ & _ & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & _ & _ & _ & _ & _ & _ & G22 & G23 & G24 & G25 & _ & G27 & G28 & G29 & G30 & _ & _ & G33 & _).
assert (XR2 : mu2 <= kFreeArrayOffset) by (img_try (rewrite G15; img_exact XR3)).
pose proof (factsX3 true XC) as ([N0 N1] & N2 & _ & _ & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _). pose proof Hmf as [[M0 M1] _].
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2. pose proof derived_rangesR as DR. pose proof high_factsR as (_ & _ & _ & _ & _ & Y6 & _).
pose proof HAR as (MA & L & BUD & MW & HS0). pose proof (WF1 (proj1 Hpum)) as W1P.
destruct (pop_new true XC) as (tops & rest & EP & Eel & Erest & Eruns & Elen).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. destruct (E_mmu_g Xlt XR3) as (K & EK & K1 & K2 & K0). rewrite EK. cbn [ibind negb].
img_apply amreal_ask; [img_try (img_exact I)|].
eapply SRr_bind; [img_try (img_exact seg3P)|]. intros W1 c1 _ HR1.
eapply SRr_bind; [img_try (img_exact (seg3Q_map Xlt W1 c1 HR1))|]. intros W2 c2 _ HR2.
eapply SRr_mono; [img_try (img_exact (SRr_with_AI _ _ _ (seg3M Xlt XR3 W2 c2 HR2)))|].
intros W4 c4 _ [HAI HN]. pose proof (proj1 HN) as EW4. (subst W4; cbv beta).
pose proof NU_facts as (Fpc & F17 & F10 & Fea & F11 & F12 & F13 & F14 & F15 & Fnc & Fhd & Fsk & Fres_r & Fres_g).
destruct HN as (HNw & msN & matN & EN & EcN & HNrest).
set (mdN := with_vm_backing (m_vm_lazy md0) matN md0) in *.
assert (EcM : cfg_model c4 = mdN) by (img_try (rewrite EcN; img_refl)).
assert (LN : ALedger tfxsegs ly S mdN) by (img_try (img_exact (ALedger_same tfxsegs ly S md0 mdN L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)))).
assert (MWN : amwf mdN) by (img_try (img_exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW))).
assert (NZN : forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) by (img_try (intros e He; unfold uw; img_apply NZ0; unfold mdN in He; rewrite m_vmmaps_wvb in He; img_exact He)).
assert (RNGU : forall a, RANGE adr a -> 0 <= a < 2 ^ 64 /\ RBv + mu <= a < RBv + mu2 /\ kHighMemBeg <= a) by (img_try (intros a Ha; unfold RANGE in Ha; clear - Ha G6 G7 G10 G15 Q2 Y6; numconst; unfold kUserMapSize in *; zlia)).
assert (SNGU : forall a, SHR sha a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg) by (img_try (intros a Ha; unfold SHR in Ha; clear - Ha G13 G14; numconst; zlia)).
assert (NAU : forall a, FAv <= a < FAv + mf -> ~ RANGE adr a) by (img_try (intros a Ha Hr; unfold RANGE in Hr; clear - Ha Hr G10 G15 XR3 DR; unfold kUserMapSize in *; zlia)).
assert (NBU : forall a, DSTv <= a < DSTv + 64 -> ~ RANGE adr a).
{ pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
intros a Ha Hr. unfold RANGE in Hr. unfold DSTv, Pr in Ha. clear - Ha Hr G9 G7 Q1 Q2 DR TP HcR. try unfold T in *. numconst. unfold kUserMapSize in *. zlia. }
lazymatch goal with |- context [ibind (ibind (ibind (K _) ?g1) ?g2) ?g3] =>
eapply (node3 (KMapUser c mu kUserMapSize) S (fun z => ibind (ibind (ibind (K z) g1) g2) g3) LEAFW W md0 WINR0 PT R3_NU c4 (SOff rADR 0) adr sha holeU cs_NU
(conj HNw (ex_intro _ msN (ex_intro _ matN (ex_intro _ EN (conj EcN HNrest))))) HAI Fpc F17 F10 Fea U_adr F11 F12 F13 F14 F15 Fnc Fhd Fsk) end.
- img_exact G8.
- img_exact G9.
- img_exact G7.
- img_exact G11.
- img_exact G12.
- unfold kHighShadowBeg; clear - G13; zlia.
- unfold kHighShadowEnd; clear - G14; zlia.
- rewrite EcM. img_exact (place_U mdN LN NZN).
- rewrite EcM. img_exact MWN.
-   rewrite EcM. img_exact (al_top _ _ _ _ LN).
- rewrite EcM. img_apply (slack_at mdN W 0 L); [img_try (unfold mdN; rewrite m_vmmaps_wvb; img_refl) | img_try (unfold mdN; rewrite eager_used_wvb; clear; zlia) | img_try (clear; zlia) | img_try (clear; zlia)].
- img_refl.
- intros z Hz. img_exact Hz.
- intros m m' _ _. img_exact I.
- intros a Ha. img_apply band_not_WINR0. img_exact (proj2 (SNGU a Ha)).
- img_apply (H0sh_of sha adr); [img_try (clear - G8; apply Z.mod_divide in G8 as [q Hq]; [|zlia]; rewrite Hq; img_apply Z.mod_divide; [zlia|]; exists (q * 8192); zlia)
| img_try (rewrite <- RBv_is; img_exact G9) | img_try (rewrite <- RBv_is; img_exact G7) | img_try (img_exact G11) | img_try (unfold kHighShadowBeg; clear - G13; zlia) | img_try (unfold kHighShadowEnd; clear - G14; zlia)].
-   img_exact holeU_false.
-
intros cpk_q. rewrite EcM. intros HRk_q HAIk_q. rewrite Fres_r in HRk_q.
pose proof (place_U mdN LN NZN) as PLk_q. rewrite holeU_false in PLk_q.
img_apply (SRr_tnil tfxsegs W cpk_q _ (seg3_Ur W mdN WINR0 PT W cpk_q WX0 pstable_PT HRk_q)); [| img_try (img_exact HAIk_q)].
intros Wk_q ck_q _ HNk_q HAIck_q. pose proof (proj1 HNk_q) as EWk_q. (subst Wk_q; cbv beta).
pose proof NR_facts as (Rpc_q & R17_q & R10_q & Rea_q & R11_q & R12_q & R13_q & R14_q & R15_q & Rnc_q & Rhd_q & Rsk_q & Rres_e_q & Rres_x_q & Rres_g_q).
destruct HNk_q as (HNwk_q & msRk_q & matRk_q & ERk_q & EcRk_q & HNrestk_q).
set (mdK_q := with_vm_backing (m_vm_lazy mdN) matRk_q mdN) in *.
assert (EcK_q : cfg_model ck_q = mdK_q) by (img_try (rewrite EcRk_q; img_refl)).
apply (node3k W mdN WINR0 PT R3_NR ck_q (SOff rADR 0) adr cs_NR (conj HNwk_q (ex_intro _ msRk_q (ex_intro _ matRk_q (ex_intro _ ERk_q (conj EcRk_q HNrestk_q))))) HAIck_q Rpc_q R17_q R10_q Rea_q U_adr R11_q R12_q R13_q R14_q R15_q Rnc_q Rhd_q Rsk_q).
+ img_exact G8.
+ img_exact G9.
+ img_exact G7.
+ rewrite EcK_q. img_exact (occupied_of_place mdN mdK_q adr (conj (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _)) (proj2 PLk_q)).
+ rewrite EcK_q. unfold mdK_q. rewrite m_vmmaps_wvb. img_exact (al_top _ _ _ _ LN).
+ intros c3_q. rewrite EcK_q, Rres_e_q. intros HR3_q HAI3_q. img_exact (seg3_URe W mdK_q WINR0 PT W c3_q WX0 pstable_PT HR3_q HAI3_q).
+ intros c3_q. rewrite EcK_q, Rres_x_q. intros HR3_q HAI3_q. img_exact (seg3_URx W mdK_q WINR0 PT W c3_q WX0 pstable_PT HR3_q HAI3_q).
-
intros cpd_q. rewrite EcM. intros md3_q AI3_q MW3_q IO3_q EG3_q HRd_q. cbv beta. rewrite (K0 0 ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia))). cbn [ibind negb].
rewrite Fres_r in HRd_q.
pose proof (place_U mdN LN NZN) as PLd_q. rewrite holeU_false in PLd_q.
set (XD_q := fun a => WINR0 a \/ RANGE adr a) in *.
assert (HXD_q : forall a, WINR0 a -> XD_q a) by (img_try (intros a Ha; left; img_exact Ha)).
eapply amrealE_SRr_pre; [img_try (img_apply SRr_F; img_exact (SRr_with_AI _ _ _ (seg3_Ur W md3_q XD_q PT W cpd_q HXD_q pstable_PT HRd_q)))|].
intros Wd_q cd_q _ [HAId_q HNd_q]. pose proof (proj1 HNd_q) as EWd_q. (subst Wd_q; cbv beta).
pose proof NR_facts as (Rpc_q & R17_q & R10_q & Rea_q & R11_q & R12_q & R13_q & R14_q & R15_q & Rnc_q & Rhd_q & Rsk_q & Rres_e_q & Rres_x_q & Rres_g_q).
destruct HNd_q as (HNwd_q & msRd_q & matRd_q & ERd_q & EcRd_q & HNrestd_q).
set (mdD_q := with_vm_backing (m_vm_lazy md3_q) matRd_q md3_q) in *.
assert (EcD_q : cfg_model cd_q = mdD_q) by (img_try (rewrite EcRd_q; img_refl)).
assert (SLD_q : same_led md3_q mdD_q) by (img_try (split; unfold mdD_q; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb)])).
destruct (free_of_destroyed mdN mdD_q adr (al_top _ _ _ _ LN)
ltac:(img_try (clear - G9 G7 DR; numconst; unfold kUserMapSize in *; zlia))
ltac:(img_try (clear - G9 G7 DR; numconst; unfold kUserMapSize in *; zlia))
SLD_q (proj1 PLd_q)) as [FREEd_q TOPd_q].
assert (DLIM_q : vm_limit (m_vmmaps md3_q) = vm_limit (m_vmmaps mdN)) by (img_try (img_exact (proj1 (proj2 (proj2 (proj2 (destroyed_shape (w64 adr) (w64 kUserMapSize) mdN))))))).
eapply (node3r _ LEAFW W md3_q XD_q PT R3_NR cd_q (SOff rADR 0) adr cs_NR (conj HNwd_q (ex_intro _ msRd_q (ex_intro _ matRd_q (ex_intro _ ERd_q (conj EcRd_q HNrestd_q))))) HAId_q Rpc_q R17_q R10_q Rea_q U_adr R11_q R12_q R13_q R14_q R15_q Rnc_q Rhd_q Rsk_q).
+ img_exact G8.
+ img_exact G9.
+ img_exact G7.
+ rewrite EcD_q. img_exact FREEd_q.
+ rewrite EcD_q. img_exact (amwf_same md3_q mdD_q (proj1 SLD_q) (proj2 SLD_q) MW3_q).
+ rewrite EcD_q, TOPd_q. img_exact (al_top _ _ _ _ LN).
+ rewrite EcD_q. pose proof (slack_at mdN W 0 L ltac:(img_try (unfold mdN; rewrite m_vmmaps_wvb; img_refl)) ltac:(img_try (unfold mdN; rewrite eager_used_wvb; clear; zlia)) ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia))) as SLK_q.
unfold mdD_q. rewrite eager_used_wvb, m_vmmaps_wvb, DLIM_q. clear - SLK_q EG3_q. unfold kUserMapSize in *. zlia.
+ intros m m' _ _. img_exact I.
+ intros c3_q. rewrite EcD_q, Rres_e_q. intros HR3_q HAI3_q. img_exact (seg3_URe W mdD_q XD_q PT W c3_q HXD_q pstable_PT HR3_q HAI3_q).
+
intros W4_q c3_q. rewrite EcD_q. intros md4_q LE4_q A4_q SUB4_q MON4_q HEQ4_q AI4_q MW4_q IO4_q EG4_q AB4_q HR4_q. rewrite Rres_g_q in HR4_q. cbn [amrealE].
set (XG4_q := fun a => XD_q a \/ RANGE adr a) in *.
assert (HXG4_q : forall a, WINR0 a -> XG4_q a) by (img_try (intros a Ha; left; left; img_exact Ha)).
apply (at_R3_strengthen W4_q md4_q XG4_q PT (P1 W4_q)) in HR4_q.
2:{ intros m MEQ _ _. img_apply (P1_of_frameX W4_q XG4_q m SUB4_q MEQ); intros a Ha [[Hw|Hw]|Hw];
[img_try (img_exact (fa_not_WINR0 a ltac:(clear - Ha M1; unfold kFreeArrayMax in *; zlia) Hw)) | img_try (img_exact (NAU a Ha Hw)) | img_try (img_exact (NAU a Ha Hw))
| img_try (img_exact (slots_not_WINR0 a Ha Hw)) | img_try (img_exact (NBU a Ha Hw)) | img_try (img_exact (NBU a Ha Hw))]. }
eapply SRrF_mono; [img_try (img_apply SRr_F; img_exact (seg3_URg W4_q md4_q XG4_q (P1 W4_q) W4_q c3_q HXG4_q (pstable_P1 W4_q) HR4_q))|]. intros W' c'' _ HRET.
img_apply (LEAF_fail mu hol true false W4_q md4_q XG4_q (P1 W4_q) W' c'' S (eq_sym SG_S) HRET).
* intros m HPm. img_apply (PF_fail W4_q m mu HPm). intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia.
* intros a [[Hw|Hw]|Hw]; unfold YF8d.XC; [img_try (unfold WINR0 in Hw; clear - Hw; tauto) | |];
(do 7 right; left; split; [img_refl | img_try (unfold W_UW, RANGE in *; img_exact Hw)]).
* intros x NX. img_apply HEQ4_q. intros Hw. img_apply NX. unfold YF8d.XC. do 6 right. left. split; [img_refl | img_try (unfold W_UW, RANGE in *; img_exact Hw)].
* img_exact SUB4_q.
* img_exact LE4_q.
* rewrite AB4_q. clear. unfold kUserMapSize. zlia.
* intros i Hi. rewrite A4_q. right. img_exact Hi.
* img_exact IO4_q.
* img_exact MW4_q.
*
destruct (user_window (as_universe B) 1 0 0 ly S c LY W1P HcR) as (WINw_q & CUTl_q & CUTh_q & NOCUTw_q).
rewrite K3U_addr in WINw_q, CUTl_q, CUTh_q, NOCUTw_q.
refine (ledger_restored S 1 adr mdN mdD_q W1P (am_placed _ _ _ _ (proj1 HAR)) LN MWN WINw_q CUTl_q CUTh_q NOCUTw_q _ SLD_q _).
-- clear - G8. apply Z.mod_divide in G8 as [q Hq]; [|img_try (zlia)]. rewrite Hq. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q * 16). zlia.
-- eapply Z.le_trans; [img_try (img_exact EG4_q)|]. unfold mdD_q. rewrite eager_used_wvb. img_exact EG3_q.
* left; img_refl.
* intros _. img_exact (conj Xlt XR2).
* intros E; discriminate E.
+   rewrite EcD_q. img_exact (same_io_trans _ _ _ IO3_q (same_io_with_vm_backing _ _ _)).
-
intros W3 c'. rewrite EcM. intros md2 LE3 A3 SUB3 MON3 AI3 MW2 IO2 EG2 HEQ3 AB3 HR. cbv beta. rewrite K1. cbn [ibind negb].
destruct (E_getreg1 true SUp XC reg_g) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
rewrite Fres_g in HR.
assert (LUp : ALedger tfxsegs ly SUp md2) by img_exact (ledger_U_grant mdN LN MWN EG2).
assert (WUp : WfP (as_universe B) 0 0 0 SUp) by img_exact (WfP_SUp Xlt XR3).
assert (NZ2 : forall e, In e (vm_maps (m_vmmaps md2)) -> 0 < uw (snd e)).
{ intros e He. unfold md2, holeU in He. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol).
- rewrite (proj1 (grant_hole_shape (w64 adr) (w64 kUserMapSize) mdN)) in He. destruct He as [<-|He]; [|img_try (img_exact (NZN e He))].
unfold uw, w64. cbn [snd]. rewrite unsigned_lit_small; unfold kUserMapSize; clear; zlia.
- rewrite (proj1 (grant_piece_shape (w64 adr) (w64 kUserMapSize) mdN)) in He. img_exact (NZN e He). }
assert (LIM2 : vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps md0)).
{ unfold md2, holeU. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol);
[img_try (rewrite (proj1 (proj2 (proj2 (grant_hole_shape (w64 adr) (w64 kUserMapSize) mdN))))) | img_try (rewrite (proj1 (proj2 (proj2 (grant_piece_shape (w64 adr) (w64 kUserMapSize) mdN)))))]; unfold mdN; rewrite m_vmmaps_wvb; img_refl. }
assert (EGd : eager_used md2 <= eager_used md0 + kUserMapSize) by (img_try (unfold mdN in EG2; rewrite eager_used_wvb in EG2; img_exact EG2)).
set (XG := fun a => WINR0 a \/ RANGE adr a) in *.
assert (HXG : forall a, WINR0 a -> XG a) by (img_try (intros a Ha; left; img_exact Ha)).
apply (at_R3_strengthen W3 md2 XG _ (P_pres W3 adr sha (P1 W))) in HR.
2:{ intros m MEQ _ HG. split; [| img_try (img_exact (proj2 (P_grant_pres _ _ _ _ _ HG)))].
img_apply (P1_of_frameX W XG m (hsub_refl _) MEQ); intros a Ha [Hw|Hw]; [img_try (img_exact (fa_not_WINR0 a ltac:(clear - Ha M1; unfold kFreeArrayMax in *; zlia) Hw)) | img_try (img_exact (NAU a Ha Hw)) | img_try (img_exact (slots_not_WINR0 a Ha Hw)) | img_try (img_exact (NBU a Ha Hw))]. }
set (PG0 := P_pres W3 adr sha (P1 W)) in *.
assert (PSG0 : pstable PG0).
{ intros m m' Hfr (HP & HG1 & HG2). split; [img_try (img_exact (pstable_P1 W m m' Hfr HP))|]. split.
- intros a Ha. destruct (RNGU a Ha) as (Ra & Fa & Ka). eapply apresent_same; [|img_try (img_exact (HG1 a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra.
intros Hw. unfold WINR0 in Hw. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & S2 & _). pose proof high_factsR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NOSTK).
destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; [img_try (img_apply (proj2 (NOSTK a ltac:(clear - Hw S1 S2; unfold RSTACK in *; zlia))); clear - Fa Q1 Q2 G15 XR3 Hmu; numconst; unfold kUserMapSize in *; zlia) | | | |];
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP; unfold zdisjoint in TP; cbn [fst snd] in TP; clear - Hw Fa Q1 Q2 DR TP HcR G15 XR3 Hmu; unfold Pr, RGv in *; try unfold T in *; try unfold SB in *; numconst; unfold kUserMapSize in *; zlia.
- intros a Ha. destruct (SNGU a Ha) as [Ra Ba]. eapply apresent_same; [|img_try (img_exact (HG2 a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra. img_apply band_not_WINR0. img_exact Ba. }
set (XK := fun a => XG a \/ W_USH a) in *. set (PG := P_ush PG0) in *.
assert (HXK : forall a, WINR0 a -> XK a) by (img_try (intros a Ha; left; left; img_exact Ha)).
assert (PSG : pstable PG) by img_exact (pstable_ush PG0 PSG0).
assert (PRE : SRr tfxsegs W3 c' (at_R3 W3 md2 XK PG R3_Dg3)).
{ eapply SRr_bind; [img_try (img_exact (seg3_Ug W3 md2 XG PG0 W3 c' HXG PSG0 HR))|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ img_apply (seg3_Ums W3 md2 XG PG0 W6 c6 HXG PSG0); [| | img_try (img_exact HR6)].
- intros m (_ & _ & HG2) a Ha. img_apply HG2. unfold SHR. unfold W_USH in Ha. img_change (kUserMapSize / 8) with 32768 in Ha. img_exact Ha.
- intros m m' Hfr Hm HP. img_exact (P_pres_keep W3 adr sha m m' MON3 Hm HP). }
intros W7 c7 _ HR7. img_exact (segC1_g XCg W3 md2 XK PG W7 c7 HXK PSG HR7). }
destruct (Z_lt_le_dec mf (4 * nfg)) as [Ylt|Yge].
2:{
unfold bind at 1. rewrite (E_efa_e true SUp XC reg_g Yge). cbn [ibind negb].
destruct (E_tail true false SUp tops rest XC (reg_ge) upd_g EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
eapply SRr_bind; [img_try (img_exact PRE)|]. intros W8 c8 _ HR8.
assert (YCge : YCOND_ge) by img_exact Yge.
eapply SRr_bind; [img_try (img_exact (segC2e_g XCg Yge W3 md2 XK PG W8 c8 HXK PSG HR8))|]. intros W9 c9 _ HR9.
eapply SRr_bind.
{ img_apply (segE1_ge XCg YCge W3 md2 XK PG W9 c9 HXK PSG); [| | img_try (img_exact HR9)].
- intros m ((HP & _ & _) & _) a Ha. img_apply (apresent_hmono (w_H W) (w_H W3) m a MON3). img_apply (proj1 HP). unfold W_FE in Ha. clear - Ha Yge F0; zlia.
- intros m m' Hfr Hm [HP HU]. split; [img_try (img_exact (P_pres_keep W3 adr sha m m' MON3 Hm HP))|].
intros x Hx. rewrite (Hfr x); [img_try (img_exact (HU x Hx))|]. intros Hw. unfold W_FE in Hw. unfold W_USH in Hx. img_change (kUserMapSize / 8) with 32768 in Hx.
clear - Hw Hx G13 G14 DR F0. numconst. zlia. }
intros W10 c10 _ HR10.
set (X10 := fun a => XK a \/ W_FE nfg a) in *. set (P10 := P_fill_ge W3 PG) in *.
assert (HX10 : forall a, WINR0 a -> X10 a) by (img_try (intros a Ha; left; img_exact (HXK a Ha))).
assert (PS10 : pstable P10) by img_exact (pstable_fill_ge XCg YCge W3 PG PSG).
eapply SRr_bind; [img_try (img_exact (segE2_ge XCg YCge W3 md2 X10 P10 W10 c10 HX10 PS10 HR10))|]. intros W11 c11 _ HR11.
eapply SRr_bind.
{ img_apply (segE3_ge XCg YCge W3 md2 X10 P10 W11 c11 HX10 PS10); [| | | img_try (img_exact HR11)].
- intros m [[(HP & _ & _) _] _] a Ha. unfold SRC3_ge in Ha. img_apply (apresent_hmono (w_H W) (w_H W3) m a MON3). img_apply (proj1 HP). clear - Ha Yge F0 N2 N7 N0 K3 Hneed; cbn [NF1 NC1] in *; zlia.
- intros m [[(HP & _ & _) _] _] a Ha. img_apply (apresent_hmono (w_H W) (w_H W3) m a MON3). img_apply (proj2 HP). unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [[HP HU] HV]. split; [img_try (split; [img_exact (P_pres_keep W3 adr sha m m' MON3 Hm HP)|])|].
+ intros x Hx. rewrite (Hfr x); [img_try (img_exact (HU x Hx))|]. intros Hw. unfold W_DST in Hw. unfold W_USH in Hx. img_change (kUserMapSize / 8) with 32768 in Hx.
pose proof high_factsR as (Fz & _). clear - Hw Hx G13 G14 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros i Hi. img_apply (val_mem_frame_ge (w_H W3) m m'); [|img_try (img_exact (HV i Hi))]. intros t Ht. img_apply Hfr. unfold W_DST.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _).
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (img_try (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR; numconst; unfold kFreeArrayMax in *; zlia)).
unfold DSTv, Pr in *. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR Yge. numconst. unfold kFreeArrayMax in *. try unfold T in *. try unfold SB in *. zlia. }
intros W12 c12 _ HR12.
eapply SRr_mono; [img_try (img_exact (segE4_ge XCg YCge W3 md2 (fun a => X10 a \/ W_DST a) (P_cpy_ge P10) W12 c12 (fun a Ha => or_introl (HX10 a Ha)) (pstable_cpy_ge XCg YCge _ PS10) HR12))|].
intros W' c'' _ HRET.
unfold MUX_ge, MFY_ge in HRET. rewrite <- G15 in HRET.
img_apply (LEAF_arm true false tops rest W3 md2 _ _ W' c'' XC ltac:(img_try (intros E; discriminate E)) (fun _ => Yge) EP HRET).
+ intros m [[[(HP & HG1 & HG2) HU] HV] HC]. cbn [NC1 MU1 MF2].
split; [img_try (intros a Ha; img_exact (apresent_hmono (w_H W) (w_H W3) m a MON3 (proj1 HP a Ha)))|].
split; [img_try (intros a Ha; img_exact (apresent_hmono (w_H W) (w_H W3) m a MON3 (proj2 HP a Ha)))|].
split; [img_try (intros _ a Ha; img_apply HG1; unfold RANGE; img_exact Ha)|].
split. { intros _ x Hx. split; [img_try (img_exact (HU x Hx))|]. pose proof (proj1 (HG2 (bv_unsigned x) ltac:(img_try (unfold SHR; unfold W_USH in Hx; img_change (kUserMapSize / 8) with 32768 in Hx; img_exact Hx)))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. img_exact Hh. }
split; [img_try (intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia)|]. split; [img_try (intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia)|].
split.
* intros i Hi. replace (nf + ncg) with nfg by (img_try (clear - G23; zlia)). img_exact (HV i Hi).
* intros j Hj. rewrite Elen in Hj |- *. unfold SRC3_ge in HC. replace (nf + ncg - n) with (nfg - n) by (img_try (clear - G23; zlia)). img_exact (HC j Hj).
+ intros a [[[[Hw|Hw]|Hw]|Hw]|Hw]; unfold YF8d.XC, YF8d.W_FEn, YF8d.NF'; cbn [NC1 MU1 MF2].
* unfold WINR0 in Hw. clear - Hw. tauto.
* do 7 right. left. split; [img_refl|]. unfold W_UW, RANGE in *. img_exact Hw.
* do 8 right. left. split; [img_refl | img_try (img_exact Hw)].
* do 6 right. left. unfold W_FE in Hw. rewrite <- G23. img_exact Hw.
* do 2 right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
+ intros x NX. img_apply HEQ3; intros Hw; img_apply NX; unfold YF8d.XC; cbn [NC1 MU1 MF2].
* do 6 right. left. split; [img_refl|]. unfold W_UW, RANGE in *. img_exact Hw.
* do 7 right. left. split; [img_refl|]. unfold W_USH, SHR in *. img_change (kUserMapSize / 8) with 32768. img_exact Hw.
+ img_exact SUB3.
+ img_exact LE3.
+ rewrite AB3. clear. unfold kUserMapSize. zlia.
+ intros i Hi. rewrite A3. do 2 right. img_exact Hi.
+ img_exact IO2.
+ img_exact MW2.
+ cbn [St2 St1]. img_exact LUp. }
destruct (Z_lt_le_dec kFreeArrayMax mf2) as [Yfail|Ymax2].
{
unfold bind at 1. destruct (E_efa_fail true SUp XC reg_g Ylt Yfail) as [f Ef]. rewrite Ef. cbn [ibind negb amreal]. img_exact I. }
assert (Ymax : mf + kFreeArrayMapSize <= kFreeArrayMax) by (img_try (rewrite <- G33; img_exact Ymax2)).
assert (Ylt' : mf < 4 * NF1 true) by img_exact Ylt.
assert (YCgg : YCOND_gg) by img_exact (conj Ylt Ymax).
unfold bind at 1. destruct (E_efa_g true SUp XC reg_g upd_g Ylt' Ymax2) as (KF & EKF & KF1 & KF2 & KF0). rewrite EKF. cbn [ibind negb].
img_apply amreal_ask; [img_try (img_exact I)|].
eapply SRr_bind; [img_try (img_exact PRE)|]. intros W8 c8 _ HR8.
eapply SRr_mono; [img_try (img_exact (SRr_with_AI _ _ _ (segC2g_g XCg Ylt Ymax W3 md2 XK PG W8 c8 HXK PSG HR8)))|].
intros W9 c9 _ [HAI9 HN9]. pose proof (proj1 HN9) as EW9. (subst W9; cbv beta).
pose proof NFg_facts as (Fpc' & F17' & F10' & Fea' & F11' & F12' & F13' & F14' & F15' & Fnc' & Fhd' & Fsk' & Fres_r' & Fres_g').
destruct HN9 as (HNw' & msN' & matN' & EN' & EcN' & HNrest').
set (mdN' := with_vm_backing (m_vm_lazy md2) matN' md2) in *.
assert (EcM' : cfg_model c9 = mdN') by (img_try (rewrite EcN'; img_refl)).
assert (LN' : ALedger tfxsegs ly SUp mdN') by (img_try (img_exact (ALedger_same tfxsegs ly SUp md2 mdN' LUp (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)))).
assert (MWN' : amwf mdN') by (img_try (img_exact (amwf_same md2 mdN' (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2))).
assert (NZN' : forall e, In e (vm_maps (m_vmmaps mdN')) -> 0 < uw (snd e)) by (img_try (intros e He; img_apply NZ2; unfold mdN' in He; rewrite m_vmmaps_wvb in He; img_exact He)).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G31 & G32 & _).
assert (RNG : forall a, RANGE fadr a -> 0 <= a < 2 ^ 64 /\ FAv + mf <= a < FAv + 2 ^ 29).
{ intros a Ha. unfold RANGE in Ha. clear - Ha G24 G31 G32 G33 Ymax2 M0 Q2 Y6. numconst. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayMax in *. zlia. }
assert (SNG : forall a, SHR shf a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg).
{ intros a Ha. unfold SHR in Ha. clear - Ha G29 G30. numconst. zlia. }
assert (SHsep : sha + 32768 <= shf).
{ rewrite G11, G27. clear - G7 G8 G10 G15 G24 XR3 DR M0. apply Z.mod_divide in G8 as [q Hq]; [|img_try (zlia)]. rewrite Hq at 1. replace (q * 65536) with (q * 8192 * 8) by zlia. rewrite Z.div_mul by zlia.
assert (X : q * 8192 * 8 + 262144 <= fadr) by (img_try (unfold kUserMapSize, kFreeArrayOffset in *; zlia)).
assert (Y : (q * 8192 * 8 + 262144) / 8 <= fadr / 8) by (img_try (img_apply Z.div_le_mono; [img_try (zlia) | img_try (img_exact X)])).
replace (q * 8192 * 8 + 262144) with ((q * 8192 + 32768) * 8) in Y by zlia. rewrite Z.div_mul in Y by zlia. zlia. }
assert (PG_keep : forall (W5 : world tfxsegs) (R : Z -> Prop) (m m' : word -> option byte),
(forall y, w_H W3 y = false -> w_H W5 y = false) ->
(forall x : word, ~ R (bv_unsigned x) -> m' x = m x) -> (forall a, W_USH a -> ~ R a) ->
(forall a, apresent (w_H W5) m a -> apresent (w_H W5) m' a) -> PG m -> PG m').
{ intros W5 R m m' MON Hfr HRu Hm [HP HU]. split.
- destruct HP as (HP1 & HG1 & HG2). split; [|img_try (split)].
+ img_exact (P1_mono W m m' (fun a Ha' => pres_keepW W W5 m m' a (fun y Hy => MON y (MON3 y Hy)) (Hm a) Ha') HP1).
+ intros a Ha. img_exact (pres_keepW W3 W5 m m' a MON (Hm a) (HG1 a Ha)).
+ intros a Ha. img_exact (pres_keepW W3 W5 m m' a MON (Hm a) (HG2 a Ha)).
- intros x Hx. rewrite (Hfr x); [img_try (img_exact (HU x Hx)) | img_try (img_exact (HRu _ Hx))]. }
assert (HPuG : forall m m' : word -> option byte, (forall x : word, ~ RANGE fadr (bv_unsigned x) -> m' x = m x) -> PG m -> PG m').
{
intros m m' Hfr [(HP1 & HG1 & HG2) HU].
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
split; [img_try (split; [|split])|].
* img_apply (P1_frame W (RANGE fadr) m m' Hfr); [| | img_try (img_exact HP1)]; intros a Ha; unfold RANGE.
-- clear - Ha G24; zlia.
-- unfold DSTv, Pr in Ha. clear - Ha G24 M0 G33 Ymax2 DR TP Q1 Q2 HcR. try unfold T in *. numconst. unfold kFreeArrayMapSize, kUserMapSize in *. zlia.
* intros a Ha. destruct (RNGU a Ha) as (Ra & Fa & _). eapply apresent_same; [|img_try (img_exact (HG1 a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra. unfold RANGE. clear - Fa G24 G15 XR3 DR M0. unfold kUserMapSize, kFreeArrayOffset in *. zlia.
* intros a Ha. destruct (SNGU a Ha) as [Ra Ba]. eapply apresent_same; [|img_try (img_exact (HG2 a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra. unfold RANGE. clear - Ba G31. numconst. zlia.
* intros x Hx. rewrite (Hfr x); [img_try (img_exact (HU x Hx))|]. unfold RANGE. unfold W_USH in Hx. img_change (kUserMapSize / 8) with 32768 in Hx. clear - Hx G13 G14 G31. numconst. zlia. }
lazymatch goal with |- context [ibind (ibind (ibind (KF _) ?g1) ?g2) ?g3] =>
eapply (node3 (KMapFreeArray c mf kFreeArrayMapSize) SUp (fun z => ibind (ibind (ibind (KF z) g1) g2) g3) LEAFW W3 md2 XK PG R3_NFg c9 (SOff rFADR 0) fadr shf (holeF true) cs_NFg
(conj HNw' (ex_intro _ msN' (ex_intro _ matN' (ex_intro _ EN' (conj EcN' HNrest'))))) HAI9 Fpc' F17' F10' Fea' U_fadr F11' F12' F13' F14' F15' Fnc' Fhd' Fsk') end.
+ img_exact G25.
+ clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia.
+ clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
+ img_exact G27.
+ img_exact G28.
+ unfold kHighShadowBeg; clear - G29; zlia.
+ unfold kHighShadowEnd; clear - G30; zlia.
+ rewrite EcM'. img_exact (place_F true 0 mdN' Ymax WUp LN' NZN').
+ rewrite EcM'. img_exact MWN'.
+   rewrite EcM'. img_exact (al_top _ _ _ _ LN').
+ rewrite EcM'. img_apply (slack_at mdN' W3 (kUserMapSize + 32768) L); [img_try (unfold mdN'; rewrite m_vmmaps_wvb; img_exact LIM2) | img_try (unfold mdN'; rewrite eager_used_wvb; clear - EGd; zlia) | img_try (rewrite AB3; clear; zlia) | img_try (unfold kUserMapSize; clear; zlia)].
+ img_refl.
+ intros z Hz. img_exact Hz.
+ img_exact HPuG.
+
intros a Ha [[Hw|Hw]|Hw]; [img_try (img_exact (band_not_WINR0 a (proj2 (SNG a Ha)) Hw)) | |].
* destruct (RNGU a Hw) as (_ & _ & Ka). pose proof (SNG a Ha) as [_ Ba]. clear - Ka Ba. zlia.
* unfold SHR in Ha. unfold W_USH in Hw. img_change (kUserMapSize / 8) with 32768 in Hw. clear - Ha Hw SHsep. zlia.
+ img_apply (H0sh_of shf fadr); [img_try (clear - G25; apply Z.mod_divide in G25 as [q Hq]; [|zlia]; rewrite Hq; img_apply Z.mod_divide; [zlia|]; exists (q * 8192); zlia)
| img_try (rewrite <- RBv_is; clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia) | img_try (rewrite <- RBv_is; clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *; zlia)
| img_try (img_exact G27) | img_try (unfold kHighShadowBeg; clear - G29; zlia) | img_try (unfold kHighShadowEnd; clear - G30; zlia)].
+   img_exact (holeF_false true).
+
intros cpk_q. rewrite EcM'. intros HRk_q HAIk_q. rewrite Fres_r' in HRk_q.
pose proof (place_F true 0 mdN' Ymax WUp LN' NZN') as PLk_q. rewrite (holeF_false true) in PLk_q.
img_apply (SRr_tnil tfxsegs W3 cpk_q _ (segD_r_g W3 mdN' XK PG W3 cpk_q HXK PSG HRk_q)); [| img_try (img_exact HAIk_q)].
intros Wk_q ck_q _ HNk_q HAIck_q. pose proof (proj1 HNk_q) as EWk_q. (subst Wk_q; cbv beta).
pose proof NRFg_facts as (Rpc_q & R17_q & R10_q & Rea_q & R11_q & R12_q & R13_q & R14_q & R15_q & Rnc_q & Rhd_q & Rsk_q & Rres_e_q & Rres_x_q & Rres_g_q).
destruct HNk_q as (HNwk_q & msRk_q & matRk_q & ERk_q & EcRk_q & HNrestk_q).
set (mdK_q := with_vm_backing (m_vm_lazy mdN') matRk_q mdN') in *.
assert (EcK_q : cfg_model ck_q = mdK_q) by (img_try (rewrite EcRk_q; img_refl)).
apply (node3k W3 mdN' XK PG R3_NRFg ck_q (SOff rFADR 0) fadr cs_NRFg (conj HNwk_q (ex_intro _ msRk_q (ex_intro _ matRk_q (ex_intro _ ERk_q (conj EcRk_q HNrestk_q))))) HAIck_q Rpc_q R17_q R10_q Rea_q U_fadr R11_q R12_q R13_q R14_q R15_q Rnc_q Rhd_q Rsk_q).
* img_exact G25.
* clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia.
* clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
* rewrite EcK_q. img_exact (occupied_of_place mdN' mdK_q fadr (conj (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _)) (proj2 PLk_q)).
* rewrite EcK_q. unfold mdK_q. rewrite m_vmmaps_wvb. img_exact (al_top _ _ _ _ LN').
* intros c3_q. rewrite EcK_q, Rres_e_q. intros HR3_q HAI3_q. img_exact (segD_re_g W3 mdK_q XK PG W3 c3_q HXK PSG HR3_q HAI3_q).
* intros c3_q. rewrite EcK_q, Rres_x_q. intros HR3_q HAI3_q. img_exact (segD_rx_g W3 mdK_q XK PG W3 c3_q HXK PSG HR3_q HAI3_q).
+
intros cpd_q. rewrite EcM'. intros md3_q AI3_q MW3_q IO3_q EG3_q HRd_q. cbv beta. rewrite (KF0 0 ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia))). cbn [ibind negb].
rewrite Fres_r' in HRd_q.
pose proof (place_F true 0 mdN' Ymax WUp LN' NZN') as PLd_q. rewrite (holeF_false true) in PLd_q.
set (XD_q := fun a => XK a \/ RANGE fadr a) in *.
assert (HXD_q : forall a, WINR0 a -> XD_q a) by (img_try (intros a Ha; left; img_exact (HXK a Ha))).
eapply amrealE_SRr_pre; [img_try (img_apply SRr_F; img_exact (SRr_with_AI _ _ _ (segD_r_g W3 md3_q XD_q PG W3 cpd_q HXD_q PSG HRd_q)))|].
intros Wd_q cd_q _ [HAId_q HNd_q]. pose proof (proj1 HNd_q) as EWd_q. (subst Wd_q; cbv beta).
pose proof NRFg_facts as (Rpc_q & R17_q & R10_q & Rea_q & R11_q & R12_q & R13_q & R14_q & R15_q & Rnc_q & Rhd_q & Rsk_q & Rres_e_q & Rres_x_q & Rres_g_q).
destruct HNd_q as (HNwd_q & msRd_q & matRd_q & ERd_q & EcRd_q & HNrestd_q).
set (mdD_q := with_vm_backing (m_vm_lazy md3_q) matRd_q md3_q) in *.
assert (EcD_q : cfg_model cd_q = mdD_q) by (img_try (rewrite EcRd_q; img_refl)).
assert (SLD_q : same_led md3_q mdD_q) by (img_try (split; unfold mdD_q; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb)])).
assert (GEO3_q : fadr mod 65536 = 0 /\ RBv <= fadr /\ fadr + kUserMapSize <= RBv + 2 ^ 32).
{ split; [img_try (img_exact G25)|]. split; [img_try (clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia) | img_try (clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia)]. }
destruct (free_of_destroyed mdN' mdD_q fadr (al_top _ _ _ _ LN')
ltac:(img_try (destruct GEO3_q as (_ & GA & GB); clear - GA GB DR; numconst; unfold kUserMapSize in *; zlia))
ltac:(img_try (destruct GEO3_q as (_ & GA & GB); clear - GA GB DR; numconst; unfold kUserMapSize in *; zlia))
SLD_q (proj1 PLd_q)) as [FREEd_q TOPd_q].
assert (DLIM_q : vm_limit (m_vmmaps md3_q) = vm_limit (m_vmmaps mdN')) by (img_try (img_exact (proj1 (proj2 (proj2 (proj2 (destroyed_shape (w64 fadr) (w64 kUserMapSize) mdN'))))))).
eapply (node3r _ LEAFW W3 md3_q XD_q PG R3_NRFg cd_q (SOff rFADR 0) fadr cs_NRFg (conj HNwd_q (ex_intro _ msRd_q (ex_intro _ matRd_q (ex_intro _ ERd_q (conj EcRd_q HNrestd_q))))) HAId_q Rpc_q R17_q R10_q Rea_q U_fadr R11_q R12_q R13_q R14_q R15_q Rnc_q Rhd_q Rsk_q).
* img_exact (proj1 GEO3_q).
* img_exact (proj1 (proj2 GEO3_q)).
* img_exact (proj2 (proj2 GEO3_q)).
* rewrite EcD_q. img_exact FREEd_q.
* rewrite EcD_q. img_exact (amwf_same md3_q mdD_q (proj1 SLD_q) (proj2 SLD_q) MW3_q).
* rewrite EcD_q, TOPd_q. img_exact (al_top _ _ _ _ LN').
* rewrite EcD_q. pose proof (slack_at mdN' W3 (kUserMapSize + 32768) L ltac:(img_try (unfold mdN'; rewrite m_vmmaps_wvb; img_exact LIM2)) ltac:(img_try (unfold mdN'; rewrite eager_used_wvb; clear - EGd; zlia)) ltac:(img_try (rewrite AB3; clear; zlia)) ltac:(img_try (unfold kUserMapSize; clear; zlia))) as SLK_q.
unfold mdD_q. rewrite eager_used_wvb, m_vmmaps_wvb, DLIM_q. clear - SLK_q EG3_q. unfold kUserMapSize in *. zlia.
* img_exact HPuG.
* intros c3_q. rewrite EcD_q, Rres_e_q. intros HR3_q HAI3_q. img_exact (segD_re_g W3 mdD_q XD_q PG W3 c3_q HXD_q PSG HR3_q HAI3_q).
*
intros W4_q c3_q. rewrite EcD_q. intros md4_q LE4_q A4_q SUB4_q MON4_q HEQ4_q AI4_q MW4_q IO4_q EG4_q AB4_q HR4_q. rewrite Rres_g_q in HR4_q. cbn [amrealE].
set (XG4_q := fun a => XD_q a \/ RANGE fadr a) in *.
assert (HXG4_q : forall a, WINR0 a -> XG4_q a) by (img_try (intros a Ha; left; img_exact (HXD_q a Ha))).
eapply SRrF_mono; [img_try (img_apply SRr_F; img_exact (segD_rg_g W4_q md4_q XG4_q PG W4_q c3_q HXG4_q PSG HR4_q))|]. intros W' c'' _ HRET.
unfold MUX_g in HRET. rewrite <- G15 in HRET.
assert (MON34_q : forall y : word, w_H W y = false -> w_H W4_q y = false) by (img_try (intros y Hy; img_exact (MON4_q y (MON3 y Hy)))).
img_apply (LEAF_fail mu2 (del_hole mu hol) true true W4_q md4_q XG4_q PG W' c'' SUp ltac:(img_try (rewrite SG_upd; img_refl)) HRET).
-- intros m [(HP1 & HG1 & HG2) HU]. img_apply (PF_fail W4_q m mu2 (P1_hmono W W4_q m MON34_q HP1)). intros _. split; [img_try (intros a Ha; img_exact (apresent_hmono (w_H W3) (w_H W4_q) m a MON4_q (HG1 a Ha)))|].
intros x Hx. split; [img_try (img_exact (HU x Hx))|]. pose proof (proj1 (HG2 (bv_unsigned x) ltac:(img_try (unfold SHR; unfold W_USH in Hx; img_change (kUserMapSize / 8) with 32768 in Hx; img_exact Hx)))) as Hh. rewrite Z_to_bv_bv_unsigned in Hh. img_exact (MON4_q _ Hh).
-- intros a [[[[Hw|Hw]|Hw]|Hw]|Hw]; unfold YF8d.XC; [img_try (unfold WINR0 in Hw; clear - Hw; tauto) | | | |].
++ do 7 right. left. split; [img_refl|]. unfold W_UW, RANGE in *. img_exact Hw.
++ do 8 right. left. split; [img_refl | img_try (img_exact Hw)].
++ do 9 right. left. split; [img_refl | img_try (unfold W_FW, RANGE, kFreeArrayMapSize, kUserMapSize in *; img_exact Hw)].
++ do 9 right. left. split; [img_refl | img_try (unfold W_FW, RANGE, kFreeArrayMapSize, kUserMapSize in *; img_exact Hw)].
-- intros x NX. rewrite (HEQ4_q x); [img_try (img_apply HEQ3; intros Hw; img_apply NX; unfold YF8d.XC) |].
++ do 6 right. left. split; [img_refl|]. unfold W_UW, RANGE in *. img_exact Hw.
++ do 7 right. left. split; [img_refl|]. unfold W_USH, SHR in *. img_change (kUserMapSize / 8) with 32768. img_exact Hw.
++ intros Hw. img_apply NX. unfold YF8d.XC. do 8 right. left. split; [img_refl | img_try (unfold W_FW, RANGE, kFreeArrayMapSize, kUserMapSize in *; img_exact Hw)].
-- img_exact (hsub_trans _ _ _ SUB4_q SUB3).
-- img_exact (wle_trans _ _ _ _ LE3 LE4_q).
-- rewrite AB4_q, AB3. clear. unfold kUserMapSize. zlia.
-- intros i Hi. rewrite A4_q, A3. do 3 right. img_exact Hi.
-- img_exact IO4_q.
-- img_exact MW4_q.
--
assert (HFA_q : rg_mapped_fa (reg (St1 true) c) + kUserMapSize <= kFreeArrayMax) by (img_try (rewrite reg_S1; unfold rg1; cbn; img_exact Ymax)).
assert (PLs_q : sec_placed ly (St1 true)) by (img_try (rewrite S1_eq; unfold sec_placed; rewrite (YG0j.sec_extents_upd ly S c); img_exact (am_placed _ _ _ _ (proj1 HAR)))).
destruct (fa_window (as_universe B) 0 0 0 ly (St1 true) c LY WUp HcR HFA_q) as (WINw_q & CUTl_q & CUTh_q & NOCUTw_q).
rewrite (K3F_addr true) in WINw_q, CUTl_q, CUTh_q, NOCUTw_q.
refine (ledger_restored (St1 true) 0 fadr mdN' mdD_q WUp PLs_q LN' MWN' WINw_q CUTl_q CUTh_q NOCUTw_q _ SLD_q _).
++ clear - G25. apply Z.mod_divide in G25 as [q Hq]; [|img_try (zlia)]. rewrite Hq. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q * 16). zlia.
++ eapply Z.le_trans; [img_try (img_exact EG4_q)|]. unfold mdD_q. rewrite eager_used_wvb. img_exact EG3_q.
-- right; split; img_refl.
-- intros _. img_exact (conj Xlt XR2).
-- intros _; img_exact Ymax2.
*   rewrite EcD_q. img_exact (same_io_trans _ _ _ IO3_q (same_io_with_vm_backing _ _ _)).
+
intros W5 c'9. rewrite EcM'. intros md4 LE5 A5 SUB5 MON5 AI5 MW5 IO5 EG5 HEQ5 AB5 HR9. cbv beta. rewrite KF1. cbn [ibind negb].
destruct (E_tail true true (SFp true) tops rest XC (reg_xg true) (upd_xg true) EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
rewrite Fres_g' in HR9.
assert (YC : 4 * nfg <= mf2) by (img_try (rewrite G33; rewrite G23; unfold kFreeArrayMapSize; clear - F1 N1 N0; cbn [NC1] in *; zlia)).
assert (MON35 : forall y, w_H W y = false -> w_H W5 y = false) by (img_try (intros y Hy; img_exact (MON5 y (MON3 y Hy)))).
set (X5 := fun a => XK a \/ RANGE fadr a) in *.
assert (HX5 : forall a, WINR0 a -> X5 a) by (img_try (intros a Ha; left; img_exact (HXK a Ha))).
apply (at_R3_weaken W5 md4 X5 X5 _ (P_pres W5 fadr shf PG)) in HR9; [| img_try (intros a Ha; img_exact Ha) | img_try (intros m Hm; img_exact (P_grant_pres _ _ _ _ _ Hm))].
set (P5 := P_pres W5 fadr shf PG) in *.
assert (P5_keep : forall (R : Z -> Prop) (m m' : word -> option byte),
(forall x : word, ~ R (bv_unsigned x) -> m' x = m x) -> (forall a, W_USH a -> ~ R a) ->
(forall a, apresent (w_H W5) m a -> apresent (w_H W5) m' a) -> P5 m -> P5 m').
{ intros R m m' Hfr HRu Hm (HP & HF1' & HF2'). split; [img_try (img_exact (PG_keep W5 R m m' MON5 Hfr HRu Hm HP))|]. split; intros a Ha; [img_try (img_exact (Hm a (HF1' a Ha))) | img_try (img_exact (Hm a (HF2' a Ha)))]. }
assert (PS5 : pstable P5).
{ intros m m' Hfr (HP & HF1' & HF2'). split; [img_try (img_exact (PSG m m' Hfr HP))|]. split.
- intros a Ha. destruct (RNG a Ha) as [Ra Fa]. eapply apresent_same; [|img_try (img_exact (HF1' a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra. img_apply fa_not_WINR0. clear - Fa M0; zlia.
- intros a Ha. destruct (SNG a Ha) as [Ra Ba]. eapply apresent_same; [|img_try (img_exact (HF2' a Ha))]. img_apply Hfr. rewrite unsigned_lit_small by img_exact Ra. img_apply band_not_WINR0. img_exact Ba. }
eapply SRr_bind; [img_try (img_exact (segD_g_g W5 md4 X5 P5 W5 c'9 HX5 PS5 HR9))|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ img_apply (segD_ms_g XCg W5 md4 X5 P5 W6 c6 HX5 PS5); [| | img_try (img_exact HR6)].
- intros m (_ & _ & HF2') a Ha. img_apply HF2'. unfold SHR. unfold W_FSH in Ha. img_change (kFreeArrayMapSize / 8) with 32768 in Ha. img_exact Ha.
- intros m m' Hfr Hm HP. img_apply (P5_keep W_FSH m m' Hfr); [|img_try (img_exact Hm)|img_try (img_exact HP)]. intros a Ha Hb. unfold W_USH in Ha. unfold W_FSH in Hb. img_change (kUserMapSize / 8) with 32768 in Ha. clear - Ha Hb SHsep; zlia. }
intros W7 c7 _ HR7.
set (X7 := fun a => X5 a \/ W_FSH a) in *.
assert (HX7 : forall a, WINR0 a -> X7 a) by (img_try (intros a Ha; left; img_exact (HX5 a Ha))).
set (P7 := P_fsh_g P5) in *.
assert (PS7 : pstable P7) by img_exact (pstable_fsh_g P5 PS5).
eapply SRr_bind.
{ img_apply (segE1_gg XCg YCgg W5 md4 X7 P7 W7 c7 HX7 PS7); [| | img_try (img_exact HR7)].
- intros m [[[[HP1 _] _] [HF1' _]] _] a Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ img_apply (apresent_hmono (w_H W) (w_H W5) m a MON35). img_apply (proj1 HP1). unfold W_FE in Ha. clear - Ha Lo F0 F1; zlia.
+ img_apply (HF1' a). unfold RANGE. unfold W_FE in Ha. clear - Ha Hi YC G24 G33; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m m' Hfr Hm [HP HFS]. split.
+ img_apply (P5_keep (W_FE nfg) m m' Hfr); [|img_try (img_exact Hm)|img_try (img_exact HP)]. intros a Ha Hb. unfold W_USH in Ha. unfold W_FE in Hb. img_change (kUserMapSize / 8) with 32768 in Ha. clear - Ha Hb G13 G14 DR F0. numconst. zlia.
+ intros x Hx. rewrite (Hfr x); [img_try (img_exact (HFS x Hx))|]. intros Hw. unfold W_FE in Hw. unfold W_FSH in Hx. img_change (kFreeArrayMapSize / 8) with 32768 in Hx. clear - Hw Hx G29 G30 DR F0. numconst. zlia. }
intros W10 c10 _ HR10.
set (X10 := fun a => X7 a \/ W_FE nfg a) in *. set (P10 := P_fill_gg W5 P7) in *.
assert (HX10 : forall a, WINR0 a -> X10 a) by (img_try (intros a Ha; left; img_exact (HX7 a Ha))).
assert (PS10 : pstable P10) by img_exact (pstable_fill_gg XCg YCgg W5 P7 PS7).
eapply SRr_bind; [img_try (img_exact (segE2_gg XCg YCgg W5 md4 X10 P10 W10 c10 HX10 PS10 HR10))|]. intros W11 c11 _ HR11.
eapply SRr_bind.
{ img_apply (segE3_gg XCg YCgg W5 md4 X10 P10 W11 c11 HX10 PS10); [| | | img_try (img_exact HR11)].
- intros m [[[[[HP1 _] _] [HF1' _]] _] _] a Ha. unfold SRC3_gg in Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ img_apply (apresent_hmono (w_H W) (w_H W5) m a MON35). img_apply (proj1 HP1). clear - Ha Lo F0 F1 N2 N7 N0 K3 Hneed; cbn [NF1 NC1] in *; zlia.
+ img_apply (HF1' a). unfold RANGE. clear - Ha Hi YC G24 G33 K3; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m [[[[[HP1 _] _] _] _] _] a Ha. img_apply (apresent_hmono (w_H W) (w_H W5) m a MON35). img_apply (proj2 HP1). unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [[HP HFS] HV]. split; [img_try (split)|].
+ img_apply (P5_keep W_DST m m' Hfr); [|img_try (img_exact Hm)|img_try (img_exact HP)]. intros a Ha Hb. unfold W_USH in Ha. unfold W_DST in Hb. img_change (kUserMapSize / 8) with 32768 in Ha. pose proof high_factsR as (Fz & _). clear - Ha Hb G13 G14 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros x Hx. rewrite (Hfr x); [img_try (img_exact (HFS x Hx))|]. intros Hw. unfold W_DST in Hw. unfold W_FSH in Hx. img_change (kFreeArrayMapSize / 8) with 32768 in Hx. pose proof high_factsR as (Fz & _). clear - Hw Hx G29 G30 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros i Hi. img_apply (val_mem_frame_gg (w_H W5) m m'); [|img_try (img_exact (HV i Hi))]. intros t Ht. img_apply Hfr. unfold W_DST.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) ltac:(img_eqrefl) ltac:(img_eqrefl)) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _).
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (img_try (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR G33 Ymax2; numconst; unfold kFreeArrayMax, kFreeArrayMapSize in *; zlia)).
unfold DSTv, Pr in *. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR YC G33 Ymax2. numconst. unfold kFreeArrayMax, kFreeArrayMapSize in *. try unfold T in *. try unfold SB in *. zlia. }
intros W12 c12 _ HR12.
eapply SRr_mono; [img_try (img_exact (segE4_gg XCg YCgg W5 md4 (fun a => X10 a \/ W_DST a) (P_cpy_gg P10) W12 c12 (fun a Ha => or_introl (HX10 a Ha)) (pstable_cpy_gg XCg YCgg _ PS10) HR12))|].
intros W' c'' _ HRET.
unfold MUX_gg, MFY_gg in HRET. rewrite <- G15, <- G33 in HRET.
img_apply (LEAF_arm true true tops rest W5 md4 _ _ W' c'' XC (fun _ => conj Ylt Ymax2) ltac:(img_try (intros E; discriminate E)) EP HRET).
* intros m [[[[[(HP1 & HGU1 & HGU2) HU] [HF1' HF2']] HFS] HV] HC]. cbn [NC1 MU1 MF2].
split; [img_try (intros a Ha; img_exact (apresent_hmono (w_H W) (w_H W5) m a MON35 (proj1 HP1 a Ha)))|].
split; [img_try (intros a Ha; img_exact (apresent_hmono (w_H W) (w_H W5) m a MON35 (proj2 HP1 a Ha)))|].
split; [img_try (intros _ a Ha; img_exact (apresent_hmono (w_H W3) (w_H W5) m a MON5 (HGU1 a Ha)))|].
split. { intros _ x Hx. split; [img_try (img_exact (HU x Hx))|]. pose proof (proj1 (HGU2 (bv_unsigned x) ltac:(img_try (unfold SHR; unfold W_USH in Hx; img_change (kUserMapSize / 8) with 32768 in Hx; img_exact Hx)))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. img_exact (MON5 _ Hh). }
split; [img_try (intros _ a Ha; img_apply HF1'; unfold RANGE, kUserMapSize, kFreeArrayMapSize in *; img_exact Ha)|].
split. { intros _ x Hx. split; [img_try (img_exact (HFS x Hx))|]. pose proof (proj1 (HF2' (bv_unsigned x) ltac:(img_try (unfold SHR; unfold W_FSH in Hx; img_change (kFreeArrayMapSize / 8) with 32768 in Hx; img_exact Hx)))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. img_exact Hh. }
split.
-- intros i Hi. replace (nf + ncg) with nfg by (img_try (clear - G23; zlia)). img_exact (HV i Hi).
-- intros j Hj. rewrite Elen in Hj |- *. unfold SRC3_gg in HC. replace (nf + ncg - n) with (nfg - n) by (img_try (clear - G23; zlia)). img_exact (HC j Hj).
* intros a [[[[[[Hw|Hw]|Hw]|Hw]|Hw]|Hw]|Hw]; unfold YF8d.XC, YF8d.W_FEn, YF8d.NF'; cbn [NC1 MU1 MF2].
-- unfold WINR0 in Hw. clear - Hw. tauto.
-- do 7 right. left. split; [img_refl|]. unfold W_UW, RANGE in *. img_exact Hw.
-- do 8 right. left. split; [img_refl | img_try (img_exact Hw)].
-- do 9 right. left. split; [img_refl|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. img_exact Hw.
-- do 10 right. split; [img_refl | img_try (img_exact Hw)].
-- do 6 right. left. unfold W_FE in Hw. rewrite <- G23. img_exact Hw.
-- do 2 right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
* intros x NX. rewrite (HEQ5 x); [img_try (img_apply HEQ3)|..]; intros Hw; img_apply NX; unfold YF8d.XC; cbn [NC1 MU1 MF2].
-- do 6 right. left. split; [img_refl|]. unfold W_UW, RANGE in *. img_exact Hw.
-- do 7 right. left. split; [img_refl|]. unfold W_USH, SHR in *. img_change (kUserMapSize / 8) with 32768. img_exact Hw.
-- do 8 right. left. split; [img_refl|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. img_exact Hw.
-- do 9 right. split; [img_refl|]. unfold W_FSH, SHR in *. img_change (kFreeArrayMapSize / 8) with 32768. img_exact Hw.
* intros a Ha. img_exact (SUB3 _ (SUB5 _ Ha)).
* img_exact (wle_trans _ _ _ _ LE3 LE5).
* rewrite AB5, AB3. clear. unfold kUserMapSize. zlia.
* intros i Hi. rewrite A5. do 2 right. rewrite A3. do 2 right. img_exact Hi.
* img_exact IO5.
* img_exact MW5.
* cbn [St2]. img_exact (ledger_F_grant true 0 mdN' Ymax WUp LN' MWN' EG5).
+ rewrite EcM'. img_exact (same_io_trans _ _ _ IO2 (same_io_with_vm_backing _ _ _)).
- rewrite EcM. img_apply same_io_with_vm_backing.
Qed.
Theorem refill_B3_W : amreal tfxsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
destruct (Z_lt_le_dec mu tot) as [Xlt|Xe].
- destruct (Z_lt_le_dec kFreeArrayOffset (mu + kUserMapSize)) as [XF|XR3]; [|img_try (img_exact (refill_B3_g Xlt XR3))].
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. destruct (E_mmu_fail Xlt XF) as [f Ef]. rewrite Ef. cbn [ibind negb amreal]. img_exact I.
- destruct (Z_lt_le_dec mf (4 * nfe)) as [Ylt|Ye]; [|img_try (img_exact (refill_B3_ee Xe Ye))].
destruct (Z_lt_le_dec kFreeArrayMax (mf + kFreeArrayMapSize)) as [YF|Ymax]; [|img_try (img_exact (refill_B3_eg Xe Ylt Ymax))].
assert (XC : XC3 false) by img_exact Xe.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. rewrite (E_mmu_e Xe). cbn [ibind negb].
destruct (E_getreg1 false S XC reg_e) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
unfold bind at 1. destruct (E_efa_fail false S XC reg_e Ylt ltac:(img_try (rewrite G33; img_exact YF))) as [f Ef]. rewrite Ef. cbn [ibind negb amreal]. img_exact I.
Qed.
Theorem refill_B3 : amreal tfxsegs (refill_tree c S) W cfg0 LEAFQ.
Proof.
img_apply (amreal_atok _ true _ W cfg0 LEAFQ (refill_tree_ok true)).
eapply amreal_mono; [|img_try (img_exact refill_B3_W)]. intros [u s'] W' c' H [ns' WF']. destruct u. img_exact (H (ex_intro _ ns' WF')).
Qed.
End g.
End d.

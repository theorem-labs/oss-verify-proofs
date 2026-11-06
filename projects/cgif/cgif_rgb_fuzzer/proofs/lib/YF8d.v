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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3i YF81 YF40 YF8b YF8a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section l. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Section z. Context {imgk : img}.
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
Local Abbreviation AR3 f := (f mf au mu) (only parsing).
Local Abbreviation ARj f := (f ly regs0 c) (only parsing).
Local Abbreviation class_facts := ((AR3 ((ARj (@YF7w.class_facts)) maxc n)) csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation AR4 f := (f imgk ly regs0) (only parsing).
Local Abbreviation high_factsR := ((AR3 ((AR4 (@YF7w.high_factsR _)) maxc)) IMG LY Hmf Hmu).
Local Abbreviation off_T := ((AR3 ((AR4 (@YF7w.off_T _)) maxc)) IMG LY Hmf Hmu).
Local Abbreviation off_C := ((AR3 ((AR4 (@YF7w.off_C _)) maxc)) IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation AR2 f := (f IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) (only parsing).
Local Abbreviation ARc f := (f c maxc n nf) (only parsing).
Local Abbreviation derived_rangesR := (AR2 ((AR3 (ARc (AR4 (@YF7w.derived_rangesR _)))) csz)).
Local Abbreviation WINR0 := (ARj (@YF7w.WINR0)).
Local Abbreviation WINR := ((ARj (@YF7w.WINR)) n).
Local Abbreviation WINR0_WINR := ((ARj (@YF7w.WINR0_WINR)) n).
Local Abbreviation WSKELR := (@YF7w.WSKELR).
Local Abbreviation win_sub := (@YF7w.win_sub).
Local Abbreviation win_sub_sound := ((AR3 ((ARj (@YF7w.win_sub_sound)) maxc n)) Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (AR2 (AR0 (AR4 (@YF7w.WSKELR_WINR0 _)))).
Local Abbreviation windows_WINR0 := (AR2 (AR0 (AR4 (@YF7w.windows_WINR0 _)))).
Local Abbreviation frame_WINR0 := (AR2 (AR0 (AR4 (@YF7w.frame_WINR0 _)))).
Local Abbreviation frame_X := (AR2 (AR0 (AR4 (@YF7w.frame_X _)))).
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
Local Abbreviation pstable := (ARj (@YF7w.pstable)).
Local Abbreviation all_disjoint_of_forall := (@YF7w.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (AR3 ((AR4 (@YF7w.kept_of_frame)) maxc)).
Local Abbreviation kept_of_frame2 := (AR3 ((AR4 (@YF7w.kept_of_frame2)) maxc)).
Local Abbreviation SKEL_TAILR := (@YF7w.SKEL_TAILR imgk).
Local Abbreviation RFACTSR := ((AR4 (@YF7w.RFACTSR)) c).
Local Abbreviation stack_ivsR := ((AR3 (@YF7w.stack_ivsR _ ly regs0 maxc)) LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := ((AR2 ((AR3 (ARc (AR4 (@YF7w.zone_litR _)))) csz)) Hsp).
Local Abbreviation zone_TR := ((AR3 ((AR4 (@YF7w.zone_TR _)) c maxc)) IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := ((AR2 ((AR3 (ARc (AR4 (@YF7w.zone_CR _)))) csz)) Hsp).
Local Abbreviation zone_RGR := ((AR2 ((AR3 (ARc (AR4 (@YF7w.zone_RGR _)))) csz)) Hsp).
Local Abbreviation slots_not_WINR0 := ((AR2 ((AR3 (ARc (AR4 (@YF7w.slots_not_WINR0 _)))) csz)) Hsp).
Local Abbreviation fa_not_WINR0 := ((AR2 ((AR3 (ARc (AR4 (@YF7w.fa_not_WINR0 _)))) csz)) Hsp).
Local Abbreviation tail_ext_okR := ((AR2 (AR0 (AR4 (@YF7w.tail_ext_okR _)))) Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := ((AR3 ((AR4 (@YF7w.rdn_of_presentR)) maxc)) Hmf Hmu).
Local Abbreviation store_ok_of_presentR := ((AR3 ((AR4 (@YF7w.store_ok_of_presentR)) maxc)) Hmf Hmu).
Local Abbreviation AR8 f := (f Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp) (only parsing).
Local Abbreviation ARf f := (AR3 f j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu) (only parsing).
Local Abbreviation cpy4_stretch := (AR8 (ARf ((AR4 (@YF7w.cpy4_stretch _)) c maxc nf))).
Local Abbreviation AR1 f := (f c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug) (only parsing).
Local Abbreviation facts3 := (AR1 (AR4 (@YF7w.facts3 _))).
Local Abbreviation RFACTS3 := ((AR4 (@YF7w.RFACTS3)) c).
Local Abbreviation tail_ext_ok3 := ((AR2 (AR0 (AR4 (@YF7w.tail_ext_ok3 _)))) Hsp).
Local Abbreviation stack_ext_ok3 := ((AR2 ((AR3 (ARc (AR4 (@YF7w.stack_ext_ok3 _)))) csz)) Hsp).
Local Abbreviation scratch_headed := (@YF7w.scratch_headed).
Local Abbreviation mem_ok_scratch_present := ((AR0 (AR4 (@YF7w.mem_ok_scratch_present _))) LY Hmf Hmu Hsp).
Local Abbreviation at_R3_run := ((AR2 (AR0 ((AR4 (@YF7w.at_R3_run _ _)) mem0))) Hsp).
Local Abbreviation at_R3_run_ecall := ((AR2 (AR0 ((AR4 (@YF7w.at_R3_run_ecall _ _)) mem0))) Hsp).
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
Local Abbreviation at_R3_ret := ((AR8 ((AR0 ((AR4 (@YF7w.at_R3_ret _)) mem0)) HcR Hnf Hmf Hmu)) Hra Htp).
Local Abbreviation at_N3_cont := ((AR2 (AR0 ((AR4 (@YF7w.at_N3_cont _ _)) mem0))) Hsp).
Local Abbreviation memset_stretch3 := (AR8 (ARf ((AR4 (@YF7w.memset_stretch3 _)) c maxc nf))).
Local Abbreviation nth_Z_to_le_bytes4 := (@YF7w.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (AR8 (ARf ((AR4 (@YF7w.popfree_stretch _)) c maxc nf))).
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
Local Abbreviation AR7 f := (f _ imgk W ly mem0 c) (only parsing).
Local Abbreviation AR9 f := (f B S HARm) (only parsing).
Local Abbreviation cls_wfR := ((AR9 ((AR7 (@YF8b.cls_wfR)) HcR)) Hinited).
Local Abbreviation cls_wf0 := (AR9 ((AR7 (@YF8b.cls_wf0)) HcR)).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation AR6 f := (f B S HARm Hnf_def Hmf_def Hau_def Hmu_def) (only parsing).
Local Abbreviation ARi f := (AR5 f c maxc nf) (only parsing).
Local Abbreviation reg_facts0 := (AR6 ((AR3 (ARi (@YF8b.reg_facts0 _))) HcR)).
Local Abbreviation reg_facts := ((AR9 ((AR3 (ARi (@YF8b.reg_facts _))) HcR Hmax Hsp)) Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (AR6 ((AR3 (ARi (@YF8b.Hnf' _))) HcR Hsp)).
Local Abbreviation Hmf' := (AR6 ((AR3 (ARi (@YF8b.Hmf' _))) HcR Hsp)).
Local Abbreviation Hmu' := (AR6 ((AR3 (ARi (@YF8b.Hmu' _))) HcR Hsp)).
Local Abbreviation Hcarved' := ((AR9 ((AR7 (@YF8b.Hcarved')) au mu HcR)) Hau_def Hmu_def).
Local Abbreviation Hau_al' := ((AR9 ((AR7 (@YF8b.Hau_al')) au csz HcR Hcsz)) Hau_def).
Local Abbreviation vis_present := (AR9 ((AR5 (@YF8b.vis_present _)) maxc)).
Local Abbreviation thread_present := (AR6 ((AR3 (ARi (@YF8b.thread_present _))) csz IMG LY HcR Hcsz Hsp)).
Local Abbreviation ARd f := (AR3 f csz IMG LY HcR Hmax Hn Hcsz Hsp) (only parsing).
Local Abbreviation rinfo_present := (AR6 (ARd (ARc (AR5 (@YF8b.rinfo_present _))))).
Local Abbreviation HslotPres' := (AR6 (ARd (ARc (AR5 (@YF8b.HslotPres' _))))).
Local Abbreviation HfaPres' := (AR6 (ARd (ARc (AR5 (@YF8b.HfaPres' _))))).
Local Abbreviation word_of_present := ((AR5 (@YF8b.word_of_present)) maxc).
Local Abbreviation val_mem_lo4 := ((AR4 (@YF8b.val_mem_lo4)) maxc).
Local Abbreviation junk_valuesR := (AR6 (ARd (ARc (AR5 (@YF8b.junk_valuesR _))))).
Local Abbreviation cell_sym := (@YF8b.cell_sym _ imgk W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@YF8b.cell_lit _ imgk W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (AR9 (@YF8b.cell_state _ imgk W ly mem0)).
Local Abbreviation In_acells_cache := ((ARj (@YF8b.In_acells_cache)) maxc HcR B S).
Local Abbreviation In_acells_region := ((ARj (@YF8b.In_acells_region)) maxc HcR B S).
Local Abbreviation cache_valsR := ((AR9 ((AR5 (@YF8b.cache_valsR _)) c maxc csz HcR Hmax Hcsz)) Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@YF8b.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (AR9 ((AR5 (@YF8b.cache_valsU _)) maxc)).
Local Abbreviation region_valsR := (AR6 ((AR3 (ARi (@YF8b.region_valsR _))) HcR)).
Local Abbreviation chunk_lit := (AR0 (AR5 (@YF8b.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR5 (@YF8b.chunk_lit_at))).
Local Abbreviation chunk_atom := (AR0 (AR5 (@YF8b.chunk_atom))).
Local Abbreviation ARa f := (f Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) (only parsing).
Local Abbreviation ARg f := (f Hpres0R B S TS HTSD HARm) (only parsing).
Local Abbreviation REG0R3_ok_but35 := (ARa (ARg (AR8 (AR2 (AR0 (AR5 (@YF8b.REG0R3_ok_but35 _))))))).
Local Abbreviation REG0R3_ok := (ARa ((ARg (AR8 (AR2 (AR0 (AR5 (@YF8b.REG0R3_ok _)))))) Hinited Hchunks)).
Local Abbreviation REG0U3_ok := (ARa (ARg (AR8 (AR2 (AR0 (AR5 (@YF8b.REG0U3_ok _))))))).
Local Abbreviation PAIRSR3_ok := ((AR2 (AR0 (AR4 (@YF8b.PAIRSR3_ok _)))) Hsp).
Local Abbreviation SPAN3_disj := ((AR2 (AR0 (AR4 (@YF8b.SPAN3_disj _)))) Hsp).
Local Abbreviation ARb f := (f Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug) (only parsing).
Local Abbreviation FACTSR3_ok := (ARb (AR8 (AR2 (AR0 (AR4 (@YF8b.FACTSR3_ok _)))))).
Local Abbreviation SEEDR3_ok := (ARa ((ARg (ARb ((AR8 (AR2 (AR0 (AR5 (@YF8b.SEEDR3_ok _ _))))) Htp Ha0 Ha1 Ha2 Ha3))) Hinited Hchunks)).
Local Abbreviation PAIRSU3_ok := ((AR2 (AR0 (AR4 (@YF8b.PAIRSU3_ok _)))) Hsp).
Local Abbreviation SEEDU3_ok := (ARa (ARg (ARb ((AR8 (AR2 (AR0 (AR5 (@YF8b.SEEDU3_ok _ _))))) Htp Ha0 Ha1 Ha2 Ha3)))).
Local Abbreviation fr := (@YF8a.fr c S).
Local Abbreviation hol := (@YF8a.hol c S).
Local Abbreviation len_facts3 := (AR9 ((AR7 (@YF8a.len_facts3)) HcR)).
Local Abbreviation ARh f := (f S Hnf_def Hmf_def Hau_def Hmu_def) (only parsing).
Local Abbreviation reg_S := (ARh (AR3 (@YF8a.reg_S c nf))).
Local Abbreviation reg_upd3 := (AR9 ((AR7 (@YF8a.reg_upd3)) HcR)).
Local Abbreviation cache_upd3 := (AR9 ((AR7 (@YF8a.cache_upd3)) HcR)).
Local Abbreviation PM3 := ((AR9 ((AR7 (@YF8a.PM3)) maxc HcR Hmax)) Hinited).
Local Abbreviation WF1 := (AR9 (@YF8a.WF1 _ imgk W ly mem0)).
Local Abbreviation ARe f := (AR3 f mu2) (only parsing).
Local Abbreviation rUp := ((ARe (@YF8a.rUp c)) S).
Local Abbreviation rUm := ((AR3 (@YF8a.rUm c)) S).
Local Abbreviation SUp := ((ARe (@YF8a.SUp c)) S).
Local Abbreviation SUm := ((AR3 (@YF8a.SUm c)) S).
Local Abbreviation MU1 := (@YF8a.MU1 mu mu2).
Local Abbreviation HO1 := (@YF8a.HO1 c mu S).
Local Abbreviation NC1 := (@YF8a.NC1 nce ncg).
Local Abbreviation NF1 := (@YF8a.NF1 nfe nfg).
Local Abbreviation AU1 := (@YF8a.AU1 aue aug).
Local Abbreviation rg1 := ((ARe (@YF8a.rg1 c)) S).
Local Abbreviation St1 := ((ARe (@YF8a.St1 c)) S).
Local Abbreviation rFp := ((ARe (@YF8a.rFp c)) mf2 S).
Local Abbreviation rFm := ((ARe (@YF8a.rFm c)) S).
Local Abbreviation SFp := ((ARe (@YF8a.SFp c)) mf2 S).
Local Abbreviation SFm := ((ARe (@YF8a.SFm c)) S).
Local Abbreviation MF2 := (@YF8a.MF2 mf mf2).
Local Abbreviation HO2 := (@YF8a.HO2 c mf mu S).
Local Abbreviation rg2 := ((ARe (@YF8a.rg2 c)) mf2 S).
Local Abbreviation St2 := ((ARe (@YF8a.St2 c)) mf2 S).
Local Abbreviation rP := ((ARe (@YF8a.rP c)) nce ncg mf2 aue aug S).
Local Abbreviation rQ := (@YF8a.rQ c mf mu mu2 mf2 aue aug S).
Local Abbreviation SQ := (@YF8a.SQ c maxc mf mu mu2 mf2 aue aug S).
Local Abbreviation S1_eq := (AR6 ((ARe ((AR7 (@YF8a.S1_eq)) nf)) HcR)).
Local Abbreviation reg_S1 := (AR6 ((ARe ((AR7 (@YF8a.reg_S1)) nf)) HcR)).
Local Abbreviation S2_eq := (AR6 ((ARe ((AR7 (@YF8a.S2_eq)) nf)) mf2 HcR)).
Local Abbreviation reg_S2 := (AR6 ((ARe ((AR7 (@YF8a.reg_S2)) nf)) mf2 HcR)).
Local Abbreviation upd_S1 := (AR6 ((ARe ((AR7 (@YF8a.upd_S1)) nf)) HcR)).
Local Abbreviation upd_S2 := (AR6 ((ARe ((AR7 (@YF8a.upd_S2)) nf)) mf2 HcR)).
Local Abbreviation XC3 := (@YF8a.XC3 mu tot).
Local Abbreviation factsX3 := (AR1 (AR4 (@YF8a.factsX3 _))).
Local Abbreviation round_user := (AR1 (AR4 (@YF8a.round_user _))).
Local Abbreviation round_fa := (AR1 (AR4 (@YF8a.round_fa _))).
Local Abbreviation runs_ok_new := (AR9 (AR1 (AR5 (@YF8a.runs_ok_new _)))).
Local Abbreviation pop_new := ((AR9 (AR1 (AR5 (@YF8a.pop_new _)))) Hnf_def).
Local Abbreviation E_mmu_e := (ARh ((AR3 (@YF8a.E_mmu_e c nf)) csz need tot Hcsz Htot)).
Local Abbreviation E_mmu_g := (ARh (AR1 (AR4 (@YF8a.E_mmu_g _)))).
Local Abbreviation E_mmu_fail := (ARh (AR1 (AR4 (@YF8a.E_mmu_fail _)))).
Local Abbreviation E_efa_e := ((AR3 (@YF8a.E_efa_e c)) tot mu2 nfe nfg S).
Local Abbreviation E_efa_g := ((AR1 (AR4 (@YF8a.E_efa_g _))) S).
Local Abbreviation E_efa_fail := ((AR1 (AR4 (@YF8a.E_efa_fail _))) S).
Local Abbreviation E_tail := ((AR9 (AR1 (AR5 (@YF8a.E_tail _)))) Hnf_def).
Local Abbreviation E_tree := ((AR9 ((AR7 (@YF8a.E_tree)) maxc n nf need HcR Hmax Hn Hnlt Hneed)) Hinited Hchunks Hnf_def).
Local Abbreviation E_pop := (@YF8a.E_pop c need S).
Local Abbreviation E_getreg1 := ((AR1 (AR4 (@YF8a.E_getreg1 _))) S Hnf_def).
Local Abbreviation reg_e := (ARh (ARe (@YF8a.reg_e c nf))).
Local Abbreviation reg_g := (AR9 ((ARe (AR7 (@YF8a.reg_g))) HcR)).
Local Abbreviation upd_e := (@YF8a.upd_e c S).
Local Abbreviation upd_g := ((ARe (@YF8a.upd_g c)) S).
Local Abbreviation reg_ee := (ARh ((ARe (@YF8a.reg_ee c nf)) mf2)).
Local Abbreviation reg_ge := (AR9 ((ARe (AR7 (@YF8a.reg_ge))) mf2 HcR)).
Local Abbreviation reg_xg := (AR9 ((ARe (AR7 (@YF8a.reg_xg))) mf2 HcR)).
Local Abbreviation upd_xg := ((ARe (@YF8a.upd_xg c)) mf2 S).
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
Let m0 := mrestrict (w_H W) mem0.
Lemma zrange_dec : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. clear.
intros lo hi a. destruct (Z_le_dec lo a) as [H1|H1]; [img_try (destruct (Z_lt_dec a hi) as [H2|H2]; [left; img_exact (conj H1 H2) | right; intros [_ H]; img_exact (H2 H)]) | img_try (right; intros [H _]; img_exact (H1 H))].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. clear. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; img_exact H. Qed.
Lemma val_mem_cell : forall (Hh : word -> bool) mem e (w : nat) e',
val_mem tfxsegs (mrestrict Hh mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview tfxsegs Hh mem) (ACell e w (AV e')).
Proof.
clear. intros Hh mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [img_refl|]. unfold YG0h.le_byte. img_apply Z.mod_pos_bound. zlia.
Qed.
Lemma val_mem_at : forall (m : word -> option byte) a a' (w : nat) x, a = a' -> val_mem tfxsegs m a' w x -> val_mem tfxsegs m a w x.
Proof. clear. intros m a a' w x -> H. img_exact H. Qed.
Lemma nth_error_run_elems : forall m lo sz j, (j < m)%nat -> nth_error (run_elems lo sz m) j = Some (lo + Z.of_nat j * sz).
Proof. clear.
induction m as [|m IH]; intros lo sz j Hj; [img_try (zlia)|]. cbn [run_elems]. destruct j as [|j]; cbn [nth_error]; [img_try (f_equal; zlia)|].
rewrite IH by zlia. f_equal. zlia.
Qed.
Lemma fa_nth_elems : forall sz fl j, runs_ok fl -> 0 <= j -> fa_nth sz fl j = nth_error (fa_elems sz fl) (Z.to_nat j).
Proof. clear.
intros sz fl. induction fl as [|[lo k|o] t IH]; intros j Hr Hj.
- cbn. destruct (Z.to_nat j); img_refl.
- inversion Hr as [|x y Hk Ht]; (subst; cbv beta). cbn [fa_nth]. rewrite fa_elems_cons_run.
destruct (Z.ltb_spec j k).
+ rewrite nth_error_app1 by (img_try (rewrite run_elems_length; zlia)). rewrite nth_error_run_elems by zlia. f_equal. rewrite Z2Nat.id by zlia. img_refl.
+ rewrite nth_error_app2 by (img_try (rewrite run_elems_length; zlia)). rewrite run_elems_length. rewrite IH by (img_try (assumption || zlia)). f_equal. zlia.
- inversion Hr as [|x y Hk Ht]; (subst; cbv beta). cbn [fa_nth]. rewrite fa_elems_cons_one. destruct (Z.eqb_spec j 0) as [->|Hne]; [img_refl|].
replace (Z.to_nat j) with (Datatypes.S (Z.to_nat (j - 1))) by zlia. cbn [nth_error]. img_apply IH; [img_try (assumption) | img_try (zlia)].
Qed.
Lemma in_combine_seq : forall (l0 : list Z) (s i : nat) vv, In (i, vv) (combine (seq s (length l0)) l0) -> (s <= i)%nat /\ nth_error l0 (i - s) = Some vv.
Proof. clear.
induction l0 as [|y t IH]; intros s i vv H; [img_try (destruct H)|]. cbn [length combine seq] in H. destruct H as [H|H].
- injection H as <- <-. split; [img_try (zlia)|]. rewrite Nat.sub_diag. img_refl.
- destruct (IH _ _ _ H) as [H1 H2]. split; [img_try (zlia)|]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by zlia. cbn [nth_error]. img_exact H2.
Qed.
Lemma flat_map_ext_in {X Y} : forall (f g : X -> list Y) (l0 : list X), (forall x, In x l0 -> f x = g x) -> flat_map f l0 = flat_map g l0.
Proof. clear.
intros f g l0. induction l0 as [|x t IH]; intros H; cbn; [img_refl|]. rewrite H by (img_try (left; img_refl)). rewrite IH; [img_refl|]. intros y Hy. img_apply H. right. img_exact Hy.
Qed.
Lemma nth_error_rev : forall (l0 : list Z) i, (i < length l0)%nat -> nth_error (rev l0) i = nth_error l0 (length l0 - 1 - i).
Proof. clear.
intros l0 i Hi. rewrite (nth_error_nth' (rev l0) 0) by (img_try (rewrite length_rev; img_exact Hi)). rewrite (nth_error_nth' l0 0) by zlia.
f_equal. rewrite rev_nth by img_exact Hi. f_equal. zlia.
Qed.
Section a0.
Variables (NC MU MF : Z) (TOPS : list Z) (FL : list fseg) (HO : list (Z * Z)).
Definition AU : Z := au + NC * csz.
Definition NF' : Z := nf + NC.
Definition NT : Z := Z.of_nat (length TOPS).
Definition rG : region := mkRegion MU AU MF FL HO.
Definition SG : astate := upd_pc c (mkPC maxc (rev TOPS)) (upd_reg c rG S).
Lemma len_factsG : length (st_regions S) = 32%nat /\ length (st_cache S) = 32%nat /\ (Z.to_nat c < 32)%nat.
Proof. pose proof (wf_len_regions _ _ _ _ _ WF). pose proof (wf_len_cache _ _ _ _ _ WF). repeat split; try assumption. clear - HcR. zlia. Qed.
Lemma SG_parts :
(forall c', 0 <= c' -> c' <> c -> reg SG c' = reg S c') /\ reg SG c = rG /\
st_cache_inited SG = st_cache_inited S /\
(forall c', 0 <= c' -> c' <> c -> cache SG c' = cache S c') /\ cache SG c = mkPC maxc (rev TOPS) /\
st_chunks SG = st_chunks S /\ st_secs SG = st_secs S /\ frames SG = frames S /\
st_qthread SG = st_qthread S /\ st_qglobal SG = st_qglobal S /\ st_fs SG = st_fs S /\
st_internal_inited SG = st_internal_inited S /\ st_sec_arr SG = st_sec_arr S /\
st_sec_reserved SG = st_sec_reserved S /\ st_depot SG = st_depot S /\ st_nev SG = st_nev S.
Proof.
pose proof len_factsG as (L1 & L2 & L3). unfold SG, upd_pc, upd_reg. repeat split; try img_refl.
- intros c' Hc' Hne. unfold reg. cbn. img_apply znth_zupd_other; [img_try (clear - HcR; zlia) | img_try (img_exact Hc') | img_try (congruence)].
- unfold reg. cbn. img_apply znth_zupd_same; [img_try (clear - HcR; zlia) | img_try (rewrite L1; img_exact L3)].
- intros c' Hc' Hne. unfold cache. cbn. img_apply znth_zupd_other; [img_try (clear - HcR; zlia) | img_try (img_exact Hc') | img_try (congruence)].
- unfold cache. cbn. img_apply znth_zupd_same; [img_try (clear - HcR; zlia) | img_try (rewrite L2; img_exact L3)].
Qed.
Lemma SG_sec_extents : sec_extents ly SG = sec_extents ly S.
Proof. img_refl. Qed.
Variables (Wd : world tfxsegs) (mdf : Model) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Let rd' : reader := aview tfxsegs (w_H Wd) mem'.
Let m' := mrestrict (w_H Wd) mem'.
Hypothesis WFG : Wf (as_universe B) SG.
Hypothesis HNC : 0 <= NC < 2 ^ 16.
Variables (uq fq : bool).
Hypothesis HUQ : uq = true -> mu < tot /\ mu2 <= kFreeArrayOffset.
Hypothesis HFQ : fq = true -> mf2 <= kFreeArrayMax.
Hypothesis HMU : (MU = mu /\ NC * csz <= mu - au) \/ (MU = mu2 /\ uq = true /\ NC * csz <= mu2 - au).
Hypothesis HMF : (MF = mf) \/ (MF = mf2 /\ fq = true).
Hypothesis HNF : 4 * NF' <= MF.
Hypothesis HNT : (TOPS = [] /\ NC = 0) \/ (NT = n /\ need <= NC).
Hypothesis E_elems : run_elems au csz (Z.to_nat NC) ++ fa_elems csz fr = TOPS ++ fa_elems csz FL.
Hypothesis E_runs : runs_ok FL.
Hypothesis E_rest : fa_len FL = NF' - NT.
Hypothesis HSUB : hsub (w_H Wd) (w_H W).
Hypothesis HBUD : A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20.
Hypothesis HINC : forall i, In i (w_A W) -> In i (w_A Wd).
Hypothesis HSL : A_bytes (w_A W) + EV_A <= abudget S.
Hypothesis HL : ALedger tfxsegs ly SG mdf.
Hypothesis HMW : amwf mdf.
Definition W_FEn (a : Z) : Prop := FAv + 4 * nf <= a < FAv + 4 * NF'.
Definition XC (a : Z) : Prop :=
(Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 64) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) \/
W_FEn a \/ (uq = true /\ W_UW a) \/ (MU = mu2 /\ W_USH a) \/ (fq = true /\ W_FW a) \/ (MF = mf2 /\ W_FSH a).
Hypothesis MEQ : forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) -> ~ XC (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis HVIS : forall x : word, ~ XC (bv_unsigned x) -> w_H Wd x = w_H W x.
Hypothesis NOREM : forall x : word, mem0 x <> None -> mem' x <> None \/ (MU = mu /\ uq = true /\ W_UW (bv_unsigned x)) \/ (MF = mf /\ fq = true /\ W_FW (bv_unsigned x)).
Hypothesis PRS : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wd) mem' a.
Hypothesis FAP : forall a, FAv <= a < FAv + MF -> apresent (w_H Wd) mem' a.
Hypothesis DSTP : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H Wd) mem' a.
Hypothesis UWP : MU = mu2 -> forall a, RBv <= a < RBv + mu2 -> apresent (w_H Wd) mem' a.
Hypothesis PC : P_cells Wd NT (NF' - NT) MF AU MU mem'.
Hypothesis CPY : forall j, 0 <= j < 4 * NT -> mem' (w64 (DSTv + j)) = mem' (w64 (FAv + 4 * (NF' - NT) + j)).
Hypothesis FILL : forall i, 0 <= i < NC -> val_mem tfxsegs m' (FAv + 4 * NF' - 4 - 4 * i) 4 ((au + i * csz) / 16).
Hypothesis USHV : MU = mu2 -> forall x : word, W_USH (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 250) /\ w_H Wd x = false.
Hypothesis FSHV : MF = mf2 -> forall x : word, W_FSH (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 250) /\ w_H Wd x = false.
Hypothesis VISLOC : forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
0 <= aeval B ly (fst r) + i < 2 ^ 64 /\
(ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize -> prim_committed_at ly S (aeval B ly (fst r) + i)).
Let MA : ARm B ly S rd0 := proj1 HAR.
Ltac drop4 := clear3;
try match type of HUQ with uq = true -> _ => clear HUQ end; try match type of HFQ with fq = true -> _ => clear HFQ end;
try match type of HMU with _ \/ _ => clear HMU end; try match type of HMF with _ \/ _ => clear HMF end;
try match type of HNT with _ \/ _ => clear HNT end.
Ltac lia4 := drop4; zlia.
Ltac nia4 := drop4; nia.
Lemma geo : kHighMemBeg <= RBv /\ RBv + 2 ^ 32 <= ASAN_CEIL /\ FAv = RBv + kFreeArrayOffset /\ adr = RBv + mu /\ fadr = FAv + mf /\
0 <= mu /\ mu2 = mu + kUserMapSize /\ MU <= kFreeArrayOffset /\ 0 <= mf /\ MF <= kFreeArrayMax /\ mf <= MF /\ mu <= MU /\
kHighShadowBeg <= sha /\ sha + 32768 <= kHighShadowEnd /\ kHighShadowBeg <= shf /\ shf + 32768 <= kHighShadowEnd /\
0 <= nf /\ 4 * nf <= mf /\ au <= AU <= MU /\ 0 <= au /\ 0 <= NT <= NF' /\ NT <= 8 /\ nf <= NF'.
Proof.
pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 &
G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32 & G33 & _).
pose proof derived_rangesR as DR. pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hmf as [[M0 M1] M2]. pose proof Hnf as [F0 F1].
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite <- RBv_is in Q5.
unfold AU, NF', NT in *. unfold kHighShadowBeg, kHighShadowEnd.
repeat split; try assumption; try (clear - DR; tauto);
try (clear - HMU HUQ U0 U1 U2 G15 HNC K4; unfold kUserMapSize in *; destruct HMU as [[EM X]|(EM & EQ & X)]; [|img_try (specialize (HUQ EQ))]; nia);
try (clear - HMF HFQ M0 M1 G33; unfold kFreeArrayMapSize in *; destruct HMF as [EM|[EM EQ]]; [|img_try (specialize (HFQ EQ))]; zlia);
try (clear - G14; zlia); try (clear - G30; zlia);
try (clear - HNT HNC K3 G1 F0 Hneed; destruct HNT as [[-> ->]|[E L]]; cbn in *; zlia).
Qed.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - RSTACK <= a < sp0) -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ra N1 N2. unfold rd', rd0, aview, mbyte, mrestrict.
rewrite (HVIS (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_exact Ra; img_exact N2)).
rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_exact Ra; assumption)). img_refl.
Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfxsegs B ly S W mem0 md0 a HAR Ho) as Ra.
ceil.
pose proof (AR_stack_law_ok tfxsegs B ly S W mem0 md0 a HAR) as NS. destruct Hsp as (S1 & S3 & S4).
img_apply AGREE0; [img_try (clear - Ra; zlia) | | img_try (img_exact Hx)].
intros Hs. img_apply NS; [|img_try (img_exact Ho)]. clear - Hs S1 S3. unfold RSTACK, sp0 in *. lia4.
Qed.
Lemma XC_where : forall a, XC a ->
(T <= a < T + kThreadObjSize /\ T + t_cache + 80 * c <= a) \/ (RGv <= a < RGv + 128) \/
(RBv <= a < RBv + 2 ^ 32 /\ (W_FEn a \/ (uq = true /\ W_UW a) \/ (fq = true /\ W_FW a))) \/
(kHighShadowBeg <= a < kHighShadowEnd /\ ((MU = mu2 /\ W_USH a) \/ (MF = mf2 /\ W_FSH a))).
Proof.
intros a Hx. pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). pose proof geo as GE. pose proof Hmf as [[M0 M1] _].
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold XC, DSTv, W_FEn, W_UW, W_USH, W_FW, W_FSH in *.
clear - Hx DR K3 GE HNF HcR HUQ HFQ M0 M1 G33. unfold Pr, NF' in *. numconst. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, kFreeArrayOffset, kHighShadowBeg, kHighShadowEnd in *. unfold T in *.
img_change (262144 / 8) with 32768 in *.
destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[[EQ Hx]|[[EQ Hx]|[[EQ Hx]|[EQ Hx]]]]]]]]]];
[ img_try (left; lia4) | img_try (left; lia4) | img_try (right; left; lia4) | img_try (left; lia4) | img_try (left; lia4)
| img_try (right; right; left; split; [lia4 | left; img_exact Hx])
| img_try (specialize (HUQ EQ); right; right; left; split; [lia4 | right; left; img_exact (conj EQ Hx)])
| img_try (right; right; right; split; [lia4 | left; img_exact (conj EQ Hx)])
| img_try (specialize (HFQ EQ); right; right; left; split; [lia4 | right; right; img_exact (conj EQ Hx)])
| img_try (right; right; right; split; [lia4 | right; img_exact (conj EQ Hx)]) ].
Qed.
Lemma Z_img : forall a, (0x10000 <= a < (0x5ff000 + D_1000) \/ 0x7fff7000 <= a < 0x2008fff7000) -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & _). pose proof derived_rangesR as DR. pose proof geo as GE.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [Hx _]]]]; clear - Ha Hx TI TH DR GE; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; try unfold T in *; zlia.
Qed.
Lemma Z_band : forall a, 0x7fff7000 <= a < kHighMemBeg -> ~ (MU = mu2 /\ W_USH a) -> ~ (MF = mf2 /\ W_FSH a) -> ~ XC a.
Proof.
intros a Ha N1 N2 Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & _). pose proof derived_rangesR as DR. pose proof geo as GE.
pose proof (zone3_apart_hsh _ _ a F1) as TH.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [_ [Hx|Hx]]]]]; [| | | img_try (img_exact (N1 Hx)) | img_try (img_exact (N2 Hx))]; clear - Ha Hx TH DR GE; numconst; try unfold T in *; zlia.
Qed.
Lemma Z_T : forall a, T <= a < T + kThreadObjSize -> (a < T + t_cache + 80 * c \/ Pr + 80 <= a) -> ~ (T + 2768 <= a < T + 2800) -> ~ (T + 2872 <= a < T + 2888) -> ~ XC a.
Proof.
intros a Ha H1 H2 H3 Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof class_facts as (_ & _ & K3 & _). pose proof geo as GE.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold XC, DSTv in Hx.
destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[[EQu Hx]|[[EQu Hx]|[[EQf Hx]|[EQf Hx]]]]]]]]]]; unfold W_FEn, W_UW, W_USH, W_FW, W_FSH in Hx;
first [pose proof (HUQ EQu) as [HU1 HU2] | pose proof I as HU2]; first [pose proof (HFQ EQf) as HF1 | pose proof I as HF1];
clear - Ha H1 H2 H3 Hx DR F1 F2 F3 F4 F5 F6 PT Q1 Q2 GE K3 HNF HU2 HF1 G33; unfold Pr, NF' in *; numconst;
unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax, kHighShadowBeg, kHighShadowEnd in *; img_change (262144 / 8) with 32768 in *; try unfold T in *; zlia.
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (RGv <= a < RGv + 128) -> ~ W_FEn a -> ~ (uq = true /\ W_UW a) -> ~ (fq = true /\ W_FW a) -> ~ XC a.
Proof.
intros a Ha HR N1 N2 N3 Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & F2 & F3 & _). pose proof geo as GE.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
destruct Hx as [[Hx _] | [Hx | [[_ [Hx|[Hx|Hx]]] | [Hx _]]]]; [| | img_try (img_exact (N1 Hx)) | img_try (img_exact (N2 Hx)) | img_try (img_exact (N3 Hx)) |]; clear - Ha HR Hx F1 F3 PT GE; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; try unfold T in *; zlia.
Qed.
Lemma Z_high : forall a, kHighMemBeg <= a -> ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) -> ~ XC a.
Proof.
intros a Ha NT0 NP Hx. apply XC_where in Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof geo as GE.
pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [Hx _]]]]; clear - Ha NT0 NP Hx DR F5 GE R1 R2; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; zlia.
Qed.
Lemma Z_out : forall a, ~ (kHighShadowBeg <= a < kHighShadowEnd) -> ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) -> ~ XC a.
Proof.
intros a Ha NT0 NP Hx. apply XC_where in Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof geo as GE.
pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [Hx _]]]]; clear - Ha NT0 NP Hx DR F5 GE R1 R2; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; zlia.
Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat ->
fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros i e a He Hi Ha. pose proof (lo_app ly LY) as HI. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ i _ HI He) as IH. cbv beta in IH. unfold in_app in IH.
assert (D : forall j e', nth_error (owned_extents ly) j = Some e' -> (j = 0 \/ j = 2)%nat -> zdisjoint e e').
{ intros j e' He' Hj. unfold static_extents in HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (img_try (apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto)).
destruct (Nat.lt_ge_cases i j) as [L|L].
- replace j with (i + Datatypes.S (j - i - 1))%nat in He' by (img_try (clear - L; zlia)). img_exact (pairwise_ij _ _ _ _ _ _ HD' He He').
- img_apply zdisjoint_sym. assert (j <> i) by (img_try (intros ->; clear - Hi Hj; zlia)). replace i with (j + Datatypes.S (i - j - 1))%nat in He by (img_try (clear - L H; zlia)). img_exact (pairwise_ij _ _ _ _ _ _ HD' He' He). }
pose proof (D 0%nat _ eq_refl ltac:(img_try (clear; zlia))) as D0. pose proof (D 2%nat _ eq_refl ltac:(img_try (clear; zlia))) as D2.
unfold zdisjoint in D0, D2. cbn [fst snd] in D0, D2.
img_apply Z_out; unfold T in *; clear - IH Ha D0 D2; numconst; zlia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros e a He Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (owned_extents ly) -> zdisjoint e e').
{ intros e' He'. img_exact (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He ltac:(img_try (unfold static_extents; img_apply in_app_iff; left; img_exact He'))). }
pose proof (D (ly_prim ly, kPrimResvSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as D0.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as D2.
unfold zdisjoint in D0, D2. cbn [fst snd] in D0, D2.
img_apply Z_out; unfold T in *; clear - HIA Ha D0 D2; numconst; zlia.
Qed.
Lemma Z_user : forall c' x a, 1 <= c' <= 31 -> 0 <= x -> x <= rg_mapped_user (reg S c') -> region_base ly c' <= a < region_base ly c' + x -> ~ XC a.
Proof.
intros c' x a Hc' Hx0 Hx Ha. pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _). pose proof derived_rangesR as DR. pose proof geo as GE.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF Hc') as MB.
unfold region_base in Ha, R1, R2. rewrite region_off_eq in Ha, R1, R2 by lia4.
assert (SEP : c' = c \/ (ly_space ly + c' * 2 ^ 32 + 2 ^ 32 <= RBv \/ RBv + 2 ^ 32 <= ly_space ly + c' * 2 ^ 32)).
{ destruct (Z.eq_dec c' c) as [->|NE]; [img_try (left; img_refl) | img_try (right)]. unfold RBv, SB. clear - Hc' HcR NE. nia4. }
img_apply Z_prim.
- clear - Hx0 Hx Ha R1 R2 MB. unfold kUserMapSize, EV_MAX in MB. lia4.
- unfold RGv, SB in *. clear - Hc' Hx0 Hx Ha HcR MB. numconst. unfold kUserMapSize, EV_MAX in MB. nia4.
- unfold W_FEn. rewrite (proj1 (proj2 (proj2 GE))). destruct SEP as [->|SEP]; [img_try (rewrite <- Hmu_def in Hx; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; pose proof I as SEP)|];
clear - Hx0 Hx Ha MB GE HNF SEP; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMax in *; zlia.
- intros [_ HW]. revert HW. unfold W_UW. rewrite (proj1 (proj2 (proj2 (proj2 GE)))). destruct SEP as [->|SEP]; [img_try (rewrite <- Hmu_def in Hx; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; pose proof I as SEP)|];
clear - Hx0 Hx Ha MB GE SEP; unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *; zlia.
- intros [EQ HW]. pose proof (HFQ EQ) as HF1. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
revert HW. unfold W_FW. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 GE))))), (proj1 (proj2 (proj2 GE))). destruct SEP as [->|SEP]; [img_try (rewrite <- Hmu_def in Hx; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; pose proof I as SEP)|];
clear - Hx0 Hx Ha MB GE SEP HF1 G33; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
Qed.
Lemma UW_uncommitted : uq = true -> forall a, W_UW a -> ~ prim_committed_at ly S a.
Proof.
intros EQ a Ha [Hr | (c' & Hc' & [Hu | Hf])]; pose proof (HUQ EQ) as [HU1 HU2]; unfold in_zr, W_UW in *; cbn [fst snd] in *; pose proof geo as GE; pose proof derived_rangesR as DR.
- unfold ly_rinfo in Hr. unfold RGv, RBv, SB in *. clear - Ha Hr GE HcR HU2. numconst. unfold kUserMapSize, kFreeArrayOffset in *. nia4.
- pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF Hc') as MB. unfold region_base in Hu. rewrite region_off_eq in Hu by lia4.
destruct (Z.eq_dec c' c) as [->|NE]; [img_try (rewrite <- Hmu_def in Hu; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; clear - Ha Hu GE; zlia)|].
unfold RBv, SB in *. clear - Ha Hu GE Hc' HcR NE MB HU2. numconst. unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. nia4.
- pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA0 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
unfold fa_base in Hf. rewrite region_off_eq in Hf by lia4. unfold RBv, SB in *.
clear - Ha Hf GE Hc' HcR FA0 FB HU2. numconst. unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMax in *. nia4.
Qed.
Lemma FW_uncommitted : fq = true -> forall a, W_FW a -> ~ prim_committed_at ly S a.
Proof.
intros EQ a Ha [Hr | (c' & Hc' & [Hu | Hf])]; pose proof (HFQ EQ) as HF1; unfold in_zr, W_FW in *; cbn [fst snd] in *; pose proof geo as GE; pose proof derived_rangesR as DR.
- unfold ly_rinfo in Hr. unfold RGv, FAv, RBv, SB in *. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _). clear - Ha Hr GE HcR HF1 G33. numconst. unfold kFreeArrayMapSize, kFreeArrayMax, kFreeArrayOffset in *. nia4.
- pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF Hc') as MB. unfold region_base in Hu. rewrite region_off_eq in Hu by lia4.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _). unfold FAv, RBv, SB in *. clear - Ha Hu GE Hc' HcR MB HF1 G33. numconst. unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. nia4.
- pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA0 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
unfold fa_base in Hf. rewrite region_off_eq in Hf by lia4.
destruct (Z.eq_dec c' c) as [->|NE]; [img_try (rewrite <- Hmf_def in Hf; unfold FAv, RBv, SB in *; rewrite ?region_off_eq in * by lia4; clear - Ha Hf GE; zlia)|].
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _). unfold FAv, RBv, SB in *. clear - Ha Hf GE Hc' HcR NE FA0 FB HF1 G33. numconst. unfold kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. nia4.
Qed.
Lemma VIS_MONO : forall a, 0 <= a < 2 ^ 64 -> rd0 a <> None -> ~ (MU = mu /\ uq = true /\ W_UW a) -> ~ (MF = mf /\ fq = true /\ W_FW a) -> rd' a <> None.
Proof.
clear - HSUB NOREM. intros a Ra HV N1 N2. unfold rd', rd0, aview, mbyte, mrestrict in *.
destruct (w_H W (Z_to_bv 64 a)) eqn:Eh.
- exfalso. img_apply HV. cbn. unfold seg_rom. rewrite (memory_read1_hidden tfxsegs (w_H W) (w_Hoff W) _ Eh). img_refl.
- destruct (w_H Wd (Z_to_bv 64 a)) eqn:E'; [img_try (rewrite (HSUB _ E') in Eh; discriminate)|].
destruct (mem0 (Z_to_bv 64 a)) as [b|] eqn:Em.
+ destruct (NOREM (Z_to_bv 64 a) ltac:(img_try (rewrite Em; discriminate))) as [NN | [X|X]].
* destruct (mem' (Z_to_bv 64 a)) as [b'|]; [img_try (cbn; discriminate) | img_try (exfalso; img_exact (NN eq_refl))].
* exfalso. img_apply N1. rewrite unsigned_lit_small in X by img_exact Ra. img_exact X.
* exfalso. img_apply N2. rewrite unsigned_lit_small in X by img_exact Ra. img_exact X.
+ destruct (mem' (Z_to_bv 64 a)) as [b'|]; [img_try (cbn; discriminate) | img_try (img_exact HV)].
Qed.
Lemma apresent_vis : forall a, apresent (w_H Wd) mem' a -> rd' a <> None.
Proof. intros a [Hh [b Hb]]. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma aview_copy : forall a b, apresent (w_H Wd) mem' a -> apresent (w_H Wd) mem' b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
mem' (w64 a) = mem' (w64 b) -> rd' a = rd' b.
Proof.
intros a b [Ha _] [Hb [xb Hxb]] Ra Rb E. unfold rd', aview, mbyte, mrestrict. unfold w64 in E. rewrite Ha, Hb, E, Hxb. img_refl.
Qed.
Lemma vis_keep : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. img_apply Forall_forall. intros r Hr i Hi.
assert (IN : In r (ajunk B ly S ++ aareas S ++ aclient S)) by (img_try (rewrite !in_app_iff; destruct H as [H|[H|H]]; [img_try (left) | img_try (right; left) | img_try (right; right)]; img_exact (H r Hr))).
assert (RV : rd0 (aeval B ly (fst r) + i) <> None).
{ destruct H as [H|[H|H]]; [img_try (img_exact (proj1 (Forall_forall _ _) (am_junk _ _ _ _ MA) r (H r Hr) i Hi)) | img_try (img_exact (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) r (H r Hr) i Hi))
| img_try (img_exact (proj1 (Forall_forall _ _) (am_client _ _ _ _ MA) r (H r Hr) i Hi))]. }
destruct (VISLOC r i IN Hi) as [Ra LOC]. pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2. pose proof geo as GE.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
img_apply (VIS_MONO _ Ra RV); intros (E & EQ & Hw); [img_try (img_apply (UW_uncommitted EQ _ Hw)) | img_try (img_apply (FW_uncommitted EQ _ Hw))]; img_apply LOC; [img_try (pose proof (HUQ EQ) as [HU1 HU2]; pose proof I as HF1) | img_try (pose proof (HFQ EQ) as HF1; pose proof I as HU2)]; unfold W_UW, W_FW in Hw;
clear - Hw R1 R2 GE HU2 HF1 G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun cc => lo <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. img_apply Forall_forall. intros cc Hc.
pose proof (proj1 (Forall_forall _ _) RNG cc Hc) as [R1 R2]. cbv beta in R1, R2.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc)))|].
intros k Hk. img_apply AGX.
- img_exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- img_apply LOC. clear - Hk R1 R2. lia4.
Qed.
Lemma keep_cell : forall cc lo len, loc_ok lo len -> In cc (acells B ly S) ->
lo <= aeval B ly (c_at cc) -> aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len -> cell_holds B ly rd' cc.
Proof.
intros cc lo len LOC Hc R1 R2. img_exact (proj1 (Forall_forall _ _) (keep_cells [cc] lo len LOC ltac:(img_try (intros x [<-|[]]; img_exact Hc)) ltac:(img_try (constructor; [img_try (split; assumption) | img_try (constructor)]))) cc (or_introl eq_refl)).
Qed.
Ltac fcons' := img_apply Forall_cons; [img_try (cbn; lia4)|].
Lemma PCv : let m := m' in
val_mem tfxsegs m Pr 4 NT /\ val_mem tfxsegs m (Pr + 4) 4 maxc /\ val_mem tfxsegs m (Pr + 8) 8 csz /\
val_mem tfxsegs m RGv 8 0 /\ val_mem tfxsegs m (RGv + 8) 8 0 /\ val_mem tfxsegs m (RGv + 16) 8 (NF' - NT) /\
val_mem tfxsegs m (RGv + 24) 8 MF /\ val_mem tfxsegs m (RGv + 32) 8 AU /\ val_mem tfxsegs m (RGv + 40) 8 0 /\
val_mem tfxsegs m (RGv + 48) 8 MU /\ val_mem tfxsegs m (RGv + 56) 8 0 /\ val_mem tfxsegs m (RGv + 68) 1 0.
Proof. img_exact (proj2 PC). Qed.
Lemma PRW : forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H Wd) mem' a.
Proof. img_exact (proj1 PC). Qed.
Definition EL : list Z := run_elems au csz (Z.to_nat NC) ++ fa_elems csz fr.
Lemma EL_len : Z.of_nat (length EL) = NF'.
Proof.
pose proof cls_wfR as C0. pose proof (fa_elems_length csz (rg_free (reg S c)) (wr_runs _ _ _ _ _ _ C0)) as L.
unfold EL, NF'. rewrite length_app, run_elems_length. unfold fr. rewrite <- Hnf_def in L. pose proof HNC as [N0 _]. clear - L N0. lia4.
Qed.
Lemma entry_rd : forall j vv, 0 <= j < NF' -> nth_error EL (Z.to_nat (NF' - 1 - j)) = Some vv -> rd32 rd' (FAv + 4 * j) (vv / 16).
Proof.
intros j vv Hj Hnth k Hk. pose proof geo as GE. pose proof HNC as [N0 N1]. pose proof Hnf as [F0 F1]. pose proof derived_rangesR as DR.
pose proof reg_facts as (_ & _ & _ & _ & RU). assert (HNT0 : 0 <= NT) by (img_try (unfold NT; clear; zlia)).
destruct (Z_lt_le_dec (NF' - 1 - j) NC) as [NEW|OLD].
-
unfold EL in Hnth. rewrite nth_error_app1 in Hnth by (img_try (rewrite run_elems_length; clear - NEW Hj N0 HNT0; zlia)).
rewrite nth_error_run_elems in Hnth by (img_try (clear - NEW Hj N0 HNT0; zlia)). injection Hnth as <-.
pose proof (FILL (NF' - 1 - j) ltac:(img_try (clear - NEW Hj GE; zlia))) as V. unfold rd'. unfold aview.
replace (FAv + 4 * NF' - 4 - 4 * (NF' - 1 - j)) with (FAv + 4 * j) in V by lia4. rewrite Z2Nat.id by (img_try (clear - Hj GE; zlia)).
unfold m' in V. rewrite (V k Hk). cbn [option_map]. rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [img_try (f_equal; f_equal; clear - Hj GE; zlia)|]. unfold YG0h.le_byte. img_apply Z.mod_pos_bound. lia4.
-
unfold EL in Hnth. rewrite nth_error_app2 in Hnth by (img_try (rewrite run_elems_length; clear - OLD; zlia)). rewrite run_elems_length in Hnth.
assert (Hjn : 0 <= j < nf) by (img_try (unfold NF' in *; clear - OLD Hj GE N0; zlia)).
assert (FN : fa_nth (class_size c) (rg_free (reg S c)) (fa_len (rg_free (reg S c)) - 1 - j) = Some vv).
{ rewrite <- Hnf_def, <- Hcsz. rewrite fa_nth_elems by (img_try (img_exact RU || (clear - Hjn; zlia))). unfold fr in Hnth. rewrite <- Hnth. f_equal. unfold NF'. clear - OLD Hjn N0. lia4. }
pose proof (am_fa _ _ _ _ MA c j vv HcR ltac:(img_try (rewrite <- Hnf_def; img_exact Hjn)) FN k Hk) as RD. rewrite <- FAv_is in RD.
rewrite AGX; [img_try (img_exact RD) | img_try (eapply own_fa; [img_exact MA | img_exact HcR | rewrite <- FAv_is; clear - Hjn Hk F1 GE; unfold kFreeArrayMax in *; zlia]) |].
img_apply Z_prim.
+ pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2. clear - Hjn Hk F1 GE R1 R2. unfold kFreeArrayOffset, kFreeArrayMax in *. lia4.
+ unfold RGv, FAv, RBv, SB in *. clear - Hjn Hk F1 GE HcR. numconst. unfold kFreeArrayOffset, kFreeArrayMax in *. lia4.
+ unfold W_FEn. clear - Hjn Hk; zlia.
+ intros [EQ HW]. pose proof (HUQ EQ) as [_ HU2]. unfold W_UW in HW. clear - Hjn Hk GE F1 HW HU2; unfold kFreeArrayOffset, kUserMapSize in *; zlia.
+ intros [_ HW]. unfold W_FW in HW. clear - Hjn Hk GE F1 HW; zlia.
Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells SG) (zseq 1 31)).
Proof.
pose proof SG_parts as (Rreg & Rc & _). img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof derived_rangesR as DR. pose proof PCv as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12).
pose proof geo as GE.
destruct (Z.eq_dec c' c) as [->|Hne].
- unfold region_cells. rewrite Rc. unfold rG. cbn [rg_free rg_mapped_fa rg_alloc_user rg_mapped_user]. rewrite E_rest.
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = RGv + d) by (img_try (intros d; cbn; unfold RGv, SB; lia4)).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = RGv + 0) by (img_try (cbn; unfold RGv, SB; lia4)).
repeat (img_apply Forall_cons; [img_try (img_apply val_mem_cell; rewrite ?ER, ?ER0; cbn [aeval];
first [ img_exact (val_mem_at m' _ _ _ _ (Z.add_0_r RGv) V4) | img_exact V5 | img_exact V6 | img_exact V7 | img_exact V8 | img_exact V9 | img_exact V10 | img_exact V11 | img_exact V12 ]) |]).
img_apply Forall_nil.
- replace (region_cells SG c') with (region_cells S c') by (img_try (unfold region_cells; rewrite (Rreg c') by (clear - Hc' Hne; zlia); img_refl)).
pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2.
img_apply (keep_cells _ (ly_space ly + kRegionInfoOff + 128 * c') 128).
+ intros a Ha. assert (LO : RBv + 2 ^ 32 <= a) by (img_try (unfold RGv, FAv, RBv, SB in *; clear - Ha Hc' DR HcR; numconst; zlia)).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
img_apply Z_prim.
* clear - Ha Hc' F3 F4 F5 DR HcR; numconst; zlia.
* unfold RGv, SB in *; clear - Ha Hc' Hne HcR; numconst; zlia.
* unfold W_FEn. clear - LO GE HNF; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
* intros [EQ HW]. pose proof (HUQ EQ) as [_ HU2]. unfold W_UW in HW. clear - LO GE HW HU2; unfold kUserMapSize, kFreeArrayOffset in *; zlia.
* intros [EQ HW]. pose proof (HFQ EQ) as HF1. unfold W_FW in HW. clear - LO GE HW HF1 G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
+ intros x Hx. unfold acells. img_apply in_app_iff. left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; lia4) | img_try (img_exact Hx)].
+ unfold region_cells, kRegionInfoOff. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma slot_cell : forall (i : nat) vv, In (i, vv) (combine (seq 0 (length (rev TOPS))) (rev TOPS)) ->
cell_holds B ly rd' (z4 (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat i)) (vv / 16)).
Proof.
intros i vv Hin. apply in_combine_seq in Hin as [_ Hnth]. rewrite Nat.sub_0_r in Hnth.
assert (Hi : (i < length TOPS)%nat). { rewrite <- (length_rev TOPS). img_apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
rewrite nth_error_rev in Hnth by img_exact Hi.
pose proof geo as GE. pose proof class_facts as (_ & _ & K3 & _). pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & _).
assert (EN : nth_error EL (Z.to_nat (NF' - 1 - (NF' - NT + Z.of_nat i))) = Some vv).
{ fold EL in E_elems. rewrite E_elems. rewrite nth_error_app1 by (img_try (unfold NT; clear - Hi; zlia)). rewrite <- Hnth. f_equal. unfold NT. clear - Hi. lia4. }
assert (HjR : 0 <= NF' - NT + Z.of_nat i < NF') by (img_try (unfold NT in *; clear - Hi GE; zlia)).
pose proof (entry_rd (NF' - NT + Z.of_nat i) vv HjR EN) as RD.
unfold cell_holds. cbn [c_at c_val c_w aeval aoff z4 c4]. intros k Hk.
rewrite (aview_copy (ly_T ly + (t_cache + 80 * c + (16 + 4 * Z.of_nat i)) + Z.of_nat k) (FAv + 4 * (NF' - NT + Z.of_nat i) + Z.of_nat k)).
- rewrite <- (RD k Hk). img_refl.
- img_apply DSTP. unfold NT in *. clear - Hi Hk K3 GE. unfold DSTv, Pr. lia4.
- img_apply FAP. unfold NT in *. clear - Hi Hk GE HNF. lia4.
- clear - DR F1 F2 Hi Hk K3 GE. unfold NT, Pr in *. numconst. lia4.
- unfold NT in *. clear - DR Hi Hk GE HNF. numconst. unfold kFreeArrayMax in *. lia4.
- replace (ly_T ly + (t_cache + 80 * c + (16 + 4 * Z.of_nat i)) + Z.of_nat k) with (DSTv + (4 * Z.of_nat i + Z.of_nat k)) by (img_try (unfold DSTv, Pr, T; lia4)).
replace (FAv + 4 * (NF' - NT + Z.of_nat i) + Z.of_nat k) with (FAv + 4 * (NF' - NT) + (4 * Z.of_nat i + Z.of_nat k)) by lia4. img_apply CPY. unfold NT in *. clear - Hi Hk. lia4.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells SG) (zseq 1 31)).
Proof.
pose proof SG_parts as (_ & _ & Rinit & Rother & Rcl & _). img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof derived_rangesR as DR. pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof PCv as (V1 & V2 & V3 & _).
destruct (Z.eq_dec c' c) as [->|Hne].
- unfold cache_cells. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks pc_max].
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c)) d) = Pr + d) by (img_try (intros d; cbn; unfold Pr; lia4)).
constructor. { img_apply val_mem_cell. cbn [aeval]. img_apply (val_mem_at m' _ Pr); [img_try (unfold Pr; lia4)|]. rewrite length_rev. fold NT. img_exact V1. }
constructor. { img_apply val_mem_cell. rewrite EP. cbn [aeval]. rewrite <- Hmax. img_exact V2. }
constructor. { img_apply val_mem_cell. rewrite EP. cbn [aeval]. rewrite <- Hcsz. img_exact V3. }
img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv). cbn [fst snd]. img_exact (slot_cell i vv Hiv).
- replace (cache_cells SG c') with (cache_cells S c') by (img_try (unfold cache_cells; rewrite Rinit, (Rother c') by lia4; img_refl)).
img_apply (keep_cells _ (T + t_cache + 80 * c') 80).
+ intros a Ha. img_apply Z_T; unfold Pr in *; unfold T in *; clear - Ha Hc' Hne HcR DR K3; numconst; nia.
+ intros x Hx. unfold acells. img_apply in_app_iff. right. img_apply in_app_iff. left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; lia4) | img_try (img_exact Hx)].
+ unfold cache_cells. pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_try (lia4))) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c' ltac:(img_try (lia4))) as (_ & _ & _ & K4' & _). unfold T.
destruct (st_cache_inited S).
* destruct WC as [PM PL]. unfold t_cache. repeat fcons'. img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. clear - Hiv PL K4'. lia4.
* unfold t_cache. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks SG)).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & Rch & _). rewrite Rch.
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_try (lia4))) as (Q1 & Q2 & Q3).
img_apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
+ intros a Ha. destruct (ck_beg k) as [|o|r o|c'' p] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF (prim_class o) ltac:(img_try (lia4)))) as AL.
apply (Z_user (prim_class o) (rg_alloc_user (reg S (prim_class o)))); [img_try (lia4) | img_try (lia4) | img_try (lia4) | img_try (lia4)].
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _). img_apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [img_try (img_exact Hin) | img_try (cbn [fst snd]; clear - Ha X2 X3 G8 Q2 G5; unfold kPage in *; zlia)].
+ intros x Hx. unfold acells. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
+ assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p]; try solve [destruct GG]; cbn; lia4. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p]; try solve [destruct GG]; cbn; lia4. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by img_refl.
clear GG. unfold chunk_cells, kChunkHeaderSize. img_apply Forall_app. split.
* repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia4)|]). img_apply Forall_nil.
* destruct (Z.eqb_spec (ck_rz k) 16); [img_try (img_apply Forall_nil)|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|img_try (lia4)]. lia4. }
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia4)|]). img_apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & Rch & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
replace (sec_cells SG) with (sec_cells S) by (img_try (unfold sec_cells; rewrite Rres, Rarr, Rch; img_refl)).
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 3 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok 0x10000 (0x5ef000 + D_1000)) by (img_try (intros a Ha; img_apply Z_img; lia4)).
unfold sec_cells in *.
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_reserved; lia4 | cbn; rewrite EI; unfold TFX_INST, o_sec_reserved, kHighShadowBeg; lia4])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_n; lia4 | cbn; rewrite EI; unfold TFX_INST, o_sec_n, kHighShadowBeg; lia4])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_mutex; lia4 | cbn; rewrite EI; unfold TFX_INST, o_sec_mutex, kHighShadowBeg; lia4])|].
img_apply Forall_app. split.
- img_apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
+ intros a Ha. img_apply (Z_ext 1 (ly_Q ly, kPtrArrayResv)); [img_refl | img_try (lia4) | img_try (cbn [fst snd]; img_exact Ha)].
+ intros x Hx. img_apply INC. do 3 right. img_apply in_app_iff. left. img_exact Hx.
+ img_apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia4.
- img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_try (lia4))) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try img_apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
img_apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
+ intros a Ha. img_apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [img_try (img_exact Gin) | img_try (cbn [fst snd]; img_exact Ha)].
+ intros x Hx. img_apply INC. do 3 right. img_apply in_app_iff. right. img_apply in_flat_map. exists k. rewrite Eb. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
+ unfold kPage in *. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [img_try (img_apply Forall_nil)|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; lia4))) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b; split; [img_refl | img_try (img_apply Hincl; left; img_refl)])).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)). { apply Z.mod_divide in X2 as [q Hq]; [|img_try (lia4)]. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA. rewrite CS in AA. apply Z.mod_divide in AA as [q' Hq']; [|img_try (lia4)]. nia4. }
intros a Ha. img_apply (Z_user kBatchClass (rg_alloc_user (reg S kBatchClass))); [img_try (unfold kBatchClass; lia4) | img_try (lia4) | img_try (lia4) |].
unfold region_base. (subst x; cbv beta). unfold kBatchBytes in Ha. lia4. }
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; left; img_refl | cbn; lia4 | cbn; unfold kBatchBytes; lia4])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; left; img_refl | cbn; lia4 | cbn; unfold kBatchBytes; lia4])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; right; left; img_refl | cbn; lia4 | cbn; unfold kBatchBytes; lia4])|].
img_apply Forall_app. split.
- img_apply (keep_cells _ _ _ LOC).
+ intros y Hy. img_apply INC. do 3 right. img_apply in_app_iff. left. img_exact Hy.
+ img_apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. lia4.
- img_apply IH; [img_try (intros y Hy; img_apply Hincl; right; img_exact Hy) | img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; right; img_exact Hy)].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells SG) with (quar_cells S) by (img_try (unfold quar_cells; rewrite Rqt, Rqg; img_refl)).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 4 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
pose proof (ts_inst B TS) as EI. pose proof derived_rangesR as DR.
assert (LOCI : loc_ok 0x10000 (0x5ef000 + D_1000)) by (img_try (intros a Ha; img_apply Z_img; lia4)).
assert (LOCT : loc_ok (T + t_qc) 32) by (img_try (intros a Ha; img_apply Z_T; unfold t_qc in *; unfold Pr, T in *; clear - Ha DR HcR; numconst; zlia)).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; left; img_refl | cbn; rewrite EI; unfold TFX_INST; lia4 | cbn; rewrite EI; unfold TFX_INST, kHighShadowBeg; lia4])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST; lia4 | cbn; rewrite EI; unfold TFX_INST, kHighShadowBeg; lia4])|].
img_apply Forall_app. split.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOCT); [img_apply INC; right; right; img_apply in_app_iff; left; cbn; tauto | cbn; unfold T; lia4 | cbn; unfold T; lia4])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; left; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. left. do 4 right. img_exact Hy.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; right; img_apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; unfold TFX_INST; lia4 | cbn; rewrite EI; unfold TFX_INST, kHighShadowBeg; lia4])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; right; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. right. do 4 right. img_exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells SG) with (fs_cells S) by (img_try (unfold fs_cells; rewrite Rfs; img_refl)).
img_apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_try (lia4) | img_try (cbn [fst snd]; img_exact Ha)].
- intros x Hx. unfold acells. do 5 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. img_apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia4.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
replace (depot_cells ly SG) with (depot_cells ly S) by (img_try (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; img_refl)).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
img_apply (keep_cells _ 0x10000 (0x5ef000 + D_1000)).
- intros a Ha. img_apply Z_img. lia4.
- intros x Hx. unfold acells. do 6 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold depot_cells. repeat (img_apply Forall_cons; [img_try (cbn; rewrite ?ED, ?ES; unfold TFX_DEPOT, TFX_STORE, d_nuniq, d_map1, s_total, s_block0, kHighShadowBeg; lia4)|]). img_apply Forall_nil.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B SG) with (ialloc_cells B S) by (img_try (unfold ialloc_cells; rewrite Rii; img_refl)).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
img_apply (keep_cells _ 0x10000 (0x5ef000 + D_1000)).
- intros a Ha. img_apply Z_img. lia4.
- intros x Hx. unfold acells. do 7 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFX_IAL_LO, TFX_IAL_W, TFX_IAL_FLAG.
repeat (img_apply Forall_cons; [img_try (cbn; rewrite ?E1, ?E3; unfold TFX_IAL_LO, TFX_IAL_FLAG, kHighShadowBeg; lia4)|]). img_apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). unfold thread_cells.
constructor; [|img_try (img_apply Forall_nil)]. img_apply (keep_cell _ (T + t_unwinding) 1).
- intros a Ha. img_apply Z_T; unfold t_unwinding in *; unfold Pr, T in *; clear - Ha DR HcR K3; numconst; zlia.
- unfold acells. do 8 (img_apply in_app_iff; right). left. img_refl.
- cbn. unfold T. lia4.
- cbn. unfold T. lia4.
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly SG).
Proof.
unfold acells.
img_apply Forall_app; split; [img_try (img_exact cells_regions)|]. img_apply Forall_app; split; [img_try (img_exact cells_caches)|]. img_apply Forall_app; split; [img_try (img_exact cells_chunks)|].
img_apply Forall_app; split; [img_try (img_exact cells_sec)|]. img_apply Forall_app; split; [img_try (img_exact cells_quar)|]. img_apply Forall_app; split; [img_try (img_exact cells_fs)|].
img_apply Forall_app; split; [img_try (img_exact cells_depot)|]. img_apply Forall_app; split; [img_try (img_exact cells_ialloc) | img_try (img_exact cells_thread)].
Qed.
Lemma fa_final : fa_entries_ok ly rd' SG.
Proof.
pose proof SG_parts as (Rreg & Rc & _). pose proof reg_facts as (_ & _ & _ & _ & RU). intros c' i vv Hc' Hi HV k Hk.
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL0. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0. pose proof geo as GE.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _). pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
destruct (Z.eq_dec c' c) as [->|Hne].
- rewrite Rc in Hi, HV. unfold rG in Hi, HV. cbn [rg_free] in Hi, HV. rewrite E_rest in Hi, HV.
rewrite <- FAv_is. img_apply (entry_rd i vv ltac:(img_try (clear - Hi GE; zlia))); [|img_try (img_exact Hk)]. rewrite <- Hcsz in HV. rewrite fa_nth_elems in HV by (img_try (img_exact E_runs || (clear - Hi; zlia))).
fold EL in E_elems. rewrite E_elems. rewrite nth_error_app2 by (img_try (unfold NT in *; clear - Hi GE; zlia)). rewrite <- HV. f_equal. unfold NT in *. clear - Hi GE. zlia.
- rewrite (Rreg c') in Hi, HV by lia4.
assert (GEO : ~ XC (fa_base ly c' + 4 * i + Z.of_nat k) /\ aowned B ly S (fa_base ly c' + 4 * i + Z.of_nat k)).
{ split.
- pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
pose proof derived_rangesR as DR.
unfold fa_base in *. unfold region_base in R1, R2. rewrite ?region_off_eq in * by (img_try (clear - Hc' HcR; zlia)). unfold RGv, FAv, RBv, SB in *.
img_apply Z_prim; unfold W_FEn, W_UW, W_FW; unfold RGv, FAv, RBv, SB in *.
+ clear - Hi Hk FL0 FB F0 R1 R2 Hc' ; numconst; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
+ clear - Hi Hk FL0 FB F0 Hc' HcR DR; numconst; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
+ clear - Hi Hk FL0 FB F0 Hc' HcR Hne GE HNF; numconst; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
+ intros [_ HW]. clear - Hi Hk FL0 FB F0 Hc' HcR Hne GE HW; numconst; unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *; zlia.
+ intros [EQ HW]. pose proof (HFQ EQ) as HF1. clear - Hi Hk FL0 FB F0 Hc' HcR Hne GE HW HF1 G33; numconst; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
- eapply own_fa; [img_try (img_exact MA) | img_try (img_exact Hc') | img_try (clear - Hi Hk FL0 FB F0; unfold kFreeArrayMax in *; zlia)]. }
destruct GEO as [NX OW]. rewrite AGX; [img_try (img_exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk)) | img_try (img_exact OW) | img_try (img_exact NX)].
Qed.
Lemma flags_final : fs_flags_ok ly rd' SG.
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & Rfr & _). intros cid pos Hc Hp. rewrite Rfr.
pose proof (flag_off_bounds cid pos Hc Hp) as FB.
rewrite AGX; [img_try (img_exact (am_flags _ _ _ _ MA cid pos Hc Hp)) | img_try (unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [img_exact MA | lia4]) |].
img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_try (lia4) | img_try (cbn [fst snd])].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia4.
Qed.
Lemma depot_ids_boundG : depot_ids S <= 4097.
Proof.
pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). lia4.
Qed.
Lemma depot_final : depot_ok B ly rd' SG.
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
pose proof depot_ids_boundG as IDB. pose proof (ts_depot B TS) as ED.
assert (EZ : forall a, (TFX_DEPOT <= a < TFX_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. img_apply AGX.
- destruct Ha as [Ha|Ha].
+ img_apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfx_owned_static. img_apply Exists_exists.
eexists. split; [img_try (right; right; right; left; img_refl)|]. unfold in_zr; cbn. unfold TFX_DEPOT, d_tab_words in Ha. lia4.
+ img_apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; lia4)].
- destruct Ha as [Ha|Ha]; [img_try (img_apply Z_img; unfold TFX_DEPOT, d_tab_words, kHighShadowBeg in *; lia4)|].
img_apply (Z_ext 4 (ly_NB ly, kNodesBlockSize)); [img_refl | img_try (lia4) | img_try (cbn [fst snd]; lia4)]. }
unfold depot_ok, depot_ids, depot_traces in *. rewrite Rdep.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|img_try (split; [|img_exact H3])].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [img_try (img_exact Hh)|]. intros k Hk. rewrite EZ; [img_try (img_exact (Hr k Hk))|]. left. rewrite ED. unfold d_tab_words in *. lia4.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [img_try (img_exact L1)|]. split.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L2 k Hk))|]. right. unfold kNodesBlockSize. lia4.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L3 k Hk))|]. right. unfold kNodesBlockSize. lia4.
Qed.
Lemma shadow_in_USH : forall g, g mod 8 = 0 -> W_USH (shadow_addr g) -> adr <= g < adr + kUserMapSize.
Proof.
intros g Hg8 Hs. pose proof geo as GE. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _).
unfold W_USH, shadow_addr in *. rewrite G11 in Hs. unfold SHBv, SHADOW_OFF in *.
apply Z.mod_divide in G8 as [q Hq]; [|img_try (lia4)]. pose proof (Z.div_mod g 8 ltac:(img_try (lia4))) as D1. rewrite Hg8 in D1.
rewrite Hq in Hs |- *. replace (q * 65536) with (q * 8192 * 8) in Hs by lia4. rewrite Z.div_mul in Hs by lia4.
unfold kUserMapSize in *. img_change (262144 / 8) with 32768 in *. clear - Hs D1. zlia.
Qed.
Lemma shadow_in_FSH : forall g, g mod 8 = 0 -> W_FSH (shadow_addr g) -> fadr <= g < fadr + kFreeArrayMapSize.
Proof.
intros g Hg8 Hs. pose proof geo as GE. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _).
unfold W_FSH, shadow_addr in *. rewrite G27 in Hs. unfold SHBv, SHADOW_OFF in *.
apply Z.mod_divide in G25 as [q Hq]; [|img_try (lia4)]. pose proof (Z.div_mod g 8 ltac:(img_try (lia4))) as D1. rewrite Hg8 in D1.
rewrite Hq in Hs |- *. replace (q * 65536) with (q * 8192 * 8) in Hs by lia4. rewrite Z.div_mul in Hs by lia4.
unfold kFreeArrayMapSize in *. img_change (262144 / 8) with 32768 in *. clear - Hs D1. zlia.
Qed.
Lemma UQ2 : MU = mu2 -> uq = true /\ mu < tot /\ mu2 <= kFreeArrayOffset.
Proof.
intros E. pose proof geo as GE. destruct HMU as [[EM _]|(EM & EQ & _)]; [img_try (exfalso; clear - E EM GE; unfold kUserMapSize in GE; zlia) | img_try (img_exact (conj EQ (HUQ EQ)))].
Qed.
Lemma FQ2 : MF = mf2 -> fq = true /\ mf2 <= kFreeArrayMax.
Proof.
intros E. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct HMF as [EM|[EM EQ]]; [img_try (exfalso; clear - E EM G33; unfold kFreeArrayMapSize in G33; zlia) | img_try (img_exact (conj EQ (HFQ EQ)))].
Qed.
Lemma committed_shadow_old : forall g, g mod 8 = 0 -> in_rangesb g (fa_poison_ranges ly S) = true ->
~ (MU = mu2 /\ W_USH (shadow_addr g)) /\ ~ (MF = mf2 /\ W_FSH (shadow_addr g)).
Proof.
intros g Hg8 IR. pose proof geo as GE. apply in_rangesb_true in IR as (lo & len & Hin & Hlo).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
assert (NU : (MU = mu2 -> ~ (adr <= g < adr + kUserMapSize)) /\ (MF = mf2 -> ~ (fadr <= g < fadr + kFreeArrayMapSize))).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(img_try (lia4))) as MB.
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_try (lia4))) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA0 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
destruct Hin as [E|[E|[]]]; injection E as <- <-.
+ destruct (Z.eq_dec c' c) as [->|NE].
* rewrite <- Hmu_def, <- RBv_is in Hlo. split; intros EQ; [|img_try (pose proof (FQ2 EQ) as [_ HF1])]; [img_try (clear - Hlo GE) | img_try (clear - Hlo GE HF1)]; unfold kUserMapSize, kFreeArrayOffset in *; zlia.
* unfold region_base in Hlo. rewrite region_off_eq in Hlo by lia4. unfold RBv, FAv, SB in *.
split; intros EQ; [|img_try (pose proof (FQ2 EQ) as [_ HF1])]; [img_try (clear - Hlo GE Hc' HcR NE MB) | img_try (clear - Hlo GE Hc' HcR NE MB HF1 G33)]; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; nia.
+ destruct (Z.eq_dec c' c) as [->|NE].
* rewrite <- Hmf_def, <- FAv_is in Hlo. split; intros EQ; [img_try (pose proof (UQ2 EQ) as (_ & _ & HU2))|]; [img_try (clear - Hlo GE HU2) | img_try (clear - Hlo GE)]; unfold kUserMapSize, kFreeArrayOffset in *; zlia.
* unfold fa_base in Hlo. rewrite region_off_eq in Hlo by lia4. unfold RBv, FAv, SB in *.
split; intros EQ; [|img_try (pose proof (FQ2 EQ) as [_ HF1])]; [img_try (clear - Hlo GE Hc' HcR NE FA0 FB) | img_try (clear - Hlo GE Hc' HcR NE FA0 FB HF1 G33)]; numconst; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; nia.
- apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p]; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL _ Gin) as (_ & [H1 H2] & _).
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Gin ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in D. cbn [fst snd] in D. unfold FAv in *.
split; intros EQ; [|img_try (pose proof (FQ2 EQ) as [_ HF1])]; [img_try (clear - Hlo D Q1 Q2 GE) | img_try (clear - Hlo D Q1 Q2 GE HF1 G33)]; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia. }
destruct NU as [NU1 NU2]. split; intros [EQ Hs]; [img_try (img_exact (NU1 EQ (shadow_in_USH g Hg8 Hs))) | img_try (img_exact (NU2 EQ (shadow_in_FSH g Hg8 Hs)))].
Qed.
Lemma shadow_final : shadow_ok B ly rd' SG.
Proof.
pose proof SG_parts as (Rreg & Rc & _ & _ & _ & Rch & _). pose proof geo as GE.
intros g vv Hg8 HV. unfold ashadow in HV. rewrite Rch in HV.
assert (SHLOW : forall g0, 0 <= g0 < kHighMemEnd -> 0x7fff7000 <= shadow_addr g0 < kHighMemBeg).
{ clear. intros g0 Hg0. unfold shadow_addr. pose proof (Z.div_mod g0 8 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound g0 8 ltac:(img_try (zlia))) as M1. numconst. unfold SHADOW_OFF. zlia. }
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
-
assert (A0 : ashadow B ly S g = Some vv) by (img_try (unfold ashadow; rewrite F0; img_exact HV)).
rewrite AGX; [img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 A0)) | img_try (img_exact (ashadow_owned B ly S rd0 g vv MA A0)) |].
apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & GG).
img_apply Z_band; [img_try (img_apply SHLOW; clear - Hg0 C1 C2; numconst; zlia) | |]; intros [EQw Hs].
+ apply shadow_in_USH in Hs; [|img_try (img_exact Hg8)].
destruct (ck_beg k0) as [|o|r o|c'' p] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF (prim_class o) ltac:(img_try (lia4)))) as AL.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S (prim_class o) WF ltac:(img_try (lia4))) as MB.
destruct (Z.eq_dec (prim_class o) c) as [EC|NE].
-- rewrite EC in *. rewrite <- Hmu_def in AL. unfold region_base in *. rewrite region_off_eq in * by lia4. unfold RBv, SB in *. clear - Hs Hg0 D1 D2 D3 D4 D5 D6 D7 D8 AL GE EC C7; unfold kUserMapSize in *. nia4.
-- unfold region_base in *. rewrite region_off_eq in * by lia4. unfold RBv, SB in *. clear - Hs Hg0 D1 D2 D3 D4 D5 D6 D7 D8 AL MB GE NE HcR C7; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. nia4.
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in D. cbn [fst snd] in D. clear - Hs Hg0 D Q1 Q2 GE X2 X3; unfold kUserMapSize, kFreeArrayOffset, kPage in *. lia4.
+ apply shadow_in_FSH in Hs; [|img_try (img_exact Hg8)]. pose proof (FQ2 EQw) as [_ HF1].
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct (ck_beg k0) as [|o|r o|c'' p] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF (prim_class o) ltac:(img_try (lia4)))) as AL.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S (prim_class o) WF ltac:(img_try (lia4))) as MB.
unfold region_base in *. rewrite region_off_eq in * by lia4. unfold FAv, RBv, SB in *. clear - Hs Hg0 D1 D2 D3 D4 D5 D6 D7 D8 AL MB GE HcR C7 HF1 G33; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. nia4.
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in D. cbn [fst snd] in D. unfold FAv in *. clear - Hs Hg0 D Q1 Q2 GE X2 X3 HF1 G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax, kPage in *. zlia.
-
rewrite ?F0 in HV. destruct (in_rangesb g (fa_poison_ranges ly SG)) eqn:IR; [|img_try (discriminate)]. injection HV as <-.
destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR0.
+
assert (A0 : ashadow B ly S g = Some shHeapLeftRz) by (img_try (unfold ashadow; rewrite F0, IR0; img_refl)).
pose proof (committed_shadow_old g Hg8 IR0) as [NU NF].
rewrite AGX; [img_try (img_exact (am_shadow _ _ _ _ MA g _ Hg8 A0)) | img_try (img_exact (ashadow_owned B ly S rd0 g _ MA A0)) |].
img_apply Z_band; [| img_try (img_exact NU) | img_try (img_exact NF)].
apply in_rangesb_true in IR0 as (lo & len & Hin & Hlo). img_apply SHLOW. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
* apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(img_try (lia4))) as (R1 & R2 & R3 & R4 & R5). pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_try (lia4))) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(img_try (lia4))) as MB.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base in *; unfold region_base in R1, R2, Hlo; rewrite region_off_eq in Hlo by lia4; rewrite region_off_eq in R1 by lia4; rewrite region_off_eq in R2 by lia4;
clear - Hlo R1 R2 F3 F6 FA1 FB MB Hc'; numconst; unfold EV_MAX in *; zlia.
* apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p]; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext. numconst. unfold kPage in *. lia4.
+
apply in_rangesb_true in IR as (lo & len & Hin & Hlo).
assert (NEWG : (MU = mu2 /\ adr <= g < adr + kUserMapSize) \/ (MF = mf2 /\ fadr <= g < fadr + kFreeArrayMapSize)).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite Rc in Hin. unfold rG in Hin. cbn [rg_mapped_user rg_mapped_fa] in Hin.
assert (OLD : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = false -> ~ (region_base ly c <= g < region_base ly c + mu) /\ ~ (fa_base ly c <= g < fa_base ly c + mf)).
{ intros Hf. split; intros X; [img_try (assert (E : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = true)) | img_try (assert (E : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = true))]; try (rewrite E in Hf; discriminate Hf);
[ img_try (img_exact (in_rangesb_In g [(region_base ly c, mu); (fa_base ly c, mf)] _ _ (or_introl eq_refl) X)) | img_try (img_exact (in_rangesb_In g [(region_base ly c, mu); (fa_base ly c, mf)] _ _ (or_intror (or_introl eq_refl)) X)) ]. }
assert (OLDF : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = false).
{ destruct (in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)]) eqn:E; [|img_refl]. exfalso.
assert (IN : in_rangesb g (fa_poison_ranges ly S) = true); [|img_try (rewrite IN in IR0; discriminate IR0)].
apply in_rangesb_true in E as (lo' & len' & Hin' & Hlo'). img_apply (in_rangesb_In g _ lo' len'); [|img_try (img_exact Hlo')].
unfold fa_poison_ranges. img_apply in_app_iff. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; lia4)|]. rewrite <- Hmu_def, <- Hmf_def. img_exact Hin'. }
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct (OLD OLDF) as [O1 O2]. unfold region_base, fa_base in *. rewrite <- (proj1 (proj2 (proj2 (proj2 GE)))) in *. unfold RBv, FAv, SB in *. rewrite region_off_eq in * by lia4.
destruct Hin as [E|[E|[]]]; injection E as <- <-; [img_try (left) | img_try (right)]; (destruct HMU as [[EM _]|(EM & _)]; destruct HMF as [EM'|[EM' _]]; rewrite ?EM, ?EM' in *;
first [ split; [img_refl | img_try (clear - Hlo O1 O2 GE G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *; zlia)] | exfalso; clear - Hlo O1 O2 GE G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *; zlia ]).
+ exfalso. assert (IN : in_rangesb g (fa_poison_ranges ly S) = true); [|img_try (rewrite IN in IR0; discriminate IR0)].
rewrite (Rreg c') in Hin by lia4. img_apply (in_rangesb_In g _ lo len); [|img_try (img_exact Hlo)].
unfold fa_poison_ranges. img_apply in_app_iff. left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; lia4) | img_try (img_exact Hin)].
- exfalso. assert (IN : in_rangesb g (fa_poison_ranges ly S) = true); [|img_try (rewrite IN in IR0; discriminate IR0)].
img_apply (in_rangesb_In g _ lo len); [|img_try (img_exact Hlo)]. unfold fa_poison_ranges. img_apply in_app_iff. right. img_exact Hin. }
assert (SHx : forall base, base mod 65536 = 0 -> base <= g < base + 262144 -> SHBv + base / 8 <= shadow_addr g < SHBv + base / 8 + 32768).
{ clear - Hg8. intros base Hb Hgb. unfold shadow_addr, SHBv, SHADOW_OFF. apply Z.mod_divide in Hb as [q Hq]; [|img_try (lia4)]. rewrite Hq in Hgb |- *.
replace (q * 65536) with (q * 8192 * 8) by lia4. rewrite Z.div_mul by lia4. pose proof (Z.div_mod g 8 ltac:(img_try (lia4))). lia4. }
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _ & G13 & G14 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _ & G29 & G30 & _).
destruct NEWG as [[EM Hg]|[EM Hg]].
* pose proof (SHx adr G8 ltac:(img_try (unfold kUserMapSize in Hg; img_exact Hg))) as WND. rewrite <- G11 in WND.
assert (Rg : 0 <= shadow_addr g < 2 ^ 64) by (img_try (clear - WND G13 G14; zlia)).
destruct (USHV EM (w64 (shadow_addr g)) ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_exact Rg; unfold W_USH; img_change (kUserMapSize / 8) with 32768; img_exact WND))) as [V Hh].
unfold rd', aview, mbyte, mrestrict. unfold w64 in V, Hh. rewrite Hh, V. img_refl.
* pose proof (SHx fadr G25 ltac:(img_try (unfold kFreeArrayMapSize in Hg; img_exact Hg))) as WND. rewrite <- G27 in WND.
assert (Rg : 0 <= shadow_addr g < 2 ^ 64) by (img_try (clear - WND G29 G30; zlia)).
destruct (FSHV EM (w64 (shadow_addr g)) ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_exact Rg; unfold W_FSH; img_change (kFreeArrayMapSize / 8) with 32768; img_exact WND))) as [V Hh].
unfold rd', aview, mbyte, mrestrict. unfold w64 in V, Hh. rewrite Hh, V. img_refl.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. img_apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. img_change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi)) | img_try (eapply own_shadow_zero; [img_exact MA | img_exact Hr | img_exact Hi]) |].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof geo as GE.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _ & G13 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _ & G29 & _ & _ & _ & G33 & _).
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
pose proof (pairwise_ij _ _ 0 7 _ _ (lo_disj ly LY) eq_refl eq_refl) as PS. unfold zdisjoint in PS. cbn [fst snd] in PS.
apply Z.mod_divide in G8 as [qa Hqa]; [|img_try (clear; zlia)]. apply Z.mod_divide in G25 as [qf Hqf]; [|img_try (clear; zlia)].
assert (Esha : sha = SHBv + qa * 8192) by (img_try (rewrite G11, Hqa; replace (qa * 65536) with (qa * 8192 * 8) by (clear; zlia); rewrite Z.div_mul by (clear; zlia); img_refl)).
assert (Eshf : shf = SHBv + qf * 8192) by (img_try (rewrite G27, Hqf; replace (qf * 65536) with (qf * 8192 * 8) by (clear; zlia); rewrite Z.div_mul by (clear; zlia); img_refl)).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
-
cbn [fst snd] in *. unfold shadow_addr. pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(img_try (clear; zlia))) as D1. pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(img_try (clear; zlia))) as M1.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_try (clear; zlia))) as D2. pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_try (clear; zlia))) as M2.
img_apply Z_band; [img_try (clear - Hi T1 T2 T4 T7 D1 D2 M1 M2; numconst; unfold SHADOW_OFF; zlia) | |]; intros [EQ Hs];
[img_try (unfold W_USH in Hs; rewrite Esha in Hs; img_change (kUserMapSize / 8) with 32768 in Hs; pose proof I as HF1)
|img_try (unfold W_FSH in Hs; rewrite Eshf in Hs; img_change (kFreeArrayMapSize / 8) with 32768 in Hs; pose proof (FQ2 EQ) as [_ HF1])];
unfold SHBv, FAv in *; clear - Hi Hs T1 T2 T4 T7 D1 D2 M1 M2 PS Q1 Q2 GE Hqa Hqf HF1 G33; numconst; unfold SHADOW_OFF, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
-
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5). destruct r as [r1 r2]. cbn [fst snd] in *.
unfold shadow_addr. unfold kLowMemEnd in Z5. pose proof (Z.div_mod r1 8 ltac:(img_try (clear; zlia))) as D1. pose proof (Z.mod_pos_bound r1 8 ltac:(img_try (clear; zlia))) as M1.
pose proof (Z.div_mod r2 8 ltac:(img_try (clear; zlia))) as D2. pose proof (Z.mod_pos_bound r2 8 ltac:(img_try (clear; zlia))) as M2.
img_apply Z_band; [img_try (clear - Hi Z1 Z2 Z3 Z4 Z5 D1 D2 M1 M2; numconst; unfold SHADOW_OFF; zlia) | |]; intros [EQ Hs];
[img_try (unfold W_USH in Hs; rewrite Esha in Hs; img_change (kUserMapSize / 8) with 32768 in Hs) | img_try (unfold W_FSH in Hs; rewrite Eshf in Hs; img_change (kFreeArrayMapSize / 8) with 32768 in Hs)];
unfold SHBv in *; clear - Hi Hs Z1 Z2 Z3 Z4 Z5 D1 D2 M1 M2 G13 G29 Esha Eshf; numconst; unfold SHADOW_OFF in *; zlia.
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly SG) /\ Forall (range_vis B ly rd') (aareas SG) /\ Forall (range_vis B ly rd') (aclient SG).
Proof.
pose proof SG_parts as (Rreg & Rc & Rinit & Rother & Rcl & Rch & Rsecs & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rnev).
pose proof derived_rangesR as DR. pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof geo as GE.
split; [|img_try (split)].
-
unfold ajunk. rewrite Rch.
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. img_refl. }
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. img_refl. }
img_apply Forall_app; split; [img_try (img_apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_app; split.
{ img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
- unfold cache_junk. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks]. rewrite length_rev. fold NT.
constructor; [|img_try (img_apply Forall_nil)]. intros i Hi. cbn [fst snd aeval] in *. img_apply apresent_vis. img_apply DSTP. unfold DSTv, Pr. clear - Hi GE K3. lia4.
- img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. img_apply in_app_iff; right. img_apply in_app_iff; left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; lia4)|].
unfold cache_junk in *. rewrite Rinit, (Rother c') in Hx by lia4. img_exact Hx. }
img_apply Forall_app; split; [img_try (img_apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; do 2 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_app; split.
{ img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 3 (img_apply in_app_iff; right). img_apply in_app_iff; left.
unfold sec_junk in *. rewrite Rarr, Rres, Rch in Hx. img_exact Hx. }
img_apply Forall_app; split.
{ img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 4 (img_apply in_app_iff; right). img_apply in_app_iff; left.
unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. img_exact Hx. }
img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 5 (img_apply in_app_iff; right). img_exact Hx.
-
unfold aareas. rewrite Rres, Rch.
img_apply Forall_app; split.
+ img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
* rewrite Rc. unfold rG. cbn [rg_mapped_user rg_mapped_fa].
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (ASp (region_off c), mu)
ltac:(img_try (unfold aareas; img_apply in_app_iff; left; img_apply in_flat_map; exists c; split; [img_try (img_apply In_zseq; lia4) | img_try (left; rewrite <- Hmu_def; img_refl)]))) as RVU.
assert (ERB : ly_space ly + region_off c = RBv) by (img_try (rewrite RBv_is; img_refl)).
assert (EFA : ly_space ly + (region_off c + kFreeArrayOffset) = FAv) by (img_try (rewrite FAv_is; unfold fa_base; clear; zlia)).
constructor; [|img_try (constructor; [|img_apply Forall_nil])]; intros i Hi; cbn [fst snd aeval] in *; rewrite ?ERB, ?EFA.
-- destruct (Z_lt_le_dec i mu) as [L|L].
++ pose proof (RVU i ltac:(img_try (cbn [snd]; clear - Hi L GE; zlia))) as RV. cbn [fst snd aeval] in RV. rewrite ERB in RV.
img_apply (VIS_MONO (RBv + i) ltac:(img_try (clear - Hi L GE; numconst; unfold kFreeArrayOffset in *; zlia)) RV);
unfold W_UW, W_FW; intros (_ & _ & X); clear - X L GE Hi; unfold kFreeArrayOffset in *; zlia.
++ destruct HMU as [[EM _]|(EM & _)]; [img_try (exfalso; clear - Hi L EM; zlia)|].
img_apply apresent_vis. img_apply (UWP EM). clear - Hi L EM; zlia.
-- img_apply apresent_vis. img_apply FAP. clear - Hi; zlia.
* rewrite (Rreg c') by lia4. img_apply vis_keep. right; left. intros x Hx. unfold aareas. img_apply in_app_iff. left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; lia4) | img_try (img_exact Hx)].
+ img_apply vis_keep. right; left. intros x Hx. unfold aareas. img_apply in_app_iff. right. img_exact Hx.
-
replace (aclient SG) with (aclient S); [img_try (img_apply vis_keep; right; right; intros x Hx; img_exact Hx)|].
unfold aclient. rewrite Rfr, Rch. img_refl.
Qed.
Definition abs_cell_okG {imgk : img} (cc : acell) : bool :=
match c_at cc with
| ANum a => ((0x10000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? (0x5ff000 + D_1000))) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x80050000))
| _ => false
end.
Lemma abs_cells_okG : forallb abs_cell_okG (Tfx_const_abs ++ Tfx_const_shadow) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
img_apply Forall_forall. intros cc Hin.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin))|].
intros k Hk. img_apply AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin k Hk))|].
rewrite (ts_const B TS ly) in Hin. unfold Tfx_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfx_const_sym in Hin. cbn [In] in Hin. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof geo as GE.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC0.
pose proof (pairwise_ij _ _ 2 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DT. pose proof (pairwise_ij _ _ 0 6 _ _ (lo_disj ly LY) eq_refl eq_refl) as DP.
pose proof (Forall_nth' _ _ 7 _ (lo_app ly LY) eq_refl) as DH. cbv beta in DH. unfold in_app in DH. unfold zdisjoint in DT, DP. cbn [fst snd] in DT, DP, DH.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in CT, PC0. cbn [fst snd] in CT, PC0.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [img_try (cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD in *;
first [ img_apply Z_img; clear - Hk; unfold TFX_TP, TFX_INST, TFX_TSD, o_space, o_rinfo, o_sec_chunks; numconst; unfold kHighShadowBeg; zlia
| img_apply Z_T; unfold Pr, T in *; clear - Hk DR F1 F2 HcR; unfold kStackSpan in *; numconst; zlia
| img_apply Z_prim; unfold W_FEn, W_UW, W_FW, RGv, FAv, RBv, Pr, T, SB in *; clear - Hk DR F1 F2 F3 F4 F5 F6 F7 F8 CT PC0 Q1 Q2 GE HcR; numconst; unfold o_space, o_rinfo, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia
| img_apply Z_out; unfold T in *; clear - Hk DR F1 F2 F3 F4 F5 F6 F7 F8 CT PC0 DT DP DH; numconst; zlia ]) |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okG cc Hin) as Hc. unfold abs_cell_okG in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbn [aeval].
apply Bool.orb_prop in Hc as [Hc|Hc]; apply andb_prop in Hc as [Hz Hc]; apply Z.leb_le in Hz; apply Z.leb_le in Hc; img_apply Z_img; lia4.
Qed.
Lemma AR_transportG : AR tfxsegs B ly SG Wd mem' (with_vm_backing (m_vm_lazy mdf) mat mdf).
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
pose proof SG_parts as (Rreg & Rc & Rinit & Rother & Rcl & Rch & Rsecs & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rnev).
split; [|img_try (split; [|split; [|split]])].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ img_exact WFG.
+ img_exact Mun.
+ img_exact Msy.
+ img_exact Mly.
+ unfold sec_placed in *. rewrite SG_sec_extents. img_exact Mpl.
+ img_exact const_final.
+ img_exact Mcow.
+ img_exact cells_final.
+ img_exact fa_final.
+ img_exact flags_final.
+ img_exact depot_final.
+ img_exact shadow_final.
+ img_exact zshadow_final.
+ img_exact (proj1 vis_final).
+ img_exact (proj1 (proj2 vis_final)).
+ img_exact (proj2 (proj2 vis_final)).
+ img_apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). img_apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [img_try (img_exact MA) | img_try (cbn; tauto) |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia4.
* img_apply Z_img. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, kHighShadowBeg in *; lia4.
+ img_exact Mts.
+   img_exact Msi.
- img_exact (ALedger_same tfxsegs ly SG mdf _ HL (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) ltac:(img_try (unfold eager_used; rewrite m_vmmaps_wvb, m_vm_lazy_wvb; img_refl))).
-   destruct BUD as [BUD PIN]. split; [| img_try (intros e He; rewrite SG_sec_extents in He; destruct (PIN e He) as [P1 P2]; split; [img_exact (HINC _ P1) | img_exact (HINC _ P2)])].
unfold abudget, sec_hulls in *. rewrite Rnev, Rsecs  . unfold sec_live_bytes in *. rewrite Rch. pose proof HSL as SL. unfold EV_A in *. clear - BUD HBUD SL. lia4.
- img_exact (amwf_same mdf _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) HMW).
-
destruct HS0 as [HS0 HZ0]. split.
{ intros a Ha NCL HV. pose proof geo as GE.
assert (NC0 : ~ aclient_byte B ly S a).
{ intros CL. img_apply NCL. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)]; [img_try (left; exists k; rewrite Rch; img_exact (conj Hk (conj Hst Hr))) | img_try (right; exists cp; rewrite Rfr; img_exact (conj Hcp Hr))]. }
assert (HV0 : w_H W (YG0u.w64 a) = true \/ ~ in_vis0 ly a) by (img_try (destruct HV as [Hh|Hv]; [img_try (left; img_exact (HSUB _ Hh)) | img_try (right; img_exact Hv)])).
pose proof (HS0 a Ha NC0 HV0) as X0.
destruct (NOREM (YG0u.w64 a) X0) as [NN | [[_ Hw]|[_ Hw]]]; [img_try (img_exact NN) | img_try (exfalso) | img_try (exfalso)]; unfold YG0u.w64 in Hw;
rewrite unsigned_lit_small in Hw by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; zlia)); unfold W_UW, W_FW in Hw;
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _); rewrite <- RBv_is in Q1, Q2; clear - Ha Hw GE Q1 Q2; numconst; unfold kHighShadowBeg, kHighShadowEnd, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia. }
img_apply (ahz_keep ly S SG mem0 mem'); [|img_try (img_exact HZ0)]. intros g Hg Happ HF.
assert (HF0 : hfree ly S g) by (img_try (unfold hfree in HF |- *; unfold sec_extents in HF |- *; rewrite Rch in HF; img_exact HF)). split; [img_try (img_exact HF0)|].
pose proof (shadow_addr_band_rw g Happ) as SBg. unfold in_band_rw, kLowShadowEnd in SBg.
assert (Hlo : 4096 <= g) by (img_try (clear - Happ; unfold in_app in Happ; zlia)). pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof derived_rangesR as DR.
pose proof (zone3_apart_hsh _ _ (shadow_addr g) F1) as TH.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). pose proof Hsp as (S1 & _).
assert (GP : g + 8 <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= g).
{ unfold hfree in HF0. img_exact (proj1 (Forall_forall _ _) HF0 (ly_prim ly, kPrimResvSize)
ltac:(img_try (img_apply in_app_iff; left; unfold static_extents, owned_extents; img_apply in_app_iff; left; left; img_refl))). }
assert (G0 : 0 <= g) by (img_try (clear - Hlo; zlia)).
assert (RP : ly_prim ly <= RBv /\ RBv + 2 ^ 32 <= ly_prim ly + kPrimResvSize) by (img_try (clear - F4 F5 DR; unfold kSpaceSize, kPrimResvSize in *; zlia)).
assert (AP : forall x y, RBv <= x -> y <= RBv + 2 ^ 32 -> shadow_addr g + 1 <= shadow_addr x \/ SHADOW_OFF + y / 8 <= shadow_addr g).
{ intros x y Hx Hy. img_apply shadow_apart; [img_try (img_exact Hg) | img_try (img_exact G0) | img_try (clear - Hx RP F3; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *; zlia) | img_try (clear - GP RP Hx Hy; zlia)]. }
unfold w64. img_apply MEQ; rewrite unsigned_lit_small by (img_try (clear - SBg; unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd in SBg; zlia)).
+ clear - SBg S1 T7. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. unfold sp0 in *. zlia.
+ intros X. apply XC_where in X. destruct X as [[X _]|[X|[[X _]|[_ X]]]].
* clear - X SBg TH. unfold zone3, kThreadObjSize, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. unfold T in *. zlia.
* clear - X SBg DR. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. zlia.
* clear - X SBg DR. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. zlia.
* pose proof Hmu as (U0 & U1 & U2 & _). pose proof Hmf as [M0f M1f].
destruct X as [[EM HWs]|[EM HWs]].
--
assert (UQ : mu2 <= kFreeArrayOffset) by (img_try (destruct HMU as [[E1 _]|(E1 & E2 & _)]; [img_try (rewrite EM in E1; rewrite Hmu2 in E1; unfold kUserMapSize in E1; zlia) | img_try (img_exact (proj2 (HUQ E2)))])).
destruct (AP adr (adr + kUserMapSize) ltac:(img_try (rewrite Hadr; zlia)) ltac:(img_try (rewrite Hadr; rewrite Hmu2 in UQ; clear - UQ U0 U1; unfold kUserMapSize, kFreeArrayOffset in *; zlia))) as [Y|Y];
unfold W_USH in HWs; rewrite Hsha in HWs; unfold SHBv in HWs; unfold shadow_addr, SHADOW_OFF in *; [img_try (clear - HWs Y; zlia)|].
assert (A8 : (adr + kUserMapSize) / 8 = adr / 8 + kUserMapSize / 8).
{ apply Z.mod_divide in U2 as [q Hq]; [|img_try (unfold kUserMapSize; zlia)]. pose proof DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB16 & _).
apply Z.mod_divide in RB16 as [p Hp]; [|img_try (zlia)]. rewrite Hadr, Hq, Hp. unfold kUserMapSize.
replace (p * 65536 + q * 262144 + 262144) with ((p * 8192 + q * 32768 + 32768) * 8) by zlia. replace (p * 65536 + q * 262144) with ((p * 8192 + q * 32768) * 8) by zlia.
rewrite !Z.div_mul by zlia. img_refl. }
rewrite A8 in Y. clear - HWs Y. zlia.
--
assert (FQ : mf2 <= kFreeArrayMax) by (img_try (destruct HMF as [E1|[E1 E2]]; [img_try (rewrite EM in E1; rewrite Hmf2 in E1; unfold kFreeArrayMapSize in E1; zlia) | img_try (img_exact (HFQ E2))])).
destruct (AP fadr (fadr + kFreeArrayMapSize) ltac:(img_try (rewrite Hfadr; unfold FAv; clear - M0f; unfold kFreeArrayOffset; zlia))
ltac:(img_try (rewrite Hfadr; unfold FAv; rewrite Hmf2 in FQ; clear - FQ M0f; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *; zlia))) as [Y|Y];
unfold W_FSH in HWs; rewrite Hshf in HWs; unfold SHBv in HWs; unfold shadow_addr, SHADOW_OFF in *; [img_try (clear - HWs Y; zlia)|].
assert (A8 : (fadr + kFreeArrayMapSize) / 8 = fadr / 8 + kFreeArrayMapSize / 8).
{ apply Z.mod_divide in M1f as [q Hq]; [|img_try (unfold kFreeArrayMapSize; zlia)]. pose proof DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB16 & _).
apply Z.mod_divide in RB16 as [p Hp]; [|img_try (zlia)]. rewrite Hfadr. unfold FAv. rewrite Hq, Hp. unfold kFreeArrayMapSize, kFreeArrayOffset.
replace (p * 65536 + 3758096384 + q * 262144 + 262144) with ((p * 8192 + 469762048 + q * 32768 + 32768) * 8) by zlia.
replace (p * 65536 + 3758096384 + q * 262144) with ((p * 8192 + 469762048 + q * 32768) * 8) by zlia.
rewrite !Z.div_mul by zlia. img_refl. }
rewrite A8 in Y. clear - HWs Y. zlia.
Qed.
Lemma XC_owned : forall a, 0 <= a < 2 ^ 64 -> XC a -> aowned B ly S a.
Proof.
intros a Ra Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & _). pose proof class_facts as (_ & _ & K3 & _). pose proof geo as GE.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _).
assert (OT : forall b, T <= b < T + kThreadObjSize -> aowned B ly S b).
{ intros b Hb. img_apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) b MA); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; unfold T in Hb; img_exact Hb)]. }
apply XC_where in Hx. destruct Hx as [[Hx _] | [Hx | [[Hp Hx] | [Hb Hx]]]].
- img_apply OT. img_exact Hx.
- img_apply (own_rinfo B ly S rd0 a MA). unfold RGv, SB in Hx. clear - Hx HcR. numconst. lia4.
-
img_apply (own_prim_nonuser B ly S rd0 a MA); [img_try (clear - Hp Q1 Q2; zlia)|].
intros k Hk Hst Hu. pose proof (chunk_facts B ly S rd0 k MA Hk) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & GG).
destruct (ck_beg k) as [|o|r o|c'' p'] eqn:Eb; try solve [destruct GG].
+ cbv zeta in GG. destruct GG as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
pose proof (mapped_user_bound (as_universe B) 0 0 0 S (prim_class o) WF ltac:(img_try (lia4))) as MB.
destruct (Z.eq_dec (prim_class o) c) as [EC|NE].
* rewrite EC in *. rewrite <- Hau_def, <- Hmu_def in D9. rewrite <- Hau_def in D8. unfold W_FEn, W_UW, W_FW in Hx. unfold region_base in D5. rewrite region_off_eq in D5, D6, D8 by lia4.
unfold FAv, RBv, SB in *. destruct Hx as [Hx|[[_ Hx]|[_ Hx]]]; clear - Hp Hx Hu C5 C8 D4 D5 D6 D8 D9 GE K3; numconst; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *; nia.
* unfold W_FEn, W_UW, W_FW in Hx. unfold region_base in D5. rewrite region_off_eq in D5, D6, D8 by lia4.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold FAv, RBv, SB in *. destruct Hx as [Hx|[[_ Hx]|[EQ Hx]]]; [| | img_try (pose proof (HFQ EQ) as HF1)]; first [pose proof I as HF1 | idtac];
clear - Hp Hx Hu C5 C8 D1 D4 D5 D6 D8 D9 MB NE GE HcR HNF HF1 G33; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; nia.
+ destruct GG as (X0 & X1 & X2 & X3 & Hin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D.
unfold zdisjoint in D. cbn [fst snd] in D. clear - Hp Hu D C5 C8 X2 X3 Q1 Q2; unfold kPage in *. zlia.
-
set (g := (a - SHADOW_OFF) * 8).
assert (Eg : shadow_addr g = a) by (img_try (unfold shadow_addr; (subst g; cbv beta); rewrite Z.div_mul by lia4; lia4)).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
assert (HF1 : MF = mf2 -> mf2 <= kFreeArrayMax) by (img_try (intros EQ; img_exact (proj2 (FQ2 EQ)))).
rewrite <- Eg. img_apply (own_shadow_prim B ly S rd0 g MA). (subst g; cbv beta). unfold W_USH, W_FSH in Hx. rewrite G11, G27 in Hx. unfold SHBv, SHADOW_OFF in Hx |- *.
apply Z.mod_divide in G8 as [q Hq]; [|img_try (clear; zlia)]. apply Z.mod_divide in G25 as [q' Hq']; [|img_try (clear; zlia)].
rewrite Hq, Hq' in Hx. replace (q * 65536) with (q * 8192 * 8) in Hx by (img_try (clear; zlia)). replace (q' * 65536) with (q' * 8192 * 8) in Hx by (img_try (clear; zlia)). rewrite !Z.div_mul in Hx by (img_try (clear; zlia)).
unfold FAv in *. unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. img_change (262144 / 8) with 32768 in *.
destruct Hx as [[_ Hx]|[EQ Hx]]; [img_try (clear HF1; pose proof I as HF1) | img_try (specialize (HF1 EQ))]; clear - Hx Hq Hq' Q1 Q2 GE HF1 G33; zlia.
Qed.
Lemma LEAF_G : forall W' c' (P : (word -> option byte) -> Prop),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy mdf) mat mdf) -> W' = Wd ->
getr regs' 10 = Z_to_bv 64 (if (length TOPS =? 0)%nat then 0 else 1) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
wle W Wd -> same_io md0 mdf ->
refill_leaf B ly S W regs0 mem0 md0 c (tt, SG) W' c'.
Proof.
intros W' c' P -> -> R10 RCS LE IO.
exists regs', mem', (with_vm_backing (m_vm_lazy mdf) mat mdf).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
cbn [fst snd]. split.
- split; [img_try (img_exact AR_transportG)|].
split; [img_try (img_apply layout_le_refl)|].
split; [img_try (img_exact LE)|].
split. { intros r Hr. img_apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia4.
clear - RCS H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (img_try (intros k Hk b Hb; img_apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; img_change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia4; symmetry; img_exact Hb)).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ img_try (rewrite (E5 2 ltac:(lia4) 2%bv eq_refl)) | img_try (rewrite (E5 3 ltac:(lia4) 3%bv eq_refl)) | img_try (rewrite (E5 4 ltac:(lia4) 4%bv eq_refl))
| img_try (rewrite (E5 8 ltac:(lia4) 8%bv eq_refl)) | img_try (rewrite (E5 9 ltac:(lia4) 9%bv eq_refl)) | img_try (rewrite (E5 18 ltac:(lia4) 18%bv eq_refl))
| img_try (rewrite (E5 19 ltac:(lia4) 19%bv eq_refl)) | img_try (rewrite (E5 20 ltac:(lia4) 20%bv eq_refl)) | img_try (rewrite (E5 21 ltac:(lia4) 21%bv eq_refl))
| img_try (rewrite (E5 22 ltac:(lia4) 22%bv eq_refl)) | img_try (rewrite (E5 23 ltac:(lia4) 23%bv eq_refl)) | img_try (rewrite (E5 24 ltac:(lia4) 24%bv eq_refl))
| img_try (rewrite (E5 25 ltac:(lia4) 25%bv eq_refl)) | img_try (rewrite (E5 26 ltac:(lia4) 26%bv eq_refl)) | img_try (rewrite (E5 27 ltac:(lia4) 27%bv eq_refl)) ];
cbn [In]; tauto. }
split. { destruct IO as (I1 & I2 & I3 & I4). unfold same_io. destruct mdf; cbn in *; repeat split; assumption. }
split.
+ intros a Ra NO NO' NS NE. unfold rd' in *. unfold aview, mbyte, mrestrict.
assert (NSC : ~ (sp0 - RSTACK <= a < sp0)) by (img_try (intros Hs; img_apply NS; unfold ascratch, spZ; left; img_exact Hs)).
assert (NX : ~ XC a) by (img_try (intros Hx; img_exact (NO (XC_owned a Ra Hx)))).
rewrite (HVIS (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_exact Ra; img_exact NX)).
rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_exact Ra; assumption)). img_refl.
+ intros a Ha. img_exact (PRS a Ha).
- rewrite R10. pose proof SG_parts as (_ & _ & _ & _ & Rcl & _). rewrite Rcl. cbn [pc_chunks].
destruct TOPS as [|x t]; [img_refl|]. cbn [length Nat.eqb]. destruct (rev (x :: t)) as [|y u] eqn:Er; [|img_refl].
exfalso. apply (f_equal (@length Z)) in Er. rewrite length_rev in Er. cbn in Er. lia4.
Qed.
End a0.
End z.
End l.

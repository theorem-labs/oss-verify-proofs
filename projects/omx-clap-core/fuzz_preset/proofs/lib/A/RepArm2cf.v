(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepArm2cf.v (commit eb934de95d13, blob 7985943c9301) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 14 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import MnRefillLocpreset MemnormLoc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB19 AF0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFl1 AFhy AFis YFkpcf YFk6cf YFk5cf AFhz YFk8cf YFk7cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFk4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFk3 AB1q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import YFhmcf YFkacf YFkkcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0dcf YG0qcf YG0lawscf YG06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YFkbcf YFkjcf YFkmcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfXsMapped YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepArmD RepArmcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepVisLcf RepModelcf RepLeafcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
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
Section f.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex : Z).
Variables (need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pr := (@YFk5cf.Pr ly c).
Local Abbreviation RGv := (@YFk5cf.RGv ly c).
Local Abbreviation RBv := (@YFk5cf.RBv ly c).
Local Abbreviation FAv := (@YFk5cf.FAv ly c).
Local Abbreviation SHBv := (@YFk5cf.SHBv).
Local Abbreviation SRCv := (@YFk5cf.SRCv ly c n nf).
Local Abbreviation DSTv := (@YFk5cf.DSTv ly c).
Local Abbreviation XWR := (@YFk5cf.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E0 := (@YFk5cf.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaT := (@YFk5cf.EaT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaC := (@YFk5cf.EaC ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSB := (@YFk5cf.EaSB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaTOP := (@YFk5cf.EaTOP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaCL := (@YFk5cf.EaCL ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaP := (@YFk5cf.EaP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMAX := (@YFk5cf.EaMAX ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaN := (@YFk5cf.EaN ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaCSZ := (@YFk5cf.EaCSZ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRG := (@YFk5cf.EaRG ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRB := (@YFk5cf.EaRB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaFA := (@YFk5cf.EaFA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNF := (@YFk5cf.EaNF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaJEX := (@YFk5cf.EaJEX ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF := (@YFk5cf.EaMF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAU := (@YFk5cf.EaAU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMU := (@YFk5cf.EaMU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHB := (@YFk5cf.EaSHB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNEED := (@YFk5cf.EaNEED ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaTOT := (@YFk5cf.EaTOT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaADR := (@YFk5cf.EaADR ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHA := (@YFk5cf.EaSHA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Hypothesis IMG : img_cover ly.
Local Abbreviation EaMU2 := (@YFk5cf.EaMU2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNCe := (@YFk5cf.EaNCe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNCg := (@YFk5cf.EaNCg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNFe := (@YFk5cf.EaNFe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNFg := (@YFk5cf.EaNFg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaFADR := (@YFk5cf.EaFADR ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHF := (@YFk5cf.EaSHF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF2 := (@YFk5cf.EaMF2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAUe := (@YFk5cf.EaAUe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAUg := (@YFk5cf.EaAUg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation Er := (@YFk5cf.Er ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E2 := (@YFk5cf.E2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E1 := (@YFk5cf.E1 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E8 := (@YFk5cf.E8 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Hypothesis LY : layout_ok ly.
Hypothesis HcR : 1 <= c <= 31.
Hypothesis Hmax : maxc = max_cached c.
Hypothesis Hn : n = maxc / 2.
Hypothesis Hcsz : csz = class_size c.
Hypothesis Hnf : 0 <= nf /\ 4 * nf <= mf.
Hypothesis Hmf : 0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0.
Hypothesis Hmu : 0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0.
Hypotheses (Hj64 : 0 <= j64 < 2 ^ 32) (Hjna : 0 <= jna < 2 ^ 64) (Hjnf : 0 <= jnf < 2 ^ 64)
(Hjsm : 0 <= jsm < 2 ^ 64) (Hjm1 : 0 <= jm1 < 2 ^ 64) (Hjm2 : 0 <= jm2 < 2 ^ 64) (Hjex : 0 <= jex < 2 ^ 8).
Hypothesis Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
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
Local Abbreviation class_facts := (@YFk5cf.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@YFk5cf.high_factsR _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_T := (@YFk5cf.off_T _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_C := (@YFk5cf.off_C _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation derived_rangesR := (@YFk5cf.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation WINR0 := (@YFk5cf.WINR0 ly regs0 c).
Local Abbreviation WINR := (@YFk5cf.WINR ly regs0 c n).
Local Abbreviation WINR0_WINR := (@YFk5cf.WINR0_WINR ly regs0 c n).
Local Abbreviation WSKELR := (@YFk5cf.WSKELR).
Local Abbreviation win_sub := (@YFk5cf.win_sub).
Local Abbreviation win_sub_sound := (@YFk5cf.win_sub_sound ly regs0 c maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (@YFk5cf.WSKELR_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation windows_WINR0 := (@YFk5cf.windows_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_WINR0 := (@YFk5cf.frame_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_X := (@YFk5cf.frame_X _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Ltac frame_acc3 HX HE :=
match goal with
| MEQ : (forall x : word, ~ ?X (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ X (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_X X E rs m1 m2 HX HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation W_DST := (@YFk5cf.W_DST ly c n).
Local Abbreviation W_FE := (@YFk5cf.W_FE ly c nf).
Local Abbreviation W_UW := (@YFk5cf.W_UW adr).
Local Abbreviation W_USH := (@YFk5cf.W_USH sha).
Local Abbreviation W_FW := (@YFk5cf.W_FW fadr).
Local Abbreviation W_FSH := (@YFk5cf.W_FSH shf).
Local Abbreviation at_R3 := (@YFk5cf.at_R3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_N3 := (@YFk5cf.at_N3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_RET3 := (@YFk5cf.at_RET3 _ regs0 mem0).
Local Abbreviation P_cells := (@YFk5cf.P_cells ly c maxc csz).
Local Abbreviation chunk_index := (@YFk5cf.chunk_index).
Local Abbreviation pstable := (@YFk5cf.pstable ly regs0 c).
Local Abbreviation all_disjoint_of_forall := (@YFk5cf.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@YFk5cf.kept_of_frame ly regs0 maxc mf au mu).
Local Abbreviation kept_of_frame2 := (@YFk5cf.kept_of_frame2 ly regs0 maxc mf au mu).
Local Abbreviation SKEL_TAILR := (@YFk5cf.SKEL_TAILR).
Local Abbreviation RFACTSR := (@YFk5cf.RFACTSR ly regs0 c).
Local Abbreviation stack_ivsR := (@YFk5cf.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := (@YFk5cf.zone_litR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_TR := (@YFk5cf.zone_TR _ ly regs0 c maxc mf au mu IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := (@YFk5cf.zone_CR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_RGR := (@YFk5cf.zone_RGR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation slots_not_WINR0 := (@YFk5cf.slots_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation fa_not_WINR0 := (@YFk5cf.fa_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation tail_ext_okR := (@YFk5cf.tail_ext_okR _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := (@YFk5cf.rdn_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation store_ok_of_presentR := (@YFk5cf.store_ok_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation cpy4_stretch := (@YFk5cf.cpy4_stretch _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 jex HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp).
Local Abbreviation facts3 := (@YFk5cf.facts3 _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation RFACTS3 := (@YFk5cf.RFACTS3 ly regs0 c).
Local Abbreviation tail_ext_ok3 := (@YFk5cf.tail_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation stack_ext_ok3 := (@YFk5cf.stack_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation scratch_headed := (@YFk5cf.scratch_headed).
Local Abbreviation mem_ok_scratch_present := (@YFk5cf.mem_ok_scratch_present _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY Hmf Hmu Hsp).
Local Abbreviation at_R3_run := (@YFk5cf.at_R3_run _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_run_ecall := (@YFk5cf.at_R3_run_ecall _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_pin := (@YFk5cf.at_R3_pin _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_arm := (@YFk5cf.at_R3_arm _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_forget := (@YFk5cf.at_R3_forget _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_noconds := (@YFk5cf.at_R3_noconds _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_weaken := (@YFk5cf.at_R3_weaken _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_facts := (@YFk5cf.at_R3_facts _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_strengthen := (@YFk5cf.at_R3_strengthen _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_eq := (@YFk5cf.at_R3_eq _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation CSAVED := (@YFk5cf.CSAVED).
Local Abbreviation sv_denot_SOff0 := (@YFk5cf.sv_denot_SOff0).
Local Abbreviation at_R3_ret := (@YFk5cf.at_R3_ret _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hra Htp).
Local Abbreviation at_N3_cont := (@YFk5cf.at_N3_cont _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation memset_stretch3 := (@YFk5cf.memset_stretch3 _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 jex HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp).
Local Abbreviation nth_Z_to_le_bytes4 := (@YFk5cf.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (@YFk5cf.popfree_stretch _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 jex HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Variable Hph : list Z.
Hypothesis HARm : ARmcf B ly S Hph (aview tfibsegs (w_H W) mem0).
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
Hypothesis Hjexv : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 68) 1 jex.
Hypothesis HQL : qloose S.
Hypothesis HAR : ARcf tfibsegs B ly S Hph W mem0 md0.
Local Abbreviation Pr_is := (@YFk5cf.Pr_is ly c).
Local Abbreviation RGv_is := (@YFk5cf.RGv_is ly c).
Local Abbreviation FAv_is := (@YFk5cf.FAv_is ly c HcR).
Local Abbreviation RBv_is := (@YFk5cf.RBv_is ly c HcR).
Local Abbreviation cls_wfR := (@YFkkcf.cls_wfR _ _ _ W ly mem0 c HcR B S Hph HARm Hinited).
Local Abbreviation cls_wf0 := (@YFkkcf.cls_wf0 _ _ _ W ly mem0 c HcR B S Hph HARm).
Local Abbreviation reg_facts0 := (@YFkkcf.reg_facts0 _ _ _ W ly regs0 mem0 c maxc nf mf au mu HcR B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_facts := (@YFkkcf.reg_facts _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hmax Hjex Hsp B S Hph HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (@YFkkcf.Hnf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmf' := (@YFkkcf.Hmf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmu' := (@YFkkcf.Hmu' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hcarved' := (@YFkkcf.Hcarved' _ _ _ W ly mem0 c au mu HcR B S Hph HARm Hau_def Hmu_def).
Local Abbreviation Hau_al' := (@YFkkcf.Hau_al' _ _ _ W ly mem0 c au csz HcR Hcsz B S Hph HARm Hau_def).
Local Abbreviation vis_present := (@YFkkcf.vis_present _ _ _ W ly regs0 mem0 maxc B S Hph HARm).
Local Abbreviation thread_present := (@YFkkcf.thread_present _ _ _ W ly regs0 mem0 c maxc nf mf au mu csz jex IMG LY HcR Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation rinfo_present := (@YFkkcf.rinfo_present _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HslotPres' := (@YFkkcf.HslotPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HfaPres' := (@YFkkcf.HfaPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation word_of_present := (@YFkkcf.word_of_present W ly regs0 mem0 maxc).
Local Abbreviation val_mem_lo4 := (@YFkkcf.val_mem_lo4 ly regs0 maxc).
Local Abbreviation junk_valuesR := (@YFkkcf.junk_valuesR _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation cell_sym := (@YFkkcf.cell_sym _ _ _ W ly mem0 B S TS Hph HARm).
Local Abbreviation cell_lit := (@YFkkcf.cell_lit _ _ _ W ly mem0 B S TS Hph HARm).
Local Abbreviation cell_state := (@YFkkcf.cell_state _ _ _ W ly mem0 B S Hph HARm).
Local Abbreviation In_acells_cache := (@YFkkcf.In_acells_cache ly regs0 c maxc HcR B S).
Local Abbreviation In_acells_region := (@YFkkcf.In_acells_region ly regs0 c maxc HcR B S).
Local Abbreviation cache_valsR := (@YFkkcf.cache_valsR _ _ _ W ly regs0 mem0 c maxc csz HcR Hmax Hcsz B S Hph HARm Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@YFkkcf.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (@YFkkcf.cache_valsU _ _ _ W ly regs0 mem0 maxc B S Hph HARm).
Local Abbreviation region_valsR := (@YFkkcf.region_valsR _ _ _ W ly regs0 mem0 c maxc nf mf au mu HcR B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation chunk_lit := (@YFkkcf.chunk_lit W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_lit_at := (@YFkkcf.chunk_lit_at W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_atom := (@YFkkcf.chunk_atom W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation REG0R3_ok_but35 := (@YFkkcf.REG0R3_ok_but35 _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation REG0R3_ok := (@YFkkcf.REG0R3_ok _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation REG0U3_ok := (@YFkkcf.REG0U3_ok _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation PAIRSR3_ok := (@YFkkcf.PAIRSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SPAN3_disj := (@YFkkcf.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation FACTSR3_ok := (@YFkkcf.FACTSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation SEEDR3_ok := (@YFkkcf.SEEDR3_ok _ _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation PAIRSU3_ok := (@YFkkcf.PAIRSU3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEEDU3_ok := (@YFkkcf.SEEDU3_ok _ _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
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
Ltac r3_station HR ss' :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_R3_eq Wx md X P ss ss' W' c' HR ltac:(vm_compute; reflexivity)) as H2; clear HR; rename H2 into HR end.
Ltac r3_run HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
let cs := eval vm_compute in (match nth_error (ss_mem ss') 0 with Some r => YP09.r_chunks r | None => [] end) in
eapply SRr_bind;
[ eapply (at_R3_run Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | exists cs; vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Ltac pin_zev3 := apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac r3_pin HR r e :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let t := eval vm_compute in (sr_get (ss_regs ss) r) in
let HU := fresh "HU" in
assert (HU : U E0 e = U E0 t);
[ | let H2 := fresh "HR" in
pose proof (at_R3_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HU) as H2;
clear HU HR; rename H2 into HR ] end.
Ltac r3_arm HR cnd tk a b :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HB := fresh "HB" in
assert (HB : branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk);
[ | let H2 := fresh "HR" in
pose proof (at_R3_arm Wx md X P ss W' c' cnd tk a b HR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HB) as H2;
clear HB HR; rename H2 into HR ] end.
Ltac r3_forget HR k clob :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_R3_forget Wx md X P ss W' c' k clob HR ltac:(unfold aHAV3; cbv; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H2;
clear HR; rename H2 into HR end.
Ltac r3_noconds HR :=
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in pose proof (at_R3_noconds Wx md X P ss W' c' HR) as H2; clear HR; rename H2 into HR end.
Ltac arm_zev3 := rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U;
rewrite !U_zev by (vm_compute; reflexivity); cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac rregS HS r R :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
pose proof (st_ok_reg_denot H E ss ms r HS) as R; change (sr_get (ss_regs ss) r) with e in R end.
Ltac memv3 HS HEn ss i off :=
let j := eval vm_compute in (chunk_index (match nth_error (ss_mem ss) i with Some r => YP09.r_chunks r | None => [] end) off) in
memv HS i j;
[ cbn [base_val YP09.r_base]; first [ unfold rP; rewrite (HEn 37%nat ltac:(cbv; zlia)), EaP | unfold rRG; rewrite (HEn 41%nat ltac:(cbv; zlia)), EaRG ];
unfold w64; rewrite unsigned_lit_small by zlia; zlia | | ].
Ltac val_atom HEn :=
first [ reflexivity
| lazymatch goal with |- sv_denot _ (SOff ?k _) = _ =>
cbn [sv_denot]; rewrite (HEn k ltac:(cbv; zlia));
rewrite ?EaN, ?EaMAX, ?EaCSZ, ?EaJEX, ?EaNF, ?EaMF, ?EaAU, ?EaMU, ?EaNFe, ?EaNFg, ?EaMF2, ?EaAUe, ?EaAUg;
unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity end ].
Ltac cells3 HS HEn ss RP RR DR F1' F2 :=
unfold P_cells; cbv zeta;
split; [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; destruct Ha as [Ha|[Ha|[Ha|Ha]]];
[ eapply (st_ok_window_apresent_off _ _ _ _ 35 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rP; rewrite (HEn 37%nat ltac:(cbv; zlia)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - RP; zlia); clear - Ha; zlia | off_by ltac:(clear - Ha RP DR; numconst; zlia) ]
| eapply (st_ok_window_apresent_off _ _ _ _ 36 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rRG; rewrite (HEn 41%nat ltac:(cbv; zlia)), EaRG; unfold w64; rewrite unsigned_lit_small by (clear - RR; zlia); clear - Ha; zlia | off_by ltac:(clear - Ha RR DR; numconst; zlia) ]
| eapply (st_ok_window_apresent_off _ _ _ _ 33 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rT; rewrite (HEn 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - F1' F2; numconst; try unfold T in *; zlia); try unfold T in *; clear - Ha; zlia | off_by ltac:(clear - Ha F1' F2; numconst; try unfold T in *; zlia) ]
| eapply (st_ok_window_apresent_off _ _ _ _ 34 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rT; rewrite (HEn 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - F1' F2; numconst; try unfold T in *; zlia); try unfold T in *; clear - Ha; zlia | off_by ltac:(clear - Ha F1' F2; numconst; try unfold T in *; zlia) ] ]
| repeat match goal with |- _ /\ _ => split end;
[ memv3 HS HEn ss 35%nat 0 | memv3 HS HEn ss 35%nat 4 | memv3 HS HEn ss 35%nat 8
| memv3 HS HEn ss 36%nat 0 | memv3 HS HEn ss 36%nat 8 | memv3 HS HEn ss 36%nat 16 | memv3 HS HEn ss 36%nat 24
| memv3 HS HEn ss 36%nat 32 | memv3 HS HEn ss 36%nat 40 | memv3 HS HEn ss 36%nat 48 | memv3 HS HEn ss 36%nat 56 | memv3 HS HEn ss 36%nat 68 ];
try val_atom HEn; try (clear; zlia) ].

Local Abbreviation PT := YFkbcf.PT.
Local Abbreviation fr := (@YFkjcf.fr c S).
Local Abbreviation hol := (@YFkjcf.hol c S).
Local Abbreviation SGf := (@YFkmcf.SG c maxc au csz S 0 mu mf [] fr hol).

Local Abbreviation leaf_G_fail := (@RepLeafcf.leaf_G_fail _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def HAR).
Local Abbreviation jex_of_cell := (@RepLeafcf.jex_of_cell _ W ly regs0 mem0 c maxc mf au mu csz jex adr mu2 fadr HcR Hjex B S Hjexv).
Local Abbreviation at_R3_addlit := (@RepLeafcf.at_R3_addlit _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation img_not_WINR0 := (@RepLeafcf.img_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_run_in := (@RepLeafcf.at_R3_run_in _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation U_jex0 := (@RepLeafcf.U_jex0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug Hjex).
Local Abbreviation at_R3_run_stk := (@RepLeafcf.at_R3_run_stk _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY Hmax Hn Hmf Hmu Hsp).
Local Abbreviation scratch2 := RepLeafcf.scratch2.

Lemma segA : jex = 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa3ed8 8 0x20443 ->
  forall W1 c1, at_R3 W md0 WINR0 PT R3_X W1 c1 -> SRr tfibsegs W1 c1 (at_R3 W md0 WINR0 PT R3_XP).
Proof.
intros Hj0 HTN W1 c1 HR.
assert (HX : forall a, WINR0 a -> WINR0 a) by (intros a H; exact H).
assert (HP : pstable PT) by (intros m m' _ _; exact I).
r3_arm HR BC_EQ true (SOff rJEX 0) (SLit 0).
{ rewrite branch_eq_U, U_jex0. apply Z.eqb_eq. rewrite Hj0. reflexivity. }
pose proof (at_R3_addlit W md0 WINR0 PT _ W1 c1 0xa2048 0xa3ed8 HR) as HR1. clear HR.
specialize (HR1 ltac:(unfold TFIB_IMG_LO; lia) ltac:(unfold TFIB_IMG_END; lia) ltac:(lia)
  ltac:(intros x Hx; apply img_not_WINR0; unfold TFIB_IMG_LO, TFIB_IMG_END; lia)
  ltac:(apply (cell_lit 0xa2048 8 0xa3ed8); vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
pose proof (at_R3_addlit W md0 WINR0 PT _ W1 c1 0xa3ed8 0x20443 HR1) as HR. clear HR1.
specialize (HR ltac:(unfold TFIB_IMG_LO; lia) ltac:(unfold TFIB_IMG_END; lia) ltac:(lia)
  ltac:(intros x Hx; apply img_not_WINR0; unfold TFIB_IMG_LO, TFIB_IMG_END; lia)
  HTN ltac:(vm_compute; reflexivity)).
r3_station HR R3_XT.
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x67e38 R3_XT)) in
let cs := eval vm_compute in (match nth_error (ss_mem R3_XP) 2 with Some r => YP09.r_chunks r | None => [] end) in
apply (at_R3_run_in W tfibtbl_rtA tfibtbl_rtA_ok 0x67e38 md0 WINR0 PT R3_XT R3_XP st W1 c1 HR);
  [ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP
  | exists cs; apply (nth_error_In _ 2); vm_compute; reflexivity ].
Qed.

Lemma pcells_XP : forall (E' : env) ms, env_agree aHAV3 E0 E' -> st_ok tfibsegs E' R3_XP (restrict (w_H W) ms) ->
  let m := mrestrict (w_H W) (ms_mem ms) in
  (forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) (ms_mem ms) a) /\
  val_mem tfibsegs m Pr 4 0 /\ val_mem tfibsegs m (Pr + 4) 4 maxc /\ val_mem tfibsegs m (Pr + 8) 8 csz /\
  val_mem tfibsegs m RGv 8 (2 ^ 60) /\ val_mem tfibsegs m (RGv + 8) 8 0 /\ val_mem tfibsegs m (RGv + 16) 8 nf /\
  val_mem tfibsegs m (RGv + 24) 8 mf /\ val_mem tfibsegs m (RGv + 32) 8 au /\ val_mem tfibsegs m (RGv + 40) 8 0 /\
  val_mem tfibsegs m (RGv + 48) 8 mu /\ val_mem tfibsegs m (RGv + 56) 8 0 /\ val_mem tfibsegs m (RGv + 68) 1 1.
Proof.
intros E' ms HE HS. cbv zeta.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] _].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & _).
assert (RP : 0 <= Pr /\ Pr + 16 < 2 ^ 64) by (clear - DR F2; numconst; zlia).
assert (RR : 0 <= RGv /\ RGv + 128 < 2 ^ 64) by (clear - DR; numconst; zlia).
split.
{ intros a Ha; destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - eapply (st_ok_window_apresent_off _ _ _ _ 37 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rP; rewrite (HEn 37%nat ltac:(cbv; zlia)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - RP; zlia); clear - Ha; zlia | off_by ltac:(clear - Ha RP DR; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off _ _ _ _ 38 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rRG; rewrite (HEn 41%nat ltac:(cbv; zlia)), EaRG; unfold w64; rewrite unsigned_lit_small by (clear - RR; zlia); clear - Ha; zlia | off_by ltac:(clear - Ha RR DR; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off _ _ _ _ 35 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rT; rewrite (HEn 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - F1' F2; numconst; try unfold T in *; zlia); try unfold T in *; clear - Ha; zlia | off_by ltac:(clear - Ha F1' F2; numconst; try unfold T in *; zlia) ].
  - eapply (st_ok_window_apresent_off _ _ _ _ 36 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold rT; rewrite (HEn 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - F1' F2; numconst; try unfold T in *; zlia); try unfold T in *; clear - Ha; zlia | off_by ltac:(clear - Ha F1' F2; numconst; try unfold T in *; zlia) ]. }
repeat match goal with |- _ /\ _ => split end;
[ memv3 HS HEn R3_XP 37%nat 0 | memv3 HS HEn R3_XP 37%nat 4 | memv3 HS HEn R3_XP 37%nat 8
| memv3 HS HEn R3_XP 38%nat 0 | memv3 HS HEn R3_XP 38%nat 8 | memv3 HS HEn R3_XP 38%nat 16 | memv3 HS HEn R3_XP 38%nat 24
| memv3 HS HEn R3_XP 38%nat 32 | memv3 HS HEn R3_XP 38%nat 40 | memv3 HS HEn R3_XP 38%nat 48 | memv3 HS HEn R3_XP 38%nat 56 | memv3 HS HEn R3_XP 38%nat 68 ];
try val_atom HEn; try (clear; zlia).
all: first [ clear - K1; zlia | clear - K4; numconst; zlia | clear - F0 F1 M0 M1; unfold kFreeArrayMax in *; zlia
           | clear - U0 U1 U2; numconst; zlia | clear; zlia ].
Qed.

Definition memA (m : word -> option byte) : word -> option byte :=
  fun x => if (RGv <=? bv_unsigned x) && (bv_unsigned x <? RGv + 8) then Some (Z_to_bv 8 0)
           else if bv_unsigned x =? RGv + 68 then Some (Z_to_bv 8 0) else m x.

Lemma memA_other : forall m x, ~ (RGv <= bv_unsigned x < RGv + 8) -> bv_unsigned x <> RGv + 68 -> memA m x = m x.
Proof.
intros m x H1 H2. unfold memA.
destruct ((RGv <=? bv_unsigned x) && (bv_unsigned x <? RGv + 8)) eqn:E1.
- exfalso. apply H1. apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. clear - E1 E2. lia.
- destruct (bv_unsigned x =? RGv + 68) eqn:E2; [apply Z.eqb_eq in E2; contradiction | reflexivity].
Qed.

Lemma memA_lock : forall m x, RGv <= bv_unsigned x < RGv + 8 -> memA m x = Some (Z_to_bv 8 0).
Proof.
intros m x H. unfold memA. replace ((RGv <=? bv_unsigned x) && (bv_unsigned x <? RGv + 8)) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - H; lia.
Qed.

Lemma memA_exh : forall m x, bv_unsigned x = RGv + 68 -> memA m x = Some (Z_to_bv 8 0).
Proof.
intros m x H. unfold memA. replace ((RGv <=? bv_unsigned x) && (bv_unsigned x <? RGv + 8)) with false.
- rewrite H, Z.eqb_refl. reflexivity.
- symmetry. apply Bool.andb_false_iff. right. apply Z.ltb_ge. clear - H. lia.
Qed.

Lemma memA_off_WINR0 : forall m x, ~ WINR0 (bv_unsigned x) -> memA m x = m x.
Proof.
intros m x Hx. apply memA_other.
- intros H. apply Hx. unfold WINR0. right. right. left. clear - H. lia.
- intros H. apply Hx. unfold WINR0. right. right. left. rewrite H. clear. lia.
Qed.

Lemma TZ_not_RG : forall a, T <= a < T + kThreadObjSize -> ~ (RGv <= a < RGv + 128).
Proof.
intros a Ha Hr. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT0. unfold zdisjoint in PT0. cbn [fst snd] in PT0.
pose proof derived_rangesR as DR. destruct DR as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & _ & _ & _ & _ & _ & _ & D17 & _).
pose proof (lo_space_in ly LY) as [SI1 SI2].
unfold T in Ha. clear - Ha Hr PT0 D8 D17 SI2. unfold kThreadObjSize, kPrimResvSize, kSpaceSize in *. lia.
Qed.

Lemma RG_bounds : 0 <= RGv /\ RGv + 128 < 2 ^ 64.
Proof.
pose proof (@ASAN_CEIL_range rc) as [CR1 _]. pose proof derived_rangesR as DR. destruct DR as (_ & _ & _ & _ & D5 & D6 & _).
clear - D5 D6 CR1. unfold kHighMemBeg in *. lia.
Qed.

Lemma Pr_not_RG : forall a, Pr <= a < Pr + 16 -> 0 <= a < 2 ^ 64 /\ ~ (RGv <= a < RGv + 128).
Proof.
intros a Ha. split.
- pose proof (@ASAN_CEIL_range rc) as [CR1 _]. pose proof high_factsR as (_ & HF2 & _). pose proof derived_rangesR as DR.
  destruct DR as (D1 & D2 & _). unfold YFk5cf.Pr in *. clear - Ha D1 D2 HF2 CR1. unfold kThreadObjSize in *. lia.
- apply TZ_not_RG. pose proof derived_rangesR as DR. destruct DR as (_ & D2 & _ & D4 & _). unfold YFk5cf.Pr in *. unfold T.
  clear - Ha D2 D4. unfold kThreadObjSize, t_cache in *. lia.
Qed.

Lemma stk_not_RG : forall a, sp0 - RSTACK <= a < sp0 -> 0 <= a < 2 ^ 64 /\ ~ (RGv <= a < RGv + 128).
Proof.
intros a Ha. pose proof Hsp as (SP1 & _). pose proof stack_ivsR as (_ & _ & _ & SI4 & SI5). fold sp0 in SI4, SI5.
pose proof derived_rangesR as DR. destruct DR as (_ & _ & _ & _ & _ & D6 & _). pose proof (lo_stk_ceil ly LY) as SC.
split.
- clear - Ha SI4 SI5. unfold kHighMemBeg, kHighMemEnd, RSTACK in *. lia.
- clear - Ha SP1 SC D6. unfold RSTACK in *. lia.
Qed.

Lemma memA_val : forall m a nb v, (forall k, (k < nb)%nat -> ~ (RGv <= a + Z.of_nat k < RGv + 8) /\ a + Z.of_nat k <> RGv + 68) ->
  0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) m) a nb v -> val_mem tfibsegs (mrestrict (w_H W) (memA m)) a nb v.
Proof.
intros m a nb v Hk A0 A1 Hv. apply (val_mem_ext (mrestrict (w_H W) m)); [|exact Hv].
intros k Hk'. destruct (Hk k Hk') as [N1 N2]. unfold mbyte, mrestrict.
assert (U : bv_unsigned (Z_to_bv 64 (a + Z.of_nat k)) = a + Z.of_nat k) by (apply unsigned_lit_small; clear - A0 A1 Hk'; lia).
rewrite memA_other; [reflexivity | rewrite U; exact N1 | rewrite U; exact N2].
Qed.

Lemma memA_val_Pr : forall m a nb v, Pr <= a -> a + Z.of_nat nb <= Pr + 16 ->
  val_mem tfibsegs (mrestrict (w_H W) m) a nb v -> val_mem tfibsegs (mrestrict (w_H W) (memA m)) a nb v.
Proof.
intros m a nb v A1 A2 Hv. destruct nb as [|nb'].
- intros k Hk. exfalso. clear - Hk. lia.
- pose proof (Pr_not_RG a ltac:(clear - A1 A2; lia)) as [[P0 _] _].
  pose proof (Pr_not_RG (a + Z.of_nat nb') ltac:(clear - A1 A2; lia)) as [[_ P1] _].
  apply memA_val; [| exact P0 | clear - P1; lia | exact Hv].
  intros k Hk. destruct (Pr_not_RG (a + Z.of_nat k) ltac:(clear - A1 A2 Hk; lia)) as [_ N].
  clear - N. split; intros H; apply N; lia.
Qed.

Lemma memA_val_RG : forall m off v, 8 <= off -> off + 8 <= 64 ->
  val_mem tfibsegs (mrestrict (w_H W) m) (RGv + off) 8 v -> val_mem tfibsegs (mrestrict (w_H W) (memA m)) (RGv + off) 8 v.
Proof.
intros m off v O1 O2 Hv. pose proof RG_bounds as [R0 R1].
apply memA_val; [| clear - R0 O1; lia | clear - R1 O2; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hv].
intros k Hk. clear - O1 O2 Hk. split; lia.
Qed.

Lemma memA_lock_val : forall m, (forall a, RGv <= a < RGv + 128 -> apresent (w_H W) m a) ->
  val_mem tfibsegs (mrestrict (w_H W) (memA m)) RGv 8 0.
Proof.
intros m PW k Hk. pose proof RG_bounds as [R0 R1]. unfold mbyte, mrestrict.
assert (U : bv_unsigned (Z_to_bv 64 (RGv + Z.of_nat k)) = RGv + Z.of_nat k) by (apply unsigned_lit_small; clear - R0 R1 Hk; lia).
rewrite memA_lock by (rewrite U; clear - Hk; lia).
destruct (PW (RGv + Z.of_nat k) ltac:(clear - Hk; lia)) as [Hh _]. rewrite Hh.
f_equal. f_equal. unfold YO0f.le_byte. rewrite Z.mod_0_l by (clear; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma memA_exh_val : forall m, (forall a, RGv <= a < RGv + 128 -> apresent (w_H W) m a) ->
  val_mem tfibsegs (mrestrict (w_H W) (memA m)) (RGv + 68) 1 0.
Proof.
intros m PW k Hk. assert (k = 0%nat) by (clear - Hk; lia). subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof RG_bounds as [R0 R1]. unfold mbyte, mrestrict.
assert (U : bv_unsigned (Z_to_bv 64 (RGv + 68)) = RGv + 68) by (apply unsigned_lit_small; clear - R0 R1; lia).
rewrite memA_exh by exact U.
destruct (PW (RGv + 68) ltac:(clear; lia)) as [Hh _]. rewrite Hh. reflexivity.
Qed.

Lemma memA_stk_present : forall m, (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) m a) ->
  forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (memA m) a.
Proof.
intros m PRS a Ha. destruct (PRS a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
destruct (stk_not_RG a Ha) as [A N].
assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact A).
rewrite memA_other; [exact Hb | rewrite U; clear - N; lia | rewrite U; clear - N; lia].
Qed.

Lemma pcells_memA : forall m, jex = 0 ->
  (forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) m a) ->
  val_mem tfibsegs (mrestrict (w_H W) m) Pr 4 0 -> val_mem tfibsegs (mrestrict (w_H W) m) (Pr + 4) 4 maxc ->
  val_mem tfibsegs (mrestrict (w_H W) m) (Pr + 8) 8 csz -> val_mem tfibsegs (mrestrict (w_H W) m) (RGv + 8) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) m) (RGv + 16) 8 nf -> val_mem tfibsegs (mrestrict (w_H W) m) (RGv + 24) 8 mf ->
  val_mem tfibsegs (mrestrict (w_H W) m) (RGv + 32) 8 au -> val_mem tfibsegs (mrestrict (w_H W) m) (RGv + 40) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) m) (RGv + 48) 8 mu -> val_mem tfibsegs (mrestrict (w_H W) m) (RGv + 56) 8 0 ->
  P_cells W 0 nf mf au mu jex (memA m).
Proof.
intros m Hj0 PW C1 C2 C3 C5 C6 C7 C8 C9 C10 C11. unfold P_cells. cbv zeta.
split.
{ intros a Ha. destruct (PW a Ha) as [Hh [b Hb]]. split; [exact Hh|].
  unfold memA. destruct ((RGv <=? bv_unsigned (Z_to_bv 64 a)) && (bv_unsigned (Z_to_bv 64 a) <? RGv + 8)); [eexists; reflexivity|].
  destruct (bv_unsigned (Z_to_bv 64 a) =? RGv + 68); [eexists; reflexivity | exists b; exact Hb]. }
assert (PWR : forall a, RGv <= a < RGv + 128 -> apresent (w_H W) m a) by (intros a Ha; apply PW; right; left; exact Ha).
split; [apply memA_val_Pr; [clear; lia | clear; cbn; lia | exact C1]|].
split; [apply memA_val_Pr; [clear; lia | clear; cbn; lia | exact C2]|].
split; [apply memA_val_Pr; [clear; lia | clear; cbn; lia | exact C3]|].
split; [exact (memA_lock_val m PWR)|].
split; [apply memA_val_RG; [clear; lia | clear; lia | exact C5]|].
split; [apply memA_val_RG; [clear; lia | clear; lia | exact C6]|].
split; [apply memA_val_RG; [clear; lia | clear; lia | exact C7]|].
split; [apply memA_val_RG; [clear; lia | clear; lia | exact C8]|].
split; [apply memA_val_RG; [clear; lia | clear; lia | exact C9]|].
split; [apply memA_val_RG; [clear; lia | clear; lia | exact C10]|].
split; [apply memA_val_RG; [clear; lia | clear; lia | exact C11]|].
rewrite Hj0. exact (memA_exh_val m PWR).
Qed.

Lemma arcf_at_call : jex = 0 -> YGcfXs.xs_mapped_cf ly S md0 -> cf_exh_off = 68 -> cf_errbuf_obj = 0xaa728 ->
  forall W1 c1, at_R3 W md0 WINR0 PT R3_XP W1 c1 ->
  exists ms1 mat1 E1, W1 = W /\ c1 = mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0) /\ env_agree aHAV3 E0 E1 /\
    st_ok tfibsegs E1 R3_XP (restrict (w_H W) ms1) /\ (forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
    (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
    ARcf tfibsegs B ly S Hph W (memA (ms_mem ms1)) (with_vm_backing (m_vm_lazy md0) mat1 md0).
Proof.
intros Hj0 HXM HOFF HOBJ W1 c1 HR.
destruct HR as (EW & ms1 & mat1 & E1 & Ec & HE & HS & MEQ & PRS & HPm).
exists ms1, mat1, E1. split; [exact EW|]. split; [exact Ec|]. split; [exact HE|]. split; [exact HS|].
split; [exact MEQ|]. split; [exact PRS|].
destruct (pcells_XP E1 ms1 HE HS) as (PW & C1 & C2 & C3 & _ & C5 & C6 & C7 & C8 & C9 & C10 & C11 & _).
set (regsF := regupd regs0 10%bv (Z_to_bv 64 0)).
assert (HRF : at_RET3 W 0 md0 WINR0 (fun m => PT m /\ P_cells W 0 nf mf au mu jex m) W
  (mkCfg (mkst regsF (getr regs0 1) (memA (ms_mem ms1)) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat1 md0))).
{ split; [reflexivity|]. exists regsF, (memA (ms_mem ms1)), mat1. split; [reflexivity|].
  split; [unfold regsF; apply getr_same; discriminate|].
  split; [intros r Hr; unfold regsF; apply getr_other; intros ->; cbn in Hr; repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); exact Hr|].
  split; [intros x Hx; rewrite (memA_off_WINR0 _ x Hx); exact (MEQ x Hx)|].
  split; [exact (memA_stk_present _ PRS)|].
  split; [exact I|].
  exact (pcells_memA _ Hj0 PW C1 C2 C3 C5 C6 C7 C8 C9 C10 C11). }
destruct (leaf_G_fail HXM HOFF HOBJ jex W _ (jex_of_cell (YG0ncf.ARcf_exh_cell tfibsegs B ly S Hph W mem0 md0 HAR) HOFF) HRF)
  as (regs1 & mem1 & md1 & Ec1 & AP & _).
unfold cfg_at in Ec1. injection Ec1 as E1' E2' E3'. subst mem1 md1.
exact (proj1 AP).
Qed.

Definition RLOW1 : YP09.region := YP09.mkRegion (Some 2%nat) (- RSTACK) (-224) (- RSTACK) (-224) [].
Definition R3_YC1 : sstate := Eval vm_compute in addreg RLOW1 R3_XC1.

Lemma STKC_sub : subregion STKC (match nth_error (ss_mem R3_XP) 2 with Some r => r | None => RNUL end).
Proof.
replace STKC with (trim_lo (match nth_error (ss_mem R3_XP) 2 with Some r => r | None => RNUL end) (-224)) by (vm_compute; reflexivity).
apply subregion_trim_lo.
Qed.

Lemma R3_YC1_eq : R3_YC1 = addreg RLOW1 (ss_after_call R3_XP [STKC] 112 0x37a9c).
Proof. vm_compute. reflexivity. Qed.

Lemma reseed1 : forall (W1 W2 : world tfibsegs) ms1 E1 regs2 (mem2 : word -> option byte),
  env_agree aHAV3 E0 E1 -> st_ok tfibsegs E1 R3_XP (restrict (w_H W1) ms1) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W1) (ms_mem ms1) a) ->
  regs_preserved (ms_regs ms1) regs2 ->
  (forall a, sp0 - 224 <= a < sp0 -> mem2 (Z_to_bv 64 a) = ms_mem ms1 (Z_to_bv 64 a)) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W2) mem2 a) ->
  exists E2, env_agree aHAV3 E0 E2 /\
    st_ok tfibsegs E2 R3_YC1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x37a9c) mem2 (seg_rom tfibsegs))).
Proof.
intros W1 W2 ms1 E1 regs2 mem2 HE HS Hp1 Hrp Hkeep Hpres.
assert (HB : forall E, env_agree aHAV3 E0 E -> base_val E (Some 2%nat) = sp0).
{ intros E [HE' _]. cbn [base_val]. rewrite (HE' 2%nat ltac:(unfold aHAV3; clear; lia)), E2. reflexivity. }
pose proof stack_ivsR as (_ & _ & _ & S4 & S5). fold sp0 in S4, S5.
assert (RK : Forall (region_kept tfibsegs E1 (ms_mem (restrict (w_H W1) ms1)) (mrestrict (w_H W2) mem2)) [STKC]).
{ apply Forall_cons; [|apply Forall_nil]. split.
  - intros a Ha. cbn [STKC YP09.r_base YP09.r_lo YP09.r_hi] in Ha. rewrite (HB E1 HE) in Ha.
    assert (Ha' : sp0 - RSTACK <= a < sp0) by (clear - Ha; unfold RSTACK; lia).
    assert (Hk2 : sp0 - 224 <= a < sp0) by (clear - Ha; lia).
    cbn [ms_mem restrict]. destruct (Hpres a Ha') as [Hh _]. destruct (Hp1 a Ha') as [Hh1 _].
    unfold mbyte, mrestrict. rewrite Hh, Hh1, (Hkeep a Hk2). reflexivity.
  - intros a Ha _. cbn [STKC YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite (HB E1 HE) in Ha.
    apply apresent_writable; [clear - Ha S4 S5; unfold TFIB_IMG_END, kHighMemBeg, kHighMemEnd, RSTACK in *; lia|].
    apply Hpres. clear - Ha. unfold RSTACK. lia. }
pose proof (st_ok_after_call tfibsegs 112 E1 R3_XP (restrict (w_H W1) ms1) regs2 (mrestrict (w_H W2) mem2) [STKC] 0x37a9c HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)
  ltac:(apply submem_drop, submem_drop, submem_keep; [exact STKC_sub | apply submem_nil])
  ltac:(vm_compute; reflexivity) Hrp RK) as HS2.
set (E2' := havoc E1 112 (map (getr regs2) CLOB)) in HS2.
assert (HE2 : env_agree aHAV3 E0 E2').
{ apply (env_agree_havoc_ge aHAV3 112 E0 E1); [unfold aHAV3; clear; lia | exact HE]. }
exists E2'. split; [exact HE2|].
rewrite <- restrict_mkst_fx in HS2.
rewrite R3_YC1_eq.
apply (st_ok_add_region E2' _ _ RLOW1 HS2 ltac:(vm_compute; reflexivity)).
- unfold region_ok, RLOW1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite (HB E2' HE2).
  split; [clear - S4 S5; unfold RSTACK, kHighMemBeg in *; lia|]. split; [clear - S4 S5; unfold RSTACK, kHighMemEnd in *; lia|].
  split; [|apply Forall_nil]. intros o Ho. cbn [ms_mem restrict mkst].
  apply apresent_writable; [clear - Ho S4 S5; unfold TFIB_IMG_END, kHighMemBeg, kHighMemEnd, RSTACK in *; lia|].
  apply Hpres. clear - Ho. unfold RSTACK in *. lia.
- apply all_disjoint_of_forall. intros r Hr. cbn [ss_mem ss_after_call In] in Hr. destruct Hr as [<-|[]].
  unfold extent_disjoint, RLOW1, STKC. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. left. clear. lia.
Qed.

Definition R3_YC1b : sstate := Eval vm_compute in runto 0x7ffffff0 R3_YC1.
Definition R3_YT31 : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_EQ true (SOff rCL 0) (SLit 31) R3_YC1b).
Definition R3_YC0 : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_YC1b).
Definition R3_YT16 : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_LTU false (SLit 16) (SOff rCL 0) R3_YC0).
Definition R3_YTM : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_LTU true (SLit 16) (SOff rCL 0) R3_YC0).
Definition R3_YK : sstate := Eval vm_compute in noconds (pin R3_YT16 13%bv (SOff rCSZ 0)).

Ltac r3_run_stk HR stop ss' lo HX :=
  lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W' ?c' =>
  let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL stop ss)) in
  let cs1 := eval vm_compute in (match nth_error (ss_mem ss') 0 with Some r => YP09.r_chunks r | None => [] end) in
  let cs2 := eval vm_compute in (match nth_error (ss_mem ss') 1 with Some r => YP09.r_chunks r | None => [] end) in
  eapply SRr_bind;
  [ apply (at_R3_run_stk Wx tfibtbl_rtA tfibtbl_rtA_ok stop md X P ss ss' st lo W' c' HR);
    [ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | intros ? ? _ _; exact I
    | split; [unfold RSTACK; lia | exists cs1, cs2; split; [apply (nth_error_In _ 0) | apply (nth_error_In _ 1)]; vm_compute; reflexivity] ]
  | clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.

Lemma U_cl : U E0 (SOff rCL 0) = c.
Proof. pose proof HcR as H. unfold rCL. apply (U_atom E0 36 c EaCL). clear - H. lia. Qed.
Lemma U_csz : U E0 (SOff rCSZ 0) = csz.
Proof. pose proof class_facts as (_ & _ & _ & K4 & _). unfold rCSZ. apply (U_atom E0 40 csz EaCSZ). clear - K4. unfold kMaxSize in *. lia. Qed.

Lemma segB : forall (Wx : world tfibsegs) md X W' c', (forall a, sp0 - RSTACK <= a < sp0 -> X a) ->
  at_R3 Wx md X PT R3_YC1 W' c' -> SRr tfibsegs W' c' (at_R3 Wx md X PT R3_YK).
Proof.
intros Wx md X W' c' HX HR.
r3_run_stk HR 0x7ffffff0 R3_YC1b (-224) HX.
destruct (Z.eq_dec c 31) as [E31|N31].
- r3_arm HR BC_EQ true (SOff rCL 0) (SLit 31). { rewrite branch_eq_U, U_cl. apply Z.eqb_eq. exact E31. }
  r3_run_stk HR 0x7ffffff0 R3_YT31 (-224) HX.
  r3_pin HR (13%bv : bv 5) (SOff rCSZ 0). { rewrite U_csz. change (U E0 (SLit 64)) with 64. rewrite Hcsz, E31. reflexivity. }
  r3_noconds HR. r3_station HR R3_YK. apply SRr_ret. exact HR.
- r3_arm HR BC_EQ false (SOff rCL 0) (SLit 31). { rewrite branch_eq_U, U_cl. apply Z.eqb_neq. exact N31. }
  r3_run_stk HR 0x7ffffff0 R3_YC0 (-224) HX.
  destruct (Z_le_gt_dec c 16) as [L16|G16].
  + r3_arm HR BC_LTU false (SLit 16) (SOff rCL 0). { rewrite branch_ltu_U, U_cl. change (U E0 (SLit 16)) with 16. apply Z.ltb_ge. exact L16. }
    r3_run_stk HR 0x7ffffff0 R3_YT16 (-224) HX.
    r3_pin HR (13%bv : bv 5) (SOff rCSZ 0).
    { pin_zev3. unfold rCSZ. rewrite EaCSZ, EaCL. unfold w64. pose proof class_facts as (_ & _ & _ & K4 & _).
      rewrite !unsigned_lit_small by (clear - K4 HcR; unfold kMaxSize in *; lia). rewrite !Z.add_0_r.
      change (Z.land (zcanon 5) 63) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
      rewrite (zcanon_id csz), (zcanon_id c), (zcanon_id (c * 32)) by (unfold M64; clear - K4 HcR; unfold kMaxSize in *; lia).
      rewrite Hcsz. unfold class_size. rewrite (proj2 (Z.eqb_neq c 31) N31), (proj2 (Z.leb_le c 16) L16). lia. }
    r3_noconds HR. r3_station HR R3_YK. apply SRr_ret. exact HR.
  + r3_arm HR BC_LTU true (SLit 16) (SOff rCL 0). { rewrite branch_ltu_U, U_cl. change (U E0 (SLit 16)) with 16. apply Z.ltb_lt. lia. }
    r3_run_stk HR 0x7ffffff0 R3_YTM (-224) HX.
    r3_pin HR (13%bv : bv 5) (SOff rCSZ 0).
    { pin_zev3. unfold rCSZ. rewrite EaCSZ, EaCL. unfold w64. pose proof class_facts as (_ & _ & _ & K4 & _).
      rewrite !unsigned_lit_small by (clear - K4 HcR; unfold kMaxSize in *; lia). rewrite !Z.add_0_r. rewrite Hcsz.
      assert (Hc : 17 <= c <= 30) by lia. clear - Hc. revert Hc. generalize c. intros x Hx.
      assert (Hx' : x = 17 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/ x = 30) by lia.
      destruct Hx' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]; vm_compute; reflexivity. }
    r3_noconds HR. r3_station HR R3_YK. apply SRr_ret. exact HR.
Qed.

End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepArmTcf.v (commit 3cae605a900a, blob 4f1bac526e07) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from cgif_file_fuzzer asan-ubsan ce511d541cda (pin 1c29845fe605), the cf layer at part 3c; module paths changed; 8 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); the read-only reads are cited by name, @cf_ro_reads CfImg_A (A/CfImgA.v:82), not as a typed list of numerals; the RELRO range is cited by name, @cf_relro_lo / @cf_relro_hi CfImg_A (A/CfImgA.v:81-82); ris_free's bounds are the named fields, so they are unfolded in L1 and L2 too. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill YGcfRoomPre.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepVisLcf RepModelcf RepModel2cf RepLeafcf RepArm2cf RepIFcf RepPrfT RepJunkcf RepKcf RepCallcf RepCompcf RepTailcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfImgA RepPrfcf RepVsncf RepAppTcf RepArmcf RepRelcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MnRefillSeamcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfInstImgA.
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

Hypothesis HHULL : cf_hull_ok S.
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
Local Abbreviation img_not_WINR0 := (@RepLeafcf.img_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation RIAP := (@RepLeafcf.RIAP _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation OBJAP := (@RepLeafcf.OBJAP _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation win_owned := (@RepLeafcf.win_owned _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu B S Hph HARm).
Local Abbreviation win_mn := (@RepLeafcf.win_mn _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation STKAP := (@RepLeafcf.STKAP _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation jex_of_cell := (@RepLeafcf.jex_of_cell _ W ly regs0 mem0 c maxc mf au mu csz jex adr mu2 fadr HcR Hjex B S Hjexv).
Local Abbreviation U_jex0 := (@RepLeafcf.U_jex0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug Hjex).
Local Abbreviation WF_S := (@RepLeafcf.WF_S _ _ _ W ly mem0 B S Hph HARm).
Local Abbreviation len_regions_S := (@RepLeafcf.len_regions_S _ _ _ W ly mem0 c HcR B S Hph HARm).
Local Abbreviation zrange_dec := RepLeafcf.zrange_dec.
Local Abbreviation at_R3_run_stk := (@RepLeafcf.at_R3_run_stk _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY Hmax Hn Hmf Hmu Hsp).
Local Abbreviation segA := (@RepArm2cf.segA _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hjex Hsp B S TS Hph HARm).
Local Abbreviation arcf_at_call := (@RepArm2cf.arcf_at_call _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hjexv HAR).
Local Abbreviation pcells_XP := (@RepArm2cf.pcells_XP _ _ W ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation memA := (@RepArm2cf.memA ly c).
Local Abbreviation memA_other := (@RepArm2cf.memA_other ly c).
Local Abbreviation memA_lock := (@RepArm2cf.memA_lock ly c).
Local Abbreviation memA_exh := (@RepArm2cf.memA_exh ly c).
Local Abbreviation memA_off_WINR0 := (@RepArm2cf.memA_off_WINR0 ly regs0 c).
Local Abbreviation RG_bounds := (@RepArm2cf.RG_bounds _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation Pr_not_RG := (@RepArm2cf.Pr_not_RG _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation stk_not_RG := (@RepArm2cf.stk_not_RG _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation reseed1 := (@RepArm2cf.reseed1 _ _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY Hmf Hmu Hsp).
Local Abbreviation segB := (@RepArm2cf.segB _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY HcR Hmax Hn Hcsz Hmf Hmu Hsp).
Local Abbreviation call1 := (@RepCallcf.call1 _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD Hph HARm Hgp Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hjexv HQL HHULL HAR).
Local Abbreviation call2 := (@RepCallcf.call2 _ _ _ _ W ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY HcR Hmax Hn Hcsz Hmf Hmu Hsp B Hph Hgp).
Local Abbreviation compose_core := (@RepCompcf.compose_core _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S Hph HARm Hchunks HAR).
Local Abbreviation cache_eta := (@RepLeafcf.cache_eta _ _ _ W ly mem0 c maxc HcR Hmax B S Hph HARm Hinited Hchunks).
Local Abbreviation scratch2 := RepLeafcf.scratch2.

Lemma arm2_cf : RepIFcf.printf_spec_cf B ->
  mu < tot -> kFreeArrayOffset < mu + kUserMapSize -> c <> kBatchClass -> YG00cf.exh_mem_cf S c = false ->
  YGcfXs.xs_mapped_cf ly S md0 -> ly_stk_lo ly + REP_STACK <= sp0 ->
  (forall a, sp0 - REP_STACK <= a < sp0 -> apresent (w_H W) mem0 a) ->
  cf_exh_off = 68 -> cf_errbuf_obj = 0xaa728 ->
  exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) -> errb_cells_cf B ly S (aview tfibsegs (w_H W) mem0) ->
  RepIFcf.rep_img_facts W mem0 -> YG00cf.ERRB_ROOM S -> WfP_cf (as_universe B) 1 1 0 S ->
  amreal tfibsegs (refill_tree_cf c S) W cfg0 (refill_leaf_core_cf B Hph ly S c W regs0 mem0 md0).
Proof.
intros HPR Hlt Hfull HBC Hexh HXM HREP HpresREP HOFF HOBJ HEXH HERRB HIMG HROOM HWF.
assert (Hj0 : jex = 0) by (rewrite (jex_of_cell HEXH HOFF), Hexh; reflexivity).
pose proof facts3 as (_ & _ & G3 & _). pose proof Hmu as ([U0 U1] & _).
pose proof (lo_stk_ceil ly LY) as SC. pose proof (@ASAN_CEIL_range rc) as [CR1 _].
pose proof (u64_range (getr regs0 2)) as U. pose proof Hsp as (SP1 & SP2 & _).
rewrite (RepModelcf.tree_classfull_cf c n need S HcR HBC Hinited Hchunks
  ltac:(rewrite cache_eta; cbn [pc_max]; exact Hmax)
  ltac:(rewrite Hn, Hmax; reflexivity)
  ltac:(rewrite <- Hnf_def; exact Hnlt)
  ltac:(rewrite <- Hnf_def; exact Hneed)
  ltac:(rewrite <- Hmu_def, <- Hau_def, <- Hcsz, <- Htot; exact Hlt)
  ltac:(rewrite <- Hmu_def, <- Hau_def, <- Hcsz, <- Htot; clear - Hlt Htot G3 U0 U1; unfold kMaxSize, kUserMapSize in *; lia)
  ltac:(rewrite <- Hmu_def; exact Hfull) Hexh).
apply RepModelcf.amreal_classfull_shift.
rewrite <- RepIFcf.len_render1, <- (RepIFcf.len_render2 c HcR).
set (L2 := Z.of_nat (length (RepIFcf.render2 c (class_size c)))).
set (S1 := RepModelcf.exh_set c S).
apply (amreal_SRr_pre tfibsegs _ W cfg0 _ (at_R3 W md0 WINR0 PT R3_XP)).
{ eapply SRr_bind; [exact (RepArmcf.seg_seed_X W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex
    need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved
    Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug mat0 msJ SEEDJ Hlt Hfull)|].
  intros W1 c1 _ HR. exact (segA Hj0 (RepIFcf.rif_toolname _ _ HIMG) W1 c1 HR). }
intros W1 c1 _ HR.
destruct (call1 Hj0 HXM HWF HROOM HBC HREP HpresREP HOFF HOBJ HEXH HERRB HIMG W1 c1 HR)
  as (ms1 & mat1 & E1 & -> & -> & HE1 & HS1 & MEQ1 & PREP1 & _ & PRE1 & ROOM1 & REGS1 & A10 & A11 & RA1 & SPZ1).
pose proof HERRB as (_ & _ & _ & _ & _ & _ & HSZ & HAL).
apply (RepKcf.printf_ipost B (RepKcf.post1_P S1 L2) _ Hph ly S1 W (ms_regs ms1) (ms_mem ms1) _ RepIFcf.FMT_OOM1
  RepIFcf.render1 (Some (RepIFcf.region_lock_addr ly c)) (fun S' => ibind (YG00cf.errb_append_cf L2 S') (fun r2 => IRet (tt, snd r2))) _ HPR).
{ apply RepKcf.post1_ipost; [clear; lia | clear; lia | | exact HSZ | exact HAL].
  unfold L2. rewrite (RepIFcf.len_render2 c HcR), RepIFcf.len_render1. pose proof (RepKcf.exh_len2_le c HcR).
  unfold exh_len1, kPage. clear - H. lia. }
{ exact PRE1. } { exact ROOM1. } { exact REGS1. } { exact A10. }
{ left. split; [reflexivity|]. split; [exact A11 | reflexivity]. }
{ rewrite RepIFcf.len_render1. unfold exh_len1. clear; lia. }
intros S' W2 c2 HP1 HPOST1.
destruct HPOST1 as (ly2 & regs2 & mem2 & md2 & Ec2 & PRE2 & SZ2 & L12 & WL12 & AR12 & IO12 & V1 & F1 & N1 & P1).
subst c2.
pose proof L12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L2LO & L2HI & _).
assert (STK1 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX_cf B ly S1 a)
  by (intros a Ha; exact (RepPrfT.rp_stack_not_AOX B _ Hph ly _ W _ _ a PRE1 Ha)).
assert (STK2 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX_cf B ly2 S' a)
  by (intros a Ha; apply (RepPrfT.rp_stack_not_AOX B _ Hph ly2 _ W2 _ _ a PRE2); rewrite L2LO, L2HI; exact Ha).
assert (KEEP1 : forall a, sp0 - 224 <= a < sp0 -> mem2 (Z_to_bv 64 a) = ms_mem ms1 (Z_to_bv 64 a)).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HREP U SC CR1; unfold sp0, REP_STACK in *; lia).
  assert (Hst : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - Ha HREP SP2; unfold sp0, REP_STACK in *; lia).
  apply F1; rewrite unsigned_lit_small by exact Ra; [exact (STK1 a Hst) | exact (STK2 a Hst) | rewrite SPZ1; clear - Ha; lia]. }
assert (PRES1 : forall a, sp0 - 1456 <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 224)) as [L|L].
  - apply P1. rewrite SPZ1. clear - Ha L. unfold RepIFcf.PR_STK, RepIFcf.APP_STK. lia.
  - destruct (RepCompcf.apresent_wle W W2 (ms_mem ms1) a WL12 (PREP1 a ltac:(clear - Ha L; unfold REP_STACK; lia))) as [Hh [b Hb]].
    split; [exact Hh|]. exists b. rewrite (KEEP1 a ltac:(clear - Ha L; lia)). exact Hb. }
apply (amreal_SRr_pre tfibsegs _ W2 _ _ _ (call2 W2 ms1 E1 ly2 S' regs2 mem2 md2 HE1 HS1
  (fun a Ha => PREP1 a ltac:(clear - Ha; unfold RSTACK, REP_STACK in *; lia)) AR12 KEEP1 PRES1 PRE2 L2LO L2HI HREP RA1)).
intros W3 c3 _ (-> & msK & matK & EK & -> & HEK & HSK & MEQK & PRSK & PREK & REGSK & K10 & K11 & K12 & K13 & RAK & SPZK).
apply (RepKcf.printf_ipost B (RepKcf.post2_P L2 S') _ Hph ly2 S' W2 (ms_regs msK) (ms_mem msK) _ RepIFcf.FMT_OOM2
  (RepIFcf.render2 c (class_size c)) (Some (RepIFcf.region_lock_addr ly c)) (fun S'' => IRet (tt, S'')) _ HPR).
{ apply RepKcf.post2_ipost. unfold L2. clear; lia. }
{ exact PREK. } { exact (RepKcf.room2 S S' c HcR HROOM SZ2). } { exact REGSK. } { exact K10. }
{ right. exists c, (class_size c). split; [reflexivity|]. split; [exact HcR|]. split; [reflexivity|].
  split; [exact K11|]. split; [exact K12|]. split; [rewrite <- Hcsz; exact K13 | reflexivity]. }
{ rewrite (RepIFcf.len_render2 c HcR). pose proof (RepKcf.exh_len2_le c HcR). clear - H. lia. }
intros S'' W4 c4 HP2 HPOST2.
destruct HPOST2 as (ly3 & regs3 & mem3 & md3 & Ec4 & PRE3 & SZ3 & L23 & WL23 & AR23 & IO23 & V2 & F2 & N2 & P2).
subst c4. cbn [amreal].
pose proof HP1 as (OS1 & G1 & _). pose proof HP2 as (OS2 & _ & _).
assert (L13 : layout_le (length (st_secs S1)) ly ly3) by exact (layout_le_trans _ _ ly ly2 ly3 G1 L12 L23).
destruct (RepCompcf.win3 ly c ly3 _ L13)
  as (_ & _ & _ & _ & WLK & WLO & WHI).
assert (STK3 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX_cf B ly3 S'' a)
  by (intros a Ha; apply (RepPrfT.rp_stack_not_AOX B _ Hph ly3 _ W4 _ _ a PRE3); rewrite WLO, WHI; exact Ha).
assert (KEEP3 : forall a, sp0 - 224 <= a < sp0 -> mem3 (Z_to_bv 64 a) = ms_mem msK (Z_to_bv 64 a)).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HREP U SC CR1; unfold sp0, REP_STACK in *; lia).
  assert (Hst : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - Ha HREP SP2; unfold sp0, REP_STACK in *; lia).
  apply F2; rewrite unsigned_lit_small by exact Ra; [exact (STK2 a Hst) | exact (STK3 a Hst) | rewrite SPZK; clear - Ha; lia]. }
assert (PRES3 : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W4) mem3 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 224)) as [L|L].
  - apply P2. rewrite SPZK. clear - Ha L. unfold RepIFcf.PR_STK, RepIFcf.APP_STK, RSTACK in *. lia.
  - destruct (RepCompcf.apresent_wle W2 W4 (ms_mem msK) a WL23 (PRSK a Ha)) as [Hh [b Hb]].
    split; [exact Hh|]. exists b. rewrite (KEEP3 a ltac:(clear - Ha L; lia)). exact Hb. }
assert (RS : reg S'' c = reg S1 c) by (rewrite (RepModel2cf.only_secs_reg _ _ c OS2), (RepModel2cf.only_secs_reg _ _ c OS1); reflexivity).
assert (CS : cache S'' c = cache S c) by (rewrite (RepModel2cf.only_secs_cache _ _ c OS2), (RepModel2cf.only_secs_cache _ _ c OS1); reflexivity).
assert (IS : st_cache_inited S'' = true)
  by (rewrite (RepModel2cf.only_secs_cache_inited _ _ OS2), (RepModel2cf.only_secs_cache_inited _ _ OS1); exact Hinited).
assert (XS : YG00cf.exh_mem_cf S'' c = true).
{ rewrite (RepModel2cf.only_secs_exh_mem _ _ c OS2), (RepModel2cf.only_secs_exh_mem _ _ c OS1).
  unfold S1. rewrite (RepModel2cf.exh_set_mem c c S (proj1 HcR) len_regions_S), Z.eqb_refl. reflexivity. }
assert (WLK' : RepIFcf.region_lock_addr ly3 c = RepIFcf.region_lock_addr ly c) by exact WLK.
pose proof PRE3 as PRE3t. rewrite <- WLK' in PRE3t.
eapply SRr_mono; [exact (RepTailcf.tail_cf W2 W4 ly ly3 _ regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex
  need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug B S'' Hph msK EK regs3 mem3 _
  HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2
  Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug L13 HEK HSK PRSK AR23 KEEP3 PRES3 PRE3t IS
  ltac:(rewrite CS; exact Hchunks)
  ltac:(rewrite RS, Hnf_def; unfold S1; rewrite (RepModel2cf.exh_set_free c S len_regions_S); reflexivity)
  ltac:(rewrite RS, Hmf_def; unfold S1; rewrite (RepModel2cf.exh_set_mapped_fa c S len_regions_S); reflexivity)
  ltac:(rewrite RS, Hau_def; unfold S1; rewrite (RepModel2cf.exh_set_alloc_user c S len_regions_S); reflexivity)
  ltac:(rewrite RS, Hmu_def; unfold S1; rewrite (RepModel2cf.exh_set_mapped_user c S len_regions_S); reflexivity)
  XS)|].
intros W5 c5 _ (regs4 & mem4 & md4 & -> & TAP & T10 & TPF & _ & TEX & TER & EW5 & TXM).
subst W5.
exact (compose_core ms1 mat1 W2 ly2 S' (ms_regs ms1) mem2 md2 msK matK W4 ly3 S'' (ms_regs msK) mem3 md3 regs4 mem4 md4
  HBC HREP MEQ1 PREP1 PRE1 HP1 HP2 SPZ1 SPZK PRE2 L12 WL12 IO12 V1 F1 N1 MEQK PRE3 L23 WL23 IO23 V2 F2 N2 P2
  TAP T10 TPF TEX TER TXM).
Qed.

End f.
End d.

Definition ris_rom (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => match seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) with
    | Some b => bv_unsigned b =? YO0f.le_byte v n k | None => false end) (seq 0 n).

Definition ris_rd (x : Z) : bool :=
  existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) (@cf_ro_reads CfImgA.CfImg_A) &&
  negb (existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_owned_static).
Definition ris_ro (a : Z) (n : nat) (v : Z) : bool :=
  ris_rom a n v && forallb (fun k => ris_rd (a + Z.of_nat k)) (seq 0 n).
Definition ris_str (a : Z) (s : list Z) : bool :=
  forallb (fun i => ris_ro (a + Z.of_nat i) 1 (nth i s 0)) (seq 0 (length s)).
Definition ris_free (x : Z) : bool :=
  (@cf_relro_lo CfImgA.CfImg_A <=? x) && (x <? @cf_relro_hi CfImgA.CfImg_A) && negb (existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_owned_static).
Definition ris_relro (a : Z) (n : nat) (v : Z) : bool :=
  ris_rom a n v && forallb (fun k => ris_free (a + Z.of_nat k)) (seq 0 n).

Lemma ris_rom_ok : forall a n v, ris_rom a n v = true -> forall k, (k < n)%nat ->
  seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k)).
Proof.
intros a n v H k Hk. unfold ris_rom in H. rewrite forallb_forall in H.
specialize (H k ltac:(apply in_seq; lia)). cbv beta in H.
destruct (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate H].
apply Z.eqb_eq in H. rewrite <- H, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma ris_vm_ro : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} B (H : word -> bool) mem a n v,
  TfibSyms B -> arodata_ok_cf (ci := CfImgA.CfImg_A) tfibsegs B mem -> ris_ro a n v = true ->
  val_mem tfibsegs (mrestrict H mem) a n v.
Proof.
intros fx rc cp B H mem a n v TS AD C k Hk. unfold ris_ro in C. apply andb_prop in C as [C1 C2].
rewrite forallb_forall in C2. specialize (C2 k ltac:(apply in_seq; lia)). cbv beta in C2. unfold ris_rd in C2.
apply andb_prop in C2 as [C2 C3]. apply negb_true_iff in C3.
rewrite (aro_read_cf tfibsegs B H mem _ AD).
- exact (ris_rom_ok a n v C1 k Hk).
- cbn [cf_ro_reads CfImgA.CfImg_A]. apply existsb_exists in C2 as (r & Hr & Hb).
  apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr.
  apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia.
- rewrite (ts_owned B TS). intros Hx. apply Exists_exists in Hx as (r & Hr & Hin).
  assert (E : existsb (fun r => (fst r <=? a + Z.of_nat k) && (a + Z.of_nat k <? fst r + snd r)) Tfib_owned_static = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. unfold in_zr in Hin.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in C3. discriminate C3.
Qed.

Lemma ris_ro_bytes : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} B (H : word -> bool) mem a s,
  TfibSyms B -> arodata_ok_cf (ci := CfImgA.CfImg_A) tfibsegs B mem -> ris_str a s = true ->
  RepIFcf.ro_bytes (mrestrict H mem) a s.
Proof.
intros fx rc cp B H mem a s TS AD C i Hi. unfold ris_str in C. rewrite forallb_forall in C.
specialize (C i ltac:(apply in_seq; lia)). cbv beta in C. exact (ris_vm_ro B H mem _ 1 _ TS AD C).
Qed.

Lemma ris_vm_relro : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} B (H : word -> bool) mem a n v,
  TfibSyms B -> arodata_ok_cf (ci := CfImgA.CfImg_A) tfibsegs B mem -> ris_relro a n v = true ->
  val_mem tfibsegs (mrestrict H mem) a n v.
Proof.
intros fx rc cp B H mem a n v TS AD C k Hk. unfold ris_relro in C. apply andb_prop in C as [C1 C2].
rewrite forallb_forall in C2. specialize (C2 k ltac:(apply in_seq; lia)). cbv beta in C2. unfold ris_free in C2.
apply andb_prop in C2 as [C2 C3]. apply andb_prop in C2 as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
apply negb_true_iff in C3.
rewrite (arodata_byte_cf tfibsegs B H mem _ AD).
- exact (ris_rom_ok a n v C1 k Hk).
- unfold aro_addr_cf. left. cbn [cf_relro_lo cf_relro_hi CfImgA.CfImg_A] in L1, L2 |- *. lia.
- rewrite (ts_owned B TS). intros Hx. apply Exists_exists in Hx as (r & Hr & Hin).
  assert (E : existsb (fun r => (fst r <=? a + Z.of_nat k) && (a + Z.of_nat k <? fst r + snd r)) Tfib_owned_static = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. unfold in_zr in Hin.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in C3. discriminate C3.
Qed.

Lemma rep_img_of_seam {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} :
  forall (B : asyms) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
    (md : Model),
  TfibSyms B -> ARcf (ci := CfImgA.CfImg_A) tfibsegs B ly S Hp W mem md ->
  arodata_ok_cf (ci := CfImgA.CfImg_A) tfibsegs B mem ->
  RepIFcf.rep_img_facts W mem.
Proof.
intros B Hp ly S W mem md TS AR AD.
pose proof AR as [M _]. destruct (amc_pf_cells _ _ _ _ _ M) as [PT PC].
constructor.
- exact (RepRelcf.rr_val_mem_of_cell B ly (w_H W) mem _ _ PT).
- exact (RepRelcf.rr_val_mem_of_cell B ly (w_H W) mem _ _ PC).
- apply (ris_vm_relro B); [exact TS | exact AD | vm_compute; reflexivity].
- constructor.
  + apply (ris_ro_bytes B); [exact TS | exact AD | vm_compute; reflexivity].
  + apply (ris_ro_bytes B); [exact TS | exact AD | vm_compute; reflexivity].
  + apply (ris_ro_bytes B); [exact TS | exact AD | vm_compute; reflexivity].
  + apply (ris_vm_ro B); [exact TS | exact AD | vm_compute; reflexivity].
  + apply (ris_vm_ro B); [exact TS | exact AD | vm_compute; reflexivity].
Qed.

Theorem classfull_cf_of_hyps {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} :
  @MnRefillSeamcf.refill_B3_classfull_cf fx rc CfImgA.CfImg_A cp.
Proof.
intros Hp W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  mat0 msJ B S sp0 T IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp HREP Hra Hra4096 Htp Ha0 Ha1 Ha2 Ha3
  Hnlt Hcarved Hau_al Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug SEEDJ Hpres0R HpresREP HslotPres HfaPres
  TS HTSD HARm Hgp Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv HEXH HERRB HQL HAR HXM
  HBR HER HWF0 HAROD HHULL [Hlt Hfull].
pose proof (rep_img_of_seam B Hp ly S W mem0 md0 TS HAR HAROD) as HIMG.
destruct (Z.eq_dec c kBatchClass) as [Eb|HBC].
{ exfalso. specialize (HBR Eb). unfold YG00cf.batch_room_cf in HBR. rewrite <- Eb, <- Hmu_def in HBR. clear - HBR Hfull. lia. }
rewrite (REP_W_other c HBC) in HREP, HpresREP.
destruct (YG00cf.exh_mem_cf S c) eqn:EX.
- exact (@RepLeafcf.arm1_cf fx rc CfImgA.CfImg_A cp W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug mat0 msJ SEEDJ B S TS HTSD Hp HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hjexv HAR Hlt Hfull HBC EX HXM HREP HpresREP
    CfInstImgA.cf_exh_off_A CfInstImgA.cf_errbuf_obj_A HEXH HERRB).
- exact (@arm2_cf fx rc CfImgA.CfImg_A cp W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug mat0 msJ SEEDJ B S TS HTSD Hp HARm Hgp Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hjexv HQL HHULL HAR (RepPrfcf.printf_ok B RepVsncf.vsn_ok (RepAppTcf.append_ok_preset B))
    Hlt Hfull HBC EX HXM HREP HpresREP CfInstImgA.cf_exh_off_A CfInstImgA.cf_errbuf_obj_A HEXH HERRB HIMG (proj1 (HER HBC)) (proj2 (HER HBC))).
Qed.

Print Assumptions classfull_cf_of_hyps.
Print Assumptions RepPrfcf.printf_ok.
Print Assumptions RepVsncf.vsn_ok.
Print Assumptions RepAppTcf.append_ok.
Print Assumptions RepAppTcf.append_ok_preset.

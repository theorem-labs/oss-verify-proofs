(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepCallcf.v (commit eb934de95d13, blob 8650cef7d76e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 8 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepVisLcf RepModelcf RepModel2cf RepLeafcf RepArm2cf RepIFcf RepPrfT RepJunkcf RepKcf.
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

Lemma rc_secs_grow_refl : forall l, secs_grow l l.
Proof.
intros l. split; [lia|]. split.
- intros i sm E. exists sm. split; [exact E|]. split; [lia|]. split; [intros H; exact H|].
  split; intros H; exact H.
- intros i sm' Hi E. apply List.nth_error_None in Hi. rewrite Hi in E. discriminate E.
Qed.

Lemma rc_hull_ok_exh_set : forall c0 S0, cf_hull_ok S0 -> cf_hull_ok (RepModelcf.exh_set c0 S0).
Proof.
intros c0 S0 H. apply (cf_hull_mono_back (RepModelcf.exh_set c0 S0) S0); [|exact H].
rewrite RepModelcf.rep_exh_secs. apply rc_secs_grow_refl.
Qed.

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
Local Abbreviation scratch2 := RepLeafcf.scratch2.

Lemma regs_XP : forall E1 (ms1 : machine_state), env_agree aHAV3 E0 E1 -> st_ok tfibsegs E1 R3_XP (restrict (w_H W) ms1) ->
  getr (ms_regs ms1) 1 = Z_to_bv 64 0x37a9c /\ getr (ms_regs ms1) 2 = Z_to_bv 64 (sp0 - 224) /\
  getr (ms_regs ms1) 3 = w64 (as_gp B) /\ getr (ms_regs ms1) 4 = w64 TFIB_TP /\
  getr (ms_regs ms1) 10 = w64 RepIFcf.FMT_OOM1 /\ getr (ms_regs ms1) 11 = w64 RepIFcf.A_TOOLNAME.
Proof.
intros E1 ms1 [HE _] HS.
rregS HS (1%bv : bv 5) R1. rregS HS (2%bv : bv 5) R2. rregS HS (3%bv : bv 5) R3. rregS HS (4%bv : bv 5) R4.
rregS HS (10%bv : bv 5) R10. rregS HS (11%bv : bv 5) R11.
cbn [sv_denot] in R1, R2, R3, R4, R10, R11.
rewrite (HE 2%nat ltac:(unfold aHAV3; clear; lia)), E2 in R2.
rewrite (HE 3%nat ltac:(unfold aHAV3; clear; lia)), (Er 3 (3%bv : bv 5) eq_refl) in R3.
split; [exact R1|]. split; [rewrite R2; reflexivity|]. split; [rewrite R3, Hgp; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [exact R4|]. split; [exact R10 | exact R11].
Qed.

Lemma present_call1 : forall m1 : word -> option byte, ly_stk_lo ly + REP_STACK <= sp0 ->
  (forall a, sp0 - REP_STACK <= a < sp0 -> apresent (w_H W) mem0 a) ->
  (forall x : word, ~ WINR0 (bv_unsigned x) -> m1 x = mem0 x) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) m1 a) ->
  forall a, sp0 - REP_STACK <= a < sp0 -> apresent (w_H W) m1 a.
Proof.
intros m1 HREP HP MEQ PRS a Ha. destruct (Z_lt_le_dec a (sp0 - RSTACK)) as [L|L]; [| apply PRS; clear - Ha L; lia].
pose proof (lo_stk_ceil ly LY) as SC. pose proof (@ASAN_CEIL_range rc) as [CR1 _]. pose proof (u64_range (getr regs0 2)) as U.
assert (Hge : ASAN_CEIL <= a) by (clear - Ha HREP SC; unfold REP_STACK in *; lia).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hge CR1 U; unfold sp0 in *; lia).
destruct (STKAP a Hge) as (N1 & N2 & N3 & N4 & N5).
assert (E : m1 (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ apply MEQ. rewrite unsigned_lit_small by exact Ra. unfold YFk5cf.WINR0. cbv zeta.
  intros [H|[H|[H|[H|H]]]]; [clear - H L; lia | exact (N1 H) | exact (N3 H) | exact (N4 H) | exact (N5 H)]. }
destruct (HP a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite E. exact Hb.
Qed.

Lemma held_call1 : forall m1 : word -> option byte,
  (forall a, RGv <= a < RGv + 128 -> apresent (w_H W) m1 a) ->
  val_mem tfibsegs (mrestrict (w_H W) m1) (RGv + 68) 1 1 ->
  (forall x : word, bv_unsigned x <> RepIFcf.region_lock_addr ly c + 68 ->
     RepIFcf.held_mem (Some (RepIFcf.region_lock_addr ly c)) m1 x = memA m1 x) /\
  RepIFcf.held_mem (Some (RepIFcf.region_lock_addr ly c)) m1 (Z_to_bv 64 (RepIFcf.region_lock_addr ly c + 68)) = Some (Z_to_bv 8 1).
Proof.
intros m1 PW C12. pose proof RG_bounds as [R0 R1].
change (RepIFcf.region_lock_addr ly c) with RGv. split.
- intros x Hx. unfold RepIFcf.held_mem, RepIFcf.in8, RepArm2cf.memA.
  destruct ((RGv <=? bv_unsigned x) && (bv_unsigned x <? RGv + 8)); [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) Hx). reflexivity.
- unfold RepIFcf.held_mem, RepIFcf.in8. rewrite unsigned_lit_small by (clear - R0 R1; lia).
  replace ((RGv <=? RGv + 68) && (RGv + 68 <? RGv + 8)) with false
    by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; clear; lia).
  destruct (PW (RGv + 68) ltac:(clear; lia)) as [Hh [b Hb]].
  pose proof (C12 0%nat ltac:(clear; lia)) as V. cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
  unfold mbyte, mrestrict in V. rewrite Hh, Hb in V. injection V as V. rewrite Hb, V. reflexivity.
Qed.

Lemma cells_call1 : forall m1 : word -> option byte, c <> kBatchClass -> cf_exh_off = 68 -> cf_errbuf_obj = 0xaa728 ->
  (forall x : word, ~ WINR0 (bv_unsigned x) -> m1 x = mem0 x) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) m1 a) ->
  (forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) m1 a) ->
  val_mem tfibsegs (mrestrict (w_H W) m1) (RGv + 68) 1 1 ->
  exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) -> errb_cells_cf B ly S (aview tfibsegs (w_H W) mem0) ->
  exh_cell_cf B ly (RepModelcf.exh_set c S) (aview tfibsegs (w_H W) m1) /\
  errb_cells_cf B ly (RepModelcf.exh_set c S) (aview tfibsegs (w_H W) m1).
Proof.
intros m1 HBC HOFF HOBJ MEQ PRS PW C12 HEXH HERRB. split.
- apply (RepKcf.exh_cell_set B ly S _ _ c HcR HBC len_regions_S HOFF HEXH).
  + intros c' Hc' Hne. destruct (RIAP c' Hc' Hne _ eq_refl) as (Ra & N0 & N1 & N2 & N3 & N4 & N5).
    apply aview_same. apply MEQ. rewrite unsigned_lit_small by exact Ra. unfold YFk5cf.WINR0. cbv zeta.
    intros [H|[H|[H|[H|H]]]]; [exact (N0 H) | exact (N1 H) | exact (N3 H) | exact (N4 H) | exact (N5 H)].
  + unfold aview. change (ly_space ly + kRegionInfoOff + 128 * c + 68) with (RGv + 68).
    pose proof (C12 0%nat ltac:(clear; lia)) as V. cbn [Z.of_nat] in V. rewrite Z.add_0_r in V. rewrite V. reflexivity.
- apply (errb_cells_cf_frame B ly ly S (RepModelcf.exh_set c S) _ _ HERRB eq_refl eq_refl eq_refl eq_refl).
  + intros a Ha. rewrite HOBJ in Ha. destruct (OBJAP a Ha) as (Ra & N0 & N1 & N2 & N3 & N4 & N5).
    apply aview_same. apply MEQ. rewrite unsigned_lit_small by exact Ra. unfold YFk5cf.WINR0. cbv zeta.
    intros [H|[H|[H|[H|H]]]]; [exact (N0 H) | exact (N1 H) | exact (N3 H) | exact (N4 H) | exact (N5 H)].
  + intros a Hv. set (x := Z_to_bv 64 a).
    assert (VIS : apresent (w_H W) m1 (bv_unsigned x) -> aview tfibsegs (w_H W) m1 a <> None).
    { intros [Hh [b Hb]]. unfold x in Hh, Hb. rewrite Z_to_bv_bv_unsigned in Hh, Hb.
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. }
    destruct (zrange_dec (sp0 - RSTACK) sp0 (bv_unsigned x)) as [D0|D0]; [exact (VIS (PRS _ D0))|].
    destruct (zrange_dec Pr (Pr + 16) (bv_unsigned x)) as [D1|D1]; [exact (VIS (PW _ (or_introl D1)))|].
    destruct (zrange_dec RGv (RGv + 128) (bv_unsigned x)) as [D3|D3]; [exact (VIS (PW _ (or_intror (or_introl D3))))|].
    destruct (zrange_dec (T + 2768) (T + 2800) (bv_unsigned x)) as [D4|D4]; [exact (VIS (PW _ (or_intror (or_intror (or_introl D4)))))|].
    destruct (zrange_dec (T + 2872) (T + 2888) (bv_unsigned x)) as [D5|D5]; [exact (VIS (PW _ (or_intror (or_intror (or_intror D5)))))|].
    assert (E : m1 x = mem0 x).
    { apply MEQ. unfold YFk5cf.WINR0. cbv zeta. intros [H|[H|[H|[H|H]]]]; contradiction. }
    rewrite (aview_same (w_H W) mem0 m1 a E). exact Hv.
Qed.

Lemma call1 : jex = 0 -> YGcfXs.xs_mapped_cf ly S md0 ->
  WfP_cf (as_universe B) 1 1 0 S -> YG00cf.ERRB_ROOM S -> c <> kBatchClass ->
  ly_stk_lo ly + REP_STACK <= sp0 -> (forall a, sp0 - REP_STACK <= a < sp0 -> apresent (w_H W) mem0 a) ->
  cf_exh_off = 68 -> cf_errbuf_obj = 0xaa728 ->
  exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) -> errb_cells_cf B ly S (aview tfibsegs (w_H W) mem0) ->
  RepIFcf.rep_img_facts W mem0 ->
  forall W1 c1, at_R3 W md0 WINR0 PT R3_XP W1 c1 ->
  exists ms1 mat1 E1, W1 = W /\
    c1 = cfg_at tfibsegs RepIFcf.A_PRINTF (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md0) mat1 md0) /\
    env_agree aHAV3 E0 E1 /\ st_ok tfibsegs E1 R3_XP (restrict (w_H W) ms1) /\
    (forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
    (forall a, sp0 - REP_STACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
    (forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) ->
       apresent (w_H W) (ms_mem ms1) a) /\
    RepIFcf.errb_call_pre B (Some (RepIFcf.region_lock_addr ly c)) Hph ly (RepModelcf.exh_set c S) W (ms_mem ms1)
      (with_vm_backing (m_vm_lazy md0) mat1 md0) /\
    RepIFcf.errb_room_for (RepModelcf.exh_set c S) (Z.of_nat (length RepIFcf.render1)) /\
    RepIFcf.errb_call_regs B RepIFcf.PR_STK ly W (ms_regs ms1) (ms_mem ms1) /\
    getr (ms_regs ms1) 10 = w64 RepIFcf.FMT_OOM1 /\ getr (ms_regs ms1) 11 = w64 RepIFcf.A_TOOLNAME /\
    raZ (ms_regs ms1) = 0x37a9c /\ spZ (ms_regs ms1) = sp0 - 224.
Proof.
intros Hj0 HXM HWF HROOM HBC HREP HpresREP HOFF HOBJ HEXH HERRB HIMG W1 c1 HR.
destruct (arcf_at_call Hj0 HXM HOFF HOBJ W1 c1 HR) as (ms1 & mat1 & E1 & EW & Ec & HE & HS & MEQ & PRS & HARA).
destruct (pcells_XP E1 ms1 HE HS) as (PW & _ & _ & _ & C4 & _ & _ & _ & _ & _ & _ & _ & C12).
destruct (regs_XP E1 ms1 HE HS) as (R1 & R2 & R3 & R4 & R10 & R11).
pose proof (present_call1 (ms_mem ms1) HREP HpresREP MEQ PRS) as PREP.
pose proof (u64_range (getr regs0 2)) as U. pose proof Hsp as (SP1 & SP2 & SP3).
pose proof (lo_stk_ceil ly LY) as SC. pose proof (@ASAN_CEIL_range rc) as [CR1 _].
assert (SPZ : spZ (ms_regs ms1) = sp0 - 224).
{ unfold spZ. rewrite R2. apply unsigned_lit_small. clear - HREP U SC CR1. unfold sp0, REP_STACK in *. lia. }
assert (Hexh : YG00cf.exh_mem_cf S c = false).
{ pose proof (jex_of_cell HEXH HOFF) as J. rewrite Hj0 in J. destruct (YG00cf.exh_mem_cf S c); [discriminate J | reflexivity]. }
exists ms1, mat1, E1. split; [exact EW|].
split.
{ rewrite Ec. unfold cfg_at. f_equal. rewrite (RepKcf.st_ok_cfg E1 R3_XP (w_H W) ms1 HS eq_refl) at 1. reflexivity. }
split; [exact HE|]. split; [exact HS|]. split; [exact MEQ|]. split; [exact PREP|]. split; [exact PW|].
split.
{ destruct (held_call1 (ms_mem ms1) (fun a Ha => PW a (or_intror (or_introl Ha))) C12) as [HA HB].
  destruct (cells_call1 (ms_mem ms1) HBC HOFF HOBJ MEQ PRS PW C12 HEXH HERRB) as [CX CE].
  unfold RepIFcf.errb_call_pre. split; [exact HOBJ|]. split; [exact HOFF|]. split; [exact LY|]. split; [exact IMG|].
  split; [exact TS|]. split; [exact HTSD|].
  split.
  { split; [right; exists c; split; [exact HcR | reflexivity]|]. split.
    - exact (RepJunkcf.ARcf_exh_set B c Hph ly S W (memA (ms_mem ms1)) _ _ HcR HBC HARA HA HB).
    - exact C4. }
  split; [unfold YGcfXs.xs_mapped_cf in *; intros e He; rewrite m_vmmaps_wvb; exact (HXM e He)|].
  split; [exact (RepModel2cf.wfp_exh_set (as_universe B) S c HcR Hexh HWF)|].
  split; [exact HQL|]. split; [exact CX|]. split; [exact CE|].
  split; [exact (RepKcf.rep_img_frame W mem0 (ms_mem ms1) HIMG (fun x Hx => MEQ x (img_not_WINR0 _ Hx))) | exact (rc_hull_ok_exh_set c S HHULL)]. }
split; [exact (RepKcf.room1 S c HROOM)|].
split.
{ unfold RepIFcf.errb_call_regs. split; [exact R3|]. split; [exact R4|].
  split; [rewrite R1; vm_compute; reflexivity|].
  split; [rewrite R1, unsigned_lit_small by (clear; lia); clear; lia|].
  rewrite SPZ. split; [clear - SP3; unfold sp0 in *; apply Z.mod_divide in SP3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16 - 224) with ((q - 14) * 16) by lia; apply Z.mod_mul; lia|].
  split; [clear - HREP; unfold RepIFcf.PR_STK, RepIFcf.APP_STK, REP_STACK in *; lia|].
  split; [clear - SP2; lia|].
  intros a Ha. apply PREP. clear - Ha. unfold RepIFcf.PR_STK, RepIFcf.APP_STK, REP_STACK in *. lia. }
split; [exact R10|]. split; [exact R11|].
split; [unfold raZ; rewrite R1; apply unsigned_lit_small; clear; lia|].
exact SPZ.
Qed.

Lemma regs_YK : forall E (ms : machine_state) (Wx : world tfibsegs), env_agree aHAV3 E0 E ->
  st_ok tfibsegs E RepArm2cf.R3_YK (restrict (w_H Wx) ms) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 0x37b10 /\ getr (ms_regs ms) 2 = Z_to_bv 64 (sp0 - 224) /\
  getr (ms_regs ms) 3 = w64 (as_gp B) /\ getr (ms_regs ms) 4 = w64 TFIB_TP /\
  getr (ms_regs ms) 10 = w64 RepIFcf.FMT_OOM2 /\ getr (ms_regs ms) 11 = w64 RepIFcf.REGION_MB /\
  getr (ms_regs ms) 12 = w64 c /\ getr (ms_regs ms) 13 = w64 csz.
Proof.
intros E ms Wx [HE _] HS.
rregS HS (1%bv : bv 5) R1. rregS HS (2%bv : bv 5) R2. rregS HS (3%bv : bv 5) R3. rregS HS (4%bv : bv 5) R4.
rregS HS (10%bv : bv 5) R10. rregS HS (11%bv : bv 5) R11. rregS HS (12%bv : bv 5) R12. rregS HS (13%bv : bv 5) R13.
cbn [sv_denot] in R1, R2, R3, R4, R10, R11, R12, R13.
rewrite (HE 2%nat ltac:(unfold aHAV3; clear; lia)), E2 in R2.
rewrite (HE 3%nat ltac:(unfold aHAV3; clear; lia)), (Er 3 (3%bv : bv 5) eq_refl) in R3.
rewrite (HE 36%nat ltac:(unfold aHAV3; clear; lia)), EaCL in R12.
rewrite (HE 40%nat ltac:(unfold aHAV3; clear; lia)), EaCSZ in R13.
split; [exact R1|]. split; [rewrite R2; reflexivity|].
split; [rewrite R3, Hgp; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [exact R4|]. split; [exact R10|]. split; [exact R11|].
split; [rewrite R12; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
rewrite R13; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.
Qed.

Local Abbreviation at_R3m mm := (@YFk5cf.at_R3 _ ly regs0 mm c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation segBm mm := (@RepArm2cf.segB _ _ ly regs0 mm c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY HcR Hmax Hn Hcsz Hmf Hmu Hsp).

Lemma call2 : forall (W2 : world tfibsegs) ms1 E1 ly2 S' regs2 mem2 md2,
  env_agree aHAV3 E0 E1 -> st_ok tfibsegs E1 R3_XP (restrict (w_H W) ms1) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) ->
  aregs_preserved (ms_regs ms1) regs2 ->
  (forall a, sp0 - 224 <= a < sp0 -> mem2 (Z_to_bv 64 a) = ms_mem ms1 (Z_to_bv 64 a)) ->
  (forall a, sp0 - 1456 <= a < sp0 -> apresent (w_H W2) mem2 a) ->
  RepIFcf.errb_call_pre B (Some (RepIFcf.region_lock_addr ly c)) Hph ly2 S' W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo ly -> ly_stk_hi ly2 = ly_stk_hi ly -> ly_stk_lo ly + REP_STACK <= sp0 ->
  raZ (ms_regs ms1) = 0x37a9c ->
  SRr tfibsegs W2 (cfg_at tfibsegs (raZ (ms_regs ms1)) regs2 mem2 md2) (fun W3 c3 => W3 = W2 /\ exists msK matK EK,
    c3 = cfg_at tfibsegs RepIFcf.A_PRINTF (ms_regs msK) (ms_mem msK) (with_vm_backing (m_vm_lazy md2) matK md2) /\
    env_agree aHAV3 E0 EK /\ st_ok tfibsegs EK RepArm2cf.R3_YK (restrict (w_H W2) msK) /\
    (forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) -> ms_mem msK x = mem2 x) /\
    (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W2) (ms_mem msK) a) /\
    RepIFcf.errb_call_pre B (Some (RepIFcf.region_lock_addr ly c)) Hph ly2 S' W2 (ms_mem msK) (with_vm_backing (m_vm_lazy md2) matK md2) /\
    RepIFcf.errb_call_regs B RepIFcf.PR_STK ly2 W2 (ms_regs msK) (ms_mem msK) /\
    getr (ms_regs msK) 10 = w64 RepIFcf.FMT_OOM2 /\ getr (ms_regs msK) 11 = w64 RepIFcf.REGION_MB /\
    getr (ms_regs msK) 12 = w64 c /\ getr (ms_regs msK) 13 = w64 csz /\
    raZ (ms_regs msK) = 0x37b10 /\ spZ (ms_regs msK) = sp0 - 224).
Proof.
intros W2 ms1 E1 ly2 S' regs2 mem2 md2 HE1 HS1 Hp1 Hrp Hkeep Hpres HPRE HLO HHI HREP HRA.
pose proof (u64_range (getr regs0 2)) as U. pose proof Hsp as (SP1 & SP2 & SP3).
pose proof (lo_stk_ceil ly LY) as SC. pose proof (@ASAN_CEIL_range rc) as [CR1 _].
destruct (reseed1 W W2 ms1 E1 regs2 mem2 HE1 HS1 Hp1 (RepKcf.aregs_regs _ _ Hrp) Hkeep
  (fun a Ha => Hpres a ltac:(clear - Ha; unfold RSTACK in *; lia))) as (E2' & HE2 & HS2).
set (X := fun a => sp0 - RSTACK <= a < sp0).
assert (HR : at_R3m mem2 W2 md2 X PT RepArm2cf.R3_YC1 W2 (cfg_at tfibsegs (raZ (ms_regs ms1)) regs2 mem2 md2)).
{ split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 0x37a9c) mem2 (seg_rom tfibsegs)), (vmst_materialized (m_vm md2)), E2'.
  split; [rewrite RepKcf.wvb_self, HRA; reflexivity|]. split; [exact HE2|]. split; [exact HS2|].
  split; [intros x _; reflexivity|]. split; [intros a Ha; apply Hpres; clear - Ha; unfold RSTACK in *; lia|]. exact I. }
eapply SRr_mono; [exact (segBm mem2 W2 md2 X W2 _ (fun a Ha => Ha) HR)|].
intros W3 c3 _ (EW & msK & matK & EK & Ec & HEK & HSK & MEQK & PRSK & _).
split; [exact EW|]. exists msK, matK, EK.
destruct (regs_YK EK msK W2 HEK HSK) as (R1 & R2 & R3 & R4 & R10 & R11 & R12 & R13).
assert (SPZ : spZ (ms_regs msK) = sp0 - 224).
{ unfold spZ. rewrite R2. apply unsigned_lit_small. clear - HREP U SC CR1. unfold sp0, REP_STACK in *. lia. }
assert (PK : forall a, sp0 - 1456 <= a < sp0 -> apresent (w_H W2) (ms_mem msK) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - RSTACK)) as [L|L]; [| apply PRSK; clear - Ha L; lia].
  assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HREP U SC CR1; unfold sp0, REP_STACK in *; lia).
  destruct (Hpres a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  rewrite (MEQK (Z_to_bv 64 a)); [exact Hb|]. rewrite unsigned_lit_small by exact Ra. unfold X. clear - L. lia. }
split.
{ rewrite Ec. unfold cfg_at. f_equal. rewrite (RepKcf.st_ok_cfg EK RepArm2cf.R3_YK (w_H W2) msK HSK eq_refl) at 1. reflexivity. }
split; [exact HEK|]. split; [exact HSK|]. split; [exact MEQK|]. split; [exact PRSK|].
split.
{ apply (RepPrfT.pre_stack_keep_wvb B _ Hph ly2 S' W2 mem2 md2 (ms_mem msK) matK (sp0 - RSTACK) sp0 HPRE).
  - rewrite HLO. clear - SP1. lia.
  - rewrite HHI. exact SP2.
  - intros x Hx. apply MEQK. exact Hx.
  - exact PRSK. }
split.
{ unfold RepIFcf.errb_call_regs. split; [exact R3|]. split; [exact R4|].
  split; [rewrite R1; vm_compute; reflexivity|].
  split; [rewrite R1, unsigned_lit_small by (clear; lia); clear; lia|].
  rewrite SPZ. split; [clear - SP3; unfold sp0 in *; apply Z.mod_divide in SP3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16 - 224) with ((q - 14) * 16) by lia; apply Z.mod_mul; lia|].
  split; [rewrite HLO; clear - HREP; unfold RepIFcf.PR_STK, RepIFcf.APP_STK, REP_STACK in *; lia|].
  split; [rewrite HHI; clear - SP2; lia|].
  intros a Ha. apply PK. clear - Ha. unfold RepIFcf.PR_STK, RepIFcf.APP_STK in *. lia. }
split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
split; [unfold raZ; rewrite R1; apply unsigned_lit_small; clear; lia|].
exact SPZ.
Qed.

End f.
End d.

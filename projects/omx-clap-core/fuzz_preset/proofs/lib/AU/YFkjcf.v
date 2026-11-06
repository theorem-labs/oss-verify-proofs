(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YFkjcf.v (commit 4d286b2e618d, file sha256 412b1ce81d98) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFkjcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 1ac5cc609b4e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (ReallocPrimary.CfW, lane W, cf refill re-base, B3 half; base on d50ec3c8a93a): YFkjcf, the cf twin of YFkj.v (this tree's copy, = c5 8d6c9f45705b).
   A hand port of YFkj.v at commit 8d6c9f45705b (its mechanical part scripted outside the tree): imports YFkpcf / YFhmcf / YFhncf and the B3 cf twins; RI+68 is the junk
   atom rJEX = 55 of YFkpcf with value jex (0 <= jex < 2 ^ 8), so the B3 atoms are 56..69; the text is otherwise YFkj.v verbatim.
   EVENT-FREE: no st_nev, EV_A, EV_MAX, EV_BIG, mtr_ok, aregime, refill_reg, qloosem or non-cf abudget.
   rule 24: no function proved (kind: re-base of the proved refill walk onto the cf instance). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YE3d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB19 YF0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFl1 YFhy YFis. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFkpcf YFk6cf YFk5cf. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhz. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFk8cf YFk7cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFk4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFk3 YB1q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFhmcf YFkacf YFkkcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstRefill.
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
Section g.
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
Local Abbreviation cls_wfR := (@YFkkcf.cls_wfR _ _ W ly mem0 c HcR B S Hph HARm Hinited).
Local Abbreviation cls_wf0 := (@YFkkcf.cls_wf0 _ _ W ly mem0 c HcR B S Hph HARm).
Local Abbreviation reg_facts0 := (@YFkkcf.reg_facts0 _ _ W ly regs0 mem0 c maxc nf mf au mu HcR B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_facts := (@YFkkcf.reg_facts _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hmax Hjex Hsp B S Hph HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (@YFkkcf.Hnf' _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmf' := (@YFkkcf.Hmf' _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmu' := (@YFkkcf.Hmu' _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hcarved' := (@YFkkcf.Hcarved' _ _ W ly mem0 c au mu HcR B S Hph HARm Hau_def Hmu_def).
Local Abbreviation Hau_al' := (@YFkkcf.Hau_al' _ _ W ly mem0 c au csz HcR Hcsz B S Hph HARm Hau_def).
Local Abbreviation vis_present := (@YFkkcf.vis_present _ _ W ly regs0 mem0 maxc B S Hph HARm).
Local Abbreviation thread_present := (@YFkkcf.thread_present _ _ W ly regs0 mem0 c maxc nf mf au mu csz jex IMG LY HcR Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation rinfo_present := (@YFkkcf.rinfo_present _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HslotPres' := (@YFkkcf.HslotPres' _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HfaPres' := (@YFkkcf.HfaPres' _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation word_of_present := (@YFkkcf.word_of_present W ly regs0 mem0 maxc).
Local Abbreviation val_mem_lo4 := (@YFkkcf.val_mem_lo4 ly regs0 maxc).
Local Abbreviation junk_valuesR := (@YFkkcf.junk_valuesR _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation cell_sym := (@YFkkcf.cell_sym _ _ W ly mem0 B S TS Hph HARm).
Local Abbreviation cell_lit := (@YFkkcf.cell_lit _ _ W ly mem0 B S TS Hph HARm).
Local Abbreviation cell_state := (@YFkkcf.cell_state _ _ W ly mem0 B S Hph HARm).
Local Abbreviation In_acells_cache := (@YFkkcf.In_acells_cache ly regs0 c maxc HcR B S).
Local Abbreviation In_acells_region := (@YFkkcf.In_acells_region ly regs0 c maxc HcR B S).
Local Abbreviation cache_valsR := (@YFkkcf.cache_valsR _ _ W ly regs0 mem0 c maxc csz HcR Hmax Hcsz B S Hph HARm Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@YFkkcf.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (@YFkkcf.cache_valsU _ _ W ly regs0 mem0 maxc B S Hph HARm).
Local Abbreviation region_valsR := (@YFkkcf.region_valsR _ _ W ly regs0 mem0 c maxc nf mf au mu HcR B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation chunk_lit := (@YFkkcf.chunk_lit W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_lit_at := (@YFkkcf.chunk_lit_at W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_atom := (@YFkkcf.chunk_atom W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation REG0R3_ok_but35 := (@YFkkcf.REG0R3_ok_but35 _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation REG0R3_ok := (@YFkkcf.REG0R3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation REG0U3_ok := (@YFkkcf.REG0U3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation PAIRSR3_ok := (@YFkkcf.PAIRSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SPAN3_disj := (@YFkkcf.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation FACTSR3_ok := (@YFkkcf.FACTSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation SEEDR3_ok := (@YFkkcf.SEEDR3_ok _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation PAIRSU3_ok := (@YFkkcf.PAIRSU3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEEDU3_ok := (@YFkkcf.SEEDU3_ok _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
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
Local Open Scope am_scope.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := amc_wf B ly S Hph rd0 HARm.
Definition fr : list fseg := rg_free (reg S c).
Definition hol : list (Z * Z) := rg_holes (reg S c).
Lemma len_facts3 : length (st_regions S) = 32%nat /\ length (st_cache S) = 32%nat /\ (Z.to_nat c < 32)%nat.
Proof. pose proof (wfc_len_regions _ _ _ _ _ WF). pose proof (wfc_len_cache _ _ _ _ _ WF). repeat split; try assumption. clear - HcR. zlia. Qed.
Lemma reg_S : reg S c = mkRegion mu au mf fr hol.
Proof. rewrite Hmu_def, Hau_def, Hmf_def. unfold fr, hol. destruct (reg S c); reflexivity. Qed.
Lemma reg_upd3 : forall r', reg (upd_reg c r' S) c = r'.
Proof. intros r'. pose proof len_facts3 as (L1 & _ & L3). apply reg_upd_reg; [clear - HcR; zlia | rewrite L1; exact L3]. Qed.
Lemma cache_upd3 : forall r' p', cache (upd_pc c p' (upd_reg c r' S)) c = p'.
Proof. intros r' p'. pose proof len_facts3 as (_ & L2 & L3). apply cache_upd_pc; [clear - HcR; zlia | unfold upd_reg; cbn; rewrite L2; exact L3]. Qed.
Lemma PM3 : pc_max (cache S c) = maxc.
Proof. pose proof (wfc_classes _ _ _ _ _ WF c HcR) as C. unfold wf_class_cf in C. rewrite Hinited in C. rewrite Hmax. exact (proj1 (wrc_cache _ _ _ _ _ _ C)). Qed.
(* cgif's WF1 built WfP 1 0 0 from Wf and the refill regime's event premise (prim_user_mapped S + kUserMapSize <=
   kUserMapSize * st_nev S), dropped in the cf layer. The cf walk runs from the call state (refill_spec_core_cf,
   YGcfInstRefill.v:171 at d80162ffa5c9, unticked), whose refill_state_gen_cf carries WfP_cf (as_universe B) 1 0 0 S
   (one user map of credit, :115): the B3 Section takes it as HWT. *)
Hypothesis HWT : WfP_cf (as_universe B) 1 0 0 S.
Lemma WF1 : WfP_cf (as_universe B) 1 0 0 S.
Proof. exact HWT. Qed.
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
intros [|]; unfold St1, rg1, MU1, HO1; [reflexivity|].
pose proof len_facts3 as (L1 & _ & L3). rewrite <- reg_S. symmetry. apply upd_reg_same; [clear - HcR; zlia | rewrite L1; exact L3].
Qed.
Lemma reg_S1 : forall (xg : bool), reg (St1 xg) c = rg1 xg.
Proof. intros xg. rewrite S1_eq. apply reg_upd3. Qed.
Lemma S2_eq : forall (xg yg : bool), St2 xg yg = upd_reg c (rg2 xg yg) S.
Proof. intros xg [|]; unfold St2, rg2, MF2, HO2; [reflexivity | rewrite S1_eq; reflexivity]. Qed.
Lemma reg_S2 : forall (xg yg : bool), reg (St2 xg yg) c = rg2 xg yg.
Proof. intros xg yg. rewrite S2_eq. apply reg_upd3. Qed.
Lemma upd_S1 : forall (xg : bool) r', upd_reg c r' (St1 xg) = upd_reg c r' S.
Proof. intros xg r'. rewrite S1_eq. apply upd_reg_upd_reg. Qed.
Lemma upd_S2 : forall (xg yg : bool) r', upd_reg c r' (St2 xg yg) = upd_reg c r' S.
Proof. intros xg yg r'. rewrite S2_eq. apply upd_reg_upd_reg. Qed.
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
assert (L : need * csz < ncg * csz + csz) by (clear - HC G3 G5 G15 G19b U0 U1; unfold kMaxSize, kUserMapSize in *; zlia).
assert (NN : need <= ncg) by (clear - L K4 G1 G18; nia).
repeat split; first [ assumption | clear - G21; zlia | rewrite G15; clear - U0 U1; unfold kUserMapSize; zlia | rewrite G15; exact HR3 | rewrite Hncg; reflexivity ].
- destruct G17 as [G17a G17b].
assert (L : need * csz < nce * csz + csz) by (clear - HC G5 G17b; zlia).
assert (NN : need <= nce) by (clear - L K4 G1 G16; nia).
repeat split; first [ assumption | clear - G20; zlia | clear - U0 U1 G17a G16 K4; nia | clear - U2; zlia | rewrite Hnce; reflexivity ].
Qed.
Lemma round_user : mu < tot -> round_up (tot - mu) kUserMapSize = kUserMapSize.
Proof.
intros HC. pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & _). pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
rewrite <- (Z.add_0_l kUserMapSize) at 2. apply round_up_step; [unfold kUserMapSize; clear; zlia | clear; reflexivity |].
clear - HC G3 G5 U0 U1. unfold kMaxSize, kUserMapSize in *. zlia.
Qed.
Lemma round_fa : forall (xg : bool), XC3 xg ->
mf < 4 * NF1 xg -> round_up (4 * NF1 xg) kFreeArrayMapSize = mf2.
Proof.
intros xg HC Hlt. pose proof (factsX3 xg HC) as ([N0 N1] & N2 & _). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] M2].
rewrite Hmf2. apply round_up_step; [unfold kFreeArrayMapSize; clear; zlia | exact M2 |]. clear - N0 N1 N2 F0 F1 Hlt. unfold kFreeArrayMapSize. zlia.
Qed.
Lemma runs_ok_new : forall (xg : bool), XC3 xg -> runs_ok (FRun au (NC1 xg) :: fr).
Proof.
intros xg HC. pose proof (factsX3 xg HC) as (_ & _ & _ & _ & NN & _). pose proof facts3 as (G1 & _).
constructor; [clear - NN G1; zlia|]. unfold fr. exact (wrc_runs _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WF c HcR)).
Qed.
Lemma pop_new : forall (xg : bool), XC3 xg ->
exists tops rest, fa_pop_n 10000 csz n (FRun au (NC1 xg) :: fr) [] = Some (tops, rest) /\
fa_elems csz (FRun au (NC1 xg) :: fr) = tops ++ fa_elems csz rest /\ fa_len rest = NF1 xg - n /\ runs_ok rest /\ Z.of_nat (length tops) = n.
Proof.
intros xg HC. pose proof (runs_ok_new xg HC) as RU. pose proof (factsX3 xg HC) as ([N0 N1] & N2 & _ & _ & NN & _). pose proof class_facts as (_ & _ & K3 & _).
pose proof Hnf as [F0 _].
assert (FL : fa_len (FRun au (NC1 xg) :: fr) = NF1 xg) by (cbn [fa_len]; unfold fr; rewrite <- Hnf_def; clear - N2; zlia).
destruct (fa_pop_n_some 10000 csz n (FRun au (NC1 xg) :: fr) [] RU ltac:(rewrite FL; clear - N2 N0 NN K3 F0 Hneed; zlia) ltac:(change (Z.of_nat 10000) with 10000; clear - K3; zlia)) as (tops & rest & EP).
destruct (fa_pop_n_spec 10000 csz n _ [] tops rest RU ltac:(clear - K3; zlia) EP) as (E1 & E2 & E3 & E4). cbn [rev app length] in E1, E4.
exists tops, rest. rewrite FL in E2. repeat split; try assumption; clear - E4; zlia.
Qed.
Lemma E_mmu_e : tot <= mu -> map_more_user c need S = IRet (true, S).
Proof.
intros HC. unfold map_more_user. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with false by (symmetry; apply Z.ltb_ge; exact HC). reflexivity.
Qed.
Lemma E_mmu_g : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset ->
exists K, map_more_user c need S = IAsk (KMapUser c mu kUserMapSize) S K /\
K 1 = IRet (true, SUp) /\ K 2 = IRet (false, SUm) /\ (forall z, z <> 1 -> z <> 2 -> K z = IRet (false, S)).
Proof.
intros HC HR. unfold map_more_user. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with true by (symmetry; apply Z.ltb_lt; exact HC). rewrite (round_user HC).
unfold mcheck. replace (mu + kUserMapSize <=? kFreeArrayOffset) with true by (symmetry; apply Z.leb_le; exact HR).
unfold bind at 1. unfold ret at 1. cbn [ibind]. unfold bind at 1. unfold askz. cbn [ibind].
eexists. split; [reflexivity|]. split; [|split].
- cbn [aGranted Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SUp, rUp, upd_reg. rewrite Hmu2. reflexivity.
- cbn [aGranted aDestroyed Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SUm, rUm, upd_reg. reflexivity.
- intros z Z1 Z2. unfold aGranted, aDestroyed. rewrite (proj2 (Z.eqb_neq z 1) Z1), (proj2 (Z.eqb_neq z 2) Z2). unfold bind, ret. cbn [ibind]. reflexivity.
Qed.
Lemma E_mmu_fail : mu < tot -> kFreeArrayOffset < mu + kUserMapSize -> exists f, map_more_user c need S = IFail f.
Proof.
intros HC HR. unfold map_more_user. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with true by (symmetry; apply Z.ltb_lt; exact HC). rewrite (round_user HC).
unfold mcheck. replace (mu + kUserMapSize <=? kFreeArrayOffset) with false by (symmetry; apply Z.leb_gt; exact HR).
unfold bind at 1. unfold fail. cbn [ibind]. eexists. reflexivity.
Qed.
Lemma E_efa_e : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg ->
4 * NF1 xg <= mf -> ensure_free_array c (NF1 xg) false s1 = IRet (true, s1).
Proof.
intros xg s1 HC R1 Hle. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. cbn [rg_mapped_fa rg1].
replace (4 * NF1 xg <=? mf) with true by (symmetry; apply Z.leb_le; exact Hle). reflexivity.
Qed.
Lemma E_efa_g : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg -> (forall r', upd_reg c r' s1 = upd_reg c r' S) ->
mf < 4 * NF1 xg -> mf2 <= kFreeArrayMax ->
exists K, ensure_free_array c (NF1 xg) false s1 = IAsk (KMapFreeArray c mf kFreeArrayMapSize) s1 K /\
K 1 = IRet (true, SFp xg) /\ K 2 = IRet (false, SFm xg) /\ (forall z, z <> 1 -> z <> 2 -> K z = IRet (false, s1)).
Proof.
intros xg s1 HC R1 U1 Hlt Hmax2. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. cbn [rg_mapped_fa rg_mapped_user rg_alloc_user rg_free rg_holes rg1].
replace (4 * NF1 xg <=? mf) with false by (symmetry; apply Z.leb_gt; exact Hlt). rewrite (round_fa xg HC Hlt).
unfold mcheck. replace (mf2 <=? kFreeArrayMax) with true by (symmetry; apply Z.leb_le; exact Hmax2).
unfold bind at 1. unfold ret at 1. cbn [ibind]. unfold bind at 1. unfold askz. cbn [ibind].
replace (mf2 - mf) with kFreeArrayMapSize by (rewrite Hmf2; clear; zlia).
eexists. split; [reflexivity|]. split; [|split].
- cbn [aGranted Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SFp. rewrite <- (U1 (rFp xg)). reflexivity.
- cbn [aGranted aDestroyed Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SFm. rewrite <- (U1 (rFm xg)). reflexivity.
- intros z Z1 Z2. unfold aGranted, aDestroyed. rewrite (proj2 (Z.eqb_neq z 1) Z1), (proj2 (Z.eqb_neq z 2) Z2). unfold bind, ret. cbn [ibind]. reflexivity.
Qed.
Lemma E_efa_fail : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg ->
mf < 4 * NF1 xg -> kFreeArrayMax < mf2 -> exists f, ensure_free_array c (NF1 xg) false s1 = IFail f.
Proof.
intros xg s1 HC R1 Hlt Hmax2. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. cbn [rg_mapped_fa rg_mapped_user rg_alloc_user rg_free rg_holes rg1].
replace (4 * NF1 xg <=? mf) with false by (symmetry; apply Z.leb_gt; exact Hlt). rewrite (round_fa xg HC Hlt).
unfold mcheck. replace (mf2 <=? kFreeArrayMax) with false by (symmetry; apply Z.leb_gt; exact Hmax2).
unfold bind at 1. unfold fail. cbn [ibind]. eexists. reflexivity.
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
split; [|split].
- unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions s2)) with (reg s2 c). rewrite R2. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes rg2].
unfold bind, set_region, modify, ret. cbn [ibind]. rewrite <- (U2 (rP xg yg)). unfold upd_reg, rP. rewrite N3, <- Hcsz. reflexivity.
- unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions (upd_reg c (rP xg yg) S))) with (reg (upd_reg c (rP xg yg) S) c). rewrite reg_upd3. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes rP].
replace (fa_len (FRun au (NC1 xg) :: fr) <? n) with false by (symmetry; apply Z.ltb_ge; cbn [fa_len]; unfold fr; rewrite <- Hnf_def; clear - N2 NN Hneed F0; zlia).
rewrite <- Hcsz, EP. unfold bind, set_region, modify, ret. cbn [ibind]. rewrite <- (upd_reg_upd_reg c (rP xg yg) (rQ xg yg rest) S). reflexivity.
- unfold set_pc, modify, SQ, upd_pc, cache_fill_order. reflexivity.
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
change (znth pclass0 c (st_cache S)) with (cache S c). rewrite Hchunks, PM3, <- Hn. reflexivity.
- unfold get_from_allocator. unfold bind at 1. unfold get_region at 1. unfold bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite <- Hnf_def.
replace (nf <? n) with true by (symmetry; apply Z.ltb_lt; exact Hnlt). rewrite <- Hneed. reflexivity.
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
Proof. reflexivity. Qed.
Lemma E_getreg1 : forall (xg : bool) (s1 : astate), XC3 xg -> reg s1 c = rg1 xg ->
get_region c s1 = IRet (rg1 xg, s1) /\
fa_len (rg_free (rg1 xg)) + (rg_mapped_user (rg1 xg) - rg_alloc_user (rg1 xg)) / class_size c = NF1 xg /\
(rg_mapped_user (rg1 xg) - rg_alloc_user (rg1 xg)) / class_size c = NC1 xg /\ rg_alloc_user (rg1 xg) = au.
Proof.
intros xg s1 HC R1. pose proof (factsX3 xg HC) as (_ & N2 & _ & _ & _ & _ & _ & DV). split; [|split; [|split]].
- unfold get_region, bind, get, ret. cbn [ibind]. change (znth region0 c (st_regions s1)) with (reg s1 c). rewrite R1. reflexivity.
- cbn [rg1 rg_free rg_mapped_user rg_alloc_user]. rewrite <- Hcsz, DV. unfold fr. rewrite <- Hnf_def. clear - N2; zlia.
- cbn [rg1 rg_mapped_user rg_alloc_user]. rewrite <- Hcsz. exact DV.
- reflexivity.
Qed.
Lemma reg_e : reg S c = rg1 false. Proof. rewrite reg_S. reflexivity. Qed.
Lemma reg_g : reg SUp c = rg1 true. Proof. unfold SUp. rewrite reg_upd3. reflexivity. Qed.
Lemma upd_e : forall r', upd_reg c r' S = upd_reg c r' S. Proof. reflexivity. Qed.
Lemma upd_g : forall r', upd_reg c r' SUp = upd_reg c r' S. Proof. intros r'. unfold SUp. apply upd_reg_upd_reg. Qed.
Lemma reg_ee : reg S c = rg2 false false. Proof. rewrite reg_S. reflexivity. Qed.
Lemma reg_ge : reg SUp c = rg2 true false. Proof. unfold SUp. rewrite reg_upd3. reflexivity. Qed.
Lemma reg_xg : forall xg : bool, reg (SFp xg) c = rg2 xg true. Proof. intros xg. unfold SFp. rewrite reg_upd3. reflexivity. Qed.
Lemma upd_xg : forall (xg : bool) r', upd_reg c r' (SFp xg) = upd_reg c r' S. Proof. intros xg r'. unfold SFp. apply upd_reg_upd_reg. Qed.

(* ================================================================================================================ *)
(* The cf tree (YG00cf.v: map_more_user_cf / populate_cf / get_from_allocator_cf / refill_if_empty_cf;
   YGcfInstRefill.refill_tree_cf).  For c = kBatchClass it is cgif's tree verbatim; for c <> kBatchClass it differs in
   two places only: the class-full case (errb_report_cf ;; set_exh_cf ;; ret false: the report arm, a separate hand,
   MnRefillSeamcf.refill_B3_classfull_cf) and populate_cf's success tail, which clears the exhausted hole
   (clear_exh_cf c: del_hole EXH_HOLE) before `ret true`.  HO3 / rPc / rQc / SQc are rP / rQ / SQ with that hole
   cleared on a non-batch class. *)
Definition HO3 (xg yg : bool) : list (Z * Z) := if c =? kBatchClass then HO2 xg yg else del_hole EXH_HOLE (HO2 xg yg).
Definition rPc (xg yg : bool) : region := mkRegion (MU1 xg) (AU1 xg) (MF2 yg) (FRun au (NC1 xg) :: fr) (HO3 xg yg).
Definition rQc (xg yg : bool) (rest : list fseg) : region := mkRegion (MU1 xg) (AU1 xg) (MF2 yg) rest (HO3 xg yg).
Definition SQc (xg yg : bool) (tops : list Z) (rest : list fseg) : astate :=
  upd_pc c (mkPC maxc (rev tops)) (upd_reg c (rQc xg yg rest) S).
Lemma E_mmu_e_cf : tot <= mu -> map_more_user_cf c need S = IRet (true, S).
Proof.
intros HC. unfold map_more_user_cf. destruct (c =? kBatchClass); [exact (E_mmu_e HC)|].
unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with false by (symmetry; apply Z.ltb_ge; exact HC). reflexivity.
Qed.
Lemma E_mmu_g_cf : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset ->
exists K, map_more_user_cf c need S = IAsk (KMapUser c mu kUserMapSize) S K /\
K 1 = IRet (true, SUp) /\ K 2 = IRet (false, SUm) /\ (forall z, z <> 1 -> z <> 2 -> K z = IRet (false, S)).
Proof.
intros HC HR. unfold map_more_user_cf. destruct (c =? kBatchClass); [exact (E_mmu_g HC HR)|].
unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite reg_S. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes]. rewrite <- Hcsz, <- Htot.
replace (mu <? tot) with true by (symmetry; apply Z.ltb_lt; exact HC). rewrite (round_user HC).
replace (mu + kUserMapSize <=? kFreeArrayOffset) with true by (symmetry; apply Z.leb_le; exact HR).
unfold bind at 1. unfold askz. cbn [ibind].
eexists. split; [reflexivity|]. split; [|split].
- cbn [aGranted Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SUp, rUp, upd_reg. rewrite Hmu2. reflexivity.
- cbn [aGranted aDestroyed Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold SUm, rUm, upd_reg. reflexivity.
- intros z Z1 Z2. unfold aGranted, aDestroyed. rewrite (proj2 (Z.eqb_neq z 1) Z1), (proj2 (Z.eqb_neq z 2) Z2). unfold bind, ret. cbn [ibind]. reflexivity.
Qed.
Lemma E_pop_cf_batch : c = kBatchClass -> populate_cf c need S = populate c need S.
Proof. intros Hb. unfold populate_cf. rewrite (proj2 (Z.eqb_eq c kBatchClass) Hb). reflexivity. Qed.
Lemma E_pop_cf : c <> kBatchClass -> populate_cf c need S =
(ok <- map_more_user_cf c need ;;
if negb ok then ret false
else (r0 <- get_region c ;;
ok2 <- ensure_free_array c (fa_len (rg_free r0) + (rg_mapped_user r0 - rg_alloc_user r0) / class_size c) false ;;
if negb ok2 then ret false
else (r4 <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r4) (rg_alloc_user r4 + (rg_mapped_user r0 - rg_alloc_user r0) / class_size c * class_size c) (rg_mapped_fa r4)
(FRun (rg_alloc_user r4) ((rg_mapped_user r0 - rg_alloc_user r0) / class_size c) :: rg_free r4) (rg_holes r4)) ;;
clear_exh_cf c ;;
ret true))) S.
Proof. intros Hb. unfold populate_cf. rewrite (proj2 (Z.eqb_neq c kBatchClass) Hb). reflexivity. Qed.
Lemma E_tail_cf : forall (xg yg : bool) (s2 : astate) tops rest, c <> kBatchClass -> XC3 xg -> reg s2 c = rg2 xg yg ->
(forall r', upd_reg c r' s2 = upd_reg c r' S) ->
fa_pop_n 10000 csz n (FRun au (NC1 xg) :: fr) [] = Some (tops, rest) ->
(r0 <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r0) (rg_alloc_user r0 + NC1 xg * class_size c) (rg_mapped_fa r0) (FRun (rg_alloc_user r0) (NC1 xg) :: rg_free r0) (rg_holes r0)) ;;
clear_exh_cf c ;;
ret true) s2 = IRet (true, upd_reg c (rPc xg yg) S) /\
(r3 <- get_region c ;;
if fa_len (rg_free r3) <? n then ret None
else match fa_pop_n 10000 (class_size c) n (rg_free r3) [] with
| None => fail (FModel 1)
| Some (tops0, rest0) => set_region c (mkRegion (rg_mapped_user r3) (rg_alloc_user r3) (rg_mapped_fa r3) rest0 (rg_holes r3)) ;; ret (Some tops0)
end) (upd_reg c (rPc xg yg) S) = IRet (Some tops, upd_reg c (rQc xg yg rest) S) /\
set_pc c (mkPC maxc (cache_fill_order tops)) (upd_reg c (rQc xg yg rest) S) = IRet (tt, SQc xg yg tops rest).
Proof.
intros xg yg s2 tops rest Hb HC R2 U2 EP. pose proof (factsX3 xg HC) as ([N0 N1] & N2 & N3 & _ & NN & _). pose proof Hnf as [F0 _].
assert (HB : (c =? kBatchClass) = false) by (apply Z.eqb_neq; exact Hb).
split; [|split].
- unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions s2)) with (reg s2 c). rewrite R2. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes rg2].
unfold bind, set_region, modify, ret. cbn [ibind].
match goal with |- context [set_regions (zupd c ?r (st_regions s2)) s2] => change (set_regions (zupd c r (st_regions s2)) s2) with (upd_reg c r s2) end.
rewrite U2.
unfold clear_exh_cf. unfold get_region, bind, get, set_region, modify, ret. cbn [ibind].
match goal with |- context [znth region0 c (st_regions ?s)] => change (znth region0 c (st_regions s)) with (reg s c) end.
rewrite reg_upd3. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes].
match goal with |- context [set_regions (zupd c ?r (st_regions ?s)) ?s] => change (set_regions (zupd c r (st_regions s)) s) with (upd_reg c r s) end.
rewrite upd_reg_upd_reg. unfold rPc, HO3. rewrite HB, N3, <- Hcsz. reflexivity.
- unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions (upd_reg c (rPc xg yg) S))) with (reg (upd_reg c (rPc xg yg) S) c). rewrite reg_upd3. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes rPc].
replace (fa_len (FRun au (NC1 xg) :: fr) <? n) with false by (symmetry; apply Z.ltb_ge; cbn [fa_len]; unfold fr; rewrite <- Hnf_def; clear - N2 NN Hneed F0; zlia).
rewrite <- Hcsz, EP. unfold bind, set_region, modify, ret. cbn [ibind]. rewrite <- (upd_reg_upd_reg c (rPc xg yg) (rQc xg yg rest) S). reflexivity.
- unfold set_pc, modify, SQc, upd_pc, cache_fill_order. reflexivity.
Qed.
Lemma E_tree_cf :
refill_tree_cf c S = (got <- get_from_allocator_cf c n ;; match got with None => ret tt | Some tops => set_pc c (mkPC maxc (cache_fill_order tops)) end) S /\
get_from_allocator_cf c n S =
(ok <- populate_cf c need ;;
if negb ok then ret None
else (r3 <- get_region c ;;
if fa_len (rg_free r3) <? n then ret None
else match fa_pop_n 10000 (class_size c) n (rg_free r3) [] with
| None => fail (FModel 1)
| Some (tops0, rest0) => set_region c (mkRegion (rg_mapped_user r3) (rg_alloc_user r3) (rg_mapped_fa r3) rest0 (rg_holes r3)) ;; ret (Some tops0)
end)) S.
Proof.
split.
- unfold refill_tree_cf. unfold bind at 1. unfold init_cache_if_needed, bind at 1, get. cbn [ibind]. rewrite Hinited. unfold ret at 1. cbn [ibind].
unfold refill_if_empty_cf. unfold bind at 1. unfold get_pc, bind at 1, get, ret at 1. cbn [ibind].
change (znth pclass0 c (st_cache S)) with (cache S c). rewrite Hchunks, PM3, <- Hn. reflexivity.
- unfold get_from_allocator_cf. unfold bind at 1. unfold get_region at 1. unfold bind at 1, get, ret at 1. cbn [ibind].
change (znth region0 c (st_regions S)) with (reg S c). rewrite <- Hnf_def.
replace (nf <? n) with true by (symmetry; apply Z.ltb_lt; exact Hnlt). rewrite <- Hneed. reflexivity.
Qed.
End g.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 15 address literal(s) rewritten, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the low shadow band of the constant cells ends at 0x800b3000 (the page above fm's last constant shadow cell 0x800b288b) instead of the donor's 0x80050000. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/AFkm.v, with its module paths and module names changed; 597 of its 877 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Threads UP through the donor refill tops: lib/A/AFku.v (refill_inited), AFkt.v (refill_B2), AFkv.v (refill_uninit, tfib_refill_ok), AFhn.v (AR_init), AFkz.v (LEAF_B2), with the seed region lemmas of AFkk.v / AFkx.v. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: the R3 region lemmas clear the R3-only hypotheses first (lia saw their divisions and products, ~2000 s each); refill top tfib_refill_okU over FSupoison.ARU. *)
(* Modified by Theorem Labs, 2026-10: refill_leafU re-exports the raw memory frame (AGif0n.rleaf / CLrefill0.refill_leafR), for the ARU lift of route 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB19 AF0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFl1 AFhy AFis AFkp AFk6 AFk5 AFhz AFk8 AFk7.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFk4.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFk3 AB1q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFhm AFka AFi3 AFk9 AFkk AFkb AFkc AFkd AFke AFkf AFkg AFkh AFki AFkj AFkm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0b YG0h YG0o YG08 YK0v YA05 YA09 YG0j YG0c YG0i YG0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFko AFkr AFks AFka AFkx AFkw AFky AFkl AFkz AFkt AFku AFhn AFkv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonAllocRf.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module FARf := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocRf.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section r3.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Variables (need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pr := (@AFk5.Pr ly c).
Local Abbreviation RGv := (@AFk5.RGv ly c).
Local Abbreviation RBv := (@AFk5.RBv ly c).
Local Abbreviation FAv := (@AFk5.FAv ly c).
Local Abbreviation SHBv := (@AFk5.SHBv).
Local Abbreviation SRCv := (@AFk5.SRCv ly c n nf).
Local Abbreviation DSTv := (@AFk5.DSTv ly c).
Local Abbreviation XWR := (@AFk5.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E0 := (@AFk5.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaT := (@AFk5.EaT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaC := (@AFk5.EaC ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSB := (@AFk5.EaSB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaTOP := (@AFk5.EaTOP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaCL := (@AFk5.EaCL ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaP := (@AFk5.EaP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMAX := (@AFk5.EaMAX ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaN := (@AFk5.EaN ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaCSZ := (@AFk5.EaCSZ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRG := (@AFk5.EaRG ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRB := (@AFk5.EaRB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaFA := (@AFk5.EaFA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNF := (@AFk5.EaNF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF := (@AFk5.EaMF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAU := (@AFk5.EaAU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMU := (@AFk5.EaMU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHB := (@AFk5.EaSHB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNEED := (@AFk5.EaNEED ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaTOT := (@AFk5.EaTOT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaADR := (@AFk5.EaADR ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHA := (@AFk5.EaSHA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Hypothesis IMG : img_cover ly.
Local Abbreviation EaMU2 := (@AFk5.EaMU2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNCe := (@AFk5.EaNCe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNCg := (@AFk5.EaNCg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNFe := (@AFk5.EaNFe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNFg := (@AFk5.EaNFg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaFADR := (@AFk5.EaFADR ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHF := (@AFk5.EaSHF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF2 := (@AFk5.EaMF2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAUe := (@AFk5.EaAUe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAUg := (@AFk5.EaAUg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation Er := (@AFk5.Er ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E2 := (@AFk5.E2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E1 := (@AFk5.E1 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E8 := (@AFk5.E8 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
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
Local Abbreviation class_facts := (@AFk5.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@AFk5.high_factsR _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_T := (@AFk5.off_T _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_C := (@AFk5.off_C _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation derived_rangesR := (@AFk5.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation WINR0 := (@AFk5.WINR0 ly regs0 c).
Local Abbreviation WINR := (@AFk5.WINR ly regs0 c n).
Local Abbreviation WINR0_WINR := (@AFk5.WINR0_WINR ly regs0 c n).
Local Abbreviation WSKELR := (@AFk5.WSKELR).
Local Abbreviation win_sub := (@AFk5.win_sub).
Local Abbreviation win_sub_sound := (@AFk5.win_sub_sound ly regs0 c maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (@AFk5.WSKELR_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation windows_WINR0 := (@AFk5.windows_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_WINR0 := (@AFk5.frame_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_X := (@AFk5.frame_X _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Ltac frame_acc3 HX HE :=
match goal with
| MEQ : (forall x : word, ~ ?X (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ X (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_X X E rs m1 m2 HX HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation W_DST := (@AFk5.W_DST ly c n).
Local Abbreviation W_FE := (@AFk5.W_FE ly c nf).
Local Abbreviation W_UW := (@AFk5.W_UW adr).
Local Abbreviation W_USH := (@AFk5.W_USH sha).
Local Abbreviation W_FW := (@AFk5.W_FW fadr).
Local Abbreviation W_FSH := (@AFk5.W_FSH shf).
Local Abbreviation at_R3 := (@AFk5.at_R3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_N3 := (@AFk5.at_N3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_RET3 := (@AFk5.at_RET3 _ regs0 mem0).
Local Abbreviation P_cells := (@AFk5.P_cells ly c maxc csz).
Local Abbreviation chunk_index := (@AFk5.chunk_index).
Local Abbreviation pstable := (@AFk5.pstable ly regs0 c).
Local Abbreviation all_disjoint_of_forall := (@AFk5.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFk5.kept_of_frame ly regs0 maxc mf au mu).
Local Abbreviation kept_of_frame2 := (@AFk5.kept_of_frame2 ly regs0 maxc mf au mu).
Local Abbreviation SKEL_TAILR := (@AFk5.SKEL_TAILR).
Local Abbreviation RFACTSR := (@AFk5.RFACTSR ly regs0 c).
Local Abbreviation stack_ivsR := (@AFk5.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := (@AFk5.zone_litR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_TR := (@AFk5.zone_TR _ ly regs0 c maxc mf au mu IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := (@AFk5.zone_CR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_RGR := (@AFk5.zone_RGR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation slots_not_WINR0 := (@AFk5.slots_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation fa_not_WINR0 := (@AFk5.fa_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation tail_ext_okR := (@AFk5.tail_ext_okR _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Variables (B : asyms) (S : astate) (UP : list (Z * Z)).
Hypothesis HARU : FSP.ARU tfibsegs B ly S UP W mem0 md0.
(* The refill seeds REG0R3 (inited, AFk6.v:40) and REG0U3 (uninited, AFka.v:16) fix only bytes of the image, the
   thread object, the stack window, the class's region info and the cache of class c: application memory, off UP. *)
Lemma REG0R3_regions_off_ush : FAR.regions_offU UP E0 REG0R3.
Proof. clear3.
apply (FAR.regions_offU_of_app B ly S UP W mem0 md0 E0 REG0R3 HARU).
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
unfold REG0R3, REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE. rewrite map_app. cbn [map app].
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold AFkp.rSB, AFkp.rSHB, AFkp.rC, AFkp.rT, AFkp.rTOP, AFkp.rP, AFkp.rRG.
rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG. unfold w64. rewrite ?unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR HcR SI4 SI5.
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold TFIB_TP, TFIB_TSD, SHADOW_OFF, kHighMemBeg, t_cache, kRegionInfoOff in *.
unfold RSTACK, kHighMemEnd in *.
repeat apply Forall_cons; try apply Forall_nil; unfold FAR.app_ext, SHADOW_OFF, kHighMemBeg; cbn [fst snd]; try zlia.
Qed.
Lemma REG0U3_regions_off_ush : FAR.regions_offU UP E0 REG0U3.
Proof. clear3.
apply (FAR.regions_offU_of_app B ly S UP W mem0 md0 E0 REG0U3 HARU).
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
unfold REG0U3, replAt, headc0, REG0R3, REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE. cbn [firstn skipn app].
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold AFkp.rSB, AFkp.rSHB, AFkp.rC, AFkp.rT, AFkp.rTOP, AFkp.rP, AFkp.rRG.
rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG. unfold w64. rewrite ?unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR HcR SI4 SI5.
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold TFIB_TP, TFIB_TSD, SHADOW_OFF, kHighMemBeg, t_cache, kRegionInfoOff in *.
unfold RSTACK, kHighMemEnd in *.
repeat apply Forall_cons; try apply Forall_nil; unfold FAR.app_ext, SHADOW_OFF, kHighMemBeg; cbn [fst snd]; try zlia.
Qed.
End r3.
Section z2.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pr := (@AFko.Pr ly c).
Local Abbreviation RGv := (@AFko.RGv ly c).
Local Abbreviation RBv := (@AFko.RBv ly c).
Local Abbreviation FAv := (@AFko.FAv ly c).
Local Abbreviation SHBv := (@AFko.SHBv).
Local Abbreviation SRCv := (@AFko.SRCv ly c n nf).
Local Abbreviation DSTv := (@AFko.DSTv ly c).
Local Abbreviation XWR := (@AFko.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E0 := (@AFko.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaT := (@AFko.EaT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaC := (@AFko.EaC ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaSB := (@AFko.EaSB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaTOP := (@AFko.EaTOP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaCL := (@AFko.EaCL ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaP := (@AFko.EaP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaMAX := (@AFko.EaMAX ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaN := (@AFko.EaN ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaCSZ := (@AFko.EaCSZ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaRG := (@AFko.EaRG ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaRB := (@AFko.EaRB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaFA := (@AFko.EaFA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaNF := (@AFko.EaNF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaMF := (@AFko.EaMF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaAU := (@AFko.EaAU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaMU := (@AFko.EaMU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation EaSHB := (@AFko.EaSHB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation Er := (@AFko.Er ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E2 := (@AFko.E2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E1 := (@AFko.E1 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation E8 := (@AFko.E8 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
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
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Ha0 : getr regs0 10 = w64 (T + t_cache).
Hypothesis Ha1 : getr regs0 11 = w64 Pr.
Hypothesis Ha2 : getr regs0 12 = w64 A_ALLOCATOR.
Hypothesis Ha3 : getr regs0 13 = w64 c.
Local Abbreviation class_facts := (@AFko.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@AFko.high_factsR _ ly regs0 maxc mf au mu LY IMG Hmf Hmu).
Local Abbreviation off_T := (@AFko.off_T _ ly regs0 maxc mf au mu LY IMG Hmf Hmu).
Local Abbreviation off_C := (@AFko.off_C _ ly regs0 maxc mf au mu LY IMG Hmf Hmu).
Ltac off_byR tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation derived_rangesR := (@AFko.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation WINR0 := (@AFko.WINR0 ly regs0 c).
Local Abbreviation WINR := (@AFko.WINR ly regs0 c n).
Local Abbreviation WINR0_WINR := (@AFko.WINR0_WINR ly regs0 c n).
Local Abbreviation WSKELR := (@AFko.WSKELR).
Local Abbreviation win_sub := (@AFko.win_sub).
Local Abbreviation win_sub_sound := (@AFko.win_sub_sound ly regs0 c maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (@AFko.WSKELR_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation windows_WINR0 := (@AFko.windows_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_WINR0 := (@AFko.frame_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Ltac frame_accR HE :=
match goal with
| MEQ : (forall x : word, ~ WINR0 (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WINR0 (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WINR0 E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation at_R := (@AFko.at_R _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation at_RC := (@AFko.at_RC _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation at_RET2 := (@AFko.at_RET2 _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz).
Local Abbreviation all_disjoint_of_forall := (@AFko.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFko.kept_of_frame W ly regs0 maxc mf au mu).
Local Abbreviation SKEL_TAILR := (@AFko.SKEL_TAILR).
Local Abbreviation RFACTSR := (@AFko.RFACTSR ly regs0 c).
Local Abbreviation stack_ivsR := (@AFko.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := (@AFko.zone_litR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_TR := (@AFko.zone_TR _ ly regs0 c maxc mf au mu LY IMG Hmf Hmu Hsp).
Local Abbreviation zone_CR := (@AFko.zone_CR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_RGR := (@AFko.zone_RGR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation slots_not_WINR0 := (@AFko.slots_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation fa_not_WINR0 := (@AFko.fa_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation tail_ext_okR := (@AFko.tail_ext_okR _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R RJ2 W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := (@AFko.rdn_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation store_ok_of_presentR := (@AFko.store_ok_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation cpy4_stretch := (@AFko.cpy4_stretch _ W ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Variables (B : asyms) (S : astate).
Variable UP : list (Z * Z).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARU : FSP.ARU tfibsegs B ly S UP W mem0 md0.
Local Abbreviation mem0u := (FSP.unpoison UP mem0).
Let HAR : AR tfibsegs B ly S W mem0u md0 := FSP.ARU_AR tfibsegs B ly S UP W mem0 md0 HARU.
Let HARm : ARm B ly S (aview tfibsegs (w_H W) mem0u) := proj1 HAR.
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
Hypothesis HQL : qloose S.
Local Abbreviation Pr_is := (@AFko.Pr_is ly c).
Local Abbreviation RGv_is := (@AFko.RGv_is ly c).
Local Abbreviation FAv_is := (@AFko.FAv_is ly c HcR).
Local Abbreviation RBv_is := (@AFko.RBv_is ly c HcR).
Local Abbreviation cls_wfR := (@AFkx.cls_wfR _ W ly mem0u c HcR B S HARm Hinited).
Local Abbreviation cls_wf0 := (@AFkx.cls_wf0 _ W ly mem0u c HcR B S HARm).
Local Abbreviation reg_facts0 := (@AFkx.reg_facts0 _ W ly regs0 mem0u c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_facts := (@AFkx.reg_facts _ W ly regs0 mem0u c maxc nf mf au mu HcR Hmax Hsp B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (@AFkx.Hnf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmf' := (@AFkx.Hmf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmu' := (@AFkx.Hmu' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation vis_present := (@AFkx.vis_present _ W ly regs0 mem0u maxc B S HARm).
Local Abbreviation thread_present := (@AFkx.thread_present _ W ly regs0 mem0u c maxc nf mf au mu LY IMG HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation rinfo_present := (@AFkx.rinfo_present _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HslotPres' := (@AFkx.HslotPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HfaPres' := (@AFkx.HfaPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation word_of_present := (@AFkx.word_of_present W ly regs0 mem0 maxc).
Local Abbreviation val_mem_lo4 := (@AFkx.val_mem_lo4 ly regs0 maxc).
Local Abbreviation junk_valuesR := (@AFkx.junk_valuesR _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation cell_sym := (@AFkx.cell_sym _ W ly mem0u B S TS HARm).
Local Abbreviation cell_lit := (@AFkx.cell_lit _ W ly mem0u B S TS HARm).
Local Abbreviation cell_state := (@AFkx.cell_state _ W ly mem0u B S HARm).
Local Abbreviation In_acells_cache := (@AFkx.In_acells_cache ly regs0 c maxc HcR B S).
Local Abbreviation In_acells_region := (@AFkx.In_acells_region ly regs0 c maxc HcR B S).
Local Abbreviation cache_valsR := (@AFkx.cache_valsR _ W ly regs0 mem0u c maxc csz HcR Hmax Hcsz B S HARm Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@AFkx.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (@AFkx.cache_valsU _ W ly regs0 mem0u maxc B S HARm).
Local Abbreviation region_valsR := (@AFkx.region_valsR _ W ly regs0 mem0u c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation chunk_lit := (@AFkx.chunk_lit W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation chunk_lit_at := (@AFkx.chunk_lit_at W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation chunk_atom := (@AFkx.chunk_atom W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2).
Local Abbreviation REG0R_ok_but35 := (@AFkx.REG0R_ok_but35 _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0R_ok := (@AFkx.REG0R_ok _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0U_ok := (@AFkx.REG0U_ok _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSR_ok := (@AFkx.PAIRSR_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SPAN_disj := (@AFkx.SPAN_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation FACTSR_ok := (@AFkx.FACTSR_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Local Abbreviation SEEDR_ok := (@AFkx.SEEDR_ok _ _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSU_ok := (@AFkx.PAIRSU_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEEDU_ok := (@AFkx.SEEDU_ok _ _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
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
Local Open Scope am_scope.
Let rd0 : reader := aview tfibsegs (w_H W) mem0u.
Let WF := am_wf B ly S rd0 HARm.
Let m0 := mrestrict (w_H W) mem0.
Local Abbreviation SRf := (@AFkz.SRf c maxc mf au mu S).
(* The B2 refill seeds REG0R (inited, AFkp.v:53) and REG0U2 (uninited, AFks.v:16): application memory only. *)
Lemma REG0R_regions_off_ush : FAR.regions_offU UP E0 REG0R.
Proof.
apply (FAR.regions_offU_of_app B ly S UP W mem0 md0 E0 REG0R HARU).
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
unfold REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold AFkp.rSB, AFkp.rSHB, AFkp.rC, AFkp.rT, AFkp.rTOP, AFkp.rP, AFkp.rRG.
rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG. unfold w64. rewrite ?unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR HcR SI4 SI5.
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold TFIB_TP, TFIB_TSD, SHADOW_OFF, kHighMemBeg, t_cache, kRegionInfoOff in *.
unfold RSTACK, kHighMemEnd in *.
repeat apply Forall_cons; try apply Forall_nil; unfold FAR.app_ext, SHADOW_OFF, kHighMemBeg; cbn [fst snd]; try zlia.
Qed.
Lemma REG0U2_regions_off_ush : FAR.regions_offU UP E0 REG0U2.
Proof.
apply (FAR.regions_offU_of_app B ly S UP W mem0 md0 E0 REG0U2 HARU).
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
unfold REG0U2, replAt, headc0, REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE. cbn [firstn skipn app].
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold AFkp.rSB, AFkp.rSHB, AFkp.rC, AFkp.rT, AFkp.rTOP, AFkp.rP, AFkp.rRG.
rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG. unfold w64. rewrite ?unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR HcR SI4 SI5.
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold TFIB_TP, TFIB_TSD, SHADOW_OFF, kHighMemBeg, t_cache, kRegionInfoOff in *.
unfold RSTACK, kHighMemEnd in *.
repeat apply Forall_cons; try apply Forall_nil; unfold FAR.app_ext, SHADOW_OFF, kHighMemBeg; cbn [fst snd]; try zlia.
Qed.
Lemma T_offU : forall a, T <= a < T + kThreadObjSize -> FAR.offU UP a.
Proof.
intros a Ha. pose proof high_factsR as (F1 & F2 & _).
apply (FAR.offU_app B ly S UP W mem0 md0 a HARU); clear - F1 F2 Ha; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END in F1; ceil;
  unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg, kThreadObjSize, ASAN_CEIL in *; lia.
Qed.
Lemma high_offU : forall a, kHighMemBeg <= a < 2 ^ 64 -> FAR.offU UP a.
Proof. intros a Ha. exact (FAR.offU_high B ly S UP W mem0 md0 a HARU Ha). Qed.
(* LEAF_B2 (lib/A/AFkz.v:990) over ARU: AR_transport at the unpoisoned memories, the frame / presence on the real
   ones; the refill B2 writes only the class cache, the slots and the region info (application memory). *)
Lemma LEAF_B2U : n <= nf -> forall tops rest W' c',
Wf (as_universe B) (SRf tops rest) ->
fa_elems (class_size c) (rg_free (reg S c)) = tops ++ fa_elems (class_size c) rest -> Z.of_nat (length tops) = n -> fa_len rest = nf - n -> runs_ok rest ->
at_RET2 W' c' -> FAR.refill_leafU B ly S UP W regs0 mem0 md0 c (tt, SRf tops rest) W' c'.
Proof.
intros Hnle tops rest W' c' WFR E1 E2' E3 E4 HR.
destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & MEQ' & PRS & PRW & CPY & VALS).
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12).
pose proof derived_rangesR as DR. pose proof class_facts as (K1 & K2 & K3 & K4 & K5).
assert (OP : forall a, Pr <= a < Pr + 48 -> FAR.offU UP a)
  by (intros a Ha; apply T_offU; clear - Ha DR; unfold kThreadObjSize, t_cache in *; zlia).
assert (OR : forall a, RGv <= a < RGv + 128 -> FAR.offU UP a) by (intros a Ha; apply high_offU; clear - Ha DR; zlia).
assert (MEQu : forall x : word, ~ WINR (bv_unsigned x) -> FSP.unpoison UP mem' x = mem0u x)
  by (intros x Hx; unfold FSP.unpoison; destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MEQ' x Hx)]).
assert (PRSu : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (FSP.unpoison UP mem') a)
  by (intros a Ha; apply FAR.apresent_to_unpoison; exact (PRS a Ha)).
assert (PRWu : forall a, (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 4 * n) \/ (RGv <= a < RGv + 128) \/
  (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) (FSP.unpoison UP mem') a)
  by (intros a Ha; apply FAR.apresent_to_unpoison; exact (PRW a Ha)).
assert (CPYu : forall k, 0 <= k < 4 * n -> FSP.unpoison UP mem' (w64 (DSTv + k)) = mem0u (w64 (SRCv + k))).
{ intros k Hk. pose proof DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DS & SR & _).
  assert (O1 : FAR.offU UP (DSTv + k)) by (apply OP; rewrite DS; clear - Hk K3; zlia).
  assert (O2 : FAR.offU UP (SRCv + k)) by (apply high_offU; destruct (SR Hnle) as [SR1 SR2]; pose proof Hmf as [[M0 M1] _]; clear - Hk SR1 SR2 DR M0 M1; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia).
  unfold w64. rewrite (FAR.unpoison_offU UP mem' _ O1), (FAR.unpoison_offU UP mem0 _ O2). exact (CPY k Hk). }
assert (VP : forall a (w : nat) v, val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> Pr <= a -> a + Z.of_nat w <= Pr + 16 ->
  val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem')) a w v).
{ intros a w v V L1 L2. apply FAR.val_mem_to_unpoison; [|exact V]. intros k Hk. apply OP. clear - L1 L2 Hk. zlia. }
assert (VR : forall a (w : nat) v, val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> RGv <= a -> a + Z.of_nat w <= RGv + 128 ->
  val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem')) a w v).
{ intros a w v V L1 L2. apply FAR.val_mem_to_unpoison; [|exact V]. intros k Hk. apply OR. clear - L1 L2 Hk. zlia. }
assert (HfaPresu : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0u a)
  by (intros a Ha; apply FAR.apresent_to_unpoison; exact (HfaPres a Ha)).
pose proof (@AFkz.AR_transport _ W ly regs0 mem0u md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
  Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp HfaPresu B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def tops rest (FSP.unpoison UP mem') mat
  HAR Hnle WFR E1 E2' E3 E4 MEQu PRSu PRWu CPYu
  (VP _ _ _ V1 ltac:(lia) ltac:(cbn; lia)) (VP _ _ _ V2 ltac:(lia) ltac:(cbn; lia)) (VP _ _ _ V3 ltac:(lia) ltac:(cbn; lia))
  (VR _ _ _ V4 ltac:(lia) ltac:(cbn; lia)) (VR _ _ _ V5 ltac:(lia) ltac:(cbn; lia)) (VR _ _ _ V6 ltac:(lia) ltac:(cbn; lia))
  (VR _ _ _ V7 ltac:(lia) ltac:(cbn; lia)) (VR _ _ _ V8 ltac:(lia) ltac:(cbn; lia)) (VR _ _ _ V9 ltac:(lia) ltac:(cbn; lia))
  (VR _ _ _ V10 ltac:(lia) ltac:(cbn; lia)) (VR _ _ _ V11 ltac:(lia) ltac:(cbn; lia)) (VR _ _ _ V12 ltac:(lia) ltac:(cbn; lia))) as ARG.
exists regs', mem', (with_vm_backing (m_vm_lazy md0) mat md0).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
cbn [fst snd]. split.
- apply (FAR.acall_postU_intro B RSTACK ly S UP W regs0 mem0 md0 (fun _ => False) ly (SRf tops rest) W regs' mem'
    (with_vm_backing (m_vm_lazy md0) mat md0) HARU ARG).
  + apply layout_le_refl.
  + apply wle_refl.
  + intros r Hr. apply RCS. unfold acallee_saved in Hr.
    assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
    clear - RCS H18.
    assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; exact Hb).
    destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    [ rewrite (E5 2 ltac:(zlia) 2%bv eq_refl) | rewrite (E5 3 ltac:(zlia) 3%bv eq_refl) | rewrite (E5 4 ltac:(zlia) 4%bv eq_refl)
    | rewrite (E5 8 ltac:(zlia) 8%bv eq_refl) | rewrite (E5 9 ltac:(zlia) 9%bv eq_refl) | rewrite (E5 18 ltac:(zlia) 18%bv eq_refl)
    | rewrite (E5 19 ltac:(zlia) 19%bv eq_refl) | rewrite (E5 20 ltac:(zlia) 20%bv eq_refl) | rewrite (E5 21 ltac:(zlia) 21%bv eq_refl)
    | rewrite (E5 22 ltac:(zlia) 22%bv eq_refl) | rewrite (E5 23 ltac:(zlia) 23%bv eq_refl) | rewrite (E5 24 ltac:(zlia) 24%bv eq_refl)
    | rewrite (E5 25 ltac:(zlia) 25%bv eq_refl) | rewrite (E5 26 ltac:(zlia) 26%bv eq_refl) | rewrite (E5 27 ltac:(zlia) 27%bv eq_refl) ];
    cbn [In]; tauto.
  + unfold same_io. destruct md0; cbn; repeat split; reflexivity.
  + intros a Ra NO NO' NS NE. apply aview_same. apply MEQ'. rewrite unsigned_lit_small by exact Ra.
    intros Hw. destruct (@AFkz.WR_owned _ W ly regs0 mem0u md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
      Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp B S HAR a Ra Hw) as [Hs|Ho]; [|exact (NO Ho)].
    apply NS. unfold ascratch, spZ. left. exact Hs.
  + intros a Ha. exact (PRS a Ha).
  + apply (FAR.upoison_ok_keep B ly S ly (SRf tops rest) UP (FSP.ARU_ok tfibsegs B ly S UP W mem0 md0 HARU)).
    intros r p nn _ Hb _ _. pose proof (@AFkz.SR_parts _ W ly regs0 mem0u c maxc mf au mu HcR Hmf Hmu B S HARm tops rest) as (_ & _ & _ & _ & _ & Rch & _).
    unfold ablocks, blocks in Hb |- *. rewrite Rch. exact Hb.
  + apply (FAR.upoisoned_keep UP W W mem0 mem' (FSP.ARU_poisoned tfibsegs B ly S UP W mem0 md0 HARU)).
    intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S UP W mem0 md0 s HARU Hs) as (_ & L1 & L2).
    assert (Rs : 0 <= s < 2 ^ 64) by (clear - L1 L2; unfold SHADOW_OFF, kHighMemBeg in *; lia).
    apply aview_same. apply MEQ'. rewrite unsigned_lit_small by exact Rs.
    pose proof high_factsR as (F1 & F2 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _).
    unfold AFko.WINR, AFko.WINR0. clear - L1 L2 F1 F2 DR T7 S1 K3.
    unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END in F1. ceil.
    unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg, kThreadObjSize, ASAN_CEIL, RSTACK, t_cache in *. unfold sp0 in *. zlia.
- split.
  + rewrite R10. pose proof (@AFkz.SR_parts _ W ly regs0 mem0u c maxc mf au mu HcR Hmf Hmu B S HARm tops rest) as (_ & _ & _ & _ & Rcl & _). rewrite Rcl. cbn [pc_chunks].
    destruct (rev tops) as [|x t] eqn:Er; [|reflexivity]. exfalso. apply (f_equal (@length Z)) in Er. rewrite length_rev in Er. cbn in Er. zlia.
  + (* the raw frame: at_RET2's MEQ' off WINR, and WINR lies in the stack window or in owned memory (AFkz.WR_owned) *)
    intros x NO _ NS. apply MEQ'. intros Hw.
    destruct (@AFkz.WR_owned _ W ly regs0 mem0u md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
      Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp B S HAR (bv_unsigned x) (u64_range x) Hw) as [Hs|Ho]; [|exact (NO Ho)].
    apply NS. unfold spZ. exact Hs.
Qed.
End z2.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refill top over ARU (donor lib/A/AFku.v, AFkt.v, AFkv.v). Each seed is built over the unpoisoned memory (the   *)
(* donor seed lemmas need AR), moved to the real memory by the region lemmas above, and walked on the real memory.    *)
(* The uninited arms initialise the caches on the real memory; AR_init runs on its unpoisoned reading.               *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section top.
Local Open Scope am_scope.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* The thread object is application memory (zone3), so off U. *)
Lemma T_offU_any : forall ly S U W mem md, FSP.ARU tfibsegs B ly S U W mem md ->
  forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU U a.
Proof.
intros ly S U W mem md H a Ha. pose proof (FSP.ARU_AR tfibsegs B ly S U W mem md H) as HAR.
pose proof (AFhn.T_facts B ly S W (FSP.unpoison U mem) md HAR (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR)))) as (_ & _ & _ & ZT).
exact (FAR.offU_zone3 B ly S U W mem md (ly_T ly) kThreadObjSize a H ZT Ha).
Qed.

(* AR_init (lib/A/AFhn.v:446) over ARU: the cache tables are written in the thread object, off U; U's bytes keep. *)
Lemma ARU_init : forall ly S U W mem0 mR md, FSP.ARU tfibsegs B ly S U W mem0 md -> st_cache_inited S = false ->
  (forall x : word, ~ TABW (ly_T ly) (bv_unsigned x) -> mR x = mem0 x) ->
  (forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) (ly_T ly) i) ->
  (forall a, TABW (ly_T ly) a -> apresent (w_H W) mR a) ->
  FSP.ARU tfibsegs B ly (AFhn.S1 S) U W mR md.
Proof.
intros ly S U W mem0 mR md HARU HU MEQ TBF TPR.
pose proof (FSP.ARU_AR tfibsegs B ly S U W mem0 md HARU) as HAR.
pose proof (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (TO : forall a, TABW (ly_T ly) a -> FAR.offU U a)
  by (intros a Ha; apply (T_offU_any ly S U W mem0 md HARU); apply TABW_range in Ha; unfold kThreadObjSize; lia).
split; [|split].
- apply (AFhn.AR_init B ly S W (FSP.unpoison U mem0) (FSP.unpoison U mR) md TS HAR HU); [| | | exact IMG].
  + intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush U (bv_unsigned x)); [reflexivity | exact (MEQ x Hx)].
  + intros i Hi. destruct (TBF i Hi) as [M1 M2].
    split; (apply FAR.val_mem_to_unpoison; [|assumption]); intros k Hk; apply TO; exists i; lia.
  + intros a Ha. apply FAR.apresent_to_unpoison. exact (TPR a Ha).
- apply (FAR.upoison_ok_keep B ly S ly (AFhn.S1 S) U (FSP.ARU_ok tfibsegs B ly S U W mem0 md HARU)).
  intros r p nn _ Hb _ _. exact Hb.
- apply (FAR.upoisoned_keep U W W mem0 mR (FSP.ARU_poisoned tfibsegs B ly S U W mem0 md HARU)).
  intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S U W mem0 md s HARU Hs) as (_ & L1 & L2).
  assert (Rs : 0 <= s < 2 ^ 64) by (clear - L1 L2; unfold SHADOW_OFF, kHighMemBeg in *; lia).
  apply aview_same. apply MEQ. rewrite unsigned_lit_small by exact Rs.
  intros Ht. pose proof (TO s Ht) as O. unfold FAR.offU in O. rewrite Z.mod_small in O by exact Rs. congruence.
Qed.

(* refill_leaf_init (lib/A/AFhn.v:489) over ARU. *)
Lemma refill_leaf_initU : forall ly S U W mem0 mR md, FSP.ARU tfibsegs B ly S U W mem0 md ->
  (forall x : word, ~ TABW (ly_T ly) (bv_unsigned x) -> mR x = mem0 x) ->
  forall regs c r W' c', FAR.refill_leafU B ly (AFhn.S1 S) U W regs mR md c r W' c' -> FAR.refill_leafU B ly S U W regs mem0 md c r W' c'.
Proof.
intros ly S U W mem0 mR md HARU MEQ regs c r W' c' (regs' & mem' & md' & Ec & ((AR' & LE & WLE & RP & IO & FR & PR) & OK' & PO') & A0 & RAW).
pose proof (FSP.ARU_AR tfibsegs B ly S U W mem0 md HARU) as HAR.
exists regs', mem', md'. split; [exact Ec|]. split; [|split; [exact A0|]].
- split; [|exact (conj OK' PO')].
  split; [exact AR'|]. split; [exact LE|]. split; [exact WLE|]. split; [exact RP|]. split; [exact IO|]. split; [|exact PR].
  intros a Ra NO NO' NS NE. rewrite (FR a Ra NO NO' NS NE). apply aview_same.
  unfold FSP.unpoison. destruct (FSP.in_ush U (bv_unsigned (Z_to_bv 64 a))); [reflexivity|].
  apply MEQ. rewrite unsigned_lit_small by exact Ra. intros Ht. apply NO.
  apply (own_core B ly S (aview tfibsegs (w_H W) (FSP.unpoison U mem0)) (ly_T ly, kThreadObjSize) a (proj1 HAR)); [unfold core_extents; cbn; tauto | cbn [fst snd]].
  apply TABW_range in Ht. unfold kThreadObjSize. lia.
- (* the raw frame: the S1 leaf's raw frame against mR, then mR = mem0 off the cache tables TABW, which lie in the
     thread object, an owned core extent (own_core), so off aowned at S *)
  intros x NO NO' NS. rewrite (RAW x NO NO' NS). apply MEQ. intros Ht. apply NO.
  apply (own_core B ly S (aview tfibsegs (w_H W) (FSP.unpoison U mem0)) (ly_T ly, kThreadObjSize) (bv_unsigned x) (proj1 HAR)); [unfold core_extents; cbn; tauto | cbn [fst snd]].
  apply TABW_range in Ht. unfold kThreadObjSize. lia.
Qed.

(* The common start of the four arms (donor AFku.v:38-50): the run invariant, the unpoisoned reading mem0u, the class. *)
Local Ltac top_pre :=
  match goal with PREU : FAR.refill_preU _ ?ly ?S ?U ?W ?regs0 ?mem0 ?md0 ?c |- _ =>
  pose proof (FAR.ARU_of_refill_preU B ly S U W regs0 mem0 md0 c PREU) as HARU;
  destruct PREU as (PRE & _ & _);
  destruct PRE as (HAR & Hslack & Hpum & HQL & Hra & Hra4096 & Hal & Hlo & Hhi & Hpres0R & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3 & HcR & Hchunks);
  pose proof (proj1 HAR) as HARm; unfold spZ, raZ in *;
  assert (LY : layout_ok ly) by exact (am_layout _ _ _ _ HARm);
  assert (IMG : img_cover ly) by exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR)));
  assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS));
  rewrite (ts_tp B TS) in Htp;
  set (sp0 := bv_unsigned (getr regs0 2)) in *;
  assert (Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (repeat split; assumption);
  assert (Hpres0Rr : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a)
    by (apply (FAR.stack_present_real B ly S U W mem0 md0 (sp0 - RSTACK) sp0 HARU); [lia | lia | exact Hpres0R]);
  set (mem0u := FSP.unpoison U mem0) in *;
  set (maxc := max_cached c); set (n := maxc / 2); set (nf := fa_len (rg_free (reg S c))); set (mf := rg_mapped_fa (reg S c));
  set (au := rg_alloc_user (reg S c)); set (mu := rg_mapped_user (reg S c)); set (csz := class_size c); set (mat0 := m_vm_materialized md0);
  assert (Hmax : maxc = max_cached c) by reflexivity; assert (Hn : n = maxc / 2) by reflexivity; assert (Hcsz : csz = class_size c) by reflexivity;
  assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by reflexivity; assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by reflexivity;
  assert (Hau_def : au = rg_alloc_user (reg S c)) by reflexivity; assert (Hmu_def : mu = rg_mapped_user (reg S c)) by reflexivity;
  replace (cfg_at tfibsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x36ce4) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
    by (unfold cfg_at, A_Refill; subst mat0; rewrite with_vm_backing_id; reflexivity)
  end.

(* The R3 quantities of the B3 arms (donor AFku.v:57-66). *)
Local Ltac top_r3 ly c n nf mf au mu csz :=
  set (need := n - nf); set (tot := au + need * csz); set (adr := AFk5.RBv ly c + mu); set (sha := AFk5.SHBv + adr / 8);
  set (mu2 := mu + kUserMapSize); set (nce := (mu - au) / csz); set (ncg := (mu2 - au) / csz); set (nfe := nf + nce); set (nfg := nf + ncg);
  set (fadr := AFk5.FAv ly c + mf); set (shf := AFk5.SHBv + fadr / 8); set (mf2 := mf + kFreeArrayMapSize);
  set (aue := au + nce * csz); set (aug := au + ncg * csz);
  assert (Hneed : need = n - nf) by reflexivity; assert (Htot : tot = au + need * csz) by reflexivity; assert (Hadr : adr = AFk5.RBv ly c + mu) by reflexivity;
  assert (Hsha : sha = AFk5.SHBv + adr / 8) by reflexivity; assert (Hmu2 : mu2 = mu + kUserMapSize) by reflexivity;
  assert (Hnce : nce = (mu - au) / csz) by reflexivity; assert (Hncg : ncg = (mu2 - au) / csz) by reflexivity;
  assert (Hnfe : nfe = nf + nce) by reflexivity; assert (Hnfg : nfg = nf + ncg) by reflexivity;
  assert (Hfadr : fadr = AFk5.FAv ly c + mf) by reflexivity; assert (Hshf : shf = AFk5.SHBv + fadr / 8) by reflexivity;
  assert (Hmf2 : mf2 = mf + kFreeArrayMapSize) by reflexivity; assert (Haue : aue = au + nce * csz) by reflexivity; assert (Haug : aug = au + ncg * csz) by reflexivity.

(* The cache-init step of the uninited arms on the real memory (donor AFkv.v:88-104): mR is the walk's memory on
   the cache tables and mem0 elsewhere. *)
Local Ltac top_init msJ TBF TPR :=
  match goal with HARU : FSP.ARU tfibsegs B ?ly ?S ?U ?W ?mem0 ?md0, HAR : AR tfibsegs B ?ly ?S ?W ?mem0u ?md0, IMG : img_cover ?ly |- _ =>
  set (mR := fun x : word => if tabwb (ly_T ly) (bv_unsigned x) then ms_mem msJ x else mem0 x);
  assert (MEQR : forall x : word, ~ TABW (ly_T ly) (bv_unsigned x) -> mR x = mem0 x)
    by (intros x Hx; unfold mR; destruct (tabwb (ly_T ly) (bv_unsigned x)) eqn:Et; [exfalso; apply Hx; apply tabwb_spec; exact Et | reflexivity]);
  assert (MON : forall x : word, TABW (ly_T ly) (bv_unsigned x) -> mR x = ms_mem msJ x)
    by (intros x Hx; unfold mR; apply tabwb_spec in Hx; rewrite Hx; reflexivity);
  pose proof (AFhn.T_facts B ly S W mem0u md0 HAR IMG) as (TR1 & TR2 & _);
  assert (TBFR : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) (ly_T ly) i)
    by (intros i Hi; destruct (TBF i Hi) as [M1 M2];
        split; (eapply val_mem_frame; [|eassumption]); intros k Hk; apply MON;
        rewrite unsigned_lit_small by (clear - Hi Hk TR1 TR2; ceil; unfold kThreadObjSize, ASAN_CEIL in *; lia); exists i; lia);
  assert (TPRR : forall a, TABW (ly_T ly) a -> apresent (w_H W) mR a)
    by (intros a Ha; pose proof (TABW_range _ _ Ha) as Hr; eapply apresent_same; [|exact (TPR a Ha)]; apply MON;
        rewrite unsigned_lit_small by (clear - Hr TR1 TR2; ceil; unfold kThreadObjSize, ASAN_CEIL in *; lia); exact Ha)
  end.

Theorem refill_inited_B3U : forall ly S U W regs0 mem0 md0 c, FAR.refill_preU B ly S U W regs0 mem0 md0 c ->
  st_cache_inited S = true -> fa_len (rg_free (reg S c)) < max_cached c / 2 ->
  amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (FAR.refill_leafU B ly S U W regs0 mem0 md0 c).
Proof.
intros ly S U W regs0 mem0 md0 c PREU Hinited Hfew. top_pre.
assert (Hnlt : nf < n) by exact Hfew.
pose proof (@AFkk.Hnf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@AFkk.Hmf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@AFkk.Hmu' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
pose proof (@AFkk.Hcarved' _ W ly mem0u c au mu HcR B S HARm Hau_def Hmu_def) as Hcarved.
pose proof (@AFkk.Hau_al' _ W ly mem0u c au csz HcR Hcsz B S HARm Hau_def) as Hau_al.
top_r3 ly c n nf mf au mu csz.
destruct (@AFkk.junk_valuesR _ W ly regs0 mem0u c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
  as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@AFkk.HslotPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPresu.
pose proof (@AFkk.HfaPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPresu.
pose proof (@AFk5.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (HslotPres : forall a, AFk5.DSTv ly c <= a < AFk5.DSTv ly c + 64 -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HslotPresu a Ha)].
  apply (T_offU_any ly S U W mem0 md0 HARU). clear - Ha DR. unfold kThreadObjSize, t_cache in *. lia. }
assert (HfaPres : forall a, AFk5.FAv ly c <= a < AFk5.FAv ly c + mf -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HfaPresu a Ha)].
  apply (FAR.offU_high B ly S U W mem0 md0 a HARU). pose proof Hmf as [[M0 M1] _]. clear - Ha DR M0 M1.
  ceil. unfold ASAN_CEIL, kFreeArrayOffset, kFreeArrayMax, kHighMemBeg in *. lia. }
pose proof (@AFkk.SEEDR3_ok _ _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg
  Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) as SEEDu.
pose proof (proj1 (FAR.st_ok_unpoison_iff U _ SS0R3 (w_H W) regs0 (w64 0x36ce4) mem0 (seg_rom tfibsegs)
  (@REG0R3_regions_off_ush W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
     IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S U HARU)) SEEDu) as SEED.
eapply amreal_SRr_pre.
{ exact (@AFkb.seg3J _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
    IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hpres0Rr mat0 SEED). }
intros W' c' _ HJ. pose proof HJ as [EW (msJ & matJ & E' & EcJ & _)]. subst W'. rewrite EcJ in HJ |- *.
exact (@FARf.refill_B3U _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2
  Haue Haug matJ msJ HJ HslotPres HfaPres B S U TS HTSD HARU Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hpum Hslack HQL).
Qed.

Theorem refill_inited_B2U : forall ly S U W regs0 mem0 md0 c, FAR.refill_preU B ly S U W regs0 mem0 md0 c ->
  st_cache_inited S = true -> max_cached c / 2 <= fa_len (rg_free (reg S c)) ->
  amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (FAR.refill_leafU B ly S U W regs0 mem0 md0 c).
Proof.
intros ly S U W regs0 mem0 md0 c PREU Hinited Henough. top_pre.
assert (Hnle : n <= nf) by exact Henough.
pose proof (@AFkx.Hnf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@AFkx.Hmf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@AFkx.Hmu' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
destruct (@AFkx.junk_valuesR _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
  as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@AFkx.HslotPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPresu.
pose proof (@AFkx.HfaPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPresu.
pose proof (@AFko.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (HslotPres : forall a, AFko.DSTv ly c <= a < AFko.DSTv ly c + 64 -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HslotPresu a Ha)].
  apply (T_offU_any ly S U W mem0 md0 HARU). clear - Ha DR. unfold kThreadObjSize, t_cache in *. lia. }
assert (HfaPres : forall a, AFko.FAv ly c <= a < AFko.FAv ly c + mf -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HfaPresu a Ha)].
  apply (FAR.offU_high B ly S U W mem0 md0 a HARU). pose proof Hmf as [[M0 M1] _]. clear - Ha DR M0 M1.
  ceil. unfold ASAN_CEIL, kFreeArrayOffset, kFreeArrayMax, kHighMemBeg in *. lia. }
pose proof (@AFkx.SEEDR_ok _ _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm
  Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) as SEEDu.
pose proof (proj1 (FAR.st_ok_unpoison_iff U _ SS0R (w_H W) regs0 (w64 0x36ce4) mem0 (seg_rom tfibsegs)
  (@REG0R_regions_off_ush W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S U HARU)) SEEDu) as SEED.
destruct (@AFkz.refill_B2_model _ W ly regs0 mem0u c maxc n nf mf au mu csz HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hnle)
  as (tops & rest & EP & RUN & WFR & Ee1 & Ee2 & Ee3 & Ee4).
eapply amreal_SRr_pre.
{ exact (@AFkw.seg2J _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp mat0 SEED). }
intros W' c' _ HJ. pose proof HJ as [EW (msJ & matJ & E' & EcJ & _)]. subst W'. rewrite EcJ in HJ |- *.
rewrite RUN. cbn [amreal].
eapply SRr_mono.
{ exact (@AFkw.segB2 _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2
    Hsp Hra Htp matJ msJ HJ HslotPres HfaPres Hnle). }
intros W'' c'' _ HR.
exact (@LEAF_B2U W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2
  Hsp matJ msJ HJ HfaPres B S U TS HTSD HARU Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hnle tops rest W'' c'' WFR Ee1 Ee2 Ee3 Ee4 HR).
Qed.

Theorem refill_uninit_B3U : forall ly S U W regs0 mem0 md0 c, FAR.refill_preU B ly S U W regs0 mem0 md0 c ->
  st_cache_inited S = false -> fa_len (rg_free (reg S c)) < max_cached c / 2 ->
  amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (FAR.refill_leafU B ly S U W regs0 mem0 md0 c).
Proof.
intros ly S U W regs0 mem0 md0 c PREU Huninit Hfew. top_pre.
assert (Hnlt : nf < n) by exact Hfew.
pose proof (@AFkk.Hnf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@AFkk.Hmf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@AFkk.Hmu' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
pose proof (@AFkk.Hcarved' _ W ly mem0u c au mu HcR B S HARm Hau_def Hmu_def) as Hcarved.
pose proof (@AFkk.Hau_al' _ W ly mem0u c au csz HcR Hcsz B S HARm Hau_def) as Hau_al.
top_r3 ly c n nf mf au mu csz.
destruct (@AFkk.junk_valuesR _ W ly regs0 mem0u c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
  as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@AFkk.HslotPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPresu.
pose proof (@AFkk.HfaPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPresu.
pose proof (@AFk5.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (HslotPres : forall a, AFk5.DSTv ly c <= a < AFk5.DSTv ly c + 64 -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HslotPresu a Ha)].
  apply (T_offU_any ly S U W mem0 md0 HARU). clear - Ha DR. unfold kThreadObjSize, t_cache in *. lia. }
assert (HfaPres : forall a, AFk5.FAv ly c <= a < AFk5.FAv ly c + mf -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HfaPresu a Ha)].
  apply (FAR.offU_high B ly S U W mem0 md0 a HARU). pose proof Hmf as [[M0 M1] _]. clear - Ha DR M0 M1.
  ceil. unfold ASAN_CEIL, kFreeArrayOffset, kFreeArrayMax, kHighMemBeg in *. lia. }
pose proof (@AFkk.thread_present _ W ly regs0 mem0u c maxc nf mf au mu csz IMG LY HcR Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HTPu.
assert (HTP : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> apresent (w_H W) mem0 a)
  by (intros a Ha; apply (FAR.apresent_of_unpoison _ U); [exact (T_offU_any ly S U W mem0 md0 HARU a Ha) | exact (HTPu a Ha)]).
pose proof (@AFkk.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@AFkk.SEEDU3_ok _ _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg
  Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Huninit) as SEEDu.
pose proof (proj1 (FAR.st_ok_unpoison_iff U _ SS0U3 (w_H W) regs0 (w64 0x36ce4) mem0 (seg_rom tfibsegs)
  (@REG0U3_regions_off_ush W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
     IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S U HARU)) SEEDu) as SEED.
eapply amreal_SRr_pre.
{ exact (@AFkl.segU _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
    IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp mat0 HTP HSPAN SEED). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
top_init msJ TBF TPR.
pose proof (ARU_init ly S U W mem0 mR md0 HARU Huninit MEQR TBFR TPRR) as HARU1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by exact (AFhn.PRES_MONO ly W mem0 mR MEQR TPRR).
assert (Hinited1 : st_cache_inited (AFhn.S1 S) = true) by reflexivity.
assert (Hchunks1 : pc_chunks (cache (AFhn.S1 S) c) = []) by (rewrite (AFhn.cache_S1 B ly S W mem0u md0 HAR Huninit c HcR); reflexivity).
assert (Hnf_def1 : nf = fa_len (rg_free (reg (AFhn.S1 S) c))) by exact Hnf_def. assert (Hmf_def1 : mf = rg_mapped_fa (reg (AFhn.S1 S) c)) by exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg (AFhn.S1 S) c)) by exact Hau_def. assert (Hmu_def1 : mu = rg_mapped_user (reg (AFhn.S1 S) c)) by exact Hmu_def.
assert (Hpum1 : refill_reg (AFhn.S1 S) c) by exact (refill_reg_init S c ltac:(clear - HcR; lia) Hpum).
assert (Hslack1 : A_bytes (w_A W) + EV_A <= abudget (AFhn.S1 S)) by exact Hslack.
assert (HQL1 : qloosem (AFhn.S1 S)) by exact HQL.
assert (HslotPres1 : forall a, AFk5.DSTv ly c <= a < AFk5.DSTv ly c + 64 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HslotPres, Ha).
assert (HfaPres1 : forall a, AFk5.FAv ly c <= a < AFk5.FAv ly c + mf -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HfaPres, Ha).
assert (HJ : @AFk5.at_R3 _ ly regs0 mR c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  W md0 (@AFk5.WINR0 ly regs0 c) AFkb.PT R3_J W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [reflexivity|]. exists msJ, matJ, E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HSJ|]. split; [|split; [exact PRS | exact I]].
  intros x Hx. destruct (TABW_dec (ly_T ly) (bv_unsigned x)) as [Ht|Ht]; [rewrite (MON x Ht); reflexivity | rewrite (MEQR x Ht); exact (MEQ x Hx Ht)]. }
rewrite (AFhn.refill_tree_init c S Huninit). fold (AFhn.S1 S).
eapply amreal_mono; [intros r W'' c''; exact (refill_leaf_initU ly S U W mem0 mR md0 HARU MEQR regs0 c r W'' c'')|].
exact (@FARf.refill_B3U _ _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2
  Haue Haug matJ msJ HJ HslotPres1 HfaPres1 B (AFhn.S1 S) U TS HTSD HARU1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 Hpum1 Hslack1 HQL1).
Qed.

Theorem refill_uninit_B2U : forall ly S U W regs0 mem0 md0 c, FAR.refill_preU B ly S U W regs0 mem0 md0 c ->
  st_cache_inited S = false -> max_cached c / 2 <= fa_len (rg_free (reg S c)) ->
  amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (FAR.refill_leafU B ly S U W regs0 mem0 md0 c).
Proof.
intros ly S U W regs0 mem0 md0 c PREU Huninit Henough. top_pre.
assert (Hnle : n <= nf) by exact Henough.
pose proof (@AFkx.Hnf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@AFkx.Hmf' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@AFkx.Hmu' _ W ly regs0 mem0u c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
destruct (@AFkx.junk_valuesR _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
  as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@AFkx.HslotPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPresu.
pose proof (@AFkx.HfaPres' _ W ly regs0 mem0u c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPresu.
pose proof (@AFko.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (HslotPres : forall a, AFko.DSTv ly c <= a < AFko.DSTv ly c + 64 -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HslotPresu a Ha)].
  apply (T_offU_any ly S U W mem0 md0 HARU). clear - Ha DR. unfold kThreadObjSize, t_cache in *. lia. }
assert (HfaPres : forall a, AFko.FAv ly c <= a < AFko.FAv ly c + mf -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (FAR.apresent_of_unpoison _ U); [|exact (HfaPresu a Ha)].
  apply (FAR.offU_high B ly S U W mem0 md0 a HARU). pose proof Hmf as [[M0 M1] _]. clear - Ha DR M0 M1.
  ceil. unfold ASAN_CEIL, kFreeArrayOffset, kFreeArrayMax, kHighMemBeg in *. lia. }
pose proof (@AFkx.thread_present _ W ly regs0 mem0u c maxc nf mf au mu LY IMG HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HTPu.
assert (HTP : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> apresent (w_H W) mem0 a)
  by (intros a Ha; apply (FAR.apresent_of_unpoison _ U); [exact (T_offU_any ly S U W mem0 md0 HARU a Ha) | exact (HTPu a Ha)]).
pose proof (@AFkx.SPAN_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@AFkx.SEEDU_ok _ _ W ly regs0 mem0u c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm
  Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Huninit) as SEEDu.
pose proof (proj1 (FAR.st_ok_unpoison_iff U _ SS0U2 (w_H W) regs0 (w64 0x36ce4) mem0 (seg_rom tfibsegs)
  (@REG0U2_regions_off_ush W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S U HARU)) SEEDu) as SEED.
eapply amreal_SRr_pre.
{ exact (@AFky.segU _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2
    Hsp mat0 HTP HSPAN SEED). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
top_init msJ TBF TPR.
pose proof (ARU_init ly S U W mem0 mR md0 HARU Huninit MEQR TBFR TPRR) as HARU1.
pose proof (proj1 (FSP.ARU_AR tfibsegs B ly (AFhn.S1 S) U W mR md0 HARU1)) as HARm1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by exact (AFhn.PRES_MONO ly W mem0 mR MEQR TPRR).
assert (Hinited1 : st_cache_inited (AFhn.S1 S) = true) by reflexivity.
assert (Hchunks1 : pc_chunks (cache (AFhn.S1 S) c) = []) by (rewrite (AFhn.cache_S1 B ly S W mem0u md0 HAR Huninit c HcR); reflexivity).
assert (Hnf_def1 : nf = fa_len (rg_free (reg (AFhn.S1 S) c))) by exact Hnf_def. assert (Hmf_def1 : mf = rg_mapped_fa (reg (AFhn.S1 S) c)) by exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg (AFhn.S1 S) c)) by exact Hau_def. assert (Hmu_def1 : mu = rg_mapped_user (reg (AFhn.S1 S) c)) by exact Hmu_def.
assert (HslotPres1 : forall a, AFko.DSTv ly c <= a < AFko.DSTv ly c + 64 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HslotPres, Ha).
assert (HfaPres1 : forall a, AFko.FAv ly c <= a < AFko.FAv ly c + mf -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HfaPres, Ha).
assert (HJ : @AFko.at_R _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 RJ2 W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [reflexivity|]. exists msJ, matJ, E'. split; [reflexivity|]. split; [exact (proj1 HE)|]. split; [exact HSJ|]. split; [|exact PRS].
  intros x Hx. destruct (TABW_dec (ly_T ly) (bv_unsigned x)) as [Ht|Ht]; [rewrite (MON x Ht); reflexivity | rewrite (MEQR x Ht); exact (MEQ x Hx Ht)]. }
rewrite (AFhn.refill_tree_init c S Huninit). fold (AFhn.S1 S).
eapply amreal_mono; [intros r W'' c''; exact (refill_leaf_initU ly S U W mem0 mR md0 HARU MEQR regs0 c r W'' c'')|].
destruct (@AFkz.refill_B2_model _ W ly regs0 (FSP.unpoison U mR) c maxc n nf mf au mu csz HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B (AFhn.S1 S) HARm1 Hinited1 Hchunks1
  Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 Hnle) as (tops & rest & EP & RUN & WFR & Ee1 & Ee2 & Ee3 & Ee4).
rewrite RUN. cbn [amreal].
eapply SRr_mono.
{ exact (@AFkw.segB2 _ _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2
    Hsp Hra Htp matJ msJ HJ HslotPres1 HfaPres1 Hnle). }
intros W'' c'' _ HR.
exact (@LEAF_B2U W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2
  Hsp matJ msJ HJ HfaPres1 B (AFhn.S1 S) U TS HTSD HARU1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 Hnle tops rest W'' c'' WFR Ee1 Ee2 Ee3 Ee4 HR).
Qed.

(* The refill top (donor lib/A/AFkv.v:226) for any U. *)
Theorem tfib_refill_okU : FAR.tfib_refill_specU B.
Proof.
intros ly S U W regs mem md c PRE.
destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [Hfew|Henough]; destruct (st_cache_inited S) eqn:Hi.
- exact (refill_inited_B3U ly S U W regs mem md c PRE Hi Hfew).
- exact (refill_uninit_B3U ly S U W regs mem md c PRE Hi Hfew).
- exact (refill_inited_B2U ly S U W regs mem md c PRE Hi Henough).
- exact (refill_uninit_B2U ly S U W regs mem md c PRE Hi Henough).
Qed.
End top.

End d.


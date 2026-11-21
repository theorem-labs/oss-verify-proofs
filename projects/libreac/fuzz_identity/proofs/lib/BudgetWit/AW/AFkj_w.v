(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFkj.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFkj.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG0s_w YG0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0l AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1w AE3d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB19 AF0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFl1_w AFhy_w AFis_w AFkp_w AFk6_w AFk5_w AFhz_w AFk8_w AFk7_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YFk4.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AFk3 AB1q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhm_w AFka_w AFkk_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFIB_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
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
Section g.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Variables (need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pr := (@AFk5_w.Pr ly c).
Local Abbreviation RGv := (@AFk5_w.RGv ly c).
Local Abbreviation RBv := (@AFk5_w.RBv ly c).
Local Abbreviation FAv := (@AFk5_w.FAv ly c).
Local Abbreviation SHBv := (@AFk5_w.SHBv).
Local Abbreviation SRCv := (@AFk5_w.SRCv ly c n nf).
Local Abbreviation DSTv := (@AFk5_w.DSTv ly c).
Local Abbreviation XWR := (@AFk5_w.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E0 := (@AFk5_w.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaT := (@AFk5_w.EaT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaC := (@AFk5_w.EaC ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSB := (@AFk5_w.EaSB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaTOP := (@AFk5_w.EaTOP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaCL := (@AFk5_w.EaCL ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaP := (@AFk5_w.EaP ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMAX := (@AFk5_w.EaMAX ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaN := (@AFk5_w.EaN ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaCSZ := (@AFk5_w.EaCSZ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRG := (@AFk5_w.EaRG ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRB := (@AFk5_w.EaRB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaFA := (@AFk5_w.EaFA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNF := (@AFk5_w.EaNF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF := (@AFk5_w.EaMF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAU := (@AFk5_w.EaAU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMU := (@AFk5_w.EaMU ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHB := (@AFk5_w.EaSHB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNEED := (@AFk5_w.EaNEED ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaTOT := (@AFk5_w.EaTOT ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaADR := (@AFk5_w.EaADR ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHA := (@AFk5_w.EaSHA ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Hypothesis IMG : img_cover ly.
Local Abbreviation EaMU2 := (@AFk5_w.EaMU2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNCe := (@AFk5_w.EaNCe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNCg := (@AFk5_w.EaNCg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNFe := (@AFk5_w.EaNFe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNFg := (@AFk5_w.EaNFg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaFADR := (@AFk5_w.EaFADR ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHF := (@AFk5_w.EaSHF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF2 := (@AFk5_w.EaMF2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAUe := (@AFk5_w.EaAUe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaAUg := (@AFk5_w.EaAUg ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation Er := (@AFk5_w.Er ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E2 := (@AFk5_w.E2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E1 := (@AFk5_w.E1 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E8 := (@AFk5_w.E8 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
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
Local Abbreviation class_facts := (@AFk5_w.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@AFk5_w.high_factsR _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_T := (@AFk5_w.off_T _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_C := (@AFk5_w.off_C _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation derived_rangesR := (@AFk5_w.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation WINR0 := (@AFk5_w.WINR0 ly regs0 c).
Local Abbreviation WINR := (@AFk5_w.WINR ly regs0 c n).
Local Abbreviation WINR0_WINR := (@AFk5_w.WINR0_WINR ly regs0 c n).
Local Abbreviation WSKELR := (@AFk5_w.WSKELR).
Local Abbreviation win_sub := (@AFk5_w.win_sub).
Local Abbreviation win_sub_sound := (@AFk5_w.win_sub_sound ly regs0 c maxc n mf au mu Hmax Hn Hmf Hmu).
Local Abbreviation WSKELR_WINR0 := (@AFk5_w.WSKELR_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation windows_WINR0 := (@AFk5_w.windows_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_WINR0 := (@AFk5_w.frame_WINR0 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation frame_X := (@AFk5_w.frame_X _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation W_DST := (@AFk5_w.W_DST ly c n).
Local Abbreviation W_FE := (@AFk5_w.W_FE ly c nf).
Local Abbreviation W_UW := (@AFk5_w.W_UW adr).
Local Abbreviation W_USH := (@AFk5_w.W_USH sha).
Local Abbreviation W_FW := (@AFk5_w.W_FW fadr).
Local Abbreviation W_FSH := (@AFk5_w.W_FSH shf).
Local Abbreviation at_R3 := (@AFk5_w.at_R3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_N3 := (@AFk5_w.at_N3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_RET3 := (@AFk5_w.at_RET3 _ regs0 mem0).
Local Abbreviation P_cells := (@AFk5_w.P_cells ly c maxc csz).
Local Abbreviation chunk_index := (@AFk5_w.chunk_index).
Local Abbreviation pstable := (@AFk5_w.pstable ly regs0 c).
Local Abbreviation all_disjoint_of_forall := (@AFk5_w.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFk5_w.kept_of_frame ly regs0 maxc mf au mu).
Local Abbreviation kept_of_frame2 := (@AFk5_w.kept_of_frame2 ly regs0 maxc mf au mu).
Local Abbreviation SKEL_TAILR := (@AFk5_w.SKEL_TAILR).
Local Abbreviation RFACTSR := (@AFk5_w.RFACTSR ly regs0 c).
Local Abbreviation stack_ivsR := (@AFk5_w.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation zone_litR := (@AFk5_w.zone_litR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_TR := (@AFk5_w.zone_TR _ ly regs0 c maxc mf au mu IMG LY Hmf Hmu Hsp).
Local Abbreviation zone_CR := (@AFk5_w.zone_CR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation zone_RGR := (@AFk5_w.zone_RGR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation slots_not_WINR0 := (@AFk5_w.slots_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation fa_not_WINR0 := (@AFk5_w.fa_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation tail_ext_okR := (@AFk5_w.tail_ext_okR _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := (@AFk5_w.rdn_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation store_ok_of_presentR := (@AFk5_w.store_ok_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation cpy4_stretch := (@AFk5_w.cpy4_stretch _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Local Abbreviation facts3 := (@AFk5_w.facts3 _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation RFACTS3 := (@AFk5_w.RFACTS3 ly regs0 c).
Local Abbreviation tail_ext_ok3 := (@AFk5_w.tail_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation stack_ext_ok3 := (@AFk5_w.stack_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation scratch_headed := (@AFk5_w.scratch_headed).
Local Abbreviation mem_ok_scratch_present := (@AFk5_w.mem_ok_scratch_present _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY Hmf Hmu Hsp).
Local Abbreviation at_R3_run := (@AFk5_w.at_R3_run _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_run_ecall := (@AFk5_w.at_R3_run_ecall _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_pin := (@AFk5_w.at_R3_pin _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_arm := (@AFk5_w.at_R3_arm _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_forget := (@AFk5_w.at_R3_forget _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_noconds := (@AFk5_w.at_R3_noconds _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_weaken := (@AFk5_w.at_R3_weaken _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_facts := (@AFk5_w.at_R3_facts _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_strengthen := (@AFk5_w.at_R3_strengthen _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_eq := (@AFk5_w.at_R3_eq _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation CSAVED := (@AFk5_w.CSAVED).
Local Abbreviation sv_denot_SOff0 := (@AFk5_w.sv_denot_SOff0).
Local Abbreviation at_R3_ret := (@AFk5_w.at_R3_ret _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp).
Local Abbreviation at_N3_cont := (@AFk5_w.at_N3_cont _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation memset_stretch3 := (@AFk5_w.memset_stretch3 _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Local Abbreviation nth_Z_to_le_bytes4 := (@AFk5_w.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (@AFk5_w.popfree_stretch _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
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
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Local Abbreviation Pr_is := (@AFk5_w.Pr_is ly c).
Local Abbreviation RGv_is := (@AFk5_w.RGv_is ly c).
Local Abbreviation FAv_is := (@AFk5_w.FAv_is ly c HcR).
Local Abbreviation RBv_is := (@AFk5_w.RBv_is ly c HcR).
Local Abbreviation cls_wfR := (@AFkk_w.cls_wfR _ W ly mem0 c HcR B S HARm Hinited).
Local Abbreviation cls_wf0 := (@AFkk_w.cls_wf0 _ W ly mem0 c HcR B S HARm).
Local Abbreviation reg_facts0 := (@AFkk_w.reg_facts0 _ W ly regs0 mem0 c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_facts := (@AFkk_w.reg_facts _ W ly regs0 mem0 c maxc nf mf au mu HcR Hmax Hsp B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (@AFkk_w.Hnf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmf' := (@AFkk_w.Hmf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmu' := (@AFkk_w.Hmu' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hcarved' := (@AFkk_w.Hcarved' _ W ly mem0 c au mu HcR B S HARm Hau_def Hmu_def).
Local Abbreviation Hau_al' := (@AFkk_w.Hau_al' _ W ly mem0 c au csz HcR Hcsz B S HARm Hau_def).
Local Abbreviation vis_present := (@AFkk_w.vis_present _ W ly regs0 mem0 maxc B S HARm).
Local Abbreviation thread_present := (@AFkk_w.thread_present _ W ly regs0 mem0 c maxc nf mf au mu csz IMG LY HcR Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation rinfo_present := (@AFkk_w.rinfo_present _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HslotPres' := (@AFkk_w.HslotPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HfaPres' := (@AFkk_w.HfaPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation word_of_present := (@AFkk_w.word_of_present W ly regs0 mem0 maxc).
Local Abbreviation val_mem_lo4 := (@AFkk_w.val_mem_lo4 ly regs0 maxc).
Local Abbreviation junk_valuesR := (@AFkk_w.junk_valuesR _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation cell_sym := (@AFkk_w.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@AFkk_w.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@AFkk_w.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_cache := (@AFkk_w.In_acells_cache ly regs0 c maxc HcR B S).
Local Abbreviation In_acells_region := (@AFkk_w.In_acells_region ly regs0 c maxc HcR B S).
Local Abbreviation cache_valsR := (@AFkk_w.cache_valsR _ W ly regs0 mem0 c maxc csz HcR Hmax Hcsz B S HARm Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@AFkk_w.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (@AFkk_w.cache_valsU _ W ly regs0 mem0 maxc B S HARm).
Local Abbreviation region_valsR := (@AFkk_w.region_valsR _ W ly regs0 mem0 c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation chunk_lit := (@AFkk_w.chunk_lit W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_lit_at := (@AFkk_w.chunk_lit_at W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_atom := (@AFkk_w.chunk_atom W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation REG0R3_ok_but35 := (@AFkk_w.REG0R3_ok_but35 _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0R3_ok := (@AFkk_w.REG0R3_ok _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0U3_ok := (@AFkk_w.REG0U3_ok _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSR3_ok := (@AFkk_w.PAIRSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SPAN3_disj := (@AFkk_w.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation FACTSR3_ok := (@AFkk_w.FACTSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation SEEDR3_ok := (@AFkk_w.SEEDR3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSU3_ok := (@AFkk_w.PAIRSU3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEEDU3_ok := (@AFkk_w.SEEDU3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Open Scope am_scope.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition fr : list fseg := rg_free (reg S c).
Definition hol : list (Z * Z) := rg_holes (reg S c).
Lemma len_facts3 : length (st_regions S) = 32%nat /\ length (st_cache S) = 32%nat /\ (Z.to_nat c < 32)%nat.
Proof. pose proof (wf_len_regions _ _ _ _ _ WF). pose proof (wf_len_cache _ _ _ _ _ WF). repeat split; try assumption. clear - HcR. zlia. Qed.
Lemma reg_S : reg S c = mkRegion mu au mf fr hol.
Proof. rewrite Hmu_def, Hau_def, Hmf_def. unfold fr, hol. destruct (reg S c); reflexivity. Qed.
Lemma reg_upd3 : forall r', reg (upd_reg c r' S) c = r'.
Proof. intros r'. pose proof len_facts3 as (L1 & _ & L3). apply reg_upd_reg; [clear - HcR; zlia | rewrite L1; exact L3]. Qed.
Lemma cache_upd3 : forall r' p', cache (upd_pc c p' (upd_reg c r' S)) c = p'.
Proof. intros r' p'. pose proof len_facts3 as (_ & L2 & L3). apply cache_upd_pc; [clear - HcR; zlia | unfold upd_reg; cbn; rewrite L2; exact L3]. Qed.
Lemma PM3 : pc_max (cache S c) = maxc.
Proof. pose proof (wf_classes _ _ _ _ _ WF c HcR) as C. unfold wf_class in C. rewrite Hinited in C. rewrite Hmax. exact (proj1 (wr_cache _ _ _ _ _ _ C)). Qed.
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
constructor; [clear - NN G1; zlia|]. unfold fr. exact (wr_runs _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c HcR)).
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
End g.
End d.

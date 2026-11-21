(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFkc.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFkc.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhm_w AFka_w AFkk_w AFkb_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
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
Section f.
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
Local Abbreviation class_facts := (@AFk5_w.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@AFk5_w.high_factsR _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_T := (@AFk5_w.off_T _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_C := (@AFk5_w.off_C _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
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
Local Abbreviation PT := (@AFkb_w.PT).
Local Abbreviation pstable_PT := (@AFkb_w.pstable_PT ly regs0 c).
Local Abbreviation WX0 := (@AFkb_w.WX0 ly regs0 c).
Local Abbreviation at_R3_init := (@AFkb_w.at_R3_init _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug mat0 msJ SEEDJ).
Local Abbreviation seg3J := (@AFkb_w.seg3J _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hpres0R).
Local Abbreviation land_hi0 := (@AFkb_w.land_hi0).
Local Abbreviation seg3P := (@AFkb_w.seg3P _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug mat0 msJ SEEDJ).
Local Abbreviation T16 := (@AFkb_w.T16).
Local Abbreviation TMID := (@AFkb_w.TMID).
Local Abbreviation U_csz := (@AFkb_w.U_csz ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation U_csz31 := (@AFkb_w.U_csz31 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug Hcsz).
Local Abbreviation U_csz16 := (@AFkb_w.U_csz16 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hcsz Hmf Hmu).
Local Abbreviation U_cszmid := (@AFkb_w.U_cszmid ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hcsz).
Local Abbreviation U_tot_of := (@AFkb_w.U_tot_of _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation U_tot31 := (@AFkb_w.U_tot31 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation U_rb := (@AFkb_w.U_rb _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation seg3Q31 := (@AFkb_w.seg3Q31 _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Q16 := (@AFkb_w.seg3Q16 _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Qmid := (@AFkb_w.seg3Qmid _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation U_mu := (@AFkb_w.U_mu ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug Hmf Hmu).
Local Abbreviation U_tot := (@AFkb_w.U_tot _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Q_map := (@AFkb_w.seg3Q_map _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Q_ok := (@AFkb_w.seg3Q_ok _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3M := (@AFkb_w.seg3M _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
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
Ltac arm_zev3 := rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U;
rewrite !U_zev by (vm_compute; reflexivity); cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv3 HS HEn ss i off :=
let j := eval vm_compute in (chunk_index (match nth_error (ss_mem ss) i with Some r => YP09.r_chunks r | None => [] end) off) in
memv HS i j;
[ cbn [base_val YP09.r_base]; first [ unfold rP; rewrite (HEn 37%nat ltac:(cbv; zlia)), EaP | unfold rRG; rewrite (HEn 41%nat ltac:(cbv; zlia)), EaRG ];
unfold w64; rewrite unsigned_lit_small by zlia; zlia | | ].
Ltac val_atom HEn :=
first [ reflexivity
| lazymatch goal with |- sv_denot _ (SOff ?k _) = _ =>
cbn [sv_denot]; rewrite (HEn k ltac:(cbv; zlia));
rewrite ?EaN, ?EaMAX, ?EaCSZ, ?EaNF, ?EaMF, ?EaAU, ?EaMU, ?EaNFe, ?EaNFg, ?EaMF2, ?EaAUe, ?EaAUg;
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
Lemma seg3_Ur : forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P R3_NUr W' c' -> SRr tfibsegs W' c' (at_N3 Wx md X P R3_NR).
Proof.
intros Wx md X P W' c' HX HP HR.
lazymatch type of HR with at_R3 ?Wy ?mdy ?Xy ?Py ?ss ?W4 ?c4 =>
let cs := eval vm_compute in (match nth_error (ss_mem R3_NR) 0 with Some r => YP09.r_chunks r | None => [] end) in
eapply (at_R3_run_ecall Wy tfibtbl_rtC tfibtbl_rtC_ok 0x7ffffff0 mdy Xy Py ss R3_NR W4 c4 HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | exists cs; vm_compute; reflexivity ] end.
Qed.
Lemma seg3_URg : forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P R3_NRg W' c' -> SRr tfibsegs W' c' (at_RET3 Wx 0 md X (fun m => P m /\ P_cells Wx 0 nf mf au mu m)).
Proof.
intros Wx md X P W' c' HX HP HR.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] _].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & _).
assert (RP : 0 <= Pr /\ Pr + 16 < 2 ^ 64) by (clear - DR F2; numconst; zlia). assert (RR : 0 <= RGv /\ RGv + 128 < 2 ^ 64) by (clear - DR; numconst; zlia).
r3_run HR tfibtbl_rtC tfibtbl_rtC_ok 0x7ffffff0 R3_F1 HX HP.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 R3_FRET HX HP.
eapply (at_R3_ret Wx md X _ R3_FRET _ _ 0); [| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| unfold CSAVED; repeat (apply Forall_cons; [vm_compute; reflexivity|]); apply Forall_nil ].
apply (at_R3_facts Wx md X P _ R3_FRET _ _ HR). clear HR. intros E' ms HE HS.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
cells3 HS HEn R3_FRET RP RR DR F1' F2.
all: first [ clear - K1; zlia | clear - K4; numconst; zlia | clear - F0 F1 M0 M1; unfold kFreeArrayMax in *; zlia | clear - U0 U1 U2; numconst; zlia ].
Qed.
Lemma seg3_Ug : forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P R3_NUg W' c' -> SRr tfibsegs W' c' (at_R3 Wx md X P R3_MSU).
Proof.
intros Wx md X P W' c' HX HP HR. pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & _).
r3_run HR tfibtbl_rtC tfibtbl_rtC_ok 0x7ffffff0 R3_G1 HX HP.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 R3_G2 HX HP.
assert (A8 : adr mod 8 = 0).
{ clear - G8. apply Z.mod_divide in G8 as [q Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q * 8192). zlia. }
assert (AHI : adr < 2 ^ 48) by (clear - G11 G14; pose proof (Z.mul_succ_div_gt adr 8 ltac:(zlia)); unfold SHBv in *; zlia).
assert (D0 : 0 <= adr / 8 < 2 ^ 45) by (clear - G6 AHI; numconst; split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; zlia]).
r3_pin HR (10%bv : bv 5) (SOff rSHA 0).
{ pin_zev3. unfold rSHA, rSHB, rADR. rewrite EaSHA, EaSHB, EaADR. unfold w64.
clear - G6 G11 G13 G14 A8 AHI D0. numconst. unfold SHBv in *.
rewrite (unsigned_lit_small sha), (unsigned_lit_small 2147450880), (unsigned_lit_small adr) by zlia.
rewrite !Z.add_0_r. rewrite (zcanon_id sha), (zcanon_id 2147450880), (zcanon_id adr) by (unfold M64; zlia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
rewrite (zcanon_id (adr / 8)) by (unfold M64; zlia).
rewrite zcanon_id by (unfold M64; zlia). zlia. }
r3_pin HR (12%bv : bv 5) (SLit 32768).
{ pin_zev3. unfold rADR. rewrite EaADR. unfold w64. clear - G6 A8 AHI D0. numconst.
rewrite (unsigned_lit_small adr) by zlia.
rewrite !Z.add_0_r. rewrite (zcanon_id (adr + 262136)), (zcanon_id adr) by (unfold M64; zlia).
change (Z.land (zcanon 3) 63) with 3. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
replace ((adr + 262136) / 8) with (adr / 8 + 32767).
2:{ apply Z.mod_divide in A8 as [q Hq]; [|zlia]. rewrite Hq. rewrite Z.div_mul by zlia. replace (q * 8 + 262136) with ((q + 32767) * 8) by zlia. rewrite Z.div_mul by zlia. zlia. }
rewrite (zcanon_id (adr / 8 + 32767)), (zcanon_id (adr / 8)) by (unfold M64; zlia).
change (zcanon 1) with 1. change (zcanon 32768) with 32768.
rewrite (zcanon_id (adr / 8 + 32767 + 1)) by (unfold M64; zlia).
replace (adr / 8 + 32767 + 1 - adr / 8) with 32768 by zlia. reflexivity. }
r3_station HR R3_MSU. apply SRr_ret. exact HR.
Qed.
Definition P_ush (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ forall x : word, W_USH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250).
Lemma pstable_ush : forall P, pstable P -> pstable (P_ush P).
Proof.
intros P HP m m' Hfr [H1 H2]. split; [exact (HP m m' Hfr H1)|].
intros x Hx. rewrite (Hfr x); [exact (H2 x Hx)|]. intros Hw.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G13 & G14 & _).
pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (_ & _ & _ & S4 & S5).
unfold W_USH, WINR0 in *. unfold Pr, RGv in *. clear - Hx Hw G13 G14 DR F1 F2 F3 F4 F5 F6 F7 F8 S4 S5 HcR. numconst. unfold kUserMapSize in *. change (262144 / 8) with 32768 in *. try unfold T in *. try unfold SB in *. zlia.
Qed.
Lemma seg3_Ums : forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
(forall m, P m -> forall a, W_USH a -> apresent (w_H Wx) m a) ->
(forall m m' : word -> option byte, (forall x : word, ~ W_USH (bv_unsigned x) -> m' x = m x) -> (forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P m -> P m') ->
at_R3 Wx md X P R3_MSU W' c' ->
SRr tfibsegs W' c' (at_R3 Wx md (fun a => X a \/ W_USH a) (P_ush P) R3_Kg).
Proof.
intros Wx md X P W' c' HX HP HPush HPu HR.
pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & _).
pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (S1 & S2 & S3 & S4 & S5).
pose proof stack_ext_ok3 as [SX1 SX2].
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
rreg HS (10%bv : bv 5) R10. rewrite (HEn 58%nat ltac:(cbv; zlia)), EaSHA in R10.
rreg HS (12%bv : bv 5) R12. rreg HS (1%bv : bv 5) R1. rreg HS (11%bv : bv 5) R11.
eapply (memset_stretch3 Wx hMSU E' R3_MSU ms _ sha 32768 0x36d24);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| exact R10 | exact R12 | exact R1
| clear; zlia | clear - G13; numconst; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia | clear - G14; zlia | reflexivity | clear; zlia
| intros a Ha; exact (HPush _ HPm a Ha)
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|Hr];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn 2%nat ltac:(cbv; zlia)), E2;
clear - G13 G14 S4 S5 SX1 SX2; numconst; try unfold sp0 in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILR in Hr by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7); clear - G13 G14 X1 X2 X3 X4 X5 X6 X7; numconst; zlia ].
intros regs3 mem3 mat3 HS3 H10' Hfr3 Hpr3 Hval3. rewrite wvb_collapse.
assert (HR : at_R3 Wx md (fun a => X a \/ W_USH a) (P_ush P) R3_G3 Wx
(mkCfg (mkst regs3 (Z_to_bv 64 0x36d24) mem3 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat3 md))).
{ split; [reflexivity|]. exists (mkst regs3 (Z_to_bv 64 0x36d24) mem3 (seg_rom tfibsegs)), mat3, (havoc E' hMSU (map (getr regs3) CLOB_MS)).
split; [reflexivity|]. split; [exact (env_agree_havoc_ge aHAV3 hMSU E0 E' _ ltac:(unfold aHAV3, hMSU; zlia) HE)|].
split; [exact HS3|]. cbn [ms_mem mkst]. split; [|split].
- intros x Hx. rewrite (Hfr3 x) by (intros Hw; apply Hx; right; exact Hw). apply MEQ. intros H; apply Hx; left; exact H.
- intros a Ha. apply Hpr3. exact (PRS a Ha).
- split; [| intros x Hx; rewrite (Hval3 x Hx), R11; reflexivity].
exact (HPu (ms_mem ms) mem3 Hfr3 Hpr3 HPm). }
clear HS HS3.
assert (HX' : forall a, WINR0 a -> X a \/ W_USH a) by (intros a Ha; left; exact (HX a Ha)).
pose proof (pstable_ush P HP) as HP'.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36d5c R3_Kg HX' HP'.
apply SRr_ret. exact HR.
Qed.
End f.
End d.

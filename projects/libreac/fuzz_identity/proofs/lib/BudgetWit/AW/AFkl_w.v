(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFkl.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFkl.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhm_w AFka_w.
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
Ltac clear3 := try clear Hnlt Hcarved Hau_al Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug.
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
Local Notation SSU := SS0U3. Local Notation REG0U := REG0U3. Local Notation REG0X := REG0R3.
Local Notation SU1 := R3_U1. Local Notation SU2 := R3_U2. Local Notation SU3 := R3_U3. Local Notation SU4 := R3_U4. Local Notation SU5 := R3_U5.
Local Notation SJ := R3_J. Local Notation HAVJ := aHAV3. Local Notation NREG := 41%nat.
Local Notation SU1_35 := R3_U1_35. Local Notation SU1_ext := R3_U1_ext. Local Notation SU1_len := R3_U1_len.
Local Notation SU2_eq := R3_U2_eq. Local Notation SU3_split := R3_U3_split. Local Notation SU3_35 := R3_U3_35'.
Local Notation SU3_ext := R3_U3_ext. Local Notation SU3_len := R3_U3_len. Local Notation SU4_eq := R3_U4_eq. Local Notation SU4_mem := R3_U4_mem.
Local Notation SUJ := R3_UJ.
Definition WINU (a : Z) : Prop :=
(sp0 - RSTACK <= a < sp0) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888).
Definition WSKELU : list (option nat * Z * Z) := [(Some 2%nat, - RSTACK, 0); (Some rRG, 0, 128); (Some rT, 2768, 2800); (Some rT, 2872, 2888)].
Lemma WINU_WINR0 : forall a, WINU a -> WINR0 a.
Proof. clear3. intros a H. unfold WINU, WINR0 in *. tauto. Qed.
Lemma WSKELU_WINU : forall (E : env) a t,
(forall k, (k < HAVJ)%nat -> ew E k = ew E0 k) -> In t WSKELU ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINU a.
Proof. clear3.
intros E a t HE Hin Hr. unfold WSKELU in Hin. cbn [In] in Hin. unfold WINU.
pose proof derived_rangesR as DR. pose proof high_factsR as HF. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize in DR, HF.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [fst snd base_val] in Hr; unfold rRG, rT in Hr; rewrite HE in Hr by (unfold aHAV3; zlia);
rewrite ?E2, ?EaT, ?EaRG in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by zlia; unfold sp0 in *; zlia |]
| False => destruct Hin
end.
Qed.
Lemma windows_WINU : forall (E : env) rs a,
(forall k, (k < HAVJ)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELU || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINU a.
Proof. clear3.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). exact (WSKELU_WINU E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Lemma frame_WINU : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < HAVJ)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELU || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINU (bv_unsigned x) -> m' x = m x.
Proof. clear3. intros E rs m m' HE Hb HF x Hx. apply HF. intros Hw. apply Hx. exact (windows_WINU E rs _ HE Hb Hw). Qed.
Definition POSTU (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
env_agree HAVJ E0 E' /\
st_ok tfibsegs E' SJ (restrict (w_H W) ms) /\
(forall x : word, ~ WINR0 (bv_unsigned x) -> ~ TABW T (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) (ms_mem ms)) T i) /\
(forall a, TABW T a -> apresent (w_H W) (ms_mem ms) a).
Lemma headcnt_TBLS0 : all_disjoint E0 headcnt TBLS0.
Proof. clear3.
apply all_disjoint_of_In. intros r Hr. destruct (In_TBLS0 r Hr) as (i & Hi & ->).
unfold extent_disjoint, headcnt, tblr. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold rP, rT. rewrite EaP, EaT.
pose proof derived_rangesR as (D1 & D2 & _). pose proof high_factsR as (F1 & F2 & _).
unfold w64. rewrite !unsigned_lit_small by (clear - D1 D2 F1 F2; numconst; try unfold T in *; zlia).
unfold Pr in *; try unfold T in *; clear - Hi HcR. numconst. assert (i < c \/ i = c \/ c < i) by zlia. zlia.
Qed.
Lemma sepU :
(forall a, T + 292 <= a < T + 2704 -> ~ WINU a) /\
(forall a, Pr <= a < Pr + 4 -> ~ WINU a /\ ~ TABW T a) /\
(forall i a, 1 <= i <= 31 -> i <> c -> T + 212 + 80 * i <= a < T + 224 + 80 * i -> ~ WINR0 a) /\
(forall a, WINU a \/ TABW T a \/ (Pr <= a < Pr + 4) -> 0 <= a < 2 ^ 64) /\
(0 <= Pr /\ Pr + 16 <= 2 ^ 64 /\ Pr = T + 208 + 80 * c /\ 4096 <= T   /\ T + kThreadObjSize <= 2 ^ 64).
Proof. clear3.
pose proof derived_rangesR as (D1 & D2 & _ & _ & D5 & D6 & _ & D8 & _ & _ & _ & _ & _ & _ & _ & _ & D17 & D18 & _).
pose proof high_factsR as (F1 & F2 & _ & _ & F5 & _). pose proof Hsp as (Hlo & Hhi & _). pose proof stack_ivsR as (SI & _ & _ & SI4).
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINU, WINR0, TABW. unfold Pr, RGv in *. try unfold T in *. try unfold SB in *. try unfold sp0 in *. numconst. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END.
assert (NRG : forall a, ly_T ly <= a < ly_T ly + 4096 -> ~ (ly_space ly + 137438953472 + 128 * c <= a < ly_space ly + 137438953472 + 128 * c + 128))
by (clear - D8 D17 F5 PT; intros a Ha X; zlia).
assert (NST : forall a, ly_T ly <= a < ly_T ly + 4096 -> ~ (bv_unsigned (getr regs0 2) - 1024 <= a < bv_unsigned (getr regs0 2))) by (clear - SI; intros a Ha X; zlia).
clear D8 D17 F5 PT SI.
split; [|split; [|split; [|split]]].
- intros a Ha [X|[X|[X|X]]]; [exact (NST a ltac:(clear - Ha; zlia) X) | exact (NRG a ltac:(clear - Ha; zlia) X) | clear - Ha X; zlia | clear - Ha X; zlia].
- intros a Ha. split.
+ intros [X|[X|[X|X]]]; [exact (NST a ltac:(clear - Ha HcR; zlia) X) | exact (NRG a ltac:(clear - Ha HcR; zlia) X) | clear - Ha X HcR; zlia | clear - Ha X HcR; zlia].
+ intros (j & Hj & Hr). clear - Ha Hj Hr HcR. assert (j < c \/ j = c \/ c < j) by zlia. zlia.
- intros i a Hi Hic Ha. intros [X|[X|[X|[X|X]]]]; [exact (NST a ltac:(clear - Ha Hi; zlia) X) | | exact (NRG a ltac:(clear - Ha Hi; zlia) X) | clear - Ha Hi X; zlia | clear - Ha Hi X; zlia].
clear - Hi Hic Ha X. assert (i < c \/ c < i) by zlia. zlia.
- intros a [[X|[X|[X|X]]]|[(j & Hj & Hr)|X]]; [clear - X Usp SI4; zlia | clear - X D5 D6; zlia | clear - X F1 F2; zlia | clear - X F1 F2; zlia | clear - Hj Hr F1 F2; zlia | clear - X F1 F2 HcR; zlia].
- clear - D1 D2 F1 F2 HcR. zlia.
Qed.
Lemma segU : forall mat,
(forall a, T <= a < T + kThreadObjSize -> apresent (w_H W) mem0 a) ->
all_disjoint E0 (YP09.mkRegion (Some rT) 292 2704 0 0 []) (dropAt 35 REG0X) ->
st_ok tfibsegs E0 SSU (restrict (w_H W) (mkst regs0 (w64 0x367e0) mem0 (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs0 (w64 0x367e0) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) POSTU.
Proof.
intros mat HTP HSPAN HS. pose proof Hwx_tfa as Hwx.
pose proof sepU as (Zspan & Zcnt & Ztab & Z64 & (P0 & P16 & EPr & TI & TE)).
pose proof class_facts as (CF1 & CF2 & CF3 & CF4 & CF5).
assert (HEn0 : forall k, (k < HAVJ)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
assert (ET : bv_unsigned (ew E0 32) = T) by (rewrite EaT; unfold w64; apply unsigned_lit_small; clear - TI TE; numconst; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in TI; zlia).
assert (EP : bv_unsigned (ew E0 37) = Pr) by (rewrite EaP; unfold w64; apply unsigned_lit_small; clear - P0 P16; zlia).
assert (HDJ : all_disjoint E0 headc0 (dropAt 35 REG0X)).
{ pose proof (st_ok_mem_ok tfibsegs E0 SSU _ HS) as (_ & _ & PW). cbn [ss_mem SSU] in PW.
change (dropAt 35 REG0X) with (dropAt 35 REG0U). apply (pairwise_disjoint_pick E0 REG0U 35 headc0 PW). vm_compute. reflexivity. }
srr_run_to_sh tfibtbl_rtA_ok HS 0x3683c.
match type of HS with st_ok _ _ ?ss (restrict _ ?msx) => change ss with SU1 in HS; set (m1 := ms_mem msx) in *; rename msx into ms1 end.
assert (MEQ1 : forall x : word, ~ WINU (bv_unsigned x) -> m1 x = mem0 x)
by (intros x Hx; exact (frame_WINU E0 (ss_mem SSU) _ _ HEn0 ltac:(vm_compute; reflexivity) HF x Hx)).
clear HF HFr.
assert (PRES1 : forall a, T <= a < T + kThreadObjSize -> ~ WINU a -> apresent (w_H W) m1 a).
{ intros a Ha Hw. apply (apresent_same (w_H W) mem0); [| exact (HTP a Ha)]. apply MEQ1. rewrite unsigned_lit_small; [exact Hw|]. clear - Ha TI TE. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in TI. zlia. }
assert (HS2 : st_ok tfibsegs E0 SU2 (restrict (w_H W) ms1)).
{ rewrite SU2_eq. apply (st_ok_mem_surgery E0 SU1 (restrict (w_H W) ms1) _ HS). cbn [ms_mem restrict]. fold m1. intros HM.
apply mem_ok_app.
- eapply (mem_ok_replAt E0 _ _ 35 headc0 headcnt HM SU1_35).
+ unfold subregion, headcnt, headc0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [zlia|]. split; [zlia|]. split; [left; zlia|]. intros ch Hch. destruct Hch as [<-|[]]. left. reflexivity.
+ reflexivity.
- exact TBLS0_wf.
- apply TBLS0_ok; unfold rT; [rewrite ET; clear - TI TE; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in TI; zlia | rewrite ET; clear - TI TE; numconst; zlia |].
intros a Ha. unfold rT in Ha. rewrite ET in Ha. apply apresent_writable_off; [off_by ltac:(clear - Ha TI TE; numconst; zlia) |].
apply PRES1; [clear - Ha; numconst; zlia | exact (Zspan a Ha)].
- apply TBLS0_pairwise.
- intros r Hr. apply (all_disjoint_replAt E0 r 35 headcnt (ss_mem SU1)); [rewrite SU1_len; zlia | |].
+ apply extent_disjoint_sym. exact (all_disjoint_In E0 headcnt TBLS0 r headcnt_TBLS0 Hr).
+ apply (TBLS0_disjoint E0 r _ Hr). exact (all_disjoint_ext3 E0 _ _ _ (eq_sym SU1_ext) HSPAN). }
clear HS. rename HS2 into HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x368d8.
match type of HS with st_ok _ _ ?ss (restrict _ ?msx) => change ss with SU3 in HS; set (m3 := ms_mem msx) in *; rename msx into ms3 end.
assert (MEQ3 : forall x : word, ~ WINU (bv_unsigned x) -> ~ TABW T (bv_unsigned x) -> m3 x = m1 x).
{ intros x Hx Ht. apply HF. rewrite SU2_eq. cbn [ss_mem]. intros Hw. apply in_wrange_app in Hw as [Hw|Hw].
- exact (Hx (windows_WINU E0 (replAt 35 headcnt (ss_mem SU1)) _ HEn0 ltac:(vm_compute; reflexivity) Hw)).
- apply Ht. pose proof (in_wrange_TBLS0 E0 _ Hw) as Hw'. cbn [base_val] in Hw'. unfold rT in Hw'. rewrite ET in Hw'. exact Hw'. }
clear HF HFr.
pose proof (st_ok_mem_ok tfibsegs E0 SU3 _ HS) as HM3. cbn [ms_mem restrict] in HM3. fold m3 in HM3. rewrite SU3_split in HM3.
pose proof (mem_ok_TBLSF E0 _ _ HM3) as TBF. unfold rT in TBF. rewrite ET in TBF.
assert (CNT : val_mem tfibsegs (mrestrict (w_H W) m3) Pr 4 0).
{ rewrite <- (Z.add_0_r Pr), <- EP. eapply (chunk_val_at (w_H W) E0 SU3 _ 35 0 _ _ 4%N _ 0 _ HS); [exact SU3_35 | reflexivity | reflexivity | reflexivity | cbn; zlia | cbn; zlia]. }
assert (HS4 : st_ok tfibsegs E0 SU4 (restrict (w_H W) ms3)).
{ rewrite SU4_eq. apply (st_ok_mem_surgery E0 SU3 (restrict (w_H W) ms3) _ HS). cbn [ms_mem restrict]. fold m3. intros _.
rewrite (replAt_insAt 35 headcJ _ ltac:(rewrite SU3_len; zlia)). apply mem_ok_insAt.
- apply mem_ok_dropAt. exact (mem_ok_app_l E0 _ _ _ HM3).
- reflexivity.
-
unfold region_ok, headcJ. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold rP. rewrite EP.
split; [clear - P0; zlia|]. split; [clear - P16; zlia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 4) as [Ho4|Ho4].
- apply apresent_writable_off; [off_by ltac:(clear - Ho P0 P16 EPr TI HcR; numconst; zlia) |]. destruct (Zcnt (Pr + o) ltac:(clear - Ho Ho4; zlia)) as [Hw Ht].
apply (apresent_same (w_H W) m1); [| apply PRES1; [clear - Ho Ho4 EPr HcR; numconst; zlia | exact Hw]].
apply MEQ3; rewrite unsigned_lit_small by (clear - Ho P0 P16; zlia); [exact Hw | exact Ht].
- replace (Pr + o) with (T + 212 + 80 * c + (o - 4)) by (clear - Ho EPr; zlia). apply (proj2 (TBF c HcR)). clear - Ho Ho4; zlia. }
pose proof (proj1 (TBF c HcR)) as [TM TSZ].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_r; exact CNT].
+ eapply chunk_ok_val; [cbn [sv_denot]; unfold rMAX; rewrite EaMAX, Hmax; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; reflexivity
| pose proof (max_cached_range c HcR); cbn; zlia | cbn; zlia |].
replace (Pr + 4) with (T + 212 + 80 * c) by (clear - EPr; zlia). exact TM.
+ eapply chunk_ok_val; [cbn [sv_denot]; unfold rCSZ; rewrite EaCSZ, Hcsz; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; reflexivity
| rewrite <- Hcsz; cbn; clear - CF4; numconst; zlia | cbn; zlia |].
replace (Pr + 8) with (T + 216 + 80 * c) by (clear - EPr; zlia). exact TSZ.
- apply (all_disjoint_head_ext3 E0 headc0 headcJ); [reflexivity|]. exact (all_disjoint_ext3 E0 _ _ _ (eq_sym SU3_ext) HDJ). }
clear HS. rename HS4 into HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x36800.
match type of HS with st_ok _ _ ?ss (restrict _ ?msx) => change ss with SU5 in HS; set (m5 := ms_mem msx) in *; rename msx into ms5 end.
assert (MEQ5 : forall x : word, ~ WINR0 (bv_unsigned x) -> m5 x = m3 x)
by (intros x Hx; exact (frame_WINR0 E0 (ss_mem SU4) _ _ HEn0 ltac:(vm_compute; reflexivity) HF x Hx)).
clear HF HFr.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists ms' mt E', mkCfg _ (with_vm_backing _ ?matx _) = _ /\ _ => exists ms5, matx, (havoc E0 hJ0 (map (getr (ms_regs ms5)) CLOB_INIT)) end.
split; [subst m5; reflexivity|].
split; [exact (env_agree_havoc_ge HAVJ hJ0 E0 E0 _ ltac:(unfold hJ0; zlia) (env_agree_refl HAVJ E0))|].
split.
{ pose proof (st_ok_forget hJ0 E0 SU5 (w_H W) ms5 CLOB_INIT HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as X'.
rewrite <- (st_ok_restrict_mkst tfibsegs (w_H W) E0 SU5 ms5 HS eq_refl) in X'.
apply (st_ok_prune _ _ _ _ [] []) in X'. rewrite <- SUJ. unfold noconds, forget. exact X'. }
assert (MEQ : forall x : word, ~ WINR0 (bv_unsigned x) -> ~ TABW T (bv_unsigned x) -> m5 x = mem0 x).
{ intros x Hx Ht. rewrite (MEQ5 x Hx). assert (Hu : ~ WINU (bv_unsigned x)) by (intros Hu; exact (Hx (WINU_WINR0 _ Hu))).
rewrite (MEQ3 x Hu Ht). exact (MEQ1 x Hu). }
split; [subst m5; exact MEQ|].
split.
{   intros a Ha. pose proof Hsp as (Hlo & Hhi & Hal). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof high_factsR as LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha; numconst; try unfold sp0 in *; zlia
| off_by ltac:(pose proof stack_ivsR as SI; clear - Ha Hlo Hhi LF Usp T7 SI; numconst; try unfold sp0 in *; zlia) ]. }
assert (OWN : forall o, 4 <= o < 16 -> apresent (w_H W) m5 (Pr + o)).
{ intros o Ho. eapply (st_ok_window_apresent_off (w_H W) E0 SU5 _ 35 _ (Pr + o) HS); [vm_compute; reflexivity | | off_by ltac:(clear - Ho P0 P16 EPr TI HcR; numconst; zlia) ].
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite EP. clear - Ho. zlia. }
assert (OTH : forall i a, 1 <= i <= 31 -> i <> c -> T + 212 + 80 * i <= a < T + 224 + 80 * i -> m5 (Z_to_bv 64 a) = m3 (Z_to_bv 64 a)).
{ intros i a Hi Hic Ha. apply MEQ5. rewrite unsigned_lit_small; [exact (Ztab i a Hi Hic Ha)|]. apply Z64. right. left. exists i. split; [exact Hi | exact Ha]. }
split.
{ intros i Hi. destruct (Z.eq_dec i c) as [->|Hic].
- split.
+ replace (T + 212 + 80 * c) with (bv_unsigned (ew E0 37) + 4) by (clear - EP EPr; rewrite EP; zlia).
eapply (chunk_val_at (w_H W) E0 SU5 _ 35 1 _ _ 4%N _ (max_cached c) _ HS); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity
| cbn [sv_denot]; unfold rMAX; rewrite EaMAX, Hmax; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; reflexivity | pose proof (max_cached_range c HcR); cbn; zlia | cbn; zlia].
+ replace (T + 216 + 80 * c) with (bv_unsigned (ew E0 37) + 8) by (clear - EP EPr; rewrite EP; zlia).
eapply (chunk_val_at (w_H W) E0 SU5 _ 35 2 _ _ 8%N _ (class_size c) _ HS); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity
| cbn [sv_denot]; unfold rCSZ; rewrite EaCSZ, Hcsz; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; reflexivity | rewrite <- Hcsz; cbn; clear - CF4; numconst; zlia | cbn; zlia].
- destruct (proj1 (TBF i Hi)) as [TM TSZ]. split.
+ eapply val_mem_frame; [|exact TM]. intros k Hk. apply (OTH i); [exact Hi | exact Hic | clear - Hk; zlia].
+ eapply val_mem_frame; [|exact TSZ]. intros k Hk. apply (OTH i); [exact Hi | exact Hic | clear - Hk; zlia]. }
intros a (i & Hi & Ha). destruct (Z.eq_dec i c) as [->|Hic].
- replace a with (Pr + (a - Pr)) by zlia. apply OWN. clear - Ha EPr. zlia.
- apply (apresent_same (w_H W) m3); [exact (OTH i a Hi Hic Ha)|].
apply writable_off_apresent; [off_by ltac:(clear - Ha Hi TI TE; numconst; zlia) |].
replace a with (T + 212 + 80 * i + (a - (T + 212 + 80 * i))) by zlia. apply (proj2 (TBF i Hi)). clear - Ha. zlia.
Qed.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AF0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFl1 AFhy AFis AFkp AFk6 AFk5 AFhz AFk8 AFk7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFk4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFk3 AB1q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhm AFka AFi3 AFk9 AFkk AFkb AFkc AFkd AFke AFkf AFkg AFkh AFki AFkj AFkm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0b YG0h YG0o YG08 YK0v YA05 YA09 YG0j YG0c YG0i YG0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0g.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
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
Section g.
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
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Local Abbreviation rdn_of_presentR := (@AFk5.rdn_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation store_ok_of_presentR := (@AFk5.store_ok_of_presentR ly regs0 maxc mf au mu Hmf Hmu).
Local Abbreviation cpy4_stretch := (@AFk5.cpy4_stretch _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Local Abbreviation facts3 := (@AFk5.facts3 _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation RFACTS3 := (@AFk5.RFACTS3 ly regs0 c).
Local Abbreviation tail_ext_ok3 := (@AFk5.tail_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation stack_ext_ok3 := (@AFk5.stack_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation scratch_headed := (@AFk5.scratch_headed).
Local Abbreviation mem_ok_scratch_present := (@AFk5.mem_ok_scratch_present _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY Hmf Hmu Hsp).
Local Abbreviation at_R3_run := (@AFk5.at_R3_run _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_run_ecall := (@AFk5.at_R3_run_ecall _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_pin := (@AFk5.at_R3_pin _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_arm := (@AFk5.at_R3_arm _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_forget := (@AFk5.at_R3_forget _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_noconds := (@AFk5.at_R3_noconds _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_weaken := (@AFk5.at_R3_weaken _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_facts := (@AFk5.at_R3_facts _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_strengthen := (@AFk5.at_R3_strengthen _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_eq := (@AFk5.at_R3_eq _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation CSAVED := (@AFk5.CSAVED).
Local Abbreviation sv_denot_SOff0 := (@AFk5.sv_denot_SOff0).
Local Abbreviation at_R3_ret := (@AFk5.at_R3_ret _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp).
Local Abbreviation at_N3_cont := (@AFk5.at_N3_cont _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation memset_stretch3 := (@AFk5.memset_stretch3 _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
Local Abbreviation nth_Z_to_le_bytes4 := (@AFk5.nth_Z_to_le_bytes4).
Local Abbreviation popfree_stretch := (@AFk5.popfree_stretch _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
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
Local Abbreviation Pr_is := (@AFk5.Pr_is ly c).
Local Abbreviation RGv_is := (@AFk5.RGv_is ly c).
Local Abbreviation FAv_is := (@AFk5.FAv_is ly c HcR).
Local Abbreviation RBv_is := (@AFk5.RBv_is ly c HcR).
Local Abbreviation cls_wfR := (@AFkk.cls_wfR _ W ly mem0 c HcR B S HARm Hinited).
Local Abbreviation cls_wf0 := (@AFkk.cls_wf0 _ W ly mem0 c HcR B S HARm).
Local Abbreviation reg_facts0 := (@AFkk.reg_facts0 _ W ly regs0 mem0 c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_facts := (@AFkk.reg_facts _ W ly regs0 mem0 c maxc nf mf au mu HcR Hmax Hsp B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (@AFkk.Hnf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmf' := (@AFkk.Hmf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmu' := (@AFkk.Hmu' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hcarved' := (@AFkk.Hcarved' _ W ly mem0 c au mu HcR B S HARm Hau_def Hmu_def).
Local Abbreviation Hau_al' := (@AFkk.Hau_al' _ W ly mem0 c au csz HcR Hcsz B S HARm Hau_def).
Local Abbreviation vis_present := (@AFkk.vis_present _ W ly regs0 mem0 maxc B S HARm).
Local Abbreviation thread_present := (@AFkk.thread_present _ W ly regs0 mem0 c maxc nf mf au mu csz IMG LY HcR Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation rinfo_present := (@AFkk.rinfo_present _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HslotPres' := (@AFkk.HslotPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HfaPres' := (@AFkk.HfaPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation word_of_present := (@AFkk.word_of_present W ly regs0 mem0 maxc).
Local Abbreviation val_mem_lo4 := (@AFkk.val_mem_lo4 ly regs0 maxc).
Local Abbreviation junk_valuesR := (@AFkk.junk_valuesR _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation cell_sym := (@AFkk.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@AFkk.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@AFkk.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_cache := (@AFkk.In_acells_cache ly regs0 c maxc HcR B S).
Local Abbreviation In_acells_region := (@AFkk.In_acells_region ly regs0 c maxc HcR B S).
Local Abbreviation cache_valsR := (@AFkk.cache_valsR _ W ly regs0 mem0 c maxc csz HcR Hmax Hcsz B S HARm Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@AFkk.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (@AFkk.cache_valsU _ W ly regs0 mem0 maxc B S HARm).
Local Abbreviation region_valsR := (@AFkk.region_valsR _ W ly regs0 mem0 c maxc nf mf au mu HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation chunk_lit := (@AFkk.chunk_lit W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_lit_at := (@AFkk.chunk_lit_at W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_atom := (@AFkk.chunk_atom W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation REG0R3_ok_but35 := (@AFkk.REG0R3_ok_but35 _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0R3_ok := (@AFkk.REG0R3_ok _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation REG0U3_ok := (@AFkk.REG0U3_ok _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSR3_ok := (@AFkk.PAIRSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SPAN3_disj := (@AFkk.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation FACTSR3_ok := (@AFkk.FACTSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation SEEDR3_ok := (@AFkk.SEEDR3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PAIRSU3_ok := (@AFkk.PAIRSU3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEEDU3_ok := (@AFkk.SEEDU3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v).
Local Abbreviation PT := (@AFkb.PT).
Local Abbreviation pstable_PT := (@AFkb.pstable_PT ly regs0 c).
Local Abbreviation WX0 := (@AFkb.WX0 ly regs0 c).
Local Abbreviation at_R3_init := (@AFkb.at_R3_init _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug mat0 msJ SEEDJ).
Local Abbreviation seg3J := (@AFkb.seg3J _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hpres0R).
Local Abbreviation land_hi0 := (@AFkb.land_hi0).
Local Abbreviation seg3P := (@AFkb.seg3P _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug mat0 msJ SEEDJ).
Local Abbreviation T16 := (@AFkb.T16).
Local Abbreviation TMID := (@AFkb.TMID).
Local Abbreviation U_csz := (@AFkb.U_csz ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation U_csz31 := (@AFkb.U_csz31 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug Hcsz).
Local Abbreviation U_csz16 := (@AFkb.U_csz16 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hcsz Hmf Hmu).
Local Abbreviation U_cszmid := (@AFkb.U_cszmid ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hcsz).
Local Abbreviation U_tot_of := (@AFkb.U_tot_of _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation U_tot31 := (@AFkb.U_tot31 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation U_rb := (@AFkb.U_rb _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation seg3Q31 := (@AFkb.seg3Q31 _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Q16 := (@AFkb.seg3Q16 _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Qmid := (@AFkb.seg3Qmid _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation U_mu := (@AFkb.U_mu ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug Hmf Hmu).
Local Abbreviation U_tot := (@AFkb.U_tot _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Q_map := (@AFkb.seg3Q_map _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3Q_ok := (@AFkb.seg3Q_ok _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3M := (@AFkb.seg3M _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3_Ur := (@AFkc.seg3_Ur _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation seg3_URg := (@AFkc.seg3_URg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp).
Local Abbreviation seg3_Ug := (@AFkc.seg3_Ug _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation P_ush := (@AFkc.P_ush sha).
Local Abbreviation pstable_ush := (@AFkc.pstable_ush _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation seg3_Ums := (@AFkc.seg3_Ums _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation XCOND_e := (@AFkd.XCOND_e mu tot).
Local Abbreviation MUX_e := (@AFkd.MUX_e mu).
Local Abbreviation factsX_e := (@AFkd.factsX_e _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segC1_e := (@AFkd.segC1_e _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segC2e_e := (@AFkd.segC2e_e _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segC2g_e := (@AFkd.segC2g_e _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segD_r_e := (@AFkd.segD_r_e _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation segD_rg_e := (@AFkd.segD_rg_e _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp).
Local Abbreviation segD_g_e := (@AFkd.segD_g_e _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation P_fsh_e := (@AFkd.P_fsh_e shf).
Local Abbreviation pstable_fsh_e := (@AFkd.pstable_fsh_e _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segD_ms_e := (@AFkd.segD_ms_e _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation XCOND_g := (@AFke.XCOND_g mu tot).
Local Abbreviation MUX_g := (@AFke.MUX_g mu).
Local Abbreviation factsX_g := (@AFke.factsX_g _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segC1_g := (@AFke.segC1_g _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segC2e_g := (@AFke.segC2e_g _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segC2g_g := (@AFke.segC2g_g _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segD_r_g := (@AFke.segD_r_g _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation segD_rg_g := (@AFke.segD_rg_g _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp).
Local Abbreviation segD_g_g := (@AFke.segD_g_g _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation P_fsh_g := (@AFke.P_fsh_g shf).
Local Abbreviation pstable_fsh_g := (@AFke.pstable_fsh_g _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segD_ms_g := (@AFke.segD_ms_g _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation XCOND_ee := (@AFkf.XCOND_ee mu tot).
Local Abbreviation MUX_ee := (@AFkf.MUX_ee mu).
Local Abbreviation MFY_ee := (@AFkf.MFY_ee mf).
Local Abbreviation YCOND_ee := (@AFkf.YCOND_ee mf nfe).
Local Abbreviation SRC3_ee := (@AFkf.SRC3_ee ly c n nfe).
Local Abbreviation factsX_ee := (@AFkf.factsX_ee _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation factsY_ee := (@AFkf.factsY_ee _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation val_mem_frame_ee := (@AFkf.val_mem_frame_ee).
Local Abbreviation P_fill_ee := (@AFkf.P_fill_ee ly c au csz nce nfe).
Local Abbreviation pstable_fill_ee := (@AFkf.pstable_fill_ee _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE1_ee := (@AFkf.segE1_ee _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE2_ee := (@AFkf.segE2_ee _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation P_cpy_ee := (@AFkf.P_cpy_ee ly c n nfe).
Local Abbreviation pstable_cpy_ee := (@AFkf.pstable_cpy_ee _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE3_ee := (@AFkf.segE3_ee _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE4_ee := (@AFkf.segE4_ee _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation XCOND_eg := (@AFkg.XCOND_eg mu tot).
Local Abbreviation MUX_eg := (@AFkg.MUX_eg mu).
Local Abbreviation MFY_eg := (@AFkg.MFY_eg mf).
Local Abbreviation YCOND_eg := (@AFkg.YCOND_eg mf nfe).
Local Abbreviation SRC3_eg := (@AFkg.SRC3_eg ly c n nfe).
Local Abbreviation factsX_eg := (@AFkg.factsX_eg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation factsY_eg := (@AFkg.factsY_eg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation val_mem_frame_eg := (@AFkg.val_mem_frame_eg).
Local Abbreviation P_fill_eg := (@AFkg.P_fill_eg ly c au csz nce nfe).
Local Abbreviation pstable_fill_eg := (@AFkg.pstable_fill_eg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE1_eg := (@AFkg.segE1_eg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE2_eg := (@AFkg.segE2_eg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation P_cpy_eg := (@AFkg.P_cpy_eg ly c n nfe).
Local Abbreviation pstable_cpy_eg := (@AFkg.pstable_cpy_eg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE3_eg := (@AFkg.segE3_eg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE4_eg := (@AFkg.segE4_eg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation XCOND_ge := (@AFkh.XCOND_ge mu tot).
Local Abbreviation MUX_ge := (@AFkh.MUX_ge mu).
Local Abbreviation MFY_ge := (@AFkh.MFY_ge mf).
Local Abbreviation YCOND_ge := (@AFkh.YCOND_ge mf nfg).
Local Abbreviation SRC3_ge := (@AFkh.SRC3_ge ly c n nfg).
Local Abbreviation factsX_ge := (@AFkh.factsX_ge _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation factsY_ge := (@AFkh.factsY_ge _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation val_mem_frame_ge := (@AFkh.val_mem_frame_ge).
Local Abbreviation P_fill_ge := (@AFkh.P_fill_ge ly c au csz ncg nfg).
Local Abbreviation pstable_fill_ge := (@AFkh.pstable_fill_ge _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE1_ge := (@AFkh.segE1_ge _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE2_ge := (@AFkh.segE2_ge _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation P_cpy_ge := (@AFkh.P_cpy_ge ly c n nfg).
Local Abbreviation pstable_cpy_ge := (@AFkh.pstable_cpy_ge _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE3_ge := (@AFkh.segE3_ge _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE4_ge := (@AFkh.segE4_ge _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation XCOND_gg := (@AFki.XCOND_gg mu tot).
Local Abbreviation MUX_gg := (@AFki.MUX_gg mu).
Local Abbreviation MFY_gg := (@AFki.MFY_gg mf).
Local Abbreviation YCOND_gg := (@AFki.YCOND_gg mf nfg).
Local Abbreviation SRC3_gg := (@AFki.SRC3_gg ly c n nfg).
Local Abbreviation factsX_gg := (@AFki.factsX_gg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation factsY_gg := (@AFki.factsY_gg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation val_mem_frame_gg := (@AFki.val_mem_frame_gg).
Local Abbreviation P_fill_gg := (@AFki.P_fill_gg ly c au csz ncg nfg).
Local Abbreviation pstable_fill_gg := (@AFki.pstable_fill_gg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE1_gg := (@AFki.segE1_gg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE2_gg := (@AFki.segE2_gg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation P_cpy_gg := (@AFki.P_cpy_gg ly c n nfg).
Local Abbreviation pstable_cpy_gg := (@AFki.pstable_cpy_gg _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE3_gg := (@AFki.segE3_gg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation segE4_gg := (@AFki.segE4_gg _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation fr := (@AFkj.fr c S).
Local Abbreviation hol := (@AFkj.hol c S).
Local Abbreviation len_facts3 := (@AFkj.len_facts3 _ W ly mem0 c HcR B S HARm).
Local Abbreviation reg_S := (@AFkj.reg_S c nf mf au mu S Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_upd3 := (@AFkj.reg_upd3 _ W ly mem0 c HcR B S HARm).
Local Abbreviation cache_upd3 := (@AFkj.cache_upd3 _ W ly mem0 c HcR B S HARm).
Local Abbreviation PM3 := (@AFkj.PM3 _ W ly mem0 c maxc HcR Hmax B S HARm Hinited).
Local Abbreviation WF1 := (@AFkj.WF1 _ W ly mem0 B S HARm).
Local Abbreviation rUp := (@AFkj.rUp c mf au mu mu2 S).
Local Abbreviation rUm := (@AFkj.rUm c mf au mu S).
Local Abbreviation SUp := (@AFkj.SUp c mf au mu mu2 S).
Local Abbreviation SUm := (@AFkj.SUm c mf au mu S).
Local Abbreviation MU1 := (@AFkj.MU1 mu mu2).
Local Abbreviation HO1 := (@AFkj.HO1 c mu S).
Local Abbreviation NC1 := (@AFkj.NC1 nce ncg).
Local Abbreviation NF1 := (@AFkj.NF1 nfe nfg).
Local Abbreviation AU1 := (@AFkj.AU1 aue aug).
Local Abbreviation rg1 := (@AFkj.rg1 c mf au mu mu2 S).
Local Abbreviation St1 := (@AFkj.St1 c mf au mu mu2 S).
Local Abbreviation rFp := (@AFkj.rFp c mf au mu mu2 mf2 S).
Local Abbreviation rFm := (@AFkj.rFm c mf au mu mu2 S).
Local Abbreviation SFp := (@AFkj.SFp c mf au mu mu2 mf2 S).
Local Abbreviation SFm := (@AFkj.SFm c mf au mu mu2 S).
Local Abbreviation MF2 := (@AFkj.MF2 mf mf2).
Local Abbreviation HO2 := (@AFkj.HO2 c mf mu S).
Local Abbreviation rg2 := (@AFkj.rg2 c mf au mu mu2 mf2 S).
Local Abbreviation St2 := (@AFkj.St2 c mf au mu mu2 mf2 S).
Local Abbreviation rP := (@AFkj.rP c mf au mu mu2 nce ncg mf2 aue aug S).
Local Abbreviation rQ := (@AFkj.rQ c mf mu mu2 mf2 aue aug S).
Local Abbreviation SQ := (@AFkj.SQ c maxc mf mu mu2 mf2 aue aug S).
Local Abbreviation S1_eq := (@AFkj.S1_eq _ W ly mem0 c nf mf au mu mu2 HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_S1 := (@AFkj.reg_S1 _ W ly mem0 c nf mf au mu mu2 HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation S2_eq := (@AFkj.S2_eq _ W ly mem0 c nf mf au mu mu2 mf2 HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_S2 := (@AFkj.reg_S2 _ W ly mem0 c nf mf au mu mu2 mf2 HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation upd_S1 := (@AFkj.upd_S1 _ W ly mem0 c nf mf au mu mu2 HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation upd_S2 := (@AFkj.upd_S2 _ W ly mem0 c nf mf au mu mu2 mf2 HcR B S HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation XC3 := (@AFkj.XC3 mu tot).
Local Abbreviation factsX3 := (@AFkj.factsX3 _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation round_user := (@AFkj.round_user _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation round_fa := (@AFkj.round_fa _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation runs_ok_new := (@AFkj.runs_ok_new _ W ly regs0 mem0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm).
Local Abbreviation pop_new := (@AFkj.pop_new _ W ly regs0 mem0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hnf_def).
Local Abbreviation E_mmu_e := (@AFkj.E_mmu_e c nf mf au mu csz need tot Hcsz Htot S Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation E_mmu_g := (@AFkj.E_mmu_g _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug S Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation E_mmu_fail := (@AFkj.E_mmu_fail _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug S Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation E_efa_e := (@AFkj.E_efa_e c mf au mu tot mu2 nfe nfg S).
Local Abbreviation E_efa_g := (@AFkj.E_efa_g _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug S).
Local Abbreviation E_efa_fail := (@AFkj.E_efa_fail _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug S).
Local Abbreviation E_tail := (@AFkj.E_tail _ W ly regs0 mem0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hnf_def).
Local Abbreviation E_tree := (@AFkj.E_tree _ W ly mem0 c maxc n nf need HcR Hmax Hn Hnlt Hneed B S HARm Hinited Hchunks Hnf_def).
Local Abbreviation E_pop := (@AFkj.E_pop c need S).
Local Abbreviation E_getreg1 := (@AFkj.E_getreg1 _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug S Hnf_def).
Local Abbreviation reg_e := (@AFkj.reg_e c nf mf au mu mu2 S Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_g := (@AFkj.reg_g _ W ly mem0 c mf au mu mu2 HcR B S HARm).
Local Abbreviation upd_e := (@AFkj.upd_e c S).
Local Abbreviation upd_g := (@AFkj.upd_g c mf au mu mu2 S).
Local Abbreviation reg_ee := (@AFkj.reg_ee c nf mf au mu mu2 mf2 S Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_ge := (@AFkj.reg_ge _ W ly mem0 c mf au mu mu2 mf2 HcR B S HARm).
Local Abbreviation reg_xg := (@AFkj.reg_xg _ W ly mem0 c mf au mu mu2 mf2 HcR B S HARm).
Local Abbreviation upd_xg := (@AFkj.upd_xg c mf au mu mu2 mf2 S).
Local Abbreviation zrange_dec := (@AFkm.zrange_dec).
Local Abbreviation apresent_word := (@AFkm.apresent_word).
Local Abbreviation val_mem_cell := (@AFkm.val_mem_cell ly B).
Local Abbreviation val_mem_at := (@AFkm.val_mem_at).
Local Abbreviation nth_error_run_elems := (@AFkm.nth_error_run_elems).
Local Abbreviation fa_nth_elems := (@AFkm.fa_nth_elems).
Local Abbreviation in_combine_seq := (@AFkm.in_combine_seq).
Local Abbreviation flat_map_ext_in := (@AFkm.flat_map_ext_in).
Local Abbreviation nth_error_rev := (@AFkm.nth_error_rev).
Local Abbreviation AU := (@AFkm.AU au csz).
Local Abbreviation NF' := (@AFkm.NF' nf).
Local Abbreviation NT := (@AFkm.NT).
Local Abbreviation rG := (@AFkm.rG au csz).
Local Abbreviation SG := (@AFkm.SG c maxc au csz S).
Local Abbreviation len_factsG := (@AFkm.len_factsG _ W ly mem0 c HcR B S HARm).
Local Abbreviation SG_parts := (@AFkm.SG_parts _ W ly mem0 c maxc au csz HcR B S HARm).
Local Abbreviation SG_sec_extents := (@AFkm.SG_sec_extents ly c maxc au csz S).
Local Abbreviation W_FEn := (@AFkm.W_FEn ly c nf).
Local Abbreviation XC := (@AFkm.XC ly c nf adr sha mu2 fadr shf mf2).
Local Abbreviation geo := (@AFkm.geo _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation AGREE0 := (@AFkm.AGREE0 W ly regs0 mem0 c nf adr sha mu2 fadr shf mf2).
Local Abbreviation AGX := (@AFkm.AGX _ W ly regs0 mem0 md0 c nf adr sha mu2 fadr shf mf2 Hsp B S HAR).
Local Abbreviation XC_where := (@AFkm.XC_where _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_img := (@AFkm.Z_img _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_band := (@AFkm.Z_band _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_T := (@AFkm.Z_T _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_prim := (@AFkm.Z_prim _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_high := (@AFkm.Z_high _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_out := (@AFkm.Z_out _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_ext := (@AFkm.Z_ext _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation Z_sec := (@AFkm.Z_sec _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HAR).
Local Abbreviation Z_user := (@AFkm.Z_user _ W ly regs0 mem0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmu_def).
Local Abbreviation UW_uncommitted := (@AFkm.UW_uncommitted _ W ly regs0 mem0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmu_def).
Local Abbreviation FW_uncommitted := (@AFkm.FW_uncommitted _ W ly regs0 mem0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmf_def).
Local Abbreviation VIS_MONO := (@AFkm.VIS_MONO W mem0 mf mu adr fadr).
Local Abbreviation apresent_vis := (@AFkm.apresent_vis).
Local Abbreviation aview_copy := (@AFkm.aview_copy).
Local Abbreviation vis_keep := (@AFkm.vis_keep _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmf_def Hmu_def HAR).
Local Abbreviation loc_ok := (@AFkm.loc_ok ly c nf adr sha mu2 fadr shf mf2).
Local Abbreviation keep_cells := (@AFkm.keep_cells _ W ly regs0 mem0 md0 c nf adr sha mu2 fadr shf mf2 Hsp B S HAR).
Local Abbreviation keep_cell := (@AFkm.keep_cell _ W ly regs0 mem0 md0 c nf adr sha mu2 fadr shf mf2 Hsp B S HAR).
Local Abbreviation PCv := (@AFkm.PCv ly c maxc nf au csz).
Local Abbreviation PRW := (@AFkm.PRW ly c maxc nf au csz).
Local Abbreviation EL := (@AFkm.EL c au csz S).
Local Abbreviation EL_len := (@AFkm.EL_len _ W ly mem0 c nf au csz HcR B S HARm Hinited Hnf_def).
Local Abbreviation entry_rd := (@AFkm.entry_rd _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR).
Local Abbreviation cells_regions := (@AFkm.cells_regions _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm HAR).
Local Abbreviation slot_cell := (@AFkm.slot_cell _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR).
Local Abbreviation cells_caches := (@AFkm.cells_caches _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR).
Local Abbreviation cells_chunks := (@AFkm.cells_chunks _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmu_def HAR).
Local Abbreviation cells_sec := (@AFkm.cells_sec _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HARm HAR).
Local Abbreviation keep_batches := (@AFkm.keep_batches _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmu_def HAR).
Local Abbreviation cells_quar := (@AFkm.cells_quar _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HARm Hmu_def HAR).
Local Abbreviation cells_fs := (@AFkm.cells_fs _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm HAR).
Local Abbreviation cells_depot := (@AFkm.cells_depot _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HARm HAR).
Local Abbreviation cells_ialloc := (@AFkm.cells_ialloc _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HARm HAR).
Local Abbreviation cells_thread := (@AFkm.cells_thread _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HAR).
Local Abbreviation cells_final := (@AFkm.cells_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR).
Local Abbreviation fa_final := (@AFkm.fa_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR).
Local Abbreviation flags_final := (@AFkm.flags_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm HAR).
Local Abbreviation depot_ids_boundG := (@AFkm.depot_ids_boundG _ W ly regs0 mem0 maxc mf au mu Hmf Hmu B S TS HARm).
Local Abbreviation depot_final := (@AFkm.depot_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HARm HAR).
Local Abbreviation shadow_in_USH := (@AFkm.shadow_in_USH _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation shadow_in_FSH := (@AFkm.shadow_in_FSH _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation UQ2 := (@AFkm.UQ2 _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation FQ2 := (@AFkm.FQ2 _ ly regs0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation committed_shadow_old := (@AFkm.committed_shadow_old _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmf_def Hmu_def HAR).
Local Abbreviation shadow_final := (@AFkm.shadow_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hmf_def Hmu_def HAR).
Local Abbreviation zshadow_final := (@AFkm.zshadow_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HAR).
Local Abbreviation vis_final := (@AFkm.vis_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hinited Hmf_def Hmu_def HAR).
Local Abbreviation abs_cell_okG := (@AFkm.abs_cell_okG).
Local Abbreviation abs_cells_okG := (@AFkm.abs_cells_okG).
Local Abbreviation const_final := (@AFkm.const_final _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD HAR).
Local Abbreviation AR_transportG := (@AFkm.AR_transportG _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR).
Local Abbreviation XC_owned := (@AFkm.XC_owned _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S HARm Hau_def Hmu_def HAR).
Local Abbreviation LEAF_G := (@AFkm.LEAF_G _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR).
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
Local Open Scope am_scope.
Let WF := am_wf B ly S _ HARm.
Hypothesis Hpum : refill_reg S c.
Hypothesis Hslack : A_bytes (w_A W) + EV_A <= abudget S.
Hypothesis Hql : qloosem S.
Lemma NZ0 : forall q, In q (vm_maps (m_vmmaps md0)) -> 0 < bv_unsigned (snd q).
Proof. exact (proj2 (proj1 (proj2 (proj2 (proj2 HAR))))). Qed.
Lemma SRr_with_AI : forall (Wx : world tfibsegs) cx (Q : world tfibsegs -> config -> Prop),
SRr tfibsegs Wx cx Q -> SRr tfibsegs Wx cx (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. clear. intros Wx cx Q H HI T HK. apply (H HI T). intros W' c' Hle HI' HQ. exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Lemma lit_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1). Proof. clear. apply bv_eq. reflexivity. Qed.
Lemma lit_enomem : Z_to_bv 64 ENOMEM_RET = errno_ret ENOMEM. Proof. clear. unfold errno_ret, ENOMEM, ENOMEM_RET. apply bv_eq. reflexivity. Qed.
Lemma pru18 : page_round_up_Z kUserMapSize = kUserMapSize. Proof. clear. reflexivity. Qed.
Lemma Hcut_out : forall (Hh : word -> bool) lo hi (a : word), ~ (lo <= bv_unsigned a < hi) -> Hcut Hh lo hi a = Hh a.
Proof.
clear. intros Hh lo hi a Ha. unfold Hcut. destruct (Z.leb_spec lo (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) hi); cbn [andb negb]; try (exfalso; zlia);
rewrite ?andb_true_r, ?andb_false_r; try reflexivity; exfalso; apply Ha; zlia.
Qed.
Lemma apresent_hmono : forall (Ha Hb : word -> bool) m a, (forall y, Ha y = false -> Hb y = false) -> apresent Ha m a -> apresent Hb m a.
Proof. clear. intros Ha Hb m a Hm [H1 H2]. split; [exact (Hm _ H1) | exact H2]. Qed.
Lemma val_mem_hmono : forall (Wa Wb : world tfibsegs) m a (w : nat) x, (forall y, w_H Wa y = false -> w_H Wb y = false) ->
val_mem tfibsegs (mrestrict (w_H Wa) m) a w x -> val_mem tfibsegs (mrestrict (w_H Wb) m) a w x.
Proof.
clear. intros Wa Wb m a w x Hm HV k Hk. pose proof (HV k Hk) as X. unfold mbyte, mrestrict in X |- *.
destruct (w_H Wa (Z_to_bv 64 (a + Z.of_nat k))) eqn:E.
- unfold seg_rom in X. rewrite (memory_read1_hidden tfibsegs (w_H Wa) (w_Hoff Wa) _ E) in X. discriminate X.
- rewrite (Hm _ E). exact X.
Qed.
Lemma aview_high_apresent : forall (Hh : word -> bool) mem a, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs Hh mem a <> None -> apresent Hh mem a.
Proof.
clear. intros Hh mem a Ha HV. unfold aview in HV. destruct (mbyte tfibsegs (mrestrict Hh mem) a) as [b|] eqn:E; [|exfalso; exact (HV eq_refl)].
exact (mbyte_high_apresent Hh mem a b Ha E).
Qed.
Lemma ALedger_shape : forall S1 S2 md,
(forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S2 c') = rg_mapped_user (reg S1 c') /\ rg_mapped_fa (reg S2 c') = rg_mapped_fa (reg S1 c') /\ rg_holes (reg S2 c') = rg_holes (reg S1 c')) ->
sec_extents ly S2 = sec_extents ly S1 -> sec_live_bytes S2 = sec_live_bytes S1 -> prim_committed S2 = prim_committed S1 ->
st_nev S2 = st_nev S1 -> st_sec_reserved S2 = st_sec_reserved S1 ->
ALedger tfibsegs ly S1 md -> ALedger tfibsegs ly S2 md.
Proof.
clear. intros S1 S2 md RGEQ SE SL PC NEV SR L. destruct L as [L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
assert (CUT : forall x, cut_ok ly S2 x <-> cut_ok ly S1 x).
{ intros x. unfold cut_ok. split; (intros [H|[H|(c' & Hc' & H)]]; [left; exact H | right; left; exact H | right; right; exists c'; split; [exact Hc'|]]);
destruct (RGEQ c' Hc') as (Q1 & Q2 & Q3); [rewrite <- Q1, <- Q2 | rewrite Q1, Q2]; exact H. }
assert (HOLE : forall a, prim_hole_at ly S2 a <-> prim_hole_at ly S1 a).
{ intros a. unfold prim_hole_at. split; intros (c' & h & Hc' & Hin & H); exists c', h; destruct (RGEQ c' Hc') as (Q1 & Q2 & Q3);
[rewrite <- Q3 | rewrite Q3]; (split; [exact Hc' | split; [exact Hin | exact H]]). }
constructor; try assumption.
- destruct L3 as (pieces & (Q1 & Q2 & Q3) & P2). exists pieces. split; [|exact P2]. split; [|split; [exact Q2|]].
+ apply Forall_forall. intros p' Hp. pose proof (proj1 (Forall_forall _ _) Q1 p' Hp) as (A1 & A2 & A3). split; [exact A1|]. split; apply CUT; assumption.
+ intros a Ha. rewrite (Q3 a Ha). rewrite HOLE. tauto.
- rewrite SE. exact L6.
- rewrite SE. exact L7.
- rewrite PC, SE, SR. exact L8.
-   rewrite SE. exact L11.
Qed.
Definition FL50 : word := Z_to_bv 64 50.
Lemma nores50 : mmap_noreserve_b FL50 = false. Proof. clear. reflexivity. Qed.
Lemma core50 : mmap_flags_core FL50 = 50. Proof. clear. reflexivity. Qed.
Lemma grant_piece_shape : forall (a n : word) md,
vm_maps (m_vmmaps (grant_md false FL50 a n md)) = vm_maps (m_vmmaps md) /\
vm_reserved (m_vmmaps (grant_md false FL50 a n md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (grant_md false FL50 a n md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (grant_md false FL50 a n md)) = vm_mmap_base (m_vmmaps md) /\
vm_init_sp (m_vmmaps (grant_md false FL50 a n md)) = vm_init_sp (m_vmmaps md).
Proof. clear. intros a n md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite nores50. cbn. destruct md as [fd [maps lazy mat] io fs pr lim tm]. cbn. destruct maps; cbn. repeat split; reflexivity. Qed.
Lemma grant_hole_shape : forall (a n : word) md,
vm_maps (m_vmmaps (grant_md true FL50 a n md)) = (a, n) :: vm_maps (m_vmmaps md) /\
vm_reserved (m_vmmaps (grant_md true FL50 a n md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (grant_md true FL50 a n md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (grant_md true FL50 a n md)) = vm_mmap_base (m_vmmaps md) /\
vm_init_sp (m_vmmaps (grant_md true FL50 a n md)) = vm_init_sp (m_vmmaps md).
Proof. clear. intros a n md. unfold grant_md, with_mmap_backing, mmap_model. rewrite nores50. destruct md as [fd [maps lazy mat] io fs pr lim tm]. cbn. destruct maps; cbn. repeat split; reflexivity. Qed.
Lemma ROOM3 : rg_mapped_user (reg S c) + kUserMapSize <= kUserMapSize * EV_MAX /\
(st_nev S <= EV_MAX \/ rg_alloc_user (reg S c) <= class_size c * (65536 - 10240)).
Proof.
pose proof class_facts as (C1 & C2 & C3 & C4 & C5).
apply (preg_room (as_universe B) 1 0 0 S S c n (WF1 (proj1 Hpum)) HcR (Z.le_refl 1) Hinited (regs_only_refl S) eq_refl Hchunks ltac:(clear - C3; zlia) (proj1 (proj2 Hpum))).
rewrite <- Hnf_def. exact Hnlt.
Qed.
Lemma refill_tree_ok : forall ns, atok ns (refill_tree c S) (fun _ r => Wf (as_universe B) (snd r)).
Proof.
intros ns. pose proof (WF1 (proj1 Hpum)) as W1. pose proof (class_ok c HcR) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs). pose proof class_facts as (C1 & C2 & C3 & C4 & C5).
assert (HL : (Z.to_nat c < length (st_regions S))%nat) by (eapply WfP_len_regions; [exact W1 | clear - HcR; zlia]).
assert (HLc : (Z.to_nat c < length (st_cache S))%nat) by (eapply WfP_len_cache; [exact W1 | clear - HcR; zlia]).
unfold refill_tree. apply atok_bind. unfold init_cache_if_needed. apply atok_bind. apply atok_get. cbn [fst snd]. rewrite Hinited. apply atok_ret. cbn [fst snd].
unfold refill_if_empty. apply atok_bind. apply atok_get_pc. cbn [fst snd]. rewrite Hchunks, PM3, <- Hn.
apply atok_bind.
eapply atok_mono; [|apply (get_from_allocator_ok (as_universe B) 1 0 0 S c n ns W1 HcR (Z.le_refl 1)); [clear - C3; zlia | rewrite Hn, Hmax; exact Kmcs | clear - C3; zlia | intros _; exact ROOM3]].
intros ns1 [got s2] Hg. cbn [fst snd]. destruct got as [tops|].
- destruct Hg as (r2 & rest & W2 & -> & Hruns & Hel & Hlen & Hfl). apply atok_set_pc. cbn [snd].
set (r' := mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)).
rewrite <- (upd_reg_upd_reg c r2 r' S).
pose proof (wf_classes _ _ _ _ _ W2 c HcR) as C0. unfold wf_class in C0.
rewrite reg_upd_reg in C0 by ((clear - HcR; zlia) || exact HL). change (cache (upd_reg c r2 S) c) with (cache S c) in C0.
change (st_cache_inited (upd_reg c r2 S)) with (st_cache_inited S) in C0. rewrite Hinited in C0.
unfold Wf. eapply (WfP_set_region_pc (as_universe B) 0 0 0 (upd_reg c r2 S) c); [exact W2 | exact HcR | | clear; zlia | | |].
+ change (st_cache_inited (upd_reg c r2 S)) with (st_cache_inited S). rewrite Hinited.
change (chunk_offs (upd_reg c r2 S) c) with (chunk_offs S c). change (batch_offs (upd_reg c r2 S) c) with (batch_offs S c).
eapply (cls_ok_repart c r2 (cache S c) true _ _ r' _ true _ _ []); try exact C0; try reflexivity.
* exact Hruns.
* subst r'. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]. pose proof (wr_fa_len _ _ _ _ _ _ C0). clear - H Hfl Hlen C3. zlia.
* cbn [pc_max pc_chunks]. split; [rewrite Hmax; reflexivity|]. unfold cache_fill_order. rewrite length_rev, <- Hmax. pose proof (Z.div_mod maxc 2 ltac:(clear; zlia)) as DM. pose proof (Z.mod_pos_bound maxc 2 ltac:(clear; zlia)) as MB. clear - Hlen C1 C3 Hn DM MB. zlia.
* subst r'. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]. rewrite Hel, Hchunks. unfold cache_fill_order. cbn [pc_chunks app].
change (chunk_offs (upd_reg c r2 S) c) with (chunk_offs S c). change (batch_offs (upd_reg c r2 S) c) with (batch_offs S c).
pose proof (perm_cache_refill (fa_elems (class_size c) rest) [] (chunk_offs S c) (batch_offs S c) tops) as PP. cbn [app] in PP. exact PP.
+ rewrite reg_upd_reg by ((clear - HcR; zlia) || exact HL). subst r'. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]. pose proof (wf_prim_ev _ _ _ _ _ W2) as PE.
unfold kUserMapSize in *. clear - PE. zlia.
+
pose proof (wf_fa_room _ _ _ _ _ W2 c HcR) as RM. unfold class_elems in RM. rewrite !reg_upd_reg in RM by ((clear - HcR; zlia) || exact HL).
change (cache (upd_reg c r2 S) c) with (cache S c) in RM. rewrite Hel, Hchunks in RM.
change (chunk_offs (upd_reg c r2 S) c) with (chunk_offs S c) in RM |- *. change (batch_offs (upd_reg c r2 S) c) with (batch_offs S c) in RM |- *.
change (st_nev (upd_reg c r2 S)) with (st_nev S) in RM |- *.
subst r'. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd pc_chunks]. unfold cache_fill_order.
eapply fa_room_xfer; [exact RM | rewrite !length_app, length_rev; cbn [length]; clear; zlia | apply Z.le_refl].
+
apply (regime_cap_keep (as_universe B) 0 0 0 (upd_reg c r2 S) c _ W2 HcR); rewrite reg_upd_reg by ((clear - HcR; zlia) || exact HL); subst r'; cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd]; [reflexivity | clear; zlia].
- destruct Hg as (r' & -> & W2 & NS). apply atok_ret. cbn [snd]. unfold Wf. eapply WfP_weaken; [exact W2 | | |]; clear; zlia.
Qed.
Definition RANGE (addr : Z) (a : Z) : Prop := addr <= a < addr + kUserMapSize.
Definition SHR (sh : Z) (a : Z) : Prop := sh <= a < sh + 32768.
Definition P_grant (W3 : world tfibsegs) (addr sh : Z) (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ (forall a, RANGE addr a -> apresent (w_H W3) m a /\ m (w64 a) = Some (Z_to_bv 8 0)) /\
(forall a, SHR sh a -> apresent (w_H W3) m a).
Lemma node3 : forall (q : kreq) (sN : astate) (K : Z -> itree astate (unit * astate)) (Q : unit * astate -> world tfibsegs -> config -> Prop)
(Wx : world tfibsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (c1 : config)
(ea : sv) (addr sh : Z) (hole : bool) (cs : list YP09.chunk),
at_N3 Wx md X P ss Wx c1 -> AI tfibsegs (w_H Wx) (w_A Wx) (cfg_model c1) ->
ss_pc ss = 0x6416c ->
sr_get (ss_regs ss) 17%bv = SLit 222 -> sr_get (ss_regs ss) 10%bv = ea -> sv_atoms_lt aHAV3 ea = true -> U E0 ea = addr ->
sr_get (ss_regs ss) 11%bv = SLit 262144 -> sr_get (ss_regs ss) 12%bv = SLit 3 -> sr_get (ss_regs ss) 13%bv = SLit 50 ->
sr_get (ss_regs ss) 14%bv = SLit 18446744073709551615 -> sr_get (ss_regs ss) 15%bv = SLit 0 ->
no_cdata (ss_mem ss) = true -> nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs) ->
map skel (tl (ss_mem ss)) = SKEL_TAILR ->
addr mod 65536 = 0 -> RBv <= addr -> addr + kUserMapSize <= RBv + 2 ^ 32 ->
sh = SHBv + addr / 8 -> sh mod 4096 = 0 -> kHighShadowBeg <= sh -> sh + 32768 <= kHighShadowEnd ->
(if hole then region_free (vm_reserved (m_vmmaps (cfg_model c1)) ++ vm_maps (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = true
else region_free (vm_reserved (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = true /\
map_contains (vm_maps (m_vmmaps (cfg_model c1))) (w64 addr) (w64 kUserMapSize) = true) ->
amwf (cfg_model c1) ->
YM05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
eager_used (cfg_model c1) + A_bytes (w_A Wx) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps (cfg_model c1)) ->
refusable q = true -> (forall z, z = 0 \/ z = 1 -> aok sN q z) ->
(forall m m' : word -> option byte, (forall x : word, ~ RANGE addr (bv_unsigned x) -> m' x = m x) -> P m -> P m') ->
(forall a, SHR sh a -> ~ X a) -> (forall a, SHR sh a -> mem0 (w64 a) <> None) ->
hole = false ->
(forall (W3 : world tfibsegs) c', let md2 := grant_md hole FL50 (w64 addr) (w64 kUserMapSize) (cfg_model c1) in
wle Wx W3 -> w_A W3 = (sh, sh + 32768) :: (addr, addr + kUserMapSize) :: w_A Wx -> hsub (w_H W3) (w_H Wx) ->
(forall a : word, w_H Wx a = false -> w_H W3 a = false) ->
AI tfibsegs (w_H W3) (w_A W3) md2 -> amwf md2 -> same_io md0 md2 -> eager_used md2 <= eager_used (cfg_model c1) + kUserMapSize ->
(forall a : word, ~ RANGE addr (bv_unsigned a) -> ~ SHR sh (bv_unsigned a) -> w_H W3 a = w_H Wx a) ->
A_bytes (w_A W3) = A_bytes (w_A Wx) + kUserMapSize + 32768 ->
at_R3 W3 md2 (fun a => X a \/ RANGE addr a) (P_grant W3 addr sh P) (resume ss ea (ss_mem ss) (ss_facts ss)) W3 c' ->
amreal tfibsegs (K 1) W3 c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H Wx) (w_A Wx) (cfg_model c1) -> AI tfibsegs (w_H Wx) (w_A Wx) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H Wx) (w_A Wx) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (K (bit i)) Wx (nx i) Q).
Proof.
intros q sN K Q Wx md X P ss c1 ea addr sh hole cs HN HAI Hpc H17 H10 Hea Uea H11 H12 H13 H14 H15 Hnc Hhd Hsk
Hal HaRB HaHI Hsh Hshal Hshlo Hshhi PLACE MWn HTOP SLACK Hrq Haok HPu HXsh H0sh HOLEF GRANT IO0.
pose proof stack_ext_ok3 as [SX1 SX2]. pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & _). pose proof stack_ivsR as (_ & _ & _ & S4 & S5).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (EcM : cfg_model c1 = mdN) by (rewrite Ec; reflexivity). rewrite EcM in *.
destruct (st_ok_ecall_shape_r tfibsegs (w_H Wx) E' ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
rewrite Hpc in Hms.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
assert (A0 : 0 <= addr /\ addr + kUserMapSize < 2 ^ 63) by (clear - HaRB HaHI DR; numconst; unfold kUserMapSize in *; zlia).
assert (A4096 : addr mod 4096 = 0) by (clear - Hal; apply Z.mod_divide in Hal as [q' Hq]; [|zlia]; rewrite Hq; apply Z.mod_divide; [zlia|]; exists (q' * 16); zlia).
assert (Uaddr : bv_unsigned (w64 addr) = addr) by (unfold w64; apply unsigned_lit_small; clear - A0; unfold kUserMapSize in A0; zlia).
assert (Un : bv_unsigned (w64 kUserMapSize) = kUserMapSize) by (unfold w64; apply unsigned_lit_small; unfold kUserMapSize; clear; zlia).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (rewrite (Hregs 17%bv), H17; reflexivity).
assert (R10 : getr regs 10 = w64 addr).
{ rewrite (Hregs 10%bv), H10. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' ea)). f_equal.
change (bv_unsigned (sv_denot E' ea)) with (U E' ea). rewrite (U_agree aHAV3 E0 E' ea HE Hea). exact Uea. }
assert (R11 : getr regs 11 = Z_to_bv 64 262144) by (rewrite (Hregs 11%bv), H11; reflexivity).
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (rewrite (Hregs 12%bv), H12; reflexivity).
assert (R13 : getr regs 13 = FL50) by (rewrite (Hregs 13%bv), H13; reflexivity).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; apply lit_m1).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (rewrite (Hregs 15%bv), H15; reflexivity).
assert (MWF0 : MWF mdN) by (apply (proj1 (amwf_MWF mdN)); exact (proj1 MWn)).
pose proof (commit_nonempty hole FL50 (w64 addr) (w64 kUserMapSize) mdN ltac:(rewrite Un; unfold kUserMapSize; clear; zlia) (proj2 MWn)) as NZg.
assert (CEIL : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_ceiling).
{ rewrite Uaddr. change (page_round_up_Z 262144) with 262144. clear - HaHI DR. numconst. unfold kUserMapSize in *. zlia. }
assert (CEILT : bv_unsigned (w64 addr) + page_round_up_Z 262144 <= alloc_top (m_vmmaps mdN)).
{ eapply Z.le_trans; [exact CEIL | apply YM05.ceil_le_top; exact HTOP]. }
assert (PLACE' : if hole then region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = true
else region_free (vm_reserved (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = true /\
map_contains (vm_maps (m_vmmaps mdN)) (w64 addr) (Z_to_bv 64 (page_round_up_Z 262144)) = true).
{ change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize). exact PLACE. }
assert (SL1 : eager_used mdN + A_bytes (w_A Wx) + page_round_up_Z 262144 <= vm_limit (m_vmmaps mdN)).
{ change (page_round_up_Z 262144) with 262144. clear - SLACK. unfold kUserMapSize in SLACK. zlia. }
pose proof (commit_AI tfibsegs (w_H Wx) (w_A Wx) mdN hole FL50 (w64 addr) 262144 HAI MWF0 nores50
ltac:(rewrite Uaddr; unfold page_size; exact A4096) ltac:(clear; zlia) CEILT PLACE' SL1) as [CG BUD].
pose proof (commit_eager tfibsegs (w_H Wx) (w_A Wx) mdN hole FL50 (w64 addr) 262144 HAI MWF0 nores50
ltac:(rewrite Uaddr; unfold page_size; exact A4096) ltac:(clear; zlia) CEILT PLACE' SL1) as EG.
change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in CG, BUD, EG.
change (page_round_up_Z 262144) with 262144 in EG.
pose proof (destroyed_AI tfibsegs (w_H Wx) (w_A Wx) mdN (w64 addr) 262144 HAI MWF0
ltac:(rewrite Uaddr; unfold page_size; exact A4096) ltac:(clear; zlia) CEILT) as [CD EGD].
change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in CD, EGD.
destruct (commit_node3 tfibsegs hole regs (Z_to_bv 64 0x6416c) mem (seg_rom tfibsegs) mdN FL50 (w64 addr) 262144
(AI_halted _ _ _ _ HAI) R17 R10 ltac:(rewrite Uaddr; unfold page_size; exact A4096) ltac:(rewrite Uaddr; clear - HaRB DR; numconst; zlia)
R11 ltac:(clear; zlia) CEILT R12 R13 core50 R14 R15 PLACE' BUD) as (I & nx & bit & i0 & NODE & Bi0 & OUT).
change (Z_to_bv 64 (page_round_up_Z 262144)) with (w64 kUserMapSize) in OUT.
destruct Hmem as (Hwf & _ & _).
assert (REXT : forall r a, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r ->
~ RANGE addr a /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. destruct (ss_mem ss) as [|r0 tl0] eqn:Em; [destruct Hr|]. try rewrite Em in Hhd; try rewrite Em in Hsk. cbn [nth_error] in Hhd. injection Hhd as Hr0. cbn [List.tl] in Hsk.
destruct Hr as [<-|Hr].
- rewrite Hr0 in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite (HEn 2%nat ltac:(cbv; zlia)), E2 in Ha.
unfold RANGE. clear - Ha SX1 S4 S5 HaRB HaHI. numconst. unfold kUserMapSize in *. try unfold sp0 in *. zlia.
- apply (in_map skel) in Hr. rewrite Hsk in Hr. pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7).
unfold RANGE. clear - Ha X2 X3 X6 HaRB HaHI. unfold kUserMapSize in *. zlia. }
assert (RWIN : forall r a, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_wlo r <= a < base_val E' (YP09.r_base r) + YP09.r_whi r ->
~ RANGE addr a /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. pose proof (region_wf_facts r (regions_wf_In _ r Hwf Hr)) as (_ & WW & _). apply (REXT r a Hr). clear - Ha WW. zlia. }
assert (SCR : forall a, sp0 - RSTACK <= a < sp0 -> ~ RANGE addr a) by (intros a Ha; unfold RANGE; clear - Ha SX1 HaRB HaHI; unfold kUserMapSize in *; zlia).
assert (LIMg : vm_limit (m_vmmaps (grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN)) = vm_limit (m_vmmaps mdN)).
{ destruct hole; [exact (proj1 (proj2 (proj2 (grant_hole_shape _ _ _)))) | exact (proj1 (proj2 (proj2 (grant_piece_shape _ _ _))))]. }
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, (fun _ => 1), (fun _ => false), i0.
split. { rewrite Ec, Hms. exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & _ & -> & ->); cbn [cfg_model]; exact (proj1 CG). }
split. { intros i. apply Haok. right; reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros i _; reflexivity|].
split; [intros i E; discriminate E|].
intros i _. cbn beta. destruct (OUT i) as (md_i & Hh_i & IO_i & Bv & NX & MD); rewrite NX; rewrite MD in IO_i |- *.
-
set (md2 := grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN) in *.
assert (AL1 : addr <= addr + kUserMapSize) by (unfold kUserMapSize; clear; zlia).
assert (AL2 : addr mod page_size = 0) by (unfold page_size; exact A4096).
assert (AL3 : (addr + kUserMapSize) mod page_size = 0).
{ unfold page_size. clear - A4096. apply Z.mod_divide in A4096 as [q' Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q' + 64). unfold kUserMapSize. zlia. }
destruct (allow_expose tfibsegs Wx md2 addr (addr + kUserMapSize) AL1 AL2 AL3 (proj1 CG) ltac:(rewrite LIMg; clear - EG SLACK; unfold kUserMapSize in *; zlia))
as (LE2 & A2 & AB2 & VIS2 & MON2 & AI2).
set (W2 := wallow tfibsegs Wx addr (addr + kUserMapSize) AL1 AL2 AL3) in *.
assert (SL1' : sh <= sh + 32768) by (clear; zlia).
assert (SL2 : sh mod page_size = 0) by (unfold page_size; exact Hshal).
assert (SL3 : (sh + 32768) mod page_size = 0).
{ unfold page_size. clear - Hshal. apply Z.mod_divide in Hshal as [q' Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q' + 8). zlia. }
destruct (allow_expose tfibsegs W2 md2 sh (sh + 32768) SL1' SL2 SL3 AI2 ltac:(rewrite LIMg, AB2; clear - EG SLACK; unfold kUserMapSize in *; zlia))
as (LE3 & A3 & AB3 & VIS3 & MON3 & AI3).
set (W3 := wallow tfibsegs W2 sh (sh + 32768) SL1' SL2 SL3) in *.
assert (MON : forall a : word, w_H Wx a = false -> w_H W3 a = false) by (intros a Ha; apply MON3, MON2, Ha).
assert (SUB : hsub (w_H W3) (w_H Wx)).
{ intros a Ha. destruct (w_H Wx a) eqn:Ex; [reflexivity|]. rewrite (MON a Ex) in Ha. discriminate Ha. }
eapply (amreal_world_le tfibsegs _ Wx W3); [exact (wle_trans _ _ _ _ LE2 LE3) | intros _; exact AI3 |].
apply (GRANT W3); [exact (wle_trans _ _ _ _ LE2 LE3) | rewrite A3, A2; reflexivity | exact SUB | exact MON | exact AI3
| split; [apply (proj2 (amwf_MWF md2)); exact (proj2 CG) | exact NZg] | exact (IOtr _ IO_i) | exact EG
| intros a N1 N2; unfold W3, W2, wallow; cbn [w_H]; rewrite (Hcut_out _ sh (sh + 32768) a) by exact N2; apply Hcut_out; unfold RANGE in N1; exact N1
| rewrite AB3, AB2; clear; unfold kUserMapSize; zlia |].
assert (FRz : forall x : word, ~ RANGE addr (bv_unsigned x) -> zfill (w64 addr) (w64 kUserMapSize) mem x = mem x).
{ intros x Hx. apply zfill_out. rewrite Uaddr, Un. unfold RANGE in Hx. clear - Hx. zlia. }
pose proof (at_N3_cont Wx W3 md2 X (P_grant W3 addr sh P) ss ea (w64 addr) (RANGE addr) (zfill (w64 addr) (w64 kUserMapSize) mem) ms E'
HE HS Hrv MEQ PRS SUB ltac:(rewrite <- R10; symmetry; rewrite <- H10; exact (Hregs 10%bv)) Hnc
ltac:(intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; exact (FRz x Hx)) REXT RWIN SCR) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc in C. rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm.
apply C. split; [exact (HPu mem _ FRz HPm)|]. split.
+ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (unfold RANGE in Ha; clear - Ha A0; unfold kUserMapSize in *; zlia).
assert (Z0 : zfill (w64 addr) (w64 kUserMapSize) mem (w64 a) = Some (Z_to_bv 8 0)).
{ apply zfill_in. rewrite Uaddr, Un. unfold w64. rewrite unsigned_lit_small by exact Ra. exact Ha. }
split; [|exact Z0]. split; [|exists (Z_to_bv 8 0); exact Z0].
apply MON3. apply VIS2. unfold w64. rewrite unsigned_lit_small by exact Ra. exact Ha.
+ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (unfold SHR in Ha; clear - Ha Hshlo Hshhi; unfold kHighShadowBeg, kHighShadowEnd in *; zlia).
split; [apply VIS3; unfold w64; rewrite unsigned_lit_small by exact Ra; exact Ha|].
assert (NR : ~ RANGE addr a) by (unfold RANGE, SHR in *; clear - Ha Hshhi HaRB DR; numconst; unfold kHighShadowEnd in *; zlia).
pose proof (FRz (w64 a) ltac:(unfold w64; rewrite unsigned_lit_small by exact Ra; exact NR)) as E.
assert (NZ : mem (w64 a) <> None).
{ pose proof (MEQ (w64 a) ltac:(unfold w64; rewrite unsigned_lit_small by exact Ra; exact (HXsh a Ha))) as EQm. rewrite Hms in EQm. cbn [ms_mem pend_at] in EQm. rewrite EQm. exact (H0sh a Ha). }
unfold w64 in E, NZ |- *. rewrite E.
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (NZ eq_refl)].
Qed.
Definition FLR : word := Z_to_bv 64 0x104022.
Lemma noresR : mmap_noreserve_b FLR = true. Proof. clear. reflexivity. Qed.
Definition LEAFQ : unit * astate -> world tfibsegs -> config -> Prop := refill_leaf B ly S W regs0 mem0 md0 c.
Lemma VIS64 : forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r -> 0 <= aeval B ly (fst r) + i < 2 ^ 64.
Proof.
intros r i Hr Hi.
pose proof (vis_lists_u64 B ly S _ (proj1 HAR) ltac:(intros r' Hr'; destruct (ts_junk B TS ly r' Hr') as (z & E & Z1 & Z2); exists z; split; [exact E|]; unfold kImgEnd; clear - Z1 Z2; zlia) r i Hr Hi) as X.
ceil; unfold ASAN_CEIL in X. clear - X. zlia.
Qed.
Definition PF (Wd : world tfibsegs) (NC MU MF : Z) (TOPS : list Z) (m : word -> option byte) : Prop :=
(forall a, FAv <= a < FAv + mf -> apresent (w_H Wd) m a) /\
(forall a, DSTv <= a < DSTv + 64 -> apresent (w_H Wd) m a) /\
(MU = mu2 -> forall a, adr <= a < adr + kUserMapSize -> apresent (w_H Wd) m a) /\
(MU = mu2 -> forall x : word, W_USH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250) /\ w_H Wd x = false) /\
(MF = mf2 -> forall a, fadr <= a < fadr + kFreeArrayMapSize -> apresent (w_H Wd) m a) /\
(MF = mf2 -> forall x : word, W_FSH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250) /\ w_H Wd x = false) /\
(forall i, 0 <= i < NC -> val_mem tfibsegs (mrestrict (w_H Wd) m) (FAv + 4 * (nf + NC) - 4 - 4 * i) 4 ((au + i * csz) / 16)) /\
(forall j, 0 <= j < 4 * Z.of_nat (length TOPS) -> m (w64 (DSTv + j)) = m (w64 (FAv + 4 * (nf + NC - Z.of_nat (length TOPS)) + j))).
Lemma or_dec : forall A B : Prop, (A \/ ~ A) -> (B \/ ~ B) -> (A \/ B) \/ ~ (A \/ B).
Proof. clear. intros A B [a|a] [b|b]; try (left; tauto); right; tauto. Qed.
Lemma and_dec : forall A B : Prop, (A \/ ~ A) -> (B \/ ~ B) -> (A /\ B) \/ ~ (A /\ B).
Proof. clear. intros A B [a|a] [b|b]; try (right; tauto); left; tauto. Qed.
Lemma zr_dec : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. clear. intros lo hi a. destruct (zrange_dec lo hi a); [left|right]; assumption. Qed.
Lemma beq_dec : forall b : bool, b = true \/ ~ (b = true).
Proof. clear. intros [|]; [left; reflexivity | right; discriminate]. Qed.
Lemma zeq_dec : forall x y : Z, x = y \/ ~ (x = y).
Proof. clear. intros x y. destruct (Z.eq_dec x y); [left|right]; assumption. Qed.
Lemma zle_dec : forall x y : Z, x <= y \/ ~ (x <= y).
Proof. clear. intros x y. destruct (Z_le_dec x y); [left|right]; assumption. Qed.
Lemma zlt_dec : forall x y : Z, x < y \/ ~ (x < y).
Proof. clear. intros x y. destruct (Z_lt_dec x y); [left|right]; assumption. Qed.
Lemma XC_dec : forall NC MU MF (uq fq : bool) a, XC NC MU MF uq fq a \/ ~ XC NC MU MF uq fq a.
Proof.
clear. intros NC MU MF uq fq a. unfold AFkm.XC, AFkm.W_FEn, W_UW, W_USH, W_FW, W_FSH.
repeat first [apply zr_dec | apply or_dec | apply and_dec | apply beq_dec | apply zeq_dec | apply zle_dec | apply zlt_dec].
Qed.
Lemma LEAF_std : forall (NC MU MF : Z) (TOPS : list Z) (FL : list fseg) (HO : list (Z * Z)) (uq fq : bool)
(Wd : world tfibsegs) (mdf : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (v cnt nfv auv : Z) W' c',
at_RET3 Wd v mdf X (fun m => P m /\ P_cells Wd cnt nfv MF auv MU m) W' c' ->
v = (if (length TOPS =? 0)%nat then 0 else 1) -> cnt = Z.of_nat (length TOPS) -> nfv = nf + NC - cnt -> auv = au + NC * csz ->
(forall m, P m -> PF Wd NC MU MF TOPS m) ->
(forall a, X a -> (sp0 - RSTACK <= a < sp0) \/ XC NC MU MF uq fq a) ->
(forall x : word, ~ XC NC MU MF uq fq (bv_unsigned x) -> w_H Wd x = w_H W x) ->
hsub (w_H Wd) (w_H W) -> wle W Wd -> A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20 -> (forall i, In i (w_A W) -> In i (w_A Wd))   -> same_io md0 mdf -> amwf mdf ->
ALedger tfibsegs ly (SG NC MU MF TOPS FL HO) mdf -> Wf (as_universe B) (SG NC MU MF TOPS FL HO) ->
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
{ intros x N1 N2. apply MEQ0. intros Hx. destruct (HX _ Hx) as [H|H]; [exact (N1 H) | exact (N2 H)]. }
assert (FAP : forall a, FAv <= a < FAv + MF -> apresent (w_H Wd) mem' a).
{ intros a Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [L|L]; [apply F1; clear - Ha L; zlia|].
destruct HMF as [EM|[EM _]]; [exfalso; clear - Ha L EM; zlia|]. apply (F5 EM). clear - Ha L EM G24 G33; unfold kFreeArrayMapSize in *; zlia. }
assert (UWP : MU = mu2 -> forall a, RBv <= a < RBv + mu2 -> apresent (w_H Wd) mem' a).
{ intros EM a Ha. destruct (Z_lt_le_dec a (RBv + mu)) as [L|L].
-
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (ASp (region_off c), mu)
ltac:(unfold aareas; apply in_app_iff; left; apply in_flat_map; exists c; split; [apply In_zseq; clear - HcR; zlia | left; rewrite <- Hmu_def; reflexivity])
(a - RBv) ltac:(cbn [snd]; clear - Ha L; zlia)) as RV.
cbn [fst aeval] in RV. replace (ly_space ly + region_off c + (a - RBv)) with a in RV by (rewrite RBv_is; unfold region_base; clear; zlia).
assert (Ra : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha L Q1 Q2 Y3 Y5 GE; numconst; zlia).
destruct (aview_high_apresent _ _ _ Ra RV) as [Hh [b Hb]].
assert (NX : ~ XC NC MU MF uq fq a) by (apply (Z_user NC MU MF TOPS HNC uq fq HUQ HFQ HMU HMF HNF HNT c mu a HcR); [clear - GE; zlia | rewrite <- Hmu_def; clear; zlia | rewrite <- RBv_is; clear - Ha L; zlia]).
assert (NS : ~ (sp0 - RSTACK <= a < sp0)).
{ intros Hs. pose proof high_factsR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NOSTK). destruct Hsp as (S1 & S3 & _).
apply (proj2 (NOSTK a ltac:(clear - Hs S1 S3; unfold RSTACK in *; zlia))). clear - Ha L Q1 Q2 GE; numconst; zlia. }
split.
+ rewrite (HVIS (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by (clear - Ra; numconst; zlia); exact NX). exact Hh.
+ exists b. rewrite (MEQ (Z_to_bv 64 a)); [exact Hb | |]; rewrite unsigned_lit_small by (clear - Ra; numconst; zlia); [exact NS | exact NX].
- apply (F3 EM). clear - Ha L GE; zlia. }
assert (NOREM : forall x : word, mem0 x <> None -> mem' x <> None \/ (MU = mu /\ uq = true /\ W_UW (bv_unsigned x)) \/ (MF = mf /\ fq = true /\ W_FW (bv_unsigned x))).
{ intros x Hx0.
assert (PRES : forall a, apresent (w_H Wd) mem' a -> bv_unsigned x = a -> mem' x <> None).
{ clear. intros a [_ [b Hb]] <-. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
destruct (zrange_dec (sp0 - RSTACK) sp0 (bv_unsigned x)) as [Ds|Ds]; [left; exact (PRES _ (PRS _ Ds) eq_refl)|].
destruct (XC_dec NC MU MF uq fq (bv_unsigned x)) as [Dx|Dx]; [| left; rewrite (MEQ x Ds Dx); exact Hx0].
pose proof PC as [PRW _].
unfold AFkm.XC, AFkm.W_FEn in Dx.
destruct Dx as [D|[D|[D|[D|[D|[D|[[EQ D]|[[EM D]|[[EQ D]|[EM D]]]]]]]]]].
+ left. apply (PRES _ (PRW _ (or_introl D)) eq_refl).
+ left. apply (PRES _ (F2 _ D) eq_refl).
+ left. apply (PRES _ (PRW _ (or_intror (or_introl D))) eq_refl).
+ left. apply (PRES _ (PRW _ (or_intror (or_intror (or_introl D)))) eq_refl).
+ left. apply (PRES _ (PRW _ (or_intror (or_intror (or_intror D)))) eq_refl).
+ left. apply (PRES (bv_unsigned x) (FAP (bv_unsigned x) ltac:(unfold AFkm.NF' in D; pose proof Hnf as [F0 _]; clear - D HNF F0; zlia)) eq_refl).
+ destruct HMU as [[EM _]|(EM & _ & _)]; [right; left; exact (conj EM (conj EQ D))|]. left. apply (PRES (bv_unsigned x) (UWP EM (bv_unsigned x) ltac:(unfold W_UW in D; clear - D GE; zlia)) eq_refl).
+ left. destruct (F4 EM x D) as [V _]. rewrite V. discriminate.
+ destruct HMF as [EM|[EM _]]; [right; right; exact (conj EM (conj EQ D))|]. left. apply (PRES (bv_unsigned x) (F5 EM (bv_unsigned x) ltac:(unfold W_FW in D; exact D)) eq_refl).
+ left. destruct (F6 EM x D) as [V _]. rewrite V. discriminate. }
assert (VISLOC : forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
0 <= aeval B ly (fst r) + i < 2 ^ 64 /\ (ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize -> prim_committed_at ly S (aeval B ly (fst r) + i))).
{ intros r i Hr Hi. split; [exact (VIS64 r i Hr Hi)|]. apply (vis_lists_committed B ly S _ MA); [|exact Hr|exact Hi].
intros r' Hr'. destruct (ts_junk B TS ly r' Hr') as (z & E & Z1 & Z2). exists z. split; [exact E|]. unfold kImgEnd. clear - Z1 Z2. zlia. }
assert (PC' : P_cells Wd (NT TOPS) (NF' NC - NT TOPS) MF (AU NC) MU mem').
{ unfold AFkm.NT, AFkm.NF', AFkm.AU. rewrite <- Ecnt, <- Eauv. replace (nf + NC - cnt) with nfv by (clear - Enfv; zlia). exact PC. }
rewrite EW. unfold LEAFQ.
apply (LEAF_G NC MU MF TOPS FL HO Wd mdf regs' mem' mat WFG HNC uq fq HUQ HFQ HMU HMF
ltac:(unfold AFkm.NF'; exact HNF) ltac:(unfold AFkm.NT; exact HNT) E_elems E_runs
ltac:(unfold AFkm.NF', AFkm.NT; exact E_rest) HSUB HBUD HINC Hslack HL HMW MEQ HVIS NOREM PRS FAP F2 UWP PC'
ltac:(unfold AFkm.NT, AFkm.NF'; exact F8) ltac:(unfold AFkm.NF'; exact F7) F4 F6 VISLOC Wd c' P Ec eq_refl);
[rewrite <- Ev; exact R10 | exact RCS | exact LE | exact IO].
Qed.
Definition LEAFW : unit * astate -> world tfibsegs -> config -> Prop :=
fun r W' c' => (exists ns' : bool, Wf (as_universe B) (snd r)) -> LEAFQ r W' c'.
Lemma amreal_ask : forall (q : kreq) (sN : astate) (Kc : Z -> itree astate (unit * astate)) (Wx : world tfibsegs) (cx : config)
(Q : unit * astate -> world tfibsegs -> config -> Prop),
match q with KDepot _ => False | _ => True end ->
SRr tfibsegs Wx cx (fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (Kc (bit i)) W1 (nx i) Q)) ->
amreal tfibsegs (IAsk q sN Kc) Wx cx Q.
Proof. clear. intros q sN Kc Wx cx Q Hq H. destruct q; try (destruct Hq); cbn [amreal]; exact H. Qed.
Lemma pairwise_In_any {A0 : Type} : forall (R : A0 -> A0 -> Prop) (l : list A0) x y, pairwise R l -> In x l -> In y l -> x = y \/ R x y \/ R y x.
Proof.
clear. intros R l. induction l as [|z l IH]; intros x y P Hx Hy; [destruct Hx|]. cbn in P. destruct P as [F P].
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [left; reflexivity | right; left; exact (proj1 (Forall_forall _ _) F y Hy) | right; right; exact (proj1 (Forall_forall _ _) F x Hx) | exact (IH x y P Hx Hy)].
Qed.
Lemma SEPS_of : forall md, amwf md -> forall e1 e2, In e1 (vm_maps (m_vmmaps md)) -> In e2 (vm_maps (m_vmmaps md)) ->
e1 = e2 \/ uw (fst e1) + uw (snd e1) <= uw (fst e2) \/ uw (fst e2) + uw (snd e2) <= uw (fst e1).
Proof.
clear. intros md [(_ & _ & _ & PW & _) _] e1 e2 H1 H2. unfold uw.     destruct (pairwise_In_any _ _ e1 e2 PW H1 H2) as [E|[X|X]]; [left; exact E | right; exact X | right; clear - X; zlia].
Qed.
Definition cs_NU : list YP09.chunk := match nth_error (ss_mem R3_NU) 0 with Some r => YP09.r_chunks r | None => [] end.
Lemma NU_facts : ss_pc R3_NU = 0x6416c /\ sr_get (ss_regs R3_NU) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NU) 10%bv = SOff rADR 0 /\ sv_atoms_lt aHAV3 (SOff rADR 0) = true /\
sr_get (ss_regs R3_NU) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NU) 12%bv = SLit 3 /\ sr_get (ss_regs R3_NU) 13%bv = SLit 50 /\
sr_get (ss_regs R3_NU) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NU) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NU) = true /\ nth_error (ss_mem R3_NU) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NU) /\
map skel (tl (ss_mem R3_NU)) = SKEL_TAILR /\
resume R3_NU (SLit ENOMEM_RET) (ss_mem R3_NU) (ss_facts R3_NU) = R3_NUr /\ resume R3_NU (SOff rADR 0) (ss_mem R3_NU) (ss_facts R3_NU) = R3_NUg.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Definition cs_NFe : list YP09.chunk := match nth_error (ss_mem R3_NFe) 0 with Some r => YP09.r_chunks r | None => [] end.
Lemma NFe_facts : ss_pc R3_NFe = 0x6416c /\ sr_get (ss_regs R3_NFe) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NFe) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NFe) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NFe) 12%bv = SLit 3 /\ sr_get (ss_regs R3_NFe) 13%bv = SLit 50 /\
sr_get (ss_regs R3_NFe) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NFe) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NFe) = true /\ nth_error (ss_mem R3_NFe) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NFe) /\
map skel (tl (ss_mem R3_NFe)) = SKEL_TAILR /\
resume R3_NFe (SLit ENOMEM_RET) (ss_mem R3_NFe) (ss_facts R3_NFe) = R3_NFer /\ resume R3_NFe (SOff rFADR 0) (ss_mem R3_NFe) (ss_facts R3_NFe) = R3_NFeg.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Definition cs_NFg : list YP09.chunk := match nth_error (ss_mem R3_NFg) 0 with Some r => YP09.r_chunks r | None => [] end.
Lemma NFg_facts : ss_pc R3_NFg = 0x6416c /\ sr_get (ss_regs R3_NFg) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NFg) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NFg) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NFg) 12%bv = SLit 3 /\ sr_get (ss_regs R3_NFg) 13%bv = SLit 50 /\
sr_get (ss_regs R3_NFg) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NFg) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NFg) = true /\ nth_error (ss_mem R3_NFg) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NFg) /\
map skel (tl (ss_mem R3_NFg)) = SKEL_TAILR /\
resume R3_NFg (SLit ENOMEM_RET) (ss_mem R3_NFg) (ss_facts R3_NFg) = R3_NFgr /\ resume R3_NFg (SOff rFADR 0) (ss_mem R3_NFg) (ss_facts R3_NFg) = R3_NFgg.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Lemma U_adr : U E0 (SOff rADR 0) = adr.
Proof. pose proof facts3 as (_ & _ & _ & _ & _ & G6 & G7 & _). pose proof derived_rangesR as DR. unfold rADR. apply (U_atom E0 57 adr EaADR). clear - G6 G7 DR. numconst. unfold kUserMapSize in *. zlia. Qed.
Lemma U_fadr : U E0 (SOff rFADR 0) = fadr.
Proof. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G31 & G32 & _). pose proof derived_rangesR as DR. unfold rFADR. apply (U_atom E0 64 fadr EaFADR). clear - G31 G32 DR. numconst. unfold kFreeArrayMapSize in *. zlia. Qed.
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
apply Z.mod_divide in Hx8 as [q Hq]; [|clear; zlia].
set (x := (q + (a - sh)) * 8).
assert (Ex : shadow_addr x = a).
{ unfold shadow_addr. subst x. rewrite Z.div_mul by (clear; zlia). rewrite Hq, Z.div_mul in Hsh by (clear; zlia). unfold SHBv in Hsh. unfold SHADOW_OFF. clear - Hsh; zlia. }
assert (Rx : region_base ly c <= x < region_base ly c + 2 ^ 32) by (subst x; clear - Hlo Hhi Ha Hq; zlia).
rewrite <- Ex. apply (HS0 (shadow_addr x)); [rewrite Ex; clear - Ha B1 B2; zlia | exact (prim_shadow_not_client B ly S _ c x MA HcR Rx) | right; exact (prim_shadow_not_vis0 ly c x LY HcR Rx)].
Qed.
Definition zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}. Proof. clear. decide equality; apply Z.eq_dec. Defined.
Definition holeU : bool := if in_dec zz_eq_dec (mu, kUserMapSize) hol then true else false.
Definition holeF (xg : bool) : bool := if in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) (HO1 xg) then true else false.
Lemma K3U_p : YG0h.SUp S c = SUp.
Proof. unfold YG0h.SUp, YG0h.rUp, YG0h.offU, AFkj.SUp, AFkj.rUp. rewrite reg_S. cbn. rewrite Hmu2. reflexivity. Qed.
Lemma K3U_m : YG0h.SUm S c = SUm.
Proof. unfold YG0h.SUm, YG0h.rUm, YG0h.offU, AFkj.SUm, AFkj.rUm. rewrite reg_S. cbn. reflexivity. Qed.
Lemma K3U_addr : YG0h.addrU ly S c = adr.
Proof. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _). unfold YG0h.addrU, YG0h.offU. rewrite <- Hmu_def, <- RBv_is. symmetry. exact G10. Qed.
Lemma K3F_p : forall xg : bool, YG0h.SFp (St1 xg) c = SFp xg.
Proof. intros xg. unfold YG0h.SFp, YG0h.rFp, YG0h.offF, AFkj.SFp, AFkj.rFp. rewrite reg_S1, S1_eq, upd_reg_upd_reg. unfold rg1. cbn. rewrite Hmf2. reflexivity. Qed.
Lemma K3F_m : forall xg : bool, YG0h.SFm (St1 xg) c = SFm xg.
Proof. intros xg. unfold YG0h.SFm, YG0h.rFm, YG0h.offF, AFkj.SFm, AFkj.rFm. rewrite reg_S1, S1_eq, upd_reg_upd_reg. unfold rg1. cbn. reflexivity. Qed.
Lemma K3F_addr : forall xg : bool, YG0h.addrF ly (St1 xg) c = fadr.
Proof. intros xg. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G24 & _). unfold YG0h.addrF, YG0h.offF. rewrite reg_S1, <- RBv_is. unfold rg1. cbn [rg_mapped_fa]. rewrite G24. unfold FAv. clear. zlia. Qed.
Lemma place_F : forall (xg : bool) (pp : Z) (mdN : Model), mf + kFreeArrayMapSize <= kFreeArrayMax ->
WfP (as_universe B) pp 0 0 (St1 xg) -> ALedger tfibsegs ly (St1 xg) mdN -> (forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) ->
if holeF xg then region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 fadr) (w64 kUserMapSize) = true
else region_free (vm_reserved (m_vmmaps mdN)) (w64 fadr) (w64 kUserMapSize) = true /\ map_contains (vm_maps (m_vmmaps mdN)) (w64 fadr) (w64 kUserMapSize) = true.
Proof.
intros xg pp mdN Ymax WP L NZ. pose proof (proj1 HAR) as MA.
assert (HFA : rg_mapped_fa (reg (St1 xg) c) + kUserMapSize <= kFreeArrayMax) by (rewrite reg_S1; unfold rg1; cbn; exact Ymax).
assert (PL : sec_placed ly (St1 xg)) by (rewrite S1_eq; unfold sec_placed; rewrite (YG0h.sec_extents_upd ly S c); exact (am_placed _ _ _ _ MA)).
unfold holeF. destruct (in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) (HO1 xg)) as [Hin|Hnin].
- pose proof (ALedger_fa_place_hole tfibsegs (as_universe B) pp 0 0 ly (St1 xg) mdN c LY WP HcR L HFA ltac:(unfold YG0h.offF; rewrite reg_S1; unfold rg1; cbn; exact Hin) PL NZ) as X.
rewrite K3F_addr in X. exact X.
- pose proof (ALedger_fa_place_piece tfibsegs (as_universe B) pp 0 0 ly (St1 xg) mdN c LY WP HcR L HFA ltac:(unfold YG0h.offF; rewrite reg_S1; unfold rg1; cbn; exact Hnin)) as X.
rewrite K3F_addr in X. exact X.
Qed.
Lemma COV_prim : forall (hole : bool) (addr : Z) (mdN : Model), amwf mdN ->
ly_prim ly <= addr -> addr + kUserMapSize <= ly_prim ly + kPrimResvSize ->
forall x, ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize) ->
YK0g.covered (vm_noaccess (m_vmmaps (grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN)) ++ m_vm_lazy (grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN)) x
= YK0g.covered (vm_noaccess (m_vmmaps mdN) ++ m_vm_lazy mdN) x.
Proof.
clear - LY. intros hole addr mdN [(A1 & A2 & A3 & _ & A5) _] H1 H2 x Hx.
pose proof (lo_high ly LY) as HI. destruct HI as [HP1 HP2].
assert (U1 : bv_unsigned (w64 addr) = addr) by (unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, bv_modulus, kHighMemBeg, ASAN_CEIL, kPrimResvSize, kUserMapSize in *; zlia]).
assert (U2 : bv_unsigned (w64 kUserMapSize) = kUserMapSize) by (unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus, kUserMapSize; zlia]).
apply (YG0j.cov_grant_md hole FL50 (w64 addr) (w64 kUserMapSize) mdN x).
- unfold YK0g.model_ivs_wf. split; [|split; [|split; [|exact A5]]]; intros q Hq; [exact (A1 q Hq) | exact (A2 q Hq) | exact (A3 q Hq)].
- rewrite U1, U2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPrimResvSize, kUserMapSize in *. zlia.
- rewrite U1, U2. intros Hin. apply Hx. zlia.
Qed.
Lemma ledger_F_grant : forall (xg : bool) (pp : Z) (mdN : Model), mf + kFreeArrayMapSize <= kFreeArrayMax ->
WfP (as_universe B) pp 0 0 (St1 xg) -> ALedger tfibsegs ly (St1 xg) mdN -> amwf mdN   ->
eager_used (grant_md (holeF xg) FL50 (w64 fadr) (w64 kUserMapSize) mdN) <= eager_used mdN + kUserMapSize ->
ALedger tfibsegs ly (SFp xg) (grant_md (holeF xg) FL50 (w64 fadr) (w64 kUserMapSize) mdN).
Proof.
intros xg pp mdN Ymax WP L MWN EG. rewrite <- K3F_p.
assert (HFA : rg_mapped_fa (reg (St1 xg) c) + kUserMapSize <= kFreeArrayMax) by (rewrite reg_S1; unfold rg1; cbn; exact Ymax).
assert (PL : sec_placed ly (St1 xg)) by (rewrite S1_eq; unfold sec_placed; rewrite (YG0h.sec_extents_upd ly S c); exact (am_placed _ _ _ _ (proj1 HAR))).
pose proof (YG0h.prim_boundsF (as_universe B) pp 0 0 ly (St1 xg) c LY WP HcR HFA) as (PB1 & PB2 & PB3 & PB4 & PB5). rewrite K3F_addr in PB3.
assert (PB6 : region_base ly c <= fadr) by (rewrite <- (K3F_addr xg); unfold YG0h.addrF; clear - PB5; unfold kFreeArrayOffset in *; zlia).
pose proof (COV_prim (holeF xg) fadr mdN MWN ltac:(clear - PB2 PB6; zlia) ltac:(clear - PB3 PB4; zlia)) as COV.
unfold holeF in *. destruct (in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) (HO1 xg)) as [Hin|Hnin].
- pose proof (grant_hole_shape (w64 fadr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
apply (ALedger_fa_granted_hole tfibsegs (as_universe B) pp 0 0 ly (St1 xg) mdN _ c LY WP HcR L RES LIM ISP PL COV (YG0g.naf_grant_md _ _ mdN _ _ MWN) HFA ltac:(unfold YG0h.offF; rewrite reg_S1; unfold rg1; cbn; exact Hin)); [|exact EG].
rewrite K3F_addr. unfold wiv. cbn [fst snd]. exact VM.
- pose proof (grant_piece_shape (w64 fadr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
apply (ALedger_fa_granted_piece tfibsegs (as_universe B) pp 0 0 ly (St1 xg) mdN _ c WP HcR L RES LIM ISP PL COV (YG0g.naf_grant_md _ _ mdN _ _ MWN) ltac:(unfold YG0h.offF; rewrite reg_S1; unfold rg1; cbn; exact Hnin) VM EG).
Qed.
Lemma WfP_SUp : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset -> WfP (as_universe B) 0 0 0 SUp.
Proof.
intros HC HR3. pose proof (WF1 (proj1 Hpum)) as W1P. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof class_facts as (_ & _ & K3 & K4 & _).
pose proof (map_more_user_ok (as_universe B) 1 0 0 S c need true W1P HcR (Z.le_refl 1) ltac:(rewrite <- Hcsz; clear - G1 G3 K4; nia) (proj1 ROOM3)  ) as AT.
destruct (E_mmu_g HC HR3) as (K & EK & K1 & _). rewrite EK in AT. cbn [atok] in AT. destruct AT as [_ AT].
specialize (AT 1 ltac:(right; reflexivity)). rewrite K1 in AT. cbn [atok] in AT. destruct AT as (r1 & _ & W1 & _). exact W1.
Qed.
Lemma WfP_St1 : forall xg : bool, XC3 xg -> WfP (as_universe B) 1 0 0 (St1 xg) \/ WfP (as_universe B) 0 0 0 (St1 xg).
Proof. intros [|] XC; [right; cbn [St1]; unfold XC3 in XC; exact (WfP_SUp (proj1 XC) (proj2 XC)) | left; exact (WF1 (proj1 Hpum))]. Qed.
Lemma place_U : forall mdN : Model, ALedger tfibsegs ly S mdN -> (forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) ->
if holeU then region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) (w64 adr) (w64 kUserMapSize) = true
else region_free (vm_reserved (m_vmmaps mdN)) (w64 adr) (w64 kUserMapSize) = true /\ map_contains (vm_maps (m_vmmaps mdN)) (w64 adr) (w64 kUserMapSize) = true.
Proof.
intros mdN L NZ. pose proof (proj1 HAR) as MA. pose proof (WF1 (proj1 Hpum)) as W1P.
unfold holeU. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol) as [Hin|Hnin].
- pose proof (ALedger_user_place_hole tfibsegs (as_universe B) 1 0 0 ly S mdN c LY W1P HcR L ltac:(unfold YG0h.offU; rewrite reg_S; cbn; exact Hin) (am_placed _ _ _ _ MA) NZ) as X.
rewrite K3U_addr in X. exact X.
- pose proof (ALedger_user_place_piece tfibsegs (as_universe B) 1 0 0 ly S mdN c LY W1P HcR L ltac:(unfold YG0h.offU; rewrite reg_S; cbn; exact Hnin)) as X.
rewrite K3U_addr in X. exact X.
Qed.
Lemma ledger_U_grant : forall mdN : Model, ALedger tfibsegs ly S mdN -> amwf mdN   ->
eager_used (grant_md holeU FL50 (w64 adr) (w64 kUserMapSize) mdN) <= eager_used mdN + kUserMapSize ->
ALedger tfibsegs ly SUp (grant_md holeU FL50 (w64 adr) (w64 kUserMapSize) mdN).
Proof.
intros mdN L MWN EG. rewrite <- K3U_p. pose proof (WF1 (proj1 Hpum)) as W1P.
pose proof (am_placed _ _ _ _ (proj1 HAR)) as PL.
pose proof (YG0h.prim_bounds (as_universe B) 1 0 0 ly S c LY W1P HcR) as (PB1 & PB2 & PB3 & PB4 & PB5). rewrite K3U_addr in PB3.
assert (PB6 : region_base ly c <= adr) by (rewrite <- K3U_addr; unfold YG0h.addrU; clear - PB5; zlia).
pose proof (COV_prim holeU adr mdN MWN ltac:(clear - PB2 PB6; zlia) ltac:(clear - PB3 PB4; unfold kFreeArrayOffset, kFreeArrayMax, kPrimResvSize in *; zlia)) as COV.
unfold holeU in *. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol) as [Hin|Hnin].
- pose proof (grant_hole_shape (w64 adr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
apply (ALedger_user_granted_hole tfibsegs (as_universe B) 1 0 0 ly S mdN _ c LY W1P HcR L RES LIM ISP PL COV (YG0g.naf_grant_md _ _ mdN _ _ MWN) ltac:(unfold YG0h.offU; rewrite reg_S; cbn; exact Hin)); [|exact EG].
rewrite K3U_addr. unfold wiv. cbn [fst snd]. exact VM.
- pose proof (grant_piece_shape (w64 adr) (w64 kUserMapSize) mdN) as (VM & RES & LIM & MMB & ISP).
apply (ALedger_user_granted_piece tfibsegs (as_universe B) 1 0 0 ly S mdN _ c W1P HcR L RES LIM ISP PL COV (YG0g.naf_grant_md _ _ mdN _ _ MWN) ltac:(unfold YG0h.offU; rewrite reg_S; cbn; exact Hnin) VM EG).
Qed.
Lemma slack_at : forall md (Wx : world tfibsegs) k, ALedger tfibsegs ly S md0 -> vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) ->
eager_used md <= eager_used md0 + k -> A_bytes (w_A Wx) <= A_bytes (w_A W) + k -> 0 <= k <= 2 ^ 20 ->
eager_used md + A_bytes (w_A Wx) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md).
Proof.
intros md Wx k L LIM EG AB Hk.
pose proof (rroom_slack _ _ ly S md0 md (A_bytes (w_A W)) (A_bytes (w_A Wx)) k WF L ltac:(clear - Hslack; unfold EV_A in Hslack; zlia) (qloosem_room S Hql) LIM EG AB (proj1 Hk)) as RS.
unfold RF_HEAD, kUserMapSize in *. clear - RS Hk. zlia.
Qed.
Definition cs_NR : list YP09.chunk := match nth_error (ss_mem R3_NR) 0 with Some r => YP09.r_chunks r | None => [] end.
Lemma NR_facts : ss_pc R3_NR = 0x6416c /\ sr_get (ss_regs R3_NR) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NR) 10%bv = SOff rADR 0 /\ sv_atoms_lt aHAV3 (SOff rADR 0) = true /\
sr_get (ss_regs R3_NR) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NR) 12%bv = SLit 0 /\ sr_get (ss_regs R3_NR) 13%bv = SLit 0x104022 /\
sr_get (ss_regs R3_NR) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NR) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NR) = true /\ nth_error (ss_mem R3_NR) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NR) /\
map skel (tl (ss_mem R3_NR)) = SKEL_TAILR /\
resume R3_NR (SLit ENOMEM_RET) (ss_mem R3_NR) (ss_facts R3_NR) = R3_NRe /\ resume R3_NR (SLit EEXIST_RET) (ss_mem R3_NR) (ss_facts R3_NR) = R3_NRx /\
resume R3_NR (SOff rADR 0) (ss_mem R3_NR) (ss_facts R3_NR) = R3_NRg.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Definition cs_NRFe : list YP09.chunk := match nth_error (ss_mem R3_NRFe) 0 with Some r => YP09.r_chunks r | None => [] end.
Lemma NRFe_facts : ss_pc R3_NRFe = 0x6416c /\ sr_get (ss_regs R3_NRFe) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NRFe) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NRFe) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NRFe) 12%bv = SLit 0 /\ sr_get (ss_regs R3_NRFe) 13%bv = SLit 0x104022 /\
sr_get (ss_regs R3_NRFe) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NRFe) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NRFe) = true /\ nth_error (ss_mem R3_NRFe) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NRFe) /\
map skel (tl (ss_mem R3_NRFe)) = SKEL_TAILR /\
resume R3_NRFe (SLit ENOMEM_RET) (ss_mem R3_NRFe) (ss_facts R3_NRFe) = R3_NRFee /\ resume R3_NRFe (SLit EEXIST_RET) (ss_mem R3_NRFe) (ss_facts R3_NRFe) = R3_NRFex /\
resume R3_NRFe (SOff rFADR 0) (ss_mem R3_NRFe) (ss_facts R3_NRFe) = R3_NRFeg.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Definition cs_NRFg : list YP09.chunk := match nth_error (ss_mem R3_NRFg) 0 with Some r => YP09.r_chunks r | None => [] end.
Lemma NRFg_facts : ss_pc R3_NRFg = 0x6416c /\ sr_get (ss_regs R3_NRFg) 17%bv = SLit 222 /\ sr_get (ss_regs R3_NRFg) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs R3_NRFg) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NRFg) 12%bv = SLit 0 /\ sr_get (ss_regs R3_NRFg) 13%bv = SLit 0x104022 /\
sr_get (ss_regs R3_NRFg) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NRFg) 15%bv = SLit 0 /\
no_cdata (ss_mem R3_NRFg) = true /\ nth_error (ss_mem R3_NRFg) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_NRFg) /\
map skel (tl (ss_mem R3_NRFg)) = SKEL_TAILR /\
resume R3_NRFg (SLit ENOMEM_RET) (ss_mem R3_NRFg) (ss_facts R3_NRFg) = R3_NRFge /\ resume R3_NRFg (SLit EEXIST_RET) (ss_mem R3_NRFg) (ss_facts R3_NRFg) = R3_NRFgx /\
resume R3_NRFg (SOff rFADR 0) (ss_mem R3_NRFg) (ss_facts R3_NRFg) = R3_NRFgg.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Lemma hol_nil : hol = [].
Proof. unfold AFkj.hol. exact (wf_noholes _ _ _ _ S c (WF1 (proj1 Hpum)) HcR). Qed.
Lemma holeU_false : holeU = false.
Proof. unfold holeU. rewrite hol_nil. destruct (in_dec zz_eq_dec (mu, kUserMapSize) []) as [[]|]; reflexivity. Qed.
Lemma holeF_false : forall xg : bool, holeF xg = false.
Proof.
intros xg. unfold holeF, AFkj.HO1. rewrite hol_nil. destruct xg; cbn [del_hole List.filter];
(destruct (in_dec zz_eq_dec (kFreeArrayOffset + mf, kFreeArrayMapSize) []) as [[]|]; reflexivity).
Qed.
Definition same_led (md md' : Model) : Prop := m_vmmaps md' = m_vmmaps md /\ m_vm_lazy md' = m_vm_lazy md.
Lemma occupied_of_place : forall (mdN mdK : Model) (a : Z), same_led mdN mdK ->
map_contains (vm_maps (m_vmmaps mdN)) (w64 a) (w64 kUserMapSize) = true ->
region_free (vm_reserved (m_vmmaps mdK) ++ vm_maps (m_vmmaps mdK)) (w64 a) (w64 kUserMapSize) = false.
Proof.
clear. intros mdN mdK a [E _] MC. rewrite E. apply kept_occupied; [| exact MC].
unfold w64. rewrite unsigned_lit_small; unfold kUserMapSize; zlia.
Qed.
Lemma free_of_destroyed : forall (mdN mdD : Model) (a : Z), YM05.ceil_of_top (alloc_top (m_vmmaps mdN)) ->
0 <= a -> a + kUserMapSize <= alloc_ceiling ->
same_led (fixedin_destroyed_model (w64 a) (w64 kUserMapSize) mdN) mdD ->
region_free (vm_reserved (m_vmmaps mdN)) (w64 a) (w64 kUserMapSize) = true ->
region_free (vm_reserved (m_vmmaps mdD) ++ vm_maps (m_vmmaps mdD)) (w64 a) (w64 kUserMapSize) = true /\
alloc_top (m_vmmaps mdD) = alloc_top (m_vmmaps mdN).
Proof.
clear. intros mdN mdD a HTOP Ha Hceil [E _] RF. rewrite E.
pose proof (YM05.ceil_le_top _ HTOP) as CT.
pose proof (alloc_top_room (m_vmmaps mdN)) as Hcv. unfold two_pow_64, stack_max_size in Hcv.
assert (Ua : bv_unsigned (w64 a) = a) by (unfold w64; apply unsigned_lit_small; unfold kUserMapSize in *; zlia).
exact (destroyed_free (w64 a) 262144 mdN ltac:(zlia) ltac:(rewrite Ua; change (page_round_up_Z 262144) with 262144; unfold kUserMapSize in Hceil; zlia) RF).
Qed.
Lemma ledger_restored : forall (S' : astate) (pp : Z) (lo : Z) (mdN mdD : Model),
WfP (as_universe B) pp 0 0 S' -> sec_placed ly S' -> ALedger tfibsegs ly S' mdN -> amwf mdN ->
(ly_prim ly <= lo /\ lo < lo + kUserMapSize /\ lo + kUserMapSize <= ly_prim ly + kPrimResvSize) ->
cut_ok ly S' lo -> cut_ok ly S' (lo + kUserMapSize) -> (forall x, cut_ok ly S' x -> ~ (lo < x < lo + kUserMapSize)) -> lo mod 4096 = 0 ->
same_led (fixedin_destroyed_model (w64 lo) (w64 kUserMapSize) mdN) mdD ->
eager_used (restore_md FLR (w64 lo) (w64 kUserMapSize) mdD) <= eager_used mdN ->
ALedger tfibsegs ly S' (restore_md FLR (w64 lo) (w64 kUserMapSize) mdD).
Proof.
intros S' pp lo mdN mdD WP PL L MWN WIN CUTlo CUThi NOCUT LOAL [EV EL] EG.
pose proof (lo_high ly LY) as HP. unfold in_high in HP. cbn [fst snd] in HP. pose proof (YG0h.prim_hi ly LY) as [C1 C2].
assert (Ulo : bv_unsigned (w64 lo) = lo) by (unfold w64; apply unsigned_lit_small; clear - WIN HP C1 C2; unfold kHighMemBeg, kUserMapSize in *; zlia).
assert (Un : bv_unsigned (w64 kUserMapSize) = kUserMapSize) by (unfold w64; apply unsigned_lit_small; unfold kUserMapSize; clear; zlia).
destruct (destroyed_shape (w64 lo) (w64 kUserMapSize) mdN) as (DM & DN & DR & DL & DB & DS & DLz & _). rewrite Ulo, Un in DM, DN, DLz.
destruct (restore_shape FLR (w64 lo) (w64 kUserMapSize) mdD) as (RM & RN & RR & RL & RB & RS & _ & RLz). rewrite noresR in RLz.
assert (LI : lazy_interior (w64 lo) (w64 kUserMapSize) = [(w64 lo, w64 kUserMapSize)]).
{ apply lazy_interior_aligned; rewrite ?Ulo, ?Un; unfold page_size;
first [exact LOAL | unfold kUserMapSize; reflexivity | clear - WIN C1 C2; unfold kUserMapSize in *; zlia]. }
rewrite LI in RLz. cbn [app] in RLz. rewrite EV in RM, RN, RR, RL, RS. rewrite EL in RLz.
destruct MWN as [(A1 & A2 & A3 & PW & A5) NZ].
assert (W64 : wiv (lo, lo + kUserMapSize - lo) = (w64 lo, w64 kUserMapSize)) by (unfold wiv; cbn [fst snd]; replace (lo + kUserMapSize - lo) with kUserMapSize by (clear; zlia); reflexivity).
apply (ALedger_restored tfibsegs (as_universe B) pp 0 0 ly S' mdN _ LY WP L) with (lo := lo) (hi := lo + kUserMapSize).
- rewrite RR, DR. reflexivity.
- rewrite RL, DL. reflexivity.
- rewrite RS, DS. reflexivity.
- exact PL.
- exact WIN.
- exact CUTlo.
- exact CUThi.
- exact NOCUT.
- intros e He. unfold uw. exact (NZ e He).
- exact (SEPS_of mdN (conj (conj A1 (conj A2 (conj A3 (conj PW A5)))) NZ)).
- exact A2.
- rewrite RM, DM, W64. reflexivity.
- rewrite RN, DN, W64. reflexivity.
-
intros x Hx. rewrite RN, RLz, DN, DLz.
assert (NR : YK0g.in_rng lo (lo + kUserMapSize) x = false).
{ unfold YK0g.in_rng. apply andb_false_iff. destruct (Z_lt_le_dec x lo); [left; apply Z.leb_gt; assumption | right; apply Z.ltb_ge; clear - WIN Hx l; zlia]. }
destruct (YK0g.maps_subtract_sem (vm_noaccess (m_vmmaps mdN)) lo (lo + kUserMapSize) ltac:(intros q Hq; exact (A2 q Hq)) ltac:(unfold kUserMapSize; clear; zlia)) as (_ & _ & Cn).
destruct (YK0g.maps_subtract_sem (m_vm_lazy mdN) lo (lo + kUserMapSize) ltac:(intros q Hq; exact (A3 q Hq)) ltac:(unfold kUserMapSize; clear; zlia)) as (_ & _ & Cl).
rewrite !YK0g.covered_app.
change (YK0g.covered ((w64 lo, w64 kUserMapSize) :: ?l) x) with (YK0g.in_iv (w64 lo, w64 kUserMapSize) x || YK0g.covered l x).
assert (IV : YK0g.in_iv (w64 lo, w64 kUserMapSize) x = false) by (unfold YK0g.in_iv, YK0g.B, YK0g.S; cbn [fst snd]; rewrite Ulo, Un; exact NR).
unfold YK0g.covered at 1 3. cbn [existsb]. rewrite IV. cbn [orb].
fold (YK0g.covered (maps_subtract (vm_noaccess (m_vmmaps mdN)) lo (lo + kUserMapSize)) x). fold (YK0g.covered (maps_subtract (m_vm_lazy mdN) lo (lo + kUserMapSize)) x).
rewrite Cn, Cl, NR. cbn [negb]. rewrite !andb_true_r. reflexivity.
- exact EG.
Qed.
Lemma LEAF_fail : forall (MU : Z) (HO : list (Z * Z)) (uq fq : bool) (Wd : world tfibsegs) mdf X P W' c' (s' : astate),
s' = SG 0 MU mf [] fr HO ->
at_RET3 Wd 0 mdf X (fun m => P m /\ P_cells Wd 0 nf mf au MU m) W' c' ->
(forall m, P m -> PF Wd 0 MU mf [] m) ->
(forall a, X a -> (sp0 - RSTACK <= a < sp0) \/ XC 0 MU mf uq fq a) ->
(forall x : word, ~ XC 0 MU mf uq fq (bv_unsigned x) -> w_H Wd x = w_H W x) ->
hsub (w_H Wd) (w_H W) -> wle W Wd -> A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20 -> (forall i, In i (w_A W) -> In i (w_A Wd))   -> same_io md0 mdf -> amwf mdf ->
ALedger tfibsegs ly s' mdf -> (MU = mu \/ (MU = mu2 /\ uq = true)) ->
(uq = true -> mu < tot /\ mu2 <= kFreeArrayOffset) -> (fq = true -> mf2 <= kFreeArrayMax) ->
LEAFW (tt, s') W' c'.
Proof.
intros MU HO uq fq Wd mdf X P W' c' s' -> HRET HPF HX HVIS HSUB LE HBUD HINC IO HMW HL HMU HUQ HFQ [ns' WFQ]. cbn [snd] in WFQ.
pose proof Hnf as [F0 F1]. pose proof Hmu as ([U0 U1] & _). pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _).
apply (LEAF_std 0 MU mf [] fr HO uq fq Wd mdf X P 0 0 nf au W' c' HRET); try assumption.
- reflexivity.
- reflexivity.
- clear; zlia.
- clear; zlia.
- clear; zlia.
- destruct HMU as [EM|[EM EQ]]; [left; split; [exact EM | clear - U0 U1; zlia] | right; split; [exact EM | split; [exact EQ | rewrite G15; clear - U0 U1; unfold kUserMapSize; zlia]]].
- left. reflexivity.
- clear - F1; zlia.
- left. split; reflexivity.
- reflexivity.
- unfold fr. exact (wr_runs _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c HcR)).
- unfold fr. rewrite <- Hnf_def. cbn. clear; zlia.
Qed.
Lemma SG_S : SG 0 mu mf [] fr hol = S.
Proof.
pose proof len_facts3 as (L1 & L2 & L3). unfold AFkm.SG, AFkm.rG, AFkm.AU. cbn [rev]. rewrite Z.mul_0_l, Z.add_0_r.
rewrite <- reg_S. rewrite upd_reg_same by ((clear - HcR; zlia) || (rewrite L1; exact L3)).
rewrite <- PM3. rewrite <- Hchunks. replace (mkPC (pc_max (cache S c)) (pc_chunks (cache S c))) with (cache S c) by (destruct (cache S c); reflexivity).
apply upd_pc_same; [clear - HcR; zlia | rewrite L2; exact L3].
Qed.
Lemma SG_upd : forall MU HO, SG 0 MU mf [] fr HO = upd_reg c (mkRegion MU au mf fr HO) S.
Proof.
intros MU HO. pose proof len_facts3 as (L1 & L2 & L3). unfold AFkm.SG, AFkm.rG, AFkm.AU. cbn [rev]. rewrite Z.mul_0_l, Z.add_0_r.
rewrite <- PM3. rewrite <- Hchunks. replace (mkPC (pc_max (cache S c)) (pc_chunks (cache S c))) with (cache S c) by (destruct (cache S c); reflexivity).
change (cache S c) with (cache (upd_reg c (mkRegion MU au mf fr HO) S) c).
apply upd_pc_same; [clear - HcR; zlia | unfold upd_reg; cbn; rewrite L2; exact L3].
Qed.
Lemma SQ_SG : forall (xg yg : bool) tops rest, XC3 xg -> SQ xg yg tops rest = SG (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg).
Proof.
intros xg yg tops rest XC. pose proof (factsX3 xg XC) as (_ & _ & N3 & _).
unfold SQ, AFkm.SG, rQ, AFkm.rG, AFkm.AU. rewrite N3. reflexivity.
Qed.
Lemma SG_ledger : forall (xg yg : bool) tops rest md, XC3 xg ->
ALedger tfibsegs ly (St2 xg yg) md -> ALedger tfibsegs ly (SG (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg)) md.
Proof.
intros xg yg tops rest md XC L. pose proof len_facts3 as (L1 & L2 & L3).
pose proof (SG_parts (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg)) as (Rreg & Rc & _ & _ & _ & Rch & _).
apply (ALedger_shape (St2 xg yg)); [| | | | | rewrite S2_eq; reflexivity | exact L].
- intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite Rc, reg_S2. unfold AFkm.rG, rg2. cbn. repeat split; reflexivity.
+ rewrite (Rreg c') by (clear - Hc' NE; zlia). rewrite S2_eq. unfold upd_reg, reg. cbn [st_regions set_regions].
rewrite znth_zupd_other; [repeat split; reflexivity | clear - HcR; zlia | clear - Hc'; zlia | congruence].
- rewrite S2_eq. reflexivity.
- rewrite S2_eq. reflexivity.
- rewrite S2_eq. unfold AFkm.SG, upd_pc, upd_reg.
match goal with |- prim_committed (set_cache ?x ?st) = _ => change (prim_committed (set_cache x st)) with (prim_committed st) end.
rewrite !prim_committed_set_region by ((clear - HcR; zlia) || (rewrite L1; exact L3)). unfold AFkm.rG, rg2. cbn [rg_mapped_user rg_mapped_fa]. reflexivity.
- rewrite S2_eq. reflexivity.
Qed.
Lemma LEAF_arm : forall (xg yg : bool) tops rest (Wd : world tfibsegs) mdf X (P : (word -> option byte) -> Prop) W' c',
XC3 xg -> (yg = true -> mf < 4 * NF1 xg /\ mf2 <= kFreeArrayMax) -> (yg = false -> 4 * NF1 xg <= mf) ->
fa_pop_n 10000 csz n (FRun au (NC1 xg) :: fr) [] = Some (tops, rest) ->
at_RET3 Wd 1 mdf X (fun m => P m /\ P_cells Wd n (NF1 xg - n) (MF2 yg) (AU1 xg) (MU1 xg) m) W' c' ->
(forall m, P m -> PF Wd (NC1 xg) (MU1 xg) (MF2 yg) tops m) ->
(forall a, X a -> (sp0 - RSTACK <= a < sp0) \/ XC (NC1 xg) (MU1 xg) (MF2 yg) xg yg a) ->
(forall x : word, ~ XC (NC1 xg) (MU1 xg) (MF2 yg) xg yg (bv_unsigned x) -> w_H Wd x = w_H W x) ->
hsub (w_H Wd) (w_H W) -> wle W Wd -> A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20 -> (forall i, In i (w_A W) -> In i (w_A Wd))   -> same_io md0 mdf -> amwf mdf ->
ALedger tfibsegs ly (St2 xg yg) mdf ->
LEAFW (tt, SQ xg yg tops rest) W' c'.
Proof.
intros xg yg tops rest Wd mdf X P W' c' XC Yg Ye EP HRET HPF HX HVIS HSUB LE HBUD HINC IO HMW HL [ns' WFQ]. cbn [snd] in WFQ.
pose proof (factsX3 xg XC) as ([N0 N1] & N2 & N3 & N4 & NN & N6 & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct (fa_pop_n_spec 10000 csz n _ [] tops rest (runs_ok_new xg XC) ltac:(clear - K3; zlia) EP) as (Eel & Erest & Eruns & Elen). cbn [rev app length Z.of_nat] in Eel, Elen.
rewrite (SQ_SG xg yg tops rest XC) in WFQ |- *.
assert (Elen' : Z.of_nat (length tops) = n) by (clear - Elen; zlia).
apply (LEAF_std (NC1 xg) (MU1 xg) (MF2 yg) tops rest (HO2 xg yg) xg yg Wd mdf X P 1 n (NF1 xg - n) (AU1 xg) W' c' HRET).
- destruct (length tops); [exfalso; clear - Elen' K3; cbn in Elen'; zlia | reflexivity].
- symmetry. exact Elen'.
- rewrite N2. clear - Elen'; zlia.
- exact N3.
- exact HPF.
- exact HX.
- exact HVIS.
- exact HSUB.
- exact LE.
- exact HBUD.
- exact HINC.
- exact IO.
- exact HMW.
- exact (SG_ledger xg yg tops rest mdf XC HL).
- exact WFQ.
- exact (conj N0 N1).
- intros ->. unfold XC3 in XC. rewrite G15. exact XC.
- intros ->. exact (proj2 (Yg eq_refl)).
- destruct xg; [right; split; [reflexivity | split; [reflexivity | exact (proj1 N4)]] | left; split; [reflexivity | exact (proj1 N4)]].
- destruct yg; [right; split; reflexivity | left; reflexivity].
- rewrite <- N2. destruct yg; cbn [MF2]; [| exact (Ye eq_refl)]. destruct (Yg eq_refl) as [Y1 Y2]. rewrite G33. rewrite N2 in Y1 |- *. unfold kFreeArrayMapSize. clear - Y1 N1 F1; zlia.
- right. exact (conj Elen' NN).
- rewrite <- fa_elems_cons_run. exact Eel.
- exact Eruns.
- rewrite Elen', <- N2. cbn [fa_len] in Erest. unfold fr in Erest |- *. rewrite <- Hnf_def in Erest. clear - Erest N2; zlia.
Qed.
Definition P1 (Wx : world tfibsegs) : (word -> option byte) -> Prop :=
fun m => (forall a, FAv <= a < FAv + mf -> apresent (w_H Wx) m a) /\ (forall a, DSTv <= a < DSTv + 64 -> apresent (w_H Wx) m a).
Lemma P1_of_frame : forall (Wx : world tfibsegs) (m : word -> option byte),
hsub (w_H Wx) (w_H W) -> (forall x : word, ~ WINR0 (bv_unsigned x) -> m x = mem0 x) -> P1 Wx m.
Proof.
intros Wx m Hs MEQ. pose proof derived_rangesR as DR. pose proof Hmf as [[M0 M1] _]. pose proof high_factsR as (F1' & F2 & _).
assert (G : forall a, 0 <= a < 2 ^ 64 -> ~ WINR0 a -> apresent (w_H W) mem0 a -> apresent (w_H Wx) m a).
{ intros a Ra Hw [Hh Hb]. split.
- destruct (w_H Wx (Z_to_bv 64 a)) eqn:E; [|reflexivity]. rewrite (Hs _ E) in Hh. discriminate Hh.
- rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ra; exact Hw). exact Hb. }
split.
- intros a Ha. apply G; [clear - Ha DR M0 M1; numconst; unfold kFreeArrayMax in *; zlia | apply fa_not_WINR0; clear - Ha M1; unfold kFreeArrayMax in *; zlia | exact (HfaPres a Ha)].
- intros a Ha. apply G; [clear - Ha DR F2; numconst; zlia | apply slots_not_WINR0; exact Ha | exact (HslotPres a Ha)].
Qed.
Lemma P1_mono : forall (Wx : world tfibsegs) (m m' : word -> option byte),
(forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P1 Wx m -> P1 Wx m'.
Proof. clear. intros Wx m m' Hm [PA PB]. split; intros a Ha; apply Hm; auto. Qed.
Lemma P1_frame : forall (Wx : world tfibsegs) (R : Z -> Prop) (m m' : word -> option byte),
(forall x : word, ~ R (bv_unsigned x) -> m' x = m x) ->
(forall a, FAv <= a < FAv + mf -> ~ R a) -> (forall a, DSTv <= a < DSTv + 64 -> ~ R a) -> P1 Wx m -> P1 Wx m'.
Proof.
intros Wx R m m' Hfr HA HB [PA PB]. pose proof derived_rangesR as DR. pose proof Hmf as [[M0 M1] _]. pose proof high_factsR as (F1' & F2 & _).
split; intros a Ha.
- eapply apresent_same; [|exact (PA a Ha)]. apply Hfr. rewrite unsigned_lit_small by (clear - Ha DR M0 M1; numconst; unfold kFreeArrayMax in *; zlia). exact (HA a Ha).
- eapply apresent_same; [|exact (PB a Ha)]. apply Hfr. rewrite unsigned_lit_small by (clear - Ha DR F2; numconst; zlia). exact (HB a Ha).
Qed.
Lemma pstable_P1 : forall Wx : world tfibsegs, pstable (P1 Wx).
Proof.
intros Wx m m' Hfr HP. pose proof Hmf as [[M0 M1] _].
apply (P1_frame Wx WINR0 m m' Hfr); [intros a Ha; apply fa_not_WINR0; clear - Ha M1; unfold kFreeArrayMax in *; zlia | intros a Ha; apply slots_not_WINR0; exact Ha | exact HP].
Qed.
Theorem refill_B3_ee : tot <= mu -> 4 * nfe <= mf -> amreal tfibsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
intros Xe Ye.
assert (XC : XC3 false) by exact Xe.
destruct (pop_new false XC) as (tops & rest & EP & Eel & Erest & Eruns & Elen).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. rewrite (E_mmu_e Xe). cbn [ibind negb].
destruct (E_getreg1 false S XC reg_e) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
unfold bind at 1. rewrite (E_efa_e false S XC reg_e Ye). cbn [ibind negb].
destruct (E_tail false false S tops rest XC reg_ee upd_e EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
eapply SRr_bind; [exact seg3P|]. intros W1 c1 _ HR1.
eapply SRr_bind; [exact (seg3Q_ok Xe W1 c1 HR1)|]. intros W2 c2 _ HR2.
eapply SRr_bind; [exact (segC1_e Xe W md0 WINR0 PT W2 c2 WX0 pstable_PT HR2)|]. intros W3 c3 _ HR3.
eapply SRr_bind; [exact (segC2e_e Xe Ye W md0 WINR0 PT W3 c3 WX0 pstable_PT HR3)|]. intros W4 c4 _ HR4.
apply (at_R3_strengthen W md0 WINR0 PT (P1 W)) in HR4; [| intros m MEQ _ _; exact (P1_of_frame W m (hsub_refl _) MEQ)].
pose proof (factsX3 false XC) as ([N0 N1] & N2 & _ & _ & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _).
assert (YC : if false then mf < 4 * NF1 false /\ mf2 <= kFreeArrayMax else 4 * NF1 false <= mf) by exact Ye.
eapply SRr_bind.
{ apply (segE1_ee Xe Ye W md0 WINR0 (P1 W) W4 c4 WX0 (pstable_P1 W)); [| | exact HR4].
- intros m [PA _] a Ha. apply PA. unfold W_FE in Ha. cbn [NF1] in Ye. clear - Ha Ye F0; zlia.
- intros m m' _ Hm. exact (P1_mono W m m' Hm). }
intros W5 c5 _ HR5.
eapply SRr_bind; [exact (segE2_ee Xe Ye W md0 _ _ W5 c5 (fun a (Ha : WINR0 a) => (or_introl Ha : WINR0 a \/ W_FE (NF1 false) a)) (pstable_fill_ee Xe Ye W (P1 W) (pstable_P1 W)) HR5)|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ apply (segE3_ee Xe Ye W md0 _ _ W6 c6 (fun a (Ha : WINR0 a) => (or_introl Ha : WINR0 a \/ W_FE (NF1 false) a)) (pstable_fill_ee Xe Ye W (P1 W) (pstable_P1 W))); [| | | exact HR6].
- intros m [[PA _] _] a Ha. apply PA. unfold SRC3_ee in Ha. cbn [NF1] in Ye, N2, N7. clear - Ha Ye F0 N2 N0 N7 K3 Hneed; zlia.
- intros m [[_ PB] _] a Ha. apply PB. unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [HPm HV]. split; [exact (P1_mono W m m' Hm HPm)|].
intros i Hi. apply (val_mem_frame_ee (w_H W) m m'); [|exact (HV i Hi)]. intros t Ht. apply Hfr. unfold W_DST.
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _). pose proof Hmf as [[M0 M1] _].
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR; numconst; unfold kFreeArrayMax in *; zlia).
unfold DSTv, Pr in *. cbn [NF1] in Ye. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR Ye. numconst. unfold kFreeArrayMax in *. try unfold T in *. try unfold SB in *. zlia. }
intros W7 c7 _ HR7.
eapply SRr_mono; [exact (segE4_ee Xe Ye W md0 _ _ W7 c7 (fun a (Ha : WINR0 a) => or_introl (or_introl Ha : WINR0 a \/ W_FE (NF1 false) a) : (WINR0 a \/ W_FE (NF1 false) a) \/ W_DST a) (pstable_cpy_ee Xe Ye _ (pstable_fill_ee Xe Ye W (P1 W) (pstable_P1 W))) HR7)|].
intros W' c' _ HRET.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _ & _ & _ & _ & _ & _ & G22 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
apply (LEAF_arm false false tops rest W md0 _ _ W' c' XC ltac:(intros E; discriminate E) (fun _ => Ye) EP HRET).
-
intros m [[[PA PB] PFI] PCP]. cbn [NC1 MU1 MF2].
split; [exact PA|]. split; [exact PB|]. split; [intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia|]. split; [intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia|].
split; [intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia|]. split; [intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia|].
split.
+ intros i Hi. replace (nf + nce) with nfe by (clear - G22; zlia). exact (PFI i Hi).
+ intros j Hj. rewrite Elen in Hj |- *. replace (nf + nce - n) with (nfe - n) by (clear - G22; zlia). exact (PCP j Hj).
-
intros a [[Hw|Hw]|Hw]; unfold AFkm.XC, AFkm.W_FEn, AFkm.NF'; cbn [NC1 MU1 MF2].
+ unfold WINR0 in Hw. clear - Hw. tauto.
+ right. do 5 right. left. unfold W_FE in Hw. rewrite <- G22. exact Hw.
+ right. right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
- intros x _. reflexivity.
- apply hsub_refl.
- apply wle_refl.
- clear. zlia.
- intros i Hi; exact Hi.
- apply same_io_refl.
- exact (proj1 (proj2 (proj2 (proj2 HAR)))).
- cbn [St2 St1]. exact (proj1 (proj2 HAR)).
Qed.
Lemma P1_hmono : forall (Wx Wy : world tfibsegs) (m : word -> option byte),
(forall y, w_H Wx y = false -> w_H Wy y = false) -> P1 Wx m -> P1 Wy m.
Proof. clear. intros Wx Wy m Hm [PA PB]. split; intros a Ha; [exact (apresent_hmono _ _ m a Hm (PA a Ha)) | exact (apresent_hmono _ _ m a Hm (PB a Ha))]. Qed.
Lemma pres_keepW : forall (Wx Wy : world tfibsegs) (m m' : word -> option byte) a,
(forall y, w_H Wx y = false -> w_H Wy y = false) -> (apresent (w_H Wy) m a -> apresent (w_H Wy) m' a) -> apresent (w_H Wx) m a -> apresent (w_H Wx) m' a.
Proof. clear. intros Wx Wy m m' a Hm Hp [Hh Hb]. destruct (Hp (conj (Hm _ Hh) Hb)) as [_ Hb']. exact (conj Hh Hb'). Qed.
Definition P_pres (W3 : world tfibsegs) (addr sh : Z) (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ (forall a, RANGE addr a -> apresent (w_H W3) m a) /\ (forall a, SHR sh a -> apresent (w_H W3) m a).
Lemma P_grant_pres : forall W3 addr sh P m, P_grant W3 addr sh P m -> P_pres W3 addr sh P m.
Proof. clear. intros W3 addr sh P m (HP & HG1 & HG2). split; [exact HP|]. split; [intros a Ha; exact (proj1 (HG1 a Ha)) | exact HG2]. Qed.
Lemma P_pres_keep : forall (W5 : world tfibsegs) addr sh (m m' : word -> option byte),
(forall y, w_H W y = false -> w_H W5 y = false) ->
(forall a, apresent (w_H W5) m a -> apresent (w_H W5) m' a) ->
P_pres W5 addr sh (P1 W) m -> P_pres W5 addr sh (P1 W) m'.
Proof.
clear. intros W5 addr sh m m' MON Hm (HP & HG1 & HG2). split; [|split].
- exact (P1_mono W m m' (fun a Ha' => pres_keepW W W5 m m' a MON (Hm a) Ha') HP).
- intros a Ha. exact (Hm a (HG1 a Ha)).
- intros a Ha. exact (Hm a (HG2 a Ha)).
Qed.
Lemma PF_fail : forall (Wd : world tfibsegs) (m : word -> option byte) (MU : Z),
P1 Wd m ->
(MU = mu2 -> (forall a, adr <= a < adr + kUserMapSize -> apresent (w_H Wd) m a) /\ (forall x : word, W_USH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250) /\ w_H Wd x = false)) ->
PF Wd 0 MU mf [] m.
Proof.
intros Wd m MU [PA PB] HU. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold PF. split; [exact PA|]. split; [exact PB|]. split; [intros E; exact (proj1 (HU E))|]. split; [intros E; exact (proj2 (HU E))|].
split; [intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia|]. split; [intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia|].
split; [intros i Hi; exfalso; clear - Hi; zlia|]. intros j Hj. exfalso. clear - Hj. cbn in Hj. zlia.
Qed.
Theorem refill_B3_eg : tot <= mu -> mf < 4 * nfe -> mf + kFreeArrayMapSize <= kFreeArrayMax -> amreal tfibsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
intros Xe Ylt Ymax.
assert (XC : XC3 false) by exact Xe.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & _ & _ & _ & _ & _ & _ & G22 & _ & G24 & G25 & _ & G27 & G28 & G29 & G30 & _ & _ & G33 & _).
pose proof (factsX3 false XC) as ([N0 N1] & N2 & _ & _ & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _). pose proof Hmf as [[M0 M1] _].
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2. pose proof derived_rangesR as DR.
assert (Ymax2 : mf2 <= kFreeArrayMax) by (rewrite G33; exact Ymax).
assert (Ylt' : mf < 4 * NF1 false) by exact Ylt.
pose proof HAR as (MA & L & BUD & MW & HS0).
destruct (pop_new false XC) as (tops & rest & EP & Eel & Erest & Eruns & Elen).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. rewrite (E_mmu_e Xe). cbn [ibind negb].
destruct (E_getreg1 false S XC reg_e) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
unfold bind at 1. destruct (E_efa_g false S XC reg_e upd_e Ylt' Ymax2) as (K & EK & K1 & K2 & K0). rewrite EK. cbn [ibind negb].
apply amreal_ask; [exact I|].
eapply SRr_bind; [exact seg3P|]. intros W1 c1 _ HR1.
eapply SRr_bind; [exact (seg3Q_ok Xe W1 c1 HR1)|]. intros W2 c2 _ HR2.
apply (at_R3_strengthen W md0 WINR0 PT (P1 W)) in HR2; [| intros m MEQ _ _; exact (P1_of_frame W m (hsub_refl _) MEQ)].
eapply SRr_bind; [exact (segC1_e Xe W md0 WINR0 (P1 W) W2 c2 WX0 (pstable_P1 W) HR2)|]. intros W3 c3 _ HR3.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (segC2g_e Xe Ylt Ymax W md0 WINR0 (P1 W) W3 c3 WX0 (pstable_P1 W) HR3))|].
intros W4 c4 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW4. subst W4.
pose proof NFe_facts as (Fpc & F17 & F10 & Fea & F11 & F12 & F13 & F14 & F15 & Fnc & Fhd & Fsk & Fres_r & Fres_g).
destruct HN as (HNw & msN & matN & EN & EcN & HNrest).
set (mdN := with_vm_backing (m_vm_lazy md0) matN md0) in *.
assert (EcM : cfg_model c4 = mdN) by (rewrite EcN; reflexivity).
assert (LN : ALedger tfibsegs ly S mdN) by (exact (ALedger_same tfibsegs ly S md0 mdN L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _))).
assert (MWN : amwf mdN) by (exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW)).
assert (NZN : forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) by (intros e He; unfold uw; apply NZ0; unfold mdN in He; rewrite m_vmmaps_wvb in He; exact He).
pose proof (WF1 (proj1 Hpum)) as W1P.
lazymatch goal with |- context [ibind (ibind (ibind (K _) ?g1) ?g2) ?g3] =>
eapply (node3 (KMapFreeArray c mf kFreeArrayMapSize) S (fun z => ibind (ibind (ibind (K z) g1) g2) g3) LEAFW W md0 WINR0 (P1 W) R3_NFe c4 (SOff rFADR 0) fadr shf (holeF false) cs_NFe
(conj HNw (ex_intro _ msN (ex_intro _ matN (ex_intro _ EN (conj EcN HNrest))))) HAI Fpc F17 F10 Fea U_fadr F11 F12 F13 F14 F15 Fnc Fhd Fsk) end.
- exact G25.
- clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia.
- clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
- exact G27.
- exact G28.
- unfold kHighShadowBeg; clear - G29; zlia.
- unfold kHighShadowEnd; clear - G30; zlia.
-   rewrite EcM. exact (place_F false 1 mdN Ymax W1P LN NZN).
- rewrite EcM. exact MWN.
-   rewrite EcM. exact (al_top _ _ _ _ LN).
- rewrite EcM. apply (slack_at mdN W 0 L); [unfold mdN; rewrite m_vmmaps_wvb; reflexivity | unfold mdN; rewrite eager_used_wvb; clear; zlia | clear; zlia | clear; zlia].
- reflexivity.
- intros z Hz. exact Hz.
-   intros m m' Hfr HP. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
apply (P1_frame W (RANGE fadr) m m' Hfr); [| | exact HP]; intros a Ha; unfold RANGE.
+ clear - Ha G24; zlia.
+ unfold DSTv, Pr in Ha. clear - Ha G24 M0 G33 Ymax2 DR TP Q1 Q2 HcR. try unfold T in *. numconst. unfold kFreeArrayMapSize, kUserMapSize in *. zlia.
-   intros a Ha. apply band_not_WINR0. unfold SHR in Ha. clear - Ha G29 G30; numconst; zlia.
-   apply (H0sh_of shf fadr); [clear - G25; apply Z.mod_divide in G25 as [q Hq]; [|zlia]; rewrite Hq; apply Z.mod_divide; [zlia|]; exists (q * 8192); zlia
| rewrite <- RBv_is; clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia | rewrite <- RBv_is; clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *; zlia
| exact G27 | unfold kHighShadowBeg; clear - G29; zlia | unfold kHighShadowEnd; clear - G30; zlia].
-   exact (holeF_false false).
-
intros W5 c'. rewrite EcM. intros md2 LE5 A5 SUB5 MON5 AI5 MW5 IO5 EG5 HEQ5 AB5 HR. cbv beta. rewrite K1. cbn [ibind negb].
destruct (E_tail false true (SFp false) tops rest XC (reg_xg false) (upd_xg false) EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
rewrite Fres_g in HR.
assert (YC : 4 * nfe <= mf2) by (rewrite G33; rewrite G22; unfold kFreeArrayMapSize; clear - F1 N1 N0; cbn [NC1] in *; zlia).
set (X5 := fun a => WINR0 a \/ RANGE fadr a) in *.
assert (HX5 : forall a, WINR0 a -> X5 a) by (intros a Ha; left; exact Ha).
apply (at_R3_weaken W5 md2 X5 X5 _ (P_pres W5 fadr shf (P1 W))) in HR; [| intros a Ha; exact Ha | intros m Hm; exact (P_grant_pres _ _ _ _ _ Hm)].
set (P5 := P_pres W5 fadr shf (P1 W)) in *.
pose proof high_factsR as (_ & _ & _ & _ & _ & Y6 & _). pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G31 & G32 & _).
assert (RNG : forall a, RANGE fadr a -> 0 <= a < 2 ^ 64 /\ FAv <= a < FAv + 2 ^ 29).
{ intros a Ha. unfold RANGE in Ha. clear - Ha G24 G31 G32 G33 Ymax2 M0 Q2 Y6. numconst. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayMax in *. zlia. }
assert (SNG : forall a, SHR shf a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg).
{ intros a Ha. unfold SHR in Ha. clear - Ha G29 G30. numconst. zlia. }
assert (PS5 : pstable P5).
{ intros m m' Hfr (HP & HG1 & HG2). split; [exact (pstable_P1 W m m' Hfr HP)|]. split.
- intros a Ha. destruct (RNG a Ha) as [Ra Fa]. eapply apresent_same; [|exact (HG1 a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra. apply fa_not_WINR0. exact Fa.
- intros a Ha. destruct (SNG a Ha) as [Ra Ba]. eapply apresent_same; [|exact (HG2 a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra. apply band_not_WINR0. exact Ba. }
eapply SRr_bind; [exact (segD_g_e W5 md2 X5 P5 W5 c' HX5 PS5 HR)|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ apply (segD_ms_e Xe W5 md2 X5 P5 W6 c6 HX5 PS5); [| | exact HR6].
- intros m (_ & _ & HG2) a Ha. apply HG2. unfold SHR. unfold W_FSH in Ha. change (kFreeArrayMapSize / 8) with 32768 in Ha. exact Ha.
- intros m m' Hfr Hm HP. exact (P_pres_keep W5 fadr shf m m' MON5 Hm HP). }
intros W7 c7 _ HR7.
assert (YCg : YCOND_eg) by (split; [exact Ylt | exact Ymax]).
set (X7 := fun a => X5 a \/ W_FSH a) in *.
assert (HX7 : forall a, WINR0 a -> X7 a) by (intros a Ha; left; left; exact Ha).
set (P7 := P_fsh_e P5) in *.
assert (PS7 : pstable P7) by exact (pstable_fsh_e P5 PS5).
eapply SRr_bind.
{ apply (segE1_eg Xe YCg W5 md2 X7 P7 W7 c7 HX7 PS7); [| | exact HR7].
-
intros m ((HP & HG1 & HG2) & _) a Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ apply (apresent_hmono (w_H W) (w_H W5) m a MON5). apply (proj1 HP). unfold W_FE in Ha. clear - Ha Lo F0 F1; zlia.
+ apply (HG1 a). unfold RANGE. unfold W_FE in Ha. clear - Ha Hi YC G24 G33; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m m' Hfr Hm [HP HF]. split; [exact (P_pres_keep W5 fadr shf m m' MON5 Hm HP)|].
intros x Hx. rewrite (Hfr x); [exact (HF x Hx)|]. intros Hw. unfold W_FE in Hw. unfold W_FSH in Hx. change (kFreeArrayMapSize / 8) with 32768 in Hx.
clear - Hw Hx G29 G30 DR F0. numconst. zlia. }
intros W8 c8 _ HR8.
set (X8 := fun a => X7 a \/ W_FE nfe a) in *. set (P8 := P_fill_eg W5 P7) in *.
assert (HX8 : forall a, WINR0 a -> X8 a) by (intros a Ha; left; exact (HX7 a Ha)).
assert (PS8 : pstable P8) by exact (pstable_fill_eg Xe YCg W5 P7 PS7).
eapply SRr_bind; [exact (segE2_eg Xe YCg W5 md2 X8 P8 W8 c8 HX8 PS8 HR8)|]. intros W9 c9 _ HR9.
eapply SRr_bind.
{ apply (segE3_eg Xe YCg W5 md2 X8 P8 W9 c9 HX8 PS8); [| | | exact HR9].
- intros m [[(HP & HG1 & HG2) _] _] a Ha. unfold SRC3_eg in Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ apply (apresent_hmono (w_H W) (w_H W5) m a MON5). apply (proj1 HP). clear - Ha Lo F0 F1 N2 N7 N0 K3 Hneed; cbn [NF1 NC1] in *; zlia.
+ apply (HG1 a). unfold RANGE. clear - Ha Hi YC G24 G33 K3; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m [[(HP & _ & _) _] _] a Ha. apply (apresent_hmono (w_H W) (w_H W5) m a MON5). apply (proj2 HP). unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [[HP HF] HV]. split; [split; [exact (P_pres_keep W5 fadr shf m m' MON5 Hm HP)|]|].
+ intros x Hx. rewrite (Hfr x); [exact (HF x Hx)|]. intros Hw. unfold W_DST in Hw. unfold W_FSH in Hx. change (kFreeArrayMapSize / 8) with 32768 in Hx.
pose proof high_factsR as (Fz & _). clear - Hw Hx G29 G30 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros i Hi. apply (val_mem_frame_eg (w_H W5) m m'); [|exact (HV i Hi)]. intros t Ht. apply Hfr. unfold W_DST.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _).
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR G33 Ymax2; numconst; unfold kFreeArrayMax, kFreeArrayMapSize in *; zlia).
unfold DSTv, Pr in *. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR YC G33 Ymax2. numconst. unfold kFreeArrayMax, kFreeArrayMapSize in *. try unfold T in *. try unfold SB in *. zlia. }
intros W10 c10 _ HR10.
eapply SRr_mono; [exact (segE4_eg Xe YCg W5 md2 (fun a => X8 a \/ W_DST a) (P_cpy_eg P8) W10 c10 (fun a Ha => or_introl (HX8 a Ha)) (pstable_cpy_eg Xe YCg _ PS8) HR10)|].
intros W' c'' _ HRET.
unfold MUX_eg, MFY_eg in HRET. rewrite <- G33 in HRET.
apply (LEAF_arm false true tops rest W5 md2 _ _ W' c'' XC (fun _ => conj Ylt Ymax2) ltac:(intros E; discriminate E) EP HRET).
+
intros m [[[(HP & HG1 & HG2) HF] HV] HC]. cbn [NC1 MU1 MF2].
split; [intros a Ha; exact (apresent_hmono (w_H W) (w_H W5) m a MON5 (proj1 HP a Ha))|].
split; [intros a Ha; exact (apresent_hmono (w_H W) (w_H W5) m a MON5 (proj2 HP a Ha))|].
split; [intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia|]. split; [intros E; exfalso; clear - E G15; unfold kUserMapSize in G15; zlia|].
split; [intros _ a Ha; apply HG1; unfold RANGE, kUserMapSize, kFreeArrayMapSize in *; exact Ha|].
split. { intros _ x Hx. split; [exact (HF x Hx)|]. pose proof (proj1 (HG2 (bv_unsigned x) ltac:(unfold SHR; unfold W_FSH in Hx; change (kFreeArrayMapSize / 8) with 32768 in Hx; exact Hx))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. exact Hh. }
split.
* intros i Hi. replace (nf + nce) with nfe by (clear - G22; zlia). exact (HV i Hi).
* intros j Hj. rewrite Elen in Hj |- *. unfold SRC3_eg in HC. replace (nf + nce - n) with (nfe - n) by (clear - G22; zlia). exact (HC j Hj).
+
intros a [[[[Hw|Hw]|Hw]|Hw]|Hw]; unfold AFkm.XC, AFkm.W_FEn, AFkm.NF'; cbn [NC1 MU1 MF2].
* unfold WINR0 in Hw. clear - Hw. tauto.
* do 9 right. left. split; [reflexivity|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. exact Hw.
* do 10 right. split; [reflexivity | exact Hw].
* do 6 right. left. unfold W_FE in Hw. rewrite <- G22. exact Hw.
* do 2 right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
+
intros x NX. apply HEQ5; intros Hw; apply NX; unfold AFkm.XC; cbn [NC1 MU1 MF2].
* do 8 right. left. split; [reflexivity|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. exact Hw.
* do 9 right. split; [reflexivity|]. unfold W_FSH, SHR in *. change (kFreeArrayMapSize / 8) with 32768. exact Hw.
+ exact SUB5.
+ exact LE5.
+ rewrite AB5. clear. unfold kUserMapSize. zlia.
+ intros i Hi. rewrite A5. do 2 right. exact Hi.
+ exact IO5.
+ exact MW5.
+ cbn [St2]. exact (ledger_F_grant false 1 mdN Ymax W1P LN MWN EG5).
-   rewrite EcM. apply same_io_with_vm_backing.
Qed.
Lemma P1_of_frameX : forall (Wx : world tfibsegs) (X : Z -> Prop) (m : word -> option byte),
hsub (w_H Wx) (w_H W) -> (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) ->
(forall a, FAv <= a < FAv + mf -> ~ X a) -> (forall a, DSTv <= a < DSTv + 64 -> ~ X a) -> P1 Wx m.
Proof.
intros Wx X m Hs MEQ NA NB. pose proof derived_rangesR as DR. pose proof Hmf as [[M0 M1] _]. pose proof high_factsR as (F1' & F2 & _).
assert (G : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> apresent (w_H W) mem0 a -> apresent (w_H Wx) m a).
{ intros a Ra Hw [Hh Hb]. split.
- destruct (w_H Wx (Z_to_bv 64 a)) eqn:E; [|reflexivity]. rewrite (Hs _ E) in Hh. discriminate Hh.
- rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ra; exact Hw). exact Hb. }
split.
- intros a Ha. apply G; [clear - Ha DR M0 M1; numconst; unfold kFreeArrayMax in *; zlia | exact (NA a Ha) | exact (HfaPres a Ha)].
- intros a Ha. apply G; [clear - Ha DR F2; numconst; zlia | exact (NB a Ha) | exact (HslotPres a Ha)].
Qed.
Theorem refill_B3_g : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset -> amreal tfibsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
intros Xlt XR3.
assert (XC : XC3 true) by exact (conj Xlt XR3). assert (XCg : XCOND_g) by exact (conj Xlt XR3).
pose proof facts3 as (_ & _ & _ & _ & _ & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & _ & _ & _ & _ & _ & _ & G22 & G23 & G24 & G25 & _ & G27 & G28 & G29 & G30 & _ & _ & G33 & _).
assert (XR2 : mu2 <= kFreeArrayOffset) by (rewrite G15; exact XR3).
pose proof (factsX3 true XC) as ([N0 N1] & N2 & _ & _ & N7 & _). pose proof Hnf as [F0 F1]. pose proof class_facts as (_ & _ & K3 & _). pose proof Hmf as [[M0 M1] _].
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2. pose proof derived_rangesR as DR. pose proof high_factsR as (_ & _ & _ & _ & _ & Y6 & _).
pose proof HAR as (MA & L & BUD & MW & HS0). pose proof (WF1 (proj1 Hpum)) as W1P.
destruct (pop_new true XC) as (tops & rest & EP & Eel & Erest & Eruns & Elen).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. destruct (E_mmu_g Xlt XR3) as (K & EK & K1 & K2 & K0). rewrite EK. cbn [ibind negb].
apply amreal_ask; [exact I|].
eapply SRr_bind; [exact seg3P|]. intros W1 c1 _ HR1.
eapply SRr_bind; [exact (seg3Q_map Xlt W1 c1 HR1)|]. intros W2 c2 _ HR2.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (seg3M Xlt XR3 W2 c2 HR2))|].
intros W4 c4 _ [HAI HN]. pose proof (proj1 HN) as EW4. subst W4.
pose proof NU_facts as (Fpc & F17 & F10 & Fea & F11 & F12 & F13 & F14 & F15 & Fnc & Fhd & Fsk & Fres_r & Fres_g).
destruct HN as (HNw & msN & matN & EN & EcN & HNrest).
set (mdN := with_vm_backing (m_vm_lazy md0) matN md0) in *.
assert (EcM : cfg_model c4 = mdN) by (rewrite EcN; reflexivity).
assert (LN : ALedger tfibsegs ly S mdN) by (exact (ALedger_same tfibsegs ly S md0 mdN L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _))).
assert (MWN : amwf mdN) by (exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW)).
assert (NZN : forall e, In e (vm_maps (m_vmmaps mdN)) -> 0 < uw (snd e)) by (intros e He; unfold uw; apply NZ0; unfold mdN in He; rewrite m_vmmaps_wvb in He; exact He).
assert (RNGU : forall a, RANGE adr a -> 0 <= a < 2 ^ 64 /\ RBv + mu <= a < RBv + mu2 /\ kHighMemBeg <= a) by (intros a Ha; unfold RANGE in Ha; clear - Ha G6 G7 G10 G15 Q2 Y6; numconst; unfold kUserMapSize in *; zlia).
assert (SNGU : forall a, SHR sha a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg) by (intros a Ha; unfold SHR in Ha; clear - Ha G13 G14; numconst; zlia).
assert (NAU : forall a, FAv <= a < FAv + mf -> ~ RANGE adr a) by (intros a Ha Hr; unfold RANGE in Hr; clear - Ha Hr G10 G15 XR3 DR; unfold kUserMapSize in *; zlia).
assert (NBU : forall a, DSTv <= a < DSTv + 64 -> ~ RANGE adr a).
{ pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
intros a Ha Hr. unfold RANGE in Hr. unfold DSTv, Pr in Ha. clear - Ha Hr G9 G7 Q1 Q2 DR TP HcR. try unfold T in *. numconst. unfold kUserMapSize in *. zlia. }
lazymatch goal with |- context [ibind (ibind (ibind (K _) ?g1) ?g2) ?g3] =>
eapply (node3 (KMapUser c mu kUserMapSize) S (fun z => ibind (ibind (ibind (K z) g1) g2) g3) LEAFW W md0 WINR0 PT R3_NU c4 (SOff rADR 0) adr sha holeU cs_NU
(conj HNw (ex_intro _ msN (ex_intro _ matN (ex_intro _ EN (conj EcN HNrest))))) HAI Fpc F17 F10 Fea U_adr F11 F12 F13 F14 F15 Fnc Fhd Fsk) end.
- exact G8.
- exact G9.
- exact G7.
- exact G11.
- exact G12.
- unfold kHighShadowBeg; clear - G13; zlia.
- unfold kHighShadowEnd; clear - G14; zlia.
- rewrite EcM. exact (place_U mdN LN NZN).
- rewrite EcM. exact MWN.
-   rewrite EcM. exact (al_top _ _ _ _ LN).
- rewrite EcM. apply (slack_at mdN W 0 L); [unfold mdN; rewrite m_vmmaps_wvb; reflexivity | unfold mdN; rewrite eager_used_wvb; clear; zlia | clear; zlia | clear; zlia].
- reflexivity.
- intros z Hz. exact Hz.
- intros m m' _ _. exact I.
- intros a Ha. apply band_not_WINR0. exact (proj2 (SNGU a Ha)).
- apply (H0sh_of sha adr); [clear - G8; apply Z.mod_divide in G8 as [q Hq]; [|zlia]; rewrite Hq; apply Z.mod_divide; [zlia|]; exists (q * 8192); zlia
| rewrite <- RBv_is; exact G9 | rewrite <- RBv_is; exact G7 | exact G11 | unfold kHighShadowBeg; clear - G13; zlia | unfold kHighShadowEnd; clear - G14; zlia].
-   exact holeU_false.
-
intros W3 c'. rewrite EcM. intros md2 LE3 A3 SUB3 MON3 AI3 MW2 IO2 EG2 HEQ3 AB3 HR. cbv beta. rewrite K1. cbn [ibind negb].
destruct (E_getreg1 true SUp XC reg_g) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
rewrite Fres_g in HR.
assert (LUp : ALedger tfibsegs ly SUp md2) by exact (ledger_U_grant mdN LN MWN EG2).
assert (WUp : WfP (as_universe B) 0 0 0 SUp) by exact (WfP_SUp Xlt XR3).
assert (NZ2 : forall e, In e (vm_maps (m_vmmaps md2)) -> 0 < uw (snd e)).
{ intros e He. unfold md2, holeU in He. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol).
- rewrite (proj1 (grant_hole_shape (w64 adr) (w64 kUserMapSize) mdN)) in He. destruct He as [<-|He]; [|exact (NZN e He)].
unfold uw, w64. cbn [snd]. rewrite unsigned_lit_small; unfold kUserMapSize; clear; zlia.
- rewrite (proj1 (grant_piece_shape (w64 adr) (w64 kUserMapSize) mdN)) in He. exact (NZN e He). }
assert (LIM2 : vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps md0)).
{ unfold md2, holeU. destruct (in_dec zz_eq_dec (mu, kUserMapSize) hol);
[rewrite (proj1 (proj2 (proj2 (grant_hole_shape (w64 adr) (w64 kUserMapSize) mdN)))) | rewrite (proj1 (proj2 (proj2 (grant_piece_shape (w64 adr) (w64 kUserMapSize) mdN))))]; unfold mdN; rewrite m_vmmaps_wvb; reflexivity. }
assert (EGd : eager_used md2 <= eager_used md0 + kUserMapSize) by (unfold mdN in EG2; rewrite eager_used_wvb in EG2; exact EG2).
set (XG := fun a => WINR0 a \/ RANGE adr a) in *.
assert (HXG : forall a, WINR0 a -> XG a) by (intros a Ha; left; exact Ha).
apply (at_R3_strengthen W3 md2 XG _ (P_pres W3 adr sha (P1 W))) in HR.
2:{ intros m MEQ _ HG. split; [| exact (proj2 (P_grant_pres _ _ _ _ _ HG))].
apply (P1_of_frameX W XG m (hsub_refl _) MEQ); intros a Ha [Hw|Hw]; [exact (fa_not_WINR0 a ltac:(clear - Ha M1; unfold kFreeArrayMax in *; zlia) Hw) | exact (NAU a Ha Hw) | exact (slots_not_WINR0 a Ha Hw) | exact (NBU a Ha Hw)]. }
set (PG0 := P_pres W3 adr sha (P1 W)) in *.
assert (PSG0 : pstable PG0).
{ intros m m' Hfr (HP & HG1 & HG2). split; [exact (pstable_P1 W m m' Hfr HP)|]. split.
- intros a Ha. destruct (RNGU a Ha) as (Ra & Fa & Ka). eapply apresent_same; [|exact (HG1 a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra.
intros Hw. unfold WINR0 in Hw. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & S2 & _). pose proof high_factsR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NOSTK).
destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; [apply (proj2 (NOSTK a ltac:(clear - Hw S1 S2; unfold RSTACK in *; zlia))); clear - Fa Q1 Q2 G15 XR3 Hmu; numconst; unfold kUserMapSize in *; zlia | | | |];
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP; unfold zdisjoint in TP; cbn [fst snd] in TP; clear - Hw Fa Q1 Q2 DR TP HcR G15 XR3 Hmu; unfold Pr, RGv in *; try unfold T in *; try unfold SB in *; numconst; unfold kUserMapSize in *; zlia.
- intros a Ha. destruct (SNGU a Ha) as [Ra Ba]. eapply apresent_same; [|exact (HG2 a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra. apply band_not_WINR0. exact Ba. }
set (XK := fun a => XG a \/ W_USH a) in *. set (PG := P_ush PG0) in *.
assert (HXK : forall a, WINR0 a -> XK a) by (intros a Ha; left; left; exact Ha).
assert (PSG : pstable PG) by exact (pstable_ush PG0 PSG0).
assert (PRE : SRr tfibsegs W3 c' (at_R3 W3 md2 XK PG R3_Dg3)).
{ eapply SRr_bind; [exact (seg3_Ug W3 md2 XG PG0 W3 c' HXG PSG0 HR)|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ apply (seg3_Ums W3 md2 XG PG0 W6 c6 HXG PSG0); [| | exact HR6].
- intros m (_ & _ & HG2) a Ha. apply HG2. unfold SHR. unfold W_USH in Ha. change (kUserMapSize / 8) with 32768 in Ha. exact Ha.
- intros m m' Hfr Hm HP. exact (P_pres_keep W3 adr sha m m' MON3 Hm HP). }
intros W7 c7 _ HR7. exact (segC1_g XCg W3 md2 XK PG W7 c7 HXK PSG HR7). }
destruct (Z_lt_le_dec mf (4 * nfg)) as [Ylt|Yge].
2:{
unfold bind at 1. rewrite (E_efa_e true SUp XC reg_g Yge). cbn [ibind negb].
destruct (E_tail true false SUp tops rest XC (reg_ge) upd_g EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
eapply SRr_bind; [exact PRE|]. intros W8 c8 _ HR8.
assert (YCge : YCOND_ge) by exact Yge.
eapply SRr_bind; [exact (segC2e_g XCg Yge W3 md2 XK PG W8 c8 HXK PSG HR8)|]. intros W9 c9 _ HR9.
eapply SRr_bind.
{ apply (segE1_ge XCg YCge W3 md2 XK PG W9 c9 HXK PSG); [| | exact HR9].
- intros m ((HP & _ & _) & _) a Ha. apply (apresent_hmono (w_H W) (w_H W3) m a MON3). apply (proj1 HP). unfold W_FE in Ha. clear - Ha Yge F0; zlia.
- intros m m' Hfr Hm [HP HU]. split; [exact (P_pres_keep W3 adr sha m m' MON3 Hm HP)|].
intros x Hx. rewrite (Hfr x); [exact (HU x Hx)|]. intros Hw. unfold W_FE in Hw. unfold W_USH in Hx. change (kUserMapSize / 8) with 32768 in Hx.
clear - Hw Hx G13 G14 DR F0. numconst. zlia. }
intros W10 c10 _ HR10.
set (X10 := fun a => XK a \/ W_FE nfg a) in *. set (P10 := P_fill_ge W3 PG) in *.
assert (HX10 : forall a, WINR0 a -> X10 a) by (intros a Ha; left; exact (HXK a Ha)).
assert (PS10 : pstable P10) by exact (pstable_fill_ge XCg YCge W3 PG PSG).
eapply SRr_bind; [exact (segE2_ge XCg YCge W3 md2 X10 P10 W10 c10 HX10 PS10 HR10)|]. intros W11 c11 _ HR11.
eapply SRr_bind.
{ apply (segE3_ge XCg YCge W3 md2 X10 P10 W11 c11 HX10 PS10); [| | | exact HR11].
- intros m [[(HP & _ & _) _] _] a Ha. unfold SRC3_ge in Ha. apply (apresent_hmono (w_H W) (w_H W3) m a MON3). apply (proj1 HP). clear - Ha Yge F0 N2 N7 N0 K3 Hneed; cbn [NF1 NC1] in *; zlia.
- intros m [[(HP & _ & _) _] _] a Ha. apply (apresent_hmono (w_H W) (w_H W3) m a MON3). apply (proj2 HP). unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [[HP HU] HV]. split; [split; [exact (P_pres_keep W3 adr sha m m' MON3 Hm HP)|]|].
+ intros x Hx. rewrite (Hfr x); [exact (HU x Hx)|]. intros Hw. unfold W_DST in Hw. unfold W_USH in Hx. change (kUserMapSize / 8) with 32768 in Hx.
pose proof high_factsR as (Fz & _). clear - Hw Hx G13 G14 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros i Hi. apply (val_mem_frame_ge (w_H W3) m m'); [|exact (HV i Hi)]. intros t Ht. apply Hfr. unfold W_DST.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _).
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR; numconst; unfold kFreeArrayMax in *; zlia).
unfold DSTv, Pr in *. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR Yge. numconst. unfold kFreeArrayMax in *. try unfold T in *. try unfold SB in *. zlia. }
intros W12 c12 _ HR12.
eapply SRr_mono; [exact (segE4_ge XCg YCge W3 md2 (fun a => X10 a \/ W_DST a) (P_cpy_ge P10) W12 c12 (fun a Ha => or_introl (HX10 a Ha)) (pstable_cpy_ge XCg YCge _ PS10) HR12)|].
intros W' c'' _ HRET.
unfold MUX_ge, MFY_ge in HRET. rewrite <- G15 in HRET.
apply (LEAF_arm true false tops rest W3 md2 _ _ W' c'' XC ltac:(intros E; discriminate E) (fun _ => Yge) EP HRET).
+ intros m [[[(HP & HG1 & HG2) HU] HV] HC]. cbn [NC1 MU1 MF2].
split; [intros a Ha; exact (apresent_hmono (w_H W) (w_H W3) m a MON3 (proj1 HP a Ha))|].
split; [intros a Ha; exact (apresent_hmono (w_H W) (w_H W3) m a MON3 (proj2 HP a Ha))|].
split; [intros _ a Ha; apply HG1; unfold RANGE; exact Ha|].
split. { intros _ x Hx. split; [exact (HU x Hx)|]. pose proof (proj1 (HG2 (bv_unsigned x) ltac:(unfold SHR; unfold W_USH in Hx; change (kUserMapSize / 8) with 32768 in Hx; exact Hx))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. exact Hh. }
split; [intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia|]. split; [intros E; exfalso; clear - E G33; unfold kFreeArrayMapSize in G33; zlia|].
split.
* intros i Hi. replace (nf + ncg) with nfg by (clear - G23; zlia). exact (HV i Hi).
* intros j Hj. rewrite Elen in Hj |- *. unfold SRC3_ge in HC. replace (nf + ncg - n) with (nfg - n) by (clear - G23; zlia). exact (HC j Hj).
+ intros a [[[[Hw|Hw]|Hw]|Hw]|Hw]; unfold AFkm.XC, AFkm.W_FEn, AFkm.NF'; cbn [NC1 MU1 MF2].
* unfold WINR0 in Hw. clear - Hw. tauto.
* do 7 right. left. split; [reflexivity|]. unfold W_UW, RANGE in *. exact Hw.
* do 8 right. left. split; [reflexivity | exact Hw].
* do 6 right. left. unfold W_FE in Hw. rewrite <- G23. exact Hw.
* do 2 right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
+ intros x NX. apply HEQ3; intros Hw; apply NX; unfold AFkm.XC; cbn [NC1 MU1 MF2].
* do 6 right. left. split; [reflexivity|]. unfold W_UW, RANGE in *. exact Hw.
* do 7 right. left. split; [reflexivity|]. unfold W_USH, SHR in *. change (kUserMapSize / 8) with 32768. exact Hw.
+ exact SUB3.
+ exact LE3.
+ rewrite AB3. clear. unfold kUserMapSize. zlia.
+ intros i Hi. rewrite A3. do 2 right. exact Hi.
+ exact IO2.
+ exact MW2.
+ cbn [St2 St1]. exact LUp. }
destruct (Z_lt_le_dec kFreeArrayMax mf2) as [Yfail|Ymax2].
{
unfold bind at 1. destruct (E_efa_fail true SUp XC reg_g Ylt Yfail) as [f Ef]. rewrite Ef. cbn [ibind negb amreal]. exact I. }
assert (Ymax : mf + kFreeArrayMapSize <= kFreeArrayMax) by (rewrite <- G33; exact Ymax2).
assert (Ylt' : mf < 4 * NF1 true) by exact Ylt.
assert (YCgg : YCOND_gg) by exact (conj Ylt Ymax).
unfold bind at 1. destruct (E_efa_g true SUp XC reg_g upd_g Ylt' Ymax2) as (KF & EKF & KF1 & KF2 & KF0). rewrite EKF. cbn [ibind negb].
apply amreal_ask; [exact I|].
eapply SRr_bind; [exact PRE|]. intros W8 c8 _ HR8.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (segC2g_g XCg Ylt Ymax W3 md2 XK PG W8 c8 HXK PSG HR8))|].
intros W9 c9 _ [HAI9 HN9]. pose proof (proj1 HN9) as EW9. subst W9.
pose proof NFg_facts as (Fpc' & F17' & F10' & Fea' & F11' & F12' & F13' & F14' & F15' & Fnc' & Fhd' & Fsk' & Fres_r' & Fres_g').
destruct HN9 as (HNw' & msN' & matN' & EN' & EcN' & HNrest').
set (mdN' := with_vm_backing (m_vm_lazy md2) matN' md2) in *.
assert (EcM' : cfg_model c9 = mdN') by (rewrite EcN'; reflexivity).
assert (LN' : ALedger tfibsegs ly SUp mdN') by (exact (ALedger_same tfibsegs ly SUp md2 mdN' LUp (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _))).
assert (MWN' : amwf mdN') by (exact (amwf_same md2 mdN' (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2)).
assert (NZN' : forall e, In e (vm_maps (m_vmmaps mdN')) -> 0 < uw (snd e)) by (intros e He; apply NZ2; unfold mdN' in He; rewrite m_vmmaps_wvb in He; exact He).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G31 & G32 & _).
assert (RNG : forall a, RANGE fadr a -> 0 <= a < 2 ^ 64 /\ FAv + mf <= a < FAv + 2 ^ 29).
{ intros a Ha. unfold RANGE in Ha. clear - Ha G24 G31 G32 G33 Ymax2 M0 Q2 Y6. numconst. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayMax in *. zlia. }
assert (SNG : forall a, SHR shf a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg).
{ intros a Ha. unfold SHR in Ha. clear - Ha G29 G30. numconst. zlia. }
assert (SHsep : sha + 32768 <= shf).
{ rewrite G11, G27. clear - G7 G8 G10 G15 G24 XR3 DR M0. apply Z.mod_divide in G8 as [q Hq]; [|zlia]. rewrite Hq at 1. replace (q * 65536) with (q * 8192 * 8) by zlia. rewrite Z.div_mul by zlia.
assert (X : q * 8192 * 8 + 262144 <= fadr) by (unfold kUserMapSize, kFreeArrayOffset in *; zlia).
assert (Y : (q * 8192 * 8 + 262144) / 8 <= fadr / 8) by (apply Z.div_le_mono; [zlia | exact X]).
replace (q * 8192 * 8 + 262144) with ((q * 8192 + 32768) * 8) in Y by zlia. rewrite Z.div_mul in Y by zlia. zlia. }
assert (PG_keep : forall (W5 : world tfibsegs) (R : Z -> Prop) (m m' : word -> option byte),
(forall y, w_H W3 y = false -> w_H W5 y = false) ->
(forall x : word, ~ R (bv_unsigned x) -> m' x = m x) -> (forall a, W_USH a -> ~ R a) ->
(forall a, apresent (w_H W5) m a -> apresent (w_H W5) m' a) -> PG m -> PG m').
{ intros W5 R m m' MON Hfr HRu Hm [HP HU]. split.
- destruct HP as (HP1 & HG1 & HG2). split; [|split].
+ exact (P1_mono W m m' (fun a Ha' => pres_keepW W W5 m m' a (fun y Hy => MON y (MON3 y Hy)) (Hm a) Ha') HP1).
+ intros a Ha. exact (pres_keepW W3 W5 m m' a MON (Hm a) (HG1 a Ha)).
+ intros a Ha. exact (pres_keepW W3 W5 m m' a MON (Hm a) (HG2 a Ha)).
- intros x Hx. rewrite (Hfr x); [exact (HU x Hx) | exact (HRu _ Hx)]. }
assert (HPuG : forall m m' : word -> option byte, (forall x : word, ~ RANGE fadr (bv_unsigned x) -> m' x = m x) -> PG m -> PG m').
{
intros m m' Hfr [(HP1 & HG1 & HG2) HU].
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
split; [split; [|split]|].
* apply (P1_frame W (RANGE fadr) m m' Hfr); [| | exact HP1]; intros a Ha; unfold RANGE.
-- clear - Ha G24; zlia.
-- unfold DSTv, Pr in Ha. clear - Ha G24 M0 G33 Ymax2 DR TP Q1 Q2 HcR. try unfold T in *. numconst. unfold kFreeArrayMapSize, kUserMapSize in *. zlia.
* intros a Ha. destruct (RNGU a Ha) as (Ra & Fa & _). eapply apresent_same; [|exact (HG1 a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra. unfold RANGE. clear - Fa G24 G15 XR3 DR M0. unfold kUserMapSize, kFreeArrayOffset in *. zlia.
* intros a Ha. destruct (SNGU a Ha) as [Ra Ba]. eapply apresent_same; [|exact (HG2 a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra. unfold RANGE. clear - Ba G31. numconst. zlia.
* intros x Hx. rewrite (Hfr x); [exact (HU x Hx)|]. unfold RANGE. unfold W_USH in Hx. change (kUserMapSize / 8) with 32768 in Hx. clear - Hx G13 G14 G31. numconst. zlia. }
lazymatch goal with |- context [ibind (ibind (ibind (KF _) ?g1) ?g2) ?g3] =>
eapply (node3 (KMapFreeArray c mf kFreeArrayMapSize) SUp (fun z => ibind (ibind (ibind (KF z) g1) g2) g3) LEAFW W3 md2 XK PG R3_NFg c9 (SOff rFADR 0) fadr shf (holeF true) cs_NFg
(conj HNw' (ex_intro _ msN' (ex_intro _ matN' (ex_intro _ EN' (conj EcN' HNrest'))))) HAI9 Fpc' F17' F10' Fea' U_fadr F11' F12' F13' F14' F15' Fnc' Fhd' Fsk') end.
+ exact G25.
+ clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia.
+ clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
+ exact G27.
+ exact G28.
+ unfold kHighShadowBeg; clear - G29; zlia.
+ unfold kHighShadowEnd; clear - G30; zlia.
+ rewrite EcM'. exact (place_F true 0 mdN' Ymax WUp LN' NZN').
+ rewrite EcM'. exact MWN'.
+   rewrite EcM'. exact (al_top _ _ _ _ LN').
+ rewrite EcM'. apply (slack_at mdN' W3 (kUserMapSize + 32768) L); [unfold mdN'; rewrite m_vmmaps_wvb; exact LIM2 | unfold mdN'; rewrite eager_used_wvb; clear - EGd; zlia | rewrite AB3; clear; zlia | unfold kUserMapSize; clear; zlia].
+ reflexivity.
+ intros z Hz. exact Hz.
+ exact HPuG.
+
intros a Ha [[Hw|Hw]|Hw]; [exact (band_not_WINR0 a (proj2 (SNG a Ha)) Hw) | |].
* destruct (RNGU a Hw) as (_ & _ & Ka). pose proof (SNG a Ha) as [_ Ba]. clear - Ka Ba. zlia.
* unfold SHR in Ha. unfold W_USH in Hw. change (kUserMapSize / 8) with 32768 in Hw. clear - Ha Hw SHsep. zlia.
+ apply (H0sh_of shf fadr); [clear - G25; apply Z.mod_divide in G25 as [q Hq]; [|zlia]; rewrite Hq; apply Z.mod_divide; [zlia|]; exists (q * 8192); zlia
| rewrite <- RBv_is; clear - G24 DR M0; unfold kFreeArrayOffset in *; zlia | rewrite <- RBv_is; clear - G24 G33 Ymax2 DR; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *; zlia
| exact G27 | unfold kHighShadowBeg; clear - G29; zlia | unfold kHighShadowEnd; clear - G30; zlia].
+   exact (holeF_false true).
+
intros W5 c'9. rewrite EcM'. intros md4 LE5 A5 SUB5 MON5 AI5 MW5 IO5 EG5 HEQ5 AB5 HR9. cbv beta. rewrite KF1. cbn [ibind negb].
destruct (E_tail true true (SFp true) tops rest XC (reg_xg true) (upd_xg true) EP) as (ET1 & ET2 & ET3).
rewrite ET1. cbn [ibind negb]. rewrite ET2. cbn [ibind]. rewrite ET3. cbn [amreal].
rewrite Fres_g' in HR9.
assert (YC : 4 * nfg <= mf2) by (rewrite G33; rewrite G23; unfold kFreeArrayMapSize; clear - F1 N1 N0; cbn [NC1] in *; zlia).
assert (MON35 : forall y, w_H W y = false -> w_H W5 y = false) by (intros y Hy; exact (MON5 y (MON3 y Hy))).
set (X5 := fun a => XK a \/ RANGE fadr a) in *.
assert (HX5 : forall a, WINR0 a -> X5 a) by (intros a Ha; left; exact (HXK a Ha)).
apply (at_R3_weaken W5 md4 X5 X5 _ (P_pres W5 fadr shf PG)) in HR9; [| intros a Ha; exact Ha | intros m Hm; exact (P_grant_pres _ _ _ _ _ Hm)].
set (P5 := P_pres W5 fadr shf PG) in *.
assert (P5_keep : forall (R : Z -> Prop) (m m' : word -> option byte),
(forall x : word, ~ R (bv_unsigned x) -> m' x = m x) -> (forall a, W_USH a -> ~ R a) ->
(forall a, apresent (w_H W5) m a -> apresent (w_H W5) m' a) -> P5 m -> P5 m').
{ intros R m m' Hfr HRu Hm (HP & HF1' & HF2'). split; [exact (PG_keep W5 R m m' MON5 Hfr HRu Hm HP)|]. split; intros a Ha; [exact (Hm a (HF1' a Ha)) | exact (Hm a (HF2' a Ha))]. }
assert (PS5 : pstable P5).
{ intros m m' Hfr (HP & HF1' & HF2'). split; [exact (PSG m m' Hfr HP)|]. split.
- intros a Ha. destruct (RNG a Ha) as [Ra Fa]. eapply apresent_same; [|exact (HF1' a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra. apply fa_not_WINR0. clear - Fa M0; zlia.
- intros a Ha. destruct (SNG a Ha) as [Ra Ba]. eapply apresent_same; [|exact (HF2' a Ha)]. apply Hfr. rewrite unsigned_lit_small by exact Ra. apply band_not_WINR0. exact Ba. }
eapply SRr_bind; [exact (segD_g_g W5 md4 X5 P5 W5 c'9 HX5 PS5 HR9)|]. intros W6 c6 _ HR6.
eapply SRr_bind.
{ apply (segD_ms_g XCg W5 md4 X5 P5 W6 c6 HX5 PS5); [| | exact HR6].
- intros m (_ & _ & HF2') a Ha. apply HF2'. unfold SHR. unfold W_FSH in Ha. change (kFreeArrayMapSize / 8) with 32768 in Ha. exact Ha.
- intros m m' Hfr Hm HP. apply (P5_keep W_FSH m m' Hfr); [|exact Hm|exact HP]. intros a Ha Hb. unfold W_USH in Ha. unfold W_FSH in Hb. change (kUserMapSize / 8) with 32768 in Ha. clear - Ha Hb SHsep; zlia. }
intros W7 c7 _ HR7.
set (X7 := fun a => X5 a \/ W_FSH a) in *.
assert (HX7 : forall a, WINR0 a -> X7 a) by (intros a Ha; left; exact (HX5 a Ha)).
set (P7 := P_fsh_g P5) in *.
assert (PS7 : pstable P7) by exact (pstable_fsh_g P5 PS5).
eapply SRr_bind.
{ apply (segE1_gg XCg YCgg W5 md4 X7 P7 W7 c7 HX7 PS7); [| | exact HR7].
- intros m [[[[HP1 _] _] [HF1' _]] _] a Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ apply (apresent_hmono (w_H W) (w_H W5) m a MON35). apply (proj1 HP1). unfold W_FE in Ha. clear - Ha Lo F0 F1; zlia.
+ apply (HF1' a). unfold RANGE. unfold W_FE in Ha. clear - Ha Hi YC G24 G33; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m m' Hfr Hm [HP HFS]. split.
+ apply (P5_keep (W_FE nfg) m m' Hfr); [|exact Hm|exact HP]. intros a Ha Hb. unfold W_USH in Ha. unfold W_FE in Hb. change (kUserMapSize / 8) with 32768 in Ha. clear - Ha Hb G13 G14 DR F0. numconst. zlia.
+ intros x Hx. rewrite (Hfr x); [exact (HFS x Hx)|]. intros Hw. unfold W_FE in Hw. unfold W_FSH in Hx. change (kFreeArrayMapSize / 8) with 32768 in Hx. clear - Hw Hx G29 G30 DR F0. numconst. zlia. }
intros W10 c10 _ HR10.
set (X10 := fun a => X7 a \/ W_FE nfg a) in *. set (P10 := P_fill_gg W5 P7) in *.
assert (HX10 : forall a, WINR0 a -> X10 a) by (intros a Ha; left; exact (HX7 a Ha)).
assert (PS10 : pstable P10) by exact (pstable_fill_gg XCg YCgg W5 P7 PS7).
eapply SRr_bind; [exact (segE2_gg XCg YCgg W5 md4 X10 P10 W10 c10 HX10 PS10 HR10)|]. intros W11 c11 _ HR11.
eapply SRr_bind.
{ apply (segE3_gg XCg YCgg W5 md4 X10 P10 W11 c11 HX10 PS10); [| | | exact HR11].
- intros m [[[[[HP1 _] _] [HF1' _]] _] _] a Ha. unfold SRC3_gg in Ha. destruct (Z_lt_le_dec a (FAv + mf)) as [Lo|Hi].
+ apply (apresent_hmono (w_H W) (w_H W5) m a MON35). apply (proj1 HP1). clear - Ha Lo F0 F1 N2 N7 N0 K3 Hneed; cbn [NF1 NC1] in *; zlia.
+ apply (HF1' a). unfold RANGE. clear - Ha Hi YC G24 G33 K3; unfold kUserMapSize, kFreeArrayMapSize in *; zlia.
- intros m [[[[[HP1 _] _] _] _] _] a Ha. apply (apresent_hmono (w_H W) (w_H W5) m a MON35). apply (proj2 HP1). unfold W_DST in Ha. clear - Ha K3; zlia.
- intros m m' Hfr Hm [[HP HFS] HV]. split; [split|].
+ apply (P5_keep W_DST m m' Hfr); [|exact Hm|exact HP]. intros a Ha Hb. unfold W_USH in Ha. unfold W_DST in Hb. change (kUserMapSize / 8) with 32768 in Ha. pose proof high_factsR as (Fz & _). clear - Ha Hb G13 G14 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros x Hx. rewrite (Hfr x); [exact (HFS x Hx)|]. intros Hw. unfold W_DST in Hw. unfold W_FSH in Hx. change (kFreeArrayMapSize / 8) with 32768 in Hx. pose proof high_factsR as (Fz & _). clear - Hw Hx G29 G30 DR K3 Fz HcR. unfold DSTv, Pr, t_cache in *. try unfold T in *. numconst. zlia.
+ intros i Hi. apply (val_mem_frame_gg (w_H W5) m m'); [|exact (HV i Hi)]. intros t Ht. apply Hfr. unfold W_DST.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & _).
cbn [NF1 NC1] in *. rewrite unsigned_lit_small by (clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR G33 Ymax2; numconst; unfold kFreeArrayMax, kFreeArrayMapSize in *; zlia).
unfold DSTv, Pr in *. clear - Hi Ht N0 N1 N2 F0 F1 M0 M1 DR F1' F2 F4 F5 TP K3 HcR YC G33 Ymax2. numconst. unfold kFreeArrayMax, kFreeArrayMapSize in *. try unfold T in *. try unfold SB in *. zlia. }
intros W12 c12 _ HR12.
eapply SRr_mono; [exact (segE4_gg XCg YCgg W5 md4 (fun a => X10 a \/ W_DST a) (P_cpy_gg P10) W12 c12 (fun a Ha => or_introl (HX10 a Ha)) (pstable_cpy_gg XCg YCgg _ PS10) HR12)|].
intros W' c'' _ HRET.
unfold MUX_gg, MFY_gg in HRET. rewrite <- G15, <- G33 in HRET.
apply (LEAF_arm true true tops rest W5 md4 _ _ W' c'' XC (fun _ => conj Ylt Ymax2) ltac:(intros E; discriminate E) EP HRET).
* intros m [[[[[(HP1 & HGU1 & HGU2) HU] [HF1' HF2']] HFS] HV] HC]. cbn [NC1 MU1 MF2].
split; [intros a Ha; exact (apresent_hmono (w_H W) (w_H W5) m a MON35 (proj1 HP1 a Ha))|].
split; [intros a Ha; exact (apresent_hmono (w_H W) (w_H W5) m a MON35 (proj2 HP1 a Ha))|].
split; [intros _ a Ha; exact (apresent_hmono (w_H W3) (w_H W5) m a MON5 (HGU1 a Ha))|].
split. { intros _ x Hx. split; [exact (HU x Hx)|]. pose proof (proj1 (HGU2 (bv_unsigned x) ltac:(unfold SHR; unfold W_USH in Hx; change (kUserMapSize / 8) with 32768 in Hx; exact Hx))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. exact (MON5 _ Hh). }
split; [intros _ a Ha; apply HF1'; unfold RANGE, kUserMapSize, kFreeArrayMapSize in *; exact Ha|].
split. { intros _ x Hx. split; [exact (HFS x Hx)|]. pose proof (proj1 (HF2' (bv_unsigned x) ltac:(unfold SHR; unfold W_FSH in Hx; change (kFreeArrayMapSize / 8) with 32768 in Hx; exact Hx))) as Hh.
rewrite Z_to_bv_bv_unsigned in Hh. exact Hh. }
split.
-- intros i Hi. replace (nf + ncg) with nfg by (clear - G23; zlia). exact (HV i Hi).
-- intros j Hj. rewrite Elen in Hj |- *. unfold SRC3_gg in HC. replace (nf + ncg - n) with (nfg - n) by (clear - G23; zlia). exact (HC j Hj).
* intros a [[[[[[Hw|Hw]|Hw]|Hw]|Hw]|Hw]|Hw]; unfold AFkm.XC, AFkm.W_FEn, AFkm.NF'; cbn [NC1 MU1 MF2].
-- unfold WINR0 in Hw. clear - Hw. tauto.
-- do 7 right. left. split; [reflexivity|]. unfold W_UW, RANGE in *. exact Hw.
-- do 8 right. left. split; [reflexivity | exact Hw].
-- do 9 right. left. split; [reflexivity|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. exact Hw.
-- do 10 right. split; [reflexivity | exact Hw].
-- do 6 right. left. unfold W_FE in Hw. rewrite <- G23. exact Hw.
-- do 2 right. left. unfold W_DST in Hw. clear - Hw K3. zlia.
* intros x NX. rewrite (HEQ5 x); [apply HEQ3|..]; intros Hw; apply NX; unfold AFkm.XC; cbn [NC1 MU1 MF2].
-- do 6 right. left. split; [reflexivity|]. unfold W_UW, RANGE in *. exact Hw.
-- do 7 right. left. split; [reflexivity|]. unfold W_USH, SHR in *. change (kUserMapSize / 8) with 32768. exact Hw.
-- do 8 right. left. split; [reflexivity|]. unfold W_FW, RANGE, kUserMapSize, kFreeArrayMapSize in *. exact Hw.
-- do 9 right. split; [reflexivity|]. unfold W_FSH, SHR in *. change (kFreeArrayMapSize / 8) with 32768. exact Hw.
* intros a Ha. exact (SUB3 _ (SUB5 _ Ha)).
* exact (wle_trans _ _ _ _ LE3 LE5).
* rewrite AB5, AB3. clear. unfold kUserMapSize. zlia.
* intros i Hi. rewrite A5. do 2 right. rewrite A3. do 2 right. exact Hi.
* exact IO5.
* exact MW5.
* cbn [St2]. exact (ledger_F_grant true 0 mdN' Ymax WUp LN' MWN' EG5).
+ rewrite EcM'. exact (same_io_trans _ _ _ IO2 (same_io_with_vm_backing _ _ _)).
- rewrite EcM. apply same_io_with_vm_backing.
Qed.
Theorem refill_B3_W : amreal tfibsegs (refill_tree c S) W cfg0 LEAFW.
Proof.
destruct (Z_lt_le_dec mu tot) as [Xlt|Xe].
- destruct (Z_lt_le_dec kFreeArrayOffset (mu + kUserMapSize)) as [XF|XR3]; [|exact (refill_B3_g Xlt XR3)].
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. destruct (E_mmu_fail Xlt XF) as [f Ef]. rewrite Ef. cbn [ibind negb amreal]. exact I.
- destruct (Z_lt_le_dec mf (4 * nfe)) as [Ylt|Ye]; [|exact (refill_B3_ee Xe Ye)].
destruct (Z_lt_le_dec kFreeArrayMax (mf + kFreeArrayMapSize)) as [YF|Ymax]; [|exact (refill_B3_eg Xe Ylt Ymax)].
assert (XC : XC3 false) by exact Xe.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct E_tree as [ET EG]. rewrite ET. unfold bind at 1. rewrite EG. unfold bind at 1. rewrite E_pop.
unfold bind at 1. rewrite (E_mmu_e Xe). cbn [ibind negb].
destruct (E_getreg1 false S XC reg_e) as (EG1 & ENF & ENC & EAU).
unfold bind at 1. rewrite EG1. cbn [ibind]. rewrite ENF, ENC.
unfold bind at 1. destruct (E_efa_fail false S XC reg_e Ylt ltac:(rewrite G33; exact YF)) as [f Ef]. rewrite Ef. cbn [ibind negb amreal]. exact I.
Qed.
Theorem refill_B3 : amreal tfibsegs (refill_tree c S) W cfg0 LEAFQ.
Proof.
apply (amreal_atok _ true _ W cfg0 LEAFQ (refill_tree_ok true)).
eapply amreal_mono; [|exact refill_B3_W]. intros [u s'] W' c' H [ns' WF']. destruct u. exact (H (ex_intro _ ns' WF')).
Qed.
End g.
End d.

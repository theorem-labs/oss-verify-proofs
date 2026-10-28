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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhm AFka AFk9 AFkk AFkb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
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
Section f.
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
Definition XCOND_ge : Prop := mu < tot /\ mu + kUserMapSize <= kFreeArrayOffset.
Definition MUX_ge : Z := (mu + kUserMapSize).
Definition MFY_ge : Z := mf.
Definition YCOND_ge : Prop := 4 * nfg <= mf.
Definition SRC3_ge : Z := FAv + 4 * (nfg - n).
Ltac get_facts3 :=
pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 &
G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32 & G33 & G34 & G35 & G36 & G37).
Lemma factsX_ge : XCOND_ge ->
0 <= ncg < 2 ^ 16 /\ nfg = nf + ncg /\ aug = au + ncg * csz /\ aug mod 16 = 0 /\
ncg * csz <= MUX_ge - au < ncg * csz + csz /\ need <= ncg /\ 0 <= MUX_ge - au < 2 ^ 32 /\ MUX_ge <= kFreeArrayOffset.
Proof.
intros HC. get_facts3. pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). unfold XCOND_ge, MUX_ge in *.
split; [clear - G18 G21; zlia|]. split; [exact G23|]. split; [exact G35|]. split; [exact G37|]. split; [rewrite <- G15; exact G19|].
destruct HC as [HC HR3]. split; [| clear - U0 U1 U2 HR3; numconst; unfold kUserMapSize in *; zlia].
assert (L : need * csz < ncg * csz + csz) by (clear - HC G3 G5 G15 G19 U0 U1; unfold kMaxSize, kUserMapSize in *; zlia).
clear - L K4 G1 G18. nia.   Qed.
Lemma factsY_ge : XCOND_ge -> YCOND_ge -> 4 * nfg <= MFY_ge /\ MFY_ge <= kFreeArrayMax /\ 0 <= MFY_ge.
Proof.
intros HC HY. pose proof (factsX_ge HC) as ([N0 N1] & N2 & _). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] M2]. unfold YCOND_ge, MFY_ge in *.
clear - HY N0 N1 N2 F0 F1 M0 M1. zlia.       Qed.
Ltac sv_zev :=
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl);
cbn [zev zalu_raw zmd_raw]; unfold rho_of end.
Lemma val_mem_frame_ge : forall (Hh : word -> bool) (m m' : word -> option byte) a (k : nat) v,
(forall t, (t < k)%nat -> m' (Z_to_bv 64 (a + Z.of_nat t)) = m (Z_to_bv 64 (a + Z.of_nat t))) ->
val_mem tfibsegs (mrestrict Hh m) a k v -> val_mem tfibsegs (mrestrict Hh m') a k v.
Proof. clear3. intros Hh m m' a k v Hfr Hv t Ht. rewrite <- (Hv t Ht). apply mbyte_mrestrict_same. apply Hfr. exact Ht. Qed.
Definition P_fill_ge (Wx : world tfibsegs) (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ forall i, 0 <= i < ncg -> val_mem tfibsegs (mrestrict (w_H Wx) m) (FAv + 4 * nfg - 4 - 4 * i) 4 ((au + i * csz) / 16).
Lemma pstable_fill_ge : XCOND_ge -> YCOND_ge -> forall Wx P, pstable P -> pstable (P_fill_ge Wx P).
Proof.
intros HC HY Wx P HP m m' Hfr [H1 H2]. pose proof (factsX_ge HC) as ([N0 N1] & N2 & _). pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR.
split; [exact (HP m m' Hfr H1)|].
intros i Hi. apply (val_mem_frame_ge (w_H Wx) m m'); [|exact (H2 i Hi)]. intros t Ht. apply Hfr.
rewrite unsigned_lit_small by (clear - Hi Ht N0 N1 N2 F0 F1 Y1 Y2 DR; numconst; unfold kFreeArrayMax in *; zlia).
apply fa_not_WINR0. clear - Hi Ht N0 N1 N2 F0 F1 Y1 Y2; unfold kFreeArrayMax in *; zlia.
Qed.
Lemma segE1_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
(forall m, P m -> forall a, W_FE nfg a -> apresent (w_H Wx) m a) ->
(forall m m' : word -> option byte, (forall x : word, ~ W_FE nfg (bv_unsigned x) -> m' x = m x) -> (forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P m -> P m') ->
at_R3 Wx md X P R3_FILLge W' c' ->
SRr tfibsegs W' c' (at_R3 Wx md (fun a => X a \/ W_FE nfg a) (P_fill_ge Wx P) R3_Tge0).
Proof.
intros HC HY Wx md X P W' c' HX HP HPfe HPu HR. get_facts3. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9).
pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). unfold MUX_ge in *.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (S1 & S2 & S3 & S4 & S5).
pose proof stack_ext_ok3 as [SX1 SX2].
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
rreg HS (10%bv : bv 5) R10. rregS HS (11%bv : bv 5) R11. rreg HS (12%bv : bv 5) R12. rreg HS (21%bv : bv 5) R21. rreg HS (19%bv : bv 5) R19.
rewrite (HEn 46%nat ltac:(cbv; zlia)), EaAU in R12. rewrite (HEn 40%nat ltac:(cbv; zlia)), EaCSZ in R21. rewrite (HEn 61%nat ltac:(cbv; zlia)), EaNCg in R19.
assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 (FAv + 4 * nfg)).
{ rewrite R11. sv_zev. rewrite (HEn 42%nat ltac:(cbv; zlia)), (HEn 63%nat ltac:(cbv; zlia)), EaRB, EaNFg. unfold w64.
clear - N0 N1 N2 F0 F1 Y1 Y2 DR. numconst. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small RBv), (unsigned_lit_small nfg) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id (RBv + 3758096384)), (zcanon_id nfg) by (unfold M64; zlia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4. rewrite (zcanon_id (nfg * 4)) by (unfold M64; zlia). rewrite zcanon_id by (unfold M64; zlia). zlia. }
eapply (popfree_stretch Wx hPF E' R3_FILLge ms _ (FAv + 4 * nfg) au csz ncg);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| exact R10 | exact R11' | exact R12 | exact R21 | exact R19
| clear - N7 G1; zlia | clear - N0 N2 F0 DR; numconst; zlia | clear - N0 N1 N2 F0 F1 Y1 Y2 DR; numconst; unfold kFreeArrayMax in *; zlia
| clear - U0; zlia | clear - K4; zlia | clear - N5 N9 U0 U1; numconst; nia | clear - N0 N2 F0 DR; numconst; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia
| intros a Ha; apply (HPfe _ HPm a); unfold W_FE; clear - Ha N2; zlia
| intros r Hr | intros r a Hr | ].
1-2: cbn [ss_mem] in Hr; destruct Hr as [<-|Hr];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn 2%nat ltac:(cbv; zlia)), E2;
clear - N0 N1 N2 F0 F1 Y1 Y2 DR S4 S5 SX1 SX2; numconst; unfold kFreeArrayMax in *; try unfold sp0 in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILR in Hr by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7); clear - N0 N1 N2 F0 F1 Y1 Y2 DR X1 X2 X3 X4 X5 X6 X7; numconst; unfold kFreeArrayMax in *; zlia ].
intros regs3 mem3 mat3 HS3 Hfr3 Hpr3 Hval3. rewrite wvb_collapse.
replace (FAv + 4 * nfg - 4 * ncg) with (FAv + 4 * nf) in Hfr3 by (clear - N2; zlia).
assert (HR : at_R3 Wx md (fun a => X a \/ W_FE nfg a) (P_fill_ge Wx P) R3_Tge0 Wx
(mkCfg (mkst regs3 (Z_to_bv 64 0x366e8) mem3 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat3 md))).
{ split; [reflexivity|]. exists (mkst regs3 (Z_to_bv 64 0x366e8) mem3 (seg_rom tfibsegs)), mat3, (havoc E' hPF (map (getr regs3) CLOB_PF)).
split; [reflexivity|]. split; [exact (env_agree_havoc_ge aHAV3 hPF E0 E' _ ltac:(unfold aHAV3, hPF; zlia) HE)|].
split; [exact HS3|]. cbn [ms_mem mkst]. split; [|split].
- intros x Hx. rewrite (Hfr3 x) by (intros Hw; apply Hx; right; exact Hw). apply MEQ. intros H; apply Hx; left; exact H.
- intros a Ha. apply Hpr3. exact (PRS a Ha).
- split; [exact (HPu (ms_mem ms) mem3 Hfr3 Hpr3 HPm) | exact Hval3]. }
apply SRr_ret. exact HR.
Qed.
Lemma segE2_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P R3_Tge0 W' c' -> SRr tfibsegs W' c' (at_R3 Wx md X P R3_Cge0).
Proof.
intros HC HY Wx md X P W' c' HX HP HR. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9). unfold MUX_ge in *.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] _].
pose proof facts3 as (G1 & _).
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x366f8 (runto 0x366f8 R3_Tge0) HX HP.
r3_pin HR (13%bv : bv 5) (SOff rAUg 0).
{ pin_zev3. unfold rAUg, rAU, rNCg, rCSZ. rewrite EaAUg, EaAU, EaNCg, EaCSZ. unfold w64. clear - N0 N1 N3 N5 N8 N9 K4 U0 U1. numconst. unfold kMaxSize in *.
rewrite (unsigned_lit_small aug), (unsigned_lit_small au), (unsigned_lit_small ncg), (unsigned_lit_small csz) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id aug), (zcanon_id au), (zcanon_id ncg), (zcanon_id csz) by (unfold M64; zlia).
rewrite (zcanon_id (ncg * csz)) by (unfold M64; nia). rewrite zcanon_id by (unfold M64; zlia). zlia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x366fc (runto 0x366fc R3_Tge1) HX HP.
r3_pin HR (10%bv : bv 5) (SOff rNFg 0).
{ pin_zev3. unfold rNFg, rNF, rNCg. rewrite EaNFg, EaNF, EaNCg. unfold w64.
clear - N0 N1 N2 F0 F1 M0 M1. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small nfg), (unsigned_lit_small nf), (unsigned_lit_small ncg) by zlia.
rewrite !Z.add_0_r. rewrite (zcanon_id nfg), (zcanon_id nf), (zcanon_id ncg) by (unfold M64; zlia). rewrite zcanon_id by (unfold M64; zlia). zlia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36704 R3_Tge3 HX HP.
r3_arm HR BC_LTU false (SOff rMU 262144) (SOff rAUg 0).     { arm_zev3. unfold rMU, rAUg. rewrite EaMU, EaAUg. unfold w64. clear - N0 K4 N3 N5 N8 N9 U0 U1 U2. numconst.
rewrite (unsigned_lit_small mu), (unsigned_lit_small aug) by nia. rewrite ?Z.add_0_r.
rewrite !zcanon_id by (unfold M64; nia). apply Z.ltb_ge. nia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x364cc (runto 0x364cc (arm BC_LTU false (SOff rMU 262144) (SOff rAUg 0) R3_Tge3)) HX HP.     r3_arm HR BC_LTU false (SOff rNFg 0) (SOff rN 0).
{ arm_zev3. unfold rNFg, rN. rewrite EaNFg, EaN. unfold w64. clear - N0 N1 N2 N7 F0 F1 M0 M1 K3 Hneed. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small nfg), (unsigned_lit_small n) by zlia. rewrite ?Z.add_0_r.
rewrite !zcanon_id by (unfold M64; zlia). apply Z.ltb_ge. zlia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36378 R3_Cge0 HX HP.
apply SRr_ret. exact HR.
Qed.
Definition P_cpy_ge (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ forall j, 0 <= j < 4 * n -> m (w64 (DSTv + j)) = m (w64 (SRC3_ge + j)).
Lemma pstable_cpy_ge : XCOND_ge -> YCOND_ge -> forall P, pstable P -> pstable (P_cpy_ge P).
Proof.
intros HC HY P HP m m' Hfr [H1 H2]. pose proof (factsX_ge HC) as ([N0 N1] & N2 & _ & _ & _ & N7 & _). pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). pose proof high_factsR as (F1' & F2 & _).
split; [exact (HP m m' Hfr H1)|].
intros j Hj. unfold w64, SRC3_ge in *. rewrite !Hfr; [exact (H2 j Hj) | |].
- rewrite unsigned_lit_small by (clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed; numconst; unfold kFreeArrayMax in *; zlia).
apply fa_not_WINR0. clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 K3 Hneed; unfold kFreeArrayMax in *; zlia.
- rewrite unsigned_lit_small by (clear - Hj DR K3 F2; numconst; zlia). apply slots_not_WINR0. clear - Hj K3; zlia.
Qed.
Lemma segE3_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
(forall m, P m -> forall a, SRC3_ge <= a < SRC3_ge + 4 * n -> apresent (w_H Wx) m a) ->
(forall m, P m -> forall a, W_DST a -> apresent (w_H Wx) m a) ->
(forall m m' : word -> option byte, (forall x : word, ~ W_DST (bv_unsigned x) -> m' x = m x) -> (forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P m -> P m') ->
at_R3 Wx md X P R3_Cge0 W' c' ->
SRr tfibsegs W' c' (at_R3 Wx md (fun a => X a \/ W_DST a) (P_cpy_ge P) R3_Cge).
Proof.
intros HC HY Wx md X P W' c' HX HP HPfe HPdst HPu HR. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9).
pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). unfold MUX_ge in *.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (S1 & S2 & S3 & S4 & S5).
pose proof stack_ext_ok3 as [SX1 SX2].
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as TP. unfold zdisjoint in TP. cbn [fst snd] in TP.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
rregS HS (20%bv : bv 5) R20. rreg HS (13%bv : bv 5) R13. rregS HS (11%bv : bv 5) R11.
assert (R20' : getr (ms_regs ms) 20 = Z_to_bv 64 SRC3_ge).
{ rewrite R20. sv_zev. rewrite (HEn 39%nat ltac:(cbv; zlia)), (HEn 43%nat ltac:(cbv; zlia)), (HEn 63%nat ltac:(cbv; zlia)), EaN, EaFA, EaNFg. unfold w64, SRC3_ge.
clear - N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed. numconst. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small n), (unsigned_lit_small FAv), (unsigned_lit_small nfg) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id n), (zcanon_id FAv), (zcanon_id nfg) by (unfold M64; zlia). change (zcanon 18446744073709551612) with (2 ^ 64 - 4).
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4. rewrite (zcanon_id (nfg * 4)) by (unfold M64; zlia).
unfold zcanon, M64. rewrite (Zplus_mod_idemp_l (n * (2 ^ 64 - 4))), Zplus_mod_idemp_l.
replace (n * (2 ^ 64 - 4) + FAv + nfg * 4) with ((FAv + nfg * 4 - 4 * n) + n * 2 ^ 64) by zlia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by zlia. zlia. }
assert (R13' : getr (ms_regs ms) 13 = Z_to_bv 64 DSTv).
{ rewrite R13, (HEn 37%nat ltac:(cbv; zlia)), EaP. unfold w64, DSTv. rewrite Zbv_add_unsigned. reflexivity. }
assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 (DSTv + 4 * n)).
{ rewrite R11. sv_zev. rewrite (HEn 37%nat ltac:(cbv; zlia)), (HEn 39%nat ltac:(cbv; zlia)), EaP, EaN. unfold w64, DSTv.
clear - DR K3 F2. numconst. rewrite (unsigned_lit_small Pr), (unsigned_lit_small n) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id (Pr + 16)), (zcanon_id n) by (unfold M64; zlia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4.
rewrite (zcanon_id (n * 4)) by (unfold M64; zlia). rewrite zcanon_id by (unfold M64; zlia). zlia. }
eapply (cpy4_stretch Wx hCP E' R3_Cge0 ms _ DSTv SRC3_ge (4 * n));
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| exact R20' | exact R13' | exact R11'
| clear - K3; zlia | clear - K3; rewrite Z.mul_comm; apply Z_mod_mult
| clear - DR; unfold DSTv in *; numconst; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia | clear - DR K3 F2; unfold DSTv in *; numconst; zlia
| clear - N0 N2 N7 F0 DR Hneed; unfold SRC3_ge in *; numconst; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia | clear - N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed; unfold SRC3_ge in *; numconst; unfold kFreeArrayMax in *; zlia
| clear - N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed F1' F2 F4 F5 TP S1; unfold SRC3_ge, DSTv, Pr in *; numconst; unfold kFreeArrayMax in *; try unfold T in *; try unfold SB in *; zlia
| intros a Ha; apply (HPdst _ HPm a); unfold W_DST; exact Ha
| intros a Ha; exact (HPfe _ HPm a Ha)
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|Hr];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn 2%nat ltac:(cbv; zlia)), E2;
clear - DR K3 F1' F2 S1 S4 S5; unfold DSTv, Pr in *; numconst; try unfold sp0 in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILR in Hr by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7); clear - DR K3 F2 X1 X2 X3 X4 X5 X6 X7; numconst; zlia ].
intros regs3 mem3 mat3 HS3 Hfr3 Hpr3 Hcp3. rewrite wvb_collapse.
assert (HR : at_R3 Wx md (fun a => X a \/ W_DST a) (P_cpy_ge P) R3_Cge Wx
(mkCfg (mkst regs3 (Z_to_bv 64 0x3638c) mem3 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat3 md))).
{ split; [reflexivity|]. exists (mkst regs3 (Z_to_bv 64 0x3638c) mem3 (seg_rom tfibsegs)), mat3, (havoc E' hCP (map (getr regs3) CLOB_CP3)).
split; [reflexivity|]. split; [exact (env_agree_havoc_ge aHAV3 hCP E0 E' _ ltac:(unfold aHAV3, hCP; zlia) HE)|].
split; [exact HS3|]. cbn [ms_mem mkst]. split; [|split].
- intros x Hx. rewrite (Hfr3 x) by (intros Hw; apply Hx; right; exact Hw). apply MEQ. intros H; apply Hx; left; exact H.
- intros a Ha. apply Hpr3. exact (PRS a Ha).
- split; [exact (HPu (ms_mem ms) mem3 Hfr3 Hpr3 HPm) |].
intros j Hj. rewrite (Hcp3 j Hj). symmetry. apply Hfr3. unfold w64, W_DST.
rewrite unsigned_lit_small by (clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed; unfold SRC3_ge in *; numconst; unfold kFreeArrayMax in *; zlia).
clear - Hj N0 N1 N2 N7 F0 F1 Y1 Y2 DR K3 Hneed F1' F2 F4 F5 TP S1; unfold SRC3_ge, DSTv, Pr in *; numconst; unfold kFreeArrayMax in *; try unfold T in *; try unfold SB in *; zlia. }
apply SRr_ret. exact HR.
Qed.
Lemma segE4_ge : XCOND_ge -> YCOND_ge -> forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P R3_Cge W' c' -> SRr tfibsegs W' c' (at_RET3 Wx 1 md X (fun m => P m /\ P_cells Wx n (nfg - n) MFY_ge aug MUX_ge m)).
Proof.
intros HC HY Wx md X P W' c' HX HP HR. pose proof (factsX_ge HC) as ([N0 N1] & N2 & N3 & N4 & [N5 N6] & N7 & N8 & N9).
pose proof (factsY_ge HC HY) as (Y1 & Y2 & Y3). get_facts3.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] _].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1' & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 R3_RETge HX HP.
eapply (at_R3_ret Wx md X _ R3_RETge _ _ 1); [| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| unfold CSAVED; repeat (apply Forall_cons; [vm_compute; reflexivity|]); apply Forall_nil ].
apply (at_R3_facts Wx md X P _ R3_RETge _ _ HR). clear HR.
intros E' ms HE HS. assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
assert (RP : 0 <= Pr /\ Pr + 16 < 2 ^ 64) by (clear - DR F2; numconst; zlia).
assert (RR : 0 <= RGv /\ RGv + 128 < 2 ^ 64) by (clear - DR; numconst; zlia).
unfold MUX_ge, MFY_ge. cells3 HS HEn R3_RETge RP RR DR F1' F2.
all: lazymatch goal with
| |- sv_denot _ _ = _ =>
first [
sv_zev; rewrite (HEn 39%nat ltac:(cbv; zlia)), (HEn 63%nat ltac:(cbv; zlia)), EaN, EaNFg; unfold w64;
clear - N0 N1 N2 N7 F0 F1 M0 M1 K3 Hneed; unfold kFreeArrayMax in *;
rewrite (unsigned_lit_small n), (unsigned_lit_small nfg) by zlia; rewrite !Z.add_0_r; rewrite (zcanon_id n), (zcanon_id nfg) by (unfold M64; zlia);
change (zcanon (-1)) with (2 ^ 64 - 1); unfold zcanon, M64;
rewrite (Zplus_mod_idemp_l (n * (2 ^ 64 - 1))); replace (n * (2 ^ 64 - 1) + nfg) with ((nfg - n) + n * 2 ^ 64) by zlia;
rewrite Z_mod_plus_full; apply Z.mod_small; zlia
|
cbn [sv_denot]; rewrite (HEn 66%nat ltac:(cbv; zlia)), EaMF2, G33; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity ]
| |- _ => first [ clear - K3; zlia | clear - K1; zlia | clear - K4; numconst; zlia
| clear - N0 N1 N2 N7 F0 F1 M0 M1 K3 Hneed; numconst; unfold kFreeArrayMax in *; zlia
| clear - Y2 Y3; unfold MFY_ge, kFreeArrayMax, kFreeArrayMapSize in *; zlia
| clear - N9 U0 U1 U2; unfold MUX_ge in *; numconst; zlia
| clear - N3 N5 N8 N9 U0 U1 N0 K4; numconst; nia ]
end.
Qed.
End f.
End d.

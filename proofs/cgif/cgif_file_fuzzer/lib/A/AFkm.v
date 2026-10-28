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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhm AFka AFi3 AFkk AFkj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section z.
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
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let m0 := mrestrict (w_H W) mem0.
Lemma zrange_dec : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. clear.
intros lo hi a. destruct (Z_le_dec lo a) as [H1|H1]; [destruct (Z_lt_dec a hi) as [H2|H2]; [left; exact (conj H1 H2) | right; intros [_ H]; exact (H2 H)] | right; intros [H _]; exact (H1 H)].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. clear. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; exact H. Qed.
Lemma val_mem_cell : forall (Hh : word -> bool) mem e (w : nat) e',
val_mem tfibsegs (mrestrict Hh mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview tfibsegs Hh mem) (ACell e w (AV e')).
Proof.
clear. intros Hh mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [reflexivity|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. zlia.
Qed.
Lemma val_mem_at : forall (m : word -> option byte) a a' (w : nat) x, a = a' -> val_mem tfibsegs m a' w x -> val_mem tfibsegs m a w x.
Proof. clear. intros m a a' w x -> H. exact H. Qed.
Lemma nth_error_run_elems : forall m lo sz j, (j < m)%nat -> nth_error (run_elems lo sz m) j = Some (lo + Z.of_nat j * sz).
Proof. clear.
induction m as [|m IH]; intros lo sz j Hj; [zlia|]. cbn [run_elems]. destruct j as [|j]; cbn [nth_error]; [f_equal; zlia|].
rewrite IH by zlia. f_equal. zlia.
Qed.
Lemma fa_nth_elems : forall sz fl j, runs_ok fl -> 0 <= j -> fa_nth sz fl j = nth_error (fa_elems sz fl) (Z.to_nat j).
Proof. clear.
intros sz fl. induction fl as [|[lo k|o] t IH]; intros j Hr Hj.
- cbn. destruct (Z.to_nat j); reflexivity.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_run.
destruct (Z.ltb_spec j k).
+ rewrite nth_error_app1 by (rewrite run_elems_length; zlia). rewrite nth_error_run_elems by zlia. f_equal. rewrite Z2Nat.id by zlia. reflexivity.
+ rewrite nth_error_app2 by (rewrite run_elems_length; zlia). rewrite run_elems_length. rewrite IH by (assumption || zlia). f_equal. zlia.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_one. destruct (Z.eqb_spec j 0) as [->|Hne]; [reflexivity|].
replace (Z.to_nat j) with (Datatypes.S (Z.to_nat (j - 1))) by zlia. cbn [nth_error]. apply IH; [assumption | zlia].
Qed.
Lemma in_combine_seq : forall (l0 : list Z) (s i : nat) vv, In (i, vv) (combine (seq s (length l0)) l0) -> (s <= i)%nat /\ nth_error l0 (i - s) = Some vv.
Proof. clear.
induction l0 as [|y t IH]; intros s i vv H; [destruct H|]. cbn [length combine seq] in H. destruct H as [H|H].
- injection H as <- <-. split; [zlia|]. rewrite Nat.sub_diag. reflexivity.
- destruct (IH _ _ _ H) as [H1 H2]. split; [zlia|]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by zlia. cbn [nth_error]. exact H2.
Qed.
Lemma flat_map_ext_in {X Y} : forall (f g : X -> list Y) (l0 : list X), (forall x, In x l0 -> f x = g x) -> flat_map f l0 = flat_map g l0.
Proof. clear.
intros f g l0. induction l0 as [|x t IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.
Lemma nth_error_rev : forall (l0 : list Z) i, (i < length l0)%nat -> nth_error (rev l0) i = nth_error l0 (length l0 - 1 - i).
Proof. clear.
intros l0 i Hi. rewrite (nth_error_nth' (rev l0) 0) by (rewrite length_rev; exact Hi). rewrite (nth_error_nth' l0 0) by zlia.
f_equal. rewrite rev_nth by exact Hi. f_equal. zlia.
Qed.
Section a0.
Variables (NC MU MF : Z) (TOPS : list Z) (FL : list fseg) (HO : list (Z * Z)).
Definition AU : Z := au + NC * csz.
Definition NF' : Z := nf + NC.
Definition NT : Z := Z.of_nat (length TOPS).
Definition rG : region := mkRegion MU AU MF FL HO.
Definition SG : astate := upd_pc c (mkPC maxc (rev TOPS)) (upd_reg c rG S).
Lemma len_factsG : length (st_regions S) = 32%nat /\ length (st_cache S) = 32%nat /\ (Z.to_nat c < 32)%nat.
Proof. pose proof (wf_len_regions _ _ _ _ _ WF). pose proof (wf_len_cache _ _ _ _ _ WF). repeat split; try assumption. clear - HcR. zlia. Qed.
Lemma SG_parts :
(forall c', 0 <= c' -> c' <> c -> reg SG c' = reg S c') /\ reg SG c = rG /\
st_cache_inited SG = st_cache_inited S /\
(forall c', 0 <= c' -> c' <> c -> cache SG c' = cache S c') /\ cache SG c = mkPC maxc (rev TOPS) /\
st_chunks SG = st_chunks S /\ st_secs SG = st_secs S /\ frames SG = frames S /\
st_qthread SG = st_qthread S /\ st_qglobal SG = st_qglobal S /\ st_fs SG = st_fs S /\
st_internal_inited SG = st_internal_inited S /\ st_sec_arr SG = st_sec_arr S /\
st_sec_reserved SG = st_sec_reserved S /\ st_depot SG = st_depot S /\ st_nev SG = st_nev S.
Proof.
pose proof len_factsG as (L1 & L2 & L3). unfold SG, upd_pc, upd_reg. repeat split; try reflexivity.
- intros c' Hc' Hne. unfold reg. cbn. apply znth_zupd_other; [clear - HcR; zlia | exact Hc' | congruence].
- unfold reg. cbn. apply znth_zupd_same; [clear - HcR; zlia | rewrite L1; exact L3].
- intros c' Hc' Hne. unfold cache. cbn. apply znth_zupd_other; [clear - HcR; zlia | exact Hc' | congruence].
- unfold cache. cbn. apply znth_zupd_same; [clear - HcR; zlia | rewrite L2; exact L3].
Qed.
Lemma SG_sec_extents : sec_extents ly SG = sec_extents ly S.
Proof. reflexivity. Qed.
Variables (Wd : world tfibsegs) (mdf : Model) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Let rd' : reader := aview tfibsegs (w_H Wd) mem'.
Let m' := mrestrict (w_H Wd) mem'.
Hypothesis WFG : Wf (as_universe B) SG.
Hypothesis HNC : 0 <= NC < 2 ^ 16.
Variables (uq fq : bool).
Hypothesis HUQ : uq = true -> mu < tot /\ mu2 <= kFreeArrayOffset.
Hypothesis HFQ : fq = true -> mf2 <= kFreeArrayMax.
Hypothesis HMU : (MU = mu /\ NC * csz <= mu - au) \/ (MU = mu2 /\ uq = true /\ NC * csz <= mu2 - au).
Hypothesis HMF : (MF = mf) \/ (MF = mf2 /\ fq = true).
Hypothesis HNF : 4 * NF' <= MF.
Hypothesis HNT : (TOPS = [] /\ NC = 0) \/ (NT = n /\ need <= NC).
Hypothesis E_elems : run_elems au csz (Z.to_nat NC) ++ fa_elems csz fr = TOPS ++ fa_elems csz FL.
Hypothesis E_runs : runs_ok FL.
Hypothesis E_rest : fa_len FL = NF' - NT.
Hypothesis HSUB : hsub (w_H Wd) (w_H W).
Hypothesis HBUD : A_bytes (w_A Wd) <= A_bytes (w_A W) + 2 ^ 20.
Hypothesis HINC : forall i, In i (w_A W) -> In i (w_A Wd).
Hypothesis HSL : A_bytes (w_A W) + EV_A <= abudget S.
Hypothesis HL : ALedger tfibsegs ly SG mdf.
Hypothesis HMW : amwf mdf.
Definition W_FEn (a : Z) : Prop := FAv + 4 * nf <= a < FAv + 4 * NF'.
Definition XC (a : Z) : Prop :=
(Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 64) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) \/
W_FEn a \/ (uq = true /\ W_UW a) \/ (MU = mu2 /\ W_USH a) \/ (fq = true /\ W_FW a) \/ (MF = mf2 /\ W_FSH a).
Hypothesis MEQ : forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) -> ~ XC (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis HVIS : forall x : word, ~ XC (bv_unsigned x) -> w_H Wd x = w_H W x.
Hypothesis NOREM : forall x : word, mem0 x <> None -> mem' x <> None \/ (MU = mu /\ uq = true /\ W_UW (bv_unsigned x)) \/ (MF = mf /\ fq = true /\ W_FW (bv_unsigned x)).
Hypothesis PRS : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wd) mem' a.
Hypothesis FAP : forall a, FAv <= a < FAv + MF -> apresent (w_H Wd) mem' a.
Hypothesis DSTP : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H Wd) mem' a.
Hypothesis UWP : MU = mu2 -> forall a, RBv <= a < RBv + mu2 -> apresent (w_H Wd) mem' a.
Hypothesis PC : P_cells Wd NT (NF' - NT) MF AU MU mem'.
Hypothesis CPY : forall j, 0 <= j < 4 * NT -> mem' (w64 (DSTv + j)) = mem' (w64 (FAv + 4 * (NF' - NT) + j)).
Hypothesis FILL : forall i, 0 <= i < NC -> val_mem tfibsegs m' (FAv + 4 * NF' - 4 - 4 * i) 4 ((au + i * csz) / 16).
Hypothesis USHV : MU = mu2 -> forall x : word, W_USH (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 250) /\ w_H Wd x = false.
Hypothesis FSHV : MF = mf2 -> forall x : word, W_FSH (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 250) /\ w_H Wd x = false.
Hypothesis VISLOC : forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
0 <= aeval B ly (fst r) + i < 2 ^ 64 /\
(ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize -> prim_committed_at ly S (aeval B ly (fst r) + i)).
Let MA : ARm B ly S rd0 := proj1 HAR.
Ltac drop4 := clear3;
try match type of HUQ with uq = true -> _ => clear HUQ end; try match type of HFQ with fq = true -> _ => clear HFQ end;
try match type of HMU with _ \/ _ => clear HMU end; try match type of HMF with _ \/ _ => clear HMF end;
try match type of HNT with _ \/ _ => clear HNT end.
Ltac lia4 := drop4; zlia.
Ltac nia4 := drop4; nia.
Lemma geo : kHighMemBeg <= RBv /\ RBv + 2 ^ 32 <= ASAN_CEIL /\ FAv = RBv + kFreeArrayOffset /\ adr = RBv + mu /\ fadr = FAv + mf /\
0 <= mu /\ mu2 = mu + kUserMapSize /\ MU <= kFreeArrayOffset /\ 0 <= mf /\ MF <= kFreeArrayMax /\ mf <= MF /\ mu <= MU /\
kHighShadowBeg <= sha /\ sha + 32768 <= kHighShadowEnd /\ kHighShadowBeg <= shf /\ shf + 32768 <= kHighShadowEnd /\
0 <= nf /\ 4 * nf <= mf /\ au <= AU <= MU /\ 0 <= au /\ 0 <= NT <= NF' /\ NT <= 8 /\ nf <= NF'.
Proof.
pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 &
G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32 & G33 & _).
pose proof derived_rangesR as DR. pose proof Hmu as ([U0 U1] & U2 & U3 & U4). pose proof Hmf as [[M0 M1] M2]. pose proof Hnf as [F0 F1].
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite <- RBv_is in Q5.
unfold AU, NF', NT in *. unfold kHighShadowBeg, kHighShadowEnd.
repeat split; try assumption; try (clear - DR; tauto);
try (clear - HMU HUQ U0 U1 U2 G15 HNC K4; unfold kUserMapSize in *; destruct HMU as [[EM X]|(EM & EQ & X)]; [|specialize (HUQ EQ)]; nia);
try (clear - HMF HFQ M0 M1 G33; unfold kFreeArrayMapSize in *; destruct HMF as [EM|[EM EQ]]; [|specialize (HFQ EQ)]; zlia);
try (clear - G14; zlia); try (clear - G30; zlia);
try (clear - HNT HNC K3 G1 F0 Hneed; destruct HNT as [[-> ->]|[E L]]; cbn in *; zlia).
Qed.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - RSTACK <= a < sp0) -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ra N1 N2. unfold rd', rd0, aview, mbyte, mrestrict.
rewrite (HVIS (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ra; exact N2).
rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ra; assumption). reflexivity.
Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfibsegs B ly S W mem0 md0 a HAR Ho) as Ra.
ceil.
pose proof (AR_stack_law_ok tfibsegs B ly S W mem0 md0 a HAR) as NS. destruct Hsp as (S1 & S3 & S4).
apply AGREE0; [clear - Ra; zlia | | exact Hx].
intros Hs. apply NS; [|exact Ho]. clear - Hs S1 S3. unfold RSTACK, sp0 in *. lia4.
Qed.
Lemma XC_where : forall a, XC a ->
(T <= a < T + kThreadObjSize /\ T + t_cache + 80 * c <= a) \/ (RGv <= a < RGv + 128) \/
(RBv <= a < RBv + 2 ^ 32 /\ (W_FEn a \/ (uq = true /\ W_UW a) \/ (fq = true /\ W_FW a))) \/
(kHighShadowBeg <= a < kHighShadowEnd /\ ((MU = mu2 /\ W_USH a) \/ (MF = mf2 /\ W_FSH a))).
Proof.
intros a Hx. pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). pose proof geo as GE. pose proof Hmf as [[M0 M1] _].
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold XC, DSTv, W_FEn, W_UW, W_USH, W_FW, W_FSH in *.
clear - Hx DR K3 GE HNF HcR HUQ HFQ M0 M1 G33. unfold Pr, NF' in *. numconst. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, kFreeArrayOffset, kHighShadowBeg, kHighShadowEnd in *. unfold T in *.
change (262144 / 8) with 32768 in *.
destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[[EQ Hx]|[[EQ Hx]|[[EQ Hx]|[EQ Hx]]]]]]]]]];
[ left; lia4 | left; lia4 | right; left; lia4 | left; lia4 | left; lia4
| right; right; left; split; [lia4 | left; exact Hx]
| specialize (HUQ EQ); right; right; left; split; [lia4 | right; left; exact (conj EQ Hx)]
| right; right; right; split; [lia4 | left; exact (conj EQ Hx)]
| specialize (HFQ EQ); right; right; left; split; [lia4 | right; right; exact (conj EQ Hx)]
| right; right; right; split; [lia4 | right; exact (conj EQ Hx)] ].
Qed.
Lemma Z_img : forall a, (0x10000 <= a < 0x5fb000 \/ 0x7fff7000 <= a < 0x2008fff7000) -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & _). pose proof derived_rangesR as DR. pose proof geo as GE.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [Hx _]]]]; clear - Ha Hx TI TH DR GE; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; try unfold T in *; zlia.
Qed.
Lemma Z_band : forall a, 0x7fff7000 <= a < kHighMemBeg -> ~ (MU = mu2 /\ W_USH a) -> ~ (MF = mf2 /\ W_FSH a) -> ~ XC a.
Proof.
intros a Ha N1 N2 Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & _). pose proof derived_rangesR as DR. pose proof geo as GE.
pose proof (zone3_apart_hsh _ _ a F1) as TH.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [_ [Hx|Hx]]]]]; [| | | exact (N1 Hx) | exact (N2 Hx)]; clear - Ha Hx TH DR GE; numconst; try unfold T in *; zlia.
Qed.
Lemma Z_T : forall a, T <= a < T + kThreadObjSize -> (a < T + t_cache + 80 * c \/ Pr + 80 <= a) -> ~ (T + 2768 <= a < T + 2800) -> ~ (T + 2872 <= a < T + 2888) -> ~ XC a.
Proof.
intros a Ha H1 H2 H3 Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof class_facts as (_ & _ & K3 & _). pose proof geo as GE.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold XC, DSTv in Hx.
destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[[EQu Hx]|[[EQu Hx]|[[EQf Hx]|[EQf Hx]]]]]]]]]]; unfold W_FEn, W_UW, W_USH, W_FW, W_FSH in Hx;
first [pose proof (HUQ EQu) as [HU1 HU2] | pose proof I as HU2]; first [pose proof (HFQ EQf) as HF1 | pose proof I as HF1];
clear - Ha H1 H2 H3 Hx DR F1 F2 F3 F4 F5 F6 PT Q1 Q2 GE K3 HNF HU2 HF1 G33; unfold Pr, NF' in *; numconst;
unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax, kHighShadowBeg, kHighShadowEnd in *; change (262144 / 8) with 32768 in *; try unfold T in *; zlia.
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (RGv <= a < RGv + 128) -> ~ W_FEn a -> ~ (uq = true /\ W_UW a) -> ~ (fq = true /\ W_FW a) -> ~ XC a.
Proof.
intros a Ha HR N1 N2 N3 Hx. apply XC_where in Hx. pose proof high_factsR as (F1 & F2 & F3 & _). pose proof geo as GE.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
destruct Hx as [[Hx _] | [Hx | [[_ [Hx|[Hx|Hx]]] | [Hx _]]]]; [| | exact (N1 Hx) | exact (N2 Hx) | exact (N3 Hx) |]; clear - Ha HR Hx F1 F3 PT GE; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; try unfold T in *; zlia.
Qed.
Lemma Z_high : forall a, kHighMemBeg <= a -> ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) -> ~ XC a.
Proof.
intros a Ha NT0 NP Hx. apply XC_where in Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof geo as GE.
pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [Hx _]]]]; clear - Ha NT0 NP Hx DR F5 GE R1 R2; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; zlia.
Qed.
Lemma Z_out : forall a, ~ (kHighShadowBeg <= a < kHighShadowEnd) -> ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) -> ~ XC a.
Proof.
intros a Ha NT0 NP Hx. apply XC_where in Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof geo as GE.
pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2.
destruct Hx as [[Hx _] | [Hx | [[Hx _] | [Hx _]]]]; clear - Ha NT0 NP Hx DR F5 GE R1 R2; numconst; unfold kHighShadowBeg, kHighShadowEnd in *; zlia.
Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat ->
fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros i e a He Hi Ha. pose proof (lo_app ly LY) as HI. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ i _ HI He) as IH. cbv beta in IH. unfold in_app in IH.
assert (D : forall j e', nth_error (owned_extents ly) j = Some e' -> (j = 0 \/ j = 2)%nat -> zdisjoint e e').
{ intros j e' He' Hj. unfold static_extents in HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto).
destruct (Nat.lt_ge_cases i j) as [L|L].
- replace j with (i + Datatypes.S (j - i - 1))%nat in He' by (clear - L; zlia). exact (pairwise_ij _ _ _ _ _ _ HD' He He').
- apply zdisjoint_sym. assert (j <> i) by (intros ->; clear - Hi Hj; zlia). replace i with (j + Datatypes.S (i - j - 1))%nat in He by (clear - L H; zlia). exact (pairwise_ij _ _ _ _ _ _ HD' He' He). }
pose proof (D 0%nat _ eq_refl ltac:(clear; zlia)) as D0. pose proof (D 2%nat _ eq_refl ltac:(clear; zlia)) as D2.
unfold zdisjoint in D0, D2. cbn [fst snd] in D0, D2.
apply Z_out; unfold T in *; clear - IH Ha D0 D2; numconst; zlia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros e a He Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (owned_extents ly) -> zdisjoint e e').
{ intros e' He'. exact (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He ltac:(unfold static_extents; apply in_app_iff; left; exact He')). }
pose proof (D (ly_prim ly, kPrimResvSize) ltac:(unfold owned_extents; cbn; tauto)) as D0.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as D2.
unfold zdisjoint in D0, D2. cbn [fst snd] in D0, D2.
apply Z_out; unfold T in *; clear - HIA Ha D0 D2; numconst; zlia.
Qed.
Lemma Z_user : forall c' x a, 1 <= c' <= 31 -> 0 <= x -> x <= rg_mapped_user (reg S c') -> region_base ly c' <= a < region_base ly c' + x -> ~ XC a.
Proof.
intros c' x a Hc' Hx0 Hx Ha. pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _). pose proof derived_rangesR as DR. pose proof geo as GE.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF Hc') as MB.
unfold region_base in Ha, R1, R2. rewrite region_off_eq in Ha, R1, R2 by lia4.
assert (SEP : c' = c \/ (ly_space ly + c' * 2 ^ 32 + 2 ^ 32 <= RBv \/ RBv + 2 ^ 32 <= ly_space ly + c' * 2 ^ 32)).
{ destruct (Z.eq_dec c' c) as [->|NE]; [left; reflexivity | right]. unfold RBv, SB. clear - Hc' HcR NE. nia4. }
apply Z_prim.
- clear - Hx0 Hx Ha R1 R2 MB. unfold kUserMapSize, EV_MAX in MB. lia4.
- unfold RGv, SB in *. clear - Hc' Hx0 Hx Ha HcR MB. numconst. unfold kUserMapSize, EV_MAX in MB. nia4.
- unfold W_FEn. rewrite (proj1 (proj2 (proj2 GE))). destruct SEP as [->|SEP]; [rewrite <- Hmu_def in Hx; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; pose proof I as SEP|];
clear - Hx0 Hx Ha MB GE HNF SEP; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMax in *; zlia.
- intros [_ HW]. revert HW. unfold W_UW. rewrite (proj1 (proj2 (proj2 (proj2 GE)))). destruct SEP as [->|SEP]; [rewrite <- Hmu_def in Hx; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; pose proof I as SEP|];
clear - Hx0 Hx Ha MB GE SEP; unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *; zlia.
- intros [EQ HW]. pose proof (HFQ EQ) as HF1. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
revert HW. unfold W_FW. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 GE))))), (proj1 (proj2 (proj2 GE))). destruct SEP as [->|SEP]; [rewrite <- Hmu_def in Hx; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; pose proof I as SEP|];
clear - Hx0 Hx Ha MB GE SEP HF1 G33; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
Qed.
Lemma UW_uncommitted : uq = true -> forall a, W_UW a -> ~ prim_committed_at ly S a.
Proof.
intros EQ a Ha [Hr | (c' & Hc' & [Hu | Hf])]; pose proof (HUQ EQ) as [HU1 HU2]; unfold in_zr, W_UW in *; cbn [fst snd] in *; pose proof geo as GE; pose proof derived_rangesR as DR.
- unfold ly_rinfo in Hr. unfold RGv, RBv, SB in *. clear - Ha Hr GE HcR HU2. numconst. unfold kUserMapSize, kFreeArrayOffset in *. nia4.
- pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF Hc') as MB. unfold region_base in Hu. rewrite region_off_eq in Hu by lia4.
destruct (Z.eq_dec c' c) as [->|NE]; [rewrite <- Hmu_def in Hu; unfold RBv, SB in *; rewrite ?region_off_eq in * by lia4; clear - Ha Hu GE; zlia|].
unfold RBv, SB in *. clear - Ha Hu GE Hc' HcR NE MB HU2. numconst. unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. nia4.
- pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA0 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
unfold fa_base in Hf. rewrite region_off_eq in Hf by lia4. unfold RBv, SB in *.
clear - Ha Hf GE Hc' HcR FA0 FB HU2. numconst. unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMax in *. nia4.
Qed.
Lemma FW_uncommitted : fq = true -> forall a, W_FW a -> ~ prim_committed_at ly S a.
Proof.
intros EQ a Ha [Hr | (c' & Hc' & [Hu | Hf])]; pose proof (HFQ EQ) as HF1; unfold in_zr, W_FW in *; cbn [fst snd] in *; pose proof geo as GE; pose proof derived_rangesR as DR.
- unfold ly_rinfo in Hr. unfold RGv, FAv, RBv, SB in *. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _). clear - Ha Hr GE HcR HF1 G33. numconst. unfold kFreeArrayMapSize, kFreeArrayMax, kFreeArrayOffset in *. nia4.
- pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF Hc') as MB. unfold region_base in Hu. rewrite region_off_eq in Hu by lia4.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _). unfold FAv, RBv, SB in *. clear - Ha Hu GE Hc' HcR MB HF1 G33. numconst. unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. nia4.
- pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA0 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
unfold fa_base in Hf. rewrite region_off_eq in Hf by lia4.
destruct (Z.eq_dec c' c) as [->|NE]; [rewrite <- Hmf_def in Hf; unfold FAv, RBv, SB in *; rewrite ?region_off_eq in * by lia4; clear - Ha Hf GE; zlia|].
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _). unfold FAv, RBv, SB in *. clear - Ha Hf GE Hc' HcR NE FA0 FB HF1 G33. numconst. unfold kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. nia4.
Qed.
Lemma VIS_MONO : forall a, 0 <= a < 2 ^ 64 -> rd0 a <> None -> ~ (MU = mu /\ uq = true /\ W_UW a) -> ~ (MF = mf /\ fq = true /\ W_FW a) -> rd' a <> None.
Proof.
clear - HSUB NOREM. intros a Ra HV N1 N2. unfold rd', rd0, aview, mbyte, mrestrict in *.
destruct (w_H W (Z_to_bv 64 a)) eqn:Eh.
- exfalso. apply HV. cbn. unfold seg_rom. rewrite (memory_read1_hidden tfibsegs (w_H W) (w_Hoff W) _ Eh). reflexivity.
- destruct (w_H Wd (Z_to_bv 64 a)) eqn:E'; [rewrite (HSUB _ E') in Eh; discriminate|].
destruct (mem0 (Z_to_bv 64 a)) as [b|] eqn:Em.
+ destruct (NOREM (Z_to_bv 64 a) ltac:(rewrite Em; discriminate)) as [NN | [X|X]].
* destruct (mem' (Z_to_bv 64 a)) as [b'|]; [cbn; discriminate | exfalso; exact (NN eq_refl)].
* exfalso. apply N1. rewrite unsigned_lit_small in X by exact Ra. exact X.
* exfalso. apply N2. rewrite unsigned_lit_small in X by exact Ra. exact X.
+ destruct (mem' (Z_to_bv 64 a)) as [b'|]; [cbn; discriminate | exact HV].
Qed.
Lemma apresent_vis : forall a, apresent (w_H Wd) mem' a -> rd' a <> None.
Proof. intros a [Hh [b Hb]]. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma aview_copy : forall a b, apresent (w_H Wd) mem' a -> apresent (w_H Wd) mem' b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
mem' (w64 a) = mem' (w64 b) -> rd' a = rd' b.
Proof.
intros a b [Ha _] [Hb [xb Hxb]] Ra Rb E. unfold rd', aview, mbyte, mrestrict. unfold w64 in E. rewrite Ha, Hb, E, Hxb. reflexivity.
Qed.
Lemma vis_keep : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. apply Forall_forall. intros r Hr i Hi.
assert (IN : In r (ajunk B ly S ++ aareas S ++ aclient S)) by (rewrite !in_app_iff; destruct H as [H|[H|H]]; [left | right; left | right; right]; exact (H r Hr)).
assert (RV : rd0 (aeval B ly (fst r) + i) <> None).
{ destruct H as [H|[H|H]]; [exact (proj1 (Forall_forall _ _) (am_junk _ _ _ _ MA) r (H r Hr) i Hi) | exact (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) r (H r Hr) i Hi)
| exact (proj1 (Forall_forall _ _) (am_client _ _ _ _ MA) r (H r Hr) i Hi)]. }
destruct (VISLOC r i IN Hi) as [Ra LOC]. pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2. pose proof geo as GE.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
apply (VIS_MONO _ Ra RV); intros (E & EQ & Hw); [apply (UW_uncommitted EQ _ Hw) | apply (FW_uncommitted EQ _ Hw)]; apply LOC; [pose proof (HUQ EQ) as [HU1 HU2]; pose proof I as HF1 | pose proof (HFQ EQ) as HF1; pose proof I as HU2]; unfold W_UW, W_FW in Hw;
clear - Hw R1 R2 GE HU2 HF1 G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun cc => lo <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. apply Forall_forall. intros cc Hc.
pose proof (proj1 (Forall_forall _ _) RNG cc Hc) as [R1 R2]. cbv beta in R1, R2.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc))|].
intros k Hk. apply AGX.
- exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- apply LOC. clear - Hk R1 R2. lia4.
Qed.
Lemma keep_cell : forall cc lo len, loc_ok lo len -> In cc (acells B ly S) ->
lo <= aeval B ly (c_at cc) -> aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len -> cell_holds B ly rd' cc.
Proof.
intros cc lo len LOC Hc R1 R2. exact (proj1 (Forall_forall _ _) (keep_cells [cc] lo len LOC ltac:(intros x [<-|[]]; exact Hc) ltac:(constructor; [split; assumption | constructor])) cc (or_introl eq_refl)).
Qed.
Ltac fcons' := apply Forall_cons; [cbn; lia4|].
Lemma PCv : let m := m' in
val_mem tfibsegs m Pr 4 NT /\ val_mem tfibsegs m (Pr + 4) 4 maxc /\ val_mem tfibsegs m (Pr + 8) 8 csz /\
val_mem tfibsegs m RGv 8 0 /\ val_mem tfibsegs m (RGv + 8) 8 0 /\ val_mem tfibsegs m (RGv + 16) 8 (NF' - NT) /\
val_mem tfibsegs m (RGv + 24) 8 MF /\ val_mem tfibsegs m (RGv + 32) 8 AU /\ val_mem tfibsegs m (RGv + 40) 8 0 /\
val_mem tfibsegs m (RGv + 48) 8 MU /\ val_mem tfibsegs m (RGv + 56) 8 0 /\ val_mem tfibsegs m (RGv + 68) 1 0.
Proof. exact (proj2 PC). Qed.
Lemma PRW : forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H Wd) mem' a.
Proof. exact (proj1 PC). Qed.
Definition EL : list Z := run_elems au csz (Z.to_nat NC) ++ fa_elems csz fr.
Lemma EL_len : Z.of_nat (length EL) = NF'.
Proof.
pose proof cls_wfR as C0. pose proof (fa_elems_length csz (rg_free (reg S c)) (wr_runs _ _ _ _ _ _ C0)) as L.
unfold EL, NF'. rewrite length_app, run_elems_length. unfold fr. rewrite <- Hnf_def in L. pose proof HNC as [N0 _]. clear - L N0. lia4.
Qed.
Lemma entry_rd : forall j vv, 0 <= j < NF' -> nth_error EL (Z.to_nat (NF' - 1 - j)) = Some vv -> rd32 rd' (FAv + 4 * j) (vv / 16).
Proof.
intros j vv Hj Hnth k Hk. pose proof geo as GE. pose proof HNC as [N0 N1]. pose proof Hnf as [F0 F1]. pose proof derived_rangesR as DR.
pose proof reg_facts as (_ & _ & _ & _ & RU). assert (HNT0 : 0 <= NT) by (unfold NT; clear; zlia).
destruct (Z_lt_le_dec (NF' - 1 - j) NC) as [NEW|OLD].
-
unfold EL in Hnth. rewrite nth_error_app1 in Hnth by (rewrite run_elems_length; clear - NEW Hj N0 HNT0; zlia).
rewrite nth_error_run_elems in Hnth by (clear - NEW Hj N0 HNT0; zlia). injection Hnth as <-.
pose proof (FILL (NF' - 1 - j) ltac:(clear - NEW Hj GE; zlia)) as V. unfold rd'. unfold aview.
replace (FAv + 4 * NF' - 4 - 4 * (NF' - 1 - j)) with (FAv + 4 * j) in V by lia4. rewrite Z2Nat.id by (clear - Hj GE; zlia).
unfold m' in V. rewrite (V k Hk). cbn [option_map]. rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [f_equal; f_equal; clear - Hj GE; zlia|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia4.
-
unfold EL in Hnth. rewrite nth_error_app2 in Hnth by (rewrite run_elems_length; clear - OLD; zlia). rewrite run_elems_length in Hnth.
assert (Hjn : 0 <= j < nf) by (unfold NF' in *; clear - OLD Hj GE N0; zlia).
assert (FN : fa_nth (class_size c) (rg_free (reg S c)) (fa_len (rg_free (reg S c)) - 1 - j) = Some vv).
{ rewrite <- Hnf_def, <- Hcsz. rewrite fa_nth_elems by (exact RU || (clear - Hjn; zlia)). unfold fr in Hnth. rewrite <- Hnth. f_equal. unfold NF'. clear - OLD Hjn N0. lia4. }
pose proof (am_fa _ _ _ _ MA c j vv HcR ltac:(rewrite <- Hnf_def; exact Hjn) FN k Hk) as RD. rewrite <- FAv_is in RD.
rewrite AGX; [exact RD | eapply own_fa; [exact MA | exact HcR | rewrite <- FAv_is; clear - Hjn Hk F1 GE; unfold kFreeArrayMax in *; zlia] |].
apply Z_prim.
+ pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2. clear - Hjn Hk F1 GE R1 R2. unfold kFreeArrayOffset, kFreeArrayMax in *. lia4.
+ unfold RGv, FAv, RBv, SB in *. clear - Hjn Hk F1 GE HcR. numconst. unfold kFreeArrayOffset, kFreeArrayMax in *. lia4.
+ unfold W_FEn. clear - Hjn Hk; zlia.
+ intros [EQ HW]. pose proof (HUQ EQ) as [_ HU2]. unfold W_UW in HW. clear - Hjn Hk GE F1 HW HU2; unfold kFreeArrayOffset, kUserMapSize in *; zlia.
+ intros [_ HW]. unfold W_FW in HW. clear - Hjn Hk GE F1 HW; zlia.
Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells SG) (zseq 1 31)).
Proof.
pose proof SG_parts as (Rreg & Rc & _). apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof derived_rangesR as DR. pose proof PCv as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12).
pose proof geo as GE.
destruct (Z.eq_dec c' c) as [->|Hne].
- unfold region_cells. rewrite Rc. unfold rG. cbn [rg_free rg_mapped_fa rg_alloc_user rg_mapped_user]. rewrite E_rest.
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = RGv + d) by (intros d; cbn; unfold RGv, SB; lia4).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = RGv + 0) by (cbn; unfold RGv, SB; lia4).
repeat (apply Forall_cons; [apply val_mem_cell; rewrite ?ER, ?ER0; cbn [aeval];
first [ exact (val_mem_at m' _ _ _ _ (Z.add_0_r RGv) V4) | exact V5 | exact V6 | exact V7 | exact V8 | exact V9 | exact V10 | exact V11 | exact V12 ] |]).
apply Forall_nil.
- replace (region_cells SG c') with (region_cells S c') by (unfold region_cells; rewrite (Rreg c') by (clear - Hc' Hne; zlia); reflexivity).
pose proof (region_in_prim ly c LY HcR) as (R1 & R2 & _). rewrite <- RBv_is in R1, R2.
apply (keep_cells _ (ly_space ly + kRegionInfoOff + 128 * c') 128).
+ intros a Ha. assert (LO : RBv + 2 ^ 32 <= a) by (unfold RGv, FAv, RBv, SB in *; clear - Ha Hc' DR HcR; numconst; zlia).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
apply Z_prim.
* clear - Ha Hc' F3 F4 F5 DR HcR; numconst; zlia.
* unfold RGv, SB in *; clear - Ha Hc' Hne HcR; numconst; zlia.
* unfold W_FEn. clear - LO GE HNF; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
* intros [EQ HW]. pose proof (HUQ EQ) as [_ HU2]. unfold W_UW in HW. clear - LO GE HW HU2; unfold kUserMapSize, kFreeArrayOffset in *; zlia.
* intros [EQ HW]. pose proof (HFQ EQ) as HF1. unfold W_FW in HW. clear - LO GE HW HF1 G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
+ intros x Hx. unfold acells. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia4 | exact Hx].
+ unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
Lemma slot_cell : forall (i : nat) vv, In (i, vv) (combine (seq 0 (length (rev TOPS))) (rev TOPS)) ->
cell_holds B ly rd' (z4 (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat i)) (vv / 16)).
Proof.
intros i vv Hin. apply in_combine_seq in Hin as [_ Hnth]. rewrite Nat.sub_0_r in Hnth.
assert (Hi : (i < length TOPS)%nat). { rewrite <- (length_rev TOPS). apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
rewrite nth_error_rev in Hnth by exact Hi.
pose proof geo as GE. pose proof class_facts as (_ & _ & K3 & _). pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & _).
assert (EN : nth_error EL (Z.to_nat (NF' - 1 - (NF' - NT + Z.of_nat i))) = Some vv).
{ fold EL in E_elems. rewrite E_elems. rewrite nth_error_app1 by (unfold NT; clear - Hi; zlia). rewrite <- Hnth. f_equal. unfold NT. clear - Hi. lia4. }
assert (HjR : 0 <= NF' - NT + Z.of_nat i < NF') by (unfold NT in *; clear - Hi GE; zlia).
pose proof (entry_rd (NF' - NT + Z.of_nat i) vv HjR EN) as RD.
unfold cell_holds. cbn [c_at c_val c_w aeval aoff z4 c4]. intros k Hk.
rewrite (aview_copy (ly_T ly + (t_cache + 80 * c + (16 + 4 * Z.of_nat i)) + Z.of_nat k) (FAv + 4 * (NF' - NT + Z.of_nat i) + Z.of_nat k)).
- rewrite <- (RD k Hk). reflexivity.
- apply DSTP. unfold NT in *. clear - Hi Hk K3 GE. unfold DSTv, Pr. lia4.
- apply FAP. unfold NT in *. clear - Hi Hk GE HNF. lia4.
- clear - DR F1 F2 Hi Hk K3 GE. unfold NT, Pr in *. numconst. lia4.
- unfold NT in *. clear - DR Hi Hk GE HNF. numconst. unfold kFreeArrayMax in *. lia4.
- replace (ly_T ly + (t_cache + 80 * c + (16 + 4 * Z.of_nat i)) + Z.of_nat k) with (DSTv + (4 * Z.of_nat i + Z.of_nat k)) by (unfold DSTv, Pr, T; lia4).
replace (FAv + 4 * (NF' - NT + Z.of_nat i) + Z.of_nat k) with (FAv + 4 * (NF' - NT) + (4 * Z.of_nat i + Z.of_nat k)) by lia4. apply CPY. unfold NT in *. clear - Hi Hk. lia4.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells SG) (zseq 1 31)).
Proof.
pose proof SG_parts as (_ & _ & Rinit & Rother & Rcl & _). apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof derived_rangesR as DR. pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof PCv as (V1 & V2 & V3 & _).
destruct (Z.eq_dec c' c) as [->|Hne].
- unfold cache_cells. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks pc_max].
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c)) d) = Pr + d) by (intros d; cbn; unfold Pr; lia4).
constructor. { apply val_mem_cell. cbn [aeval]. apply (val_mem_at m' _ Pr); [unfold Pr; lia4|]. rewrite length_rev. fold NT. exact V1. }
constructor. { apply val_mem_cell. rewrite EP. cbn [aeval]. rewrite <- Hmax. exact V2. }
constructor. { apply val_mem_cell. rewrite EP. cbn [aeval]. rewrite <- Hcsz. exact V3. }
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv). cbn [fst snd]. exact (slot_cell i vv Hiv).
- replace (cache_cells SG c') with (cache_cells S c') by (unfold cache_cells; rewrite Rinit, (Rother c') by lia4; reflexivity).
apply (keep_cells _ (T + t_cache + 80 * c') 80).
+ intros a Ha. apply Z_T; unfold Pr in *; unfold T in *; clear - Ha Hc' Hne HcR DR K3; numconst; nia.
+ intros x Hx. unfold acells. apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia4 | exact Hx].
+ unfold cache_cells. pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia4)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c' ltac:(lia4)) as (_ & _ & _ & K4' & _). unfold T.
destruct (st_cache_inited S).
* destruct WC as [PM PL]. unfold t_cache. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. clear - Hiv PL K4'. lia4.
* unfold t_cache. repeat fcons'. apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks SG)).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & Rch & _). rewrite Rch.
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia4)) as (Q1 & Q2 & Q3).
apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
+ intros a Ha. destruct (ck_beg k) as [|o|r o|c'' p] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF (prim_class o) ltac:(lia4))) as AL.
apply (Z_user (prim_class o) (rg_alloc_user (reg S (prim_class o)))); [lia4 | lia4 | lia4 | lia4].
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _). apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Hin | cbn [fst snd]; clear - Ha X2 X3 G8 Q2 G5; unfold kPage in *; zlia].
+ intros x Hx. unfold acells. do 2 (apply in_app_iff; right). apply in_app_iff; left. apply in_flat_map. exists k. split; [exact Hk | exact Hx].
+ assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p]; try solve [destruct GG]; cbn; lia4. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p]; try solve [destruct GG]; cbn; lia4. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
* repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia4|]). apply Forall_nil.
* destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia4]. lia4. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia4|]). apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & Rch & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
replace (sec_cells SG) with (sec_cells S) by (unfold sec_cells; rewrite Rres, Rarr, Rch; reflexivity).
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok 0x10000 0x5eb000) by (intros a Ha; apply Z_img; lia4).
unfold sec_cells in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_reserved; lia4 | cbn; rewrite EI; unfold TFIB_INST, o_sec_reserved, kHighShadowBeg; lia4]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_n; lia4 | cbn; rewrite EI; unfold TFIB_INST, o_sec_n, kHighShadowBeg; lia4]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_mutex; lia4 | cbn; rewrite EI; unfold TFIB_INST, o_sec_mutex, kHighShadowBeg; lia4]|].
apply Forall_app. split.
- apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
+ intros a Ha. apply (Z_ext 1 (ly_Q ly, kPtrArrayResv)); [reflexivity | lia4 | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. left. exact Hx.
+ apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia4.
- apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia4)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
+ intros a Ha. apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Gin | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. rewrite Eb. split; [exact Hk | exact Hx].
+ unfold kPage in *. repeat fcons'. apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia4)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)). { apply Z.mod_divide in X2 as [q Hq]; [|lia4]. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA. rewrite CS in AA. apply Z.mod_divide in AA as [q' Hq']; [|lia4]. nia4. }
intros a Ha. apply (Z_user kBatchClass (rg_alloc_user (reg S kBatchClass))); [unfold kBatchClass; lia4 | lia4 | lia4 |].
unfold region_base. subst x. unfold kBatchBytes in Ha. lia4. }
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; left; reflexivity | cbn; lia4 | cbn; unfold kBatchBytes; lia4]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; left; reflexivity | cbn; lia4 | cbn; unfold kBatchBytes; lia4]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; right; left; reflexivity | cbn; lia4 | cbn; unfold kBatchBytes; lia4]|].
apply Forall_app. split.
- apply (keep_cells _ _ _ LOC).
+ intros y Hy. apply INC. do 3 right. apply in_app_iff. left. exact Hy.
+ apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. lia4.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells SG) with (quar_cells S) by (unfold quar_cells; rewrite Rqt, Rqg; reflexivity).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI. pose proof derived_rangesR as DR.
assert (LOCI : loc_ok 0x10000 0x5eb000) by (intros a Ha; apply Z_img; lia4).
assert (LOCT : loc_ok (T + t_qc) 32) by (intros a Ha; apply Z_T; unfold t_qc in *; unfold Pr, T in *; clear - Ha DR HcR; numconst; zlia).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; lia4 | cbn; rewrite EI; unfold TFIB_INST, kHighShadowBeg; lia4]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; lia4 | cbn; rewrite EI; unfold TFIB_INST, kHighShadowBeg; lia4]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOCT); [apply INC; right; right; apply in_app_iff; left; cbn; tauto | cbn; unfold T; lia4 | cbn; unfold T; lia4]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; right; apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; unfold TFIB_INST; lia4 | cbn; rewrite EI; unfold TFIB_INST, kHighShadowBeg; lia4]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells SG) with (fs_cells S) by (unfold fs_cells; rewrite Rfs; reflexivity).
apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | lia4 | cbn [fst snd]; exact Ha].
- intros x Hx. unfold acells. do 5 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. apply Forall_forall. intros cc Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia4.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
replace (depot_cells ly SG) with (depot_cells ly S) by (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; reflexivity).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
apply (keep_cells _ 0x10000 0x5eb000).
- intros a Ha. apply Z_img. lia4.
- intros x Hx. unfold acells. do 6 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold depot_cells. repeat (apply Forall_cons; [cbn; rewrite ?ED, ?ES; unfold TFIB_DEPOT, TFIB_STORE, d_nuniq, d_map1, s_total, s_block0, kHighShadowBeg; lia4|]). apply Forall_nil.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B SG).
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B SG) with (ialloc_cells B S) by (unfold ialloc_cells; rewrite Rii; reflexivity).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
apply (keep_cells _ 0x10000 0x5eb000).
- intros a Ha. apply Z_img. lia4.
- intros x Hx. unfold acells. do 7 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_FLAG.
repeat (apply Forall_cons; [cbn; rewrite ?E1, ?E3; unfold TFIB_IAL_LO, TFIB_IAL_FLAG, kHighShadowBeg; lia4|]). apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
pose proof derived_rangesR as DR. pose proof class_facts as (_ & _ & K3 & _). unfold thread_cells.
constructor; [|apply Forall_nil]. apply (keep_cell _ (T + t_unwinding) 1).
- intros a Ha. apply Z_T; unfold t_unwinding in *; unfold Pr, T in *; clear - Ha DR HcR K3; numconst; zlia.
- unfold acells. do 8 (apply in_app_iff; right). left. reflexivity.
- cbn. unfold T. lia4.
- cbn. unfold T. lia4.
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly SG).
Proof.
unfold acells.
apply Forall_app; split; [exact cells_regions|]. apply Forall_app; split; [exact cells_caches|]. apply Forall_app; split; [exact cells_chunks|].
apply Forall_app; split; [exact cells_sec|]. apply Forall_app; split; [exact cells_quar|]. apply Forall_app; split; [exact cells_fs|].
apply Forall_app; split; [exact cells_depot|]. apply Forall_app; split; [exact cells_ialloc | exact cells_thread].
Qed.
Lemma fa_final : fa_entries_ok ly rd' SG.
Proof.
pose proof SG_parts as (Rreg & Rc & _). pose proof reg_facts as (_ & _ & _ & _ & RU). intros c' i vv Hc' Hi HV k Hk.
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL0. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0. pose proof geo as GE.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _). pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
destruct (Z.eq_dec c' c) as [->|Hne].
- rewrite Rc in Hi, HV. unfold rG in Hi, HV. cbn [rg_free] in Hi, HV. rewrite E_rest in Hi, HV.
rewrite <- FAv_is. apply (entry_rd i vv ltac:(clear - Hi GE; zlia)); [|exact Hk]. rewrite <- Hcsz in HV. rewrite fa_nth_elems in HV by (exact E_runs || (clear - Hi; zlia)).
fold EL in E_elems. rewrite E_elems. rewrite nth_error_app2 by (unfold NT in *; clear - Hi GE; zlia). rewrite <- HV. f_equal. unfold NT in *. clear - Hi GE. zlia.
- rewrite (Rreg c') in Hi, HV by lia4.
assert (GEO : ~ XC (fa_base ly c' + 4 * i + Z.of_nat k) /\ aowned B ly S (fa_base ly c' + 4 * i + Z.of_nat k)).
{ split.
- pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
pose proof derived_rangesR as DR.
unfold fa_base in *. unfold region_base in R1, R2. rewrite ?region_off_eq in * by (clear - Hc' HcR; zlia). unfold RGv, FAv, RBv, SB in *.
apply Z_prim; unfold W_FEn, W_UW, W_FW; unfold RGv, FAv, RBv, SB in *.
+ clear - Hi Hk FL0 FB F0 R1 R2 Hc' ; numconst; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
+ clear - Hi Hk FL0 FB F0 Hc' HcR DR; numconst; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
+ clear - Hi Hk FL0 FB F0 Hc' HcR Hne GE HNF; numconst; unfold kFreeArrayOffset, kFreeArrayMax in *; zlia.
+ intros [_ HW]. clear - Hi Hk FL0 FB F0 Hc' HcR Hne GE HW; numconst; unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *; zlia.
+ intros [EQ HW]. pose proof (HFQ EQ) as HF1. clear - Hi Hk FL0 FB F0 Hc' HcR Hne GE HW HF1 G33; numconst; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *; zlia.
- eapply own_fa; [exact MA | exact Hc' | clear - Hi Hk FL0 FB F0; unfold kFreeArrayMax in *; zlia]. }
destruct GEO as [NX OW]. rewrite AGX; [exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk) | exact OW | exact NX].
Qed.
Lemma flags_final : fs_flags_ok ly rd' SG.
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & Rfr & _). intros cid pos Hc Hp. rewrite Rfr.
pose proof (flag_off_bounds cid pos Hc Hp) as FB.
rewrite AGX; [exact (am_flags _ _ _ _ MA cid pos Hc Hp) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact MA | lia4] |].
apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | lia4 | cbn [fst snd]].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia4.
Qed.
Lemma depot_ids_boundG : depot_ids S <= 4097.
Proof.
pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). lia4.
Qed.
Lemma depot_final : depot_ok B ly rd' SG.
Proof.
pose proof SG_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
pose proof depot_ids_boundG as IDB. pose proof (ts_depot B TS) as ED.
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. apply AGX.
- destruct Ha as [Ha|Ha].
+ apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa5850, 0x5c8650 - 0xa5850). split; [cbn; tauto|]. unfold in_zr; cbn. unfold TFIB_DEPOT, d_tab_words in Ha. lia4.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [unfold core_extents; cbn; tauto | cbn [fst snd]; lia4].
- destruct Ha as [Ha|Ha]; [apply Z_img; unfold TFIB_DEPOT, d_tab_words, kHighShadowBeg in *; lia4|].
apply (Z_ext 4 (ly_NB ly, kNodesBlockSize)); [reflexivity | lia4 | cbn [fst snd]; lia4]. }
unfold depot_ok, depot_ids, depot_traces in *. rewrite Rdep.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|]. left. rewrite ED. unfold d_tab_words in *. lia4.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
+ intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. right. unfold kNodesBlockSize. lia4.
+ intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. right. unfold kNodesBlockSize. lia4.
Qed.
Lemma shadow_in_USH : forall g, g mod 8 = 0 -> W_USH (shadow_addr g) -> adr <= g < adr + kUserMapSize.
Proof.
intros g Hg8 Hs. pose proof geo as GE. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _).
unfold W_USH, shadow_addr in *. rewrite G11 in Hs. unfold SHBv, SHADOW_OFF in *.
apply Z.mod_divide in G8 as [q Hq]; [|lia4]. pose proof (Z.div_mod g 8 ltac:(lia4)) as D1. rewrite Hg8 in D1.
rewrite Hq in Hs |- *. replace (q * 65536) with (q * 8192 * 8) in Hs by lia4. rewrite Z.div_mul in Hs by lia4.
unfold kUserMapSize in *. change (262144 / 8) with 32768 in *. clear - Hs D1. zlia.
Qed.
Lemma shadow_in_FSH : forall g, g mod 8 = 0 -> W_FSH (shadow_addr g) -> fadr <= g < fadr + kFreeArrayMapSize.
Proof.
intros g Hg8 Hs. pose proof geo as GE. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _).
unfold W_FSH, shadow_addr in *. rewrite G27 in Hs. unfold SHBv, SHADOW_OFF in *.
apply Z.mod_divide in G25 as [q Hq]; [|lia4]. pose proof (Z.div_mod g 8 ltac:(lia4)) as D1. rewrite Hg8 in D1.
rewrite Hq in Hs |- *. replace (q * 65536) with (q * 8192 * 8) in Hs by lia4. rewrite Z.div_mul in Hs by lia4.
unfold kFreeArrayMapSize in *. change (262144 / 8) with 32768 in *. clear - Hs D1. zlia.
Qed.
Lemma UQ2 : MU = mu2 -> uq = true /\ mu < tot /\ mu2 <= kFreeArrayOffset.
Proof.
intros E. pose proof geo as GE. destruct HMU as [[EM _]|(EM & EQ & _)]; [exfalso; clear - E EM GE; unfold kUserMapSize in GE; zlia | exact (conj EQ (HUQ EQ))].
Qed.
Lemma FQ2 : MF = mf2 -> fq = true /\ mf2 <= kFreeArrayMax.
Proof.
intros E. pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct HMF as [EM|[EM EQ]]; [exfalso; clear - E EM G33; unfold kFreeArrayMapSize in G33; zlia | exact (conj EQ (HFQ EQ))].
Qed.
Lemma committed_shadow_old : forall g, g mod 8 = 0 -> in_rangesb g (fa_poison_ranges ly S) = true ->
~ (MU = mu2 /\ W_USH (shadow_addr g)) /\ ~ (MF = mf2 /\ W_FSH (shadow_addr g)).
Proof.
intros g Hg8 IR. pose proof geo as GE. apply in_rangesb_true in IR as (lo & len & Hin & Hlo).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
assert (NU : (MU = mu2 -> ~ (adr <= g < adr + kUserMapSize)) /\ (MF = mf2 -> ~ (fadr <= g < fadr + kFreeArrayMapSize))).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(lia4)) as MB.
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia4)) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA0 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
destruct Hin as [E|[E|[]]]; injection E as <- <-.
+ destruct (Z.eq_dec c' c) as [->|NE].
* rewrite <- Hmu_def, <- RBv_is in Hlo. split; intros EQ; [|pose proof (FQ2 EQ) as [_ HF1]]; [clear - Hlo GE | clear - Hlo GE HF1]; unfold kUserMapSize, kFreeArrayOffset in *; zlia.
* unfold region_base in Hlo. rewrite region_off_eq in Hlo by lia4. unfold RBv, FAv, SB in *.
split; intros EQ; [|pose proof (FQ2 EQ) as [_ HF1]]; [clear - Hlo GE Hc' HcR NE MB | clear - Hlo GE Hc' HcR NE MB HF1 G33]; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; nia.
+ destruct (Z.eq_dec c' c) as [->|NE].
* rewrite <- Hmf_def, <- FAv_is in Hlo. split; intros EQ; [pose proof (UQ2 EQ) as (_ & _ & HU2)|]; [clear - Hlo GE HU2 | clear - Hlo GE]; unfold kUserMapSize, kFreeArrayOffset in *; zlia.
* unfold fa_base in Hlo. rewrite region_off_eq in Hlo by lia4. unfold RBv, FAv, SB in *.
split; intros EQ; [|pose proof (FQ2 EQ) as [_ HF1]]; [clear - Hlo GE Hc' HcR NE FA0 FB | clear - Hlo GE Hc' HcR NE FA0 FB HF1 G33]; numconst; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; nia.
- apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p]; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL _ Gin) as (_ & [H1 H2] & _).
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Gin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in D. cbn [fst snd] in D. unfold FAv in *.
split; intros EQ; [|pose proof (FQ2 EQ) as [_ HF1]]; [clear - Hlo D Q1 Q2 GE | clear - Hlo D Q1 Q2 GE HF1 G33]; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia. }
destruct NU as [NU1 NU2]. split; intros [EQ Hs]; [exact (NU1 EQ (shadow_in_USH g Hg8 Hs)) | exact (NU2 EQ (shadow_in_FSH g Hg8 Hs))].
Qed.
Lemma shadow_final : shadow_ok B ly rd' SG.
Proof.
pose proof SG_parts as (Rreg & Rc & _ & _ & _ & Rch & _). pose proof geo as GE.
intros g vv Hg8 HV. unfold ashadow in HV. rewrite Rch in HV.
assert (SHLOW : forall g0, 0 <= g0 < kHighMemEnd -> 0x7fff7000 <= shadow_addr g0 < kHighMemBeg).
{ clear. intros g0 Hg0. unfold shadow_addr. pose proof (Z.div_mod g0 8 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound g0 8 ltac:(zlia)) as M1. numconst. unfold SHADOW_OFF. zlia. }
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
-
assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0; exact HV).
rewrite AGX; [exact (am_shadow _ _ _ _ MA g vv Hg8 A0) | exact (ashadow_owned B ly S rd0 g vv MA A0) |].
apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & GG).
apply Z_band; [apply SHLOW; clear - Hg0 C1 C2; numconst; zlia | |]; intros [EQw Hs].
+ apply shadow_in_USH in Hs; [|exact Hg8].
destruct (ck_beg k0) as [|o|r o|c'' p] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF (prim_class o) ltac:(lia4))) as AL.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S (prim_class o) WF ltac:(lia4)) as MB.
destruct (Z.eq_dec (prim_class o) c) as [EC|NE].
-- rewrite EC in *. rewrite <- Hmu_def in AL. unfold region_base in *. rewrite region_off_eq in * by lia4. unfold RBv, SB in *. clear - Hs Hg0 D1 D2 D3 D4 D5 D6 D7 D8 AL GE EC C7; unfold kUserMapSize in *. nia4.
-- unfold region_base in *. rewrite region_off_eq in * by lia4. unfold RBv, SB in *. clear - Hs Hg0 D1 D2 D3 D4 D5 D6 D7 D8 AL MB GE NE HcR C7; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. nia4.
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in D. cbn [fst snd] in D. clear - Hs Hg0 D Q1 Q2 GE X2 X3; unfold kUserMapSize, kFreeArrayOffset, kPage in *. lia4.
+ apply shadow_in_FSH in Hs; [|exact Hg8]. pose proof (FQ2 EQw) as [_ HF1].
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct (ck_beg k0) as [|o|r o|c'' p] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF (prim_class o) ltac:(lia4))) as AL.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S (prim_class o) WF ltac:(lia4)) as MB.
unfold region_base in *. rewrite region_off_eq in * by lia4. unfold FAv, RBv, SB in *. clear - Hs Hg0 D1 D2 D3 D4 D5 D6 D7 D8 AL MB GE HcR C7 HF1 G33; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. nia4.
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in D. cbn [fst snd] in D. unfold FAv in *. clear - Hs Hg0 D Q1 Q2 GE X2 X3 HF1 G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax, kPage in *. zlia.
-
rewrite ?F0 in HV. destruct (in_rangesb g (fa_poison_ranges ly SG)) eqn:IR; [|discriminate]. injection HV as <-.
destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR0.
+
assert (A0 : ashadow B ly S g = Some shHeapLeftRz) by (unfold ashadow; rewrite F0, IR0; reflexivity).
pose proof (committed_shadow_old g Hg8 IR0) as [NU NF].
rewrite AGX; [exact (am_shadow _ _ _ _ MA g _ Hg8 A0) | exact (ashadow_owned B ly S rd0 g _ MA A0) |].
apply Z_band; [| exact NU | exact NF].
apply in_rangesb_true in IR0 as (lo & len & Hin & Hlo). apply SHLOW. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
* apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(lia4)) as (R1 & R2 & R3 & R4 & R5). pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia4)) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(lia4)) as MB.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base in *; unfold region_base in R1, R2, Hlo; rewrite region_off_eq in Hlo by lia4; rewrite region_off_eq in R1 by lia4; rewrite region_off_eq in R2 by lia4;
clear - Hlo R1 R2 F3 F6 FA1 FB MB Hc'; numconst; unfold EV_MAX in *; zlia.
* apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p]; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext. numconst. unfold kPage in *. lia4.
+
apply in_rangesb_true in IR as (lo & len & Hin & Hlo).
assert (NEWG : (MU = mu2 /\ adr <= g < adr + kUserMapSize) \/ (MF = mf2 /\ fadr <= g < fadr + kFreeArrayMapSize)).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite Rc in Hin. unfold rG in Hin. cbn [rg_mapped_user rg_mapped_fa] in Hin.
assert (OLD : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = false -> ~ (region_base ly c <= g < region_base ly c + mu) /\ ~ (fa_base ly c <= g < fa_base ly c + mf)).
{ intros Hf. split; intros X; [assert (E : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = true) | assert (E : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = true)]; try (rewrite E in Hf; discriminate Hf);
[ exact (in_rangesb_In g [(region_base ly c, mu); (fa_base ly c, mf)] _ _ (or_introl eq_refl) X) | exact (in_rangesb_In g [(region_base ly c, mu); (fa_base ly c, mf)] _ _ (or_intror (or_introl eq_refl)) X) ]. }
assert (OLDF : in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)] = false).
{ destruct (in_rangesb g [(region_base ly c, mu); (fa_base ly c, mf)]) eqn:E; [|reflexivity]. exfalso.
assert (IN : in_rangesb g (fa_poison_ranges ly S) = true); [|rewrite IN in IR0; discriminate IR0].
apply in_rangesb_true in E as (lo' & len' & Hin' & Hlo'). apply (in_rangesb_In g _ lo' len'); [|exact Hlo'].
unfold fa_poison_ranges. apply in_app_iff. left. apply in_flat_map. exists c. split; [apply In_zseq; lia4|]. rewrite <- Hmu_def, <- Hmf_def. exact Hin'. }
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
destruct (OLD OLDF) as [O1 O2]. unfold region_base, fa_base in *. rewrite <- (proj1 (proj2 (proj2 (proj2 GE)))) in *. unfold RBv, FAv, SB in *. rewrite region_off_eq in * by lia4.
destruct Hin as [E|[E|[]]]; injection E as <- <-; [left | right]; (destruct HMU as [[EM _]|(EM & _)]; destruct HMF as [EM'|[EM' _]]; rewrite ?EM, ?EM' in *;
first [ split; [reflexivity | clear - Hlo O1 O2 GE G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *; zlia] | exfalso; clear - Hlo O1 O2 GE G33; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *; zlia ]).
+ exfalso. assert (IN : in_rangesb g (fa_poison_ranges ly S) = true); [|rewrite IN in IR0; discriminate IR0].
rewrite (Rreg c') in Hin by lia4. apply (in_rangesb_In g _ lo len); [|exact Hlo].
unfold fa_poison_ranges. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia4 | exact Hin].
- exfalso. assert (IN : in_rangesb g (fa_poison_ranges ly S) = true); [|rewrite IN in IR0; discriminate IR0].
apply (in_rangesb_In g _ lo len); [|exact Hlo]. unfold fa_poison_ranges. apply in_app_iff. right. exact Hin. }
assert (SHx : forall base, base mod 65536 = 0 -> base <= g < base + 262144 -> SHBv + base / 8 <= shadow_addr g < SHBv + base / 8 + 32768).
{ clear - Hg8. intros base Hb Hgb. unfold shadow_addr, SHBv, SHADOW_OFF. apply Z.mod_divide in Hb as [q Hq]; [|lia4]. rewrite Hq in Hgb |- *.
replace (q * 65536) with (q * 8192 * 8) by lia4. rewrite Z.div_mul by lia4. pose proof (Z.div_mod g 8 ltac:(lia4)). lia4. }
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _ & G13 & G14 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _ & G29 & G30 & _).
destruct NEWG as [[EM Hg]|[EM Hg]].
* pose proof (SHx adr G8 ltac:(unfold kUserMapSize in Hg; exact Hg)) as WND. rewrite <- G11 in WND.
assert (Rg : 0 <= shadow_addr g < 2 ^ 64) by (clear - WND G13 G14; zlia).
destruct (USHV EM (w64 (shadow_addr g)) ltac:(unfold w64; rewrite unsigned_lit_small by exact Rg; unfold W_USH; change (kUserMapSize / 8) with 32768; exact WND)) as [V Hh].
unfold rd', aview, mbyte, mrestrict. unfold w64 in V, Hh. rewrite Hh, V. reflexivity.
* pose proof (SHx fadr G25 ltac:(unfold kFreeArrayMapSize in Hg; exact Hg)) as WND. rewrite <- G27 in WND.
assert (Rg : 0 <= shadow_addr g < 2 ^ 64) by (clear - WND G29 G30; zlia).
destruct (FSHV EM (w64 (shadow_addr g)) ltac:(unfold w64; rewrite unsigned_lit_small by exact Rg; unfold W_FSH; change (kFreeArrayMapSize / 8) with 32768; exact WND)) as [V Hh].
unfold rd', aview, mbyte, mrestrict. unfold w64 in V, Hh. rewrite Hh, V. reflexivity.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi) | eapply own_shadow_zero; [exact MA | exact Hr | exact Hi] |].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof geo as GE.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _ & G13 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _ & G29 & _ & _ & _ & G33 & _).
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
pose proof (pairwise_ij _ _ 0 7 _ _ (lo_disj ly LY) eq_refl eq_refl) as PS. unfold zdisjoint in PS. cbn [fst snd] in PS.
apply Z.mod_divide in G8 as [qa Hqa]; [|clear; zlia]. apply Z.mod_divide in G25 as [qf Hqf]; [|clear; zlia].
assert (Esha : sha = SHBv + qa * 8192) by (rewrite G11, Hqa; replace (qa * 65536) with (qa * 8192 * 8) by (clear; zlia); rewrite Z.div_mul by (clear; zlia); reflexivity).
assert (Eshf : shf = SHBv + qf * 8192) by (rewrite G27, Hqf; replace (qf * 65536) with (qf * 8192 * 8) by (clear; zlia); rewrite Z.div_mul by (clear; zlia); reflexivity).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
-
cbn [fst snd] in *. unfold shadow_addr. pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(clear; zlia)) as D1. pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(clear; zlia)) as M1.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(clear; zlia)) as D2. pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(clear; zlia)) as M2.
apply Z_band; [clear - Hi T1 T2 T4 T7 D1 D2 M1 M2; numconst; unfold SHADOW_OFF; zlia | |]; intros [EQ Hs];
[unfold W_USH in Hs; rewrite Esha in Hs; change (kUserMapSize / 8) with 32768 in Hs; pose proof I as HF1
|unfold W_FSH in Hs; rewrite Eshf in Hs; change (kFreeArrayMapSize / 8) with 32768 in Hs; pose proof (FQ2 EQ) as [_ HF1]];
unfold SHBv, FAv in *; clear - Hi Hs T1 T2 T4 T7 D1 D2 M1 M2 PS Q1 Q2 GE Hqa Hqf HF1 G33; numconst; unfold SHADOW_OFF, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia.
-
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5). destruct r as [r1 r2]. cbn [fst snd] in *.
unfold shadow_addr. unfold kLowMemEnd in Z5. pose proof (Z.div_mod r1 8 ltac:(clear; zlia)) as D1. pose proof (Z.mod_pos_bound r1 8 ltac:(clear; zlia)) as M1.
pose proof (Z.div_mod r2 8 ltac:(clear; zlia)) as D2. pose proof (Z.mod_pos_bound r2 8 ltac:(clear; zlia)) as M2.
apply Z_band; [clear - Hi Z1 Z2 Z3 Z4 Z5 D1 D2 M1 M2; numconst; unfold SHADOW_OFF; zlia | |]; intros [EQ Hs];
[unfold W_USH in Hs; rewrite Esha in Hs; change (kUserMapSize / 8) with 32768 in Hs | unfold W_FSH in Hs; rewrite Eshf in Hs; change (kFreeArrayMapSize / 8) with 32768 in Hs];
unfold SHBv in *; clear - Hi Hs Z1 Z2 Z3 Z4 Z5 D1 D2 M1 M2 G13 G29 Esha Eshf; numconst; unfold SHADOW_OFF in *; zlia.
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly SG) /\ Forall (range_vis B ly rd') (aareas SG) /\ Forall (range_vis B ly rd') (aclient SG).
Proof.
pose proof SG_parts as (Rreg & Rc & Rinit & Rother & Rcl & Rch & Rsecs & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rnev).
pose proof derived_rangesR as DR. pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof geo as GE.
split; [|split].
-
unfold ajunk. rewrite Rch.
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. reflexivity. }
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. reflexivity. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
- unfold cache_junk. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks]. rewrite length_rev. fold NT.
constructor; [|apply Forall_nil]. intros i Hi. cbn [fst snd aeval] in *. apply apresent_vis. apply DSTP. unfold DSTv, Pr. clear - Hi GE K3. lia4.
- apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. apply in_app_iff; right. apply in_app_iff; left. apply in_flat_map. exists c'. split; [apply In_zseq; lia4|].
unfold cache_junk in *. rewrite Rinit, (Rother c') in Hx by lia4. exact Hx. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; do 2 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left.
unfold sec_junk in *. rewrite Rarr, Rres, Rch in Hx. exact Hx. }
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 4 (apply in_app_iff; right). apply in_app_iff; left.
unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 5 (apply in_app_iff; right). exact Hx.
-
unfold aareas. rewrite Rres, Rch.
apply Forall_app; split.
+ apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
* rewrite Rc. unfold rG. cbn [rg_mapped_user rg_mapped_fa].
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (ASp (region_off c), mu)
ltac:(unfold aareas; apply in_app_iff; left; apply in_flat_map; exists c; split; [apply In_zseq; lia4 | left; rewrite <- Hmu_def; reflexivity])) as RVU.
assert (ERB : ly_space ly + region_off c = RBv) by (rewrite RBv_is; reflexivity).
assert (EFA : ly_space ly + (region_off c + kFreeArrayOffset) = FAv) by (rewrite FAv_is; unfold fa_base; clear; zlia).
constructor; [|constructor; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in *; rewrite ?ERB, ?EFA.
-- destruct (Z_lt_le_dec i mu) as [L|L].
++ pose proof (RVU i ltac:(cbn [snd]; clear - Hi L GE; zlia)) as RV. cbn [fst snd aeval] in RV. rewrite ERB in RV.
apply (VIS_MONO (RBv + i) ltac:(clear - Hi L GE; numconst; unfold kFreeArrayOffset in *; zlia) RV);
unfold W_UW, W_FW; intros (_ & _ & X); clear - X L GE Hi; unfold kFreeArrayOffset in *; zlia.
++ destruct HMU as [[EM _]|(EM & _)]; [exfalso; clear - Hi L EM; zlia|].
apply apresent_vis. apply (UWP EM). clear - Hi L EM; zlia.
-- apply apresent_vis. apply FAP. clear - Hi; zlia.
* rewrite (Rreg c') by lia4. apply vis_keep. right; left. intros x Hx. unfold aareas. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia4 | exact Hx].
+ apply vis_keep. right; left. intros x Hx. unfold aareas. apply in_app_iff. right. exact Hx.
-
replace (aclient SG) with (aclient S); [apply vis_keep; right; right; intros x Hx; exact Hx|].
unfold aclient. rewrite Rfr, Rch. reflexivity.
Qed.
Definition abs_cell_okG (cc : acell) : bool :=
match c_at cc with
| ANum a => ((0x10000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x5fb000)) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x80050000))
| _ => false
end.
Lemma abs_cells_okG : forallb abs_cell_okG (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros cc Hin.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin)|].
intros k Hk. apply AGX; [exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin k Hk)|].
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof geo as GE.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC0.
pose proof (pairwise_ij _ _ 2 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DT. pose proof (pairwise_ij _ _ 0 6 _ _ (lo_disj ly LY) eq_refl eq_refl) as DP.
pose proof (Forall_nth' _ _ 7 _ (lo_app ly LY) eq_refl) as DH. cbv beta in DH. unfold in_app in DH. unfold zdisjoint in DT, DP. cbn [fst snd] in DT, DP, DH.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
unfold zdisjoint in CT, PC0. cbn [fst snd] in CT, PC0.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD in *;
first [ apply Z_img; clear - Hk; unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks; numconst; unfold kHighShadowBeg; zlia
| apply Z_T; unfold Pr, T in *; clear - Hk DR F1 F2 HcR; unfold kStackSpan in *; numconst; zlia
| apply Z_prim; unfold W_FEn, W_UW, W_FW, RGv, FAv, RBv, Pr, T, SB in *; clear - Hk DR F1 F2 F3 F4 F5 F6 F7 F8 CT PC0 Q1 Q2 GE HcR; numconst; unfold o_space, o_rinfo, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia
| apply Z_out; unfold T in *; clear - Hk DR F1 F2 F3 F4 F5 F6 F7 F8 CT PC0 DT DP DH; numconst; zlia ] |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okG cc Hin) as Hc. unfold abs_cell_okG in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbn [aeval].
apply Bool.orb_prop in Hc as [Hc|Hc]; apply andb_prop in Hc as [Hz Hc]; apply Z.leb_le in Hz; apply Z.leb_le in Hc; apply Z_img; lia4.
Qed.
Lemma AR_transportG : AR tfibsegs B ly SG Wd mem' (with_vm_backing (m_vm_lazy mdf) mat mdf).
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
pose proof SG_parts as (Rreg & Rc & Rinit & Rother & Rcl & Rch & Rsecs & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rnev).
split; [|split; [|split; [|split]]].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ exact WFG.
+ exact Mun.
+ exact Msy.
+ exact Mly.
+ unfold sec_placed in *. rewrite SG_sec_extents. exact Mpl.
+ exact const_final.
+ exact Mcow.
+ exact cells_final.
+ exact fa_final.
+ exact flags_final.
+ exact depot_final.
+ exact shadow_final.
+ exact zshadow_final.
+ exact (proj1 vis_final).
+ exact (proj1 (proj2 vis_final)).
+ exact (proj2 (proj2 vis_final)).
+ apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact MA | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia4.
* apply Z_img. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, kHighShadowBeg in *; lia4.
+ exact Mts.
+   exact Msi.
- exact (ALedger_same tfibsegs ly SG mdf _ HL (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) ltac:(unfold eager_used; rewrite m_vmmaps_wvb, m_vm_lazy_wvb; reflexivity)).
-   destruct BUD as [BUD PIN]. split; [| intros e He; rewrite SG_sec_extents in He; destruct (PIN e He) as [P1 P2]; split; [exact (HINC _ P1) | exact (HINC _ P2)]].
unfold abudget, sec_hulls in *. rewrite Rnev, Rsecs  . unfold sec_live_bytes in *. rewrite Rch. pose proof HSL as SL. unfold EV_A in *. clear - BUD HBUD SL. lia4.
- exact (amwf_same mdf _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) HMW).
-
destruct HS0 as [HS0 HZ0]. split.
{ intros a Ha NCL HV. pose proof geo as GE.
assert (NC0 : ~ aclient_byte B ly S a).
{ intros CL. apply NCL. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)]; [left; exists k; rewrite Rch; exact (conj Hk (conj Hst Hr)) | right; exists cp; rewrite Rfr; exact (conj Hcp Hr)]. }
assert (HV0 : w_H W (YG0n.w64 a) = true \/ ~ in_vis0 ly a) by (destruct HV as [Hh|Hv]; [left; exact (HSUB _ Hh) | right; exact Hv]).
pose proof (HS0 a Ha NC0 HV0) as X0.
destruct (NOREM (YG0n.w64 a) X0) as [NN | [[_ Hw]|[_ Hw]]]; [exact NN | exfalso | exfalso]; unfold YG0n.w64 in Hw;
rewrite unsigned_lit_small in Hw by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; zlia); unfold W_UW, W_FW in Hw;
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _); rewrite <- RBv_is in Q1, Q2; clear - Ha Hw GE Q1 Q2; numconst; unfold kHighShadowBeg, kHighShadowEnd, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; zlia. }
apply (ahz_keep ly S SG mem0 mem'); [|exact HZ0]. intros g Hg Happ HF.
assert (HF0 : hfree ly S g) by (unfold hfree in HF |- *; unfold sec_extents in HF |- *; rewrite Rch in HF; exact HF). split; [exact HF0|].
pose proof (shadow_addr_band_rw g Happ) as SBg. unfold in_band_rw, kLowShadowEnd in SBg.
assert (Hlo : 4096 <= g) by (clear - Happ; unfold in_app in Happ; zlia). pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof derived_rangesR as DR.
pose proof (zone3_apart_hsh _ _ (shadow_addr g) F1) as TH.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). pose proof Hsp as (S1 & _).
assert (GP : g + 8 <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= g).
{ unfold hfree in HF0. exact (proj1 (Forall_forall _ _) HF0 (ly_prim ly, kPrimResvSize)
ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; apply in_app_iff; left; left; reflexivity)). }
assert (G0 : 0 <= g) by (clear - Hlo; zlia).
assert (RP : ly_prim ly <= RBv /\ RBv + 2 ^ 32 <= ly_prim ly + kPrimResvSize) by (clear - F4 F5 DR; unfold kSpaceSize, kPrimResvSize in *; zlia).
assert (AP : forall x y, RBv <= x -> y <= RBv + 2 ^ 32 -> shadow_addr g + 1 <= shadow_addr x \/ SHADOW_OFF + y / 8 <= shadow_addr g).
{ intros x y Hx Hy. apply shadow_apart; [exact Hg | exact G0 | clear - Hx RP F3; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *; zlia | clear - GP RP Hx Hy; zlia]. }
unfold w64. apply MEQ; rewrite unsigned_lit_small by (clear - SBg; unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd in SBg; zlia).
+ clear - SBg S1 T7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. unfold sp0 in *. zlia.
+ intros X. apply XC_where in X. destruct X as [[X _]|[X|[[X _]|[_ X]]]].
* clear - X SBg TH. unfold zone3, kThreadObjSize, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. unfold T in *. zlia.
* clear - X SBg DR. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. zlia.
* clear - X SBg DR. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. zlia.
* pose proof Hmu as (U0 & U1 & U2 & _). pose proof Hmf as [M0f M1f].
destruct X as [[EM HWs]|[EM HWs]].
--
assert (UQ : mu2 <= kFreeArrayOffset) by (destruct HMU as [[E1 _]|(E1 & E2 & _)]; [rewrite EM in E1; rewrite Hmu2 in E1; unfold kUserMapSize in E1; zlia | exact (proj2 (HUQ E2))]).
destruct (AP adr (adr + kUserMapSize) ltac:(rewrite Hadr; zlia) ltac:(rewrite Hadr; rewrite Hmu2 in UQ; clear - UQ U0 U1; unfold kUserMapSize, kFreeArrayOffset in *; zlia)) as [Y|Y];
unfold W_USH in HWs; rewrite Hsha in HWs; unfold SHBv in HWs; unfold shadow_addr, SHADOW_OFF in *; [clear - HWs Y; zlia|].
assert (A8 : (adr + kUserMapSize) / 8 = adr / 8 + kUserMapSize / 8).
{ apply Z.mod_divide in U2 as [q Hq]; [|unfold kUserMapSize; zlia]. pose proof DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB16 & _).
apply Z.mod_divide in RB16 as [p Hp]; [|zlia]. rewrite Hadr, Hq, Hp. unfold kUserMapSize.
replace (p * 65536 + q * 262144 + 262144) with ((p * 8192 + q * 32768 + 32768) * 8) by zlia. replace (p * 65536 + q * 262144) with ((p * 8192 + q * 32768) * 8) by zlia.
rewrite !Z.div_mul by zlia. reflexivity. }
rewrite A8 in Y. clear - HWs Y. zlia.
--
assert (FQ : mf2 <= kFreeArrayMax) by (destruct HMF as [E1|[E1 E2]]; [rewrite EM in E1; rewrite Hmf2 in E1; unfold kFreeArrayMapSize in E1; zlia | exact (HFQ E2)]).
destruct (AP fadr (fadr + kFreeArrayMapSize) ltac:(rewrite Hfadr; unfold FAv; clear - M0f; unfold kFreeArrayOffset; zlia)
ltac:(rewrite Hfadr; unfold FAv; rewrite Hmf2 in FQ; clear - FQ M0f; unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *; zlia)) as [Y|Y];
unfold W_FSH in HWs; rewrite Hshf in HWs; unfold SHBv in HWs; unfold shadow_addr, SHADOW_OFF in *; [clear - HWs Y; zlia|].
assert (A8 : (fadr + kFreeArrayMapSize) / 8 = fadr / 8 + kFreeArrayMapSize / 8).
{ apply Z.mod_divide in M1f as [q Hq]; [|unfold kFreeArrayMapSize; zlia]. pose proof DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB16 & _).
apply Z.mod_divide in RB16 as [p Hp]; [|zlia]. rewrite Hfadr. unfold FAv. rewrite Hq, Hp. unfold kFreeArrayMapSize, kFreeArrayOffset.
replace (p * 65536 + 3758096384 + q * 262144 + 262144) with ((p * 8192 + 469762048 + q * 32768 + 32768) * 8) by zlia.
replace (p * 65536 + 3758096384 + q * 262144) with ((p * 8192 + 469762048 + q * 32768) * 8) by zlia.
rewrite !Z.div_mul by zlia. reflexivity. }
rewrite A8 in Y. clear - HWs Y. zlia.
Qed.
Lemma XC_owned : forall a, 0 <= a < 2 ^ 64 -> XC a -> aowned B ly S a.
Proof.
intros a Ra Hx. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & _). pose proof class_facts as (_ & _ & K3 & _). pose proof geo as GE.
pose proof (region_in_prim ly c LY HcR) as (Q1 & Q2 & _). rewrite <- RBv_is in Q1, Q2.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & _ & G11 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & G27 & _).
assert (OT : forall b, T <= b < T + kThreadObjSize -> aowned B ly S b).
{ intros b Hb. apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) b MA); [unfold core_extents; cbn; tauto | cbn [fst snd]; unfold T in Hb; exact Hb]. }
apply XC_where in Hx. destruct Hx as [[Hx _] | [Hx | [[Hp Hx] | [Hb Hx]]]].
- apply OT. exact Hx.
- apply (own_rinfo B ly S rd0 a MA). unfold RGv, SB in Hx. clear - Hx HcR. numconst. lia4.
-
apply (own_prim_nonuser B ly S rd0 a MA); [clear - Hp Q1 Q2; zlia|].
intros k Hk Hst Hu. pose proof (chunk_facts B ly S rd0 k MA Hk) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & GG).
destruct (ck_beg k) as [|o|r o|c'' p'] eqn:Eb; try solve [destruct GG].
+ cbv zeta in GG. destruct GG as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
pose proof (mapped_user_bound (as_universe B) 0 0 0 S (prim_class o) WF ltac:(lia4)) as MB.
destruct (Z.eq_dec (prim_class o) c) as [EC|NE].
* rewrite EC in *. rewrite <- Hau_def, <- Hmu_def in D9. rewrite <- Hau_def in D8. unfold W_FEn, W_UW, W_FW in Hx. unfold region_base in D5. rewrite region_off_eq in D5, D6, D8 by lia4.
unfold FAv, RBv, SB in *. destruct Hx as [Hx|[[_ Hx]|[_ Hx]]]; clear - Hp Hx Hu C5 C8 D4 D5 D6 D8 D9 GE K3; numconst; unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *; nia.
* unfold W_FEn, W_UW, W_FW in Hx. unfold region_base in D5. rewrite region_off_eq in D5, D6, D8 by lia4.
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
unfold FAv, RBv, SB in *. destruct Hx as [Hx|[[_ Hx]|[EQ Hx]]]; [| | pose proof (HFQ EQ) as HF1]; first [pose proof I as HF1 | idtac];
clear - Hp Hx Hu C5 C8 D1 D4 D5 D6 D8 D9 MB NE GE HcR HNF HF1 G33; numconst; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *; nia.
+ destruct GG as (X0 & X1 & X2 & X3 & Hin & _).
pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ _ (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. clear - Hp Hu D C5 C8 X2 X3 Q1 Q2; unfold kPage in *. zlia.
-
set (g := (a - SHADOW_OFF) * 8).
assert (Eg : shadow_addr g = a) by (unfold shadow_addr; subst g; rewrite Z.div_mul by lia4; lia4).
pose proof facts3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G33 & _).
assert (HF1 : MF = mf2 -> mf2 <= kFreeArrayMax) by (intros EQ; exact (proj2 (FQ2 EQ))).
rewrite <- Eg. apply (own_shadow_prim B ly S rd0 g MA). subst g. unfold W_USH, W_FSH in Hx. rewrite G11, G27 in Hx. unfold SHBv, SHADOW_OFF in Hx |- *.
apply Z.mod_divide in G8 as [q Hq]; [|clear; zlia]. apply Z.mod_divide in G25 as [q' Hq']; [|clear; zlia].
rewrite Hq, Hq' in Hx. replace (q * 65536) with (q * 8192 * 8) in Hx by (clear; zlia). replace (q' * 65536) with (q' * 8192 * 8) in Hx by (clear; zlia). rewrite !Z.div_mul in Hx by (clear; zlia).
unfold FAv in *. unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax in *. change (262144 / 8) with 32768 in *.
destruct Hx as [[_ Hx]|[EQ Hx]]; [clear HF1; pose proof I as HF1 | specialize (HF1 EQ)]; clear - Hx Hq Hq' Q1 Q2 GE HF1 G33; zlia.
Qed.
Lemma LEAF_G : forall W' c' (P : (word -> option byte) -> Prop),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdf) mat mdf) -> W' = Wd ->
getr regs' 10 = Z_to_bv 64 (if (length TOPS =? 0)%nat then 0 else 1) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
wle W Wd -> same_io md0 mdf ->
refill_leaf B ly S W regs0 mem0 md0 c (tt, SG) W' c'.
Proof.
intros W' c' P -> -> R10 RCS LE IO.
exists regs', mem', (with_vm_backing (m_vm_lazy mdf) mat mdf).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
cbn [fst snd]. split.
- split; [exact AR_transportG|].
split; [apply layout_le_refl|].
split; [exact LE|].
split. { intros r Hr. apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia4.
clear - RCS H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia4; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(lia4) 2%bv eq_refl) | rewrite (E5 3 ltac:(lia4) 3%bv eq_refl) | rewrite (E5 4 ltac:(lia4) 4%bv eq_refl)
| rewrite (E5 8 ltac:(lia4) 8%bv eq_refl) | rewrite (E5 9 ltac:(lia4) 9%bv eq_refl) | rewrite (E5 18 ltac:(lia4) 18%bv eq_refl)
| rewrite (E5 19 ltac:(lia4) 19%bv eq_refl) | rewrite (E5 20 ltac:(lia4) 20%bv eq_refl) | rewrite (E5 21 ltac:(lia4) 21%bv eq_refl)
| rewrite (E5 22 ltac:(lia4) 22%bv eq_refl) | rewrite (E5 23 ltac:(lia4) 23%bv eq_refl) | rewrite (E5 24 ltac:(lia4) 24%bv eq_refl)
| rewrite (E5 25 ltac:(lia4) 25%bv eq_refl) | rewrite (E5 26 ltac:(lia4) 26%bv eq_refl) | rewrite (E5 27 ltac:(lia4) 27%bv eq_refl) ];
cbn [In]; tauto. }
split. { destruct IO as (I1 & I2 & I3 & I4). unfold same_io. destruct mdf; cbn in *; repeat split; assumption. }
split.
+ intros a Ra NO NO' NS NE. unfold rd' in *. unfold aview, mbyte, mrestrict.
assert (NSC : ~ (sp0 - RSTACK <= a < sp0)) by (intros Hs; apply NS; unfold ascratch, spZ; left; exact Hs).
assert (NX : ~ XC a) by (intros Hx; exact (NO (XC_owned a Ra Hx))).
rewrite (HVIS (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ra; exact NX).
rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ra; assumption). reflexivity.
+ intros a Ha. exact (PRS a Ha).
- rewrite R10. pose proof SG_parts as (_ & _ & _ & _ & Rcl & _). rewrite Rcl. cbn [pc_chunks].
destruct TOPS as [|x t]; [reflexivity|]. cbn [length Nat.eqb]. destruct (rev (x :: t)) as [|y u] eqn:Er; [|reflexivity].
exfalso. apply (f_equal (@length Z)) in Er. rewrite length_rev in Er. cbn in Er. lia4.
Qed.
End a0.
End z.
End l.

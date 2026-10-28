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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhm AFka AFkk.
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
Definition PT : (word -> option byte) -> Prop := fun _ => True.
Lemma pstable_PT : pstable PT. Proof. clear3. intros m m' _ _. exact I. Qed.
Lemma WX0 : forall a, WINR0 a -> WINR0 a. Proof. clear3. intros a H; exact H. Qed.
Lemma at_R3_init : at_R3 W md0 WINR0 PT R3_J W cfg0.
Proof. exact SEEDJ. Qed.
Lemma seg3J : forall mat, st_ok tfibsegs E0 SS0R3 (restrict (w_H W) (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) (at_R3 W md0 WINR0 PT R3_J).
Proof.
intros mat SEED0. pose proof pstable_PT as HP.
assert (HR : at_R3 W md0 WINR0 PT SS0R3 W (mkCfg (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0))).
{ clear - SEED0 Hpres0R. split; [reflexivity|]. exists (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs)), mat, E0. split; [reflexivity|].
split; [split; [intros; reflexivity | reflexivity]|]. split; [exact SEED0|]. split; [intros; reflexivity|]. split; [exact Hpres0R | exact I]. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36124 (runto 0x36124 SS0R3) WX0 HP.
r3_forget HR hJ0 CLOB_INIT. r3_noconds HR. r3_station HR R3_J.
apply SRr_ret. exact HR.
Qed.
Lemma land_hi0 : forall x, 0 <= x < 2 ^ 18 -> Z.land x (2 ^ 64 - 2 ^ 18) = 0.
Proof. clear.
intros x Hx. replace (2 ^ 64 - 2 ^ 18) with (Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
destruct (Z_lt_le_dec i 18) as [L|L].
- rewrite (Z.ones_spec_low 18 i) by zlia. cbn [negb]. rewrite !Bool.andb_false_r. reflexivity.
- rewrite (Z.bits_above_log2 x i); [reflexivity | zlia |]. destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; zlia|].
apply (Z.lt_le_trans _ 18); [|zlia]. apply Z.log2_lt_pow2; zlia.
Qed.
Lemma seg3P : SRr tfibsegs W cfg0 (at_R3 W md0 WINR0 PT R3_P).
Proof.
pose proof at_R3_init as HR. pose proof pstable_PT as HP.
pose proof class_facts as (CF1 & CF2 & CF3 & CF4 & CF5). pose proof derived_rangesR as DR. pose proof high_factsR as LF.
pose proof Hnf as [NF1 NF2]. pose proof Hmf as [MF1 MF2]. pose proof Hmu as (MU1 & MU2 & MU3 & MU4). pose proof facts3 as (G1 & _).
clear Hcarved Hau_al Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in DR, LF.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36128 R3_10 WX0 HP.
r3_pin HR (9%bv : bv 5) (SOff rN 0).
{ clear - CF1 CF2 CF3 Hn. pin_zev3. unfold rN, rMAX. rewrite EaN, EaMAX. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (maxc + 0)) by (unfold M64; zlia). rewrite (zcanon_id 1) by (unfold M64; zlia). rewrite (zcanon_id (n + 0)) by (unfold M64; zlia).
rewrite (Z.mod_small (maxc + 0)) by zlia. change (Z.land (1 mod 2 ^ 32) 31) with 1.
rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 1) with 2. rewrite !Z.add_0_r, <- Hn.
rewrite bv_swrap_small. 2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2) with 2147483648. zlia. }
rewrite bv_wrap_small. 2:{ unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. zlia. } reflexivity. }
r3_station HR R3_1.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36284 R3_A0 WX0 HP.
r3_pin HR (8%bv : bv 5) (SOff rRG 0).
{ clear - SB DR LF HcR. pin_zev3. unfold rRG, rSB, rCL. rewrite EaRG, EaSB, EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 7) with 128. zcanon_simp. unfold RGv, kRegionInfoOff in *. unfold SB in *. zlia. }
r3_pin HR (20%bv : bv 5) (SOff rFA 0).
{ clear - SB DR LF HcR. pin_zev3. unfold rFA, rSB, rCL. rewrite EaFA, EaSB, EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. zcanon_simp. unfold FAv, RBv, kFreeArrayOffset in *. unfold SB in *. zlia. }
r3_station HR R3_A.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36358 R3_B WX0 HP.
r3_arm HR BC_LTU true (SOff rNF 0) (SOff rN 0).
{ clear - NF1 NF2 MF1 CF3 Hnlt. rewrite branch_ltu_U. unfold rNF, rN. rewrite (U_atom E0 44 nf EaNF), (U_atom E0 39 n EaN); [|zlia| unfold kFreeArrayMax in *; zlia]. apply Z.ltb_lt. exact Hnlt. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36544 R3_P0 WX0 HP.
r3_pin HR (14%bv : bv 5) (SOff rNEED 0).
{ clear - NF1 NF2 MF1 CF3 Hnlt G1 Hneed. pin_zev3. unfold rNEED, rN, rNF. rewrite EaNEED, EaN, EaNF. unfold w64. rewrite !unsigned_lit_small by (unfold kFreeArrayMax in *; zlia).
rewrite (zcanon_id (need + 0)), (zcanon_id (n + 0)), (zcanon_id (nf + 0)) by (unfold M64, kFreeArrayMax in *; zlia).
unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite Zplus_mod_idemp_r.
replace (n + 0 + (nf + 0) * (2 ^ 64 - 1)) with (need + nf * 2 ^ 64) by (rewrite Hneed; zlia).
rewrite Z_mod_plus_full. rewrite Z.add_0_r. symmetry. apply Z.mod_small. zlia. }
r3_station HR R3_P. apply SRr_ret. exact HR.
Qed.
Definition T16 : sv := SAlu ALU_SLL (SOff 36 0) (SLit 5).
Definition TMID : sv :=
SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SOff 36 0) (SLit 63)) (SLit 63)) (SAlu ALU_SRL (SAlu ALU_SLL (SLit 512) (SAlu ALU_SRL (SOff 36 (-16)) (SLit 1))) (SLit 1)))
(SAlu ALU_SLL (SLit 512) (SAlu ALU_SRL (SOff 36 (-16)) (SLit 1))).
Lemma U_csz : U E0 (SOff rCSZ 0) = csz.
Proof. clear3. pose proof class_facts as (_ & _ & _ & K4 & _). unfold rCSZ. apply (U_atom E0 40 csz EaCSZ). unfold kMaxSize in K4. zlia. Qed.
Lemma U_csz31 : c = 31 -> U E0 (SLit 64) = csz.
Proof. clear3. intros E. rewrite Hcsz, E. reflexivity. Qed.
Lemma U_csz16 : c <= 16 -> c <> 31 -> U E0 T16 = csz.
Proof. clear3.
intros L N. rewrite (U_zev E0 T16 eq_refl). cbn [zev zalu_raw zmd_raw T16]. unfold rho_of. rewrite EaCL. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (c + 0)), (zcanon_id 5) by (unfold M64; zlia). change (Z.land 5 63) with 5. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 5) with 32.
rewrite zcanon_id by (unfold M64; zlia). rewrite Hcsz. unfold class_size.
replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; exact N). replace (c <=? 16) with true by (symmetry; apply Z.leb_le; exact L). zlia.
Qed.
Lemma U_cszmid : 17 <= c <= 30 -> U E0 TMID = csz.
Proof. clear3.
intros R. rewrite (U_zev E0 TMID eq_refl). cbn [zev zalu_raw zmd_raw TMID]. unfold rho_of. rewrite EaCL. unfold w64. rewrite !unsigned_lit_small by zlia. rewrite Hcsz.
clear - R. assert (H : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by zlia.
clear R. destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]; rewrite E; vm_compute; reflexivity.
Qed.
Lemma U_tot_of : forall t, U E0 t = csz -> svpure t = true ->
U E0 (SOff rTOT 0) = U E0 (SAlu ALU_ADD (SOff 46 0) (SMd M_MUL t (SOff 55 0))).
Proof.
intros t Ht Hp. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof Hmu as ([U0 U1] & U2 & _). pose proof class_facts as (_ & _ & _ & K4 & _). clear3.
rewrite (U_zev E0 (SAlu ALU_ADD (SOff 46 0) (SMd M_MUL t (SOff 55 0)))) by (cbn [svpure andb]; rewrite Hp; reflexivity).
cbn [zev zalu_raw zmd_raw]. rewrite <- (U_zev E0 t Hp), Ht. unfold rho_of, rTOT. rewrite EaAU, EaNEED.
rewrite (U_atom E0 56 tot EaTOT) by (unfold kMaxSize, kFreeArrayOffset in *; nia).
unfold w64. rewrite !unsigned_lit_small by (unfold kFreeArrayOffset in *; zlia).
rewrite (zcanon_id (au + 0)), (zcanon_id (need + 0)) by (unfold M64, kFreeArrayOffset in *; zlia).
rewrite (zcanon_id (csz * (need + 0))) by (unfold M64, kMaxSize in *; nia). rewrite zcanon_id by (unfold M64, kMaxSize, kFreeArrayOffset in *; nia). rewrite G5. zlia.
Qed.
Lemma U_tot31 : c = 31 -> U E0 (SOff rTOT 0) = U E0 (SAlu ALU_ADD (SOff 46 0) (SAlu ALU_SLL (SOff 55 0) (SLit 6))).
Proof.
intros E. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof Hmu as ([U0 U1] & U2 & _).
assert (C64 : csz = 64) by (rewrite Hcsz, E; reflexivity). clear3.
pin_zev3. unfold rTOT. rewrite EaAU, EaNEED, EaTOT. unfold w64. rewrite !unsigned_lit_small by (unfold kMaxSize, kFreeArrayOffset in *; nia).
rewrite (zcanon_id (au + 0)), (zcanon_id (need + 0)), (zcanon_id 6) by (unfold M64, kFreeArrayOffset in *; zlia). change (Z.land 6 63) with 6.
rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 6) with 64. rewrite (zcanon_id ((need + 0) * 64)) by (unfold M64; zlia).
rewrite !zcanon_id by (unfold M64, kFreeArrayOffset in *; zlia). rewrite G5, C64. zlia.
Qed.
Lemma U_rb : U E0 (SOff rRB 0) = U E0 (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 36 0) (SLit 32))).
Proof. clear3.
pose proof derived_rangesR as DR. pose proof high_factsR as (_ & _ & F3 & F4 & F5 & F6 & _).
pin_zev3. unfold rRB. rewrite EaRB, EaSB, EaCL. unfold w64. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize in *.
rewrite !unsigned_lit_small by (unfold SB; zlia).
rewrite (zcanon_id (c + 0)), (zcanon_id 32), (zcanon_id (ly_space ly + 0)) by (unfold M64; zlia). change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2 by zlia. rewrite (zcanon_id ((c + 0) * 2 ^ 32)) by (unfold M64; zlia).
rewrite !zcanon_id by (unfold M64, RBv, SB in *; zlia). unfold RBv, SB. zlia.
Qed.
Lemma seg3Q31 : c = 31 -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfibsegs W' c' (at_R3 W md0 WINR0 PT R3_Q31).
Proof.
intros E W' c' HR. pose proof pstable_PT as HP.
r3_arm HR BC_EQ true (SOff rCL 0) (SLit 31).
{ rewrite branch_eq_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (clear - HcR; zlia). apply Z.eqb_eq. rewrite E. reflexivity. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36760 R3_Q31a WX0 HP.
r3_pin HR (21%bv : bv 5) (SOff rCSZ 0). { rewrite U_csz. symmetry. exact (U_csz31 E). }
r3_pin HR (19%bv : bv 5) (SOff rTOT 0). { exact (U_tot31 E). }
r3_pin HR (18%bv : bv 5) (SOff rRB 0). { exact U_rb. }
r3_station HR R3_Q31. apply SRr_ret. exact HR.
Qed.
Lemma seg3Q16 : c <= 16 -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfibsegs W' c' (at_R3 W md0 WINR0 PT R3_Q16).
Proof.
intros L W' c' HR. pose proof pstable_PT as HP. assert (N : c <> 31) by (clear - L; zlia).
r3_arm HR BC_EQ false (SOff rCL 0) (SLit 31).
{ rewrite branch_eq_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (clear - HcR; zlia). apply Z.eqb_neq. rewrite (U_zev E0 (SLit 31) eq_refl). change (zev (rho_of E0) (SLit 31)) with 31. exact N. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x3654c R3_Pn31 WX0 HP.
r3_arm HR BC_LTU false (SLit 16) (SOff rCL 0).
{ rewrite branch_ltu_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (clear - HcR; zlia). rewrite (U_zev E0 (SLit 16) eq_refl). change (zev (rho_of E0) (SLit 16)) with 16. apply Z.ltb_ge. exact L. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36568 R3_Q16a WX0 HP.
r3_pin HR (21%bv : bv 5) (SOff rCSZ 0). { rewrite U_csz. symmetry. exact (U_csz16 L N). }
r3_pin HR (19%bv : bv 5) (SOff rTOT 0). { exact (U_tot_of T16 (U_csz16 L N) eq_refl). }
r3_pin HR (18%bv : bv 5) (SOff rRB 0). { exact U_rb. }
r3_station HR R3_Q16. apply SRr_ret. exact HR.
Qed.
Lemma seg3Qmid : 17 <= c <= 30 -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfibsegs W' c' (at_R3 W md0 WINR0 PT R3_Qmid).
Proof.
intros R W' c' HR. pose proof pstable_PT as HP. assert (N : c <> 31) by (clear - R; zlia).
r3_arm HR BC_EQ false (SOff rCL 0) (SLit 31).
{ rewrite branch_eq_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (clear - HcR; zlia). apply Z.eqb_neq. rewrite (U_zev E0 (SLit 31) eq_refl). change (zev (rho_of E0) (SLit 31)) with 31. exact N. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x3654c R3_Pn31 WX0 HP.
r3_arm HR BC_LTU true (SLit 16) (SOff rCL 0).
{ rewrite branch_ltu_U. unfold rCL. rewrite (U_atom E0 36 c EaCL) by (clear - HcR; zlia). rewrite (U_zev E0 (SLit 16) eq_refl). change (zev (rho_of E0) (SLit 16)) with 16. apply Z.ltb_lt. clear - R; zlia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365a8 R3_Qmida WX0 HP.
r3_pin HR (21%bv : bv 5) (SOff rCSZ 0). { rewrite U_csz. symmetry. exact (U_cszmid R). }
r3_pin HR (19%bv : bv 5) (SOff rTOT 0). { exact (U_tot_of TMID (U_cszmid R) eq_refl). }
r3_pin HR (18%bv : bv 5) (SOff rRB 0). { exact U_rb. }
r3_station HR R3_Qmid. apply SRr_ret. exact HR.
Qed.
Lemma U_mu : U E0 (SOff rMU 0) = mu.
Proof. clear3. pose proof Hmu as ([U0 U1] & U2 & _). unfold rMU. apply (U_atom E0 47 mu EaMU). unfold kFreeArrayOffset in *; zlia. Qed.
Lemma U_tot : U E0 (SOff rTOT 0) = tot.
Proof. pose proof facts3 as (G1 & _ & G3 & _ & G5 & _). pose proof Hmu as ([U0 U1] & U2 & _). pose proof class_facts as (_ & _ & _ & K4 & _). unfold rTOT. apply (U_atom E0 56 tot EaTOT). clear - G1 G3 G5 U0 U1 U2 K4. unfold kMaxSize, kFreeArrayOffset in *; nia. Qed.
Lemma seg3Q_map : mu < tot -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfibsegs W' c' (at_R3 W md0 WINR0 PT R3_M).
Proof.
intros Hlt W' c' HR. pose proof pstable_PT as HP.
assert (BT : branch_taken BC_LTU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = true) by (rewrite branch_ltu_U, U_mu, U_tot; apply Z.ltb_lt; exact Hlt).
assert (BF : branch_taken BC_GEU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = false) by (rewrite branch_geu_U, U_mu, U_tot; rewrite (proj2 (Z.ltb_lt mu tot) Hlt); reflexivity).
destruct (Z.eq_dec c 31) as [E|N]; [|destruct (Z_le_dec c 16) as [L|G]].
- eapply SRr_bind; [exact (seg3Q31 E W' c' HR)|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU true (SOff rMU 0) (SOff rTOT 0); [exact BT|].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365ac (runto 0x365ac (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q31)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. r3_station HR R3_M. apply SRr_ret. exact HR.
- eapply SRr_bind; [exact (seg3Q16 L W' c' HR)|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU true (SOff rMU 0) (SOff rTOT 0); [exact BT|].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365ac (runto 0x365ac (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q16)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_M_16 in HR. apply SRr_ret. exact HR.
- eapply SRr_bind; [exact (seg3Qmid ltac:(zlia) W' c' HR)|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_GEU false (SOff rMU 0) (SOff rTOT 0); [exact BF|].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365ac (runto 0x365ac (arm BC_GEU false (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_M_mid in HR. apply SRr_ret. exact HR.
Qed.
Lemma seg3Q_ok : tot <= mu -> forall W' c', at_R3 W md0 WINR0 PT R3_P W' c' -> SRr tfibsegs W' c' (at_R3 W md0 WINR0 PT R3_Ke).
Proof.
intros Hge W' c' HR. pose proof pstable_PT as HP.
assert (BF : branch_taken BC_LTU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = false) by (rewrite branch_ltu_U, U_mu, U_tot; apply Z.ltb_ge; zlia).
assert (BT : branch_taken BC_GEU (sv_denot E0 (SOff rMU 0)) (sv_denot E0 (SOff rTOT 0)) = true) by (rewrite branch_geu_U, U_mu, U_tot; rewrite (proj2 (Z.ltb_ge mu tot) Hge); reflexivity).
destruct (Z.eq_dec c 31) as [E|N]; [|destruct (Z_le_dec c 16) as [L|G]].
- eapply SRr_bind; [exact (seg3Q31 E W' c' HR)|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU false (SOff rMU 0) (SOff rTOT 0); [exact BF|].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36680 (runto 0x36680 (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q31)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. r3_station HR R3_Ke. apply SRr_ret. exact HR.
- eapply SRr_bind; [exact (seg3Q16 L W' c' HR)|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_LTU false (SOff rMU 0) (SOff rTOT 0); [exact BF|].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36680 (runto 0x36680 (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q16)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_Ke_16 in HR. apply SRr_ret. exact HR.
- eapply SRr_bind; [exact (seg3Qmid ltac:(zlia) W' c' HR)|]. clear HR. intros W2 c2 _ HR.
r3_arm HR BC_GEU true (SOff rMU 0) (SOff rTOT 0); [exact BT|].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x36680 (runto 0x36680 (arm BC_GEU true (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) WX0 HP.
r3_forget HR hJ1 CLOB_J1. r3_noconds HR. rewrite R3_Ke_mid in HR. apply SRr_ret. exact HR.
Qed.
Lemma seg3M : mu < tot -> mu + kUserMapSize <= kFreeArrayOffset ->
forall W' c', at_R3 W md0 WINR0 PT R3_M W' c' -> SRr tfibsegs W' c' (at_N3 W md0 WINR0 PT R3_NU).
Proof.
intros Hlt Hroom W' c' HR. pose proof pstable_PT as HP. pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & _).
pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
assert (J2 : SRr tfibsegs W' c' (at_R3 W md0 WINR0 PT R3_M2)).
{ destruct (Z.eq_dec mu 0) as [Z0|NZ].
- r3_arm HR BC_EQ true (SOff rMU 0) (SLit 0). { rewrite branch_eq_U, U_mu. apply Z.eqb_eq. rewrite Z0. reflexivity. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365b0 R3_M2z WX0 HP.
r3_pin HR (20%bv : bv 5) (SOff rMU 0). { rewrite U_mu, Z0. reflexivity. }
r3_forget HR hJ2 [11%bv : bv 5]. r3_noconds HR. rewrite R3_M2_z in HR. apply SRr_ret. exact HR.
- r3_arm HR BC_EQ false (SOff rMU 0) (SLit 0). { rewrite branch_eq_U, U_mu. apply Z.eqb_neq. change (U E0 (SLit 0)) with 0. exact NZ. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365b0 (runto 0x365b0 (arm BC_EQ false (SOff rMU 0) (SLit 0) R3_M)) WX0 HP.
r3_forget HR hJ2 [11%bv : bv 5]. r3_noconds HR. r3_station HR R3_M2. apply SRr_ret. exact HR. }
clear HR. eapply SRr_bind; [exact J2|]. clear J2. intros W2 c2 _ HR.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365cc (runto 0x365cc R3_M2) WX0 HP.
r3_pin HR (19%bv : bv 5) (SLit 262144).
{ pin_zev3. rewrite EaTOT, EaMU. unfold w64. rewrite !unsigned_lit_small by (clear - G3 G4 G5 U0 U1 U2; unfold kMaxSize, kFreeArrayOffset in *; zlia).
clear - G3 G4 G5 U0 U1 U2 Hlt. unfold kMaxSize, kFreeArrayOffset in *.
rewrite (zcanon_id (tot + 0)), (zcanon_id (mu + 0)) by (unfold M64; zlia). change (zcanon (-1)) with (2 ^ 64 - 1). change (zcanon (-262144)) with (2 ^ 64 - 2 ^ 18).
rewrite lxor_ones64 by zlia. rewrite (zcanon_id (2 ^ 64 - 1 - (mu + 0))) by (unfold M64; zlia).
replace (zcanon (tot + 0 + (2 ^ 64 - 1 - (mu + 0)))) with (tot - mu - 1).
2:{ unfold zcanon, M64. replace (tot + 0 + (2 ^ 64 - 1 - (mu + 0))) with ((tot - mu - 1) + 1 * 2 ^ 64) by zlia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. zlia. }
rewrite land_hi0 by zlia. reflexivity. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x365e0 R3_M4 WX0 HP.
r3_arm HR BC_GEU false (SOff rMU 262144) (SLit 3758096385).
{ rewrite branch_geu_U. unfold rMU. rewrite (U_atom_off E0 47 mu 262144 EaMU) by (clear - U0 U1 U2 Hroom; unfold kFreeArrayOffset, kUserMapSize in *; zlia).
change (U E0 (SLit 3758096385)) with 3758096385. rewrite (proj2 (Z.ltb_lt _ _)); [reflexivity|]. clear - Hroom. unfold kFreeArrayOffset, kUserMapSize in *. zlia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x6e0b8 R3_M5a WX0 HP.
assert (UADR : U E0 (SOff rADR 0) = U E0 (SAlu ALU_ADD (SOff 42 0) (SOff 47 0))).
{ pin_zev3. unfold rADR. rewrite EaADR, EaRB, EaMU. unfold w64. pose proof derived_rangesR as DR. pose proof high_factsR as (_ & _ & F3 & F4 & F5 & F6 & _).
clear - G6 G7 G10 U0 U1 U2 DR F3 F4 F5 F6. numconst.
rewrite (unsigned_lit_small adr), (unsigned_lit_small RBv), (unsigned_lit_small mu) by zlia.
rewrite (zcanon_id (adr + 0)), (zcanon_id (RBv + 0)), (zcanon_id (mu + 0)) by (unfold M64; zlia). rewrite zcanon_id by (unfold M64; zlia). zlia. }
r3_pin HR (11%bv : bv 5) (SOff rADR 0). { exact UADR. }
r3_pin HR (20%bv : bv 5) (SOff rADR 0). { exact UADR. }
r3_station HR R3_M5.
lazymatch type of HR with at_R3 ?Wx ?md ?X ?P ?ss ?W4 ?c4 =>
let cs := eval vm_compute in (match nth_error (ss_mem R3_NU) 0 with Some r => YP09.r_chunks r | None => [] end) in
eapply (at_R3_run_ecall Wx tfibtbl_rtC tfibtbl_rtC_ok 0x7ffffff0 md X P ss R3_NU W4 c4 HR);
[ vm_compute; reflexivity | reflexivity | exact WX0 | vm_compute; reflexivity | exact HP | exists cs; vm_compute; reflexivity ] end.
Qed.
End f.
End d.

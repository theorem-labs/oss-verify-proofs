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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhm AFka.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let m0 := mrestrict (w_H W) mem0.
Ltac clean := clear3; try clear SEEDJ; try clear Hpres0R; try clear HslotPres; try clear HfaPres; try clear Hnf; try clear Hmf; try clear Hmu; try clear Hcarved; try clear Hau_al;
try clear Hj64; try clear Hjna; try clear Hjnf; try clear Hjsm; try clear Hjm1; try clear Hjm2;
try clear Hj64v; try clear Hjnav; try clear Hjnfv; try clear Hjsmv; try clear Hjm1v; try clear Hjm2v.
Lemma cls_wfR : cls_ok c (reg S c) (cache S c) true (chunk_offs S c) (batch_offs S c).
Proof. clean. pose proof (wf_classes _ _ _ _ _ WF c HcR) as C0. unfold wf_class in C0. rewrite Hinited in C0. exact C0. Qed.
Lemma cls_wf0 : cls_ok c (reg S c) (cache S c) (st_cache_inited S) (chunk_offs S c) (batch_offs S c).
Proof. clean. try clear Hinited. exact (wf_classes _ _ _ _ _ WF c HcR). Qed.
Lemma reg_facts0 :
(0 <= nf /\ 4 * nf <= mf) /\ (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) /\
(0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) /\
runs_ok (rg_free (reg S c)).
Proof. clean. try clear Hinited.
pose proof cls_wf0 as CL. pose proof (class_ok c HcR) as (K1 & K2 & _).
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_mapped_al _ _ _ _ _ _ CL) as A2. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as A3.
pose proof (wr_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as F3. pose proof (wr_fa_len _ _ _ _ _ _ CL) as F4.
pose proof (wr_runs _ _ _ _ _ _ CL) as RU.
pose proof (fa_len_nonneg _ RU) as F0.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF HcR) as MB. unfold kUserMapSize, EV_MAX in MB.
rewrite <- Hnf_def in *. rewrite <- Hmf_def in *. rewrite <- Hau_def in *. rewrite <- Hmu_def in *.
assert (A16 : au mod 16 = 0).
{ apply Z.mod_divide in A3 as [q Hq]; [|zlia]. apply Z.mod_divide in K2 as [r Hr]; [|zlia]. apply Z.mod_divide; [zlia|]. exists (q * (r * 2)). zlia. }
unfold kFreeArrayOffset, kUserMapSize in *. repeat split; try assumption; zlia.
Qed.
Lemma reg_facts :
(0 <= nf /\ 4 * nf <= mf) /\ (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) /\
(0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) /\
pc_max (cache S c) = maxc /\ runs_ok (rg_free (reg S c)).
Proof. clean.
pose proof cls_wfR as CL. pose proof (proj1 (wr_cache _ _ _ _ _ _ CL)) as PM. rewrite Hmax. pose proof reg_facts0 as X. tauto.
Qed.
Lemma Hnf' : 0 <= nf /\ 4 * nf <= mf. Proof. clean. try clear Hinited. pose proof reg_facts0; tauto. Qed.
Lemma Hmf' : 0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0. Proof. clean. try clear Hinited. pose proof reg_facts0; tauto. Qed.
Lemma Hmu' : 0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0. Proof. clean. try clear Hinited. pose proof reg_facts0; tauto. Qed.
Lemma Hcarved' : mu - au < kUserMapSize + kMaxSize.
Proof. clean. try clear Hinited. pose proof (wr_carved _ _ _ _ _ _ cls_wf0) as X. rewrite <- Hmu_def, <- Hau_def in X. exact X. Qed.
Lemma Hau_al' : au mod csz = 0.
Proof. clean. try clear Hinited. pose proof (wr_alloc_al _ _ _ _ _ _ cls_wf0) as X. rewrite <- Hau_def, <- Hcsz in X. exact X. Qed.
Ltac clean2 := clean; try clear Hinited; pose proof Hnf' as Hnf; pose proof Hmf' as Hmf; pose proof Hmu' as Hmu; pose proof Hcarved' as Hcarved; pose proof Hau_al' as Hau_al.
Lemma vis_present : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent (w_H W) mem0 a.
Proof. clean. try clear Hinited.
intros e len a Hin Ha Hhi.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) _ Hin) | exact (proj1 (Forall_forall _ _) (am_areas B ly S rd0 HARm) _ Hin)]. }
destruct (range_vis_mbyte B ly (w_H W) mem0 e len (a - aeval B ly e) RV ltac:(zlia)) as [b Hb].
replace (aeval B ly e + (a - aeval B ly e)) with a in Hb by zlia. exact (mbyte_off_apresent (w_H W) mem0 a b Hhi Hb).
Qed.
Lemma thread_present : forall a, T <= a < T + kThreadObjSize -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof high_factsR as (F1 & F2 & _).
apply (vis_present (AT 0) kThreadObjSize).
- right. unfold aareas. do 3 (apply in_or_app; right). do 3 right. left. reflexivity.
- cbn [aeval]. unfold T in *. zlia.
- off_by ltac:(clear - Ha F1 F2; numconst; unfold T in *; zlia).
Qed.
Lemma rinfo_present : forall a, RGv <= a < RGv + 128 -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof derived_rangesR as DR.
apply (vis_present (ASp kRegionInfoOff) 4096).
- right. unfold aareas. do 3 (apply in_or_app; right). do 4 right. left. reflexivity.
- cbn [aeval]. unfold RGv, SB in *. clear - Ha HcR. numconst. zlia.
- clear - Ha DR. numconst. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *. zlia.
Qed.
Lemma HslotPres' : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Proof. clean2. intros a Ha. pose proof derived_rangesR as DR. apply thread_present. unfold DSTv in *. clear - Ha DR. numconst. zlia. Qed.
Lemma HfaPres' : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof Hmf as [[M0 M1] _].
apply (vis_present (ASp (region_off c + kFreeArrayOffset)) (rg_mapped_fa (reg S c))).
- right. unfold aareas. apply in_or_app; left. apply in_flat_map. exists c. split; [apply In_zseq; zlia|]. right; left; reflexivity.
- cbn [aeval]. rewrite <- Hmf_def. pose proof FAv_is as E. unfold fa_base in E. clear - Ha E. zlia.
- clear - Ha DR F1 F2 F3 F4 F5 F6 M0 M1. numconst. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *. zlia.
Qed.
Lemma word_of_present : forall a, (forall i, 0 <= i < 8 -> apresent (w_H W) mem0 (a + i)) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs m0 a 8 w.
Proof. clean. try clear Hinited.
intros a PR.
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte tfibsegs m0 (a + Z.of_nat k) = Some b).
{ intros k Hk. apply apresent_mbyte. apply PR. zlia. }
destruct (BY 0%nat ltac:(zlia)) as [b0 B0]. destruct (BY 1%nat ltac:(zlia)) as [b1 B1]. destruct (BY 2%nat ltac:(zlia)) as [b2 B2]. destruct (BY 3%nat ltac:(zlia)) as [b3 B3].
destruct (BY 4%nat ltac:(zlia)) as [b4 B4]. destruct (BY 5%nat ltac:(zlia)) as [b5 B5]. destruct (BY 6%nat ltac:(zlia)) as [b6 B6]. destruct (BY 7%nat ltac:(zlia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
split; [zlia|].
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YG0f.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YG0f.le_byte. rewrite Z.shiftr_div_pow2 by zlia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); zlia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); zlia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs m0 (a + Z.of_nat kk) = Some bk -> YG0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs m0 (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|zlia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 0)) with 1; zlia | change (2 ^ (8 * Z.of_nat 0)) with 1; zlia | zlia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 1)) with 256; zlia | change (2 ^ (8 * Z.of_nat 1)) with 256; zlia | zlia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia | change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia | zlia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia | zlia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia | zlia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia | zlia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia | zlia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia | zlia].
Qed.
Lemma val_mem_lo4 : forall m a w, 0 <= w < 2 ^ 64 -> val_mem tfibsegs m a 8 w -> val_mem tfibsegs m a 4 (w mod 2 ^ 32).
Proof. clean. try clear Hinited.
intros m a w Hw H k Hk. rewrite (H k ltac:(zlia)). do 2 f_equal. rewrite <- (le_byte_eq w). rewrite <- (le_byte_eq (w mod 2 ^ 32)).
rewrite <- (le_byte_split_lo (w mod 2 ^ 32) (w / 2 ^ 32) k); [| pose proof (Z.mod_pos_bound w (2 ^ 32)); zlia | split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; zlia] | exact Hk].
f_equal. pose proof (Z.div_mod w (2 ^ 32) ltac:(zlia)). zlia.
Qed.
Lemma junk_valuesR : exists j64' jna' jnf' jsm' jm1' jm2',
(0 <= j64' < 2 ^ 32 /\ val_mem tfibsegs m0 (RGv + 64) 4 j64') /\ (0 <= jna' < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 72) 8 jna') /\
(0 <= jnf' < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 80) 8 jnf') /\ (0 <= jsm' < 2 ^ 64 /\ val_mem tfibsegs m0 (T + 2792) 8 jsm') /\
(0 <= jm1' < 2 ^ 64 /\ val_mem tfibsegs m0 (T + 2872) 8 jm1') /\ (0 <= jm2' < 2 ^ 64 /\ val_mem tfibsegs m0 (T + 2880) 8 jm2').
Proof. clean. try clear Hinited.
destruct (word_of_present (RGv + 64)) as (w0 & R0 & V0); [intros i Hi; apply rinfo_present; zlia|].
destruct (word_of_present (RGv + 72)) as (w1 & R1 & V1); [intros i Hi; apply rinfo_present; zlia|].
destruct (word_of_present (RGv + 80)) as (w2 & R2 & V2); [intros i Hi; apply rinfo_present; zlia|].
destruct (word_of_present (T + 2792)) as (w3 & R3 & V3); [intros i Hi; apply thread_present; numconst; zlia|].
destruct (word_of_present (T + 2872)) as (w4 & R4 & V4); [intros i Hi; apply thread_present; numconst; zlia|].
destruct (word_of_present (T + 2880)) as (w5 & R5 & V5); [intros i Hi; apply thread_present; numconst; zlia|].
exists (w0 mod 2 ^ 32), w1, w2, w3, w4, w5.
pose proof (Z.mod_pos_bound w0 (2 ^ 32) ltac:(zlia)).
repeat split; try zlia; try assumption. apply val_mem_lo4; [exact R0 | exact V0].
Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. clean. try clear Hinited. intros e w e' E. exact (tfib_const_lookup_sym B TS ly S (w_H W) mem0 e w e' HARm E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. clean. try clear Hinited. intros a w x E. exact (tfib_const_lookup B TS ly S (w_H W) mem0 a w x HARm E). Qed.
Lemma cell_state : forall cc e (w : nat) x, In cc (acells B ly S) -> cc = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. clean. try clear Hinited.
intros cc e w x Hin ->. apply (cell_holds_val_mem B ly (w_H W) mem0 e w (ANum x)).
exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm) _ Hin).
Qed.
Lemma In_acells_cache : forall cc, In cc (cache_cells S c) -> In cc (acells B ly S).
Proof. clean. try clear Hinited.
intros cc Hc. unfold acells. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c.
split; [apply In_zseq; zlia | exact Hc].
Qed.
Lemma In_acells_region : forall cc, In cc (region_cells S c) -> In cc (acells B ly S).
Proof. clean. try clear Hinited.
intros cc Hc. unfold acells. apply in_or_app. left. apply in_flat_map. exists c. split; [apply In_zseq; zlia | exact Hc].
Qed.
Lemma cache_valsR : val_mem tfibsegs m0 Pr 4 0 /\ val_mem tfibsegs m0 (Pr + 4) 4 maxc /\ val_mem tfibsegs m0 (Pr + 8) 8 csz.
Proof. clean.
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c)) d) = Pr + d) by (intros d; cbn; unfold Pr; zlia).
assert (EP0 : aeval B ly (AT (t_cache + 80 * c)) = Pr) by (cbn; unfold Pr; zlia).
split; [|split].
- rewrite <- EP0. eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; left; reflexivity|].
rewrite Hchunks. reflexivity.
- rewrite <- (EP 4). eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; left; reflexivity|].
rewrite Hmax. reflexivity.
- rewrite <- (EP 8). eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; left; reflexivity|].
rewrite Hcsz. reflexivity.
Qed.
Lemma In_acells_cache_i : forall i cc, 1 <= i <= 31 -> In cc (cache_cells S i) -> In cc (acells B ly S).
Proof. clean. try clear Hinited.
intros i cc Hi Hc. unfold acells. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists i.
split; [apply In_zseq; zlia | exact Hc].
Qed.
Lemma cache_valsU : st_cache_inited S = false -> forall i, 1 <= i <= 31 ->
val_mem tfibsegs m0 (T + 208 + 80 * i) 4 0 /\ val_mem tfibsegs m0 (T + 212 + 80 * i) 4 0 /\ val_mem tfibsegs m0 (T + 216 + 80 * i) 8 0.
Proof. clean. try clear Hinited.
intros HU i Hi.
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * i)) d) = T + 208 + 80 * i + d) by (intros d; cbn; unfold T, t_cache; zlia).
assert (EP0 : aeval B ly (AT (t_cache + 80 * i)) = T + 208 + 80 * i) by (cbn; unfold T, t_cache; zlia).
split; [|split].
- rewrite <- EP0. eapply cell_state; [apply (In_acells_cache_i i); [exact Hi|]; unfold cache_cells; rewrite HU; left; reflexivity | reflexivity].
- replace (T + 212 + 80 * i) with (T + 208 + 80 * i + 4) by zlia. rewrite <- (EP 4).
eapply cell_state; [apply (In_acells_cache_i i); [exact Hi|]; unfold cache_cells; rewrite HU; right; left; reflexivity | reflexivity].
- replace (T + 216 + 80 * i) with (T + 208 + 80 * i + 8) by zlia. rewrite <- (EP 8).
eapply cell_state; [apply (In_acells_cache_i i); [exact Hi|]; unfold cache_cells; rewrite HU; right; right; left; reflexivity | reflexivity].
Qed.
Lemma region_valsR :
val_mem tfibsegs m0 RGv 8 0 /\ val_mem tfibsegs m0 (RGv + 8) 8 0 /\ val_mem tfibsegs m0 (RGv + 16) 8 nf /\ val_mem tfibsegs m0 (RGv + 24) 8 mf /\
val_mem tfibsegs m0 (RGv + 32) 8 au /\ val_mem tfibsegs m0 (RGv + 40) 8 0 /\ val_mem tfibsegs m0 (RGv + 48) 8 mu /\ val_mem tfibsegs m0 (RGv + 56) 8 0 /\
val_mem tfibsegs m0 (RGv + 68) 1 0.
Proof. clean. try clear Hinited.
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = RGv + d) by (intros d; cbn; unfold RGv, SB; zlia).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = RGv) by (cbn; unfold RGv, SB; zlia).
repeat split.
- rewrite <- ER0. eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; left; reflexivity | reflexivity].
- rewrite <- (ER 8). eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 1 right; left; reflexivity | reflexivity].
- rewrite <- (ER 16), Hnf_def. eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 2 right; left; reflexivity | reflexivity].
- rewrite <- (ER 24), Hmf_def. eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 3 right; left; reflexivity | reflexivity].
- rewrite <- (ER 32), Hau_def. eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 4 right; left; reflexivity | reflexivity].
- rewrite <- (ER 40). eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 5 right; left; reflexivity | reflexivity].
- rewrite <- (ER 48), Hmu_def. eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 6 right; left; reflexivity | reflexivity].
- rewrite <- (ER 56). eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 7 right; left; reflexivity | reflexivity].
- rewrite <- (ER 68). eapply cell_state; [apply In_acells_region; unfold region_cells; cbv zeta; do 8 right; left; reflexivity | reflexivity].
Qed.
Lemma chunk_lit : forall a (nn : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal nn (SLit x))).
Proof. clean. try clear Hinited. intros a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | rewrite Z.add_0_l; exact H]. Qed.
Lemma chunk_lit_at : forall base a (nn : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SLit x))).
Proof. clean. try clear Hinited. intros base a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | exact H]. Qed.
Lemma chunk_atom : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SOff k d))).
Proof. clean. try clear Hinited.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| exact Hx | exact Hnn | exact H].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; zlia | cbn; zlia] |]); apply Forall_nil.
Lemma REG0R3_ok_but35 : forall hd, region_ok tfibsegs E0 m0 hd -> Forall (region_ok tfibsegs E0 m0) (replAt 35 hd REG0R3).
Proof. clear3. try clear Hinited. intros hd Hhd.
pose proof (tfib_const_lookup B TS ly S (w_H W) mem0 0x137c28 8 0x1010101 HARm ltac:(vm_compute; reflexivity)) as L8.
pose proof (tfib_const_lookup B TS ly S (w_H W) mem0 0x9dfd8 8 1 HARm ltac:(vm_compute; reflexivity)) as L9.
pose proof (tfib_const_lookup B TS ly S (w_H W) mem0 0x9dfe0 8 0x137b1c HARm ltac:(vm_compute; reflexivity)) as L10.
pose proof (tfib_const_lookup B TS ly S (w_H W) mem0 0x137b1c 4 0 HARm ltac:(vm_compute; reflexivity)) as L11.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
pose proof region_valsR as (RV0 & RV1 & RV2 & RV3 & RV4 & RV5 & RV6 & RV7 & RV8).
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hnf as [N0 N1]. pose proof Hmf as [[M0 M1] M2]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7, K4, M0, M1, U1, U2.
unfold replAt, REG0R3, REG0R, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE. cbn [firstn skipn app map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold rSB, rSHB, rC, rT, rTOP, rCL, rP, rMAX, rN, rCSZ, rRG, rRB, rFA, rNF, rMF, rAU, rMU, rJ64, rJNA, rJNF, rJSM, rJM1, rJM2.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- 1024)); [rewrite E2; reflexivity | zlia | zlia |].
intros a Ha. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; zlia) | apply Hpres0R; unfold RSTACK; zlia]. }
do 5 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 34%nat 0 SB); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | | unfold SB; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 666040 with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TS); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; unfold SB; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 34%nat 137438953472 (SB + 137438953472)); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | | unfold SB; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 666056 with (aeval B ly (AInst o_rinfo)) by (cbn; rewrite (ts_inst B TS); reflexivity).
replace (SB + 137438953472) with (aeval B ly (ASp kRegionInfoOff)) by (cbn; unfold SB, kRegionInfoOff; zlia). apply cell_sym. vm_compute. reflexivity. }
do 15 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 48%nat 0 SHBv); [reflexivity | unfold SHBv; zlia | | unfold SHBv; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 4 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| cbn; zlia | cbn; zlia]. pose proof (cell_lit 0x5d8fa0 8 0 ltac:(vm_compute; reflexivity)) as H8.
intros k Hk. rewrite (H8 k ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
apply Forall_cons; [lit_region|].
apply Forall_cons. {   reg_intro. unfold TFIB_TP. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; zlia | cbn; zlia].
replace (6131600 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. unfold TFIB_TSD. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 6267704 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; unfold T; zlia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply thread_present. unfold kThreadObjSize, T in *. zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 52%nat 0 jsm); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hjsmv | cbn; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply thread_present. unfold kThreadObjSize, T in *. zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 53%nat 0 jm1); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hjm1v | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 54%nat 0 jm2); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hjm2v | cbn; zlia | cbn; zlia]. }
apply Forall_cons; [exact Hhd|].
apply Forall_cons. {   reg_intro. rewrite EaRG. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply rinfo_present. zlia. }
repeat (apply Forall_cons; [|try apply Forall_nil]).
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. rewrite Z.add_0_r. exact RV0.
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. exact RV1.
- apply (chunk_atom _ _ 8 44%nat 0 nf); [rewrite Z.sub_0_r; exact EaNF | zlia | exact RV2 | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 45%nat 0 mf); [rewrite Z.sub_0_r; exact EaMF | zlia | exact RV3 | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 46%nat 0 au); [rewrite Z.sub_0_r; exact EaAU | zlia | exact RV4 | cbn; zlia | cbn; zlia].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. exact RV5.
- apply (chunk_atom _ _ 8 47%nat 0 mu); [rewrite Z.sub_0_r; exact EaMU | zlia | exact RV6 | cbn; zlia | cbn; zlia].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. exact RV7.
- apply (chunk_atom _ _ 4 49%nat 0 j64); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hj64v | cbn; zlia | cbn; zlia].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. exact RV8.
- apply (chunk_atom _ _ 8 50%nat 0 jna); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hjnav | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 51%nat 0 jnf); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hjnfv | cbn; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L8]. }
apply Forall_cons. {   reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L9]. }
apply Forall_cons. {   reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L10]. }
apply Forall_cons; [|apply Forall_nil]. {   reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L11]. }
Qed.
Lemma REG0R3_ok : Forall (region_ok tfibsegs E0 m0) REG0R3.
Proof. clear3.
pose proof derived_rangesR as DR. pose proof high_factsR as (hf1 & hf2 & _). pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof cache_valsR as (CV1 & CV2 & CV3).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, kMaxSize in hf1, hf2, DR, K4.
change REG0R3 with (replAt 35 (YP09.mkRegion (Some rP) 0 16 0 16 [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]) REG0R3).
apply REG0R3_ok_but35. reg_intro. unfold rP. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply thread_present. unfold kThreadObjSize, T in *. zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. rewrite Z.add_0_r. exact CV1.
- apply (chunk_atom _ _ 4 38%nat 0 maxc); [rewrite Z.sub_0_r; exact EaMAX | zlia | exact CV2 | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 40%nat 0 csz); [rewrite Z.sub_0_r; exact EaCSZ | zlia | exact CV3 | cbn; zlia | cbn; zlia].
Qed.
Lemma REG0U3_ok : st_cache_inited S = false -> Forall (region_ok tfibsegs E0 m0) (replAt 35 headc0 REG0R3).
Proof. clear3. try clear Hinited. intros HU.
pose proof derived_rangesR as DR. pose proof high_factsR as (hf1 & hf2 & _). pose proof (cache_valsU HU c HcR) as (CV1 & CV2 & CV3).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, kMaxSize in hf1, hf2, DR.
apply REG0R3_ok_but35. unfold headc0. reg_intro. unfold rP. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + 208 + 80 * c) by (unfold Pr, T, t_cache; zlia) end. exact CV1.
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + 212 + 80 * c) by (unfold Pr, T, t_cache; zlia) end. exact CV2.
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + 216 + 80 * c) by (unfold Pr, T, t_cache; zlia) end. exact CV3.
Qed.
Lemma PAIRSR3_ok : pairwise_disjoint E0 REG0R3.
Proof. clear3.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
apply pairwise_disjoint_of_extents. unfold REG0R3, REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE. rewrite map_app. cbn [map app].
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold rSB, rSHB, rC, rT, rTOP, rP, rRG.
rewrite E2, EaT, EaC, EaP, EaRG. unfold w64. rewrite !unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT.
pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC. unfold zdisjoint in CT, PT, PC. cbn [fst snd] in CT, PT, PC.
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR SI1 SI2 SI3 SI4 SI5 CT PT PC HcR.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_TP, TFIB_TSD, RSTACK, kThreadObjSize, kPrimResvSize, kHighMemBeg, kHighMemEnd in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold t_cache, kRegionInfoOff in *.
repeat split; zlia.
Qed.
Lemma SPAN3_disj : all_disjoint E0 (YP09.mkRegion (Some rT) 292 2704 0 0 []) (dropAt 35 REG0R3).
Proof. clear3.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7.
apply all_disjoint_of_extents. unfold dropAt, REG0R3, REG0R, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE. cbn [firstn skipn app map].
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold rSB, rSHB, rC, rT, rTOP, rP, rRG.
rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG. unfold w64. rewrite !unsigned_lit_small by zlia.
pose proof stack_ivsR as (SI1 & SI2 & SI3 & SI4 & SI5).
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT.
pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC. unfold zdisjoint in CT, PT, PC. cbn [fst snd] in CT, PT, PC.
clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR SI1 SI2 SI3 SI4 SI5 CT PT PC HcR.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_TP, TFIB_TSD, RSTACK, kThreadObjSize, kPrimResvSize, kHighMemBeg, kHighMemEnd in *. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold Pr, RGv in *. unfold t_cache, kRegionInfoOff in *.
repeat split; zlia.
Qed.
Lemma FACTSR3_ok : atoms_ok E0 (f_atoms FR3).
Proof.
pose proof facts3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G28a & G28b & G28c & G28d & G29 & G30 & G31 & G32 & G33).
clear3.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hnf as [N0 N1]. pose proof Hmf as [[M0 M1] M2]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7, K4, M0, M1, M2, U1, U2, U3.
pose proof (lo_space_al ly LY) as SAL. pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL. unfold page_aligned in TAL.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; zlia. }
cbn [FR3 FR f_atoms atoms_ok app]. unfold rSB, rSHB, rC, rT, rTOP, rCL, rP, rMAX, rN, rCSZ, rRG, rRB, rFA, rNF, rMF, rAU, rMU, rJ64, rJNA, rJNF, rJSM, rJM1, rJM2, rNEED, rTOT, rADR, rSHA, rMU2, rNCe, rNCg, rNFe, rNFg, rFADR, rSHF, rMF2, rAUe, rAUg.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL.
split. { apply (AF 2%nat sp0); [exact E2'| | | |].
all: pose proof (u64_range (getr regs0 2)) as U; clear - U S1 S3 S4 T4 T7; unfold RSTACK in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact S4]. }
split. { apply (AF 32%nat T); [exact EaT| | | |]. all: clear - hf1 hf2 TAL; first [zlia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |]. all: clear - hf7 hf8 CAL; first [zlia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |]. all: unfold SB; clear - hf3 hf4 hf5 hf6 SAL; first [zlia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |]. all: clear - T1 T2 T3 T4 T7; first [zlia | exact T3]. }
split. { apply (AF 36%nat c); [exact EaCL| | | |]. all: clear - HcR; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 37%nat Pr); [exact EaP| | | |]. all: clear - DR hf1 hf2; first [zlia | replace (2 ^ 4) with 16 by reflexivity; tauto]. }
split. { apply (AF 38%nat maxc); [exact EaMAX| | | |]. all: clear - K1 K2; first [zlia | replace (2 ^ 1) with 2 by reflexivity; exact K2]. }
split. { apply (AF 39%nat n); [exact EaN| | | |]. all: clear - K3; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 40%nat csz); [exact EaCSZ| | | |]. all: clear - K4 K5; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact K5]. }
split. { apply (AF 41%nat RGv); [exact EaRG| | | |]. all: clear - DR; first [zlia | replace (2 ^ 7) with 128 by reflexivity; tauto]. }
split. { apply (AF 42%nat RBv); [exact EaRB| | | |]. all: clear - DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 16) with 65536 by reflexivity; tauto]. }
split. { apply (AF 43%nat FAv); [exact EaFA| | | |]. all: clear - DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 12) with 4096 by reflexivity; tauto]. }
split. { apply (AF 44%nat nf); [exact EaNF| | | |]. all: clear - N0 N1 M0 M1; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 45%nat mf); [exact EaMF| | | |]. all: clear - M0 M1 M2; first [zlia | replace (2 ^ 18) with 262144 by reflexivity; exact M2]. }
split. { apply (AF 46%nat au); [exact EaAU| | | |]. all: clear - U0 U1 U2 U4; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact U4]. }
split. { apply (AF 47%nat mu); [exact EaMU| | | |]. all: clear - U0 U1 U2 U3; first [zlia | replace (2 ^ 18) with 262144 by reflexivity; exact U3]. }
split. { apply (AF 48%nat SHBv); [exact EaSHB| | | |]. all: clear; unfold SHBv; first [zlia | reflexivity]. }
split. { apply (AF 49%nat j64); [reflexivity| | | |]. all: clear - Hj64; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 50%nat jna); [reflexivity| | | |]. all: clear - Hjna; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 51%nat jnf); [reflexivity| | | |]. all: clear - Hjnf; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 52%nat jsm); [reflexivity| | | |]. all: clear - Hjsm; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 53%nat jm1); [reflexivity| | | |]. all: clear - Hjm1; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 54%nat jm2); [reflexivity| | | |]. all: clear - Hjm2; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
assert (M1r : forall x, x mod 2 ^ 0 = 0) by (intros x; replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r).
pose proof (Z.mod_pos_bound adr 8 ltac:(zlia)) as MA8. pose proof (Z.mod_pos_bound fadr 8 ltac:(zlia)) as MF8.
assert (TOT16 : tot mod 2 ^ 4 = 0).
{ replace (2 ^ 4) with 16 by reflexivity. rewrite G5. apply Z.mod_divide in U4 as [qa Hqa]; [|zlia]. pose proof K5 as K5'. apply Z.mod_divide in K5' as [qc Hqc]; [|zlia].
rewrite Hqa, Hqc. apply Z.mod_divide; [zlia|]. exists (qa + need * qc). zlia. }
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kUserMapSize, kFreeArrayMapSize, kMaxSize, kFreeArrayOffset, kFreeArrayMax in *.
split. { apply (AF 55%nat need); [exact EaNEED| | | |]. all: clear - G1 M1r; first [zlia | apply M1r]. }
split. { apply (AF 56%nat tot); [exact EaTOT| | | |]. all: clear - G1 G3 G4 G5 U0 U1 U2 TOT16; first [zlia | exact TOT16]. }
split. { apply (AF 57%nat adr); [exact EaADR| | | |]. all: clear - G6 G7 G8 DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 16) with 65536 by reflexivity; exact G8]. }
split. { apply (AF 58%nat sha); [exact EaSHA| | | |]. all: clear - G11 G12 G13 G14; first [zlia | replace (2 ^ 12) with 4096 by reflexivity; exact G12]. }
split. { apply (AF 59%nat mu2); [exact EaMU2| | | |]. all: clear - G15 U0 U1 U2 U3 M1r; try zlia.
replace (2 ^ 18) with 262144 by reflexivity. rewrite G15. apply Z.mod_divide in U3 as [q Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q + 1). zlia. }
split. { apply (AF 60%nat nce); [exact EaNCe| | | |]. all: clear - G16 G20 M1r; first [zlia | apply M1r]. }
split. { apply (AF 61%nat ncg); [exact EaNCg| | | |]. all: clear - G18 G21 M1r; first [zlia | apply M1r]. }
split. { apply (AF 62%nat nfe); [exact EaNFe| | | |]. all: clear - G16 G20 G22 N0 N1 M0 M1 M1r; first [zlia | apply M1r]. }
split. { apply (AF 63%nat nfg); [exact EaNFg| | | |]. all: clear - G18 G21 G23 N0 N1 M0 M1 M1r; first [zlia | apply M1r]. }
split. { apply (AF 64%nat fadr); [exact EaFADR| | | |]. all: clear - G25 G28c G28d DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 16) with 65536 by reflexivity; exact G25]. }
split. { apply (AF 65%nat shf); [exact EaSHF| | | |]. all: clear - G27 G28 G28a G28b; first [zlia | replace (2 ^ 12) with 4096 by reflexivity; exact G28]. }
split. { apply (AF 66%nat mf2); [exact EaMF2| | | |]. all: clear - G29 M0 M1 M2 M1r; try zlia.
replace (2 ^ 18) with 262144 by reflexivity. rewrite G29. apply Z.mod_divide in M2 as [q Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q + 1). zlia. }
split. { apply (AF 67%nat aue); [exact EaAUe| | | |]. all: clear - G30 G16 G17 U0 U1 U2 G32 K4; first [nia | replace (2 ^ 4) with 16 by reflexivity; exact G32]. }
split; [|exact I]. { apply (AF 68%nat aug); [exact EaAUg| | | |]. all: clear - G31 G18 G19 G15 U0 U1 U2 G33 K4; first [nia | replace (2 ^ 4) with 16 by reflexivity; exact G33]. }
Qed.
Lemma SEEDR3_ok : st_ok tfibsegs E0 SS0R3 (restrict (w_H W) (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold SS0R3, REGS0R, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 XWR) rCL) with (ew E0 36); rewrite EaCL, Ha3; unfold w64; rewrite unsigned_lit_small by zlia; f_equal; zlia].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact Ha2].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 XWR) rP) with (ew E0 37); rewrite EaP, Ha1; unfold w64; rewrite unsigned_lit_small by (pose proof derived_rangesR; pose proof high_factsR; numconst; unfold T; zlia); f_equal; zlia].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 XWR) rT) with (ew E0 32); rewrite EaT, Ha0; unfold w64; rewrite unsigned_lit_small by (pose proof high_factsR; numconst; unfold T; zlia); f_equal; unfold T; zlia].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0R3_ok.
- exact PAIRSR3_ok.
- split; [exact FACTSR3_ok | split; exact I].
Qed.
Lemma PAIRSU3_ok : pairwise_disjoint E0 REG0U3.
Proof. apply (pairwise_disjoint_ext3 E0 REG0R3); [vm_compute; reflexivity | exact PAIRSR3_ok]. Qed.
Lemma SEEDU3_ok : st_cache_inited S = false -> st_ok tfibsegs E0 SS0U3 (restrict (w_H W) (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs))).
Proof. try clear Hinited. intros HU.
rewrite restrict_mkst_fx. unfold SS0U3, REGS0R, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 XWR) rCL) with (ew E0 36); rewrite EaCL, Ha3; unfold w64; rewrite unsigned_lit_small by zlia; f_equal; zlia].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact Ha2].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 XWR) rP) with (ew E0 37); rewrite EaP, Ha1; unfold w64; rewrite unsigned_lit_small by (pose proof derived_rangesR; pose proof high_factsR; numconst; unfold T; zlia); f_equal; zlia].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 XWR) rT) with (ew E0 32); rewrite EaT, Ha0; unfold w64; rewrite unsigned_lit_small by (pose proof high_factsR; numconst; unfold T; zlia); f_equal; unfold T; zlia].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact (REG0U3_ok HU).
- exact PAIRSU3_ok.
- split; [exact FACTSR3_ok | split; exact I].
Qed.
End g.
End f.

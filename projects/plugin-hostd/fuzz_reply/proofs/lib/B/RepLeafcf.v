(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepLeafcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 02ac722d5bcf) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 5 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 5 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, RepF1Top / RepF1Leaf): the LEAF of PopulateFreeArray's class-full report arm.
   The section header is YFkbcf.v:9-386 VERBATIM (so YFkmcf's own section variables line up by name).
   [leaf_G_fail] instantiates YFkmcf.LEAF_G at the degenerate "populate returned false" parameters
   (NC = 0, TOPS = [], MU = mu, MF = mf, FL = fr, HO = hol, uq = fq = false, EXV = jex), where
   SG = S (SG_is_S), so the result is acall_post_cf over the window RSTACK with an empty frame exception;
   LEAF_G's VISLOC premise is RepVisLcf.visloc_cf.  Field round 2: LEAF_G also takes the two machine cells at the
   result (HCX / HCE); leaf_G_fail proves them from the entry relation's cells (YG0ncf.ARcf_exh_cell / ARcf_errb_cells):
   [RIAP] / [OBJAP] place the other classes' bytes and the errbuf object outside the windows, and the class's byte is
   the run's exv, the model's flag (RepKcf.exh_cell_same); it returns them with its post.
   [leaf_core_fail] weakens that post to the layer's refill_leaf_core_cf (YGcfInstRefill.v) at the entry state:
   the window RSTACK widens to REP_W c = REP_STACK, the five arm windows are owned ([win_owned]) and lie below the
   stack ([STKAP]), and memnorm is kept on the windows ([win_mn]).
   Every address side condition is a separate lemma proved in a cleared context (no numconst over the big context).
   [arm1_cf] closes the class-full case whose byte is already set.  The report arm's machine pieces built on these
   lemmas (segA, arcf_at_call, reseed1, segB) are in RepArm2cf.v.
   rule 24: proves no function (kind: segment lemma of PopulateFreeArray's walk). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0n AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import MnRefillLocreply MemnormLoc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB19 YF0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFl1 YFhy YFis YFkpcf YFk6cf YFk5cf YFhz YFk8cf YFk7cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFk4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFk3 YB1q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFhmcf YFkacf YFkkcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0dcf YG0qcf YG0lawscf YG06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFkbcf YFkjcf YFkmcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfXsMapped YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RepArmD RepArmcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT RepVisLcf RepModelcf RepKcf.
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
Section f.
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
Local Abbreviation cls_wfR := (@YFkkcf.cls_wfR _ _ _ W ly mem0 c HcR B S Hph HARm Hinited).
Local Abbreviation cls_wf0 := (@YFkkcf.cls_wf0 _ _ _ W ly mem0 c HcR B S Hph HARm).
Local Abbreviation reg_facts0 := (@YFkkcf.reg_facts0 _ _ _ W ly regs0 mem0 c maxc nf mf au mu HcR B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation reg_facts := (@YFkkcf.reg_facts _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hmax Hjex Hsp B S Hph HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hnf' := (@YFkkcf.Hnf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmf' := (@YFkkcf.Hmf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hmu' := (@YFkkcf.Hmu' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation Hcarved' := (@YFkkcf.Hcarved' _ _ _ W ly mem0 c au mu HcR B S Hph HARm Hau_def Hmu_def).
Local Abbreviation Hau_al' := (@YFkkcf.Hau_al' _ _ _ W ly mem0 c au csz HcR Hcsz B S Hph HARm Hau_def).
Local Abbreviation vis_present := (@YFkkcf.vis_present _ _ _ W ly regs0 mem0 maxc B S Hph HARm).
Local Abbreviation thread_present := (@YFkkcf.thread_present _ _ _ W ly regs0 mem0 c maxc nf mf au mu csz jex IMG LY HcR Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation rinfo_present := (@YFkkcf.rinfo_present _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HslotPres' := (@YFkkcf.HslotPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation HfaPres' := (@YFkkcf.HfaPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation word_of_present := (@YFkkcf.word_of_present W ly regs0 mem0 maxc).
Local Abbreviation val_mem_lo4 := (@YFkkcf.val_mem_lo4 ly regs0 maxc).
Local Abbreviation junk_valuesR := (@YFkkcf.junk_valuesR _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex IMG LY HcR Hmax Hn Hcsz Hjex Hsp B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation cell_sym := (@YFkkcf.cell_sym _ _ _ W ly mem0 B S TS Hph HARm).
Local Abbreviation cell_lit := (@YFkkcf.cell_lit _ _ _ W ly mem0 B S TS Hph HARm).
Local Abbreviation cell_state := (@YFkkcf.cell_state _ _ _ W ly mem0 B S Hph HARm).
Local Abbreviation In_acells_cache := (@YFkkcf.In_acells_cache ly regs0 c maxc HcR B S).
Local Abbreviation In_acells_region := (@YFkkcf.In_acells_region ly regs0 c maxc HcR B S).
Local Abbreviation cache_valsR := (@YFkkcf.cache_valsR _ _ _ W ly regs0 mem0 c maxc csz HcR Hmax Hcsz B S Hph HARm Hinited Hchunks).
Local Abbreviation In_acells_cache_i := (@YFkkcf.In_acells_cache_i ly regs0 maxc B S).
Local Abbreviation cache_valsU := (@YFkkcf.cache_valsU _ _ _ W ly regs0 mem0 maxc B S Hph HARm).
Local Abbreviation region_valsR := (@YFkkcf.region_valsR _ _ _ W ly regs0 mem0 c maxc nf mf au mu HcR B S Hph HARm Hnf_def Hmf_def Hau_def Hmu_def).
Local Abbreviation chunk_lit := (@YFkkcf.chunk_lit W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_lit_at := (@YFkkcf.chunk_lit_at W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation chunk_atom := (@YFkkcf.chunk_atom W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation REG0R3_ok_but35 := (@YFkkcf.REG0R3_ok_but35 _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation REG0R3_ok := (@YFkkcf.REG0R3_ok _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation REG0U3_ok := (@YFkkcf.REG0U3_ok _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation PAIRSR3_ok := (@YFkkcf.PAIRSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SPAN3_disj := (@YFkkcf.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation FACTSR3_ok := (@YFkkcf.FACTSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug).
Local Abbreviation SEEDR3_ok := (@YFkkcf.SEEDR3_ok _ _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
Local Abbreviation PAIRSU3_ok := (@YFkkcf.PAIRSU3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEEDU3_ok := (@YFkkcf.SEEDU3_ok _ _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hph HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv).
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

(* ================================================================================================================ *)
Local Abbreviation PT := YFkbcf.PT.
Local Abbreviation fr := (@YFkjcf.fr c S).
Local Abbreviation hol := (@YFkjcf.hol c S).
Local Abbreviation SGf := (@YFkmcf.SG c maxc au csz S 0 mu mf [] fr hol).

Lemma zrange_dec : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. clear. intros lo hi a. destruct (Z_le_dec lo a) as [L|L]; [destruct (Z_lt_dec a hi) as [H|H]|].
- left. split; assumption.
- right. intros [_ C]. exact (H C).
- right. intros [C _]. exact (L C). Qed.

Lemma WF_S : Wf_cf (as_universe B) S.
Proof. exact (amc_wf B ly S Hph (aview tfibsegs (w_H W) mem0) HARm). Qed.

Lemma len_regions_S : (Z.to_nat c < length (st_regions S))%nat.
Proof. pose proof (wfc_len_regions _ _ _ _ _ WF_S) as L. rewrite L. clear - HcR. zlia. Qed.

Lemma len_cache_S : (Z.to_nat c < length (st_cache S))%nat.
Proof. pose proof (wfc_len_cache _ _ _ _ _ WF_S) as L. rewrite L. clear - HcR. zlia. Qed.

Lemma cache_eta : cache S c = mkPC maxc [].
Proof.
pose proof (wfc_classes _ _ _ _ _ WF_S c HcR) as C. unfold wf_class_cf in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as HC. rewrite Hinited in HC. destruct HC as [HM _].
destruct (cache S c) as [pm pc] eqn:E. cbn in HM, Hchunks. rewrite Hmax. rewrite <- HM.
rewrite <- Hchunks. reflexivity.
Qed.

Lemma reg_eta : mkRegion mu au mf fr hol = reg S c.
Proof.
unfold YFkjcf.fr, YFkjcf.hol. rewrite Hmu_def, Hau_def, Hmf_def.
destruct (reg S c) as [a1 a2 a3 a4 a5]. reflexivity.
Qed.

Lemma SG_is_S : SGf = S.
Proof.
unfold YFkmcf.SG, YFkmcf.rG, YFkmcf.AU. cbn [rev]. rewrite Z.mul_0_l, Z.add_0_r.
rewrite reg_eta, (upd_reg_same c S ltac:(clear - HcR; zlia) len_regions_S).
rewrite <- cache_eta. exact (upd_pc_same c S ltac:(clear - HcR; zlia) len_cache_S).
Qed.

Lemma mu_ne_mu2 : mu <> mu2.
Proof. rewrite Hmu2. unfold kUserMapSize. clear. zlia. Qed.
Lemma mf_ne_mf2 : mf <> mf2.
Proof. rewrite Hmf2. unfold kFreeArrayMapSize. clear. zlia. Qed.

(* ================================================================================================================ *)
(* The address facts the leaf and its weakening use, each in a cleared context.                                      *)
(* The five arm windows lie below the refill's stack (ASAN_CEIL <= ly_stk_lo, YG0f.v:335). *)Lemma STKAP : forall a, ASAN_CEIL <= a ->
  ~ (Pr <= a < Pr + 16) /\ ~ (DSTv <= a < DSTv + 64) /\ ~ (RGv <= a < RGv + 128) /\
  ~ (T + 2768 <= a < T + 2800) /\ ~ (T + 2872 <= a < T + 2888).
Proof.
intros a Ha. pose proof derived_rangesR as DR. pose proof high_factsR as HF.
destruct DR as (D1 & D2 & _ & _ & _ & D6 & _). destruct HF as (_ & HF2 & _).
unfold T, YFk5cf.DSTv. clear - Ha D1 D2 D6 HF2. unfold kThreadObjSize in HF2.
repeat split; lia.
Qed.

(* Another class's exhausted byte RegionInfo(c') + 68 is outside the six windows. *)
Lemma RIAP : forall c', 1 <= c' <= 31 -> c' <> c -> forall a, a = ly_space ly + kRegionInfoOff + 128 * c' + 68 ->
  0 <= a < 2 ^ 64 /\ ~ (sp0 - RSTACK <= a < sp0) /\
  ~ (Pr <= a < Pr + 16) /\ ~ (DSTv <= a < DSTv + 64) /\ ~ (RGv <= a < RGv + 128) /\
  ~ (T + 2768 <= a < T + 2800) /\ ~ (T + 2872 <= a < T + 2888).
Proof.
intros c' Hc' Hne a Ha. pose proof (lo_space_in ly LY) as [SI1 SI2]. pose proof (lo_stk_ceil ly LY) as SC.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
pose proof Hsp as (SP1 & _). pose proof derived_rangesR as DR. pose proof high_factsR as HF.
destruct DR as (D1 & D2 & _ & D4 & _ & D6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D18 & _).
destruct HF as (_ & HF2 & HF3 & _). pose proof (@ASAN_CEIL_range rc) as [CR1 _].
unfold T, YFk5cf.DSTv, YFk5cf.RGv. unfold YFk5cf.Pr in D2, D4 |- *.
clear - CR1 Ha Hc' Hne SI1 SI2 SC PT SP1 D2 D4 D18 HF2 HF3 HcR.
unfold kRegionInfoOff, kSpaceSize, kPrimResvSize, kThreadObjSize, RSTACK, t_cache, kHighMemBeg in *.
subst a. repeat split; lia.
Qed.

(* The errbuf object (cgif's error_message_buffer, 0xa5ae8, 56 bytes) is an image address, outside the six windows. *)
Lemma OBJAP : forall a, 0xa5ea8 <= a < 0xa5ea8 + 56 ->
  0 <= a < 2 ^ 64 /\ ~ (sp0 - RSTACK <= a < sp0) /\
  ~ (Pr <= a < Pr + 16) /\ ~ (DSTv <= a < DSTv + 64) /\ ~ (RGv <= a < RGv + 128) /\
  ~ (T + 2768 <= a < T + 2800) /\ ~ (T + 2872 <= a < T + 2888).
Proof.
intros a Ha. pose proof (lo_stk_ceil ly LY) as SC. pose proof (@ASAN_CEIL_range rc) as [CR1 _].
pose proof Hsp as (SP1 & _). pose proof derived_rangesR as DR. pose proof high_factsR as HF.
destruct DR as (D1 & D2 & _ & D4 & D5 & D6 & _).
destruct HF as (HF1 & HF2 & _). unfold zone3, zone3cases in HF1.
unfold T, YFk5cf.DSTv. unfold YFk5cf.Pr in D2, D4 |- *.
clear - CR1 Ha SC SP1 D2 D4 D5 D6 HF1 HF2.
unfold kThreadObjSize, RSTACK, t_cache, kHighMemBeg, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in *.
repeat split; lia.
Qed.

Lemma le1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof. intros v Hv. unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite Z.mul_1_r, Z.mul_0_r, Z.shiftr_0_r.
rewrite (Z.mod_small v (2 ^ 8)) by lia. apply Z.mod_small. lia. Qed.

(* The seed's junk atom jex is the class's exhausted byte, which exh_cell_cf ties to the model. *)
Lemma jex_of_cell : YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) -> cf_exh_off = 68 ->
  jex = (if YG00cf.exh_mem_cf S c then 1 else 0).
Proof.
intros [HE _] HO. specialize (HE c HcR). unfold cell_holds in HE. cbn [c_at c_w c_val z1 c1] in HE.
specialize (HE 0%nat ltac:(lia)). pose proof (Hjexv 0%nat ltac:(lia)) as V.
cbn [Z.of_nat] in HE, V. rewrite Z.add_0_r in HE, V.
assert (EA : aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) = RGv + 68)
  by (cbn [aeval aoff]; rewrite HO; unfold YFk5cf.RGv; lia).

rewrite EA in HE. unfold aview in HE. rewrite V in HE. cbn [option_map] in HE. injection HE as HE.
cbn [aeval] in HE. pose proof Hjex as J.
rewrite Z_to_bv_unsigned, bv_wrap_small in HE by (rewrite le1 by exact J; change (bv_modulus 8) with 256; lia).
change le_byte with YO0f.le_byte in HE. rewrite (le1 jex J) in HE.
destruct (YG00cf.exh_mem_cf S c); rewrite le1 in HE by lia; exact HE.
Qed.

(* YFkmcf.LEAF_G at the populate-false parameters.  Everything the leaf needs beyond the machine run. *)
(* The image-junk shape RepVisLcf.visloc_cf needs, from TfibSyms (as c5's callers do, YFkn.v:1015-1017). *)
Lemma JK_ts : forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd.
Proof.
intros r Hr. destruct (ts_junk B TS ly r Hr) as (z & E & Z1 & Z2). exists z. split; [exact E|].
unfold kImgEnd. clear - Z1 Z2. zlia.
Qed.

Lemma leaf_G_fail : YGcfXs.xs_mapped_cf ly S md0 -> cf_exh_off = 68 -> cf_errbuf_obj = 0xa5ea8 -> forall exv W' c',
  exv = (if YG00cf.exh_mem_cf S c then 1 else 0) ->
  at_RET3 W 0 md0 WINR0 (fun m => PT m /\ P_cells W 0 nf mf au mu exv m) W' c' ->
  exists regs1 mem1 md1, c' = cfg_at tfibsegs (raZ regs0) regs1 mem1 md1 /\
    acall_post_cf tfibsegs B RSTACK ly S Hph W regs0 mem0 md0 (fun _ => False) ly S W' regs1 mem1 md1 /\
    getr regs1 10 = w64 (match pc_chunks (cache S c) with [] => 0 | _ => 1 end) /\
    (forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) ->
       ~ (Pr <= bv_unsigned x < Pr + 16) -> ~ (DSTv <= bv_unsigned x < DSTv + 64) ->
       ~ (RGv <= bv_unsigned x < RGv + 128) -> ~ (T + 2768 <= bv_unsigned x < T + 2800) ->
       ~ (T + 2872 <= bv_unsigned x < T + 2888) -> mem1 x = mem0 x) /\
    val_mem tfibsegs (mrestrict (w_H W') mem1) (RGv + 68) 1 exv /\
    exh_cell_cf B ly S (aview tfibsegs (w_H W') mem1) /\ errb_cells_cf B ly S (aview tfibsegs (w_H W') mem1).
Proof.
intros HXM HOFF HOBJ exv W' c' HEXV HRET.
pose proof HRET as HRETc.
destruct HRET as (EW & regs' & mem' & mat & Ec & R10 & RCS & MEQ0 & PRS0 & HPm & PC0).
pose proof Hnf as [F0 F1]. pose proof Hmf as [[M0 M1] _]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
pose proof (wfc_classes _ _ _ _ _ WF_S c HcR) as CLS. unfold wf_class_cf in CLS.
pose proof HAR as (MA & HLg & HBg & HMWg & _).
assert (MEQX : forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) ->
  ~ (Pr <= bv_unsigned x < Pr + 16) -> ~ (DSTv <= bv_unsigned x < DSTv + 64) ->
  ~ (RGv <= bv_unsigned x < RGv + 128) -> ~ (T + 2768 <= bv_unsigned x < T + 2800) ->
  ~ (T + 2872 <= bv_unsigned x < T + 2888) -> mem' x = mem0 x).
{ intros x N0 N1 N2 N3 N4 N5. apply MEQ0. intros Hw. unfold YFk5cf.WINR0 in Hw.
  destruct Hw as [H|[H|[H|[H|H]]]]; [exact (N0 H)|exact (N1 H)|exact (N3 H)|exact (N4 H)|exact (N5 H)]. }
assert (DSTP : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem' a).
{ intros a Ha. assert (E : mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
  { apply MEQ0. rewrite unsigned_lit_small.
    - intros Hw. exact (slots_not_WINR0 a Ha Hw).
    - pose proof derived_rangesR as DR. pose proof high_factsR as (HF1 & HF2 & _).
      clear - Ha DR HF1 HF2. numconst. zlia. }
  pose proof (HslotPres' a Ha) as [Hh [bb Hb]]. split; [exact Hh|]. exists bb. rewrite E. exact Hb. }
assert (FAP : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem' a).
{ intros a Ha. assert (E : mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
  { apply MEQ0. rewrite unsigned_lit_small.
    - intros Hw. apply (fa_not_WINR0 a); [clear - Ha M0 M1; unfold kFreeArrayMax in *; zlia | exact Hw].
    - pose proof derived_rangesR as DR. pose proof high_factsR as (HF1 & HF2 & _).
      clear - Ha M0 M1 DR HF1 HF2. numconst. unfold kFreeArrayMax in *. zlia. }
  pose proof (HfaPres' a Ha) as [Hh [bb Hb]]. split; [exact Hh|]. exists bb. rewrite E. exact Hb. }
pose proof PC0 as PCv. pose proof (proj1 PCv) as PRW.
assert (NOREM : forall x : word, mem0 x <> None -> mem' x <> None \/
  (mu = mu /\ false = true /\ W_UW (bv_unsigned x)) \/ (mf = mf /\ false = true /\ W_FW (bv_unsigned x))).
{ intros x Hx0. left.
  assert (PRES : forall a, apresent (w_H W) mem' a -> bv_unsigned x = a -> mem' x <> None).
  { clear. intros a [_ [bb Hb]] <-. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
  destruct (zrange_dec (sp0 - RSTACK) sp0 (bv_unsigned x)) as [Ds|Ds]; [exact (PRES _ (PRS0 _ Ds) eq_refl)|].
  destruct (zrange_dec Pr (Pr + 16) (bv_unsigned x)) as [D1|D1]; [exact (PRES _ (PRW _ (or_introl D1)) eq_refl)|].
  destruct (zrange_dec DSTv (DSTv + 64) (bv_unsigned x)) as [D2|D2]; [exact (PRES _ (DSTP _ D2) eq_refl)|].
  destruct (zrange_dec RGv (RGv + 128) (bv_unsigned x)) as [D3|D3]; [exact (PRES _ (PRW _ (or_intror (or_introl D3))) eq_refl)|].
  destruct (zrange_dec (T + 2768) (T + 2800) (bv_unsigned x)) as [D4|D4]; [exact (PRES _ (PRW _ (or_intror (or_intror (or_introl D4)))) eq_refl)|].
  destruct (zrange_dec (T + 2872) (T + 2888) (bv_unsigned x)) as [D5|D5]; [exact (PRES _ (PRW _ (or_intror (or_intror (or_intror D5)))) eq_refl)|].
  rewrite (MEQX x Ds D1 D2 D3 D4 D5). exact Hx0. }
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PCv)))))))))))) as VJ.
(* The two cells at the result (round 2: LEAF_G's HCX / HCE, the relation carries them): the other classes' bytes and the
   errbuf object lie off the windows (RIAP, OBJAP); the class's byte is the run's exv, the model's flag. *)
assert (CX : exh_cell_cf B ly S (aview tfibsegs (w_H W) mem')).
{ apply (RepKcf.exh_cell_same B ly S _ _ c HcR HOFF (YG0ncf.ARcf_exh_cell tfibsegs B ly S Hph W mem0 md0 HAR)).
  - intros c0 Hc0 Hne. destruct (RIAP c0 Hc0 Hne _ eq_refl) as (Ra & N0 & N1 & N2 & N3 & N4 & N5).
    apply aview_same. apply MEQX; rewrite unsigned_lit_small by exact Ra; assumption.
  - unfold aview. change (ly_space ly + kRegionInfoOff + 128 * c + 68) with (RGv + 68).
    pose proof (VJ 0%nat ltac:(clear; lia)) as V. cbn [Z.of_nat] in V. rewrite Z.add_0_r in V. rewrite V.
    rewrite HEXV. destruct (YG00cf.exh_mem_cf S c); reflexivity. }
assert (VISG : forall a, aview tfibsegs (w_H W) mem0 a <> None -> aview tfibsegs (w_H W) mem' a <> None).
{ intros a Hv. set (x := Z_to_bv 64 a).
  assert (VIS : apresent (w_H W) mem' (bv_unsigned x) -> aview tfibsegs (w_H W) mem' a <> None).
  { intros [Hh [bb Hb]]. unfold x in Hh, Hb. rewrite Z_to_bv_bv_unsigned in Hh, Hb.
    unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. }
  destruct (zrange_dec (sp0 - RSTACK) sp0 (bv_unsigned x)) as [D0|D0]; [exact (VIS (PRS0 _ D0))|].
  destruct (zrange_dec Pr (Pr + 16) (bv_unsigned x)) as [D1|D1]; [exact (VIS (PRW _ (or_introl D1)))|].
  destruct (zrange_dec DSTv (DSTv + 64) (bv_unsigned x)) as [D2|D2]; [exact (VIS (DSTP _ D2))|].
  destruct (zrange_dec RGv (RGv + 128) (bv_unsigned x)) as [D3|D3]; [exact (VIS (PRW _ (or_intror (or_introl D3))))|].
  destruct (zrange_dec (T + 2768) (T + 2800) (bv_unsigned x)) as [D4|D4]; [exact (VIS (PRW _ (or_intror (or_intror (or_introl D4)))))|].
  destruct (zrange_dec (T + 2872) (T + 2888) (bv_unsigned x)) as [D5|D5]; [exact (VIS (PRW _ (or_intror (or_intror (or_intror D5)))))|].
  rewrite (aview_same (w_H W) mem0 mem' a (MEQX x D0 D1 D2 D3 D4 D5)). exact Hv. }
assert (CE : errb_cells_cf B ly S (aview tfibsegs (w_H W) mem')).
{ apply (YGcfInstBase.errb_cells_cf_frame B ly ly S S _ _ (YG0ncf.ARcf_errb_cells tfibsegs B ly S Hph W mem0 md0 HAR)
    eq_refl eq_refl eq_refl eq_refl).
  - intros a Ha. rewrite HOBJ in Ha. destruct (OBJAP a Ha) as (Ra & N0 & N1 & N2 & N3 & N4 & N5).
    apply aview_same. apply MEQX; rewrite unsigned_lit_small by exact Ra; assumption.
  - exact VISG. }
exists regs', mem', (with_vm_backing (m_vm_lazy md0) mat md0).
split. { rewrite Ec. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ pose proof (@YFkmcf.LEAF_G _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex
    need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
    IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha
    Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD Hph HARm Hinited Hnf_def Hmf_def Hau_def Hmu_def HAR
    0 mu mf [] fr hol W md0 regs' mem' mat
    ltac:(rewrite SG_is_S; exact WF_S) ltac:(clear; zlia) false false
    ltac:(intros E; discriminate E) ltac:(intros E; discriminate E)
    ltac:(left; split; [reflexivity | clear - U0 U1; zlia]) ltac:(left; reflexivity)
    ltac:(unfold YFkmcf.NF'; clear - F0 F1; zlia) ltac:(left; split; reflexivity)
    ltac:(cbn [run_elems app Z.to_nat]; reflexivity)
    ltac:(exact (wrc_runs _ _ _ _ _ _ CLS))
    ltac:(unfold YFkmcf.NF', YFkmcf.NT, YFkjcf.fr; cbn [length Z.of_nat]; rewrite <- Hnf_def; clear; zlia)
    (hsub_refl (w_H W)) (fun i Hi => Hi)
    ltac:(rewrite SG_is_S; exact (proj1 HBg)) ltac:(rewrite SG_is_S; exact HLg) HMWg
    (YGcfXsMapped.mkeep_refl [] md0) exv
    ltac:(intros x NA NB; apply MEQX; [exact NA
          | intros H; apply NB; unfold YFkmcf.XC; left; exact H
          | intros H; apply NB; unfold YFkmcf.XC; right; left; exact H
          | intros H; apply NB; unfold YFkmcf.XC; right; right; left; exact H
          | intros H; apply NB; unfold YFkmcf.XC; right; right; right; left; exact H
          | intros H; apply NB; unfold YFkmcf.XC; right; right; right; right; left; exact H])
    (fun x _ => eq_refl) NOREM PRS0 FAP DSTP
    ltac:(intros E; exfalso; exact (mu_ne_mu2 E))
    ltac:(unfold YFkmcf.NT, YFkmcf.NF', YFkmcf.AU; cbn [length]; change (Z.of_nat 0) with 0; rewrite ?Z.add_0_r, ?Z.sub_0_r, ?Z.mul_0_l; exact PC0)
    ltac:(intros j Hj; exfalso; unfold YFkmcf.NT in Hj; cbn [length Z.of_nat] in Hj; clear - Hj; zlia)
    ltac:(intros i Hi; exfalso; clear - Hi; zlia)
    ltac:(intros E; exfalso; exact (mu_ne_mu2 E)) ltac:(intros E; exfalso; exact (mf_ne_mf2 E))
    (RepVisLcf.visloc_cf B ly S Hph (aview tfibsegs (w_H W) mem0) HARm JK_ts)
    ltac:(rewrite SG_is_S; exact CX) ltac:(rewrite SG_is_S; exact CE)
    W' c' PT Ec EW R10 RCS (@wle_refl tfibsegs W) ltac:(unfold same_io; repeat split; reflexivity)) as LG.
  destruct LG as (regs1 & mem1 & md1 & Ec1 & AP & _).
  rewrite SG_is_S in AP.
  assert (Er : regs1 = regs' /\ mem1 = mem' /\ md1 = with_vm_backing (m_vm_lazy md0) mat md0).
  { rewrite Ec in Ec1. unfold cfg_at in Ec1. injection Ec1 as E1 E2 E3 E4. repeat split; congruence. }
  destruct Er as (-> & -> & ->). exact AP. }
split. { rewrite R10. rewrite Hchunks. reflexivity. }
split. { exact MEQX. }
rewrite EW. split; [exact VJ|]. split; [exact CX | exact CE].
Qed.


(* The five arm windows are allocator-owned: four inside the thread object, one the class's RegionInfo. *)
Lemma win_owned : forall a,
  (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 64) \/ (RGv <= a < RGv + 128) \/
  (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> aowned B ly S a.
Proof.
intros a Hx. pose proof derived_rangesR as DR. destruct DR as (D1 & D2 & _ & D4 & _).
assert (OT : forall b, ly_T ly <= b < ly_T ly + kThreadObjSize -> aowned B ly S b).
{ intros b Hb. apply (own_core_cf B ly S Hph (aview tfibsegs (w_H W) mem0) (ly_T ly, kThreadObjSize) b HARm);
  [ unfold core_extents; right; left; reflexivity | exact Hb ]. }
unfold T, YFk5cf.DSTv, YFk5cf.RGv in Hx. unfold YFk5cf.Pr in D2, D4, Hx.
destruct Hx as [H|[H|[H|[H|H]]]].
- apply OT. clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
- apply OT. clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
- apply (own_rinfo_cf B ly S Hph (aview tfibsegs (w_H W) mem0) a HARm). clear - H HcR. unfold kRegionInfoOff in *. lia.
- apply OT. clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
- apply OT. clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
Qed.

(* Every byte of the six windows is memnorm-safe: the stack, the thread object, below the ceiling. *)
Lemma win_mn : forall x : word,
  (sp0 - RSTACK <= bv_unsigned x < sp0) \/ (Pr <= bv_unsigned x < Pr + 16) \/ (DSTv <= bv_unsigned x < DSTv + 64) \/
  (RGv <= bv_unsigned x < RGv + 128) \/ (T + 2768 <= bv_unsigned x < T + 2800) \/ (T + 2872 <= bv_unsigned x < T + 2888) ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx. pose proof derived_rangesR as DR. destruct DR as (D1 & D2 & _ & D4 & D5 & D6 & _).
pose proof Hsp as (SP1 & SP2 & _). pose proof (lo_stk_ceil ly LY) as SC.
unfold T, YFk5cf.DSTv in Hx. unfold YFk5cf.Pr in D2, D4, Hx.
destruct Hx as [H|[H|[H|[H|[H|H]]]]].
- apply (mn_safe_stack ly x LY). clear - H SP1 SP2. unfold RSTACK in *. lia.
- apply (mn_safe_thread ly x LY IMG). clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
- apply (mn_safe_thread ly x LY IMG). clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
- apply MemnormLoc.mn_safe_ceil. clear - H D5 D6. unfold kImgEnd, kHighMemBeg in *. lia.
- apply (mn_safe_thread ly x LY IMG). clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
- apply (mn_safe_thread ly x LY IMG). clear - H D2 D4. unfold kThreadObjSize, t_cache in *. lia.
Qed.

(* leaf_G_fail's acall_post_cf, weakened to the shape refill_leaf_core_cf asks for (the populate-false return at the
   entry state: no report, the class's byte already set). *)
Lemma leaf_core_fail : YGcfXs.xs_mapped_cf ly S md0 ->
  ly_stk_lo ly + REP_STACK <= sp0 ->
  (forall a, sp0 - REP_STACK <= a < sp0 -> apresent (w_H W) mem0 a) ->
  c <> kBatchClass -> cf_exh_off = 68 -> cf_errbuf_obj = 0xa5ea8 ->
  YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) ->
  YG0ncf.errb_cells_cf B ly S (aview tfibsegs (w_H W) mem0) ->
  forall W' c',
  at_RET3 W 0 md0 WINR0 (fun m => PT m /\ P_cells W 0 nf mf au mu jex m) W' c' ->
  refill_leaf_core_cf B Hph ly S c W regs0 mem0 md0 (tt, S) W' c'.
Proof.
intros HXM HREP HpresREP HBC HOFF HOBJ HEXH HERRB W' c' HRET.
pose proof HRET as HRETc.
destruct HRETc as (EW & regsX & memX & matX & Ec & R10 & RCS & MEQ0 & PRS0 & HPm & PC0).
destruct (leaf_G_fail HXM HOFF HOBJ jex W' c' (jex_of_cell HEXH HOFF) HRET) as (regs1 & mem1 & md1 & Ec1 & AP & R10b & FR & _ & CX & CE).
rewrite Ec in Ec1. unfold cfg_at in Ec1. injection Ec1 as E1 E2 E3.

subst regs1 mem1 md1. clear E2.
pose proof (lo_stk_ceil ly LY) as SC. pose proof Hsp as (SP1 & SP2 & _). pose proof (lo_top ly LY) as LT.
assert (SPR : sp0 < 2 ^ 64) by (clear - SP2 LT; destruct LT as (_ & _ & _ & LT4 & _); unfold kHighMemEnd in *; lia).
unfold refill_leaf_core_cf. cbn [snd]. rewrite (REP_W_other c HBC).
exists ly, regsX, memX, (with_vm_backing (m_vm_lazy md0) matX md0).
split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
destruct AP as (APar & APly & APw & APrg & APio & APav & APpr).
split.
{ split; [exact APar|]. split; [exact APly|]. split; [exact APw|]. split; [exact APrg|]. split; [exact APio|].
  split.
  - intros a Ra NO NO' NS NE. apply APav; [exact Ra | exact NO | exact NO' | | intros []].
    intros Hs. apply NS. unfold ascratch in Hs |- *. destruct Hs as [Hs|He]; [left | right; exact He].
    change (spZ regs0) with sp0 in Hs |- *. clear - Hs. unfold RSTACK, REP_STACK in *. lia.
  - intros a Ha. change (spZ regs0) with sp0 in Ha.
    destruct (Z_lt_le_dec a (sp0 - RSTACK)) as [L|L].
    + assert (Hge : ASAN_CEIL <= a) by (clear - Ha SC HREP; unfold REP_STACK in *; lia).
      destruct (STKAP a Hge) as (N1 & N2 & N3 & N4 & N5).
      assert (Ra : 0 <= a < 2 ^ 64) by (pose proof (@ASAN_CEIL_range rc) as [CR1 _]; clear - Ha Hge CR1 SPR; lia).
      assert (E : memX (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
      { apply FR; rewrite unsigned_lit_small by exact Ra; [clear - L; lia | exact N1 | exact N2 | exact N3 | exact N4 | exact N5]. }
      destruct (HpresREP a ltac:(clear - Ha; unfold REP_STACK in *; lia)) as [Hh [bb Hb]].
      rewrite EW. split; [exact Hh|]. exists bb. rewrite E. exact Hb.
    + exact (APpr a (conj L (proj2 Ha))). }

split. { exact R10b. }
split. { intros _. reflexivity. }
split. { unfold YGcfXs.xs_mapped_cf in *. intros e He. rewrite m_vmmaps_wvb. exact (HXM e He). }
split; [exact CX|]. split; [exact CE|].

assert (FRO : forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ (sp0 - REP_STACK <= bv_unsigned x < sp0) -> memX x = mem0 x).
{ intros x NO NS. apply FR.
  - intros Hw. apply NS. clear - Hw. unfold RSTACK, REP_STACK in *. lia.
  - intros Hw. apply NO. apply win_owned. left. exact Hw.
  - intros Hw. apply NO. apply win_owned. right. left. exact Hw.
  - intros Hw. apply NO. apply win_owned. right. right. left. exact Hw.
  - intros Hw. apply NO. apply win_owned. right. right. right. left. exact Hw.
  - intros Hw. apply NO. apply win_owned. right. right. right. right. exact Hw. }
split.
{ intros a Ra _ NO _ NS _. rewrite EW. apply aview_same. apply FRO; rewrite unsigned_lit_small by exact Ra; [exact NO | exact NS]. }
split.
{ intros x NO _ NS _. apply FRO; [exact NO | exact NS]. }
split.
{ intros a _ Ha _. exfalso. clear - Ha. lia. }
apply (MemnormT.memnorm_frame tfibsegs (fun a => (sp0 - RSTACK <= a < sp0) \/ (Pr <= a < Pr + 16) \/
  (DSTv <= a < DSTv + 64) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888))).
- exact win_mn.
- intros x HN. apply FR.
  + intros Hw. apply HN. left. exact Hw.
  + intros Hw. apply HN. right. left. exact Hw.
  + intros Hw. apply HN. right. right. left. exact Hw.
  + intros Hw. apply HN. right. right. right. left. exact Hw.
  + intros Hw. apply HN. right. right. right. right. left. exact Hw.
  + intros Hw. apply HN. right. right. right. right. right. exact Hw.
Qed.

(* ================================================================================================================ *)
(* Arm 1: the class's byte is already set (exh_mem_cf S c = true): no report; the tree is (tt, S).                  *)


(* Arm 1 of the class-full case, end to end: RepModelcf.tree_classfull_set_cf / exh_set_same on the model side;
   RepArmcf.seg_seed_X, RepArmcf.seg3XN and leaf_core_fail on the machine side. *)
Lemma arm1_cf : mu < tot -> kFreeArrayOffset < mu + kUserMapSize -> c <> kBatchClass -> YG00cf.exh_mem_cf S c = true ->
  YGcfXs.xs_mapped_cf ly S md0 -> ly_stk_lo ly + REP_STACK <= sp0 ->
  (forall a, sp0 - REP_STACK <= a < sp0 -> apresent (w_H W) mem0 a) ->
  cf_exh_off = 68 -> cf_errbuf_obj = 0xa5ea8 ->
  YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) ->
  YG0ncf.errb_cells_cf B ly S (aview tfibsegs (w_H W) mem0) ->
  amreal tfibsegs (refill_tree_cf c S) W cfg0 (refill_leaf_core_cf B Hph ly S c W regs0 mem0 md0).
Proof.
intros Hlt Hfull HBC Hexh HXM HREP HpresREP HOFF HOBJ HEXH HERRB.
assert (Hj1 : jex = 1) by (rewrite (jex_of_cell HEXH HOFF), Hexh; reflexivity).
pose proof facts3 as (_ & _ & G3 & _). pose proof Hmu as ([U0 U1] & _).
pose proof (wfc_classes _ _ _ _ _ WF_S c HcR) as CLS. unfold wf_class_cf in CLS.
destruct (wrc_holes _ _ _ _ _ _ CLS) as [Hh Hnd].
rewrite (RepModelcf.tree_classfull_set_cf c n need S HBC Hinited Hchunks
  ltac:(rewrite cache_eta; cbn [pc_max]; exact Hmax)
  ltac:(rewrite Hn, Hmax; reflexivity)
  ltac:(rewrite <- Hnf_def; exact Hnlt)
  ltac:(rewrite <- Hnf_def; exact Hneed)
  ltac:(rewrite <- Hmu_def, <- Hau_def, <- Hcsz, <- Htot; exact Hlt)
  ltac:(rewrite <- Hmu_def, <- Hau_def, <- Hcsz, <- Htot; clear - Hlt Htot G3 U0 U1; unfold kMaxSize, kUserMapSize in *; lia)
  ltac:(rewrite <- Hmu_def; exact Hfull) Hexh).
rewrite (RepModelcf.exh_set_same c S ltac:(lia) len_regions_S Hh (proj2 (NoDup_ListNoDup _) Hnd) Hexh).
cbn [amreal].
eapply SRr_bind; [exact (RepArmcf.seg_seed_X W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex
  need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnlt Hcarved
  Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug mat0 msJ SEEDJ Hlt Hfull)|].
intros W1 c1 _ HR.
eapply SRr_bind; [exact (RepArmcf.seg3XN ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex
  need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu
  Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hra Htp ltac:(rewrite Hj1; discriminate) W md0 WINR0 PT W1 c1
  (fun a H => H) (fun m m' _ _ => I) HR)|].
intros W2 c2 _ HRET. apply SRr_ret.
exact (leaf_core_fail HXM HREP HpresREP HBC HOFF HOBJ HEXH HERRB W2 c2 HRET).
Qed.

(* ================================================================================================================ *)
(* Arm 2's first segment helpers: image literal regions added to an R3 state, and a run lemma whose scratch region   *)
(* may sit anywhere in the region list (RepArmD's report states put the two literals in front).                     *)

Definition lit_ok (a : Z) (t : option nat * Z * Z * Z * Z) : bool :=
  let '(b, lo, hi, _, _) := t in
  match b with
  | None => (hi <=? a) || (a + 8 <=? lo)
  | Some k => ((Nat.eqb k 2) && (- RSTACK <=? lo) && (hi <=? 0)) || ((Nat.eqb k 32) && (0 <=? lo) && (hi <=? 4096)) ||
              ((Nat.eqb k 37) && (0 <=? lo) && (hi <=? 16)) || ((Nat.eqb k 33) && (0 <=? lo) && (hi <=? 256)) ||
              ((Nat.eqb k 41) && (0 <=? lo) && (hi <=? 128))
  end.

Lemma lit_disjoint : forall (E : env) rs a v, (forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
  TFIB_IMG_LO <= a -> a + 8 <= TFIB_IMG_END -> forallb (lit_ok a) (map skel rs) = true -> all_disjoint E (lit8 a v) rs.
Proof.
intros E rs a v HE A1 A2 Hb. apply all_disjoint_of_forall. intros r Hin.
rewrite forallb_forall in Hb. specialize (Hb (skel r) (in_map skel rs r Hin)).
pose proof derived_rangesR as DR. destruct DR as (D1 & D2 & _ & D4 & D5 & D6 & _).
pose proof high_factsR as HF. destruct HF as (HF1 & HF2 & _ & _ & _ & _ & HF7 & HF8 & _).
pose proof stack_ivsR as (_ & _ & _ & SI4 & SI5). pose proof (@ASAN_CEIL_range rc) as [CR1 _].
unfold zone3, zone3cases in HF1, HF7.
unfold extent_disjoint, lit8. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
unfold skel, lit_ok in Hb. destruct r as [rb rlo rhi rwlo rwhi rcs]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hb |- *.
destruct rb as [k|].
- cbn [base_val]. rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Nat.eqb_eq, !Z.leb_le in Hb.
  destruct Hb as [[[[[[-> H1] H2] | [[-> H1] H2]] | [[-> H1] H2]] | [[-> H1] H2]] | [[-> H1] H2]];
  rewrite HE by (unfold aHAV3; lia).
  + rewrite E2. fold sp0. clear - A1 A2 H1 H2 SI4 SI5. unfold RSTACK, TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg in *. lia.
  + rewrite EaT. unfold w64. rewrite unsigned_lit_small by (clear - HF1 HF2 CR1; unfold kThreadObjSize in *; lia).
    clear - A1 A2 H1 H2 HF1. unfold kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, kLowShadowBeg in *. lia.
  + rewrite EaP. unfold w64. rewrite unsigned_lit_small by (unfold YFk5cf.Pr in *; clear - D1 D2 HF2 CR1; unfold kThreadObjSize in *; lia).
    unfold YFk5cf.Pr in *. clear - A1 A2 H1 H2 HF1 D2 D4. unfold kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, kLowShadowBeg, t_cache in *. lia.
  + rewrite EaC. unfold w64. rewrite unsigned_lit_small by (clear - HF7 HF8 CR1; lia).
    clear - A1 A2 H1 H2 HF7. unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, kLowShadowBeg in *. lia.
  + rewrite EaRG. unfold w64. rewrite unsigned_lit_small by (clear - D5 D6 CR1; unfold kHighMemBeg in *; lia).
    clear - A1 A2 H1 H2 D5. unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg in *. lia.
- cbn [base_val]. rewrite Bool.orb_true_iff, !Z.leb_le in Hb. lia.
Qed.

Lemma at_R3_addlit : forall (Wx : world tfibsegs) md X P ss W' c' a v,
  at_R3 Wx md X P ss W' c' -> TFIB_IMG_LO <= a -> a + 8 <= TFIB_IMG_END -> 0 <= v < 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> ~ X x) ->
  val_mem tfibsegs (mrestrict (w_H Wx) mem0) a 8 v ->
  forallb (lit_ok a) (map skel (ss_mem ss)) = true ->
  at_R3 Wx md X P (addreg (lit8 a v) ss) W' c'.
Proof.
intros Wx md X P ss W' c' a v HR A1 A2 Hv HX Hval Hb.
destruct HR as (EW & ms & mat & E' & Ec & HE & HS & MEQ & PRS & HPm).
split; [exact EW|]. exists ms, mat, E'. split; [exact Ec|]. split; [exact HE|].
split; [| split; [exact MEQ | split; [exact PRS | exact HPm]]].
unfold addreg. apply (st_ok_add_region E' ss _ (lit8 a v) HS).
- unfold YP09.region_wf, lit8, chunk_inside. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb].
  apply andb_true_intro; split; [apply andb_true_intro; split; [apply Z.leb_le; lia | apply Bool.orb_true_iff; left; apply Z.leb_le; lia]|].
  cbn. rewrite !Z.leb_refl. reflexivity.
- unfold region_ok, lit8. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  assert (A3 : 0 <= a /\ a + 8 <= 2 ^ 64) by (clear - A1 A2; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia).
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E' _ 0 a 8 (SLit v) v); [reflexivity | cbn; lia | lia |].
  rewrite Z.add_0_l. cbn [ms_mem restrict]. apply (val_mem_ext (mrestrict (w_H Wx) mem0)); [|exact Hval].
  intros k Hk. unfold mbyte, mrestrict. rewrite (MEQ (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
  rewrite unsigned_lit_small by lia. apply HX. lia.
- exact (lit_disjoint E' (ss_mem ss) a v (proj1 HE) A1 A2 Hb).
Qed.

Definition scratch_in (ss : sstate) : Prop :=
  exists cs, In (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs) (ss_mem ss).

Lemma mem_ok_scratch_in : forall (Wx : world tfibsegs) (E' : env) ss (m : word -> option byte),
  env_agree aHAV3 E0 E' -> scratch_in ss -> mem_ok tfibsegs E' (mrestrict (w_H Wx) m) (ss_mem ss) ->
  forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) m a.
Proof.
intros Wx E' ss m [HE _] [cs Hin] (_ & Hrs & _) a Ha. pose proof stack_ivsR as (_ & _ & _ & S4 & S5). pose proof (u64_range (getr regs0 2)) as U.
pose proof (proj1 (Forall_forall _ _) Hrs _ Hin) as (_ & _ & Hw & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite (HE 2%nat ltac:(unfold aHAV3; lia)), E2 in Hw.
apply writable_high_apresent; [clear - Ha S4 S5 U; unfold sp0, TFIB_IMG_END, kHighMemBeg, kHighMemEnd, RSTACK in *; lia|].
replace a with (bv_unsigned (getr regs0 2) + (a - sp0)) by (unfold sp0; lia). apply Hw. unfold sp0 in *. lia.
Qed.

Lemma at_R3_run_in : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' st W' c',
  at_R3 Wx md X P ss W' c' ->
  sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
  (forall a, WINR0 a -> X a) ->
  forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows (ss_mem ss)) = true ->
  pstable P -> scratch_in ss' ->
  SRr tfibsegs W' c' (at_R3 Wx md X P ss').
Proof.
intros Wx tbl tblok stop md X P ss ss' st W' c' HR Hrun Hst HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfibsegs tbl tblok Hwx Wx FUEL stop E' ss ss' st ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
assert (HS'' : st_ok tfibsegs E' ss' (restrict (w_H Wx) ms')) by (destruct st; [exact HS' | destruct Hst | exact HS']). clear HS'.
apply SRr_ret. split; [reflexivity|]. exists ms', mat', E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HS''|].
assert (FR : forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x) by (intros x Hx; exact (frame_X WINR0 E' _ _ _ (fun a H => H) (proj1 HE) Hwin HF x Hx)).
split; [|split].
- intros x Hx. rewrite (FR x) by (intros Hw; exact (Hx (HX _ Hw))). exact (MEQ x Hx).
- exact (mem_ok_scratch_in Wx E' ss' (ms_mem ms') HE Hsc (st_ok_mem_ok tfibsegs E' ss' _ HS'')).
- exact (HP _ _ FR HPm).
Qed.

Lemma img_not_WINR0 : forall x, TFIB_IMG_LO <= x < TFIB_IMG_END -> ~ WINR0 x.
Proof.
intros x Hx Hw. pose proof derived_rangesR as DR. destruct DR as (D1 & D2 & _ & D4 & D5 & D6 & _).
pose proof high_factsR as HF. destruct HF as (HF1 & HF2 & _).
pose proof stack_ivsR as (_ & _ & _ & SI4 & SI5). unfold zone3, zone3cases in HF1.
unfold WINR0 in Hw. unfold YFk5cf.Pr, YFk5cf.RGv in *. fold sp0 in SI4, SI5.
clear - Hx Hw D2 D4 D5 HF1 SI4.
unfold kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, kLowShadowBeg, t_cache, RSTACK in *.
destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; lia.
Qed.

Lemma U_jex0 : U E0 (SOff rJEX 0) = jex.
Proof. pose proof Hjex as J. unfold rJEX. apply (U_atom E0 55 jex EaJEX). clear - J. lia. Qed.

(* Post-call states: the stack is two regions, [-RSTACK, lo) (fresh, no chunks) and [lo, 0) (the caller's kept frame). *)
Definition scratch2 (ss : sstate) (lo : Z) : Prop :=
  - RSTACK <= lo <= 0 /\ exists cs1 cs2,
  In (YP09.mkRegion (Some 2%nat) (- RSTACK) lo (- RSTACK) lo cs1) (ss_mem ss) /\
  In (YP09.mkRegion (Some 2%nat) lo 0 lo 0 cs2) (ss_mem ss).

Lemma mem_ok_scratch2 : forall (Wx : world tfibsegs) (E' : env) ss lo (m : word -> option byte),
  env_agree aHAV3 E0 E' -> scratch2 ss lo -> mem_ok tfibsegs E' (mrestrict (w_H Wx) m) (ss_mem ss) ->
  forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) m a.
Proof.
intros Wx E' ss lo m [HE _] (Hlo & cs1 & cs2 & Hin1 & Hin2) (_ & Hrs & _) a Ha.
pose proof stack_ivsR as (_ & _ & _ & S4 & S5). pose proof (u64_range (getr regs0 2)) as U.
apply writable_high_apresent; [clear - Ha S4 S5 U; unfold sp0, TFIB_IMG_END, kHighMemBeg, kHighMemEnd, RSTACK in *; lia|].
destruct (Z_lt_le_dec a (sp0 + lo)) as [L|L].
- pose proof (proj1 (Forall_forall _ _) Hrs _ Hin1) as (_ & _ & Hw & _).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite (HE 2%nat ltac:(unfold aHAV3; lia)), E2 in Hw.
  replace a with (bv_unsigned (getr regs0 2) + (a - sp0)) by (unfold sp0; lia). apply Hw. unfold sp0 in *. lia.
- pose proof (proj1 (Forall_forall _ _) Hrs _ Hin2) as (_ & _ & Hw & _).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite (HE 2%nat ltac:(unfold aHAV3; lia)), E2 in Hw.
  replace a with (bv_unsigned (getr regs0 2) + (a - sp0)) by (unfold sp0; lia). apply Hw. unfold sp0 in *. lia.
Qed.

Lemma windows_stk : forall (E : env) rs a, (forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
  forallb (fun t => win_sub t (Some 2%nat, - RSTACK, 0) || (snd t <=? snd (fst t))) (windows rs) = true ->
  in_wrange E rs a -> sp0 - RSTACK <= a < sp0.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- pose proof (win_sub_sound E a _ _ Ht Hr) as H2. cbn [fst snd base_val] in H2.
  rewrite (HE 2%nat ltac:(unfold aHAV3; lia)), E2 in H2. unfold sp0. lia.
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.

Lemma at_R3_run_stk : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' st lo W' c',
  at_R3 Wx md X P ss W' c' ->
  sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
  (forall a, sp0 - RSTACK <= a < sp0 -> X a) ->
  forallb (fun t => win_sub t (Some 2%nat, - RSTACK, 0) || (snd t <=? snd (fst t))) (windows (ss_mem ss)) = true ->
  (forall m m', (forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) -> m' x = m x) -> P m -> P m') ->
  scratch2 ss' lo ->
  SRr tfibsegs W' c' (at_R3 Wx md X P ss').
Proof.
intros Wx tbl tblok stop md X P ss ss' st lo W' c' HR Hrun Hst HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfibsegs tbl tblok Hwx Wx FUEL stop E' ss ss' st ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
assert (HS'' : st_ok tfibsegs E' ss' (restrict (w_H Wx) ms')) by (destruct st; [exact HS' | destruct Hst | exact HS']). clear HS'.
apply SRr_ret. split; [reflexivity|]. exists ms', mat', E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HS''|].
assert (FR : forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) -> ms_mem ms' x = ms_mem ms x)
  by (intros x Hx; apply HF; intros Hw; apply Hx; exact (windows_stk E' _ _ (proj1 HE) Hwin Hw)).
split; [|split].
- intros x Hx. rewrite (FR x) by (intros Hw; exact (Hx (HX _ Hw))). exact (MEQ x Hx).
- exact (mem_ok_scratch2 Wx E' ss' lo (ms_mem ms') HE Hsc (st_ok_mem_ok tfibsegs E' ss' _ HS'')).
- exact (HP _ _ FR HPm).
Qed.

End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepTailcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 8280d695148e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 10 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 14 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (accept.tsv, re-measured each run): _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm+0xb0 (lui-in-section: CONSTANT (size; enters a store base only as a scaled count into a runtime array): kUserMapSize = 0x40000)), and 4 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, RepF1Tail): step 3d of PopulateFreeArray's class-full report arm, the TAIL
   after Printf #2.  At Printf #2's return (0x37130) the walk keeps only the caller's frame [-224, 0) of the call state
   R3_YK; [R3_YR] re-adds the fresh stack below it (RLOW1), the class's RegionInfo lock word (a writable 8-byte region
   at rRG whose chunk is the held value 2^60, ARcf_locked's third conjunct) and the image literal 0x103a0 (the Mutex
   mask GetFromAllocator's unlock loads, a Tfib_const cell).  The run [R3_YR] -> [R3_YE] is PopulateFreeArray's
   epilogue (a0 = 0), GetFromAllocator's Mutex::Unlock (0x36c60 .. 0x36d28, sc.d of 0 to the lock word) and Refill's
   epilogue up to its ret 0x36a20; its frame is the stack and the lock word ([XS]).  The post-call memory equals the
   post package's relation memory held_mem lk mem3 off [XS], so the arm's cells at the return (P_cells, exhausted byte
   1) come from the post package's ARcf (YFkkcf.cache_valsR / region_valsR / thread_present / rinfo_present), and
   RepLeafcf.leaf_G_fail applies AT THE POST PACKAGE (W3, ly3, held_mem lk mem3, md3, S3) with exv = 1 (the
   measurement).  [tail_cf] is that, closed, in the shape the report's call
   sites supply (step 3c's call state of Printf #2 and errb_call_post's unpacked post).
   The section header is YFkbcf.v's (as RepLeafcf.v), at (W, ly, mem0, md0, S) := (W3, ly3, held_mem lk mem3, md3, S3).
   rule 24: proves no function (kind: segment lemma: the tail after Printf #2 of the class-full report arm of
   SizeClassAllocator64's refill walk). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG AGif0n AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import MnRefillLocreply MemnormLoc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB19 AF0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFl1 AFhy AFis YFkpcf YFk6cf YFk5cf AFhz YFk8cf YFk7cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFk4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFk3 AB1q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YFhmcf YFkacf YFkkcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0dcf YG0qcf YG0lawscf YG06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YFkbcf YFkjcf YFkmcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfXsMapped YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RepArmD RepArmcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT RepVisLcf RepModelcf RepLeafcf RepArm2cf RepIFcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.

(* ================================================================================================================ *)
(* The re-seed after Printf #2 and the run to Refill's ret.                                                          *)
Definition STK2 : YP09.region := Eval vm_compute in match nth_error (ss_mem RepArm2cf.R3_YK) 1 with Some r => r | None => RNUL end.
Definition RGL : YP09.region := YP09.mkRegion (Some 41%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit (2 ^ 60)))].
Definition R3_YA : sstate := Eval vm_compute in ss_after_call RepArm2cf.R3_YK [STK2] 128 0x37130.
Definition R3_YR0 : sstate := Eval vm_compute in addreg RGL (addreg RepArm2cf.RLOW1 R3_YA).
Definition R3_YR : sstate := Eval vm_compute in addreg (lit8 0x103a0 0xafffff00000fffff) R3_YR0.
Definition R3_YE : sstate := Eval vm_compute in fst (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_YR).
Lemma R3_YR0_eq : R3_YR0 = addreg RGL (addreg RepArm2cf.RLOW1 (ss_after_call RepArm2cf.R3_YK [STK2] 128 0x37130)).
Proof. vm_compute. reflexivity. Qed.
Lemma R3_YR_eq : addreg (lit8 0x103a0 0xafffff00000fffff) R3_YR0 = R3_YR.
Proof. vm_compute. reflexivity. Qed.
Lemma STK2_sub : subregion STK2 (match nth_error (ss_mem RepArm2cf.R3_YK) 1 with Some r => r | None => RNUL end).
Proof.
change (match nth_error (ss_mem RepArm2cf.R3_YK) 1 with Some r => r | None => RNUL end) with STK2.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|]. intros ch Hch. exact Hch.
Qed.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
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
Local Abbreviation RIAP := (@RepLeafcf.RIAP _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation OBJAP := (@RepLeafcf.OBJAP _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation STKAP := (@RepLeafcf.STKAP _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation TZ_not_RG := (@RepArm2cf.TZ_not_RG _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation img_not_WINR0 := (@RepLeafcf.img_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation mem_ok_scratch2 := (@RepLeafcf.mem_ok_scratch2 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug LY Hmf Hmu Hsp).
Local Abbreviation at_R3_addlit := (@RepLeafcf.at_R3_addlit _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation leaf_G_fail := (@RepLeafcf.leaf_G_fail _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug B S TS HTSD Hph HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def HAR).

Local Abbreviation PT := YFkbcf.PT.

(* The tail's frame: the stack window and the class's lock word. *)
Definition XS (a : Z) : Prop := (sp0 - RSTACK <= a < sp0) \/ (RGv <= a < RGv + 8).

Lemma RR : 0 <= RGv /\ RGv + 128 < 2 ^ 64 /\ TFIB_IMG_END <= RGv.
Proof.
pose proof derived_rangesR as DR. pose proof (@ASAN_CEIL_range rc) as [CR1 _]. destruct DR as (_ & _ & _ & _ & D5 & D6 & _).
clear - D5 D6 CR1. unfold kHighMemBeg, TFIB_IMG_END in *. lia.
Qed.

Lemma XS_WINR0 : forall a, XS a -> WINR0 a.
Proof. intros a [H|H]; unfold WINR0; [left; exact H | right; right; left; lia]. Qed.

(* The arm's windows lie below the refill's stack. *)
Lemma win_below : forall a,
  (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 64) \/ (RGv <= a < RGv + 128) \/
  (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> a < sp0 - RSTACK.
Proof.
intros a Ha. destruct (Z_lt_le_dec a ASAN_CEIL) as [L|L].
- pose proof (lo_stk_ceil ly LY) as SC. pose proof Hsp as (SP1 & _). clear - L SC SP1. lia.
- exfalso. destruct (STKAP a L) as (N1 & N2 & N3 & N4 & N5). clear - Ha N1 N2 N3 N4 N5. tauto.
Qed.

(* The cells P_cells reads, other than the lock word, are off the tail's frame. *)
Lemma notXS_win : forall a,
  (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 64) \/ (RGv + 8 <= a < RGv + 128) \/
  (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> ~ XS a.
Proof.
intros a Ha. assert (B0 : a < sp0 - RSTACK).
{ apply win_below. destruct Ha as [H|[H|[H|[H|H]]]]; [left | right; left | right; right; left; lia | right; right; right; left | right; right; right; right]; exact H. }
assert (NR : ~ (RGv <= a < RGv + 8)).
{ pose proof derived_rangesR as DR. destruct DR as (_ & D2 & _ & D4 & _).
  destruct Ha as [H|[H|[H|[H|H]]]]; [| | lia | |]; intros Hr; apply (TZ_not_RG a); [| lia | | lia | | lia | | lia];
  unfold YFk5cf.DSTv, YFk5cf.Pr in *; unfold T in *; clear - H D2 D4; unfold kThreadObjSize, t_cache in *; lia. }
intros [H|H]; [lia | exact (NR H)].
Qed.

(* The run lemma of the tail: the region windows lie in the stack or the lock word. *)
Lemma windows_srg : forall (E : env) rs a, (forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
  forallb (fun t => win_sub t (Some 2%nat, - RSTACK, 0) || win_sub t (Some 41%nat, 0, 8) || (snd t <=? snd (fst t))) (windows rs) = true ->
  in_wrange E rs a -> XS a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht.
apply Bool.orb_prop in Ht as [Ht|Ht]; [apply Bool.orb_prop in Ht as [Ht|Ht]|].
- left. pose proof (win_sub_sound E a _ _ Ht Hr) as H2. cbn [fst snd base_val] in H2.
  rewrite (HE 2%nat ltac:(unfold aHAV3; lia)), E2 in H2. unfold sp0. lia.
- right. pose proof (win_sub_sound E a _ _ Ht Hr) as H2. cbn [fst snd base_val] in H2.
  rewrite (HE 41%nat ltac:(unfold aHAV3; lia)), EaRG in H2. unfold w64 in H2. pose proof RR as (R1 & R2 & _).
  rewrite unsigned_lit_small in H2 by lia. lia.
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.

Lemma at_R3_run_srg : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' st lo W' c',
  at_R3 Wx md X P ss W' c' ->
  sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
  (forall a, XS a -> X a) ->
  forallb (fun t => win_sub t (Some 2%nat, - RSTACK, 0) || win_sub t (Some 41%nat, 0, 8) || (snd t <=? snd (fst t))) (windows (ss_mem ss)) = true ->
  (forall m m', (forall x : word, ~ XS (bv_unsigned x) -> m' x = m x) -> P m -> P m') ->
  RepLeafcf.scratch2 ss' lo ->
  SRr tfibsegs W' c' (at_R3 Wx md X P ss').
Proof.
intros Wx tbl tblok stop md X P ss ss' st lo W' c' HR Hrun Hst HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfibsegs tbl tblok Hwx Wx FUEL stop E' ss ss' st ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
assert (HS'' : st_ok tfibsegs E' ss' (restrict (w_H Wx) ms')) by (destruct st; [exact HS' | destruct Hst | exact HS']). clear HS'.
apply SRr_ret. split; [reflexivity|]. exists ms', mat', E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HS''|].
assert (FR : forall x : word, ~ XS (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x)
  by (intros x Hx; apply HF; intros Hw; apply Hx; exact (windows_srg E' _ _ (proj1 HE) Hwin Hw)).
split; [|split].
- intros x Hx. rewrite (FR x) by (intros Hw; exact (Hx (HX _ Hw))). exact (MEQ x Hx).
- exact (mem_ok_scratch2 Wx E' ss' lo (ms_mem ms') HE Hsc (st_ok_mem_ok tfibsegs E' ss' _ HS'')).
- exact (HP _ _ FR HPm).
Qed.

(* The re-seed after Printf #2: reseed1's after-call step at R3_YK (the caller's frame kept), RLOW1 below it, and the
   lock word region on top (its value 2^60 at the post-call memory). *)
Lemma reseed2 : forall (W2 : world tfibsegs) msK EK regs3 (mem3 : word -> option byte),
  env_agree aHAV3 E0 EK -> st_ok tfibsegs EK RepArm2cf.R3_YK (restrict (w_H W2) msK) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W2) (ms_mem msK) a) ->
  regs_preserved (ms_regs msK) regs3 ->
  (forall a, sp0 - 224 <= a < sp0 -> mem3 (Z_to_bv 64 a) = ms_mem msK (Z_to_bv 64 a)) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem3 a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) RGv 8 (2 ^ 60) ->
  exists E2, env_agree aHAV3 E0 E2 /\
    st_ok tfibsegs E2 R3_YR0 (restrict (w_H W) (mkst regs3 (Z_to_bv 64 0x37130) mem3 (seg_rom tfibsegs))).
Proof.
intros W2 msK EK regs3 mem3 HE HS Hp1 Hrp Hkeep Hpres Hlk.
assert (HB : forall E, env_agree aHAV3 E0 E -> base_val E (Some 2%nat) = sp0).
{ intros E [HE' _]. cbn [base_val]. rewrite (HE' 2%nat ltac:(unfold aHAV3; clear; lia)), E2. reflexivity. }
pose proof RR as (R1 & R2 & R3).
assert (HG : forall E, env_agree aHAV3 E0 E -> base_val E (Some 41%nat) = RGv).
{ intros E [HE' _]. cbn [base_val]. rewrite (HE' 41%nat ltac:(unfold aHAV3; clear; lia)), EaRG. unfold w64.
  apply unsigned_lit_small. clear - R1 R2. lia. }
pose proof stack_ivsR as (_ & _ & _ & S4 & S5). fold sp0 in S4, S5.
assert (RK : Forall (region_kept tfibsegs EK (ms_mem (restrict (w_H W2) msK)) (mrestrict (w_H W) mem3)) [STK2]).
{ apply Forall_cons; [|apply Forall_nil]. split.
  - intros a Ha. cbn [STK2 YP09.r_base YP09.r_lo YP09.r_hi] in Ha. rewrite (HB EK HE) in Ha.
    cbn [ms_mem restrict]. destruct (Hpres a ltac:(clear - Ha; unfold RSTACK; lia)) as [Hh _].
    destruct (Hp1 a ltac:(clear - Ha; unfold RSTACK; lia)) as [Hh1 _].
    unfold mbyte, mrestrict. rewrite Hh, Hh1, Hkeep by (clear - Ha; lia). reflexivity.
  - intros a Ha _. cbn [STK2 YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite (HB EK HE) in Ha.
    apply apresent_writable; [clear - Ha S4 S5; unfold TFIB_IMG_END, kHighMemBeg, kHighMemEnd, RSTACK in *; lia|].
    apply Hpres. clear - Ha. unfold RSTACK. lia. }
pose proof (st_ok_after_call tfibsegs 128 EK RepArm2cf.R3_YK (restrict (w_H W2) msK) regs3 (mrestrict (w_H W) mem3) [STK2] 0x37130 HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)
  ltac:(apply submem_drop, submem_keep; [exact STK2_sub | apply submem_nil])
  ltac:(vm_compute; reflexivity) Hrp RK) as HS2.
set (E2' := havoc EK 128 (map (getr regs3) CLOB)) in HS2.
assert (HE2 : env_agree aHAV3 E0 E2').
{ apply (env_agree_havoc_ge aHAV3 128 E0 EK); [unfold aHAV3; clear; lia | exact HE]. }
exists E2'. split; [exact HE2|].
rewrite <- restrict_mkst_fx in HS2.
assert (HS3 : st_ok tfibsegs E2' (addreg RepArm2cf.RLOW1 (ss_after_call RepArm2cf.R3_YK [STK2] 128 0x37130))
  (restrict (w_H W) (mkst regs3 (Z_to_bv 64 0x37130) mem3 (seg_rom tfibsegs)))).
{ apply (st_ok_add_region E2' _ _ RepArm2cf.RLOW1 HS2 ltac:(vm_compute; reflexivity)).
  - unfold region_ok, RepArm2cf.RLOW1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite (HB E2' HE2).
    split; [clear - S4 S5; unfold RSTACK, kHighMemBeg in *; lia|]. split; [clear - S4 S5; unfold RSTACK, kHighMemEnd in *; lia|].
    split; [|apply Forall_nil]. intros o Ho. cbn [ms_mem restrict mkst].
    apply apresent_writable; [clear - Ho S4 S5; unfold TFIB_IMG_END, kHighMemBeg, kHighMemEnd, RSTACK in *; lia|].
    apply Hpres. clear - Ho. unfold RSTACK in *. lia.
  - apply all_disjoint_of_forall. intros r Hr. cbn [ss_mem ss_after_call In] in Hr. destruct Hr as [<-|[]].
    unfold extent_disjoint, RepArm2cf.RLOW1, STK2. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. left. clear. lia. }
rewrite R3_YR0_eq.
apply (st_ok_add_region E2' _ _ RGL HS3 ltac:(vm_compute; reflexivity)).
- unfold region_ok, RGL. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite (HG E2' HE2).
  split; [clear - R1; lia|]. split; [clear - R2; lia|]. split.
  + intros o Ho. cbn [ms_mem restrict mkst]. pose proof (Hlk (Z.to_nat o) ltac:(clear - Ho; lia)) as V.
    rewrite Z2Nat.id in V by (clear - Ho; lia).
    eapply AF0x.mbyte_high_writable; [|exact V]. clear - Ho R2 R3. lia.
  + apply Forall_cons; [|apply Forall_nil]. cbn [ms_mem restrict mkst].
    apply (chunk_ok_val tfibsegs E2' _ RGv 0 8 (SLit (2 ^ 60)) (2 ^ 60)); [reflexivity | cbn; clear; lia | clear; lia |].
    rewrite Z.add_0_r. exact Hlk.
- pose proof (lo_stk_ceil ly LY) as SC. pose proof Hsp as (SP1 & _). pose proof derived_rangesR as DR.
  destruct DR as (_ & _ & _ & _ & _ & D6 & _).
  apply all_disjoint_of_forall. intros r Hr. cbn [ss_mem addreg ss_after_call In] in Hr. destruct Hr as [<-|[<-|[]]];
  unfold extent_disjoint, RGL, RepArm2cf.RLOW1, STK2; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite (HG E2' HE2), (HB E2' HE2);
  left; clear - SC SP1 D6; unfold RSTACK in *; lia.
Qed.

(* The tail's seed: at_R3 at R3_YR over the post-call memory, the relation memory being held_mem lk mem3. *)
Lemma seed2 : forall (W2 : world tfibsegs) msK EK regs3 (mem3 : word -> option byte),
  mem0 = RepIFcf.held_mem (Some RGv) mem3 ->
  env_agree aHAV3 E0 EK -> st_ok tfibsegs EK RepArm2cf.R3_YK (restrict (w_H W2) msK) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W2) (ms_mem msK) a) ->
  regs_preserved (ms_regs msK) regs3 ->
  (forall a, sp0 - 224 <= a < sp0 -> mem3 (Z_to_bv 64 a) = ms_mem msK (Z_to_bv 64 a)) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem3 a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) RGv 8 (2 ^ 60) ->
  at_R3 W md0 XS PT R3_YR W (cfg_at tfibsegs (raZ (ms_regs msK)) regs3 mem3 md0).
Proof.
intros W2 msK EK regs3 mem3 Hm0 HE HS Hp1 Hrp Hkeep Hpres Hlk.
destruct (reseed2 W2 msK EK regs3 mem3 HE HS Hp1 Hrp Hkeep Hpres Hlk) as (E2' & HE2 & HS2).
assert (RA : raZ (ms_regs msK) = 0x37130).
{ pose proof (st_ok_reg_denot (w_H W2) EK RepArm2cf.R3_YK msK 1 HS) as R1.
  change (sr_get (ss_regs RepArm2cf.R3_YK) 1%bv) with (SLit 0x37130) in R1. cbn [sv_denot] in R1.
  unfold raZ. rewrite R1. apply unsigned_lit_small. clear. lia. }
assert (HR0 : at_R3 W md0 XS PT R3_YR0 W (cfg_at tfibsegs (raZ (ms_regs msK)) regs3 mem3 md0)).
{ split; [reflexivity|]. exists (mkst regs3 (Z_to_bv 64 0x37130) mem3 (seg_rom tfibsegs)), (m_vm_materialized md0), E2'.
  split. { unfold cfg_at, w64. rewrite RA, wvb_self. reflexivity. }
  split; [exact HE2|]. split; [exact HS2|].
  split. { intros x Hx. cbn [ms_mem mkst]. rewrite Hm0. unfold RepIFcf.held_mem, RepIFcf.in8.
    replace ((RGv <=? bv_unsigned x) && (bv_unsigned x <? RGv + 8)) with false; [reflexivity|].
    symmetry. apply Bool.andb_false_iff. destruct (Z_le_gt_dec RGv (bv_unsigned x)) as [L|L].
    - right. apply Z.ltb_ge. destruct (Z_lt_le_dec (bv_unsigned x) (RGv + 8)) as [L2|L2]; [exfalso; apply Hx; right; split; assumption | exact L2].
    - left. apply Z.leb_gt. clear - L. lia. }
  split; [exact Hpres | exact I]. }
pose proof (at_R3_addlit W md0 XS PT R3_YR0 W _ 0x103a0 0xafffff00000fffff HR0) as HR1.
specialize (HR1 ltac:(unfold TFIB_IMG_LO; clear; lia) ltac:(unfold TFIB_IMG_END; clear; lia) ltac:(clear; lia)
  ltac:(intros x Hx HX; apply (img_not_WINR0 x); [clear - Hx; unfold TFIB_IMG_LO, TFIB_IMG_END; lia | exact (XS_WINR0 x HX)])
  ltac:(apply (cell_lit 0x103a0 8 0xafffff00000fffff); vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
rewrite R3_YR_eq in HR1. exact HR1.
Qed.

(* Bounds of the arm's windows. *)
Lemma win_range : forall a,
  (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 64) \/ (RGv <= a < RGv + 128) \/
  (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof (win_below a Ha) as Bw. pose proof stack_ivsR as (_ & _ & _ & S4 & S5). fold sp0 in S4, S5.
pose proof derived_rangesR as DR. destruct DR as (D1 & D2 & _ & D4 & D5 & _).
unfold YFk5cf.DSTv, YFk5cf.Pr in *. unfold T in *.
clear - Ha Bw S5 D1 D2 D4 D5. unfold kHighMemEnd, kHighMemBeg, t_cache, RSTACK in *. lia.
Qed.

(* P_cells at the return with the exhausted byte 1: the memory equals the relation memory off [XS], whose cells the
   post package's ARcf gives (cache_valsR, region_valsR, thread_present, rinfo_present); the lock word is the run's 0. *)
Lemma pcells_post : forall m : word -> option byte,
  val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 68) 1 1 ->
  (forall x : word, ~ XS (bv_unsigned x) -> m x = mem0 x) ->
  val_mem tfibsegs (mrestrict (w_H W) m) RGv 8 0 ->
  P_cells W 0 nf mf au mu 1 m.
Proof.
intros m V68 MEQ Q0.
pose proof RR as (R1 & R2 & R3).
assert (RP : 0 <= Pr /\ Pr + 16 <= 2 ^ 64).
{ pose proof (win_range Pr ltac:(left; clear; lia)) as W0. pose proof (win_range (Pr + 15) ltac:(left; clear; lia)) as W15. clear - W0 W15. lia. }
assert (VX : forall a nb v, (forall k, (k < nb)%nat -> ~ XS (a + Z.of_nat k)) -> 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) a nb v -> val_mem tfibsegs (mrestrict (w_H W) m) a nb v).
{ intros a nb v Hk A0 A1 Hv. apply (val_mem_ext (mrestrict (w_H W) mem0)); [|exact Hv].
  intros k Hk'. unfold mbyte, mrestrict. rewrite (MEQ (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
  rewrite unsigned_lit_small by (clear - Hk' A0 A1; lia). exact (Hk k Hk'). }
pose proof cache_valsR as (C1 & C2 & C3).
pose proof region_valsR as (G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56).
unfold P_cells. cbv zeta.
split.
{ intros a Ha. destruct (RepLeafcf.zrange_dec RGv (RGv + 8) a) as [L|L].
  - pose proof (Q0 (Z.to_nat (a - RGv)) ltac:(clear - L; lia)) as V. rewrite Z2Nat.id in V by (clear - L; lia).
    replace (RGv + (a - RGv)) with a in V by (clear; lia).
    eapply AF0x.mbyte_high_apresent; [|exact V]. clear - L R2 R3. lia.
  - assert (Hw : (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 64) \/ (RGv <= a < RGv + 128) \/
      (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888)) by (clear - Ha; tauto).
    assert (NX : ~ XS a).
    { apply notXS_win. clear - Ha L. destruct Ha as [H|[H|[H|H]]];
      [left; exact H | right; right; left; lia | right; right; right; left; exact H | right; right; right; right; exact H]. }
    pose proof (win_range a Hw) as Ra.
    assert (P0 : apresent (w_H W) mem0 a).
    { pose proof derived_rangesR as DR. destruct DR as (D1 & D2 & _ & D4 & _).
      destruct Ha as [H|[H|[H|H]]]; [apply thread_present | apply rinfo_present; exact H | apply thread_present | apply thread_present];
      unfold YFk5cf.Pr in *; unfold T in *; clear - H D2 D4; unfold kThreadObjSize, t_cache in *; lia. }
    destruct P0 as [Hh [b Hb]]. split; [exact Hh|]. exists b.
    rewrite MEQ; [exact Hb | rewrite unsigned_lit_small by exact Ra; exact NX]. }
split; [apply VX; [intros k Hk; apply notXS_win; left; clear - Hk; lia | clear - RP; lia | clear - RP; lia | exact C1]|].
split; [apply VX; [intros k Hk; apply notXS_win; left; clear - Hk; lia | clear - RP; lia | clear - RP; lia | exact C2]|].
split; [apply VX; [intros k Hk; apply notXS_win; left; clear - Hk; lia | clear - RP; lia | clear - RP; lia | exact C3]|].
split; [exact Q0|].
split; [apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact G8]|].
split; [apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact G16]|].
split; [apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact G24]|].
split; [apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact G32]|].
split; [apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact G40]|].
split; [apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact G48]|].
split; [apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact G56]|].
apply VX; [intros k Hk; apply notXS_win; right; right; left; clear - Hk; lia | clear - R1; lia | clear - R2; lia | exact V68].
Qed.

(* The tail, from Printf #2's return to Refill's ret, with the arm's cells at the post package. *)
Lemma tail_in : forall (W2 : world tfibsegs) msK EK regs3 (mem3 : word -> option byte),
  mem0 = RepIFcf.held_mem (Some RGv) mem3 ->
  env_agree aHAV3 E0 EK -> st_ok tfibsegs EK RepArm2cf.R3_YK (restrict (w_H W2) msK) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W2) (ms_mem msK) a) ->
  regs_preserved (ms_regs msK) regs3 ->
  (forall a, sp0 - 224 <= a < sp0 -> mem3 (Z_to_bv 64 a) = ms_mem msK (Z_to_bv 64 a)) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem3 a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) RGv 8 (2 ^ 60) ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 68) 1 1 ->
  SRr tfibsegs W (cfg_at tfibsegs (raZ (ms_regs msK)) regs3 mem3 md0)
    (at_RET3 W 0 md0 WINR0 (fun m => PT m /\ P_cells W 0 nf mf au mu 1 m)).
Proof.
intros W2 msK EK regs3 mem3 Hm0 HE HS Hp1 Hrp Hkeep Hpres Hlk V68.
pose proof (seed2 W2 msK EK regs3 mem3 Hm0 HE HS Hp1 Hrp Hkeep Hpres Hlk) as HR.
let cs1 := eval vm_compute in (match nth_error (ss_mem R3_YE) 2 with Some r => YP09.r_chunks r | None => [] end) in
let cs2 := eval vm_compute in (match nth_error (ss_mem R3_YE) 3 with Some r => YP09.r_chunks r | None => [] end) in
eapply SRr_bind;
[ apply (at_R3_run_srg W tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 md0 XS PT R3_YR R3_YE (RS_stopped (SR_jalr (SOff 1 0))) (-224) W _ HR);
  [ vm_compute; reflexivity | exact I | intros a Ha; exact Ha | vm_compute; reflexivity | intros ? ? _ _; exact I
  | split; [unfold RSTACK; clear; lia | exists cs1, cs2; split; [apply (nth_error_In _ 2) | apply (nth_error_In _ 3)]; vm_compute; reflexivity] ]
| clear HR; intros W1 c1 _ HR ].
assert (HRq : at_R3 W md0 XS (fun m => PT m /\ val_mem tfibsegs (mrestrict (w_H W) m) RGv 8 0) R3_YE W1 c1).
{ apply (at_R3_facts W md0 XS PT _ R3_YE W1 c1 HR). intros E' ms HE' HS'.
  assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE')).
  pose proof RR as (R1 & R2 & _).
  eapply (chunk_val_at (w_H W) E' R3_YE ms 1 0 _ 0 8 (SLit 0) 0 RGv HS'); [reflexivity | reflexivity | | reflexivity | cbn; clear; lia | clear; lia].
  cbn [base_val YP09.r_base]. rewrite (HEn 41%nat ltac:(cbv; clear; lia)), EaRG. unfold w64.
  rewrite unsigned_lit_small by (clear - R1 R2; lia). clear. lia. }
pose proof (at_R3_strengthen W md0 XS _ (fun m => PT m /\ P_cells W 0 nf mf au mu 1 m) R3_YE W1 c1 HRq
  (fun m MEQ _ HP => conj I (pcells_post m V68 MEQ (proj2 HP)))) as HR2.
pose proof (at_R3_weaken W md0 XS WINR0 _ _ R3_YE W1 c1 HR2 XS_WINR0 (fun m Hm => Hm)) as HR3.
apply (at_R3_ret W md0 WINR0 _ R3_YE W1 c1 0 HR3); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity |].
unfold YFk5cf.CSAVED. repeat (apply Forall_cons; [vm_compute; reflexivity|]). apply Forall_nil.
Qed.

Lemma held_off : forall (mem3 : word -> option byte) x, ~ (RGv <= bv_unsigned x < RGv + 8) -> RepIFcf.held_mem (Some RGv) mem3 x = mem3 x.
Proof.
intros mem3 x Hx. unfold RepIFcf.held_mem, RepIFcf.in8.
replace ((RGv <=? bv_unsigned x) && (bv_unsigned x <? RGv + 8)) with false; [reflexivity|].
symmetry. apply Bool.andb_false_iff. destruct (Z_le_gt_dec RGv (bv_unsigned x)) as [L|L].
- right. apply Z.ltb_ge. destruct (Z_lt_le_dec (bv_unsigned x) (RGv + 8)) as [L2|L2]; [exfalso; apply Hx; split; assumption | exact L2].
- left. apply Z.leb_gt. clear - L. lia.
Qed.

(* The class's exhausted byte at the post package: exh_cell_cf with the class flagged. *)
Lemma exh_byte_post : forall (mem3 : word -> option byte), cf_exh_off = 68 ->
  YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W) mem3) -> YG00cf.exh_mem_cf S c = true ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (RGv + 68) 1 1.
Proof.
intros mem3 HO [HE _] HEM. specialize (HE c HcR). unfold cell_holds in HE. cbn [c_at c_w c_val z1 c1] in HE.
specialize (HE 0%nat ltac:(clear; lia)). cbn [Z.of_nat] in HE. rewrite Z.add_0_r in HE.
assert (EA : aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) = RGv + 68)
  by (cbn [aeval aoff]; rewrite HO; unfold YFk5cf.RGv; clear; lia).
rewrite EA, HEM in HE. unfold aview in HE.
intros k Hk. assert (k = 0%nat) by (clear - Hk; lia). subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem3) (RGv + 68)) as [b|] eqn:Eb; [|discriminate HE].
cbn [option_map] in HE. injection HE as HE. f_equal.
transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
rewrite HE. change le_byte with YO0f.le_byte. reflexivity.
Qed.

(* The tail with the leaf at the post package: leaf_G_fail's post, and the two machine cells at the result. *)
Lemma tail_sec : forall (W2 : world tfibsegs) msK EK regs3 (mem3 : word -> option byte),
  mem0 = RepIFcf.held_mem (Some RGv) mem3 ->
  env_agree aHAV3 E0 EK -> st_ok tfibsegs EK RepArm2cf.R3_YK (restrict (w_H W2) msK) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W2) (ms_mem msK) a) ->
  regs_preserved (ms_regs msK) regs3 ->
  (forall a, sp0 - 224 <= a < sp0 -> mem3 (Z_to_bv 64 a) = ms_mem msK (Z_to_bv 64 a)) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem3 a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) RGv 8 (2 ^ 60) ->
  YGcfXs.xs_mapped_cf ly S md0 -> cf_exh_off = 68 -> cf_errbuf_obj = 0xa5928 ->
  YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W) mem3) ->
  YG00cf.exh_mem_cf S c = true ->
  SRr tfibsegs W (cfg_at tfibsegs (raZ (ms_regs msK)) regs3 mem3 md0)
    (fun W' c' => exists regs1 mem1 md1, c' = cfg_at tfibsegs (raZ regs0) regs1 mem1 md1 /\
      acall_post_cf tfibsegs B RSTACK ly S Hph W regs0 mem0 md0 (fun _ => False) ly S W' regs1 mem1 md1 /\
      getr regs1 10 = w64 0 /\
      (forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) ->
         ~ (Pr <= bv_unsigned x < Pr + 16) -> ~ (DSTv <= bv_unsigned x < DSTv + 64) ->
         ~ (RGv <= bv_unsigned x < RGv + 128) -> ~ (T + 2768 <= bv_unsigned x < T + 2800) ->
         ~ (T + 2872 <= bv_unsigned x < T + 2888) -> mem1 x = mem0 x) /\
      val_mem tfibsegs (mrestrict (w_H W') mem1) (RGv + 68) 1 1 /\
      YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W') mem1) /\
      YG0ncf.errb_cells_cf B ly S (aview tfibsegs (w_H W') mem1) /\
      W' = W /\ YGcfXs.xs_mapped_cf ly S md1).
Proof.
intros W2 msK EK regs3 mem3 Hm0 HE HS Hp1 Hrp Hkeep Hpres Hlk HXM HOFF HOBJ HEXH HEM.
pose proof (exh_byte_post mem3 HOFF HEXH HEM) as V3.
assert (V0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 68) 1 1).
{ apply (val_mem_ext (mrestrict (w_H W) mem3)); [|exact V3]. intros k Hk. assert (k = 0%nat) by (clear - Hk; lia). subst k.
  cbn [Z.of_nat]. rewrite Z.add_0_r. pose proof RR as (R1 & R2 & _).
  unfold mbyte, mrestrict. rewrite Hm0, held_off; [reflexivity|]. rewrite unsigned_lit_small by (clear - R1 R2; lia). clear. lia. }
eapply SRr_bind; [exact (tail_in W2 msK EK regs3 mem3 Hm0 HE HS Hp1 Hrp Hkeep Hpres Hlk V0)|].
intros W' c' _ HRET. apply SRr_ret.
pose proof HRET as HRETc. destruct HRETc as (EW & regsX & memX & matX & Ec & R10 & RCS & MEQ0 & PRS0 & HPm & PC0).
destruct (leaf_G_fail HXM HOFF HOBJ 1 W' c' ltac:(rewrite HEM; reflexivity) HRET)
  as (regs1 & mem1 & md1 & Ec1 & AP & R10b & FR & VJ & CX & CE).
exists regs1, mem1, md1. split; [exact Ec1|]. split; [exact AP|]. split; [rewrite R10b, Hchunks; reflexivity|].
split; [exact FR|]. split; [exact VJ|]. split; [exact CX|]. split; [exact CE|].
rewrite Ec in Ec1. unfold cfg_at in Ec1. injection Ec1 as E1 E2' E3. subst regs1 mem1 md1. clear E2'.
split; [exact EW|].
unfold YGcfXs.xs_mapped_cf in *. intros e He. rewrite m_vmmaps_wvb. exact (HXM e He).
Qed.
End f.
End d.

(* ================================================================================================================ *)
(* The closed statement for step 3e: the arm's states use the entry layout ly; Printf #2 returns at ly3.            *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The arm's environment reads the layout only through T / C / space / top, which layout_le keeps. *)
Lemma E0_ly : forall k (ly ly3 : alayout) (regs0 : bvmap 5 word) (c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z),
  layout_le k ly ly3 -> YFk5cf.E0 ly3 regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug = YFk5cf.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug.
Proof.
intros k ly ly3 regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HL. destruct HL as (P1 & P2 & P3 & P4 & P5 & _ & _ & _ & P9 & _).
unfold YFk5cf.E0, YFk5cf.XWR, YFk5cf.FAv, YFk5cf.Pr, YFk5cf.RGv, YFk5cf.RBv. rewrite P2, P4, P5, P9. reflexivity.
Qed.

Lemma tail_cf :
forall (W2 W3 : world tfibsegs) (ly ly3 : alayout) (k : nat) (regs0 : bvmap 5 word)
  (c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z) (B : asyms) (S3 : astate) (Hph : list Z) (msK : machine_state) (EK : env)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model),
  let sp0 := bv_unsigned (getr regs0 2) in
  let lk := Some (RepIFcf.region_lock_addr ly3 c) in
  (* the arm's pure facts, as RepLeafcf's section takes them (at the entry layout ly) *)
  1 <= c <= 31 -> maxc = max_cached c -> n = maxc / 2 -> csz = class_size c ->
  0 <= nf /\ 4 * nf <= mf -> 0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0 ->
  0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0 ->
  0 <= j64 < 2 ^ 32 -> 0 <= jna < 2 ^ 64 -> 0 <= jnf < 2 ^ 64 -> 0 <= jsm < 2 ^ 64 ->
  0 <= jm1 < 2 ^ 64 -> 0 <= jm2 < 2 ^ 64 -> 0 <= jex < 2 ^ 8 ->
  ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0 ->
  YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = w64 TFIB_TP ->
  nf < n -> mu - au < kUserMapSize + kMaxSize -> need = n - nf -> tot = au + need * csz ->
  adr = YFk5cf.RBv ly c + mu -> sha = YFk5cf.SHBv + adr / 8 -> mu2 = mu + kUserMapSize ->
  nce = (mu - au) / csz -> ncg = (mu2 - au) / csz -> nfe = nf + nce -> nfg = nf + ncg ->
  fadr = YFk5cf.FAv ly c + mf -> shf = YFk5cf.SHBv + fadr / 8 -> mf2 = mf + kFreeArrayMapSize ->
  aue = au + nce * csz -> aug = au + ncg * csz ->
  (* the layouts: the arm's symbolic states use ly; Printf #2 returns at ly3 *)
  layout_le k ly ly3 ->
  (* Printf #2's call state (step 3c: segB's at_R3 at R3_YK, destructed) *)
  env_agree aHAV3 (YFk5cf.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug) EK ->
  st_ok tfibsegs EK RepArm2cf.R3_YK (restrict (w_H W2) msK) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W2) (ms_mem msK) a) ->
  (* Printf #2's return (errb_call_post lk PR_STK _ Hph _ _ S3 W2 (ms_regs msK) (ms_mem msK) _ W3 _, unpacked) *)
  aregs_preserved (ms_regs msK) regs3 ->
  (forall a, sp0 - 224 <= a < sp0 -> mem3 (Z_to_bv 64 a) = ms_mem msK (Z_to_bv 64 a)) ->
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W3) mem3 a) ->
  RepIFcf.errb_call_pre B lk Hph ly3 S3 W3 mem3 md3 ->
  (* the model state after the report: the class's cache and region fields as at the arm's entry, its byte set *)
  st_cache_inited S3 = true -> pc_chunks (cache S3 c) = [] ->
  nf = fa_len (rg_free (reg S3 c)) -> mf = rg_mapped_fa (reg S3 c) ->
  au = rg_alloc_user (reg S3 c) -> mu = rg_mapped_user (reg S3 c) ->
  YG00cf.exh_mem_cf S3 c = true ->
  SRr tfibsegs W3 (cfg_at tfibsegs (raZ (ms_regs msK)) regs3 mem3 md3)
    (fun W' c' => exists regs1 mem1 md1, c' = cfg_at tfibsegs (raZ regs0) regs1 mem1 md1 /\
      acall_post_cf tfibsegs B RSTACK ly3 S3 Hph W3 regs0 (RepIFcf.held_mem lk mem3) md3 (fun _ => False) ly3 S3 W' regs1 mem1 md1 /\
      getr regs1 10 = w64 0 /\
      (forall x : word, ~ (sp0 - RSTACK <= bv_unsigned x < sp0) ->
         ~ (YFk5cf.Pr ly3 c <= bv_unsigned x < YFk5cf.Pr ly3 c + 16) -> ~ (YFk5cf.DSTv ly3 c <= bv_unsigned x < YFk5cf.DSTv ly3 c + 64) ->
         ~ (YFk5cf.RGv ly3 c <= bv_unsigned x < YFk5cf.RGv ly3 c + 128) -> ~ (ly_T ly3 + 2768 <= bv_unsigned x < ly_T ly3 + 2800) ->
         ~ (ly_T ly3 + 2872 <= bv_unsigned x < ly_T ly3 + 2888) -> mem1 x = RepIFcf.held_mem lk mem3 x) /\
      val_mem tfibsegs (mrestrict (w_H W') mem1) (YFk5cf.RGv ly3 c + 68) 1 1 /\
      YG0ncf.exh_cell_cf B ly3 S3 (aview tfibsegs (w_H W') mem1) /\
      YG0ncf.errb_cells_cf B ly3 S3 (aview tfibsegs (w_H W') mem1) /\
      W' = W3 /\ YGcfXs.xs_mapped_cf ly3 S3 md1).
Proof.
intros W2 W3 ly ly3 k regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug B S3 Hph msK EK regs3 mem3 md3 sp0 lk
  HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug
  HL HE HS Hp1 Hrp Hkeep Hpres HPRE Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def HEM.
destruct HPRE as (HOBJ & HOFF & LY3 & IMG3 & TS & HTSD & (_ & HAR & HLK) & HXM & _ & _ & HEXH & _ & _).
pose proof HL as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _).
assert (Hsp3 : ly_stk_lo ly3 + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly3 /\ sp0 mod 16 = 0) by (rewrite P10, P11; exact Hsp).
assert (Hadr3 : adr = YFk5cf.RBv ly3 c + mu) by (unfold YFk5cf.RBv; rewrite P2; exact Hadr).
assert (Hfadr3 : fadr = YFk5cf.FAv ly3 c + mf) by (unfold YFk5cf.FAv, YFk5cf.RBv; rewrite P2; exact Hfadr).
rewrite <- (E0_ly k ly ly3 regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HL) in HE.
exact (@tail_sec fx rc ci cp W3 ly3 regs0 (RepIFcf.held_mem lk mem3) md3 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG3 LY3 HcR Hmax Hn Hcsz Hnf Hmf Hmu
  Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp3 Hra Htp Hnlt Hcarved Hneed Htot Hadr3 Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr3 Hshf Hmf2 Haue Haug
  B S3 TS HTSD Hph (proj1 HAR) Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def HAR W2 msK EK regs3 mem3 eq_refl HE HS Hp1
  (fun r Hr => Hrp r Hr) Hkeep Hpres HLK HXM HOFF HOBJ HEXH HEM).
Qed.
End t.

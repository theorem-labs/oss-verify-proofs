(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/FGwN.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 39d388e2ecdc) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 16 image addresses moved by code-verified function pairs (22 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py), and 16 pcs named in comments; 18 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, a Theorem Labs lane's real-merge drain walk; a Theorem Labs lane approval 01:19Z): an ADDITIVE copy of
   FGw.v for tfib_efa_spec_lk (FGtN.v): EnsureFreeArraySpace's walk with the region info's LOCK WORD (RG+0) carried as a literal
   chunk.  The ONLY semantic change against FGw.v is noted at its site; everything else is FGw.v with FGs/FGk/FGw/FGc/FGt renamed to
   their N copies.  Why: ReturnToAllocator re-reads RG+0 after the call (0x34920, the unlock), and the original leaf frames the callee by
   all of RG..RG+128, so the value was lost.  rule 24: proves function __sanitizer::SizeClassAllocator64::EnsureFreeArraySpace
   (re-walk of the released FG* walk with one more invariant chunk); reuse search `proof-index ReturnToAllocator EnsureFreeArraySpace
   0x348d0 0x3476c` 2026-10-30T01:1xZ exit 4: no released contract of EnsureFreeArraySpace that keeps RG+0 (the released
   YFgz.segK2 walks ReturnToAllocator's tail only on the no-growth arm). *)
(* The walk of EnsureFreeArraySpace entered from ReturnToAllocator: the segments between the symbolic states of FGsN.v.

   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFkd.v:473-520 (segC2g_e: 0x34ab8 -> 0x34ad0 / 0x34ad8 / 0x34af0 /
   0x34b20 -> MapWithCallback 0x6ff14 -> the mmap ecall), YFkd.v:550-640 (segD_g_e, segD_ms_e: the granted answer
   back to EnsureFreeArraySpace, the shadow fill) and YFk5.v:730-756 (at_R3_ret), re-based on EnsureFreeArraySpace's
   own entry (FGsN.SSF).  New: the no-growth arm (segA: the bgeu at 0x34ab8 taken, straight to the ret 0x34b94) and
   the return at 0x34b94 (at_R3_retF), where the refill's walk went on into PopulateFreeArray.

   The section is YFk5's (the same environment E0 and the same at_R3 / at_N3 / at_RET3), with only the hypotheses
   YFk5's state lemmas and YFkn.node3 use; the refill's own hypotheses (Ha0..Ha3, Hnlt, Hneed, ...) are not
   assumed.  [nfe] is EnsureFreeArraySpace's count argument (a3), [mf] the class's mapped free-array bytes, [fadr]
   the address of the next free-array map and [shf] its shadow. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB19 AF0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFl1 AFhy AFis AFkp AFk6 AFk5 AFhz AFk8 AFk9.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0j YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import FGsN.
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
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFIB_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
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
Local Abbreviation E0 := (@AFk5.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRB := (@AFk5.EaRB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF := (@AFk5.EaMF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHB := (@AFk5.EaSHB ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaNFe := (@AFk5.EaNFe ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaFADR := (@AFk5.EaFADR ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaSHF := (@AFk5.EaSHF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF2 := (@AFk5.EaMF2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation Er := (@AFk5.Er ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation E2 := (@AFk5.E2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Hypothesis IMG : img_cover ly.
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
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hfadr : fadr = FAv + mf.
Hypothesis Hshf : shf = SHBv + fadr / 8.
Hypothesis Hmf2 : mf2 = mf + kFreeArrayMapSize.
Hypothesis Hnfe : 0 <= nfe <= 2 ^ 27.
Local Abbreviation class_facts := (@AFk5.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@AFk5.high_factsR _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_T := (@AFk5.off_T _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_C := (@AFk5.off_C _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation derived_rangesR := (@AFk5.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation WINR0 := (@AFk5.WINR0 ly regs0 c).
Local Abbreviation W_FSH := (@AFk5.W_FSH shf).
Local Abbreviation at_R3 := (@AFk5.at_R3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_N3 := (@AFk5.at_N3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_RET3 := (@AFk5.at_RET3 _ regs0 mem0).
Local Abbreviation pstable := (@AFk5.pstable ly regs0 c).
Local Abbreviation SKEL_TAILR := (@AFk5.SKEL_TAILR).
Local Abbreviation stack_ivsR := (@AFk5.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation tail_ext_ok3 := (@AFk5.tail_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation stack_ext_ok3 := (@AFk5.stack_ext_ok3 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_run := (@AFk5.at_R3_run _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_run_ecall := (@AFk5.at_R3_run_ecall _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation at_R3_pin := (@AFk5.at_R3_pin _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_arm := (@AFk5.at_R3_arm _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_eq := (@AFk5.at_R3_eq _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_facts := (@AFk5.at_R3_facts _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_R3_weaken := (@AFk5.at_R3_weaken _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation CSAVED := (@AFk5.CSAVED).
Local Abbreviation memset_stretch3 := (@AFk5.memset_stretch3 _ ly regs0 c maxc nf mf au mu j64 jna jnf jsm jm1 jm2 HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp).
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

(* The numbers of the next free-array map (YFk5.facts3's conjuncts G24..G33, from the three definitions alone). *)
Lemma factsF :
fadr = FAv + mf /\ fadr mod 65536 = 0 /\ FAv mod 65536 = 0 /\ shf = SHBv + fadr / 8 /\ shf mod 4096 = 0 /\
2201439137792 <= shf /\ shf + 32768 <= 17594332479488 /\ kHighMemBeg <= fadr /\ fadr + kFreeArrayMapSize <= RBv + 2 ^ 32 + kFreeArrayMapSize /\
mf2 = mf + kFreeArrayMapSize.
Proof.
pose proof derived_rangesR as DR. pose proof Hmf as [[M0 M1] M2].
assert (RBAL : RBv mod 65536 = 0) by (clear - DR; tauto).
pose proof RBAL as RBAL'. apply Z.mod_divide in RBAL' as [qb Hqb]; [|clear; lia].
pose proof M2 as M2'. apply Z.mod_divide in M2' as [qm Hqm]; [|clear; unfold kFreeArrayMapSize; lia].
assert (FAE : FAv = RBv + kFreeArrayOffset) by (clear - DR; tauto).
assert (FAL : FAv mod 65536 = 0).
{ rewrite FAE, Hqb. apply Z.mod_divide; [clear; lia|]. exists (qb + 57344). unfold kFreeArrayOffset. clear; lia. }
assert (FDAL : fadr mod 65536 = 0).
{ rewrite Hfadr, FAE, Hqb, Hqm. apply Z.mod_divide; [clear; lia|]. exists (qb + 57344 + 4 * qm). unfold kFreeArrayOffset, kFreeArrayMapSize. clear; lia. }
assert (SHAL : forall x, x mod 65536 = 0 -> (SHBv + x / 8) mod 4096 = 0).
{ clear. intros x Hx. apply Z.mod_divide in Hx as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536) with (q * 8192 * 8) by lia. rewrite Z.div_mul by lia.
apply Z.mod_divide; [lia|]. exists (524280 + 2 * q). unfold SHBv. lia. }
pose proof (SHAL fadr FDAL) as SFL. rewrite <- Hshf in SFL.
assert (F1 : kHighMemBeg <= fadr) by (rewrite Hfadr, FAE; clear - DR M0; numconst; lia).
assert (F2 : fadr + kFreeArrayMapSize <= RBv + 2 ^ 32 + kFreeArrayMapSize) by (rewrite Hfadr, FAE; clear - M0 M1; numconst; lia).
assert (FCE : fadr <= ASAN_CEIL) by (clear - DR F2; numconst; lia).
assert (SF1 : 2201439137792 <= shf) by (rewrite Hshf; pose proof (Z.div_le_mono kHighMemBeg fadr 8 ltac:(clear; lia) F1) as X; clear - X; unfold SHBv, kHighMemBeg in *; change (17594333495296 / 8) with 2199291686912 in X; lia).
assert (SF2 : shf + 32768 <= 17594332479488).
{ rewrite Hshf. ceil. pose proof (Z.div_le_mono fadr 140737479966720 8 ltac:(clear; lia) ltac:(clear - FCE CR0; unfold ASAN_CEIL in *; lia)) as X. clear - X. unfold SHBv. change (140737479966720 / 8) with 17592184995840 in X. lia. }
repeat split; assumption.
Qed.
Ltac get_factsF := pose proof factsF as (G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32 & G33).

(* The no-growth arm: 4 * nfe <= mf, the bgeu at 0x34ab8 is taken, and EnsureFreeArraySpace returns 1. *)
Lemma segA : 4 * nfe <= mf -> forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P SSF W' c' -> SRr tfibsegs W' c' (at_R3 Wx md X P F_RN).
Proof.
intros Hle Wx md X P W' c' HX HP HR. pose proof Hmf as [[M0 M1] _].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x34ab8 F_D HX HP.
r3_arm HR BC_GEU true (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)).
{ arm_zev3. unfold rMF, rNFe. rewrite EaMF, EaNFe. unfold w64. clear - Hnfe M0 M1 Hle. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small mf), (unsigned_lit_small nfe) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id mf), (zcanon_id nfe) by (unfold M64; zlia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; zlia).
rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity | zlia]. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 F_RN HX HP.
apply SRr_ret. exact HR.
Qed.

(* The growth arm, up to the mmap ecall (YFkd.segC2g_e). *)
Lemma segB : mf < 4 * nfe -> 4 * nfe <= mf + kFreeArrayMapSize -> mf + kFreeArrayMapSize <= kFreeArrayMax ->
forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P SSF W' c' -> SRr tfibsegs W' c' (at_N3 Wx md X P F_N).
Proof.
intros Hfg Hfg2 Hmax2 Wx md X P W' c' HX HP HR. pose proof Hmf as [[M0 M1] M2].
get_factsF. pose proof derived_rangesR as DR.
assert (M2' : exists q, mf = q * 262144) by (apply Z.mod_divide in M2 as [q Hq]; [exists q; exact Hq | unfold kFreeArrayMapSize; zlia]). destruct M2' as [qm Hqm].
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x34ab8 F_D HX HP.
r3_arm HR BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)).
{ arm_zev3. unfold rMF, rNFe. rewrite EaMF, EaNFe. unfold w64. clear - Hnfe M0 M1 Hfg. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small mf), (unsigned_lit_small nfe) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id mf), (zcanon_id nfe) by (unfold M64; zlia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; zlia).
rewrite (proj2 (Z.ltb_lt _ _)); [reflexivity | zlia]. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x34ad0 (runto 0x34ad0 (arm BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) F_D)) HX HP.
r3_pin HR (8%bv : bv 5) (SOff rMF2 0).
{ pin_zev3. unfold rMF2, rNFe. rewrite EaMF2, EaNFe. unfold w64. clear - Hnfe M0 M1 Hfg Hfg2 G33 Hqm Hmax2. unfold kFreeArrayMax, kFreeArrayMapSize in *.
rewrite (unsigned_lit_small mf2), (unsigned_lit_small nfe) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id mf2), (zcanon_id nfe) by (unfold M64; zlia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 2) with 4. change (zcanon 262143) with 262143. change (zcanon (-262144)) with (2 ^ 64 - 2 ^ 18).
rewrite (zcanon_id (nfe * 4)) by (unfold M64; zlia). rewrite (zcanon_id (nfe * 4 + 262143)) by (unfold M64; zlia).
rewrite land_neg_pow2_u64 by zlia.
replace ((nfe * 4 + 262143) mod 2 ^ 18) with (nfe * 4 + 262143 - (qm + 1) * 262144).
2:{ apply (Z.mod_unique_pos _ (2 ^ 18) (qm + 1)); zlia. }
rewrite zcanon_id by (unfold M64; zlia). zlia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x34ad8 (runto 0x34ad8 F_1) HX HP.
r3_arm HR BC_GEU false (SOff rMF2 0) (SLit 536870913).
{ arm_zev3. unfold rMF2. rewrite EaMF2. unfold w64. clear - M0 G33 Hmax2. unfold kFreeArrayMax, kFreeArrayMapSize in *.
rewrite (unsigned_lit_small mf2) by zlia. rewrite !Z.add_0_r. rewrite (zcanon_id mf2) by (unfold M64; zlia). change (zcanon 536870913) with 536870913.
rewrite (proj2 (Z.ltb_lt _ _)); [reflexivity | zlia]. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x34af0 (runto 0x34af0 (arm BC_GEU false (SOff rMF2 0) (SLit 536870913) (runto 0x34ad8 F_1))) HX HP.
r3_pin HR (9%bv : bv 5) (SOff rFADR 0).
{ pin_zev3. unfold rFADR, rRB, rMF. rewrite EaFADR, EaRB, EaMF. unfold w64. pose proof high_factsR as (_ & _ & HF3 & HF4 & HF5 & HF6 & _).
clear - M0 M1 G24 DR HF3 HF4 HF5 HF6. numconst. unfold kFreeArrayMax in *.
rewrite (unsigned_lit_small fadr), (unsigned_lit_small RBv), (unsigned_lit_small mf) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id fadr), (zcanon_id (RBv + 3758096384)), (zcanon_id mf) by (unfold M64; zlia). rewrite zcanon_id by (unfold M64; zlia). zlia. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x34b20 (runto 0x34b20 F_2) HX HP.
r3_pin HR (18%bv : bv 5) (SLit 262144).
{ pin_zev3. unfold rMF2, rMF. rewrite EaMF2, EaMF. unfold w64. clear - M0 M1 G33. unfold kFreeArrayMax, kFreeArrayMapSize in *.
rewrite (unsigned_lit_small mf2), (unsigned_lit_small mf) by zlia. rewrite !Z.add_0_r.
rewrite (zcanon_id mf2), (zcanon_id mf) by (unfold M64; zlia). change (zcanon (-1)) with (2 ^ 64 - 1). change (zcanon 262144) with 262144.
unfold zcanon, M64. rewrite Zplus_mod_idemp_l. replace (mf * (2 ^ 64 - 1) + mf2) with (262144 + mf * 2 ^ 64) by zlia.
rewrite Z_mod_plus_full. reflexivity. }
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x6ff14 F_4 HX HP.
lazymatch type of HR with at_R3 ?Wy ?mdy ?Xy ?Py ?ss ?W4 ?c4 =>
let cs := eval vm_compute in (match nth_error (ss_mem F_N) 0 with Some r => YP09.r_chunks r | None => [] end) in
eapply (at_R3_run_ecall Wy tfibtbl_rtC tfibtbl_rtC_ok 0x7ffffff0 mdy Xy Py ss F_N W4 c4 HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | exists cs; vm_compute; reflexivity ] end.
Qed.

(* The granted answer: back through the map wrapper to EnsureFreeArraySpace, up to the shadow fill's memset
   (YFkd.segD_g_e). *)
Lemma segC : forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
at_R3 Wx md X P F_Ng W' c' -> SRr tfibsegs W' c' (at_R3 Wx md X P F_MS).
Proof.
intros Wx md X P W' c' HX HP HR. get_factsF.
r3_run HR tfibtbl_rtC tfibtbl_rtC_ok 0x7ffffff0 F_G1 HX HP.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 F_G2 HX HP.
assert (A8 : fadr mod 8 = 0).
{ clear - G25. apply Z.mod_divide in G25 as [q Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q * 8192). zlia. }
assert (AHI : fadr < 2 ^ 48) by (clear - G27 G30; pose proof (Z.mul_succ_div_gt fadr 8 ltac:(zlia)); unfold SHBv in *; zlia).
assert (D0 : 0 <= fadr / 8 < 2 ^ 45) by (clear - G31 AHI; numconst; split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; zlia]).
r3_pin HR (10%bv : bv 5) (SOff rSHF 0).
{ pin_zev3. unfold rSHF, rSHB, rFADR. rewrite EaSHF, EaSHB, EaFADR. unfold w64.
clear - G31 G27 G29 G30 A8 AHI D0. numconst. unfold SHBv in *.
rewrite (unsigned_lit_small shf), (unsigned_lit_small 2147450880), (unsigned_lit_small fadr) by zlia.
rewrite !Z.add_0_r. rewrite (zcanon_id shf), (zcanon_id 2147450880), (zcanon_id fadr) by (unfold M64; zlia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
rewrite (zcanon_id (fadr / 8)) by (unfold M64; zlia).
rewrite zcanon_id by (unfold M64; zlia). zlia. }
r3_pin HR (12%bv : bv 5) (SLit 32768).
{ pin_zev3. unfold rFADR. rewrite EaFADR. unfold w64. clear - G31 A8 AHI D0. numconst.
rewrite (unsigned_lit_small fadr) by zlia.
rewrite !Z.add_0_r. rewrite (zcanon_id (fadr + 262136)), (zcanon_id fadr) by (unfold M64; zlia).
change (Z.land (zcanon 3) 63) with 3. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
replace ((fadr + 262136) / 8) with (fadr / 8 + 32767).
2:{ apply Z.mod_divide in A8 as [q Hq]; [|zlia]. rewrite Hq. rewrite Z.div_mul by zlia. replace (q * 8 + 262136) with ((q + 32767) * 8) by zlia. rewrite Z.div_mul by zlia. zlia. }
rewrite (zcanon_id (fadr / 8 + 32767)), (zcanon_id (fadr / 8)) by (unfold M64; zlia).
change (zcanon 1) with 1. change (zcanon 32768) with 32768.
rewrite (zcanon_id (fadr / 8 + 32767 + 1)) by (unfold M64; zlia).
replace (fadr / 8 + 32767 + 1 - fadr / 8) with 32768 by zlia. reflexivity. }
r3_station HR F_MS. apply SRr_ret. exact HR.
Qed.

Definition P_fshF (P : (word -> option byte) -> Prop) : (word -> option byte) -> Prop :=
fun m => P m /\ forall x : word, W_FSH (bv_unsigned x) -> m x = Some (Z_to_bv 8 250).
Lemma pstable_fshF : forall P, pstable P -> pstable (P_fshF P).
Proof.
intros P HP m m' Hfr [H1 H2]. split; [exact (HP m m' Hfr H1)|].
intros x Hx. rewrite (Hfr x); [exact (H2 x Hx)|]. intros Hw. get_factsF.
pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (_ & _ & _ & S4 & S5).
unfold AFk5.W_FSH, AFk5.WINR0 in *. unfold AFk5.Pr, AFk5.RGv in *. clear - Hx Hw G29 G30 DR F1 F2 F3 F4 F5 F6 F7 F8 S4 S5 HcR. numconst. unfold kFreeArrayMapSize in *. change (262144 / 8) with 32768 in *. try unfold T in *. try unfold SB in *. try unfold sp0 in *. zlia.
Qed.

(* The shadow fill (memset 0xfa over the new map's shadow), the stats, the return (YFkd.segD_ms_e, then the run to
   EnsureFreeArraySpace's ret 0x34b94 in place of PopulateFreeArray's continuation). *)
Lemma segD : forall (Wx : world tfibsegs) md X P W' c',
(forall a, WINR0 a -> X a) -> pstable P ->
(forall m, P m -> forall a, W_FSH a -> apresent (w_H Wx) m a) ->
(forall m m' : word -> option byte, (forall x : word, ~ W_FSH (bv_unsigned x) -> m' x = m x) -> (forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m' a) -> P m -> P m') ->
at_R3 Wx md X P F_MS W' c' ->
SRr tfibsegs W' c' (at_R3 Wx md (fun a => X a \/ W_FSH a) (P_fshF P) F_RG).
Proof.
intros Wx md X P W' c' HX HP HPush HPu HR. get_factsF.
pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof stack_ivsR as (S1 & S2 & S3 & S4 & S5).
pose proof stack_ext_ok3 as [SX1 SX2].
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
assert (HEn : forall k, (k < aHAV3)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
rreg HS (10%bv : bv 5) R10. rewrite (HEn 65%nat ltac:(cbv; zlia)), EaSHF in R10.
rreg HS (12%bv : bv 5) R12. rreg HS (1%bv : bv 5) R1. rreg HS (11%bv : bv 5) R11.
eapply (memset_stretch3 Wx hMSF E' F_MS ms _ shf 32768 0x34b50);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| exact R10 | exact R12 | exact R1
| clear; zlia | clear - G29; numconst; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia | clear - G30; zlia | reflexivity | clear; zlia
| intros a Ha; exact (HPush _ HPm a Ha)
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|Hr];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn 2%nat ltac:(cbv; zlia)), E2;
clear - G29 G30 S4 S5 SX1 SX2; numconst; try unfold sp0 in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILR in Hr by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok3 E' r HEn Hr) as ((X1 & X2 & X3 & X4 & X5) & X6 & X7); clear - G29 G30 X1 X2 X3 X4 X5 X6 X7; numconst; zlia ].
intros regs3 mem3 mat3 HS3 H10' Hfr3 Hpr3 Hval3. rewrite wvb_collapse.
assert (HR : at_R3 Wx md (fun a => X a \/ W_FSH a) (P_fshF P) F_G3 Wx
(mkCfg (mkst regs3 (Z_to_bv 64 0x34b50) mem3 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat3 md))).
{ split; [reflexivity|]. exists (mkst regs3 (Z_to_bv 64 0x34b50) mem3 (seg_rom tfibsegs)), mat3, (havoc E' hMSF (map (getr regs3) CLOB_MS)).
split; [reflexivity|]. split; [exact (env_agree_havoc_ge aHAV3 hMSF E0 E' _ ltac:(unfold aHAV3, hMSF; zlia) HE)|].
split; [exact HS3|]. cbn [ms_mem mkst]. split; [|split].
- intros x Hx. rewrite (Hfr3 x) by (intros Hw; apply Hx; right; exact Hw). apply MEQ. intros H; apply Hx; left; exact H.
- intros a Ha. apply Hpr3. exact (PRS a Ha).
- split; [| intros x Hx; rewrite (Hval3 x Hx), R11; reflexivity].
exact (HPu (ms_mem ms) mem3 Hfr3 Hpr3 HPm). }
clear HS HS3.
assert (HX' : forall a, WINR0 a -> X a \/ W_FSH a) by (intros a Ha; left; exact (HX a Ha)).
pose proof (pstable_fshF P HP) as HP'.
r3_run HR tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 F_RG HX' HP'.
apply SRr_ret. exact HR.
Qed.

(* The return at 0x34b94 (YFk5.at_R3_ret at the refill's ret 0x36a20, here at EnsureFreeArraySpace's). *)
Lemma at_R3_retF : forall (Wx : world tfibsegs) md X P ss W' c' (v : Z),
at_R3 Wx md X P ss W' c' -> ss_resv ss = None -> ss_pc ss = A_EFA_RET ->
sr_get (ss_regs ss) 1%bv = SOff 1 0 -> sr_get (ss_regs ss) 10%bv = SLit v ->
sr_get (ss_regs ss) 4%bv = SLit TFIB_TP ->
Forall (fun r : bv 5 => sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0) CSAVED ->
SRr tfibsegs W' c' (at_RET3 Wx v md X P).
Proof.
intros Wx md X P ss W' c' v HR Hrv Hpc H1 H10 H4 Hcs.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx Wx E' ss ms _ _ HS Hrv); [rewrite Hpc; vm_compute; reflexivity|].
intros mat'. rewrite wvb_collapse.
assert (RG : forall r : bv 5, sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> (Z.to_nat (bv_unsigned r) < aHAV3)%nat -> getr (ms_regs ms) r = getr regs0 r).
{ intros r Hr Hlt. rewrite (st_ok_reg_denot (w_H Wx) E' ss ms r HS), Hr, AFk5.sv_denot_SOff0, (proj1 HE _ Hlt). apply (Er _ r). rewrite Z2Nat.id; [reflexivity | pose proof (bv_unsigned_in_range 5 r); lia]. }
assert (R1 : getr (ms_regs ms) 1 = getr regs0 1) by (apply RG; [exact H1 | cbv; lia]).
rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), mat'. split; [reflexivity|].
split. { rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 10 HS), H10. reflexivity. }
split. { intros r Hr. destruct (bv_eqb r 4%bv) eqn:E4.
- apply bv_eqb_eq in E4. subst r. rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 4 HS), H4. cbn [sv_denot]. symmetry. exact Htp.
- assert (N4 : r <> 4%bv) by (intros ->; rewrite bv_eqb_refl in E4; discriminate E4).
assert (IN : In r CSAVED).
{ unfold AFk5.CSAVED. cbn [In] in Hr. cbn [In].
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [first [exfalso; apply N4; reflexivity | tauto] |] | False => destruct Hr end. }
apply RG; [exact (proj1 (Forall_forall _ _) Hcs r IN)|].
pose proof (bv_unsigned_in_range 5 r) as B. change (bv_modulus 5) with 32 in B. unfold aHAV3. lia. }
split; [exact MEQ|]. split; [exact PRS | exact HPm].
Qed.

(* The facts of the two returns and of the ecall, by computation. *)
Lemma RN_facts : ss_resv F_RN = None /\ ss_pc F_RN = A_EFA_RET /\ sr_get (ss_regs F_RN) 1%bv = SOff 1 0 /\
sr_get (ss_regs F_RN) 10%bv = SLit 1 /\ sr_get (ss_regs F_RN) 4%bv = SLit TFIB_TP /\
Forall (fun r : bv 5 => sr_get (ss_regs F_RN) r = SOff (Z.to_nat (bv_unsigned r)) 0) CSAVED.
Proof. clear. vm_compute. repeat split; repeat constructor. Qed.
Lemma RG_facts : ss_resv F_RG = None /\ ss_pc F_RG = A_EFA_RET /\ sr_get (ss_regs F_RG) 1%bv = SOff 1 0 /\
sr_get (ss_regs F_RG) 10%bv = SLit 1 /\ sr_get (ss_regs F_RG) 4%bv = SLit TFIB_TP /\
Forall (fun r : bv 5 => sr_get (ss_regs F_RG) r = SOff (Z.to_nat (bv_unsigned r)) 0) CSAVED.
Proof. clear. vm_compute. repeat split; repeat constructor. Qed.
Definition cs_FN : list YP09.chunk := match nth_error (ss_mem F_N) 0 with Some r => YP09.r_chunks r | None => [] end.
Lemma FN_facts : ss_pc F_N = 0x65a08 /\ sr_get (ss_regs F_N) 17%bv = SLit 222 /\ sr_get (ss_regs F_N) 10%bv = SOff rFADR 0 /\ sv_atoms_lt aHAV3 (SOff rFADR 0) = true /\
sr_get (ss_regs F_N) 11%bv = SLit 262144 /\ sr_get (ss_regs F_N) 12%bv = SLit 3 /\ sr_get (ss_regs F_N) 13%bv = SLit 50 /\
sr_get (ss_regs F_N) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs F_N) 15%bv = SLit 0 /\
no_cdata (ss_mem F_N) = true /\ nth_error (ss_mem F_N) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs_FN) /\
map skel (tl (ss_mem F_N)) = SKEL_TAILR /\
resume F_N (SOff rFADR 0) (ss_mem F_N) (ss_facts F_N) = F_Ng.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Lemma U_fadrF : U E0 (SOff rFADR 0) = fadr.
Proof. get_factsF. pose proof derived_rangesR as DR. unfold rFADR. apply (U_atom E0 64 fadr EaFADR). clear - G31 G32 DR. numconst. unfold kFreeArrayMapSize in *. zlia. Qed.
Lemma band_not_WINR0F : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ WINR0 a.
Proof.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _).
pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof class_facts as (_ & _ & Kn & _).
unfold AFk5.WINR0 in Hw. clear - Ha Hw DR TH T7 S1 HcR Kn. numconst. unfold AFk5.Pr, t_cache in *. try unfold T in *. unfold RSTACK in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; zlia.
Qed.
End f.
End d.

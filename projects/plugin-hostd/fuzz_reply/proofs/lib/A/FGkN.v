(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/FGkN.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 25510ca93f6a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 10 image addresses moved by code-verified function pairs (13 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 3 data addresses the tool read as sizes, by the same value MAPS prediction, and 4 pcs named in comments; 4 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, a Theorem Labs lane's real-merge drain walk; a Theorem Labs lane approval 01:19Z): an ADDITIVE copy of
   FGk.v for tfib_efa_spec_lk (FGtN.v): EnsureFreeArraySpace's walk with the region info's LOCK WORD (RG+0) carried as a literal
   chunk.  The ONLY semantic change against FGk.v is noted at its site; everything else is FGk.v with FGs/FGk/FGw/FGc/FGt renamed to
   their N copies.  Why: ReturnToAllocator re-reads RG+0 after the call (0x34920, the unlock), and the original leaf frames the callee by
   all of RG..RG+128, so the value was lost.  rule 24: proves function __sanitizer::SizeClassAllocator64::EnsureFreeArraySpace
   (re-walk of the released FG* walk with one more invariant chunk); reuse search `proof-index ReturnToAllocator EnsureFreeArraySpace
   0x348d0 0x3476c` 2026-10-30T01:1xZ exit 4: no released contract of EnsureFreeArraySpace that keeps RG+0 (the released
   YFgz.segK2 walks ReturnToAllocator's tail only on the no-growth arm). *)
(* The seed of the EnsureFreeArraySpace walk: FGsN.SSF holds at EnsureFreeArraySpace's entry, from machine facts only.

   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFkk.v:539-776 (REG0R3_ok_but35, FACTSR3_ok, SEEDR3_ok, the seed of
   the refill walk), with every read of cgif's allocator relation (YFkk's ARm / AR hypotheses) replaced by a machine
   premise: the image's constant cells (the [as_const] list of the symbols B, as AGif0.hview's hv_const), the
   presence of the four windows the walk writes, the mapped_free_array word of the class's region info and the two
   thread stats words.  No allocator model is read here, so the seed serves cgif's instance and the shared one alike.
   The atoms the walk does not use (the refill's need, tot, adr, ...) are pinned to values in their FR3 ranges. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFl1 AFhy AFis AFhm AFkp AFk6 AFk5 AFhz AFk8 AFk9 AFkk.
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
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFIB_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.

(* The image's constant cells, from the constant-cell list of the symbols (AGiw.mv_cell_lit / mv_cell_sym). *)
Lemma const_litF : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte), TfibSyms B ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly) ->
forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) a w x.
Proof.
intros B W ly mem0 TS HC a w x E. apply (cell_holds_val_mem B ly (w_H W) mem0 (ANum a) w (ANum x)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly)) HC).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma const_symF : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte), TfibSyms B ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly) ->
forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (aeval B ly e) w (aeval B ly e').
Proof.
intros B W ly mem0 TS HC e w e' E. apply (cell_holds_val_mem B ly (w_H W) mem0 e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly)) HC).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.

Section f.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Variables (need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Local Abbreviation Pr := (@AFk5.Pr ly c).
Local Abbreviation RGv := (@AFk5.RGv ly c).
Local Abbreviation RBv := (@AFk5.RBv ly c).
Local Abbreviation FAv := (@AFk5.FAv ly c).
Local Abbreviation SHBv := (@AFk5.SHBv).
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
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Ha0 : getr regs0 10 = w64 A_ALLOCATOR.
Hypothesis Ha1 : getr regs0 11 = w64 RGv.
Hypothesis Ha2 : getr regs0 12 = w64 RBv.
Hypothesis Ha3 : getr regs0 13 = w64 nfe.
Hypothesis Hfadr : fadr = FAv + mf.
Hypothesis Hshf : shf = SHBv + fadr / 8.
Hypothesis Hmf2 : mf2 = mf + kFreeArrayMapSize.
Hypothesis Hnfe : 0 <= nfe <= 2 ^ 27.
(* the atoms the walk does not use, pinned in their FR3 ranges *)
Hypothesis Hneed : need = 1.
Hypothesis Htot : tot = 16.
Hypothesis Hadr : adr = fadr.
Hypothesis Hsha : sha = shf.
Hypothesis Hmu2 : mu2 = kUserMapSize.
Hypothesis Hnce : nce = 0.
Hypothesis Hncg : ncg = 0.
Hypothesis Hnfg : nfg = 0.
Hypothesis Haue : aue = 0.
Hypothesis Haug : aug = 0.
(* the machine facts *)
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis Hconst : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly).
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hcells : forall a, (RGv <= a < RGv + 128) \/ (Pr <= a < Pr + 16) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) ->
apresent (w_H W) mem0 a.
Hypothesis Hmfv : val_mem tfibsegs m0 (RGv + 24) 8 mf.
Hypothesis Hjm1v : val_mem tfibsegs m0 (T + 2872) 8 jm1.
Hypothesis Hjm2v : val_mem tfibsegs m0 (T + 2880) 8 jm2.
(* N: the region's lock word, as ReturnToAllocator leaves it (FGsN.LOCKV). *)
Hypothesis Hlk : val_mem tfibsegs m0 RGv 8 LOCKV.
(* N: the cells the caller re-reads after the call, carried in spare atoms (FGsN). *)
Hypothesis Hk80 : val_mem tfibsegs m0 (RGv + 80) 8 jna.
Hypothesis Hk88 : val_mem tfibsegs m0 (RGv + 88) 8 jnf.
Hypothesis Hkp : val_mem tfibsegs m0 (Pr + 0) 4 n.
Hypothesis Hks : val_mem tfibsegs m0 (Pr + 8) 8 csz.
Hypothesis Hkt : val_mem tfibsegs m0 (T + 2784) 8 jsm.
(* N: the region record's cells and the class max (FGsN.R_RGF / R_PF). *)
Hypothesis Hk8 : val_mem tfibsegs m0 (RGv + 8) 8 0.
Hypothesis Hk16 : val_mem tfibsegs m0 (RGv + 16) 8 nf.
Hypothesis Hk32 : val_mem tfibsegs m0 (RGv + 32) 8 au.
Hypothesis Hk40 : val_mem tfibsegs m0 (RGv + 40) 8 0.
Hypothesis Hk48 : val_mem tfibsegs m0 (RGv + 48) 8 mu.
Hypothesis Hk56 : val_mem tfibsegs m0 (RGv + 56) 8 0.
(* N: the class's exhausted byte RG+68 (at cf the flag; EnsureFreeArraySpace never writes it), in the spare atom j64. *)
Hypothesis Hk68 : 0 <= j64 < 2 ^ 8 /\ val_mem tfibsegs m0 (RGv + 68) 1 j64.
Hypothesis Hkmax : val_mem tfibsegs m0 (Pr + 4) 4 maxc.
Local Abbreviation class_facts := (@AFk5.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation high_factsR := (@AFk5.high_factsR _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_T := (@AFk5.off_T _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_C := (@AFk5.off_C _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation derived_rangesR := (@AFk5.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation stack_ivsR := (@AFk5.stack_ivsR _ ly regs0 maxc mf au mu LY Hmf Hmu Hsp).
Local Abbreviation PAIRSR3_ok := (@AFkk.PAIRSR3_ok _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. exact (const_litF B W ly mem0 TS Hconst). Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. exact (const_symF B W ly mem0 TS Hconst). Qed.
Lemma chunk_lit : forall a (nn : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal nn (SLit x))).
Proof. intros a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | rewrite Z.add_0_l; exact H]. Qed.
Lemma chunk_atom : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SOff k d))).
Proof.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| exact Hx | exact Hnn | exact H].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; zlia | cbn; zlia] |]); apply Forall_nil.

(* The regions of the seed hold at the entry (YFkk.REG0R3_ok_but35, with the region info, the cache cells and the
   refill's thread word reduced to what this walk reads). *)
Lemma REG0F_ok : Forall (region_ok tfibsegs E0 m0) REG0F.
Proof.
pose proof (cell_lit 0x137ce8 8 0x1010101 ltac:(vm_compute; reflexivity)) as L8.
pose proof (cell_lit 0x9da10 8 1 ltac:(vm_compute; reflexivity)) as L9.
pose proof (cell_lit 0x9da18 8 0x137bdc ltac:(vm_compute; reflexivity)) as L10.
pose proof (cell_lit 0x137bdc 4 0 ltac:(vm_compute; reflexivity)) as L11.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hnf as [N0 N1]. pose proof Hmf as [[M0 M1] M2]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7, K4, M0, M1, U1, U2.
unfold REG0F, TAILF, R_TJF, R_PF, R_RGF, REG0R3, REG0R, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE.
cbn [firstn skipn tl nth app map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold rSB, rSHB, rC, rT, rTOP, rCL, rP, rMAX, rN, rCSZ, rRG, rRB, rFA, rNF, rMF, rAU, rMU, rJ64, rJNA, rJNF, rJSM, rJM1, rJM2.
apply Forall_cons.
{ apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- 1024)); [rewrite E2; reflexivity | zlia | zlia |].
intros a Ha. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; zlia) | apply Hpres0R; unfold RSTACK; zlia]. }
do 5 (apply Forall_cons; [lit_region|]).
apply Forall_cons. { reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 34%nat 0 SB); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | | unfold SB; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 666232 with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TS); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; unfold SB; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 34%nat 137438953472 (SB + 137438953472)); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | | unfold SB; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 666248 with (aeval B ly (AInst o_rinfo)) by (cbn; rewrite (ts_inst B TS); reflexivity).
replace (SB + 137438953472) with (aeval B ly (ASp kRegionInfoOff)) by (cbn; unfold SB, kRegionInfoOff; zlia). apply cell_sym. vm_compute. reflexivity. }
do 15 (apply Forall_cons; [lit_region|]).
apply Forall_cons. { reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 48%nat 0 SHBv); [reflexivity | unfold SHBv; zlia | | unfold SHBv; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 4 (apply Forall_cons; [lit_region|]).
apply Forall_cons. { reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| cbn; zlia | cbn; zlia]. pose proof (cell_lit 0x5d9480 8 0 ltac:(vm_compute; reflexivity)) as H8.
intros k Hk. rewrite (H8 k ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
apply Forall_cons; [lit_region|].
apply Forall_cons. { reg_intro. unfold TFIB_TP. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; zlia | cbn; zlia].
replace (6132848 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. unfold TFIB_TSD. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 6268952 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; unfold T; zlia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply Hcells. unfold T in *. zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 rJSM 0 jsm); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hkt | cbn; zlia | cbn; zlia]. }
apply Forall_cons. { reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply Hcells. unfold T in *. zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 53%nat 0 jm1); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hjm1v | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 54%nat 0 jm2); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hjm2v | cbn; zlia | cbn; zlia]. }
apply Forall_cons. { reg_intro. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply Hcells. zlia. }
pose proof class_facts as (_ & _ & CFn & CFs & _).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atom _ _ 4 rN 0 n); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hkp | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 4 rMAX 0 maxc); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hkmax | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 rCSZ 0 csz); [rewrite Z.sub_0_r; reflexivity | unfold kMaxSize in *; zlia | exact Hks | cbn; unfold kMaxSize in *; zlia | cbn; zlia]. }
apply Forall_cons. { reg_intro. rewrite EaRG. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply Hcells. zlia. }
repeat (apply Forall_cons; [|]). all: try apply Forall_nil.
- eapply chunk_ok_val; [reflexivity | unfold LOCKV; cbn; zlia | cbn; zlia | rewrite Z.add_0_r; exact Hlk].
- eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | exact Hk8].
- apply (chunk_atom _ _ 8 rNF 0 nf); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hk16 | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 45%nat 0 mf); [rewrite Z.sub_0_r; exact EaMF | zlia | exact Hmfv | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 rAU 0 au); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hk32 | cbn; zlia | cbn; zlia].
- eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | exact Hk40].
- apply (chunk_atom _ _ 8 rMU 0 mu); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hk48 | cbn; zlia | cbn; zlia].
- eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | exact Hk56].
- apply (chunk_atom _ _ 1 rJ64 0 j64); [rewrite Z.sub_0_r; reflexivity | zlia | exact (proj2 Hk68) | cbn; destruct Hk68; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 rJNA 0 jna); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hk80 | cbn; zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 rJNF 0 jnf); [rewrite Z.sub_0_r; reflexivity | zlia | exact Hk88 | cbn; zlia | cbn; zlia]. }
apply Forall_cons. { reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L8]. }
apply Forall_cons. { reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L9]. }
apply Forall_cons. { reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L10]. }
apply Forall_cons; [|apply Forall_nil]. { reg_intro.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact L11]. }
Qed.

Lemma PAIRSF_ok : pairwise_disjoint E0 REG0F.
Proof. apply (pairwise_disjoint_ext3 E0 REG0R3); [vm_compute; reflexivity | exact PAIRSR3_ok]. Qed.

(* The atom facts of FR3 at the entry (YFkk.FACTSR3_ok with the walk's own values). *)
Lemma FACTSF_ok : atoms_ok E0 (f_atoms FR3).
Proof.
pose proof high_factsR as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9 & _). pose proof derived_rangesR as DR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S3 & S4). unfold RSTACK in S1.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof Hnf as [N0 N1]. pose proof Hmf as [[M0 M1] M2]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
(* the next free-array map's numbers (FGwN.factsF) *)
assert (FAE : FAv = RBv + kFreeArrayOffset) by (clear - DR; tauto).
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DR)))))))))))) as RBAL.
assert (RBAL' : RBv mod 65536 = 0) by (clear - DR; tauto). clear RBAL.
apply Z.mod_divide in RBAL' as [qb Hqb]; [|clear; lia].
pose proof M2 as M2'. apply Z.mod_divide in M2' as [qm Hqm]; [|clear; unfold kFreeArrayMapSize; lia].
assert (FDAL : fadr mod 65536 = 0).
{ rewrite Hfadr, FAE, Hqb, Hqm. apply Z.mod_divide; [clear; lia|]. exists (qb + 57344 + 4 * qm). unfold kFreeArrayOffset, kFreeArrayMapSize. clear; lia. }
assert (SFL : shf mod 4096 = 0).
{ rewrite Hshf. clear - FDAL. apply Z.mod_divide in FDAL as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536) with (q * 8192 * 8) by lia. rewrite Z.div_mul by lia.
apply Z.mod_divide; [lia|]. exists (524280 + 2 * q). unfold AFk5.SHBv. lia. }
assert (F1 : kHighMemBeg <= fadr) by (rewrite Hfadr, FAE; clear - DR M0; numconst; lia).
assert (F2 : fadr + kFreeArrayMapSize <= RBv + 2 ^ 32 + kFreeArrayMapSize) by (rewrite Hfadr, FAE; clear - M0 M1; numconst; lia).
assert (FCE : fadr <= ASAN_CEIL) by (clear - DR F2; numconst; lia).
assert (SF1 : 2201439137792 <= shf) by (rewrite Hshf; pose proof (Z.div_le_mono kHighMemBeg fadr 8 ltac:(clear; lia) F1) as X; clear - X; unfold AFk5.SHBv, kHighMemBeg in *; change (17594333495296 / 8) with 2199291686912 in X; lia).
assert (SF2 : shf + 32768 <= 17594332479488).
{ rewrite Hshf. ceil. pose proof (Z.div_le_mono fadr 140737479966720 8 ltac:(clear; lia) ltac:(clear - FCE CR0; unfold ASAN_CEIL in *; lia)) as X. clear - X. unfold AFk5.SHBv. change (140737479966720 / 8) with 17592184995840 in X. lia. }
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, T2, T4, T7, K4, M0, M1, M2, U1, U2, U3, F1, F2, FCE.
pose proof (lo_space_al ly LY) as SAL. pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL. unfold page_aligned in TAL.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; zlia. }
assert (M1r : forall x, x mod 2 ^ 0 = 0) by (intros x; replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r).
cbn [FR3 FR f_atoms atoms_ok app]. unfold rSB, rSHB, rC, rT, rTOP, rCL, rP, rMAX, rN, rCSZ, rRG, rRB, rFA, rNF, rMF, rAU, rMU, rJ64, rJNA, rJNF, rJSM, rJM1, rJM2, rNEED, rTOT, rADR, rSHA, rMU2, rNCe, rNCg, rNFe, rNFg, rFADR, rSHF, rMF2, rAUe, rAUg.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL.
split. { apply (AF 2%nat sp0); [exact E2'| | | |].
all: pose proof (u64_range (getr regs0 2)) as U; clear - U S1 S3 S4 T4 T7; unfold RSTACK in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact S4]. }
split. { apply (AF 32%nat T); [exact EaT| | | |]. all: clear - hf1 hf2 TAL; first [zlia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |]. all: clear - hf7 hf8 CAL; first [zlia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |]. all: unfold SB; clear - hf3 hf4 hf5 hf6 SAL; first [zlia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |]. all: clear - T1 T2 T3 T4 T7; first [zlia | exact T3]. }
split. { apply (AF 36%nat c); [exact EaCL| | | |]. all: clear - HcR M1r; first [zlia | apply M1r]. }
split. { apply (AF 37%nat Pr); [exact EaP| | | |]. all: clear - DR hf1 hf2; first [zlia | replace (2 ^ 4) with 16 by reflexivity; tauto]. }
split. { apply (AF 38%nat maxc); [exact EaMAX| | | |]. all: clear - K1 K2; first [zlia | replace (2 ^ 1) with 2 by reflexivity; exact K2]. }
split. { apply (AF 39%nat n); [exact EaN| | | |]. all: clear - K3 M1r; first [zlia | apply M1r]. }
split. { apply (AF 40%nat csz); [exact EaCSZ| | | |]. all: clear - K4 K5; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact K5]. }
split. { apply (AF 41%nat RGv); [exact EaRG| | | |]. all: clear - DR; first [zlia | replace (2 ^ 7) with 128 by reflexivity; tauto]. }
split. { apply (AF 42%nat RBv); [exact EaRB| | | |]. all: clear - DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 16) with 65536 by reflexivity; tauto]. }
split. { apply (AF 43%nat FAv); [exact EaFA| | | |]. all: clear - DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 12) with 4096 by reflexivity; tauto]. }
split. { apply (AF 44%nat nf); [exact EaNF| | | |]. all: clear - N0 N1 M0 M1 M1r; first [zlia | apply M1r]. }
split. { apply (AF 45%nat mf); [exact EaMF| | | |]. all: clear - M0 M1 M2; first [zlia | replace (2 ^ 18) with 262144 by reflexivity; exact M2]. }
split. { apply (AF 46%nat au); [exact EaAU| | | |]. all: clear - U0 U1 U2 U4; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact U4]. }
split. { apply (AF 47%nat mu); [exact EaMU| | | |]. all: clear - U0 U1 U2 U3; first [zlia | replace (2 ^ 18) with 262144 by reflexivity; exact U3]. }
split. { apply (AF 48%nat SHBv); [exact EaSHB| | | |]. all: clear; unfold AFk5.SHBv; first [zlia | reflexivity]. }
split. { apply (AF 49%nat j64); [reflexivity| | | |]. all: clear - Hj64 M1r; first [zlia | apply M1r]. }
split. { apply (AF 50%nat jna); [reflexivity| | | |]. all: clear - Hjna M1r; first [zlia | apply M1r]. }
split. { apply (AF 51%nat jnf); [reflexivity| | | |]. all: clear - Hjnf M1r; first [zlia | apply M1r]. }
split. { apply (AF 52%nat jsm); [reflexivity| | | |]. all: clear - Hjsm M1r; first [zlia | apply M1r]. }
split. { apply (AF 53%nat jm1); [reflexivity| | | |]. all: clear - Hjm1 M1r; first [zlia | apply M1r]. }
split. { apply (AF 54%nat jm2); [reflexivity| | | |]. all: clear - Hjm2 M1r; first [zlia | apply M1r]. }
split. { apply (AF 55%nat need); [exact EaNEED| | | |]. all: try rewrite Hneed; first [zlia | apply M1r]. }
split. { apply (AF 56%nat tot); [exact EaTOT| | | |]. all: try rewrite Htot; first [zlia | reflexivity]. }
split. { apply (AF 57%nat adr); [exact EaADR| | | |]. all: try rewrite Hadr; clear - F1 F2 FDAL DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 16) with 65536 by reflexivity; exact FDAL]. }
split. { apply (AF 58%nat sha); [exact EaSHA| | | |]. all: try rewrite Hsha; clear - SF1 SF2 SFL; first [zlia | replace (2 ^ 12) with 4096 by reflexivity; exact SFL]. }
split. { apply (AF 59%nat mu2); [exact EaMU2| | | |]. all: try rewrite Hmu2; unfold kUserMapSize; first [zlia | reflexivity]. }
split. { apply (AF 60%nat nce); [exact EaNCe| | | |]. all: try rewrite Hnce; first [zlia | reflexivity]. }
split. { apply (AF 61%nat ncg); [exact EaNCg| | | |]. all: try rewrite Hncg; first [zlia | reflexivity]. }
split. { apply (AF 62%nat nfe); [exact EaNFe| | | |]. all: clear - Hnfe M1r; first [zlia | apply M1r]. }
split. { apply (AF 63%nat nfg); [exact EaNFg| | | |]. all: try rewrite Hnfg; first [zlia | reflexivity]. }
split. { apply (AF 64%nat fadr); [exact EaFADR| | | |]. all: clear - F1 F2 FDAL DR hf3 hf4 hf5 hf6; first [zlia | replace (2 ^ 16) with 65536 by reflexivity; exact FDAL]. }
split. { apply (AF 65%nat shf); [exact EaSHF| | | |]. all: clear - SF1 SF2 SFL; first [zlia | replace (2 ^ 12) with 4096 by reflexivity; exact SFL]. }
split. { apply (AF 66%nat mf2); [exact EaMF2| | | |]. all: try rewrite Hmf2; unfold kFreeArrayMapSize; clear - M0 M1 M2; try zlia.
replace (2 ^ 18) with 262144 by reflexivity. apply Z.mod_divide in M2 as [q Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q + 1). zlia. }
split. { apply (AF 67%nat aue); [exact EaAUe| | | |]. all: try rewrite Haue; first [zlia | reflexivity]. }
split; [|exact I]. { apply (AF 68%nat aug); [exact EaAUg| | | |]. all: try rewrite Haug; first [zlia | reflexivity]. }
Qed.

(* The seed (YFkk.SEEDR3_ok at 0x369c8, here at EnsureFreeArraySpace's entry). *)
Lemma SEEDF_ok : st_ok tfibsegs E0 SSF (restrict (w_H W) (mkst regs0 (w64 A_EFA) mem0 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold SSF, REGSF, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 (AFk5.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug)) rNFe) with (ew E0 62); rewrite EaNFe, Ha3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 (AFk5.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug)) rRB) with (ew E0 42); rewrite EaRB, Ha2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; change (ew (Ereg regs0 (AFk5.XWR ly c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug)) rRG) with (ew E0 41); rewrite EaRG, Ha1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact Ha0].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0F_ok.
- exact PAIRSF_ok.
- split; [exact FACTSF_ok | split; exact I].
Qed.
End f.
End d.

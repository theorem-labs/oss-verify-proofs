(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/FGcN.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 375e5096a330) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 11 pcs named in comments; 6 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, a Theorem Labs lane's real-merge drain walk; a Theorem Labs lane approval 01:19Z): an ADDITIVE copy of
   FGc.v for tfib_efa_spec_lk (FGtN.v): EnsureFreeArraySpace's walk with the region info's LOCK WORD (RG+0) carried as a literal
   chunk.  The ONLY semantic change against FGc.v is noted at its site; everything else is FGc.v with FGs/FGk/FGw/FGc/FGt renamed to
   their N copies.  Why: ReturnToAllocator re-reads RG+0 after the call (0x34920, the unlock), and the original leaf frames the callee by
   all of RG..RG+128, so the value was lost.  rule 24: proves function __sanitizer::SizeClassAllocator64::EnsureFreeArraySpace
   (re-walk of the released FG* walk with one more invariant chunk); reuse search `proof-index ReturnToAllocator EnsureFreeArraySpace
   0x348d0 0x3476c` 2026-10-30T01:1xZ exit 4: no released contract of EnsureFreeArraySpace that keeps RG+0 (the released
   YFgz.segK2 walks ReturnToAllocator's tail only on the no-growth arm). *)
(* The callee contract of EnsureFreeArraySpace (0x34a94) entered from ReturnToAllocator (the jal at 0x348cc, model
   YG00.v:453: ensure_free_array c newlen true), with the caller's frame abstract.

   Ported from the released growth walk of the refill path: proofs/cgif/cgif_file_fuzzer/lib/YFkd.v:473-520 (the walk
   to the mmap ecall), YFkn.v:757-911 (node3, the KMapFreeArray node over commit_node3, YG0c.v:69) and its use at
   YFkn.v:1535-1610 (refill_B3_eg: E_efa_g, node3, segD_g_e, segD_ms_e).  New: the entry / exit frame of the free
   path (spin_on_fail = true; the seed FGkN.SEEDF_ok, the walk FGwN.v, the return 0x34b94) and the model lemmas for
   spin_on_fail = true below.

   The two answers of the KMapFreeArray request.
   - granted: the walk maps the next 256 KiB of the class's free array (MAP_FIXED inside the reservation), fills its
     shadow, stores mapped_free_array := mf + kFreeArrayMapSize and returns 1; the model sets the region
     (efa_leaf's second disjunct);
   - refused: the model spins (E_efaT_g: K z = ISpin 213516 for every z <> 1).  The refused answer is no step of the
     run: cgif_file's node_ok is over sstep_cfg ACFG (R/Cfg.v), which drops a refusal while a non-refusal outcome
     exists, and with the footprint room (the premise [eager_used md0 + A_bytes + 2 * kUserMapSize + 32768 <=
     vm_limit]) the budget gate passes, so node3 has no refused successor (sp = false).  The halts statement's form
     of the same fact, over forced_only_cfg, is FGrf.fo_dead_freearray_refused (the fo_dead_commit3 treatment of
     cgif_rgb_fuzzer/lib/YF8e.v:791, over FGfo.v, the port of cgif_rgb's HaltsFO.v).

   No allocator relation is read: every premise is a machine fact (FGkN's seed premises) or a model fact about the one
   region field the walk reads (rg_mapped_fa (reg S c) = mf, mirrored at RGv + 24).  So the contract serves cgif's
   instance and the shared (reply / preset) instance alike; the generic Deallocate's drain / recycle callee
   (DMspec.tfib_drain_spec_cf, drain_body_cf -> do_recycle -> cache_dealloc -> return_to_allocator) cites
   [efa_ret_contract] at the jal 0x348cc and resumes at 0x348d0 from [efa_leaf]. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFkn FGwN FGkN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model: ensure_free_array c need true (YG00.v:258-275), for one map step.                                      *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* The region after a granted free-array map (YG00.v:267-268). *)
Definition rgG (r : region) : region :=
  mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r + kFreeArrayMapSize) (rg_free r)
    (del_hole (kFreeArrayOffset + rg_mapped_fa r) (rg_holes r)).

Lemma round_upF : forall m x, m mod kFreeArrayMapSize = 0 -> 0 <= m -> m < x -> x <= m + kFreeArrayMapSize ->
  round_up x kFreeArrayMapSize = m + kFreeArrayMapSize.
Proof.
  intros m x Hm H0 H1 H2. unfold round_up. unfold kFreeArrayMapSize in *.
  apply Z.mod_divide in Hm as [q Hq]; [|lia]. subst m.
  replace ((x + 262144 - 1) / 262144) with (q + 1); [lia|].
  apply (Z.div_unique_pos (x + 262144 - 1) 262144 (q + 1) (x - 1 - q * 262144)); lia.
Qed.

(* No growth: 4 * need <= mapped. *)
Lemma E_efaT_e : forall (S : astate) c nd, 4 * nd <= rg_mapped_fa (reg S c) ->
  ensure_free_array c nd true S = IRet (true, S).
Proof.
  intros S c nd Hle. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
  change (znth region0 c (st_regions S)) with (reg S c).
  replace (4 * nd <=? rg_mapped_fa (reg S c)) with true by (symmetry; apply Z.leb_le; exact Hle). reflexivity.
Qed.

(* One map step: the request, its granted continuation, and the spin of every other answer. *)
Lemma E_efaT_g : forall (S : astate) c nd mfv, rg_mapped_fa (reg S c) = mfv ->
  mfv mod kFreeArrayMapSize = 0 -> 0 <= mfv -> mfv < 4 * nd -> 4 * nd <= mfv + kFreeArrayMapSize ->
  mfv + kFreeArrayMapSize <= kFreeArrayMax ->
  exists K, ensure_free_array c nd true S = IAsk (KMapFreeArray c mfv kFreeArrayMapSize) S K /\
    K 1 = IRet (true, upd_reg c (rgG (reg S c)) S) /\ (forall z, z <> 1 -> K z = ISpin 213516).
Proof.
  intros S c nd mfv Hm Hal H0 Hlt Hle Hmax. unfold ensure_free_array. unfold bind at 1. unfold get_region, bind at 1, get, ret at 1. cbn [ibind].
  change (znth region0 c (st_regions S)) with (reg S c). rewrite Hm.
  replace (4 * nd <=? mfv) with false by (symmetry; apply Z.leb_gt; exact Hlt).
  rewrite (round_upF mfv (4 * nd) Hal H0 Hlt Hle).
  unfold mcheck. replace (mfv + kFreeArrayMapSize <=? kFreeArrayMax) with true by (symmetry; apply Z.leb_le; exact Hmax).
  unfold bind at 1. unfold ret at 1. cbn [ibind]. unfold bind at 1. unfold askz. cbn [ibind].
  replace (mfv + kFreeArrayMapSize - mfv) with kFreeArrayMapSize by lia.
  eexists. split; [reflexivity|]. split.
  - cbn [aGranted Z.eqb Pos.eqb]. unfold bind, set_region, modify, ret. cbn [ibind]. unfold upd_reg, rgG. rewrite Hm. reflexivity.
  - intros z Hz. cbv beta. unfold aGranted, aDestroyed. rewrite (proj2 (Z.eqb_neq z 1) Hz).
    destruct (z =? 2); unfold bind, set_region, modify, ret, spin; cbn [ibind]; reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFIB_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.

Definition PT : (word -> option byte) -> Prop := fun _ => True.

Section f.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Variables (need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Local Abbreviation Pr := (@AFk5.Pr ly c).
Local Abbreviation RGv := (@AFk5.RGv ly c).
Local Abbreviation RBv := (@AFk5.RBv ly c).
Local Abbreviation FAv := (@AFk5.FAv ly c).
Local Abbreviation SHBv := (@AFk5.SHBv).
Local Abbreviation E0 := (@AFk5.E0 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaRG := (@AFk5.EaRG ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF := (@AFk5.EaMF ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation EaMF2 := (@AFk5.EaMF2 ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
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
Hypothesis Ha0 : getr regs0 10 = w64 A_ALLOCATOR.
Hypothesis Ha1 : getr regs0 11 = w64 RGv.
Hypothesis Ha2 : getr regs0 12 = w64 RBv.
Hypothesis Ha3 : getr regs0 13 = w64 nfe.
Hypothesis Hfadr : fadr = FAv + mf.
Hypothesis Hshf : shf = SHBv + fadr / 8.
Hypothesis Hmf2 : mf2 = mf + kFreeArrayMapSize.
Hypothesis Hnfe : 0 <= nfe <= 2 ^ 27.
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
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis Hconst : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly).
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hcells : forall a, (RGv <= a < RGv + 128) \/ (Pr <= a < Pr + 16) \/ (ly_T ly + 2768 <= a < ly_T ly + 2800) \/ (ly_T ly + 2872 <= a < ly_T ly + 2888) ->
apresent (w_H W) mem0 a.
Hypothesis Hmfv : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 24) 8 mf.
Hypothesis Hjm1v : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2872) 8 jm1.
Hypothesis Hjm2v : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2880) 8 jm2.
(* N: the region's lock word as ReturnToAllocator leaves it (FGsN.LOCKV, measured at 0x347fc-0x34830). *)
Hypothesis Hlk : val_mem tfibsegs (mrestrict (w_H W) mem0) RGv 8 LOCKV.
(* N: the cells the caller re-reads after the call (FGsN), carried in spare atoms. *)
Hypothesis Hk80 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 80) 8 jna.
Hypothesis Hk88 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 88) 8 jnf.
Hypothesis Hkp : val_mem tfibsegs (mrestrict (w_H W) mem0) (Pr + 0) 4 n.
Hypothesis Hks : val_mem tfibsegs (mrestrict (w_H W) mem0) (Pr + 8) 8 csz.
Hypothesis Hkt : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2784) 8 jsm.
Hypothesis Hk8 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 8) 8 0.
Hypothesis Hk16 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 16) 8 nf.
Hypothesis Hk32 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 32) 8 au.
Hypothesis Hk40 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 40) 8 0.
Hypothesis Hk48 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 48) 8 mu.
Hypothesis Hk56 : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 56) 8 0.
Hypothesis Hk68 : 0 <= j64 < 2 ^ 8 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 68) 1 j64.
Hypothesis Hkmax : val_mem tfibsegs (mrestrict (w_H W) mem0) (Pr + 4) 4 maxc.
Local Abbreviation WINR0 := (@AFk5.WINR0 ly regs0 c).
Local Abbreviation W_FSH := (@AFk5.W_FSH shf).
Local Abbreviation at_R3 := (@AFk5.at_R3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation at_RET3 := (@AFk5.at_RET3 _ regs0 mem0).
Local Abbreviation pstable := (@AFk5.pstable ly regs0 c).
Local Abbreviation class_facts := (@AFk5.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu).
Local Abbreviation derived_rangesR := (@AFk5.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu).
Local Abbreviation high_factsR := (@AFk5.high_factsR _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation off_T := (@AFk5.off_T _ ly regs0 maxc mf au mu IMG LY Hmf Hmu).
Local Abbreviation fa_not := (@AFk5.fa_not_WINR0 _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation band_not := (@FGwN.band_not_WINR0F _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation factsF := (@FGwN.factsF _ ly regs0 c maxc n nf mf au mu csz fadr shf mf2 IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hfadr Hshf Hmf2).
Local Abbreviation U_fadrF := (@FGwN.U_fadrF _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hfadr Hshf Hmf2).
Local Abbreviation segA := (@FGwN.segA _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hnfe).
Local Abbreviation segB := (@FGwN.segB _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hfadr Hshf Hmf2 Hnfe).
Local Abbreviation segC := (@FGwN.segC _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hfadr Hshf Hmf2).
Local Abbreviation segD := (@FGwN.segD _ _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hfadr Hshf Hmf2).
Local Abbreviation retF := (@FGwN.at_R3_retF _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug HcR Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnfe).
Local Abbreviation at_R3_facts := (@AFk5.at_R3_facts _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug).
Local Abbreviation node3 := (@AFkn.node3 _ _ ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp).
Local Abbreviation SEED := (@FGkN.SEEDF_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hfadr Hshf Hmf2 Hnfe Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfg Haue Haug B TS HTSD Hconst Hpres0R Hcells Hmfv Hjm1v Hjm2v Hlk Hk80 Hk88 Hkp Hks Hkt Hk8 Hk16 Hk32 Hk40 Hk48 Hk56 Hk68 Hkmax).

(* The class's mapped_free_array word, read at RGv + 24. *)
Definition P_mf (Wx : world tfibsegs) (v : Z) (m : word -> option byte) : Prop :=
  val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 24) 8 v.
(* N: the lock word at RG+0, read off the literal chunk of region 36 (FGsN.R_RGF). *)
Definition P_lk (Wx : world tfibsegs) (m : word -> option byte) : Prop :=
  val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 0) 8 LOCKV /\
  val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 80) 8 jna /\ val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 88) 8 jnf /\
  val_mem tfibsegs (mrestrict (w_H Wx) m) (Pr + 0) 4 n /\ val_mem tfibsegs (mrestrict (w_H Wx) m) (Pr + 8) 8 csz /\
  val_mem tfibsegs (mrestrict (w_H Wx) m) (ly_T ly + 2784) 8 jsm /\
  (* the region info stays present (ReturnToAllocator stores RG+16 at 0x34900 after the call) *)
  (forall a, RGv <= a < RGv + 128 -> apresent (w_H Wx) m a) /\
  (* the region record's cells and the class max, unchanged (FGsN.R_RGF / R_PF) *)
  val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 8) 8 0 /\ val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 16) 8 nf /\
  val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 32) 8 au /\ val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 40) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 48) 8 mu /\ val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 56) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H Wx) m) (RGv + 68) 1 j64 /\ val_mem tfibsegs (mrestrict (w_H Wx) m) (Pr + 4) 4 maxc /\
  (* the two thread stats windows stay present (EnsureFreeArraySpace writes T+2872 / T+2880) *)
  (forall a, (ly_T ly + 2768 <= a < ly_T ly + 2800) \/ (ly_T ly + 2872 <= a < ly_T ly + 2888) -> apresent (w_H Wx) m a).
(* The write window of the growth arm: the walk's windows, the new free-array map, its shadow. *)
Definition XG (a : Z) : Prop := (WINR0 a \/ AFkn.RANGE fadr a) \/ W_FSH a.
(* The model after the grant, from the materialization [matN] at the ecall (node3's md2). *)
Definition mdG (matN : list word) : Model :=
  grant_md false AFkn.FL50 (w64 fadr) (w64 kUserMapSize) (with_vm_backing (m_vm_lazy md0) matN md0).

(* THE LEAF: EnsureFreeArraySpace has returned 1 to ReturnToAllocator (pc = ra, callee-saved registers, sp and tp
   kept, memory changed only in the write window), and the model has taken the matching arm. *)
Definition efa_leaf (S : astate) (r : bool * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  fst r = true /\
  ((4 * nfe <= mf /\ snd r = S /\ at_RET3 W 1 md0 WINR0 (fun m => PT m /\ (P_mf W mf m /\ P_lk W m)) W' c') \/
   (mf < 4 * nfe /\ snd r = upd_reg c (rgG (reg S c)) S /\
    exists (matN : list word) (W3 : world tfibsegs),
      wle W W3 /\ w_A W3 = (shf, shf + 32768) :: (fadr, fadr + kUserMapSize) :: w_A W /\ hsub (w_H W3) (w_H W) /\
      (forall a : word, w_H W a = false -> w_H W3 a = false) /\
      (forall a : word, ~ AFkn.RANGE fadr (bv_unsigned a) -> ~ AFkn.SHR shf (bv_unsigned a) -> w_H W3 a = w_H W a) /\
      A_bytes (w_A W3) = A_bytes (w_A W) + kUserMapSize + 32768 /\
      AI tfibsegs (w_H W3) (w_A W3) (mdG matN) /\ amwf (mdG matN) /\ same_io md0 (mdG matN) /\
      eager_used (mdG matN) <= eager_used md0 + kUserMapSize /\
      at_RET3 W3 1 (mdG matN) XG (fun m => FGwN.P_fshF shf (AFkn.P_grant W3 fadr shf PT) m /\ (P_mf W3 mf2 m /\ P_lk W3 m)) W' c')).

Lemma P_mf_at : forall (Wx : world tfibsegs) ss (E' : env) ms (k : nat) v cs (j : nat),
  env_agree aHAV3 E0 E' -> st_ok tfibsegs E' ss (restrict (w_H Wx) ms) ->
  nth_error (ss_mem ss) 36 = Some (YP09.mkRegion (Some rRG) 0 128 0 128 cs) ->
  nth_error cs j = Some (YP09.mkChunk 24 (CVal 8 (SOff k 0))) ->
  (k < aHAV3)%nat -> ew E0 k = w64 v -> 0 <= v < 2 ^ 64 ->
  P_mf Wx v (ms_mem ms).
Proof.
  intros Wx ss E' ms k v cs j HE HS Hnth Hj Hk Ek Hv. pose proof derived_rangesR as DR. pose proof high_factsR as HF.
  assert (B41 : base_val E' (Some rRG) = RGv).
  { cbn [base_val]. rewrite (proj1 HE rRG ltac:(unfold rRG, aHAV3; lia)). unfold rRG. rewrite EaRG. unfold w64.
    apply unsigned_lit_small. clear - DR HF. numconst. zlia. }
  unfold P_mf. rewrite <- B41. change 8%nat with (N.to_nat 8).
  exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat _ j 24 8 (SOff k 0) v HS Hnth Hj
    ltac:(rewrite AFk5.sv_denot_SOff0, (proj1 HE k Hk), Ek; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma P_lk_at : forall (Wx : world tfibsegs) ss (E' : env) ms r36 r35 r33 r34 (j0 j80 j88 jp js jt j8 j16 j32 j40 j48 j56 j68 jmx : nat),
  env_agree aHAV3 E0 E' -> st_ok tfibsegs E' ss (restrict (w_H Wx) ms) ->
  nth_error (ss_mem ss) 36 = Some r36 -> YP09.r_base r36 = Some rRG ->
  YP09.r_wlo r36 = 0 -> YP09.r_whi r36 = 128 ->
  nth_error (YP09.r_chunks r36) j0 = Some (YP09.mkChunk 0 (CVal 8 (SLit LOCKV))) ->
  nth_error (YP09.r_chunks r36) j80 = Some (YP09.mkChunk 80 (CVal 8 (SOff rJNA 0))) ->
  nth_error (YP09.r_chunks r36) j88 = Some (YP09.mkChunk 88 (CVal 8 (SOff rJNF 0))) ->
  nth_error (ss_mem ss) 35 = Some r35 -> YP09.r_base r35 = Some rP ->
  nth_error (YP09.r_chunks r35) jp = Some (YP09.mkChunk 0 (CVal 4 (SOff rN 0))) ->
  nth_error (YP09.r_chunks r35) js = Some (YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))) ->
  nth_error (ss_mem ss) 33 = Some r33 -> YP09.r_base r33 = Some rT ->
  nth_error (YP09.r_chunks r33) jt = Some (YP09.mkChunk 2784 (CVal 8 (SOff rJSM 0))) ->
  nth_error (YP09.r_chunks r36) j8 = Some (YP09.mkChunk 8 (CVal 8 (SLit 0))) ->
  nth_error (YP09.r_chunks r36) j16 = Some (YP09.mkChunk 16 (CVal 8 (SOff rNF 0))) ->
  nth_error (YP09.r_chunks r36) j32 = Some (YP09.mkChunk 32 (CVal 8 (SOff rAU 0))) ->
  nth_error (YP09.r_chunks r36) j40 = Some (YP09.mkChunk 40 (CVal 8 (SLit 0))) ->
  nth_error (YP09.r_chunks r36) j48 = Some (YP09.mkChunk 48 (CVal 8 (SOff rMU 0))) ->
  nth_error (YP09.r_chunks r36) j56 = Some (YP09.mkChunk 56 (CVal 8 (SLit 0))) ->
  nth_error (YP09.r_chunks r36) j68 = Some (YP09.mkChunk 68 (CVal 1 (SOff rJ64 0))) ->
  nth_error (YP09.r_chunks r35) jmx = Some (YP09.mkChunk 4 (CVal 4 (SOff rMAX 0))) ->
  YP09.r_wlo r33 = 2768 -> YP09.r_whi r33 = 2800 ->
  nth_error (ss_mem ss) 34 = Some r34 -> YP09.r_base r34 = Some rT -> YP09.r_wlo r34 = 2872 -> YP09.r_whi r34 = 2888 ->
  P_lk Wx (ms_mem ms).
Proof.
  intros Wx ss E' ms r36 r35 r33 r34 j0 j80 j88 jp js jt j8 j16 j32 j40 j48 j56 j68 jmx HE HS H36 B36 W36lo W36hi C0 C80 C88 H35 B35 Cp Cs H33 B33 Ct
    C8 C16 C32 C40 C48 C56 C68 Cmx W33lo W33hi H34 B34 W34lo W34hi.
  pose proof derived_rangesR as DR. pose proof high_factsR as HF. pose proof class_facts as (CFm & _ & CFn & CFs & _).
  assert (BRG : base_val E' (YP09.r_base r36) = RGv).
  { rewrite B36. cbn [base_val]. rewrite (proj1 HE rRG ltac:(unfold rRG, aHAV3; lia)). unfold rRG. rewrite EaRG. unfold w64.
    apply unsigned_lit_small. clear - DR HF. numconst. zlia. }
  assert (BP : base_val E' (YP09.r_base r35) = Pr).
  { rewrite B35. cbn [base_val]. rewrite (proj1 HE rP ltac:(unfold rP, aHAV3; lia)). unfold rP. rewrite EaP. unfold w64.
    apply unsigned_lit_small. clear - DR HF. numconst. zlia. }
  assert (BT : base_val E' (YP09.r_base r33) = ly_T ly).
  { rewrite B33. cbn [base_val]. rewrite (proj1 HE rT ltac:(unfold rT, aHAV3; lia)). unfold rT. rewrite EaT. unfold w64.
    apply unsigned_lit_small. clear - DR HF. numconst. zlia. }
  assert (BT4 : base_val E' (YP09.r_base r34) = ly_T ly).
  { rewrite B34. cbn [base_val]. rewrite (proj1 HE rT ltac:(unfold rT, aHAV3; lia)). unfold rT. rewrite EaT. unfold w64.
    apply unsigned_lit_small. clear - DR HF. numconst. zlia. }
  assert (DA : forall k v, (k < aHAV3)%nat -> ew E0 k = w64 v -> sv_denot E' (SOff k 0) = Z_to_bv 64 v).
  { intros k v Hk Ek. rewrite AFk5.sv_denot_SOff0, (proj1 HE k Hk), Ek. reflexivity. }
  pose proof Hnf as [NF0 NF1]. pose proof Hmu as (MU0 & MU1 & _). pose proof Hmf as [[MF0 MF1] _].
  unfold P_lk. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|]]]]]]]]]]]]]]].
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j0 0 8 (SLit LOCKV) LOCKV HS H36 C0 ltac:(reflexivity) ltac:(unfold LOCKV; cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j80 80 8 _ jna HS H36 C80 (DA rJNA jna ltac:(unfold rJNA, aHAV3; lia) eq_refl) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j88 88 8 _ jnf HS H36 C88 (DA rJNF jnf ltac:(unfold rJNF, aHAV3; lia) eq_refl) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BP. change 4%nat with (N.to_nat 4).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 35%nat r35 jp 0 4 _ n HS H35 Cp (DA rN n ltac:(unfold rN, aHAV3; lia) eq_refl) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BP. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 35%nat r35 js 8 8 _ csz HS H35 Cs (DA rCSZ csz ltac:(unfold rCSZ, aHAV3; lia) eq_refl) ltac:(cbn; unfold kMaxSize in *; lia) ltac:(cbn; lia)).
  - rewrite <- BT. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 33%nat r33 jt 2784 8 _ jsm HS H33 Ct (DA rJSM jsm ltac:(unfold rJSM, aHAV3; lia) eq_refl) ltac:(cbn; lia) ltac:(cbn; lia)).
  - intros a Ha. eapply (st_ok_window_apresent_off (w_H Wx) E' ss ms 36%nat r36 a HS H36);
      [ rewrite BRG; rewrite W36lo, W36hi; lia | ].
    apply off_img_high. clear - Ha DR HF. numconst. zlia.
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j8 8 8 (SLit 0) 0 HS H36 C8 ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j16 16 8 _ nf HS H36 C16 (DA rNF nf ltac:(unfold rNF, aHAV3; lia) eq_refl) ltac:(cbn; unfold kFreeArrayMax in *; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j32 32 8 _ au HS H36 C32 (DA rAU au ltac:(unfold rAU, aHAV3; lia) eq_refl) ltac:(cbn; unfold kFreeArrayOffset in *; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j40 40 8 (SLit 0) 0 HS H36 C40 ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j48 48 8 _ mu HS H36 C48 (DA rMU mu ltac:(unfold rMU, aHAV3; lia) eq_refl) ltac:(cbn; unfold kFreeArrayOffset in *; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 8%nat with (N.to_nat 8).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j56 56 8 (SLit 0) 0 HS H36 C56 ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BRG. change 1%nat with (N.to_nat 1). pose proof Hk68 as [J68 _].
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 36%nat r36 j68 68 1 _ j64 HS H36 C68 (DA rJ64 j64 ltac:(unfold rJ64, aHAV3; lia) eq_refl) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite <- BP. change 4%nat with (N.to_nat 4).
    exact (st_ok_chunk_val (w_H Wx) E' ss ms 35%nat r35 jmx 4 4 _ maxc HS H35 Cmx (DA rMAX maxc ltac:(unfold rMAX, aHAV3; lia) eq_refl) ltac:(cbn; clear - CFm; lia) ltac:(cbn; lia)).
  - intros a [Ha|Ha].
    + eapply (st_ok_window_apresent_off (w_H Wx) E' ss ms 33%nat r33 a HS H33); [ rewrite BT; rewrite W33lo, W33hi; lia | ].
      apply off_T. unfold kThreadObjSize. lia.
    + eapply (st_ok_window_apresent_off (w_H Wx) E' ss ms 34%nat r34 a HS H34); [ rewrite BT4; rewrite W34lo, W34hi; lia | ].
      apply off_T. unfold kThreadObjSize. lia.
Qed.

(* N: the regions and chunk positions the leaf reads, computed (the grant's store re-orders a chunk list). *)
Definition chunk_pos (cs : list YP09.chunk) (off : Z) : nat :=
  (fix go (l : list YP09.chunk) (i : nat) := match l with [] => 0%nat | ch :: t => if YP09.c_off ch =? off then i else go t (S i) end) cs 0%nat.
Definition rgi (ss : sstate) (i : nat) : YP09.region :=
  match nth_error (ss_mem ss) i with Some r => r | None => YP09.mkRegion None 0 0 0 0 [] end.
Definition R36_RN : YP09.region := Eval vm_compute in rgi F_RN 36.
Definition R35_RN : YP09.region := Eval vm_compute in rgi F_RN 35.
Definition R33_RN : YP09.region := Eval vm_compute in rgi F_RN 33.
Definition R34_RN : YP09.region := Eval vm_compute in rgi F_RN 34.
Definition R36_RG : YP09.region := Eval vm_compute in rgi F_RG 36.
Definition R35_RG : YP09.region := Eval vm_compute in rgi F_RG 35.
Definition R33_RG : YP09.region := Eval vm_compute in rgi F_RG 33.
Definition R34_RG : YP09.region := Eval vm_compute in rgi F_RG 34.
Definition CS_RN : list YP09.chunk := Eval vm_compute in YP09.r_chunks R36_RN.
Definition CS_RG : list YP09.chunk := Eval vm_compute in YP09.r_chunks R36_RG.
Definition IJ24 : nat := Eval vm_compute in chunk_pos CS_RG 24.
Definition IJ24n : nat := Eval vm_compute in chunk_pos CS_RN 24.

Lemma seedF : forall mat,
  at_R3 W md0 WINR0 PT SSF W (mkCfg (mkst regs0 (w64 A_EFA) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)).
Proof.
  intros mat. split; [reflexivity|]. exists (mkst regs0 (w64 A_EFA) mem0 (seg_rom tfibsegs)), mat, E0. split; [reflexivity|].
  split; [split; [intros; reflexivity | reflexivity]|]. split; [exact SEED|]. split; [intros; reflexivity|].
  split; [exact Hpres0R | exact I].
Qed.

Lemma pstable_PT : pstable PT. Proof. intros m m' _ _. exact I. Qed.

(* THE CONTRACT at the image level: the call of EnsureFreeArraySpace, followed by any continuation [k] of the caller
   (ReturnToAllocator's rest), is realized when the continuation is realized from the leaf. *)
Theorem efa_call : forall (S : astate) (k : bool -> M unit) (Q : unit * astate -> world tfibsegs -> config -> Prop),
  rg_mapped_fa (reg S c) = mf ->
  4 * nfe <= mf + kFreeArrayMapSize ->
  (mf < 4 * nfe ->
     mf + kFreeArrayMapSize <= kFreeArrayMax /\
     region_free (vm_reserved (m_vmmaps md0)) (w64 fadr) (w64 kUserMapSize) = true /\
     map_contains (vm_maps (m_vmmaps md0)) (w64 fadr) (w64 kUserMapSize) = true /\
     amwf md0 /\ YM05.ceil_of_top (alloc_top (m_vmmaps md0)) /\
     eager_used md0 + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md0) /\
     (forall a, AFkn.SHR shf a -> mem0 (w64 a) <> None)) ->
  (forall r W' c', efa_leaf S r W' c' -> amreal tfibsegs (k (fst r) (snd r)) W' c' Q) ->
  amreal tfibsegs (bind (ensure_free_array c nfe true) k S) W (cfg_at tfibsegs A_EFA regs0 mem0 md0) Q.
Proof.
  intros S k Q Hmfe Hone Hgrow Hk.
  pose proof derived_rangesR as DR. pose proof high_factsR as HF. pose proof Hmf as [[M0 M1] M2].
  pose proof factsF as (G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32 & G33).
  set (mat0 := m_vm_materialized md0).
  assert (HC0 : cfg_at tfibsegs A_EFA regs0 mem0 md0 =
    mkCfg (mkst regs0 (w64 A_EFA) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
    by (unfold cfg_at; subst mat0; rewrite with_vm_backing_id; reflexivity).
  rewrite HC0. pose proof (seedF mat0) as HR0.
  assert (WX : forall a, WINR0 a -> WINR0 a) by (intros a Ha; exact Ha).
  destruct (Z_le_gt_dec (4 * nfe) mf) as [Hle | Hgt0]; [| assert (Hgt : mf < 4 * nfe) by lia; clear Hgt0].
  - (* no growth *)
    unfold bind. cbv beta. rewrite (E_efaT_e S c nfe ltac:(rewrite Hmfe; exact Hle)). cbn [ibind].
    apply (amreal_SRr_pre tfibsegs _ W _ Q (at_RET3 W 1 md0 WINR0 (fun m => PT m /\ (P_mf W mf m /\ P_lk W m)))).
    + eapply SRr_bind; [exact (segA Hle W md0 WINR0 PT W _ WX pstable_PT HR0)|].
      intros W1 c1 _ HR1.
      apply (at_R3_facts W md0 WINR0 PT (fun m => P_mf W mf m /\ P_lk W m) F_RN W1 c1) in HR1;
        [| intros E' ms HE HS; exact (conj (P_mf_at W F_RN E' ms rMF mf CS_RN IJ24n HE HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(unfold rMF, aHAV3; lia) EaMF ltac:(clear - M0 M1; unfold kFreeArrayMax in *; lia))
             (P_lk_at W F_RN E' ms R36_RN R35_RN R33_RN R34_RN (chunk_pos (YP09.r_chunks R36_RN) 0) (chunk_pos (YP09.r_chunks R36_RN) 80) (chunk_pos (YP09.r_chunks R36_RN) 88) (chunk_pos (YP09.r_chunks R35_RN) 0) (chunk_pos (YP09.r_chunks R35_RN) 8) (chunk_pos (YP09.r_chunks R33_RN) 2784) (chunk_pos (YP09.r_chunks R36_RN) 8) (chunk_pos (YP09.r_chunks R36_RN) 16) (chunk_pos (YP09.r_chunks R36_RN) 32) (chunk_pos (YP09.r_chunks R36_RN) 40) (chunk_pos (YP09.r_chunks R36_RN) 48) (chunk_pos (YP09.r_chunks R36_RN) 56) (chunk_pos (YP09.r_chunks R36_RN) 68) (chunk_pos (YP09.r_chunks R35_RN) 4) HE HS
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)))].
      destruct FGwN.RN_facts as (R1 & R2 & R3 & R4 & R5 & R6).
      exact (retF W md0 WINR0 _ F_RN W1 c1 1 HR1 R1 R2 R3 R4 R5 R6).
    + intros W' c' _ HRET. apply (Hk (true, S) W' c'). split; [reflexivity|]. left.
      split; [exact Hle|]. split; [reflexivity | exact HRET].
  - (* growth: one KMapFreeArray request *)
    destruct (Hgrow Hgt) as (Hmax2 & PLr & PLm & MW0 & TOP0 & SL0 & SH0).
    destruct (E_efaT_g S c nfe mf Hmfe M2 M0 Hgt Hone Hmax2) as (K & EK & K1 & _).
    unfold bind. cbv beta. rewrite EK. cbn [ibind amreal].
    eapply SRr_mono; [exact (AFkn.SRr_with_AI _ _ _ (segB Hgt Hone Hmax2 W md0 WINR0 PT W _ WX pstable_PT HR0))|].
    intros W4 c4 _ [HAI HN]. pose proof (proj1 HN) as EW4. subst W4.
    pose proof FGwN.FN_facts as (Fpc & F17 & F10 & Fea & F11 & F12 & F13 & F14 & F15 & Fnc & Fhd & Fsk & Fres).
    destruct HN as (HNw & msN & matN & EN & EcN & HNrest). subst c4.
    assert (RNG : forall a, AFkn.RANGE fadr a -> 0 <= a < 2 ^ 64 /\ FAv <= a < FAv + 2 ^ 29).
    { intros a Ha. unfold AFkn.RANGE in Ha. clear - Ha G24 G32 Hmax2 M0 DR HF. numconst. zlia. }
    assert (SNG : forall a, AFkn.SHR shf a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg).
    { intros a Ha. unfold AFkn.SHR in Ha. clear - Ha G29 G30. numconst. zlia. }
    lazymatch goal with |- context [ibind (K _) ?g] =>
    eapply (node3 (KMapFreeArray c mf kFreeArrayMapSize) S (fun z => ibind (K z) g) Q W md0 WINR0 PT F_N _ (SOff rFADR 0) fadr shf false FGwN.cs_FN
      (conj HNw (ex_intro _ msN (ex_intro _ matN (ex_intro _ EN (conj eq_refl HNrest))))) HAI Fpc F17 F10 Fea U_fadrF F11 F12 F13 F14 F15 Fnc Fhd Fsk)
    end.
    + exact G25.
    + clear - G24 DR M0. numconst. zlia.
    + clear - G24 Hmax2 DR M0. numconst. zlia.
    + exact G27.
    + exact G28.
    + unfold kHighShadowBeg. clear - G29. zlia.
    + unfold kHighShadowEnd. clear - G30. zlia.
    + cbn [cfg_model]. rewrite m_vmmaps_wvb. split; [exact PLr | exact PLm].
    + cbn [cfg_model]. exact (amwf_same md0 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW0).
    + cbn [cfg_model]. rewrite m_vmmaps_wvb. exact TOP0.
    + cbn [cfg_model]. rewrite m_vmmaps_wvb, eager_used_wvb. exact SL0.
    + reflexivity.
    + intros z Hz. exact Hz.
    + intros m m' _ _. exact I.
    + intros a Ha. apply band_not. exact (proj2 (SNG a Ha)).
    + exact SH0.
    + reflexivity.
    + intros W3 c' md2 LE3 A3 SUB3 MON3 AI3 MW3 IO3 EG3 HEQ3 AB3 HR.
      cbv beta. rewrite K1. cbn [ibind].
      set (X3 := fun a => WINR0 a \/ AFkn.RANGE fadr a) in *.
      assert (HX3 : forall a, WINR0 a -> X3 a) by (intros a Ha; left; exact Ha).
      set (P3 := AFkn.P_grant W3 fadr shf PT) in *.
      assert (PS3 : pstable P3).
      { intros m m' Hfr (HP & HG1 & HG2). split; [exact I|]. split.
        - intros a Ha. destruct (RNG a Ha) as [Ra Fa].
          assert (E : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (apply Hfr; rewrite unsigned_lit_small by exact Ra; apply fa_not; exact Fa).
          destruct (HG1 a Ha) as [HPa HZa]. split; [eapply apresent_same; [exact E | exact HPa] | unfold w64 in *; rewrite E; exact HZa].
        - intros a Ha. destruct (SNG a Ha) as [Ra Ba]. eapply apresent_same; [|exact (HG2 a Ha)].
          apply Hfr. rewrite unsigned_lit_small by exact Ra. apply band_not. exact Ba. }
      rewrite Fres in HR.
      apply (amreal_SRr_pre tfibsegs _ W3 _ Q
        (at_RET3 W3 1 md2 XG (fun m => FGwN.P_fshF shf (AFkn.P_grant W3 fadr shf PT) m /\ (P_mf W3 mf2 m /\ P_lk W3 m)))).
      * eapply SRr_bind; [exact (segC W3 md2 X3 P3 W3 c' HX3 PS3 HR)|]. intros W6 c6 _ HR6.
        eapply SRr_bind.
        { apply (segD W3 md2 X3 P3 W6 c6 HX3 PS3); [| | exact HR6].
          - intros m (_ & _ & HG2) a Ha. apply HG2. unfold AFkn.SHR. unfold AFk5.W_FSH in Ha.
            change (kFreeArrayMapSize / 8) with 32768 in Ha. exact Ha.
          - intros m m' Hfr Hpr (HP & HG1 & HG2). split; [exact I|]. split.
            + intros a Ha. destruct (RNG a Ha) as [Ra Fa].
              assert (E : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
              { apply Hfr. rewrite unsigned_lit_small by exact Ra. intros Hw. unfold AFk5.W_FSH in Hw.
                change (kFreeArrayMapSize / 8) with 32768 in Hw. unfold AFkn.RANGE in Ha. clear - Ha Hw G30 G31. numconst. zlia. }
              destruct (HG1 a Ha) as [HPa HZa]. split; [eapply apresent_same; [exact E | exact HPa] | unfold w64 in *; rewrite E; exact HZa].
            + intros a Ha. apply Hpr. exact (HG2 a Ha). }
        intros W7 c7 _ HR7.
        apply (at_R3_facts W3 md2 _ _ (fun m => P_mf W3 mf2 m /\ P_lk W3 m) F_RG W7 c7) in HR7;
          [| intros E' ms HE HS; exact (conj (P_mf_at W3 F_RG E' ms rMF2 mf2 CS_RG IJ24 HE HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(unfold rMF2, aHAV3; lia) EaMF2 ltac:(clear - G33 M0 Hmax2; unfold kFreeArrayMax, kFreeArrayMapSize in *; lia))
               (P_lk_at W3 F_RG E' ms R36_RG R35_RG R33_RG R34_RG (chunk_pos (YP09.r_chunks R36_RG) 0) (chunk_pos (YP09.r_chunks R36_RG) 80) (chunk_pos (YP09.r_chunks R36_RG) 88) (chunk_pos (YP09.r_chunks R35_RG) 0) (chunk_pos (YP09.r_chunks R35_RG) 8) (chunk_pos (YP09.r_chunks R33_RG) 2784) (chunk_pos (YP09.r_chunks R36_RG) 8) (chunk_pos (YP09.r_chunks R36_RG) 16) (chunk_pos (YP09.r_chunks R36_RG) 32) (chunk_pos (YP09.r_chunks R36_RG) 40) (chunk_pos (YP09.r_chunks R36_RG) 48) (chunk_pos (YP09.r_chunks R36_RG) 56) (chunk_pos (YP09.r_chunks R36_RG) 68) (chunk_pos (YP09.r_chunks R35_RG) 4) HE HS
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)))].
        destruct FGwN.RG_facts as (R1 & R2 & R3 & R4 & R5 & R6).
        exact (retF W3 md2 _ _ F_RG W7 c7 1 HR7 R1 R2 R3 R4 R5 R6).
      * intros W' c'' _ HRET. apply (Hk (true, upd_reg c (rgG (reg S c)) S) W' c''). split; [reflexivity|]. right.
        split; [exact Hgt|]. split; [reflexivity|]. exists matN, W3.
        cbn [cfg_model] in EG3. rewrite eager_used_wvb in EG3.
        split; [exact LE3|]. split; [exact A3|]. split; [exact SUB3|]. split; [exact MON3|]. split; [exact HEQ3|].
        split; [exact AB3|]. split; [exact AI3|]. split; [exact MW3|]. split; [exact IO3|]. split; [exact EG3|].
        exact HRET.
    + cbn [cfg_model]. repeat split; reflexivity.
Qed.
End f.
End d.

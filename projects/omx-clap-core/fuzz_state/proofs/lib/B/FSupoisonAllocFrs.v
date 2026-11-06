(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Reusable/YFf7.v, with its module paths changed; 372 of its 459 lines of code are new or changed and 44 lines of the source are left out. *)
(* Free's recycle_chunk of a secondary chunk (lib/A/AFg9.v, over lib/A/AFg8.v, AFf6.v, AFf7.v) for any U, lane rs: tfib_rchunk_secU, the U form of lib/A/AFfs.v tfib_rchunk_sec_spec. The runs are the donor's, on the real memory; the facts, seeds and the leaf are the donor's, on FSupoison.unpoison UP mem. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFrs.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt; the pcs are by name: PC_GBB_L0, PC_MUNMAP_ECALL, PC_MUNMAP_RET. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFeq YFex YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj YFfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb YFgx YFfd YFgv YFg8 YFfc YFf6 YFfe YFf7 YFf8 YFf9 YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocFK FSupoisonAllocFrsR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* The pcs inside a function, by name: the entry is lib/B/YFeu.v / lib/B/YFew.v A_xxx or the lib/B/YB1w.v row, the offset is the B donor's pc minus that entry. *)
(* the GetBlockBegin scan loop head (lib/B/YFf6.v:126, L0_STL's pc). *)
Definition PC_GBB_L0 : Z := tfib_A__ZNK11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE13GetBlockBeginEPKv + 0x6c.
(* the ecall of __sanitizer::internal_munmap, "li a7, 215; ecall; ret" (lib/B/YFg8.v:352). *)
Definition PC_MUNMAP_ECALL : Z := tfib_A__ZN11__sanitizer15internal_munmapEPvm + 4.
(* the ret of __sanitizer::internal_munmap (lib/B/YFgv.v:376, lib/B/YFf8.v:464). *)
Definition PC_MUNMAP_RET : Z := tfib_A__ZN11__sanitizer15internal_munmapEPvm + 8.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFK.
Module FRR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFrsR.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, YFgu.GFRAME, YFgx.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (UP : list (Z * Z)) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PREU : FK.rcc_preU B ly X k cbp UP W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Local Notation sp0 := (bv_unsigned (YK11.getr regs 2)).
Local Notation mu := (FSP.unpoison UP mem).
Local Notation T := (ly_T ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation nA := (YFg8.nA X).
Local Notation idx := (YFg8.idx i).
Local Notation qi := (YFg8.qi ly i).
Local Notation lst := (YFg8.lst ly X r).
Local Notation own := (YFg8.own X i).
Local Notation ql := (YFf9.ql ly X).
Local Notation hdr := (YFfc.hdr B ly k).
Local Notation HWv := (YFfc.HWv B ly k W mu).
Local Notation j1 := (YFfc.j1 ly W mu).
Local Notation j2 := (YFfc.j2 ly W mu).
Local Notation ji1 := (YFfc.ji1 W mu).
Local Notation ji2 := (YFfc.ji2 W mu).
Local Notation ji3 := (YFfc.ji3 W mu).
Local Notation ji4 := (YFfc.ji4 W mu).
Local Notation j5 := (YFfc.j5 ly W mu).
Local Notation j6 := (YFfc.j6 ly W mu).
Local Notation vra := (YFf6.v regs 1%bv).
Local Notation vs0 := (YFf6.v regs 8%bv).
Local Notation vs1 := (YFf6.v regs 9%bv).
Local Notation vs2 := (YFf6.v regs 18%bv).
Local Notation vs3 := (YFf6.v regs 19%bv).
Local Notation vs4 := (YFf6.v regs 20%bv).
Local Notation W2 := (wrefund tfibsegs W (YFg8.MAP ly r, YFg8.MAP ly r + YFg8.LEN sm)).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The donor pre at mu, ARU, and where U is not.                                                                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma PRE_u : rcc_pre B ly X k cbp W regs mu md. Proof. exact (proj1 PREU). Qed.
Lemma M_u : ARm B ly X (aview tfibsegs (w_H W) mu). Proof. exact (proj1 (proj1 PRE_u)). Qed.
Lemma Hk_u : In k (st_chunks X). Proof. exact (proj1 (proj2 (proj2 PRE_u))). Qed.
Lemma Hst_u : ck_state k = CQuarantined. Proof. exact (proj1 (proj2 (proj2 (proj2 PRE_u)))). Qed.
Lemma ARU0 : FSP.ARU tfibsegs B ly X UP W mem md.
Proof. destruct PREU as (P & OK & PO). exact (conj (proj1 P) (conj OK PO)). Qed.
Lemma OFFa : forall a, FRR.appb a -> FAR.offU UP a.
Proof. intros a Ha. exact (FRR.offU_appb B ly X UP W mem md a ARU0 Ha). Qed.
Lemma Z3app : forall x sz a, zone3 x sz -> x <= a < x + sz -> FRR.appb a.
Proof. intros x sz a Z Ha. unfold FRR.appb. clear - Z Ha. numconst. lia. Qed.

(* The chunk being recycled is quarantined: no live block meets its mapping. *)
Lemma map_nonlive : forall g, MAP <= g < MAP + LEN -> forall p n, In (p, n) (ablocks B ly X) -> ~ (p <= g < p + req_size n).
Proof.
intros g Hg p n Hbl Hin.
destruct (FRR.ablocks_alloc B ly X p n Hbl) as (y & Hy & Hay & Hp & Hn).
pose proof (chunk_facts B ly X _ y M_u Hy) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
assert (Hne : ck_beg y <> ck_beg k).
{ destruct (YFf4.SPLIT B ly X _ M_u k Hk_u) as (l1 & l2 & E1 & E2 & N1 & N2). intros Eb.
  rewrite E1 in Hy. apply in_app_iff in Hy as [Hy|[Hy|Hy]].
  - apply N1. rewrite <- Eb. apply in_map. exact Hy.
  - subst y. unfold is_alloc in Hay. rewrite Hst_u in Hay. cbn in Hay. discriminate.
  - apply N2. rewrite <- Eb. apply in_map. exact Hy. }
pose proof (YFf4.ext_off_map B ly X _ M_u k r o sm Hk_u Hb Hsm y Hy Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
pose proof (YFfc.ELEN B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as (E & _).
unfold YFf4.MAP, YFf4.LEN in DJ. rewrite <- E in DJ. unfold YFg8.MAP, YFg8.LEN in *.
subst p n. rewrite C4 in Hin. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The region condition: every byte whose value or presence moves between mem and mu, and the run's write window. *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Definition rchunk_sec_fixed (a : Z) : Prop := FRR.appb a \/ (YFgv.SHAv MAP <= a < YFgv.SHAv MAP + YFgv.CNTv LEN).
Lemma rchunk_sec_regions_off_ush : forall a, rchunk_sec_fixed a -> FAR.offU UP a.
Proof.
intros a [Ha|Ha]; [exact (OFFa a Ha)|].
pose proof (YFfc.GEOM B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as (M1 & M2 & M3 & M4 & M5 & _).
assert (Ht : 0 <= a - YFgv.SHAv MAP < LEN / 8) by (unfold YFgv.CNTv in Ha; lia).
assert (ESA : shadow_addr (MAP + 8 * (a - YFgv.SHAv MAP)) = a).
{ unfold shadow_addr, YFgv.SHAv. apply Z.mod_divide in M3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia.
  rewrite Z_div_mult by lia.
  replace (q * 512 * 8 + 8 * (a - (SHADOW_OFF + q * 512))) with ((q * 512 + (a - (SHADOW_OFF + q * 512))) * 8) by lia.
  rewrite Z_div_mult by lia. lia. }
pose proof (Z.mul_div_le LEN 8 ltac:(lia)) as DL.
rewrite <- ESA. apply (FAR.offU_shadow_nonlive B ly X UP W mem md _ ARU0).
- clear - M1 M2 Ht DL. numconst. lia.
- apply map_nonlive. lia.
Qed.
Lemma OFFS : forall a, YFgv.SHAv MAP <= a < YFgv.SHAv MAP + YFgv.CNTv LEN -> FAR.offU UP a.
Proof. intros a Ha. apply rchunk_sec_regions_off_ush. right. exact Ha. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Run posts moved to mu, for the donor seeds (lib/B/YFfe.v XSEED, lib/B/YFf9.v DSEED) and leaf (YFg8.v FIN).     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma STX_u : forall regsX memX, YFf6.STX B ly X k cbp W regs mem r regsX memX -> YFf6.STX B ly X k cbp W regs mu r regsX (FSP.unpoison UP memX).
Proof.
intros regsX memX (regsL & PX & SR & R13). exists regsL. split; [|exact (conj SR R13)].
destruct PX as (SRL & L2 & L1r & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & MQA & PRS & V1 & V8 & V9 & V18 & V19 & V20 & V56 & V10 & V72 & V80 & VM).
pose proof (YFfc.HSP B ly X k cbp W regs mu md PRE_u) as [S1 S2].
pose proof (YFfc.HI B TB ly X k cbp W regs mu md PRE_u) as (_ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _).
assert (VS : forall a v, sp0 - 80 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict (w_H W) memX) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP memX)) a 8 v).
{ intros a v H1 H2 V. apply (FRR.vm_unp UP OFFa); [|exact V]. intros b Hq. right. clear - Hq H1 H2 S1 S2 hS1 hS2. numconst. lia. }
unfold YFf6.PREX.
refine (conj SRL (conj L2 (conj L1r (conj L8 (conj L9 (conj L10 (conj L11 (conj L12 (conj L13 (conj L14 (conj L19 (conj L20 _)))))))))))).
split. { intros x Hx. apply FRR.unpoison_eq. exact (MQA x Hx). }
split. { intros a Ha. apply FAR.apresent_to_unpoison. exact (PRS a Ha). }
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); try (apply VS; [lia | lia | assumption]).
apply (FRR.vm_unp UP OFFa); [intros b Hq; left; clear - Hq; numconst; lia | exact VM].
Qed.
Lemma PRED_u : forall regsD memD, YFf7.PRED ly W regs mem r regsD memD -> YFf7.PRED ly W regs mu r regsD (FSP.unpoison UP memD).
Proof.
intros regsD memD (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
refine (conj DSR (conj D2 (conj D1 (conj D8 (conj D9 (conj D18 (conj D10 (conj D11 (conj D12 (conj _ (conj _ (conj _ _)))))))))))).
- intros x Hx. apply FRR.unpoison_eq. exact (MQD x Hx).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (DPRS a Ha).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (DTJ a Ha).
- apply (FRR.vm_unp UP OFFa); [intros b Hq; left; clear - Hq; numconst; lia | exact DMUT].
Qed.
Lemma LINKD_u : forall regsD memD, YFg8.LINKD ly W regs mem regsD memD -> YFg8.LINKD ly W regs mu regsD (FSP.unpoison UP memD).
Proof.
intros regsD memD (L2 & LS & LM & LP). refine (conj L2 (conj LS (conj _ _))).
- intros x Hx. apply FRR.unpoison_eq. exact (LM x Hx).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (LP a Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The walk to the munmap call (lib/B/YFf6.v L0_STL / to_XG, lib/B/YFf7.v to_LMD, lib/B/YFg9.v WALK) on the real   *)
(*    memory: the donor text, with each seed taken at mu and its record moved to mem (FSupoisonAllocFrsR).          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma L0_STL_U : forall W' c', YFgu.at_L0 W regs mem md hdr nA Q W' c' ->
W' = W /\ exists regsL memL matL, c' = mkCfg (YK11.mkst regsL (w64 PC_GBB_L0) memL (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) matL md) /\
YFfb.stL W hdr (YFf6.lim ly X) Q 0 (YFf6.hs ly X) regsL memL /\ YFf6.PREX B ly X k cbp W regs mem regsL memL.
Proof.
intros W' c' HL. destruct HL as (-> & regsL & memL & matL & -> & SR & R2 & R1 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R19 & R20 & MQ & PRS & VALS).
pose proof (YFfc.HI B TB ly X k cbp W regs mu md PRE_u) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & _).
pose proof (YFfc.HSP B ly X k cbp W regs mu md PRE_u) as [S1 S2].
pose proof (YFfc.ARRF B ly X k cbp W regs mu md r i PRE_u Hi) as (A1 & A2 & A3 & A4 & A5).
pose proof (YFfc.hdr_facts B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as (D1 & D2 & D3 & _).
pose proof (YFfc.GEOM B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as (M1 & M2 & M3 & M4 & _).
pose proof (YFf6.hs_facts B ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi) as (L1 & L2 & L3 & L4 & L5).
pose proof (YFf6.CBP B TB ly X k cbp W regs mu md PRE_u) as (C10 & _).
assert (MQA : YFf6.MEQA regs mem memL).
{ intros x Hx. apply MQ. unfold YFgu.WIN. unfold YFf6.WINA in Hx. numconst. exact Hx. }
split; [reflexivity|]. exists regsL, memL, matL. split; [reflexivity|]. split.
-
unfold YFfb.stL. splits; try assumption.
+ clear - hQ1. unfold zone3 in hQ1. lia.
+ clear - hQAL. apply Z.mod_divide in hQAL as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 512). lia.
+ rewrite L1. unfold YFf6.lim, YFg8.nA. lia.
+ lia.
+ clear - D1 M1. numconst. lia.
+ intros j h Hj. destruct (L5 j h Hj) as (rj & Hrj & ->).
destruct (YFfc.slot_val B TB ly X k cbp W regs mu md r i PRE_u Hi j rj Hrj) as [SV SP].
destruct (YFfc.slot_geom B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm j rj Hrj) as (y & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof (nth_error_lt _ _ _ Hrj) as JL.
assert (OUT : forall a, Q + 8 * Z.of_nat j <= a < Q + 8 * Z.of_nat j + 8 -> ~ YFf6.WINA regs a /\ 0 <= a < 2 ^ 64 /\ FRR.appb a).
{ intros a Ha. unfold YFf6.WINA. unfold YFg8.nA in A4. split; [|split].
  - clear - Ha hQ1 hQ2 hCE S1 JL A4. numconst. lia.
  - clear - Ha hQ1 hQ2 JL A4. numconst. lia.
  - apply (Z3app _ _ a hQ1). clear - Ha JL A4. unfold kPtrArrayResv. lia. }
assert (SV' : val_mem tfibsegs (mrestrict (w_H W) mem) (Q + 8 * Z.of_nat j) 8 (ly_sec ly rj)).
{ apply (FRR.vm_real UP OFFa); [intros b Hq; apply OUT; lia | exact SV]. }
splits.
* apply (val_mem_frame (w_H W) mem memL); [|exact SV']. intros kk Hkk. apply MQA. destruct (OUT (Q + 8 * Z.of_nat j + Z.of_nat kk) ltac:(lia)) as (O1 & O2 & _).
rewrite unsigned_lit_small by exact O2. exact O1.
* intros a Ha. destruct (OUT a Ha) as (O1 & O2 & O3).
apply (apresent_same (w_H W) mem); [apply MQA; rewrite unsigned_lit_small by exact O2; exact O1 | exact (FRR.ap_real UP OFFa _ _ a O3 (SP a Ha))].
* clear - G1. unfold zone3 in G1. lia.
* lia.
* exact G3.
-
unfold YFf6.PREX. cbv zeta in VALS. unfold YFf6.v.
destruct VALS as (V1 & V8 & V9 & V18 & V19 & V20 & V56 & V10 & V72 & V80 & VM).
unfold w64 in C10. pose proof (YFf6.CBP B TB ly X k cbp W regs mu md PRE_u) as (_ & _ & _ & _ & CR). rewrite C10 in V10. rewrite unsigned_lit_small in V10 by exact CR.
splits; first [assumption | exact V1 | exact V8 | exact V9 | exact V18 | exact V19 | exact V20 | exact V56 | exact V10 | exact V72 | exact V80 | exact VM].
Qed.
Theorem to_XG_U : forall mat, SRr tfibsegs W (mkCfg (YK11.mkst regs (w64 A_RChunk) mem (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
  (YFf6.ATX B ly X k cbp W regs mem md r).
Proof.
intros mat.
pose proof (FRR.fhA_real UP OFFa W ly regs mem _ _ _ (YFfc.FH_A B TB ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi)) as FHA.
eapply SRr_bind; [exact (YFf5.segGA W ly regs mem md hdr nA Q mat FHA)|].
intros W1 c1 _ HL0. destruct (L0_STL_U W1 c1 HL0) as (-> & regsL & memL & matL & -> & STL & PX).
pose proof (YFf6.hs_facts B ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi) as (L1 & L2 & _).
pose proof (YFfc.IMG B ly X k cbp W regs mu md PRE_u) as IMG.
pose proof (am_layout B ly X _ M_u) as LO.
eapply SRr_mono; [exact (YFfb.gloop W ly md hdr (YFf6.lim ly X) LO IMG (YFf6.HP B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm)
  (YFf6.HLIM B TB ly X k cbp W regs mu md r i PRE_u Hi) (YFf6.hs ly X) Q 0 regsL memL matL L2 STL)|].
intros W2' c2 _ HX. destruct HX as (-> & regsX & memX & matX & -> & SR & A12 & A13 & MQ).
split; [reflexivity|]. exists regsX, memX, matX. split; [reflexivity|].
assert (EM : memX = memL) by (apply functional_extensionality; exact MQ). rewrite EM.
exists regsL. split; [exact PX|]. split; [exact SR|]. rewrite A13, (YFf6.scan_is_MAP B ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi). reflexivity.
Qed.
Theorem to_LMD_U : forall mat, SRr tfibsegs W (mkCfg (YK11.mkst regs (w64 A_RChunk) mem (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
  (YFf7.ATD ly W regs mem md r).
Proof.
intros mat.
pose proof (YFfc.HI B TB ly X k cbp W regs mu md PRE_u) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _).
pose proof (YFfc.HSP B ly X k cbp W regs mu md PRE_u) as [S1 S2].
eapply SRr_bind; [exact (to_XG_U mat)|].
intros W1 c1 _ HX. destruct HX as (-> & regsX & memX & matX & -> & SX).
pose proof (YFfe.XSEED B TB ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi HTSD regsX _ (STX_u regsX memX SX)) as FHXu.
pose proof (FRR.fhX_real UP OFFa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FHXu) as FHX.
destruct SX as (regsL & PX & SR & R13).
destruct PX as (SRL & L2 & L1r & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & MQA & PRS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VM).
assert (X2 : YK11.getr regsX 2 = w64 (sp0 - 80)) by (rewrite (SR 2%bv ltac:(inS)); exact L2).
assert (USX : bv_unsigned (YK11.getr regsX 2) = sp0 - 80) by (rewrite X2; unfold w64; apply unsigned_lit_small; pose proof (u64_range (YK11.getr regs 2)); clear - S1 S2 hS1 hS2 H; numconst; lia).
eapply SRr_mono; [exact (YFfd.segGX W ly regsX memX md hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 matX FHX)|].
intros W2' c2 _ HD. destruct HD as (-> & regsD & memD & matD & -> & DSR & D2 & D1 & D8 & D9 & D18 & D19 & D20 & D10 & D11 & D12 & MQX & DPRS & DMUT & DJ1 & DJ2).
rewrite USX in D2, DPRS. unfold YFgx.MEQ, YFgx.WIN in MQX. rewrite USX in MQX.
split; [reflexivity|]. exists regsD, memD, matD. split; [reflexivity|].
unfold YFf7.PRED. splits.
- intros r' Hr'. unfold YFgv.SREGS in Hr'. cbn [In] in Hr'.
assert (CASE : r' = 19%bv \/ r' = 20%bv \/ In r' YFgx.SREGS).
{ unfold YFgx.SREGS. cbn [In]. clear - Hr'. intuition (subst; auto 20). }
destruct CASE as [-> | [-> | C]].
+ rewrite D19. unfold YFf6.v, w64. apply Z_to_bv_bv_unsigned.
+ rewrite D20. unfold YFf6.v, w64. apply Z_to_bv_bv_unsigned.
+ rewrite (DSR r' C). assert (C2 : In r' YFgw.SREGS /\ In r' YFgu.SREGS).
{ unfold YFgx.SREGS in C. unfold YFgw.SREGS, YFgu.SREGS. cbn [In] in C |- *. clear - C. intuition (subst; auto 40). }
destruct C2 as [C2 C3]. rewrite (SR r' C2). exact (SRL r' C3).
- rewrite D2. replace (sp0 - 80 + YFgx.GFRAME) with sp0 by (numconst; lia). unfold w64. apply Z_to_bv_bv_unsigned.
- exact D1.
- exact D8.
- exact D9.
- exact D18.
- exact D10.
- exact D11.
- exact D12.
- intros x Hx. unfold YFf7.WIND, YFf6.WINA in Hx. rewrite MQX by (clear - Hx; numconst; lia). apply MQA. unfold YFf6.WINA. clear - Hx. lia.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - 48)) as [LOW|HI'].
+ apply DPRS. lia.
+ apply (apresent_same (w_H W) memX); [|apply PRS; lia]. apply MQX. rewrite unsigned_lit_small by (clear - Ha S1 S2 hS1 hS2; numconst; lia).
clear - Ha HI' S1 S2 hS1 hCE hT1 hT2. numconst. lia.
- intros a Ha. assert (Ha' : off_img a) by (apply (zone3_off_img _ _ _ hT1); clear - Ha; unfold t_stats, kThreadObjSize in *; lia).
destruct (Z_lt_le_dec a (T + t_stats + 48)) as [LOW|HI'].
+ pose proof (DJ1 (Z.to_nat (a - (T + t_stats + 40))) ltac:(lia)) as Hb'. rewrite Z2Nat.id in Hb' by lia. replace (T + t_stats + 40 + (a - (T + t_stats + 40))) with a in Hb' by lia.
exact (mbyte_off_apresent (w_H W) memD a _ Ha' Hb').
+ pose proof (DJ2 (Z.to_nat (a - (T + t_stats + 48))) ltac:(lia)) as Hb'. rewrite Z2Nat.id in Hb' by lia. replace (T + t_stats + 48 + (a - (T + t_stats + 48))) with a in Hb' by lia.
exact (mbyte_off_apresent (w_H W) memD a _ Ha' Hb').
-
intros kk Hkk. destruct kk as [|kk'].
+ pose proof (DMUT 0%nat ltac:(lia)) as E0. cbn [Z.of_nat] in E0 |- *. rewrite le_byte_zero in *. exact E0.
+ rewrite (mbyte_mrestrict_same (w_H W) memX memD).
* pose proof (VM (S kk') Hkk) as E1. rewrite E1. f_equal. f_equal. rewrite le_byte_zero.
unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. rewrite (Z.mod_small 1 4294967296) by lia.
rewrite Z.div_small; [reflexivity|]. split; [lia|]. eapply Z.lt_le_trans with (2 ^ 8); [lia|]. apply Z.pow_le_mono_r; lia.
* apply MQX. unfold A_ALLOCATOR. rewrite unsigned_lit_small by lia. clear - Hkk S1 hS1 hT1. numconst. lia.
Qed.

Section s.
Hypothesis Hidx : index_of (st_sec_arr X) r 0%nat = Some i.
Hypothesis SMALL : needs_remap (sm_len sm) = false.
Theorem WALK_U : SRr tfibsegs W (cfg_at tfibsegs A_RChunk regs mem md) (YFg8.POSTMUN ly X W regs mem md r sm i).
Proof.
unfold cfg_at. rewrite <- (YFf6.wvb_self md) at 1.
eapply SRr_bind; [exact (to_LMD_U (m_vm_materialized md))|].
intros W1 c1 _ HD. destruct HD as (-> & regsD & memD & matD & -> & PD).
pose proof (YFf9.DSEED B TB ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi true SMALL HTSD regsD _ (PRED_u regsD memD PD)) as FHDu.
pose proof (FRR.fhD_real UP OFFa W ly regsD memD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own true OFFS FHDu) as FHD.
assert (GATE : forall PB kk, 0 < kk -> YFgv.SHAv MAP <= PB -> PB + kk <= YFgv.SHEv MAP LEN ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
{ intros PB kk Hkk H1 H2.
pose proof (YFgv.fh_Hmap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FHD) as (Z3 & ZC & _ & ZL & _).
pose proof (YFgv.fh_LY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FHD) as LO.
pose proof PRE_u as ((_ & LG & _) & _).
apply (madvise_gate_L tfibsegs ly X md PB kk LO LG Hkk).
unfold YFgv.SHAv, YFgv.SHEv, YFgv.CNTv, YFgv.SHAv in H1, H2. clear - Z3 ZC ZL H1 H2 Hkk. ceil.
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *.
Z.div_mod_to_equations. lia. }
eapply SRr_mono; [exact (YFf8.segGD W ly regsD memD md MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own true matD FHD GATE eq_refl)|].
intros W2' c2 _ HM. unfold YFg8.POSTMUN. exists regsD, memD. split; [|exact HM].
destruct PD as (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
unfold YFg8.LINKD. split; [exact D2|]. split; [exact DSR|]. split; [|exact DTJ].
intros x Hx. apply MQD. intros HW. apply Hx. unfold YFg8.WPRE. unfold YFf7.WIND, YFf6.WINA in HW.
unfold GDEPTH. clear - HW. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The leaf (lib/B/YFg8.v FIN) at mu, and U's two invariants after the munmap and the refund of the mapping.     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma ablocks_X2 : forall p n, In (p, n) (ablocks B ly X) -> In (p, n) (ablocks B ly (YFg8.X2 (YFf3.X1 X k) r i sm)).
Proof.
intros p n Hbl. apply (FRR.ablocks_keep B ly X _ p n); [|exact Hbl].
intros y Hy Hay. destruct (YFf4.SPLIT B ly X _ M_u k Hk_u) as (l1 & l2 & E1 & E2 & N1 & N2).
replace (st_chunks (YFg8.X2 (YFf3.X1 X k) r i sm)) with (st_chunks (YFf3.X1 X k)) by reflexivity. rewrite E2.
rewrite E1 in Hy. apply in_app_iff in Hy as [Hy|[Hy|Hy]]; [apply in_app_iff; left; exact Hy | | apply in_app_iff; right; exact Hy].
subst y. unfold is_alloc in Hay. rewrite Hst_u in Hay. cbn in Hay. discriminate.
Qed.
Lemma FINU : forall regsD memD mat1 c', YFg8.LINKD ly W regs mem regsD memD ->
YFgv.at_RET W ly regsD memD MAP LEN idx nA qi lst vra vs0 vs1 vs2 own (munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)) W c' ->
FK.rcc_leafU B ly X k UP W regs mem md (tt, YFg8.X2 (YFf3.X1 X k) r i sm) W2 c'.
Proof.
intros regsD memD mat1 c' LNK HR.
pose proof LNK as (LSP & _ & LMEM & _).
pose proof (YFfc.HI B TB ly X k cbp W regs mu md PRE_u) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _).
pose proof (YFfc.HSP B ly X k cbp W regs mu md PRE_u) as [S1 S2].
pose proof (YFfc.ARRF B ly X k cbp W regs mu md r i PRE_u Hi) as (_ & _ & _ & A4 & A5).
pose proof (YFfc.GEOM B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as (M1 & M2 & _).
pose proof (YFfc.last_facts B TB ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi) as (_ & _ & _ & _ & _ & LL1 & _).
assert (SPD : bv_unsigned (YK11.getr regsD 2) = sp0) by (rewrite LSP; reflexivity).
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FRR.appb a) by (intros a Ha; right; clear - Ha hS1 hS2; numconst; lia).
assert (APP : forall a, YFgv.WIN ly regsD qi lst a \/ YFgv.WINM MAP LEN a \/ YFg8.WPRE ly regs a -> FRR.appb a).
{ intros a [HW|[HW|HW]].
  - unfold YFgv.WIN in HW. rewrite SPD in HW. unfold YFg8.qi, YFg8.idx in HW. unfold YFg8.nA in A4, A5.
    destruct HW as [HW|[HW|[HW|[HW|[HW|[HW|[HW|HW]]]]]]].
    + apply STK. clear - HW S1 S2. numconst. lia.
    + left. clear - HW. numconst. lia.
    + left. clear - HW. numconst. lia.
    + left. clear - HW. numconst. lia.
    + left. clear - HW. numconst. lia.
    + apply (Z3app _ _ a hQ1). clear - HW A4 A5. unfold kPtrArrayResv. lia.
    + apply (Z3app _ _ a hT1). clear - HW. numconst. lia.
    + apply (Z3app _ _ a LL1). clear - HW. lia.
  - exact (Z3app _ _ a M1 HW).
  - unfold YFg8.WPRE in HW. destruct HW as [HW|[HW|HW]].
    + apply STK. clear - HW S1 S2. numconst. lia.
    + left. clear - HW. numconst. lia.
    + apply (Z3app _ _ a hT1). clear - HW. numconst. lia. }
assert (OW : forall b, YFgv.WIN ly regsD qi lst b -> FAR.offU UP b) by (intros b Hq; apply OFFa, APP; left; exact Hq).
destruct (FRR.at_RET_unpoison UP W ly regsD memD MAP LEN idx nA qi lst vra vs0 vs1 vs2 own _ W c' OW HR) as (regs' & mem' & mat & Ec & MQ' & HRu).
pose proof (YFg8.FIN B TB ly X k cbp W regs mu md r o sm i PRE_u Hb Hsm Hi HTSD regsD (FSP.unpoison UP memD) mat1 W _ (LINKD_u regsD memD LNK) HRu) as LF.
set (mdR := with_vm_backing (m_vm_lazy (munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md))) mat
  (munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md))) in *.
assert (Ec' : c' = cfg_at tfibsegs (raZ regs) regs' mem' mdR) by (rewrite Ec; reflexivity).
rewrite Ec'. apply FK.rcc_leafU_intro.
- exact LF.
- cbn [snd]. apply (FAR.upoison_ok_keep B ly X ly _ UP (proj1 (proj2 PREU))). intros rr p n _ Hbl _ _. exact (ablocks_X2 p n Hbl).
- intros s Hs. pose proof (FSP.ush_range tfibsegs B ly X UP W mem md s ARU0 Hs) as Hs64.
  assert (NF : ~ rchunk_sec_fixed s).
  { intros F. pose proof (rchunk_sec_regions_off_ush s F) as O. unfold FAR.offU in O. rewrite Z.mod_small in O by exact Hs64. rewrite O in Hs. discriminate. }
  rewrite wrefund_H. transitivity (aview tfibsegs (w_H W) mem s); [|exact (proj2 (proj2 PREU) s Hs)].
  apply (FSP.aview_at tfibsegs).
  rewrite MQ'.
  2:{ rewrite unsigned_lit_small by exact Hs64. intros HW. apply NF. unfold YFgv.WIN3 in HW. destruct HW as [HW|[HW|HW]].
      - left. apply APP. left. exact HW.
      - right. exact HW.
      - left. apply APP. right; left. exact HW. }
  apply LMEM. rewrite unsigned_lit_small by exact Hs64. intros HW. apply NF. left. apply APP. right; right. exact HW.
- (* the raw frame: the walk's window (YFg8.WPRE, LMEM) and the return's (YFgv.WIN3, MQ') are in YFf4.D (as in
     YFg8.FIN), owned by X or in the stack scratch (YFf4.D_owned) *)
  pose proof (YFg8.KFACTS B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as (_ & _ & ELEN & _).
  assert (ELEN' : sec_map_size (ck_req k) = LEN) by (symmetry; exact ELEN).
  pose proof (YFg8.LEN_facts B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as [L1 _].
  assert (EI : A_ALLOCATOR = as_inst B) by (rewrite (ts_inst _ TB); reflexivity).
  pose proof (YFf4.ARR B ly X _ M_u r i Hi) as (_ & _ & _ & _ & _ & _ & _ & A8).
  assert (WD : forall a, 0 <= a < 2 ^ 64 -> (YFg8.WPRE ly regs a \/ YFgv.WIN3 ly regsD MAP LEN qi lst a) -> YFf4.D B ly X k r i sp0 a).
  { intros a Ha HW. unfold YFf4.D, YFf4.DS, YFf4.DI, YFf4.DJ, YFf4.DQ, YFf4.DL, YFf4.DH, YFf4.DM.
    unfold YFf4.own, YFf4.qi, YFf4.lst, YFf4.MAP, YFf4.LEN, YFf4.idx, YFf4.nA, YFf4.lastr, YFf4.arr.
    rewrite ELEN'. fold MAP. rewrite <- EI. unfold shadow_addr.
    unfold YFg8.WPRE, YFgv.WIN3, YFgv.WIN2, YFgv.WIN, YFgv.WINS, YFgv.WINM, YFgv.SHAv, YFgv.CNTv, GDEPTH in HW. rewrite SPD in HW.
    unfold YFg8.own, YFg8.qi, YFg8.lst, YFg8.idx, YFg8.nA in *.
    destruct (Z.eqb_spec (Z.of_nat i) (Z.of_nat (length (st_sec_arr X)) - 1)) as [EO|NEO].
    - assert (LR : last (st_sec_arr X) r = r) by (apply A8; unfold YFf4.own, YFf4.idx, YFf4.nA, YFf4.arr; apply Z.eqb_eq; exact EO).
      rewrite LR in HW. fold MAP in HW. unfold KSTACK.
      lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ _) \/ ?G =>
      enough (G' : A \/ Bq \/ C \/ Dq \/ G) by (destruct G' as [?|[?|[?|[?|?]]]]; [left | right; left | do 2 right; left | do 3 right; left | do 5 right]; assumption) end.
      clear - HW L1 Ha. lia.
    - unfold KSTACK.
      lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ ?F) \/ ?G =>
      enough (G' : A \/ Bq \/ C \/ Dq \/ F \/ G) by (destruct G' as [?|[?|[?|[?|[?|?]]]]]; [left | right; left | do 2 right; left | do 3 right; left | do 4 right; left; split; [reflexivity | assumption] | do 5 right]; assumption) end.
      clear - HW L1 Ha. lia. }
  assert (INC : forall a, 0 <= a < 2 ^ 64 -> (YFg8.WPRE ly regs a \/ YFgv.WIN3 ly regsD MAP LEN qi lst a) ->
    ~ aowned B ly X a -> ~ ascratch B KSTACK regs a -> False).
  { intros a Ha HW NOa NSa.
    destruct (YFf4.D_owned B TB ly X _ M_u k r o sm i Hk_u Hst_u Hb Hsm Hi sp0 (YFfc.HSP B ly X k cbp W regs mu md PRE_u)
      (YFfc.IMG B ly X k cbp W regs mu md PRE_u) a (proj1 Ha) (WD a Ha HW)) as [O|O].
    - exact (NOa O).
    - apply NSa. unfold ascratch, spZ. left. exact O. }
  intros x NO _ NS _. rewrite MQ'.
  + apply LMEM. intros HW. exact (INC _ (bv_unsigned_in_range _ x) (or_introl HW) NO NS).
  + intros HW. exact (INC _ (bv_unsigned_in_range _ x) (or_intror HW) NO NS).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The arm (lib/B/YFg8.v plumbing, lib/B/YFg9.v tfib_rchunk_sec_small_arm): the donor text over WALK_U and FINU. *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem tfib_rchunk_sec_small_armU : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (FK.rcc_leafU B ly X k UP W regs mem md).
Proof.
pose proof (YFg8.MAP_facts B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as (P1 & P2 & P3 & INA & INV & MW).
pose proof (YFg8.LEN_facts B ly X k cbp W regs mu md r o sm PRE_u Hb Hsm) as [L1 L2].
rewrite (YFg8.recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hk_u) Hb Hsm Hidx SMALL). cbn [amreal].
eapply SRr_bind; [exact WALK_U|]. intros W1 c1 _ (regsD & memD & LNK & HM).
destruct HM as (-> & regs1 & mem1 & mat1 & -> & H17 & H10 & H11 & INNER). cbv zeta in INNER.
apply SRr_use_AI. cbn [cfg_model]. intros HAI. apply SRr_ret.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (c2 := mkCfg (YK11.mkst (YK11.regupd regs1 10 (w64 0)) (w64 PC_MUNMAP_RET) (unfill (w64 MAP) (w64 LEN) mem1) (YK11.seg_rom tfibsegs)) (munmap_model (w64 MAP) (w64 LEN) md1)).
assert (UM : bv_unsigned (w64 MAP) = MAP) by (unfold w64; apply unsigned_lit_small; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (UL : bv_unsigned (w64 LEN) = LEN) by (unfold w64; apply unsigned_lit_small; lia).
assert (MW1 : amwf md1) by (apply (amwf_same md md1); [subst md1; apply m_vmmaps_wvb | subst md1; apply m_vm_lazy_wvb | exact MW]).
assert (INV1 : In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1))) by (subst md1; rewrite m_vmmaps_wvb; exact INV).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
exists unit, (fun _ => c2), (fun _ => 1), (fun _ => false), tt.
split.
{ pose proof (munmap_node tfibsegs regs1 (w64 PC_MUNMAP_ECALL) mem1 (YK11.seg_rom tfibsegs) md1 (w64 MAP) LEN (AI_halted _ _ _ _ HAI) H17 H10
ltac:(rewrite UM; unfold page_size; exact P3) H11 ltac:(lia)
ltac:(rewrite UM, (YFg8.page_round_up_Z_aligned LEN) by lia; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, two_pow_64, TASK_SIZE, kHighMemBeg, ASAN_CEIL in *; lia)
ltac:(rewrite (YFg8.page_round_up_Z_aligned LEN) by lia; exact (map_has_In _ _ _ INV1))) as ND.
cbv zeta in ND. rewrite (YFg8.page_round_up_Z_aligned LEN) in ND by lia. exact ND. }
split. { intros [] _. cbn [cfg_model]. exact (munmap_AI tfibsegs (w_H W) (w_A W) md1 (w64 MAP, w64 LEN) l1 l2 HAI MW1 EVM ltac:(cbn [fst]; rewrite UM; unfold page_size; exact P3)
ltac:(cbn [fst snd]; rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)). }
split. { intros []. cbn [aok]. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros [] _; reflexivity|].   split; [intros [] XX; discriminate XX|].
intros [] _. cbn [amreal].
eapply SRr_bind; [exact INNER|]. intros W3 c3 _ HR. pose proof HR as (-> & regs' & mem' & mat' & Ec3 & _).
apply SRr_use_AI. intros HAI3. rewrite Ec3 in HAI3 |- *. cbn [cfg_model] in HAI3.
apply (SRr_world_le tfibsegs W W2).
{ apply wrefund_wle. }
{ intros _. cbn [cfg_model]. apply AI_refund_gen; [exact HAI3|]. intros p Hp. rewrite m_vm_lazy_wvb in Hp. cbn [fst snd].
pose proof (munmap_lazy_out (w64 MAP) (w64 LEN) md1 p ltac:(destruct MW1 as [(_ & _ & W3l & _) _]; intros q Hq; exact (W3l q Hq))
ltac:(rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) Hp) as NL. rewrite UM, UL in NL. exact NL. }
apply SRr_ret. rewrite <- Ec3. exact (FINU regsD memD mat1 c3 LNK HR).
Qed.
End s.
End b.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 7. The secondary-chunk spec for any U (lib/B/YFg9.v tfib_rchunk_sec_small, tfib_rchunk_sec).                      *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem tfib_rchunk_sec_smallU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly X UP k cbp W regs mem md r o,
FK.rcc_preU B ly X k cbp UP W regs mem md -> ck_beg k = PSec r o -> needs_remap (sec_map_size (ck_req k)) = false ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (FK.rcc_leafU B ly X k UP W regs mem md).
Proof.
intros B LAWS TB ly X UP k cbp W regs mem md r o PREU Hb SMALL. pose proof PREU as (((M & _) & _ & Hk & _) & _).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly X _ M); apply (ts_tsd _ TB)).
pose proof (am_wf B ly X _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK]. rewrite Hb in CK. destruct CK as (_ & _ & sm & Hsm & Hlive & Hsz & Hlen).
destruct (wf_secondary _ _ _ _ _ WF) as [_ Sac _ _ _].
assert (Hr : In r (st_sec_arr X)).
{ apply (proj2 (Sac r)). exists k. split; [exact Hk|]. rewrite Hb.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK']. rewrite Hb in CK'. destruct CK' as (_ & -> & _). reflexivity. }
destruct (index_of_spec (st_sec_arr X) r 0%nat Hr) as (i & Hidx & Hi). rewrite Nat.add_0_l in Hidx.
assert (SM : needs_remap (sm_len sm) = false) by (rewrite Hlen; exact SMALL).
exact (tfib_rchunk_sec_small_armU B TB ly X UP k cbp W regs mem md r o sm i PREU Hb Hsm Hi HTSD Hidx SM).
Qed.
Theorem tfib_rchunk_secU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FK.tfib_rchunk_sec_specU B.
Proof.
intros B LAWS TB ly X k cbp UP W regs mem md r o PREU Hb.
apply (tfib_rchunk_sec_smallU B LAWS TB ly X UP k cbp W regs mem md r o PREU Hb). apply needs_remap_false.
pose proof PREU as (((M & _) & _ & Hk & _) & _). pose proof (am_wf B ly X _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [CKr _].
pose proof (YG08.sec_map_size_bound (ck_req k) (proj1 CKr)) as SB. unfold req_size, MALLOC_MAX in *.
destruct (ck_req k =? 0); lia.
Qed.
End a.

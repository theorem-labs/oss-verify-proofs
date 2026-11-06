(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Malloc PRIMARY miss arms and the miss / hit join under ARU, any UP: the twins of lib/A/AFim.v (malloc_missg),
   lib/A/AFin.v (malloc_missk) and lib/A/AFij.v (malloc_miss / malloc_prim). The refill the miss arm performs is
   discharged by FSupoisonAllocRt.tfib_refill_okU through FSupoisonAllocR.tfib_refill_specU; the tail after a refill
   that filled the cache is FSupoisonAllocMp2.tail_innerU / FSupoisonAllocMp3.tail_innerU; the hit arms of the join
   are FSupoisonAllocMp2.malloc_hitgU / FSupoisonAllocMp3.malloc_hitkU; the miss seed (AFi4.v MS0 / MK0) moves
   between the two readings of memory by FSupoisonAllocMp4.st_ok_real. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: new file; it proves malloc_missgU, malloc_misskU and malloc_primU over FSupoison.ARU for any user-poisoned head list UP. *)
(* Modified by Theorem Labs, 2026-10: image-B port (fuzz_state.asan-ubsan, sha256 5ac5ce0954f87e2d) of lib/A/FSupoisonAllocMm.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), the kit is lib/B/FSupoisonAllocR / Rf / Rt, every statement is over B's tfibsegs (lib/B/YB1v.v); the entry, return, refill and refill-return pcs are named (PC_WRAP_MALLOC, PC_MALLOC_RA0, PC_REFILL, RA_REFILL); the read-write window lemmas are the donors' own (YFim / YFin rw_writable, aview_rw_some), not restated. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG06 YG07 YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFhy YFi1 YFhz YFi2 YFi4 YFhm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFis YFi3 YFiy YFiz YFj0 YFix YFj2 YFiw YFiu YFit YFiv YFi5 YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFj6 YFjc YFjd YFje YFjb YFjg YFja YFj8 YFj7 YFj9.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfk.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFkq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFim YFin.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocRt FSupoisonAllocMp1 FSupoisonAllocMp2 FSupoisonAllocMp3 FSupoisonAllocMp4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* Constants kept from the A template are image-independent; each is verbatim in a B donor: the refill frame 2320 / 145
   (lib/B/YFim.v:200, 269), the thread-object words T + 2784 .. 2816 (YFim.v:361), the class bounds 448 .. 64512
   (YFim.v:150, 109) and their spans 128 / 512 / 1024 (YFij.v:45, 47, 48), the shadow bytes 250 / 255 (YFim.v:449, 164). *)
(* B's addresses by name, each evaluated to its literal so that the terms are the YF donors' own: the code table
   Tfib_code (lib/B/YF0l.v), lib/B/YFl1.v's A_Refill, and a function entry of lib/B/YB1w.v plus the offset of the
   instruction in that function (the offset image A has; read off the unstripped B image with pyelftools + capstone). *)
Local Notation "'zlit' x" := ltac:(let v := eval vm_compute in (x : Z) in exact v) (at level 10, x at level 0, only parsing).
Local Notation PC_WRAP_MALLOC := (zlit (pc_wrap_malloc Tfib_code)) (only parsing).
Local Notation PC_MALLOC_RA0 := (zlit (pc_malloc_ra0 Tfib_code)) (only parsing).
(* The refill entry (lib/B/YFl1.v A_Refill) and the return address of CombinedAllocator::Allocate's Refill call. *)
Local Notation PC_REFILL := (zlit A_Refill) (only parsing).
Local Notation RA_REFILL := (zlit (tfib_A__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x2b0)) (only parsing).
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module AllocR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module Rt := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocRt.
Module Mp1 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocMp1.
Module Mp2 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocMp2.
Module Mp3 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocMp3.
Module Mp4 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocMp4.
Module Dm := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YFim.
Module Dk := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YFin.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 0. A frame-pointer chain reads only [bp - 16, bp) at each link, and each link sits at or below the top; so a run  *)
(*    that keeps the bytes of [lo, top) keeps the chain. Byte-level form of FSupoisonAllocR.fpchain_ext.             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma fpchain_bytes : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a < top -> r2 a = r1 a) -> lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp E Hlo Hhi H; cbn [fpchain] in *.
- destruct H as (r & Hr & Hb).
  rewrite (AllocR.rdword_ext r1 r2 (bp - 8) ltac:(intros k Hk; symmetry; apply E; lia)) in Hr.
  exists r. split; assumption.
- destruct H as (-> & A8 & L1 & L2 & R4 & HN).
  rewrite (AllocR.rdword_ext r1 r2 (bp - 8) ltac:(intros k Hk; symmetry; apply E; lia)) in L1.
  rewrite (AllocR.rdword_ext r1 r2 (bp - 16) ltac:(intros k Hk; symmetry; apply E; lia)) in L2.
  refine (conj eq_refl (conj A8 (conj L1 (conj L2 (conj R4 _))))).
  destruct (bad_next bp top nfp) eqn:BN; [exact HN|].
  unfold bad_next in BN. apply orb_false_iff in BN as [BN1 BN3]. apply orb_false_iff in BN1 as [BN1 BN2].
  apply Z.leb_gt in BN1. apply Z.leb_gt in BN2. apply (IH nfp E); [lia | lia | exact HN].
Qed.

(* The OOM byte and errno live in the image's read-write window: lib/B/YFim.v:465 rw_writable (its statement carries the
   section variables ly regs0 n, passed at each use) and :467 aview_rw_some, and their YFin.v twins. *)

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The miss-g arm (49 <= n <= 64512) for any UP. Port-from: lib/B/YFim.v:624.                                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Set Default Proof Using "All".
Section ga.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Variable UP : list (Z * Z).
Let tr : list Z := call_trace ly PC_MALLOC_RA0 regs0 ch.
Hypothesis PRE : FSU.acall_preU tfibsegs B ly S UP W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange0 : 49 <= n <= 64512.
Hypothesis Htr : tr_admit (as_universe B) S tr.
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let cl : Z := chunk_class n.
Let kz : Z := rz_log n.
Let csz : Z := class_size cl.
Let mat0 : list word := m_vm_materialized md0.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Let E0m : env := YFis.E0 ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => YFix.DPOST3 W ly regs0 ch B S1 z m.

(* The two readings: AR holds of the unpoisoned reading, the machine runs on mem0. *)
Lemma HARU0 : FSP.ARU tfibsegs B ly S UP W mem0 md0.
Proof. exact (AllocR.ARU_of_acall_preU B ly S UP W regs0 mem0 md0 ch PRE). Qed.
Lemma HAR0u : AR tfibsegs B ly S W (FSP.unpoison UP mem0) md0.
Proof. exact (proj1 (proj1 PRE)). Qed.
Lemma HARm0u : ARm B ly S (aview tfibsegs (w_H W) (FSP.unpoison UP mem0)).
Proof. exact (proj1 HAR0u). Qed.
Lemma Hev : aregime S. Proof. exact (proj1 (proj2 (proj1 PRE))). Qed.
Lemma HAR1u : AR tfibsegs B ly S1 W (FSP.unpoison UP mem0) md0.
Proof. exact (AR_tick B ly S W (FSP.unpoison UP mem0) md0 HAR0u Hev). Qed.
Lemma HARm1u : ARm B ly S1 (aview tfibsegs (w_H W) (FSP.unpoison UP mem0)).
Proof. exact (proj1 HAR1u). Qed.
Lemma HARU1 : FSP.ARU tfibsegs B ly S1 UP W mem0 md0.
Proof. exact (AllocR.ARU_tick B ly S UP W mem0 md0 HARU0 Hev). Qed.
Lemma LY : layout_ok ly. Proof. exact (am_layout _ _ _ _ HARm0u). Qed.
Lemma IMG : img_cover ly. Proof. exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR0u))). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (am_tsd _ _ _ _ HARm0u). exact (ts_tsd B TS). Qed.
Lemma Htp : getr regs0 4 = w64 TFIB_TP.
Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp' & _) & _). rewrite (ts_tp B TS) in Htp'. exact Htp'. Qed.
Lemma Hgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.
Lemma Hra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE as ((_ & _ & H & _) & _). exact H. Qed.
Lemma Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Proof. destruct PRE as ((_ & _ & _ & Hal & Hlo & Hbot & Hhi & _) & _). unfold spZ in *. repeat split; assumption. Qed.
Lemma Hpres0u : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (FSP.unpoison UP mem0) a.
Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.
Lemma HQT : qmeter S. Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.
Lemma HOK : FSP.upoison_ok B ly S UP. Proof. exact (proj1 (proj2 PRE)). Qed.
Lemma HPO : FSP.upoisoned tfibsegs W mem0 UP. Proof. exact (proj2 (proj2 PRE)). Qed.
Lemma STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof (lo_top ly LY) as (_ & _ & _ & H4 & _ & _ & H7). split; [exact H7 | exact H4]. Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. apply u64_range. Qed.

(* The stack window and the chain, on the REAL memory the machine runs on. *)
Lemma Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
apply (AllocR.stack_present_real B ly S UP W mem0 md0 (sp0 - ASTACK) sp0 HARU0);
  [unfold ASTACK in *; lia | lia | exact Hpres0u].
Qed.
Lemma CHr : chain_pre ly (aview tfibsegs (w_H W) mem0) regs0 ch.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CH & _) & _).
exact (AllocR.chain_pre_real B ly S UP W regs0 mem0 md0 ch HARU0 ltac:(unfold spZ, sp0, ASTACK in *; lia) CH).
Qed.
Lemma Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. pose proof CHr as [H _]. unfold raZ in H. exact H. Qed.
Lemma Hch : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof. pose proof CHr as [_ H]. unfold frame0_ok, spZ, s0Z in H. exact H. Qed.

(* The class geometry of the request. *)
Lemma Hkz : 1 <= kz <= 6 /\ rz_lo kz <= n <= rz_hi kz.
Proof.
subst kz. unfold rz_log. clear - Nrange0.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [cbn; lia|]. destruct (Z.leb_spec n 448); [cbn; lia|].
destruct (Z.leb_spec n 3968); [cbn; lia|]. destruct (Z.leb_spec n 16128); [cbn; lia|]. destruct (Z.leb_spec n 32256); [cbn; lia|].
destruct (Z.leb_spec n 64512); [cbn; lia|]. lia.
Qed.
Lemma Hkz1 : 1 <= kz <= 6. Proof. exact (proj1 Hkz). Qed.
Lemma Nrange : rz_lo kz <= n <= rz_hi kz. Proof. exact (proj2 Hkz). Qed.
Lemma Hcl_class : cl = chunk_class n. Proof. reflexivity. Qed.
Lemma Hcsz_def : csz = class_size cl. Proof. reflexivity. Qed.
Lemma Hcl : 1 <= cl <= 31. Proof. exact (@YFiy.Hcl' ly regs0 mem0 n cl 0 kz DPOSTm Hkz1 Nrange [] 0 Hcl_class). Qed.
Lemma Hcl_def : cl = class_id (YFis.R8v n + YFis.RZ kz).
Proof. pose proof (@YFis.casek_sizes n kz Hkz1 Nrange) as (L & RS & R8 & NP & FP & NS & RQ). subst cl. unfold chunk_class. rewrite NS, <- RS. reflexivity. Qed.
Lemma FP : from_primary n = true. Proof. pose proof (@YFis.casek_sizes n kz Hkz1 Nrange) as (_ & _ & _ & _ & FP' & _). exact FP'. Qed.
Lemma Hmiss1 : pc_chunks (cache S1 cl) = []. Proof. exact Hmiss. Qed.
Lemma Hvd : 0 <= 0 /\ 16 * 0 + 2 ^ 16 <= 2 ^ 32. Proof. lia. Qed.
Lemma Hcntd : 1 <= 1 <= 16. Proof. lia. Qed.
Lemma Hjbd : 0 <= 0 <= 255. Proof. lia. Qed.
Lemma Hv2d : 0 mod 2 = 0. Proof. reflexivity. Qed.
Lemma WfP1 : WfP (as_universe B) 1 1 1 S1. Proof. exact (WfP_tick _ S (am_wf _ _ _ _ HARm0u) Hev). Qed.
Lemma T_range : zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL.
Proof. pose proof (@YFis.high_facts _ ly regs0 mem0 n 0 kz Hvd LY IMG DPOSTm) as (F1 & F2 & _). split; assumption. Qed.
Lemma C_range : zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL.
Proof. pose proof (@YFis.high_facts _ ly regs0 mem0 n 0 kz Hvd LY IMG DPOSTm) as (_ & _ & _ & _ & _ & _ & F7 & F8 & _). split; assumption. Qed.

(* Where UP is not: the stack window, the image's literals, the thread object, the cache array. *)
Lemma offU_stk : forall a, sp0 - ASTACK <= a < sp0 -> AllocR.offU UP a.
Proof.
intros a Ha. pose proof Hsp as (P1 & P2 & P3 & P4).
exact (AllocR.stack_offU B ly S1 UP W mem0 md0 a HARU1 ltac:(unfold ASTACK in *; lia)).
Qed.
Lemma offU_lo : forall a, 0 <= a < SHADOW_OFF -> AllocR.offU UP a.
Proof. intros a Ha. exact (Mp1.offU_lit B ly S1 UP W mem0 md0 a HARU1 Ha). Qed.
Lemma offU_T : forall a, T <= a < T + kThreadObjSize -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S1 UP W mem0 md0 (ly_T ly, kThreadObjSize) a HARU1
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. unfold T in Ha. exact Ha.
Qed.
Lemma offU_C : forall a, ly_C ly <= a < ly_C ly + 256 -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S1 UP W mem0 md0 (ly_C ly, 256) a HARU1
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. exact Ha.
Qed.

(* Every byte the miss seed's regions (YFi4.v MREG0) fix is off UP, or the region fixes nothing at all. *)
Lemma MREG0_offU : forall r, In r (ss_mem MS0) ->
  Mp4.reg_inert r = true \/
  (forall a, base_val E0m (YP09.r_base r) + YP09.r_lo r <= a < base_val E0m (YP09.r_base r) + YP09.r_hi r ->
     AllocR.offU UP a).
Proof.
pose proof (@YFis.derived_ranges _ ly regs0 mem0 n cl 1 0 kz Hcl Hvd Hcntd Hv2d LY IMG DPOSTm Hkz1 Nrange) as DR.
pose proof (@YFis.high_facts _ ly regs0 mem0 n 0 kz Hvd LY IMG DPOSTm) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
pose proof Hsp as (SP1 & SP2 & SP3 & SP4). pose proof Hcl as HC1.
destruct F1 as (ZT1 & ZT2 & _). destruct F7 as (ZC1 & ZC2 & _).
ceil. unfold kThreadObjSize, ASAN_CEIL, t_cache, t_unwinding, kHighMemBeg in *.
assert (RT : 0 <= ly_T ly < 2 ^ 64) by lia.
assert (RC : 0 <= ly_C ly < 2 ^ 64) by lia.
assert (RPv : 0 <= YFis.Pv ly cl < 2 ^ 64) by lia.
assert (RPVv : 0 <= YFis.PVv ly cl 1 < 2 ^ 64) by lia.
assert (RSS : 0 <= YFis.SSLOTv ly cl < 2 ^ 64) by lia.
change (ss_mem MS0) with MREG0.
intros r Hr. pose proof (proj1 (forallb_forall _ _) Mp4.MREG0_classb r Hr) as K.
apply Bool.orb_prop in K as [K|K]; [left; exact K|]. right. intros a Ha.
unfold E0m in Ha. unfold Mp4.reg_appb in K.
set (rb := YP09.r_base r) in *. clearbody rb. destruct rb as [k|]; cbn [base_val] in Ha.
2:{ apply andb_prop in K as [K1' K2']. apply Z.leb_le in K1'. apply Z.leb_le in K2'. apply offU_lo. lia. }
repeat match type of K with (_ || _) = true => apply Bool.orb_prop in K; destruct K as [K|K] end;
  apply andb_prop in K as [K K3']; apply andb_prop in K as [K1' K2'];
  apply Nat.eqb_eq in K1'; subst k; apply Z.leb_le in K2'; apply Z.leb_le in K3'.
- rewrite (@YFis.E2 ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz) in Ha.
  change (bv_unsigned (getr regs0 2)) with sp0 in Ha. apply offU_stk. unfold ASTACK in *. lia.
- rewrite (@YFis.EaT ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RT. apply offU_T. lia.
- rewrite (@YFis.EaC ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RC. apply offU_C. lia.
- rewrite (@YFis.EaP ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RPv.
  apply offU_T. unfold kThreadObjSize, t_cache in *. lia.
- rewrite (@YFis.EaPV ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RPVv.
  apply offU_T. unfold kThreadObjSize, t_cache in *. lia.
- rewrite (@YFis.EaSSLOT ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RSS.
  apply offU_T. unfold kThreadObjSize, t_unwinding in *. lia.
Qed.

(* The miss seed, first at the unpoisoned reading (the donor's lemma), then on the real memory. *)
Lemma SEEDMu : st_ok tfibsegs E0m MS0 (restrict (w_H W) (mkst regs0 (w64 PC_WRAP_MALLOC) (FSP.unpoison UP mem0) (seg_rom tfibsegs))).
Proof.
exact (@YFiw.SEEDM_ok _ _ W ly regs0 (FSP.unpoison UP mem0) n ch cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Htp Hsp DPOSTm Hkz1 Nrange B S1 TS HTSD HARm1u Hpres0u Hmiss1).
Qed.
Lemma SEEDM : st_ok tfibsegs E0m MS0 (restrict (w_H W) (mkst regs0 (w64 PC_WRAP_MALLOC) mem0 (seg_rom tfibsegs))).
Proof. exact (Mp4.st_ok_real UP E0m MS0 (w_H W) regs0 (w64 PC_WRAP_MALLOC) mem0 (seg_rom tfibsegs) MREG0_offU SEEDMu). Qed.

Lemma MISS1 : SRr tfibsegs W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (YFiu.at_STM W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 kz MS_CALL).
Proof.
replace (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 PC_WRAP_MALLOC) mem0 (seg_rom tfibsegs)) (md0' mat0))
by (unfold cfg_at, md0', mat0; rewrite with_vm_backing_id; reflexivity).
exact (@YFiu.miss1 _ _ W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Hra4096 Hsp Hch DPOSTm Hkz1 Nrange Hcl_def mat0 U1 [] 0 SEEDM).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1b. At the call to Refill. Port-from: lib/B/YFim.v section f.                                                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section gf.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em MS_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ YFiu.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).

Lemma ms1_shape : ms1 = mkst (ms_regs ms1) (w64 PC_REFILL) (ms_mem ms1) (seg_rom tfibsegs).
Proof. exact (st_ok_restrict_mkst tfibsegs (w_H W) Em _ _ HSC eq_refl). Qed.
Lemma HSC' : st_ok tfibsegs Em MS_CALL (mkst (ms_regs ms1) (w64 PC_REFILL) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs)).
Proof. pose proof HSC as H. rewrite ms1_shape in H. exact H. Qed.
Lemma Em2 : ew Em 2 = getr regs0 2. Proof. rewrite (HEm 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em3 : ew Em 3 = getr regs0 3. Proof. rewrite (HEm 3%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em32 : ew Em 32 = w64 T. Proof. rewrite (HEm 32%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em39 : ew Em 39 = w64 cl. Proof. rewrite (HEm 39%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em40 : ew Em 40 = w64 (YFis.Pv ly cl). Proof. rewrite (HEm 40%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma R_ra : getr (ms_regs ms1) 1 = w64 RA_REFILL. Proof. rreg HSC (1%bv : bv 5) R. exact R. Qed.
Lemma R_sp : getr (ms_regs ms1) 2 = w64 (sp0 - 2320).
Proof. rreg HSC (2%bv : bv 5) R. rewrite R, Em2. unfold w64, sp0. f_equal; lia. Qed.
Lemma R_gp : getr (ms_regs ms1) 3 = getr regs0 3. Proof. rreg HSC (3%bv : bv 5) R. rewrite R, Em3. reflexivity. Qed.
Lemma R_tp : getr (ms_regs ms1) 4 = w64 TFIB_TP. Proof. rreg HSC (4%bv : bv 5) R. exact R. Qed.
Lemma R_a0 : getr (ms_regs ms1) 10 = w64 (T + t_cache).
Proof. rreg HSC (10%bv : bv 5) R. rewrite R, Em32. unfold w64, t_cache. rewrite Zbv_add_unsigned. reflexivity. Qed.
Lemma R_a1 : getr (ms_regs ms1) 11 = w64 (T + t_cache + 80 * cl). Proof. rreg HSC (11%bv : bv 5) R. rewrite R, Em40. reflexivity. Qed.
Lemma R_a2 : getr (ms_regs ms1) 12 = w64 A_ALLOCATOR. Proof. rreg HSC (12%bv : bv 5) R. exact R. Qed.
Lemma R_a3 : getr (ms_regs ms1) 13 = w64 cl. Proof. rreg HSC (13%bv : bv 5) R. rewrite R, Em39. reflexivity. Qed.
Lemma SP1 : spZ (ms_regs ms1) = sp0 - 2320.
Proof. unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small. pose proof Usp. pose proof Hsp. pose proof STK. unfold ASTACK, kHighMemBeg in *. lia. Qed.
Lemma UNW1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (T + t_unwinding) 1 0.
Proof.
pose proof T_range as [T1 T2].
memv HSC 41%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite Em32; unfold w64, t_unwinding; rewrite unsigned_lit_small by (ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); reflexivity
| reflexivity | cbn; lia].
Qed.
Lemma UNW_cell : forall Sx rd, ARm B ly Sx rd -> rd (T + t_unwinding) = Some 0.
Proof.
intros Sx rd M. assert (IN : In (z1 (AT t_unwinding) 0) (acells B ly Sx)).
{ unfold acells. repeat (apply in_app_iff; right). left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M) _ IN 0%nat ltac:(cbn; lia)) as X. cbn [c_at c_w aeval z1 c1] in X.
rewrite Z.add_0_r in X. exact X.
Qed.
Lemma AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros a Ha Hs. destruct (Z.eq_dec a (T + t_unwinding)) as [->|Hne].
- assert (OU : AllocR.offU UP (T + t_unwinding)) by (apply offU_T; unfold kThreadObjSize, t_unwinding; lia).
  rewrite <- (AllocR.aview_unpoison (w_H W) UP mem0 _ OU).
  rewrite (UNW_cell S1 _ HARm1u).
  pose proof (Dm.val_mem_aview (w_H W) (ms_mem ms1) (T + t_unwinding) 1 0 0 UNW1 ltac:(lia)) as X.
  rewrite Z.add_0_r in X. rewrite X. reflexivity.
- apply aview_same. apply MEQW. rewrite unsigned_lit_small by exact Ha. unfold YFiu.WINM. fold sp0. unfold T in Hne. clear - Hs Hne. lia.
Qed.
Lemma ARUms1 : FSP.ARU tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1).
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof T_range as [T1 T2].
apply (FSP.ARU_frame tfibsegs B (AR_laws_ok tfibsegs B) ly S1 UP W mem0 md0 (ms_mem ms1) (md0' mat1) HARU1).
- intros a Ha Ho. apply AG1; [exact Ha|]. intros Hst.
  apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison UP mem0) md0 a HAR1u); [clear - Hst Hlo Hhi; unfold ASTACK in *; lia | exact Ho].
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (AV : forall m, aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
  rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  destruct (Z_lt_le_dec a' (sp0 - ASTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a' sp0) as [H2|H2]].
  2:{ apply Dm.apresent_aview_some; [clear - H1 H2 K1 Ha' Hlo; unfold TFIB_IMG_END, kHighMemBeg, ASTACK in *; lia | apply PRESW; lia]. }
  all: rewrite (AG1 a' Ha' ltac:(lia)); exact Hv.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. rewrite (MEQW (w64 a)); [reflexivity|].
  assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
  unfold w64. rewrite unsigned_lit_small by exact Ha'. unfold YFiu.WINM. fold sp0.
  pose proof (zone3_apart_hsh _ _ a T1) as TH. unfold T in TH. clear - Ha K1 Hlo TH.
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, kThreadObjSize in *. lia.
Qed.
Lemma AR1u : AR tfibsegs B ly S1 W (FSP.unpoison UP (ms_mem ms1)) (md0' mat1).
Proof. exact (FSP.ARU_AR tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1) ARUms1). Qed.
Lemma REFILL_PREu : AllocR.refill_preU B ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
pose proof HAR0u as (_ & _ & [BUD _] & _).
unfold AllocR.refill_preU.
split; [|split; [exact (FSP.ARU_ok tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1) ARUms1)
               | exact (FSP.ARU_poisoned tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1) ARUms1)]].
unfold refill_pre. rewrite SP1. unfold raZ. rewrite R_ra, R_gp, R_tp, R_a0, R_a1, R_a2, R_a3, Hgp, (ts_tp B TS).
split; [exact AR1u|].
split; [unfold abudget in *; cbn [st_nev set_nev S1]; change (sec_live_bytes S1) with (sec_live_bytes S); change (sec_hulls S1) with (sec_hulls S); unfold EV_A in *; lia|].
split; [split; [pose proof (wf_prim_ev _ _ _ _ _ WfP1) as PE; cbn [st_nev set_nev S1] in PE |- *; change (prim_user_mapped S1) with (prim_user_mapped S) in *; lia|];
split; [exact (aregime_preg_tick S cl Hev Hcl) | exact (aregime_mid_tick S Hev)]|].
split; [split; [apply qtight_qloose; exact (qmeter_tight _ HQT) | apply (rroom_tick S); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (qmeter_room _ HQT)]]|].
split; [apply ret_ok_even; reflexivity|]. split; [unfold w64; rewrite unsigned_lit_small by lia; lia|].
split; [clear - Hal; replace (sp0 - 2320) with (sp0 + (-145) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [clear - Hlo; unfold ASTACK, RSTACK in *; lia|]. split; [lia|].
split; [intros a Ha; apply AllocR.apresent_to_unpoison; apply PRESW; clear - Ha; unfold ASTACK, RSTACK in *; lia|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hcl | exact Hmiss1].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1c. After the refill. Port-from: lib/B/YFim.v section g.                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section gg.
Variables (S' : astate) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis WFP' : WfP (as_universe B) 0 1 1 S'.
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : FSU.acall_postU tfibsegs B RSTACK ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Let msR : machine_state := mkst regsR (w64 RA_REFILL) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).

Lemma POSTd : acall_post tfibsegs B RSTACK ly S1 W (ms_regs ms1) (FSP.unpoison UP (ms_mem ms1)) (md0' mat1) (fun _ => False) ly S' W' regsR (FSP.unpoison UP memR) mdR.
Proof. exact (proj1 POST). Qed.
Lemma HAR'u : AR tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR. Proof. exact (proj1 POSTd). Qed.
Lemma HARm'u : ARm B ly S' (aview tfibsegs (w_H W') (FSP.unpoison UP memR)). Proof. exact (proj1 HAR'u). Qed.
Lemma HARU' : FSP.ARU tfibsegs B ly S' UP W' memR mdR.
Proof. split; [exact HAR'u|]. split; [exact (proj1 (proj2 POST)) | exact (proj2 (proj2 POST))]. Qed.
Lemma WLE : wle W W'. Proof. exact (proj1 (proj2 (proj2 POSTd))). Qed.
Lemma ERRNO_low : as_errno B + 4 <= kHighMemBeg.
Proof. rewrite (ts_errno B TS). unfold TFIB_ERRNO, kHighMemBeg. lia. Qed.
Lemma AGR : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2320 - RSTACK <= a < sp0 - 2320) ->
aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Proof.
intros a Ha Hns. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof ERRNO_low as EL.
assert (OU : AllocR.offU UP a) by (apply (AllocR.stack_offU B ly S' UP W' memR mdR a HARU'); unfold ASTACK in *; lia).
rewrite <- (AllocR.aview_unpoison (w_H W') UP memR a OU), <- (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU).
destruct POSTd as (_ & _ & _ & _ & _ & FR & _). apply FR.
- clear - Ha Hlo K1 U. unfold ASTACK, kHighMemBeg in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison UP (ms_mem ms1)) (md0' mat1) a AR1u). clear - Ha Hlo Hhi. unfold ASTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a HAR'u). clear - Ha Hlo Hhi. unfold ASTACK in *. lia.
- unfold ascratch. rewrite SP1. intros [X|X]; [exact (Hns X)|]. clear - X Ha Hlo K1 EL. unfold ASTACK, kHighMemBeg in *. lia.
- intros [].
Qed.
Lemma PRES' : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
assert (Hhi' : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha Hlo K1 U; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia).
destruct (Z_lt_le_dec a (sp0 - 2320 - RSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a (sp0 - 2320)) as [H2|H2]].
- apply (Dm.apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply AGR; [exact Ha | lia] | apply PRESW; exact Ha].
- assert (OU : AllocR.offU UP a) by (apply (AllocR.stack_offU B ly S' UP W' memR mdR a HARU'); unfold ASTACK in *; lia).
  apply (AllocR.apresent_of_unpoison (w_H W') UP memR a OU).
  destruct POSTd as (_ & _ & _ & _ & _ & _ & PRS). apply PRS. rewrite SP1. lia.
- apply (Dm.apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply AGR; [exact Ha | lia] | apply PRESW; exact Ha].
Qed.
Lemma BUF' : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') memR) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof.
intros i Hi. pose proof (@YFis.tr_length ly regs0 mem0 n ch 0 kz DPOSTm) as LEN. change (YFis.tr ly regs0 ch) with tr in LEN.
eapply Dm.val_mem_aview_xfer; [|exact (BUFW i Hi)]. intros k Hk. apply AGR; clear - Hi Hk LEN; unfold IFRAME, ASTACK, RSTACK in *; lia.
Qed.
(* The caller's frame-pointer chain survives the refill: it is read from the stack above sp0 only. *)
Lemma AGtop : forall a, sp0 <= a < ly_top ly -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros a Ha. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof ERRNO_low as EL.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha U T2 K2; unfold kHighMemEnd in *; lia).
assert (OU : AllocR.offU UP a) by (apply (AllocR.stack_offU B ly S' UP W' memR mdR a HARU'); unfold ASTACK in *; lia).
rewrite <- (AllocR.aview_unpoison (w_H W') UP memR a OU).
rewrite <- (AG1 a Ra ltac:(clear - Ha; lia)), <- (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU).
destruct POSTd as (_ & _ & _ & _ & _ & FR & _). apply FR.
- clear - Ha Hlo K1 U T2 K2. unfold kHighMemEnd, kHighMemBeg in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison UP (ms_mem ms1)) (md0' mat1) a AR1u). clear - Ha Hlo T2. unfold ASTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a HAR'u). clear - Ha Hlo T2. unfold ASTACK in *. lia.
- unfold ascratch. rewrite SP1. intros [X|X]; [clear - X Ha; unfold RSTACK in *; lia|]. clear - X Ha Hlo K1 EL. unfold kHighMemBeg, ASTACK in *. lia.
- intros [].
Qed.
Lemma Hch' : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W') memR)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof.
pose proof Hch as H. destruct (sp0 + 16 <? ly_top ly); [|exact H].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:BN; [exact H|].
destruct H as [H1 H2]. split; [exact H1|].
unfold bad_next in BN. apply orb_false_iff in BN as [BN1 BN3]. apply orb_false_iff in BN1 as [BN1 BN2].
apply Z.leb_gt in BN1. apply Z.leb_gt in BN2.
apply (fpchain_bytes (aview tfibsegs (w_H W) mem0) (aview tfibsegs (w_H W') memR) sp0 (ly_top ly) ch
  (bv_unsigned (getr regs0 8))).
- exact AGtop.
- exact H1.
- lia.
- exact H2.
Qed.
Let E1 : env := havoc Em hRF (map (getr regsR) CLOB).
Lemma Em2u : bv_unsigned (ew Em 2) = sp0. Proof. rewrite Em2. reflexivity. Qed.
Lemma KEPT3 : Forall (region_kept tfibsegs Em (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W') memR)) RS3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
assert (A : forall a, sp0 - 2320 <= a < sp0 -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a)
by (intros a Ha; apply AGR; clear - Ha; unfold ASTACK, RSTACK; lia).
unfold RS3. repeat (apply Forall_cons; [eapply (Dm.region_kept_view (w_H W) (w_H W') Em (ms_mem ms1) memR 2 _ _ _ _ _ sp0 Em2u);
[intros a Ha; apply A; clear - Ha; lia | clear - Hlo K1; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia | clear - U; lia | clear; intros a Ha; lia] |]).
apply Forall_nil.
Qed.
Let ms3 : machine_state := mkst regsR (w64 RA_REFILL) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Lemma HS3 : st_ok tfibsegs E1 SS3 ms3.
Proof.
rewrite SS3_eq. pose proof MS_CALL_facts as (F1 & F2 & F3 & F4 & F5 & F6). destruct MS_CALL_mem3 as [rest ER].
apply (st_ok_after_call tfibsegs hRF Em MS_CALL (mkst (ms_regs ms1) (w64 PC_REFILL) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs))
regsR (mrestrict (w_H W') memR) RS3 RA_REFILL HSC' F6 F1 F2 F3 F4).
- rewrite ER. change RS3 with [R3bst; trim_lo R3scr (-2320); R3top].
apply submem_keep; [apply Dm.subregion_refl|]. apply submem_keep; [apply subregion_trim_lo|]. apply submem_keep; [apply Dm.subregion_refl|]. apply submem_nil.
- exact F5.
- destruct POSTd as (_ & _ & _ & CS & _). intros r Hr. apply CS. exact Hr.
- exact KEPT3.
Qed.

Section gj.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA0 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => YFix.DPOST3 W' ly regs0 ch B S' z m.
Lemma Hcnt_def' : cnt' = Z.of_nat (length (l ++ [off])). Proof. reflexivity. Qed.
Lemma Hoffv' : off = 16 * v' /\ v' mod 2 = 0.
Proof.
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm'u) cl Hcl) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache' in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(rewrite !in_app_iff; cbn; tauto)) as [_ O2].
pose proof (class_ok cl Hcl) as (K1 & K2 & _). apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [r Hr]; [|lia].
subst v'. rewrite Hq, Hr. replace (q * (r * 32)) with ((2 * q * r) * 16) by lia. rewrite Z.div_mul by lia. split; [lia|].
rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma Hoff_def' : off = 16 * v'. Proof. exact (proj1 Hoffv'). Qed.
Lemma Hv2' : v' mod 2 = 0. Proof. exact (proj2 Hoffv'). Qed.
Lemma Hv' : 0 <= v' /\ 16 * v' + 2 ^ 16 <= 2 ^ 32.
Proof. exact (@YFiy.Hv' _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' kz Hv2' DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def'). Qed.
Lemma Hcnt' : 1 <= cnt' <= 16.
Proof. exact (@YFiy.Hcnt' _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' kz Hv2' Hsp DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def'). Qed.

(* The new chunk and its shadow are off UP: the chunk is high application memory, and its shadow bytes read 250. *)
(* Port-from: lib/B/FSupoisonAllocMp2.v:183-201 (OKv / OKS of malloc_hitgU), at the state the refill left. *)
Lemma OKv' : forall a, YFis.Kv ly cl v' <= a < YFis.Kv ly cl v' + csz -> AllocR.offU UP a.
Proof.
intros a Ha. pose proof (@YFis.derived_ranges _ ly regs0 memR n cl cnt' v' kz Hcl Hv' Hcnt' Hv2' LY IMG DPOST' Hkz1 Nrange) as DR.
pose proof (@YFiy.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' kz DPOST' Hkz1 Nrange l off Hcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
apply (Mp1.offU_hi B ly S' UP W' memR mdR a HARU').
ceil. unfold kHighMemBeg, ASAN_CEIL, kMaxSize in *. rewrite Hcsz_def in Ha. lia.
Qed.
Lemma OKS' : forall g, g mod 8 = 0 -> YFis.Kv ly cl v' <= g < YFis.Kv ly cl v' + csz -> AllocR.offU UP (shadow_addr g).
Proof.
intros g G8 Hg. pose proof (@YFis.derived_ranges _ ly regs0 memR n cl cnt' v' kz Hcl Hv' Hcnt' Hv2' LY IMG DPOST' Hkz1 Nrange) as DR.
pose proof (@YFiy.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' kz DPOST' Hkz1 Nrange l off Hcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
apply (AllocR.offU_nonzero B ly S' UP W' memR mdR (shadow_addr g) 250 HARU').
- unfold shadow_addr. ceil.
  pose proof (Z.div_pos g 8 ltac:(unfold kHighMemBeg in *; lia) ltac:(lia)) as D1'.
  pose proof (Z.div_le_upper_bound g 8 (2 ^ 44) ltac:(lia) ltac:(unfold ASAN_CEIL, kMaxSize in *; rewrite Hcsz_def in Hg; lia)) as D2'.
  unfold SHADOW_OFF. lia.
- exact (@YFiy.shadow250 _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kz Hv2' LY Hsp DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def g G8 ltac:(rewrite <- Hcsz_def; exact Hg)).
- lia.
- lia.
Qed.
Lemma SHK' : forall j, shadow_addr (YFis.Kv ly cl v' + 8 * j) = YFis.SKv ly cl v' + j.
Proof.
intros j. pose proof (@YFis.derived_ranges _ ly regs0 memR n cl cnt' v' kz Hcl Hv' Hcnt' Hv2' LY IMG DPOST' Hkz1 Nrange) as DR.
pose proof (Z.div_mod (YFis.Kv ly cl v') 16 ltac:(lia)) as DK.
unfold shadow_addr, YFis.SKv, YFis.SHBv, SHADOW_OFF.
replace (YFis.Kv ly cl v' + 8 * j) with ((YFis.Kv ly cl v' / 16 * 2 + j) * 8) by lia.
replace (YFis.Kv ly cl v') with (YFis.Kv ly cl v' / 16 * 2 * 8) at 2 by lia.
rewrite !Z.div_mul by lia. lia.
Qed.
Lemma HKpres' : forall a, YFis.Kv ly cl v' <= a < YFis.Kv ly cl v' + YFis.RZ kz + YFis.R8v n -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof (@YFis.derived_ranges _ ly regs0 memR n cl cnt' v' kz Hcl Hv' Hcnt' Hv2' LY IMG DPOST' Hkz1 Nrange) as DR.
pose proof (@YFiy.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' kz DPOST' Hkz1 Nrange l off Hcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
apply (AllocR.apresent_of_unpoison (w_H W') UP memR a ltac:(apply OKv'; rewrite Hcsz_def; lia)).
exact (@YFiy.KPRES _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kz Hv2' LY Hsp DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def a Ha).
Qed.
Lemma HSKpres' : forall a, YFis.SKv ly cl v' <= a < YFis.SKv ly cl v' + (YFis.RZ kz + YFis.R8v n) / 8 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof (@YFis.derived_ranges _ ly regs0 memR n cl cnt' v' kz Hcl Hv' Hcnt' Hv2' LY IMG DPOST' Hkz1 Nrange) as DR.
pose proof (@YFiy.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' kz DPOST' Hkz1 Nrange l off Hcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (Z.div_mod (YFis.Kv ly cl v') 16 ltac:(lia)) as DK.
apply (AllocR.apresent_of_unpoison (w_H W') UP memR a
  ltac:(replace a with (shadow_addr (YFis.Kv ly cl v' + 8 * (a - YFis.SKv ly cl v'))) by (rewrite SHK'; lia);
        apply OKS'; [replace (YFis.Kv ly cl v' + 8 * (a - YFis.SKv ly cl v')) with ((YFis.Kv ly cl v' / 16 * 2 + (a - YFis.SKv ly cl v')) * 8) by lia; apply Z.mod_mul; lia
                   | rewrite Hcsz_def; pose proof (Z.mul_div_le (YFis.RZ kz + YFis.R8v n) 8 ltac:(lia)); lia])).
exact (@YFiy.SKPRES _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kz Hv2' LY IMG Hsp DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def a Ha).
Qed.
Lemma HPB250' : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W') memR) (YFis.PBv ly n cl v' kz) 1 250.
Proof.
intros E8. pose proof (@YFis.derived_ranges _ ly regs0 memR n cl cnt' v' kz Hcl Hv' Hcnt' Hv2' LY IMG DPOST' Hkz1 Nrange) as DR.
pose proof (@YFiy.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' kz DPOST' Hkz1 Nrange l off Hcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (Z.div_mod (YFis.Kv ly cl v') 16 ltac:(lia)) as DK.
apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (YFis.PBv ly n cl v' kz) 1 250).
- intros k Hk. replace (YFis.PBv ly n cl v' kz + Z.of_nat k) with (shadow_addr (YFis.Kv ly cl v' + YFis.RZ kz + YFis.N8D n)).
  2:{ replace (Z.of_nat k) with 0 by lia. rewrite Z.add_0_r.
      unfold shadow_addr, YFis.PBv, YFis.SHBv, SHADOW_OFF. reflexivity. }
  apply OKS'.
  + unfold YFis.N8D. pose proof (Z.div_mod n 8 ltac:(lia)).
    replace (YFis.Kv ly cl v' + YFis.RZ kz + n / 8 * 8) with ((YFis.Kv ly cl v' / 16 * 2 + YFis.RZ kz / 8 + n / 8) * 8) by lia.
    apply Z.mod_mul. lia.
  + rewrite Hcsz_def. unfold YFis.N8D in *. pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
- exact (@YFiy.PB250 _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kz Hv2' LY IMG Hsp DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def E8).
Qed.
(* The junk the walk reads off the thread object and the new chunk, on the REAL memory. *)
Lemma junk_real : exists j0 j1 j2 j3 j4 jb,
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2784) 8 j0 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2800) 8 j1 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2808) 8 j2 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2816) 8 j3 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (YFis.SSLOTv ly cl) 8 j4 /\
  0 <= jb <= 255 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (YFis.Kv ly cl v' + YFis.RZ kz - 15) 1 jb.
Proof.
pose proof (@YFis.derived_ranges _ ly regs0 memR n cl cnt' v' kz Hcl Hv' Hcnt' Hv2' LY IMG DPOST' Hkz1 Nrange) as DR.
pose proof (@YFiy.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' kz DPOST' Hkz1 Nrange l off Hcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
assert (OT : forall a, T <= a < T + kThreadObjSize -> AllocR.offU UP a).
{ intros a Ha. apply (Mp1.offU_owned B ly S' UP W' memR mdR (ly_T ly, kThreadObjSize) a HARU'
    ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. unfold T in Ha. exact Ha. }
destruct (@YFiy.junk_values _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kz Hv2' LY IMG Hsp DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0u & Hj1u & Hj2u & Hj3u & Hj4u & Hjb & Hjbu).
exists j0, j1, j2, j3, j4, jb.
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2784) 8 j0); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj0u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2800) 8 j1); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj1u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2808) 8 j2); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj2u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2816) 8 j3); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj3u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (YFis.SSLOTv ly cl) 8 j4);
        [intros k Hk; apply OT; unfold YFis.SSLOTv, T, kThreadObjSize, t_stats in *; pose proof Hcl; lia | exact Hj4u]|].
split; [exact Hjb|].
apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (YFis.Kv ly cl v' + YFis.RZ kz - 15) 1 jb);
  [intros k Hk; apply OKv'; rewrite Hcsz_def; lia | exact Hjbu].
Qed.

Section gk.
Variables (j0 jb j1 j2 j3 j4 : Z).
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W') memR) (YFis.SSLOTv ly cl) 8 j4.
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (YFis.Kv ly cl v' + YFis.RZ kz - 15) 1 jb.
Let E0' : env := YFis.E0 ly regs0 n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz.
Let Es : env := env_merge PND E1 E0'.
Lemma HEs : forall k, (k < aHAV)%nat -> ew Es k = ew E0' k.
Proof.
intros k Hk. unfold aHAV in Hk. destruct (PND k) eqn:HP.
- unfold Es. rewrite (ew_merge_in PND E1 E0' k HP). unfold E1. rewrite ew_havoc_old by (unfold hRF; lia).
rewrite (HEm k Hk). unfold E0m, E0'. apply Dm.E0_nondummy; [exact Hk | exact HP].
- unfold Es. apply ew_merge_out. exact HP.
Qed.
Lemma AGs : env_agree 64 E0' Es.
Proof. split; [exact HEs | reflexivity]. Qed.
Lemma Es2 : bv_unsigned (ew Es 2) = sp0. Proof. rewrite (HEs 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma FACTS' : atoms_ok E0' (f_atoms FG).
Proof.
exact (@YFj0.FACTS_ok _ W' ly regs0 (FSP.unpoison UP memR) n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Hsp DPOST' Hkz1 Nrange B S' l off HARm'u CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def).
Qed.
(* The donor's seed on the real memory: FSupoisonAllocMp2.SEEDr, at the state the refill left. *)
Lemma SEED' : st_ok tfibsegs E0' SS0 (restrict (w_H W') (mkst regs0 (w64 PC_WRAP_MALLOC) memR (seg_rom tfibsegs))).
Proof.
exact (Mp2.SEEDr W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz B S' l off UP DPOST'
  Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Htp Hsp HKpres' HSKpres' HPB250' Hkz1 Nrange Hcl_def TS HTSD HARU' PRES'
  CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Qed.
Lemma MEMOK' : mem_ok tfibsegs E0' (mrestrict (w_H W') memR) REG0.
Proof.
destruct SEED' as (_ & _ & _ & _ & _ & _ & _ & X8 & _). exact X8.
Qed.
Lemma REG0' : Forall (region_ok tfibsegs E0' (mrestrict (w_H W') memR)) REG0.
Proof. exact (proj1 (proj2 MEMOK')). Qed.
Lemma PAIRS' : pairwise_disjoint E0' REG0.
Proof. exact (proj2 (proj2 MEMOK')). Qed.
Lemma HS4 : st_ok tfibsegs Es SS3 ms3.
Proof.
pose proof SS3_atoms as (A1 & A2 & A3 & A4 & A5). pose proof tlREG0_facts as (_ & _ & T3).
apply (st_ok_agree_on2 tfibsegs PND E1 Es SS3 ms3 HS3 (env_merge_on PND E1 E0') A1 A2 A3 A4).
rewrite A5. exact (atoms_ok_agree 64 E0' Es _ AGs T3 FACTS').
Qed.
Lemma HS5 : st_ok tfibsegs Es (mkSS (ss_pc SS3) (sr_set (ss_regs SS3) 10%bv (SLit 1)) (ss_mem SS3) (ss_resv SS3) (ss_facts SS3)) ms3.
Proof.
apply (st_ok_pin_regU Es SS3 ms3 10%bv (SLit 1) HS4); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs Es SS3 ms3 10%bv HS4) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity.
Qed.
Lemma region_ok_agree_on_lt : forall r, In r (tl REG0) -> region_ok tfibsegs E0' (mrestrict (w_H W') memR) r -> region_ok tfibsegs Es (ms_mem ms3) r.
Proof.
intros r Hr H. pose proof tlREG0_facts as (T1 & _). unfold ms3. cbn [ms_mem mkst].
apply (region_ok_agree tfibsegs 64 E0' Es _ r AGs); [|exact H]. exact (proj1 (forallb_forall _ _) T1 r Hr).
Qed.
Lemma HS6 : st_ok tfibsegs Es (mkSS RA_REFILL (sr_set (ss_regs SS3) 10%bv (SLit 1)) [R3bst; R3scr; R3top] None (ss_facts SS3)) ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
pose proof (st_ok_mem_surgery Es _ ms3 [R3bst; R3scr; R3top] HS5) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val Es (Some 2%nat) = sp0) by (cbn [base_val]; exact Es2).
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons; [|exact (Forall_inv_tail (Forall_inv_tail HF))].
pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, R3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; lia|]. split; [clear - U; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 U; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia|]. apply PRES'. clear - Ho; unfold ASTACK; lia.
- unfold R3bst, R3scr, R3top. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV. repeat split; lia.
Qed.
Lemma HS7 : st_ok tfibsegs Es MS_AFTER ms3.
Proof.
rewrite MS_AFTER_eq3. pose proof tlREG0_facts as (T1 & T2 & T3).
pose proof (st_ok_mem_surgery Es _ ms3 ([R3bst; R3scr; R3top] ++ tl REG0) HS6) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros HM. pose proof PAIRS' as PP. change REG0 with (hd R_bst REG0 :: tl REG0) in PP. destruct PP as [A0 PT].
pose proof REG0' as RR. change REG0 with (hd R_bst REG0 :: tl REG0) in RR. apply Forall_inv_tail in RR.
apply mem_ok_app; [exact HM | exact T2 | | |].
- apply Forall_forall. intros r Hr. apply (region_ok_agree_on_lt r Hr). exact (proj1 (Forall_forall _ _) RR r Hr).
- exact (pairwise_disjoint_agree 64 E0' Es (tl REG0) AGs T1 PT).
- intros r Hr. pose proof (all_disjoint_In E0' _ _ r A0 Hr) as D0.
assert (Hb : obase_lt 64 (YP09.r_base r) = true).
{ pose proof (proj1 (forallb_forall _ _) T1 r Hr) as Ha. unfold region_atoms_lt in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
pose proof (extent_disjoint_agree 64 E0' Es (hd R_bst REG0) r AGs eq_refl Hb D0) as D. clear D0.
cbn [all_disjoint]. repeat split; apply extent_disjoint_sym;
(eapply (Dm.extent_disjoint_sub Es (hd R_bst REG0) r); [reflexivity | cbn; unfold ASTACK; lia | cbn; lia | cbn; lia | exact D]).
Qed.
Lemma ATJ : YFis.at_ST W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz MS_AFTER W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), Es. split; [reflexivity|]. split; [exact HEs|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HS7|].
split; [intros x _; reflexivity|]. split; [exact PRES' | exact BUF'].
Qed.
Lemma TAILJ : amreal tfibsegs (malloc_join n tr cl S') W' (cfg_at tfibsegs RA_REFILL regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> FSU.malloc_leafU tfibsegs B ly S' UP W' regs0 memR mdR n r W'' c'').
Proof.
replace (cfg_at tfibsegs RA_REFILL regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@YFit.segJ _ _ W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hv2' LY IMG Hsp DPOST' Hkz1 Nrange l off W' cR ATJ). }
intros W2 c2 _ HJ. pose proof (proj1 HJ) as EW. subst W2.
exact (Mp2.tail_innerU W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz B S' l off UP DPOST'
  Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Htp Hsp HKpres' HSKpres' HPB250' Hkz1 Nrange Hcl_def TS HTSD HARU' PRES'
  CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def
  (m_vm_materialized mdR) Hra Hra4096 Hch' U1 Hgp (tr_admit_len _ _ _ (ts_universe B TS) Htr) D1 (fun z m H => H) (fun z m H => H) eq_refl
  c2 HJ).
Qed.
End gk.
End gj.
End gg.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1d. After a refill that did not fill the cache: the out-of-memory return. Port-from: lib/B/YFim.v section h.      *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section gh.
Variables (S' : astate) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis WFP' : WfP (as_universe B) 0 1 1 S'.
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : FSU.acall_postU tfibsegs B RSTACK ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.
Let msR : machine_state := mkst regsR (w64 RA_REFILL) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Let ms3 : machine_state := mkst regsR (w64 RA_REFILL) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Let E1 : env := havoc Em hRF (map (getr regsR) CLOB).
Lemma HE1 : forall k, (k < aHAV)%nat -> ew E1 k = ew E0m k.
Proof. intros k Hk. unfold E1. unfold aHAV in Hk. rewrite ew_havoc_old by (unfold hRF; lia). apply HEm. exact Hk. Qed.
Lemma E1_2 : bv_unsigned (ew E1 2) = sp0. Proof. rewrite (HE1 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma HSN : st_ok tfibsegs E1 MS_N0 ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us.
pose proof (HS3 S' W' regsR memR mdR WFP' RO CI POST) as H3. fold E1 in H3. change (mkst regsR (w64 RA_REFILL) (mrestrict (w_H W') memR) (seg_rom tfibsegs)) with ms3 in H3.
assert (H4 : st_ok tfibsegs E1 (mkSS (ss_pc SS3) (sr_set (ss_regs SS3) 10%bv (SLit 0)) (ss_mem SS3) (ss_resv SS3) (ss_facts SS3)) ms3).
{ apply (st_ok_pin_regU E1 SS3 ms3 10%bv (SLit 0) H3); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs E1 SS3 ms3 10%bv H3) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity. }
rewrite MS_N0_eq. pose proof (st_ok_mem_surgery E1 _ ms3 ([R3bst; R3scr; R3top] ++ NREGS) H4) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X H4 H3.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val E1 (Some 2%nat) = sp0) by (cbn [base_val]; exact E1_2).
pose proof (PRES' S' W' regsR memR mdR WFP' RO CI POST) as PR.
assert (OOM1 : val_mem tfibsegs (mrestrict (w_H W') memR) (TFIB_OOM + 1) 1 1).
{ assert (OU : AllocR.offU UP (TFIB_OOM + 1)) by (apply offU_lo; unfold TFIB_OOM, SHADOW_OFF; lia).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (HARm'u S' W' regsR memR mdR WFP' RO CI POST)) (z1 (ANum (TFIB_OOM + 1)) 1)) as C.
rewrite (ts_const B TS ly) in C. specialize (C ltac:(unfold Tfib_const; apply in_app_iff; right; apply in_app_iff; left; apply (nth_error_In _ 60); reflexivity)).
apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (TFIB_OOM + 1) 1 1); [intros k Hk; replace (Z.of_nat k) with 0 by lia; rewrite Z.add_0_r; exact OU|].
exact (cell_holds_val_mem B ly (w_H W') (FSP.unpoison UP memR) (ANum (TFIB_OOM + 1)) 1 (ANum 1) C). }
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons.
{ pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, R3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; lia|]. split; [clear - Us; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 Us; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia|]. apply PR. clear - Ho; unfold ASTACK; lia. }
apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HF)))|].
unfold NREGS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ unfold region_ok, lit1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia |]. rewrite Z.add_0_l. exact OOM1.
+ unfold region_ok, oomR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply (Dm.rw_writable ly regs0 n). unfold TFIB_OOM in *. lia.
+ unfold region_ok, errR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_ERRNO; lia|]. split; [unfold TFIB_ERRNO; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply (Dm.rw_writable ly regs0 n). unfold TFIB_ERRNO in *. lia.
- unfold R3bst, R3scr, R3top, NREGS, lit1, oomR, errR. cbn [pairwise_disjoint all_disjoint app]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BV. cbn [base_val]. clear - Hlo K1 Us. unfold TFIB_OOM, TFIB_ERRNO, ASTACK, kHighMemBeg in *. repeat split; lia.
Qed.
Lemma ATN : YFiv.at_STN W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 kz MS_N0 W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), E1. split; [reflexivity|]. split; [exact HE1|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HSN|]. split; [reflexivity | exact (PRES' S' W' regsR memR mdR WFP' RO CI POST)].
Qed.
Lemma errno_not_owned : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S' a.
Proof.
intros a Ha O. pose proof (HAR'u S' W' regsR memR mdR WFP' RO CI POST) as AR'.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. rewrite YB13.tfib_segs_eq.
eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. lia. }
apply (proj1 (AR_owned_image_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a AR' IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.
Lemma oom_owned : aowned B ly S' TFIB_OOM.
Proof.
apply (own_area B ly S' _ (as_oom_byte B, 1) TFIB_OOM (HARm'u S' W' regsR memR mdR WFP' RO CI POST)); [unfold asyms_areas; cbn; tauto|].
cbn [fst snd]. rewrite (ts_oom B TS). lia.
Qed.
Lemma TAILN : amreal tfibsegs (malloc_join n tr cl S') W' (cfg_at tfibsegs RA_REFILL regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W'' c'').
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us.
pose proof (ERRNO_low S' W' regsR memR mdR WFP' RO CI POST) as EL.
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K. cbn [amreal].
replace (cfg_at tfibsegs RA_REFILL regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono.
{ exact (@YFiv.segN _ _ W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 kz Hvd LY IMG Htp Hra Hsp DPOSTm [] 0 W' cR ATN). }
intros W6 c6 _ HR [WF' QT']. cbn [fst snd] in WF', QT' |- *.
destruct HR as (-> & regs' & mem' & mat & -> & A0 & CS' & MEQ' & PRS' & VOOM & VERR).
pose proof (POSTd S' W' regsR memR mdR WFP' RO CI POST) as (AR' & _ & WLE' & CS & SIO & FR & _).
pose proof (HARm'u S' W' regsR memR mdR WFP' RO CI POST) as M'.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy mdR) mat mdR).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [|split; [rewrite A0; cbn [sptr_addr sptr_exp aeval]; reflexivity | exact QT']].
assert (NWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> mem' (Z_to_bv 64 a) = memR (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3. apply MEQ'. rewrite unsigned_lit_small by exact Ra. unfold YFiv.WINN. fold sp0. clear - N1 N2 N3. unfold IFRAME, ASTACK in *. lia. }
assert (NWINu : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
  FSP.unpoison UP mem' (Z_to_bv 64 a) = FSP.unpoison UP memR (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned (Z_to_bv 64 a))); [reflexivity | exact (NWIN a Ra N1 N2 N3)]. }
split; [|split].
2:{ exact (proj1 (proj2 POST)). }
2:{ intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S' UP W' memR mdR s (HARU' S' W' regsR memR mdR WFP' RO CI POST) Hs) as (_ & L1 & L2).
  rewrite (FSP.aview_at tfibsegs (w_H W') mem' memR s
    (NWIN s ltac:(unfold SHADOW_OFF, kHighMemBeg in *; lia) ltac:(clear - L1 L2 Hlo K1; unfold ASTACK, kHighMemBeg, SHADOW_OFF in *; lia)
          ltac:(clear - L1; unfold TFIB_OOM, SHADOW_OFF in *; lia) ltac:(clear - L1; unfold TFIB_ERRNO, SHADOW_OFF in *; lia))).
  exact ((proj2 (proj2 POST)) s Hs). }
split.
{
apply (YFi5.AR_oom B ly S' W' (FSP.unpoison UP memR) (FSP.unpoison UP mem') mdR (with_vm_backing (m_vm_lazy mdR) mat mdR) TS AR').
- intros a Ra Ho NX. apply FSP.aview_at. apply NWINu; [exact Ra | | clear - NX; unfold YFi5.XJ in NX; lia |].
  + intros ST. exact (AR_stack_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a AR' ltac:(clear - ST Hlo Hhi; unfold ASTACK in *; lia) Ho).
  + intros ER. exact (errno_not_owned a ER Ho).
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (AV : forall m, aview tfibsegs (w_H W') m a = aview tfibsegs (w_H W') m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
  rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  destruct (Z_le_gt_dec (sp0 - ASTACK) a') as [G1|G1]; [destruct (Z_lt_ge_dec a' sp0) as [G2|G2]|].
  { apply Dm.apresent_aview_some; [clear - G1 G2 K1 Ha' Hlo; unfold TFIB_IMG_END, kHighMemBeg, ASTACK in *; lia|].
    apply AllocR.apresent_to_unpoison. apply PRS'. lia. }
  all: destruct (Z.eq_dec a' TFIB_OOM) as [->|NO]; [apply Dm.aview_rw_some; unfold TFIB_OOM; lia|].
  all: destruct (Z_le_gt_dec TFIB_ERRNO a') as [G3|G3];
    [destruct (Z_lt_ge_dec a' (TFIB_ERRNO + 4)) as [G4|G4]; [apply Dm.aview_rw_some; unfold TFIB_ERRNO in *; lia|]|].
  all: rewrite (FSP.aview_at tfibsegs (w_H W') (FSP.unpoison UP mem') (FSP.unpoison UP memR) a' (NWINu a' Ha' ltac:(lia) NO ltac:(lia))); exact Hv.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. unfold YG0n.w64. apply NWINu.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
  + clear - Ha K1 Hlo. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. lia.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. lia.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. lia.
}
split; [apply layout_le_refl|].
split; [exact WLE'|].
split.
{
intros r Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - RR CS'. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst r; apply CS'; cbn [In];
repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ (Dm.same_io_wvb md0 mat1) SIO) (Dm.same_io_wvb mdR mat))|].
split; [|intros a Ha; apply AllocR.apresent_to_unpoison; apply PRS'; exact Ha].
intros a Ha NO NO' NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (intros O; apply NO; exact (proj1 (Dm.aowned_tick B ly S a) O)).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ; left; exact X).
assert (NER : ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4)) by (intros X; apply NS; unfold ascratch; right; rewrite (ts_errno B TS); exact X).
assert (NOO : a <> TFIB_OOM) by (intros ->; exact (NO' oom_owned)).
rewrite (FSP.aview_at tfibsegs (w_H W') (FSP.unpoison UP mem') (FSP.unpoison UP memR) a (NWINu a Ha NST NOO NER)).
rewrite (FR a Ha NO1 NO').
- assert (OU : AllocR.offU UP a) by (apply (AllocR.offU_not_owned B ly S1 UP W mem0 md0 a HARU1 Ha NO1)).
  rewrite (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU), (AllocR.aview_unpoison (w_H W) UP mem0 a OU).
  exact (AG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite SP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; apply NS; [left; clear - X; unfold ASTACK, RSTACK in *; lia | right; exact X].
- intros [].
Qed.
End gh.

(* The leaf of the inner walk is the caller's leaf: the refill kept every live block and every byte off the
   scratch window. Port-from: lib/B/YFim.v:602 SHIFT, with the memories read through UP. *)
Lemma SHIFTU : forall S' W' regsR memR mdR, regs_only S1 S' ->
FSU.acall_postU tfibsegs B RSTACK ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR ->
forall r W6 c6, FSU.malloc_leafU tfibsegs B ly S' UP W' regs0 memR mdR n r W6 c6 ->
FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W6 c6.
Proof.
intros S' W' regsR memR mdR RO POST r W6 c6 (ly' & regs' & mem' & md' & -> & AP & RA0 & QT).
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
assert (EL : as_errno B + 4 <= kHighMemBeg) by (rewrite (ts_errno B TS); unfold TFIB_ERRNO, kHighMemBeg; lia).
destruct AP as (AP6 & OK6 & PO6). destruct AP6 as (AR6 & LLE & WLE6 & CS6 & SIO6 & FR6 & PRS6).
destruct POST as (POSTd' & _ & _). destruct POSTd' as (AR' & _ & WLE' & _ & SIO & FR & _).
exists ly', regs', mem', md'. split; [reflexivity|]. split; [|split; [exact RA0 | exact QT]].
split; [|split; [exact OK6 | exact PO6]].
split; [exact AR6|]. split.
{ destruct RO as (_ & Rsecs & _). rewrite Rsecs in LLE. exact LLE. }
split; [exact (wle_trans _ _ _ _ WLE' WLE6)|]. split; [exact CS6|].
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ (Dm.same_io_wvb md0 mat1) SIO) SIO6)|]. split; [|exact PRS6].
intros a Ha NO NO6 NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (intros O; apply NO; exact (proj1 (Dm.aowned_tick B ly S a) O)).
assert (NO' : ~ aowned B ly S' a) by (intros O; apply NO1; exact (proj1 (Dm.aowned_regs_only B ly S1 S' a RO) O)).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ; left; exact X).
rewrite (FR6 a Ha NO' NO6 NS NE). rewrite (FR a Ha NO1 NO').
- assert (OU : AllocR.offU UP a) by (apply (AllocR.offU_not_owned B ly S1 UP W mem0 md0 a HARU1 Ha NO1)).
  rewrite (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU), (AllocR.aview_unpoison (w_H W) UP mem0 a OU).
  exact (AG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite SP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; apply NS; [left; clear - X; unfold ASTACK, RSTACK in *; lia | right; exact X].
- intros [].
Qed.
End gf.

Theorem malloc_missgU :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ HARm0u) Hev); [unfold MALLOC_MAX; lia | exact Hlive | exact Htr]. }
rewrite (malloc_primary_eq n tr S FP). eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
fold S1. change (chunk_class n) with cl.
eapply (YG0d.amreal_mbind tfibsegs (refill_tree cl) (fun _ : unit => malloc_join n tr cl) S1 W _
(fun r W' c' => exists ms1 mat1 Em,
((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em MS_CALL (restrict (w_H W) ms1) /\
(forall x : word, ~ YFiu.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
((WfP (as_universe B) (1 - 1) 1 1 (snd r) /\ regs_only S1 (snd r) /\ st_cache_inited (snd r) = true) /\
AllocR.refill_leafU B ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl r W' c'))).
-
eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
pose proof (Rt.tfib_refill_okU B TS ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl
  (REFILL_PREu ms1 mat1 Em HEm HSC MEQW PRESW BUFW)) as RR.
unfold cfg_at, A_Refill in RR. rewrite (ms1_shape ms1 mat1 Em HEm HSC MEQW PRESW BUFW) at 1.
change (md0' mat1) with (with_vm_backing (m_vm_lazy md0) mat1 md0) in RR at 1.
pose proof (refill_tree_apost (as_universe B) 1 1 1 S1 cl WfP1 Hcl ltac:(lia) (aregime_preg_tick S cl Hev Hcl)) as APOST.
eapply amreal_mono; [| exact (amreal_apost tfibsegs _ _ W _ _ APOST RR)].
intros r W' c' H. exists ms1, mat1, Em. split; [|exact H]. repeat (split; [assumption|]). exact BUFW.
-
intros [] S' W' c' (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & (WFP' & RO & CI) & HL). cbn [fst snd] in WFP', RO, CI, HL.
destruct HL as (regsR & memR & mdR & -> & POST & HA0 & _). cbn [snd] in HA0.
unfold raZ. rewrite (R_ra ms1 mat1 Em HEm HSC MEQW PRESW BUFW). unfold w64 at 1. rewrite unsigned_lit_small by lia.
destruct (pc_chunks (cache S' cl)) as [|x t] eqn:El.
+
eapply amreal_mono; [| exact (TAILN ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR WFP' RO CI POST El HA0)].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP. apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ HQT))).
+ assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
destruct LX as (l & off & LX). rewrite LX in El.
destruct (junk_real ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR WFP' RO CI POST l off El HA0)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| exact (TAILJ ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR WFP' RO CI POST l off El HA0 j0 jb j1 j2 j3 j4 Hj0 Hj1 Hj2 Hj3 Hj4 Hjb Hjb_def)].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP.
apply (SHIFTU ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR RO POST (p, s6) W6 c6).
apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ HQT))).
Qed.
End ga.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The miss-k arm (0 <= n <= 48) for any UP. Port-from: lib/B/YFin.v:614. The walk is lib/B/YFin.v's, over        *)
(*    YFj6 / YFja / YFj8 / YFj7 / YFj9 / YFjb / YFjc / YFje and FSupoisonAllocMp3's tail.                            *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* The miss-k seed's regions (YFi4.v MKREG0) are the hit-k seed's, trimmed: each is inert or application memory. *)
Lemma MKREG0_classb : forallb (fun r => Mp4.reg_inert r || Mp4.reg_appb r) MKREG0 = true.
Proof. vm_compute. reflexivity. Qed.

Section ka.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Variable UP : list (Z * Z).
Let tr : list Z := call_trace ly PC_MALLOC_RA0 regs0 ch.
Hypothesis PRE : FSU.acall_preU tfibsegs B ly S UP W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Htr : tr_admit (as_universe B) S tr.
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let cl : Z := chunk_class n.
Let csz : Z := class_size cl.
Let mat0 : list word := m_vm_materialized md0.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Let E0m : env := YFj6.E0 ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => YFjb.DPOST3 W ly regs0 ch B S1 z m.

Lemma kHARU0 : FSP.ARU tfibsegs B ly S UP W mem0 md0.
Proof. exact (AllocR.ARU_of_acall_preU B ly S UP W regs0 mem0 md0 ch PRE). Qed.
Lemma kHAR0u : AR tfibsegs B ly S W (FSP.unpoison UP mem0) md0.
Proof. exact (proj1 (proj1 PRE)). Qed.
Lemma kHARm0u : ARm B ly S (aview tfibsegs (w_H W) (FSP.unpoison UP mem0)).
Proof. exact (proj1 kHAR0u). Qed.
Lemma kHev : aregime S. Proof. exact (proj1 (proj2 (proj1 PRE))). Qed.
Lemma kHAR1u : AR tfibsegs B ly S1 W (FSP.unpoison UP mem0) md0.
Proof. exact (AR_tick B ly S W (FSP.unpoison UP mem0) md0 kHAR0u kHev). Qed.
Lemma kHARm1u : ARm B ly S1 (aview tfibsegs (w_H W) (FSP.unpoison UP mem0)).
Proof. exact (proj1 kHAR1u). Qed.
Lemma kHARU1 : FSP.ARU tfibsegs B ly S1 UP W mem0 md0.
Proof. exact (AllocR.ARU_tick B ly S UP W mem0 md0 kHARU0 kHev). Qed.
Lemma kLY : layout_ok ly. Proof. exact (am_layout _ _ _ _ kHARm0u). Qed.
Lemma kIMG : img_cover ly. Proof. exact (img_cover_of_ledger ly _ _ (proj1 (proj2 kHAR0u))). Qed.
Lemma kHTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (am_tsd _ _ _ _ kHARm0u). exact (ts_tsd B TS). Qed.
Lemma kHtp : getr regs0 4 = w64 TFIB_TP.
Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp' & _) & _). rewrite (ts_tp B TS) in Htp'. exact Htp'. Qed.
Lemma kHgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.
Lemma kHra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE as ((_ & _ & H & _) & _). exact H. Qed.
Lemma kHsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Proof. destruct PRE as ((_ & _ & _ & Hal & Hlo & Hbot & Hhi & _) & _). unfold spZ in *. repeat split; assumption. Qed.
Lemma kHpres0u : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (FSP.unpoison UP mem0) a.
Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.
Lemma kHQT : qmeter S. Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.
Lemma kSTK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof (lo_top ly kLY) as (_ & _ & _ & H4 & _ & _ & H7). split; [exact H7 | exact H4]. Qed.
Lemma kUsp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. apply u64_range. Qed.
Lemma kHpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal).
apply (AllocR.stack_present_real B ly S UP W mem0 md0 (sp0 - ASTACK) sp0 kHARU0);
  [unfold ASTACK in *; lia | lia | exact kHpres0u].
Qed.
Lemma kCHr : chain_pre ly (aview tfibsegs (w_H W) mem0) regs0 ch.
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal).
destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CH & _) & _).
exact (AllocR.chain_pre_real B ly S UP W regs0 mem0 md0 ch kHARU0 ltac:(unfold spZ, sp0, ASTACK in *; lia) CH).
Qed.
Lemma kHra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. pose proof kCHr as [H _]. unfold raZ in H. exact H. Qed.
Lemma kHch : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof. pose proof kCHr as [_ H]. unfold frame0_ok, spZ, s0Z in H. exact H. Qed.
Lemma kHcl_class : cl = chunk_class n. Proof. reflexivity. Qed.
Lemma kHcsz_def : csz = class_size cl. Proof. reflexivity. Qed.
Lemma kHcl : 1 <= cl <= 31. Proof. exact (@YFjc.Hcl' ly regs0 mem0 n cl 0 DPOSTm Nrange [] 0 kHcl_class). Qed.
Lemma kHcl_def : cl = class_id (YFj6.R8v n + YFj6.RZ).
Proof. pose proof (@YFj6.case0_sizes n Nrange) as (L & RS & R8 & NP & FPx & NS & RQ). subst cl. unfold chunk_class. rewrite NS, <- RS. reflexivity. Qed.
Lemma kFP : from_primary n = true. Proof. pose proof (@YFj6.case0_sizes n Nrange) as (_ & _ & _ & _ & FPx & _). exact FPx. Qed.
Lemma kHmiss1 : pc_chunks (cache S1 cl) = []. Proof. exact Hmiss. Qed.
Lemma kHvd : 0 <= 0 /\ 16 * 0 + 2 ^ 16 <= 2 ^ 32. Proof. lia. Qed.
Lemma kHcntd : 1 <= 1 <= 16. Proof. lia. Qed.
Lemma kHjbd : 0 <= 0 <= 255. Proof. lia. Qed.
Lemma kHv2d : 0 mod 2 = 0. Proof. reflexivity. Qed.
Lemma kWfP1 : WfP (as_universe B) 1 1 1 S1. Proof. exact (WfP_tick _ S (am_wf _ _ _ _ kHARm0u) kHev). Qed.
Lemma kT_range : zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL.
Proof. pose proof (@YFj6.high_facts _ ly regs0 mem0 n 0 kHvd kLY kIMG DPOSTm) as (F1 & F2 & _). split; assumption. Qed.

Lemma koffU_stk : forall a, sp0 - ASTACK <= a < sp0 -> AllocR.offU UP a.
Proof.
intros a Ha. pose proof kHsp as (P1 & P2 & P3 & P4).
exact (AllocR.stack_offU B ly S1 UP W mem0 md0 a kHARU1 ltac:(unfold ASTACK in *; lia)).
Qed.
Lemma koffU_lo : forall a, 0 <= a < SHADOW_OFF -> AllocR.offU UP a.
Proof. intros a Ha. exact (Mp1.offU_lit B ly S1 UP W mem0 md0 a kHARU1 Ha). Qed.
Lemma koffU_T : forall a, T <= a < T + kThreadObjSize -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S1 UP W mem0 md0 (ly_T ly, kThreadObjSize) a kHARU1
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. unfold T in Ha. exact Ha.
Qed.
Lemma koffU_C : forall a, ly_C ly <= a < ly_C ly + 256 -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S1 UP W mem0 md0 (ly_C ly, 256) a kHARU1
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. exact Ha.
Qed.

Lemma kMKREG0_offU : forall r, In r (ss_mem MK0) ->
  Mp4.reg_inert r = true \/
  (forall a, base_val E0m (YP09.r_base r) + YP09.r_lo r <= a < base_val E0m (YP09.r_base r) + YP09.r_hi r ->
     AllocR.offU UP a).
Proof.
pose proof (@YFj6.derived_ranges _ ly regs0 mem0 n cl 1 0 kHcl kHvd kHcntd kHv2d kLY kIMG DPOSTm Nrange) as DR.
pose proof (@YFj6.high_facts _ ly regs0 mem0 n 0 kHvd kLY kIMG DPOSTm) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
pose proof kHsp as (SP1 & SP2 & SP3 & SP4). pose proof kHcl as HC1.
destruct F1 as (ZT1 & ZT2 & _). destruct F7 as (ZC1 & ZC2 & _).
ceil. unfold kThreadObjSize, ASAN_CEIL, t_cache, t_unwinding, kHighMemBeg in *.
assert (RT : 0 <= ly_T ly < 2 ^ 64) by lia.
assert (RC : 0 <= ly_C ly < 2 ^ 64) by lia.
assert (RPv : 0 <= YFj6.Pv ly cl < 2 ^ 64) by lia.
assert (RPVv : 0 <= YFj6.PVv ly cl 1 < 2 ^ 64) by lia.
assert (RSS : 0 <= YFj6.SSLOTv ly cl < 2 ^ 64) by lia.
change (ss_mem MK0) with MKREG0.
intros r Hr. pose proof (proj1 (forallb_forall _ _) MKREG0_classb r Hr) as K.
apply Bool.orb_prop in K as [K|K]; [left; exact K|]. right. intros a Ha.
unfold E0m in Ha. unfold Mp4.reg_appb in K.
set (rb := YP09.r_base r) in *. clearbody rb. destruct rb as [k|]; cbn [base_val] in Ha.
2:{ apply andb_prop in K as [K1' K2']. apply Z.leb_le in K1'. apply Z.leb_le in K2'. apply koffU_lo. lia. }
repeat match type of K with (_ || _) = true => apply Bool.orb_prop in K; destruct K as [K|K] end;
  apply andb_prop in K as [K K3']; apply andb_prop in K as [K1' K2'];
  apply Nat.eqb_eq in K1'; subst k; apply Z.leb_le in K2'; apply Z.leb_le in K3'.
- rewrite (@YFj6.E2 ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0) in Ha.
  change (bv_unsigned (getr regs0 2)) with sp0 in Ha. apply koffU_stk. unfold ASTACK in *. lia.
- rewrite (@YFj6.EaT ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RT. apply koffU_T. lia.
- rewrite (@YFj6.EaC ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RC. apply koffU_C. lia.
- rewrite (@YFj6.EaP ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RPv.
  apply koffU_T. unfold kThreadObjSize, t_cache in *. lia.
- rewrite (@YFj6.EaPV ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RPVv.
  apply koffU_T. unfold kThreadObjSize, t_cache in *. lia.
- rewrite (@YFj6.EaSSLOT ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0) in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RSS.
  apply koffU_T. unfold kThreadObjSize, t_unwinding in *. lia.
Qed.

Lemma kSEEDMu : st_ok tfibsegs E0m MK0 (restrict (w_H W) (mkst regs0 (w64 PC_WRAP_MALLOC) (FSP.unpoison UP mem0) (seg_rom tfibsegs))).
Proof.
exact (@YFja.SEEDM_ok _ _ W ly regs0 (FSP.unpoison UP mem0) n ch cl 1 0 csz 0 0 0 0 0 0 kHcl kHvd kHcntd kHjbd kHv2d kLY kIMG Hn kHtp kHsp DPOSTm Nrange kHcl_def B S1 TS kHTSD kHARm1u kHpres0u kHmiss1).
Qed.
Lemma kSEEDM : st_ok tfibsegs E0m MK0 (restrict (w_H W) (mkst regs0 (w64 PC_WRAP_MALLOC) mem0 (seg_rom tfibsegs))).
Proof. exact (Mp4.st_ok_real UP E0m MK0 (w_H W) regs0 (w64 PC_WRAP_MALLOC) mem0 (seg_rom tfibsegs) kMKREG0_offU kSEEDMu). Qed.
Lemma kMISS1 : SRr tfibsegs W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (YFj8.at_STM W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 MK_CALL).
Proof.
replace (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 PC_WRAP_MALLOC) mem0 (seg_rom tfibsegs)) (md0' mat0))
by (unfold cfg_at, md0', mat0; rewrite with_vm_backing_id; reflexivity).
exact (@YFj8.miss1 _ _ W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 kHcl kHvd kHcntd kHjbd kHv2d kLY kIMG Hn kHra4096 kHsp kHch DPOSTm Nrange kHcl_def mat0 U1 [] 0 kSEEDM).
Qed.

Section kf.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em MK_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ YFj8.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).

Lemma kms1_shape : ms1 = mkst (ms_regs ms1) (w64 PC_REFILL) (ms_mem ms1) (seg_rom tfibsegs).
Proof. exact (st_ok_restrict_mkst tfibsegs (w_H W) Em _ _ HSC eq_refl). Qed.
Lemma kHSC' : st_ok tfibsegs Em MK_CALL (mkst (ms_regs ms1) (w64 PC_REFILL) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs)).
Proof. pose proof HSC as H. rewrite kms1_shape in H. exact H. Qed.
Lemma kEm2 : ew Em 2 = getr regs0 2. Proof. rewrite (HEm 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma kEm3 : ew Em 3 = getr regs0 3. Proof. rewrite (HEm 3%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma kEm32 : ew Em 32 = w64 T. Proof. rewrite (HEm 32%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma kEm39 : ew Em 39 = w64 cl. Proof. rewrite (HEm 39%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma kEm40 : ew Em 40 = w64 (YFj6.Pv ly cl). Proof. rewrite (HEm 40%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma kR_ra : getr (ms_regs ms1) 1 = w64 RA_REFILL. Proof. rreg HSC (1%bv : bv 5) R. exact R. Qed.
Lemma kR_sp : getr (ms_regs ms1) 2 = w64 (sp0 - 2320).
Proof. rreg HSC (2%bv : bv 5) R. rewrite R, kEm2. unfold w64, sp0. f_equal; lia. Qed.
Lemma kR_gp : getr (ms_regs ms1) 3 = getr regs0 3. Proof. rreg HSC (3%bv : bv 5) R. rewrite R, kEm3. reflexivity. Qed.
Lemma kR_tp : getr (ms_regs ms1) 4 = w64 TFIB_TP. Proof. rreg HSC (4%bv : bv 5) R. exact R. Qed.
Lemma kR_a0 : getr (ms_regs ms1) 10 = w64 (T + t_cache).
Proof. rreg HSC (10%bv : bv 5) R. rewrite R, kEm32. unfold w64, t_cache. rewrite Zbv_add_unsigned. reflexivity. Qed.
Lemma kR_a1 : getr (ms_regs ms1) 11 = w64 (T + t_cache + 80 * cl). Proof. rreg HSC (11%bv : bv 5) R. rewrite R, kEm40. reflexivity. Qed.
Lemma kR_a2 : getr (ms_regs ms1) 12 = w64 A_ALLOCATOR. Proof. rreg HSC (12%bv : bv 5) R. exact R. Qed.
Lemma kR_a3 : getr (ms_regs ms1) 13 = w64 cl. Proof. rreg HSC (13%bv : bv 5) R. rewrite R, kEm39. reflexivity. Qed.
Lemma kSP1 : spZ (ms_regs ms1) = sp0 - 2320.
Proof. unfold spZ. rewrite kR_sp. unfold w64. apply unsigned_lit_small. pose proof kUsp. pose proof kHsp. pose proof kSTK. unfold ASTACK, kHighMemBeg in *. lia. Qed.
Lemma kUNW1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (T + t_unwinding) 1 0.
Proof.
pose proof kT_range as [T1 T2].
memv HSC 41%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite kEm32; unfold w64, t_unwinding; rewrite unsigned_lit_small by (ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); reflexivity
| reflexivity | cbn; lia].
Qed.
Lemma kUNW_cell : forall Sx rd, ARm B ly Sx rd -> rd (T + t_unwinding) = Some 0.
Proof.
intros Sx rd M. assert (IN : In (z1 (AT t_unwinding) 0) (acells B ly Sx)).
{ unfold acells. repeat (apply in_app_iff; right). left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M) _ IN 0%nat ltac:(cbn; lia)) as X. cbn [c_at c_w aeval z1 c1] in X.
rewrite Z.add_0_r in X. exact X.
Qed.
Lemma kAG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros a Ha Hs. destruct (Z.eq_dec a (T + t_unwinding)) as [->|Hne].
- assert (OU : AllocR.offU UP (T + t_unwinding)) by (apply koffU_T; unfold kThreadObjSize, t_unwinding; lia).
  rewrite <- (AllocR.aview_unpoison (w_H W) UP mem0 _ OU).
  rewrite (kUNW_cell S1 _ kHARm1u).
  pose proof (Dm.val_mem_aview (w_H W) (ms_mem ms1) (T + t_unwinding) 1 0 0 kUNW1 ltac:(lia)) as X.
  rewrite Z.add_0_r in X. rewrite X. reflexivity.
- apply aview_same. apply MEQW. rewrite unsigned_lit_small by exact Ha. unfold YFj8.WINM. fold sp0. unfold T in Hne. clear - Hs Hne. lia.
Qed.
Lemma kARUms1 : FSP.ARU tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1).
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U. pose proof kT_range as [T1 T2].
apply (FSP.ARU_frame tfibsegs B (AR_laws_ok tfibsegs B) ly S1 UP W mem0 md0 (ms_mem ms1) (md0' mat1) kHARU1).
- intros a Ha Ho. apply kAG1; [exact Ha|]. intros Hst.
  apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison UP mem0) md0 a kHAR1u); [clear - Hst Hlo Hhi; unfold ASTACK in *; lia | exact Ho].
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (AV : forall m, aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
  rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  destruct (Z_lt_le_dec a' (sp0 - ASTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a' sp0) as [H2|H2]].
  2:{ apply Dm.apresent_aview_some; [clear - H1 H2 K1 Ha' Hlo; unfold TFIB_IMG_END, kHighMemBeg, ASTACK in *; lia | apply PRESW; lia]. }
  all: rewrite (kAG1 a' Ha' ltac:(lia)); exact Hv.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. rewrite (MEQW (w64 a)); [reflexivity|].
  assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
  unfold w64. rewrite unsigned_lit_small by exact Ha'. unfold YFj8.WINM. fold sp0.
  pose proof (zone3_apart_hsh _ _ a T1) as TH. unfold T in TH. clear - Ha K1 Hlo TH.
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, kThreadObjSize in *. lia.
Qed.
Lemma kAR1u : AR tfibsegs B ly S1 W (FSP.unpoison UP (ms_mem ms1)) (md0' mat1).
Proof. exact (FSP.ARU_AR tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1) kARUms1). Qed.
Lemma kREFILL_PREu : AllocR.refill_preU B ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl.
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U.
pose proof kHAR0u as (_ & _ & [BUD _] & _).
unfold AllocR.refill_preU.
split; [|split; [exact (FSP.ARU_ok tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1) kARUms1)
               | exact (FSP.ARU_poisoned tfibsegs B ly S1 UP W (ms_mem ms1) (md0' mat1) kARUms1)]].
unfold refill_pre. rewrite kSP1. unfold raZ. rewrite kR_ra, kR_gp, kR_tp, kR_a0, kR_a1, kR_a2, kR_a3, kHgp, (ts_tp B TS).
split; [exact kAR1u|].
split; [unfold abudget in *; cbn [st_nev set_nev S1]; change (sec_live_bytes S1) with (sec_live_bytes S); change (sec_hulls S1) with (sec_hulls S); unfold EV_A in *; lia|].
split; [split; [pose proof (wf_prim_ev _ _ _ _ _ kWfP1) as PE; cbn [st_nev set_nev S1] in PE |- *; change (prim_user_mapped S1) with (prim_user_mapped S) in *; lia|];
split; [exact (aregime_preg_tick S cl kHev kHcl) | exact (aregime_mid_tick S kHev)]|].
split; [split; [apply qtight_qloose; exact (qmeter_tight _ kHQT) | apply (rroom_tick S); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (qmeter_room _ kHQT)]]|].
split; [apply ret_ok_even; reflexivity|]. split; [unfold w64; rewrite unsigned_lit_small by lia; lia|].
split; [clear - Hal; replace (sp0 - 2320) with (sp0 + (-145) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [clear - Hlo; unfold ASTACK, RSTACK in *; lia|]. split; [lia|].
split; [intros a Ha; apply AllocR.apresent_to_unpoison; apply PRESW; clear - Ha; unfold ASTACK, RSTACK in *; lia|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact kHcl | exact kHmiss1].
Qed.

Section kg.
Variables (S' : astate) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis WFP' : WfP (as_universe B) 0 1 1 S'.
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : FSU.acall_postU tfibsegs B RSTACK ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Let msR : machine_state := mkst regsR (w64 RA_REFILL) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).

Lemma kPOSTd : acall_post tfibsegs B RSTACK ly S1 W (ms_regs ms1) (FSP.unpoison UP (ms_mem ms1)) (md0' mat1) (fun _ => False) ly S' W' regsR (FSP.unpoison UP memR) mdR.
Proof. exact (proj1 POST). Qed.
Lemma kHAR'u : AR tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR. Proof. exact (proj1 kPOSTd). Qed.
Lemma kHARm'u : ARm B ly S' (aview tfibsegs (w_H W') (FSP.unpoison UP memR)). Proof. exact (proj1 kHAR'u). Qed.
Lemma kHARU' : FSP.ARU tfibsegs B ly S' UP W' memR mdR.
Proof. split; [exact kHAR'u|]. split; [exact (proj1 (proj2 POST)) | exact (proj2 (proj2 POST))]. Qed.
Lemma kWLE : wle W W'. Proof. exact (proj1 (proj2 (proj2 kPOSTd))). Qed.
Lemma kERRNO_low : as_errno B + 4 <= kHighMemBeg.
Proof. rewrite (ts_errno B TS). unfold TFIB_ERRNO, kHighMemBeg. lia. Qed.
Lemma kAGR : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2320 - RSTACK <= a < sp0 - 2320) ->
aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Proof.
intros a Ha Hns. pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U. pose proof kERRNO_low as EL.
assert (OU : AllocR.offU UP a) by (apply (AllocR.stack_offU B ly S' UP W' memR mdR a kHARU'); unfold ASTACK in *; lia).
rewrite <- (AllocR.aview_unpoison (w_H W') UP memR a OU), <- (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU).
destruct kPOSTd as (_ & _ & _ & _ & _ & FR & _). apply FR.
- clear - Ha Hlo K1 U. unfold ASTACK, kHighMemBeg in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison UP (ms_mem ms1)) (md0' mat1) a kAR1u). clear - Ha Hlo Hhi. unfold ASTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a kHAR'u). clear - Ha Hlo Hhi. unfold ASTACK in *. lia.
- unfold ascratch. rewrite kSP1. intros [X|X]; [exact (Hns X)|]. clear - X Ha Hlo K1 EL. unfold ASTACK, kHighMemBeg in *. lia.
- intros [].
Qed.
Lemma kPRES' : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U.
assert (Hhi' : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha Hlo K1 U; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia).
destruct (Z_lt_le_dec a (sp0 - 2320 - RSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a (sp0 - 2320)) as [H2|H2]].
- apply (Dm.apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply kAGR; [exact Ha | lia] | apply PRESW; exact Ha].
- assert (OU : AllocR.offU UP a) by (apply (AllocR.stack_offU B ly S' UP W' memR mdR a kHARU'); unfold ASTACK in *; lia).
  apply (AllocR.apresent_of_unpoison (w_H W') UP memR a OU).
  destruct kPOSTd as (_ & _ & _ & _ & _ & _ & PRS). apply PRS. rewrite kSP1. lia.
- apply (Dm.apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply kAGR; [exact Ha | lia] | apply PRESW; exact Ha].
Qed.
Lemma kBUF' : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') memR) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof.
intros i Hi. pose proof (@YFj6.tr_length ly regs0 mem0 n ch 0 DPOSTm) as LEN. change (YFj6.tr ly regs0 ch) with tr in LEN.
eapply Dm.val_mem_aview_xfer; [|exact (BUFW i Hi)]. intros k Hk. apply kAGR; clear - Hi Hk LEN; unfold IFRAME, ASTACK, RSTACK in *; lia.
Qed.
Lemma kAGtop : forall a, sp0 <= a < ly_top ly -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros a Ha. pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U. pose proof kERRNO_low as EL.
pose proof (lo_top ly kLY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha U T2 K2; unfold kHighMemEnd in *; lia).
assert (OU : AllocR.offU UP a) by (apply (AllocR.stack_offU B ly S' UP W' memR mdR a kHARU'); unfold ASTACK in *; lia).
rewrite <- (AllocR.aview_unpoison (w_H W') UP memR a OU).
rewrite <- (kAG1 a Ra ltac:(clear - Ha; lia)), <- (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU).
destruct kPOSTd as (_ & _ & _ & _ & _ & FR & _). apply FR.
- clear - Ha Hlo K1 U T2 K2. unfold kHighMemEnd, kHighMemBeg in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison UP (ms_mem ms1)) (md0' mat1) a kAR1u). clear - Ha Hlo T2. unfold ASTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a kHAR'u). clear - Ha Hlo T2. unfold ASTACK in *. lia.
- unfold ascratch. rewrite kSP1. intros [X|X]; [clear - X Ha; unfold RSTACK in *; lia|]. clear - X Ha Hlo K1 EL. unfold kHighMemBeg, ASTACK in *. lia.
- intros [].
Qed.
Lemma kHch' : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W') memR)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof.
pose proof kHch as H. destruct (sp0 + 16 <? ly_top ly); [|exact H].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:BN; [exact H|].
destruct H as [H1 H2]. split; [exact H1|].
unfold bad_next in BN. apply orb_false_iff in BN as [BN1 BN3]. apply orb_false_iff in BN1 as [BN1 BN2].
apply Z.leb_gt in BN1. apply Z.leb_gt in BN2.
apply (fpchain_bytes (aview tfibsegs (w_H W) mem0) (aview tfibsegs (w_H W') memR) sp0 (ly_top ly) ch
  (bv_unsigned (getr regs0 8))).
- exact kAGtop.
- exact H1.
- lia.
- exact H2.
Qed.
Let E1 : env := havoc Em hRFk (map (getr regsR) CLOB).
Lemma kEm2u : bv_unsigned (ew Em 2) = sp0. Proof. rewrite kEm2. reflexivity. Qed.
Lemma kKEPT3 : Forall (region_kept tfibsegs Em (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W') memR)) RSK3.
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U.
assert (A : forall a, sp0 - 2320 <= a < sp0 -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a)
by (intros a Ha; apply kAGR; clear - Ha; unfold ASTACK, RSTACK; lia).
unfold RSK3. repeat (apply Forall_cons; [eapply (Dm.region_kept_view (w_H W) (w_H W') Em (ms_mem ms1) memR 2 _ _ _ _ _ sp0 kEm2u);
[intros a Ha; apply A; clear - Ha; lia | clear - Hlo K1; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia | clear - U; lia | clear; intros a Ha; lia] |]).
apply Forall_nil.
Qed.
Let ms3 : machine_state := mkst regsR (w64 RA_REFILL) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Lemma kHS3 : st_ok tfibsegs E1 SSK3 ms3.
Proof.
rewrite SSK3_eq. pose proof MK_CALL_facts as (F1 & F2 & F3 & F4 & F5 & F6). destruct MK_CALL_mem3 as [rest ER].
apply (st_ok_after_call tfibsegs hRFk Em MK_CALL (mkst (ms_regs ms1) (w64 PC_REFILL) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs))
regsR (mrestrict (w_H W') memR) RSK3 RA_REFILL kHSC' F6 F1 F2 F3 F4).
- rewrite ER. change RSK3 with [K3bst; trim_lo K3scr (-2320); K3top].
apply submem_keep; [apply Dm.subregion_refl|]. apply submem_keep; [apply subregion_trim_lo|]. apply submem_keep; [apply Dm.subregion_refl|]. apply submem_nil.
- exact F5.
- destruct kPOSTd as (_ & _ & _ & CS & _). intros r Hr. apply CS. exact Hr.
- exact kKEPT3.
Qed.

Section kj.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA0 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => YFjb.DPOST3 W' ly regs0 ch B S' z m.
Lemma kHcnt_def' : cnt' = Z.of_nat (length (l ++ [off])). Proof. reflexivity. Qed.
Lemma kHoffv' : off = 16 * v' /\ v' mod 2 = 0.
Proof.
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ kHARm'u) cl kHcl) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache' in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(rewrite !in_app_iff; cbn; tauto)) as [_ O2].
pose proof (class_ok cl kHcl) as (K1 & K2 & _). apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [r Hr]; [|lia].
subst v'. rewrite Hq, Hr. replace (q * (r * 32)) with ((2 * q * r) * 16) by lia. rewrite Z.div_mul by lia. split; [lia|].
rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma kHoff_def' : off = 16 * v'. Proof. exact (proj1 kHoffv'). Qed.
Lemma kHv2' : v' mod 2 = 0. Proof. exact (proj2 kHoffv'). Qed.
Lemma kHv' : 0 <= v' /\ 16 * v' + 2 ^ 16 <= 2 ^ 32.
Proof. exact (@YFjc.Hv' _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' kHv2' DPOST' Nrange B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def'). Qed.
Lemma kHcnt' : 1 <= cnt' <= 16.
Proof. exact (@YFjc.Hcnt' _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' kHv2' kHsp DPOST' Nrange B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def'). Qed.
Lemma kOKv' : forall a, YFj6.Kv ly cl v' <= a < YFj6.Kv ly cl v' + csz -> AllocR.offU UP a.
Proof.
intros a Ha. pose proof (@YFj6.derived_ranges _ ly regs0 memR n cl cnt' v' kHcl kHv' kHcnt' kHv2' kLY kIMG DPOST' Nrange) as DR.
pose proof (@YFjc.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' DPOST' Nrange l off kHcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
apply (Mp1.offU_hi B ly S' UP W' memR mdR a kHARU').
ceil. unfold kHighMemBeg, ASAN_CEIL, kMaxSize in *. rewrite kHcsz_def in Ha. lia.
Qed.
Lemma kOKS' : forall g, g mod 8 = 0 -> YFj6.Kv ly cl v' <= g < YFj6.Kv ly cl v' + csz -> AllocR.offU UP (shadow_addr g).
Proof.
intros g G8 Hg. pose proof (@YFj6.derived_ranges _ ly regs0 memR n cl cnt' v' kHcl kHv' kHcnt' kHv2' kLY kIMG DPOST' Nrange) as DR.
pose proof (@YFjc.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' DPOST' Nrange l off kHcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
apply (AllocR.offU_nonzero B ly S' UP W' memR mdR (shadow_addr g) 250 kHARU').
- unfold shadow_addr. ceil.
  pose proof (Z.div_pos g 8 ltac:(unfold kHighMemBeg in *; lia) ltac:(lia)) as D1'.
  pose proof (Z.div_le_upper_bound g 8 (2 ^ 44) ltac:(lia) ltac:(unfold ASAN_CEIL, kMaxSize in *; rewrite kHcsz_def in Hg; lia)) as D2'.
  unfold SHADOW_OFF. lia.
- exact (@YFjc.shadow250 _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kHv2' kLY kHsp DPOST' Nrange B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def g G8 ltac:(rewrite <- kHcsz_def; exact Hg)).
- lia.
- lia.
Qed.
Lemma kSHK' : forall j, shadow_addr (YFj6.Kv ly cl v' + 8 * j) = YFj6.SKv ly cl v' + j.
Proof.
intros j. pose proof (@YFj6.derived_ranges _ ly regs0 memR n cl cnt' v' kHcl kHv' kHcnt' kHv2' kLY kIMG DPOST' Nrange) as DR.
pose proof (Z.div_mod (YFj6.Kv ly cl v') 16 ltac:(lia)) as DK.
unfold shadow_addr, YFj6.SKv, YFj6.SHBv, SHADOW_OFF.
replace (YFj6.Kv ly cl v' + 8 * j) with ((YFj6.Kv ly cl v' / 16 * 2 + j) * 8) by lia.
replace (YFj6.Kv ly cl v') with (YFj6.Kv ly cl v' / 16 * 2 * 8) at 2 by lia.
rewrite !Z.div_mul by lia. lia.
Qed.
Lemma kHKpres' : forall a, YFj6.Kv ly cl v' <= a < YFj6.Kv ly cl v' + YFj6.RZ + YFj6.R8v n -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof (@YFj6.derived_ranges _ ly regs0 memR n cl cnt' v' kHcl kHv' kHcnt' kHv2' kLY kIMG DPOST' Nrange) as DR.
pose proof (@YFjc.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' DPOST' Nrange l off kHcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
apply (AllocR.apresent_of_unpoison (w_H W') UP memR a ltac:(apply kOKv'; rewrite kHcsz_def; lia)).
exact (@YFjc.KPRES _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kHv2' kLY kHsp DPOST' Nrange B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def a Ha).
Qed.
Lemma kHSKpres' : forall a, YFj6.SKv ly cl v' <= a < YFj6.SKv ly cl v' + (YFj6.RZ + YFj6.R8v n) / 8 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof (@YFj6.derived_ranges _ ly regs0 memR n cl cnt' v' kHcl kHv' kHcnt' kHv2' kLY kIMG DPOST' Nrange) as DR.
pose proof (@YFjc.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' DPOST' Nrange l off kHcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (Z.div_mod (YFj6.Kv ly cl v') 16 ltac:(lia)) as DK.
apply (AllocR.apresent_of_unpoison (w_H W') UP memR a
  ltac:(replace a with (shadow_addr (YFj6.Kv ly cl v' + 8 * (a - YFj6.SKv ly cl v'))) by (rewrite kSHK'; lia);
        apply kOKS'; [replace (YFj6.Kv ly cl v' + 8 * (a - YFj6.SKv ly cl v')) with ((YFj6.Kv ly cl v' / 16 * 2 + (a - YFj6.SKv ly cl v')) * 8) by lia; apply Z.mod_mul; lia
                   | rewrite kHcsz_def; pose proof (Z.mul_div_le (YFj6.RZ + YFj6.R8v n) 8 ltac:(lia)); lia])).
exact (@YFjc.SKPRES _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kHv2' kLY kIMG kHsp DPOST' Nrange B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def a Ha).
Qed.
Lemma kHPB250' : YFj6.NPv n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W') memR) (YFj6.PBv ly n cl v') 1 250.
Proof.
intros E8. pose proof (@YFj6.derived_ranges _ ly regs0 memR n cl cnt' v' kHcl kHv' kHcnt' kHv2' kLY kIMG DPOST' Nrange) as DR.
pose proof (@YFjc.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' DPOST' Nrange l off kHcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (Z.div_mod (YFj6.Kv ly cl v') 16 ltac:(lia)) as DK.
apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (YFj6.PBv ly n cl v') 1 250).
- intros k Hk. replace (YFj6.PBv ly n cl v' + Z.of_nat k) with (shadow_addr (YFj6.Kv ly cl v' + YFj6.RZ + YFj6.N8D n)).
  2:{ replace (Z.of_nat k) with 0 by lia. rewrite Z.add_0_r.
      unfold shadow_addr, YFj6.PBv, YFj6.SHBv, SHADOW_OFF. reflexivity. }
  apply kOKS'.
  + unfold YFj6.N8D. pose proof (Z.div_mod (YFj6.NPv n) 8 ltac:(lia)).
    replace (YFj6.Kv ly cl v' + YFj6.RZ + YFj6.NPv n / 8 * 8) with ((YFj6.Kv ly cl v' / 16 * 2 + YFj6.RZ / 8 + YFj6.NPv n / 8) * 8) by lia.
    apply Z.mod_mul. lia.
  + rewrite kHcsz_def. unfold YFj6.N8D in *. pose proof (Z.div_mod (YFj6.NPv n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (YFj6.NPv n) 8 ltac:(lia)). lia.
- exact (@YFjc.PB250 _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kHv2' kLY kIMG kHsp DPOST' Nrange B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def E8).
Qed.
Lemma kjunk_real : exists j0 j1 j2 j3 j4 jb,
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2784) 8 j0 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2800) 8 j1 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2808) 8 j2 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2816) 8 j3 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (YFj6.SSLOTv ly cl) 8 j4 /\
  0 <= jb <= 255 /\
  val_mem tfibsegs (mrestrict (w_H W') memR) (YFj6.Kv ly cl v' + YFj6.RZ - 15) 1 jb.
Proof.
pose proof (@YFj6.derived_ranges _ ly regs0 memR n cl cnt' v' kHcl kHv' kHcnt' kHv2' kLY kIMG DPOST' Nrange) as DR.
pose proof (@YFjc.cls_geom ly regs0 (FSP.unpoison UP memR) n cl v' DPOST' Nrange l off kHcl_class) as (C1 & C2 & C3 & C4 & C5 & C6).
assert (OT : forall a, T <= a < T + kThreadObjSize -> AllocR.offU UP a).
{ intros a Ha. apply (Mp1.offU_owned B ly S' UP W' memR mdR (ly_T ly, kThreadObjSize) a kHARU'
    ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. unfold T in Ha. exact Ha. }
destruct (@YFjc.junk_values _ W' ly regs0 (FSP.unpoison UP memR) n cl cnt' v' csz kHv2' kLY kIMG kHsp DPOST' Nrange B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0u & Hj1u & Hj2u & Hj3u & Hj4u & Hjb & Hjbu).
exists j0, j1, j2, j3, j4, jb.
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2784) 8 j0); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj0u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2800) 8 j1); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj1u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2808) 8 j2); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj2u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (T + 2816) 8 j3); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj3u]|].
split; [apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (YFj6.SSLOTv ly cl) 8 j4);
        [intros k Hk; apply OT; unfold YFj6.SSLOTv, T, kThreadObjSize, t_stats in *; pose proof kHcl; lia | exact Hj4u]|].
split; [exact Hjb|].
apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (YFj6.Kv ly cl v' + YFj6.RZ - 15) 1 jb);
  [intros k Hk; apply kOKv'; rewrite kHcsz_def; unfold YFj6.RZ in *; lia | exact Hjbu].
Qed.

Section kk.
Variables (j0 jb j1 j2 j3 j4 : Z).
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W') memR) (YFj6.SSLOTv ly cl) 8 j4.
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (YFj6.Kv ly cl v' + YFj6.RZ - 15) 1 jb.
Let E0' : env := YFj6.E0 ly regs0 n ch cl cnt' v' csz j0 jb j1 j2 j3 j4.
Let Es : env := env_merge PND E1 E0'.
Lemma kHEs : forall k, (k < aHAV)%nat -> ew Es k = ew E0' k.
Proof.
intros k Hk. unfold aHAV in Hk. destruct (PND k) eqn:HP.
- unfold Es. rewrite (ew_merge_in PND E1 E0' k HP). unfold E1. rewrite ew_havoc_old by (unfold hRFk; lia).
rewrite (HEm k Hk). unfold E0m, E0'. apply Dk.E0_nondummy; [exact Hk | exact HP].
- unfold Es. apply ew_merge_out. exact HP.
Qed.
Lemma kAGs : env_agree 64 E0' Es.
Proof. split; [exact kHEs | reflexivity]. Qed.
Lemma kEs2 : bv_unsigned (ew Es 2) = sp0. Proof. rewrite (kHEs 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma kFACTS' : atoms_ok E0' (f_atoms FK).
Proof.
exact (@YFje.FACTS_ok _ W' ly regs0 (FSP.unpoison UP memR) n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kHcl kHv' kHcnt' Hjb kHv2' kLY kIMG Hn kHsp DPOST' Nrange kHcl_def B S' l off kHARm'u CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def).
Qed.
Lemma kSEED' : st_ok tfibsegs E0' SS0K (restrict (w_H W') (mkst regs0 (w64 PC_WRAP_MALLOC) memR (seg_rom tfibsegs))).
Proof.
exact (Mp3.SEEDr W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 B S' l off UP DPOST'
  kHcl kHv' kHcnt' Hjb kHv2' kLY kIMG Hn kHtp kHsp kHKpres' kHSKpres' kHPB250' Nrange kHcl_def TS kHTSD kHARU' kPRES'
  CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Qed.
Lemma kMEMOK' : mem_ok tfibsegs E0' (mrestrict (w_H W') memR) REG0K.
Proof.
destruct kSEED' as (_ & _ & _ & _ & _ & _ & _ & X8 & _). exact X8.
Qed.
Lemma kREG0' : Forall (region_ok tfibsegs E0' (mrestrict (w_H W') memR)) REG0K.
Proof. exact (proj1 (proj2 kMEMOK')). Qed.
Lemma kPAIRS' : pairwise_disjoint E0' REG0K.
Proof. exact (proj2 (proj2 kMEMOK')). Qed.
Lemma kHS4 : st_ok tfibsegs Es SSK3 ms3.
Proof.
pose proof SSK3_atoms as (A1 & A2 & A3 & A4 & A5). pose proof tlREG0K_facts as (_ & _ & T3).
apply (st_ok_agree_on2 tfibsegs PND E1 Es SSK3 ms3 kHS3 (env_merge_on PND E1 E0') A1 A2 A3 A4).
rewrite A5. exact (atoms_ok_agree 64 E0' Es _ kAGs T3 kFACTS').
Qed.
Lemma kHS5 : st_ok tfibsegs Es (mkSS (ss_pc SSK3) (sr_set (ss_regs SSK3) 10%bv (SLit 1)) (ss_mem SSK3) (ss_resv SSK3) (ss_facts SSK3)) ms3.
Proof.
apply (st_ok_pin_regU Es SSK3 ms3 10%bv (SLit 1) kHS4); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs Es SSK3 ms3 10%bv kHS4) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity.
Qed.
Lemma kregion_ok_agree_on_lt : forall r, In r (tl REG0K) -> region_ok tfibsegs E0' (mrestrict (w_H W') memR) r -> region_ok tfibsegs Es (ms_mem ms3) r.
Proof.
intros r Hr H. pose proof tlREG0K_facts as (T1 & _). unfold ms3. cbn [ms_mem mkst].
apply (region_ok_agree tfibsegs 64 E0' Es _ r kAGs); [|exact H]. exact (proj1 (forallb_forall _ _) T1 r Hr).
Qed.
Lemma kHS6 : st_ok tfibsegs Es (mkSS RA_REFILL (sr_set (ss_regs SSK3) 10%bv (SLit 1)) [K3bst; K3scr; K3top] None (ss_facts SSK3)) ms3.
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U.
pose proof (st_ok_mem_surgery Es _ ms3 [K3bst; K3scr; K3top] kHS5) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val Es (Some 2%nat) = sp0) by (cbn [base_val]; exact kEs2).
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons; [|exact (Forall_inv_tail (Forall_inv_tail HF))].
pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, K3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; lia|]. split; [clear - U; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 U; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia|]. apply kPRES'. clear - Ho; unfold ASTACK; lia.
- unfold K3bst, K3scr, K3top. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV. repeat split; lia.
Qed.
Lemma kHS7 : st_ok tfibsegs Es MK_AFTER ms3.
Proof.
rewrite MK_AFTER_eq3. pose proof tlREG0K_facts as (T1 & T2 & T3).
pose proof (st_ok_mem_surgery Es _ ms3 ([K3bst; K3scr; K3top] ++ tl REG0K) kHS6) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros HM. pose proof kPAIRS' as PP. change REG0K with (hd R_bst REG0K :: tl REG0K) in PP. destruct PP as [A0 PT].
pose proof kREG0' as RR. change REG0K with (hd R_bst REG0K :: tl REG0K) in RR. apply Forall_inv_tail in RR.
apply mem_ok_app; [exact HM | exact T2 | | |].
- apply Forall_forall. intros r Hr. apply (kregion_ok_agree_on_lt r Hr). exact (proj1 (Forall_forall _ _) RR r Hr).
- exact (pairwise_disjoint_agree 64 E0' Es (tl REG0K) kAGs T1 PT).
- intros r Hr. pose proof (all_disjoint_In E0' _ _ r A0 Hr) as D0.
assert (Hb : obase_lt 64 (YP09.r_base r) = true).
{ pose proof (proj1 (forallb_forall _ _) T1 r Hr) as Ha. unfold region_atoms_lt in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
pose proof (extent_disjoint_agree 64 E0' Es (hd R_bst REG0K) r kAGs eq_refl Hb D0) as D. clear D0.
cbn [all_disjoint]. repeat split; apply extent_disjoint_sym;
(eapply (Dm.extent_disjoint_sub Es (hd R_bst REG0K) r); [reflexivity | cbn; unfold ASTACK; lia | cbn; lia | cbn; lia | exact D]).
Qed.
Lemma kATJ : YFj6.at_ST W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 MK_AFTER W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), Es. split; [reflexivity|]. split; [exact kHEs|].
split; [unfold msR; rewrite restrict_mkst_fx; exact kHS7|].
split; [intros x _; reflexivity|]. split; [exact kPRES' | exact kBUF'].
Qed.
Lemma kTAILJ : amreal tfibsegs (malloc_join n tr cl S') W' (cfg_at tfibsegs RA_REFILL regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> FSU.malloc_leafU tfibsegs B ly S' UP W' regs0 memR mdR n r W'' c'').
Proof.
replace (cfg_at tfibsegs RA_REFILL regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@YFj7.segJ _ _ W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kHcl kHv' kHcnt' kHv2' kLY kIMG kHsp DPOST' Nrange l off W' cR kATJ). }
intros W2 c2 _ HJ. pose proof (proj1 HJ) as EW. subst W2.
exact (Mp3.tail_innerU W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 B S' l off UP DPOST'
  kHcl kHv' kHcnt' Hjb kHv2' kLY kIMG Hn kHtp kHsp kHKpres' kHSKpres' kHPB250' Nrange kHcl_def TS kHTSD kHARU' kPRES'
  CI Hcache' kHcl_class kHcnt_def' kHoff_def' kHcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def
  (m_vm_materialized mdR) kHra kHra4096 kHch' U1 kHgp (tr_admit_len _ _ _ (ts_universe B TS) Htr) D1 (fun z m H => H) (fun z m H => H) eq_refl
  c2 HJ).
Qed.
End kk.
End kj.
End kg.

Section kh.
Variables (S' : astate) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis WFP' : WfP (as_universe B) 0 1 1 S'.
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : FSU.acall_postU tfibsegs B RSTACK ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.
Let msR : machine_state := mkst regsR (w64 RA_REFILL) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Let ms3 : machine_state := mkst regsR (w64 RA_REFILL) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Let E1 : env := havoc Em hRFk (map (getr regsR) CLOB).
Lemma kHE1 : forall k, (k < aHAV)%nat -> ew E1 k = ew E0m k.
Proof. intros k Hk. unfold E1. unfold aHAV in Hk. rewrite ew_havoc_old by (unfold hRFk; lia). apply HEm. exact Hk. Qed.
Lemma kE1_2 : bv_unsigned (ew E1 2) = sp0. Proof. rewrite (kHE1 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma kHSN : st_ok tfibsegs E1 MK_N0 ms3.
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as Us.
pose proof (kHS3 S' W' regsR memR mdR WFP' RO CI POST) as H3. fold E1 in H3. change (mkst regsR (w64 RA_REFILL) (mrestrict (w_H W') memR) (seg_rom tfibsegs)) with ms3 in H3.
assert (H4 : st_ok tfibsegs E1 (mkSS (ss_pc SSK3) (sr_set (ss_regs SSK3) 10%bv (SLit 0)) (ss_mem SSK3) (ss_resv SSK3) (ss_facts SSK3)) ms3).
{ apply (st_ok_pin_regU E1 SSK3 ms3 10%bv (SLit 0) H3); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs E1 SSK3 ms3 10%bv H3) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity. }
rewrite MK_N0_eq. pose proof (st_ok_mem_surgery E1 _ ms3 ([K3bst; K3scr; K3top] ++ NREGS) H4) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X H4 H3.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val E1 (Some 2%nat) = sp0) by (cbn [base_val]; exact kE1_2).
pose proof (kPRES' S' W' regsR memR mdR WFP' RO CI POST) as PR.
assert (OOM1 : val_mem tfibsegs (mrestrict (w_H W') memR) (TFIB_OOM + 1) 1 1).
{ assert (OU : AllocR.offU UP (TFIB_OOM + 1)) by (apply koffU_lo; unfold TFIB_OOM, SHADOW_OFF; lia).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (kHARm'u S' W' regsR memR mdR WFP' RO CI POST)) (z1 (ANum (TFIB_OOM + 1)) 1)) as C.
rewrite (ts_const B TS ly) in C. specialize (C ltac:(unfold Tfib_const; apply in_app_iff; right; apply in_app_iff; left; apply (nth_error_In _ 60); reflexivity)).
apply (AllocR.val_mem_of_unpoison (w_H W') UP memR (TFIB_OOM + 1) 1 1); [intros k Hk; replace (Z.of_nat k) with 0 by lia; rewrite Z.add_0_r; exact OU|].
exact (cell_holds_val_mem B ly (w_H W') (FSP.unpoison UP memR) (ANum (TFIB_OOM + 1)) 1 (ANum 1) C). }
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons.
{ pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, K3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; lia|]. split; [clear - Us; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 Us; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia|]. apply PR. clear - Ho; unfold ASTACK; lia. }
apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HF)))|].
unfold NREGS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ unfold region_ok, lit1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia |]. rewrite Z.add_0_l. exact OOM1.
+ unfold region_ok, oomR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply (Dk.rw_writable ly regs0 n). unfold TFIB_OOM in *. lia.
+ unfold region_ok, errR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_ERRNO; lia|]. split; [unfold TFIB_ERRNO; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply (Dk.rw_writable ly regs0 n). unfold TFIB_ERRNO in *. lia.
- unfold K3bst, K3scr, K3top, NREGS, lit1, oomR, errR. cbn [pairwise_disjoint all_disjoint app]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BV. cbn [base_val]. clear - Hlo K1 Us. unfold TFIB_OOM, TFIB_ERRNO, ASTACK, kHighMemBeg in *. repeat split; lia.
Qed.
Lemma kATN : YFj9.at_STN W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 MK_N0 W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), E1. split; [reflexivity|]. split; [exact kHE1|].
split; [unfold msR; rewrite restrict_mkst_fx; exact kHSN|]. split; [reflexivity | exact (kPRES' S' W' regsR memR mdR WFP' RO CI POST)].
Qed.
Lemma kerrno_not_owned : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S' a.
Proof.
intros a Ha O. pose proof (kHAR'u S' W' regsR memR mdR WFP' RO CI POST) as AR'.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. rewrite YB13.tfib_segs_eq.
eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. lia. }
apply (proj1 (AR_owned_image_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a AR' IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.
Lemma koom_owned : aowned B ly S' TFIB_OOM.
Proof.
apply (own_area B ly S' _ (as_oom_byte B, 1) TFIB_OOM (kHARm'u S' W' regsR memR mdR WFP' RO CI POST)); [unfold asyms_areas; cbn; tauto|].
cbn [fst snd]. rewrite (ts_oom B TS). lia.
Qed.
Lemma kTAILN : amreal tfibsegs (malloc_join n tr cl S') W' (cfg_at tfibsegs RA_REFILL regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W'' c'').
Proof.
pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as Us.
pose proof (kERRNO_low S' W' regsR memR mdR WFP' RO CI POST) as EL.
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K. cbn [amreal].
replace (cfg_at tfibsegs RA_REFILL regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono.
{ exact (@YFj9.segN _ _ W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 kHvd kLY kIMG kHtp kHra kHsp DPOSTm [] 0 W' cR kATN). }
intros W6 c6 _ HR [WF' QT']. cbn [fst snd] in WF', QT' |- *.
destruct HR as (-> & regs' & mem' & mat & -> & A0 & CS' & MEQ' & PRS' & VOOM & VERR).
pose proof (kPOSTd S' W' regsR memR mdR WFP' RO CI POST) as (AR' & _ & WLE' & CS & SIO & FR & _).
pose proof (kHARm'u S' W' regsR memR mdR WFP' RO CI POST) as M'.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy mdR) mat mdR).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [|split; [rewrite A0; cbn [sptr_addr sptr_exp aeval]; reflexivity | exact QT']].
assert (NWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> mem' (Z_to_bv 64 a) = memR (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3. apply MEQ'. rewrite unsigned_lit_small by exact Ra. unfold YFj9.WINN. fold sp0. clear - N1 N2 N3. unfold IFRAME, ASTACK in *. lia. }
assert (NWINu : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
  FSP.unpoison UP mem' (Z_to_bv 64 a) = FSP.unpoison UP memR (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned (Z_to_bv 64 a))); [reflexivity | exact (NWIN a Ra N1 N2 N3)]. }
split; [|split].
2:{ exact (proj1 (proj2 POST)). }
2:{ intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S' UP W' memR mdR s (kHARU' S' W' regsR memR mdR WFP' RO CI POST) Hs) as (_ & L1 & L2).
  rewrite (FSP.aview_at tfibsegs (w_H W') mem' memR s
    (NWIN s ltac:(unfold SHADOW_OFF, kHighMemBeg in *; lia) ltac:(clear - L1 L2 Hlo K1; unfold ASTACK, kHighMemBeg, SHADOW_OFF in *; lia)
          ltac:(clear - L1; unfold TFIB_OOM, SHADOW_OFF in *; lia) ltac:(clear - L1; unfold TFIB_ERRNO, SHADOW_OFF in *; lia))).
  exact ((proj2 (proj2 POST)) s Hs). }
split.
{
apply (YFi5.AR_oom B ly S' W' (FSP.unpoison UP memR) (FSP.unpoison UP mem') mdR (with_vm_backing (m_vm_lazy mdR) mat mdR) TS AR').
- intros a Ra Ho NX. apply FSP.aview_at. apply NWINu; [exact Ra | | clear - NX; unfold YFi5.XJ in NX; lia |].
  + intros ST. exact (AR_stack_law_ok tfibsegs B ly S' W' (FSP.unpoison UP memR) mdR a AR' ltac:(clear - ST Hlo Hhi; unfold ASTACK in *; lia) Ho).
  + intros ER. exact (kerrno_not_owned a ER Ho).
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (AV : forall m, aview tfibsegs (w_H W') m a = aview tfibsegs (w_H W') m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
  rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  destruct (Z_le_gt_dec (sp0 - ASTACK) a') as [G1|G1]; [destruct (Z_lt_ge_dec a' sp0) as [G2|G2]|].
  { apply Dm.apresent_aview_some; [clear - G1 G2 K1 Ha' Hlo; unfold TFIB_IMG_END, kHighMemBeg, ASTACK in *; lia|].
    apply AllocR.apresent_to_unpoison. apply PRS'. lia. }
  all: destruct (Z.eq_dec a' TFIB_OOM) as [->|NO]; [apply Dk.aview_rw_some; unfold TFIB_OOM; lia|].
  all: destruct (Z_le_gt_dec TFIB_ERRNO a') as [G3|G3];
    [destruct (Z_lt_ge_dec a' (TFIB_ERRNO + 4)) as [G4|G4]; [apply Dk.aview_rw_some; unfold TFIB_ERRNO in *; lia|]|].
  all: rewrite (FSP.aview_at tfibsegs (w_H W') (FSP.unpoison UP mem') (FSP.unpoison UP memR) a' (NWINu a' Ha' ltac:(lia) NO ltac:(lia))); exact Hv.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. unfold YG0n.w64. apply NWINu.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
  + clear - Ha K1 Hlo. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. lia.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. lia.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. lia.
}
split; [apply layout_le_refl|].
split; [exact WLE'|].
split.
{
intros r Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - RR CS'. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst r; apply CS'; cbn [In];
repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ (Dm.same_io_wvb md0 mat1) SIO) (Dm.same_io_wvb mdR mat))|].
split; [|intros a Ha; apply AllocR.apresent_to_unpoison; apply PRS'; exact Ha].
intros a Ha NO NO' NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (intros O; apply NO; exact (proj1 (Dm.aowned_tick B ly S a) O)).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ; left; exact X).
assert (NER : ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4)) by (intros X; apply NS; unfold ascratch; right; rewrite (ts_errno B TS); exact X).
assert (NOO : a <> TFIB_OOM) by (intros ->; exact (NO' koom_owned)).
rewrite (FSP.aview_at tfibsegs (w_H W') (FSP.unpoison UP mem') (FSP.unpoison UP memR) a (NWINu a Ha NST NOO NER)).
rewrite (FR a Ha NO1 NO').
- assert (OU : AllocR.offU UP a) by (apply (AllocR.offU_not_owned B ly S1 UP W mem0 md0 a kHARU1 Ha NO1)).
  rewrite (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU), (AllocR.aview_unpoison (w_H W) UP mem0 a OU).
  exact (kAG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite kSP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; apply NS; [left; clear - X; unfold ASTACK, RSTACK in *; lia | right; exact X].
- intros [].
Qed.
End kh.

Lemma kSHIFTU : forall S' W' regsR memR mdR, regs_only S1 S' ->
FSU.acall_postU tfibsegs B RSTACK ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR ->
forall r W6 c6, FSU.malloc_leafU tfibsegs B ly S' UP W' regs0 memR mdR n r W6 c6 ->
FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W6 c6.
Proof.
intros S' W' regsR memR mdR RO POST r W6 c6 (ly' & regs' & mem' & md' & -> & AP & RA0 & QT).
pose proof kHsp as (Hlo & Hbot & Hhi & Hal). pose proof kSTK as [K1 K2]. pose proof kUsp as U.
assert (EL : as_errno B + 4 <= kHighMemBeg) by (rewrite (ts_errno B TS); unfold TFIB_ERRNO, kHighMemBeg; lia).
destruct AP as (AP6 & OK6 & PO6). destruct AP6 as (AR6 & LLE & WLE6 & CS6 & SIO6 & FR6 & PRS6).
destruct POST as (POSTd' & _ & _). destruct POSTd' as (AR' & _ & WLE' & _ & SIO & FR & _).
exists ly', regs', mem', md'. split; [reflexivity|]. split; [|split; [exact RA0 | exact QT]].
split; [|split; [exact OK6 | exact PO6]].
split; [exact AR6|]. split.
{ destruct RO as (_ & Rsecs & _). rewrite Rsecs in LLE. exact LLE. }
split; [exact (wle_trans _ _ _ _ WLE' WLE6)|]. split; [exact CS6|].
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ (Dm.same_io_wvb md0 mat1) SIO) SIO6)|]. split; [|exact PRS6].
intros a Ha NO NO6 NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (intros O; apply NO; exact (proj1 (Dm.aowned_tick B ly S a) O)).
assert (NO' : ~ aowned B ly S' a) by (intros O; apply NO1; exact (proj1 (Dm.aowned_regs_only B ly S1 S' a RO) O)).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ; left; exact X).
rewrite (FR6 a Ha NO' NO6 NS NE). rewrite (FR a Ha NO1 NO').
- assert (OU : AllocR.offU UP a) by (apply (AllocR.offU_not_owned B ly S1 UP W mem0 md0 a kHARU1 Ha NO1)).
  rewrite (AllocR.aview_unpoison (w_H W) UP (ms_mem ms1) a OU), (AllocR.aview_unpoison (w_H W) UP mem0 a OU).
  exact (kAG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite kSP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; apply NS; [left; clear - X; unfold ASTACK, RSTACK in *; lia | right; exact X].
- intros [].
Qed.
End kf.

Theorem malloc_misskU :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ kHARm0u) kHev); [unfold MALLOC_MAX; lia | exact Hlive | exact Htr]. }
rewrite (malloc_primary_eq n tr S kFP). eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
fold S1. change (chunk_class n) with cl.
eapply (YG0d.amreal_mbind tfibsegs (refill_tree cl) (fun _ : unit => malloc_join n tr cl) S1 W _
(fun r W' c' => exists ms1 mat1 Em,
((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em MK_CALL (restrict (w_H W) ms1) /\
(forall x : word, ~ YFj8.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
((WfP (as_universe B) (1 - 1) 1 1 (snd r) /\ regs_only S1 (snd r) /\ st_cache_inited (snd r) = true) /\
AllocR.refill_leafU B ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl r W' c'))).
-
eapply amreal_SRr_pre; [exact kMISS1|]. intros W1 c1 _ HC.
destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
pose proof (Rt.tfib_refill_okU B TS ly S1 UP W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl
  (kREFILL_PREu ms1 mat1 Em HEm HSC MEQW PRESW BUFW)) as RR.
unfold cfg_at, A_Refill in RR. rewrite (kms1_shape ms1 mat1 Em HEm HSC MEQW PRESW BUFW) at 1.
change (md0' mat1) with (with_vm_backing (m_vm_lazy md0) mat1 md0) in RR at 1.
pose proof (refill_tree_apost (as_universe B) 1 1 1 S1 cl kWfP1 kHcl ltac:(lia) (aregime_preg_tick S cl kHev kHcl)) as APOST.
eapply amreal_mono; [| exact (amreal_apost tfibsegs _ _ W _ _ APOST RR)].
intros r W' c' H. exists ms1, mat1, Em. split; [|exact H]. repeat (split; [assumption|]). exact BUFW.
-
intros [] S' W' c' (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & (WFP' & RO & CI) & HL). cbn [fst snd] in WFP', RO, CI, HL.
destruct HL as (regsR & memR & mdR & -> & POST & HA0 & _). cbn [snd] in HA0.
unfold raZ. rewrite (kR_ra ms1 mat1 Em HEm HSC MEQW PRESW BUFW). unfold w64 at 1. rewrite unsigned_lit_small by lia.
destruct (pc_chunks (cache S' cl)) as [|x t] eqn:El.
+
eapply amreal_mono; [| exact (kTAILN ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR WFP' RO CI POST El HA0)].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP. apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ kHQT))).
+ assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
destruct LX as (l & off & LX). rewrite LX in El.
destruct (kjunk_real ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR WFP' RO CI POST l off El HA0)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| exact (kTAILJ ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR WFP' RO CI POST l off El HA0 j0 jb j1 j2 j3 j4 Hj0 Hj1 Hj2 Hj3 Hj4 Hjb Hjb_def)].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP.
apply (kSHIFTU ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR RO POST (p, s6) W6 c6).
apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ kHQT))).
Qed.
End ka.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The primary path for any UP: the two miss arms and the two hit arms, joined on the cache. Port-from:           *)
(*    lib/B/YFij.v:62 (malloc_miss) and lib/B/YFij.v:69 (malloc_prim).                                              *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section pj.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Variable UP : list (Z * Z).
Let tr : list Z := call_trace ly PC_MALLOC_RA0 regs0 ch.
Hypothesis PRE : FSU.acall_preU tfibsegs B ly S UP W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 0 <= n <= 64512.
Hypothesis Htr : tr_admit (as_universe B) S tr.
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.

Lemma prim_fpU : from_primary n = true.
Proof.
clear - Nrange. unfold from_primary, needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize. apply Z.leb_le.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M.
destruct (Z.leb_spec n 48); [change (Z.shiftl 16 0) with 16; lia|].
destruct (Z.leb_spec n 96); [change (Z.shiftl 16 1) with 32; lia|].
destruct (Z.leb_spec n 448); [change (Z.shiftl 16 2) with 64; lia|].
destruct (Z.leb_spec n 3968); [change (Z.shiftl 16 3) with 128; lia|].
destruct (Z.leb_spec n 16128); [change (Z.shiftl 16 4) with 256; lia|].
destruct (Z.leb_spec n 32256); [change (Z.shiftl 16 5) with 512; lia|].
destruct (Z.leb_spec n 64512); [change (Z.shiftl 16 6) with 1024; lia|]. lia.
Qed.

Theorem malloc_missU : pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
intros Hmiss. destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
- exact (malloc_missgU B TS U1 D1 ly S W regs0 mem0 md0 n ch UP PRE Hn ltac:(lia) Htr Hlive Hmiss).
- exact (malloc_misskU B TS U1 D1 ly S W regs0 mem0 md0 n ch UP PRE Hn ltac:(lia) Htr Hlive Hmiss).
Qed.

Theorem malloc_hitU : forall l off, st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
intros l off Hinited Hcache. destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
- exact (Mp2.malloc_hitgU B TS U1 D1 ly S W regs0 mem0 md0 n ch UP PRE Hn ltac:(lia) Htr Hlive l off Hinited Hcache).
- exact (Mp3.malloc_hitkU B TS U1 D1 ly S W regs0 mem0 md0 n ch UP PRE Hn ltac:(lia) Htr Hlive l off Hinited Hcache).
Qed.

Theorem malloc_primU :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs PC_WRAP_MALLOC regs0 mem0 md0) (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
destruct (pc_chunks (cache S (chunk_class n))) as [|x t] eqn:El; [exact (malloc_missU El)|].
assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
destruct LX as (l & off & LX). rewrite LX in El.
pose proof (proj1 (proj1 (proj1 PRE))) as HARm.
pose proof (primary_geometry n ltac:(lia) prim_fpU) as (Hcl & _).
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) (chunk_class n) ltac:(lia))) as WC.
destruct (st_cache_inited S) eqn:CI; [exact (malloc_hitU l off CI El)|].
exfalso. rewrite WC in El. cbn in El. destruct l; discriminate El.
Qed.
End pj.
End a.

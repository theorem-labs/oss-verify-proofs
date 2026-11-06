(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFf8.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/AFf8.v, with its module paths changed; 234 of its 271 lines of code are new or changed and 1383 lines of the source are left out. *)
(* Free's recycle_chunk of a secondary chunk (lib/A/AFg9.v) for any U, lane rs, part 1: what needs only the walk-spec files lib/A/AFgu.v, AFgx.v, AFgv.v. The three run records moved from FSupoison.unpoison UP mem to mem, and the return post at_RET moved from mem to unpoison UP mem. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFew AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AFgu AFgx AFgv FSupoison FSupoisonAllocR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize,
kPtrArrayResv, t_stats, KSTACK, TFIB_IMG_END, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_ALLOCATOR, AFgu.GFRAME, AFgx.GFRAME, AFgv.GDEPTH in *.
(* The cases of a symbolic state's region list. *)
Ltac reg_split Hr := repeat match type of Hr with
  | In _ (_ :: _) => destruct Hr as [<-|Hr]
  | In _ [] => destruct Hr
  | In _ (_ ++ _) => apply in_app_iff in Hr as [Hr|Hr]
  end.
Ltac reg_open Ha := cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val AFeq.flit8 AFeq.flit1 AFeq.flit4 AFeq.fatom8] in Ha.

Section rs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Application memory: the bytes below the shadow and above it. No byte of U is there (FSupoisonAllocR.offU_app). *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Definition appb (a : Z) : Prop := (0 <= a < SHADOW_OFF) \/ (kHighMemBeg <= a < 2 ^ 64).

Lemma offU_appb : forall B ly S UP W mem md a, FSP.ARU tfibsegs B ly S UP W mem md -> appb a -> FAR.offU UP a.
Proof.
intros B ly S UP W mem md a H [Ha|Ha]; apply (FAR.offU_app B ly S UP W mem md a H); unfold SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

(* unpoison reads each byte from that byte only. *)
Lemma unpoison_eq : forall UP (m1 m2 : word -> option byte) (x : word), m1 x = m2 x -> FSP.unpoison UP m1 x = FSP.unpoison UP m2 x.
Proof. intros UP m1 m2 x E. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact E]. Qed.
Lemma unpoison_zero : forall UP (m : word -> option byte) (x : word), m x = Some (Z_to_bv 8 0) -> FSP.unpoison UP m x = Some (Z_to_bv 8 0).
Proof. intros UP m x E. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact E]. Qed.

Section x.
Variable UP : list (Z * Z).
Hypothesis OFF : forall a, appb a -> FAR.offU UP a.

Lemma vm_real : forall (H : word -> bool) (m : word -> option byte) a (w : nat) v, (forall b, a <= b < a + Z.of_nat w -> appb b) ->
  val_mem tfibsegs (mrestrict H (FSP.unpoison UP m)) a w v -> val_mem tfibsegs (mrestrict H m) a w v.
Proof. intros H m a w v O V. apply (FAR.val_mem_of_unpoison H UP m a w v); [intros kk Hk; apply OFF, O; lia | exact V]. Qed.
Lemma vm_unp : forall (H : word -> bool) (m : word -> option byte) a (w : nat) v, (forall b, a <= b < a + Z.of_nat w -> appb b) ->
  val_mem tfibsegs (mrestrict H m) a w v -> val_mem tfibsegs (mrestrict H (FSP.unpoison UP m)) a w v.
Proof. intros H m a w v O V. apply (FAR.val_mem_to_unpoison H UP m a w v); [intros kk Hk; apply OFF, O; lia | exact V]. Qed.
Lemma ap_real : forall (H : word -> bool) (m : word -> option byte) a, appb a -> apresent H (FSP.unpoison UP m) a -> apresent H m a.
Proof. intros H m a O P. exact (FAR.apresent_of_unpoison H UP m a (OFF a O) P). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The record of the first run segment (lib/A/AFgu.v free_hyps, lib/A/AFf5.v segGA).                              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section ga.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (m n q : Z).
Theorem fhA_real : AFgu.free_hyps W ly regs0 (FSP.unpoison UP mem0) m n q -> AFgu.free_hyps W ly regs0 mem0 m n q.
Proof.
intros FH. pose proof (AFgu.LYB W ly regs0 _ m n q FH) as (_ & _ & _ & _ & L5 & L6 & _).
destruct FH as [LY IMG RG HSP HAL PRS HM SB [HN HN'] [HQ HQ'] MUT SEED].
set (sp0 := bv_unsigned (YK11.getr regs0 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (STK : forall b, ly_stk_lo ly <= b < ly_stk_hi ly -> appb b) by (intros b Hb; right; unfold kHighMemEnd in L5; lia).
assert (LOW : forall b, 0 <= b < SHADOW_OFF -> appb b) by (intros b Hb; left; exact Hb).
assert (RO : FAR.regions_offU UP (AFgu.E0 ly regs0 m n q) (ss_mem AFgu.SS0)).
{ intros rg a Hr Ha. apply OFF. unfold AFgu.SS0, AFgu.REG0 in Hr. cbn [ss_mem] in Hr. reg_split Hr; reg_open Ha.
  - unfold AFgu.R_STK in Ha. reg_open Ha. rewrite (AFgu.E2 ly regs0 m n q) in Ha. fold sp0 in Ha. apply STK. clear - Ha HSP. numconst. lia.
  - unfold AFgu.R_MUT in Ha. reg_open Ha. apply LOW. numconst. lia.
  - apply LOW. numconst. lia.
  - apply LOW. numconst. lia.
  - apply LOW. numconst. lia. }
constructor; try assumption.
- intros a Ha. apply (ap_real _ _ a); [apply STK; clear - Ha HSP; numconst; lia | exact (PRS a Ha)].
- apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact SB].
- split; [|exact HN']. apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact HN].
- split; [|exact HQ']. apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact HQ].
- apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact MUT].
- apply (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO)). exact SEED.
Qed.
End ga.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The record of the segment after the scan of the secondary array (lib/A/AFgx.v free_hyps, lib/A/AFfd.v segGX).  *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section gx.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte).
Variables (m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 : Z).
Local Notation E0 := (AFgx.E0 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation E2 := (AFgx.E2 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqT := (AFgx.EqT ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqC := (AFgx.EqC ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqM := (AFgx.EqM ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqMAP := (AFgx.EqMAP ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Theorem fhX_real : AFgx.free_hyps W ly regs0 (FSP.unpoison UP mem0) m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 ->
  AFgx.free_hyps W ly regs0 mem0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4.
Proof.
intros FH. pose proof (AFgx.LYB W ly regs0 _ m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 FH) as (ZT & ZT2 & _ & _ & _ & _ & L5 & L6 & _ & ZC & ZC2 & _).
destruct FH as [LY IMG HTP RG HSP HAL PRS [F0 [F8 [F16 [F24 [F32 [F40 [F48 [F56 [F64 F72]]]]]]]]] SV HMAP [MH0 [MH8 MHP]] HHW [HD0 [HD4 HDP]] MUT SB
  [TS0 [TS8 TS152]] [JS40 [JS48 JSR]] SEED].
set (sp0 := bv_unsigned (YK11.getr regs0 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (STK : forall b, ly_stk_lo ly <= b < ly_stk_hi ly -> appb b) by (intros b Hb; right; unfold kHighMemEnd in L5; lia).
assert (LOW : forall b, 0 <= b < SHADOW_OFF -> appb b) by (intros b Hb; left; exact Hb).
assert (Z3 : forall x sz b, zone3 x sz -> x <= b < x + sz -> appb b).
{ intros x sz b Z Hb. unfold appb. clear - Z Hb. numconst. lia. }
pose proof HMAP as (HM1 & HM2 & HM3 & HM4 & HM5 & HM6 & HM7 & HM8 & _). pose proof HHW as [HW1 HW2].
assert (MB : forall b, map <= b < map + len -> appb b) by (intros b Hb; exact (Z3 map len b HM1 Hb)).
assert (HDR : forall b, m <= b < m + 8 -> appb b).
{ intros b Hb. apply MB. clear - Hb HM3 HM5 HM6 HM7 HM8 HW2. Z.div_mod_to_equations. lia. }
assert (TB : forall b, ly_T ly <= b < ly_T ly + kThreadObjSize -> appb b) by (intros b Hb; exact (Z3 _ _ b ZT Hb)).
assert (CB : forall b, ly_C ly <= b < ly_C ly + 256 -> appb b) by (intros b Hb; exact (Z3 _ _ b ZC Hb)).
assert (UT : 0 <= ly_T ly < 2 ^ 64) by (clear - ZT ZT2; numconst; lia).
assert (UC : 0 <= ly_C ly < 2 ^ 64) by (clear - ZC ZC2; numconst; lia).
assert (UM : 0 <= m < 2 ^ 64) by (clear - HM1 HM2 HM6 HM7 HW2; numconst; lia).
assert (UMAP : 0 <= map < 2 ^ 64) by (clear - HM1 HM2 HM4; numconst; lia).
assert (RO : FAR.regions_offU UP E0 (ss_mem AFgx.SS0)).
{ intros rg a Hr Ha. apply OFF. unfold AFgx.SS0, AFgx.REG0 in Hr. cbn [ss_mem] in Hr. reg_split Hr; reg_open Ha.
  - unfold AFgx.R_STK in Ha. reg_open Ha. rewrite E2 in Ha. fold sp0 in Ha. apply STK. clear - Ha HSP. numconst. lia.
  - unfold AFgx.R_MAPH in Ha. reg_open Ha. rewrite EqMAP in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact UMAP. apply MB. lia.
  - unfold AFgx.R_HDR in Ha. reg_open Ha. rewrite EqM in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact UM. apply HDR. lia.
  - unfold AFgx.R_MUT1 in Ha. reg_open Ha. apply LOW. clear - Ha. numconst. lia.
  - unfold AFgx.R_CTX in Ha. reg_open Ha. rewrite EqC in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact UC. apply CB. lia.
  - unfold AFgx.R_JST in Ha. reg_open Ha. rewrite EqT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact UT. apply TB. clear - Ha. numconst. lia.
  - apply LOW. clear - Ha. numconst. lia.
  - apply LOW. clear - Ha. numconst. lia.
  - apply LOW. clear - Ha. numconst. lia.
  - apply LOW. clear - Ha. numconst. lia.
  - apply LOW. clear - Ha. numconst. lia.
  - apply LOW. clear - Ha. numconst. lia. }
assert (FR : forall b, sp0 <= b < sp0 + 80 -> appb b) by (intros b Hb; apply STK; clear - Hb HSP; numconst; lia).
constructor; try assumption.
- intros a Ha. apply (ap_real _ _ a); [apply STK; clear - Ha HSP; numconst; lia | exact (PRS a Ha)].
- refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); (apply vm_real; [intros b Hb; apply FR; lia | assumption]).
- split; [apply vm_real; [intros b Hb; apply MB; lia | exact MH0]|]. split; [apply vm_real; [intros b Hb; apply MB; lia | exact MH8]|].
  intros a Ha. apply (ap_real _ _ a); [apply MB; lia | exact (MHP a Ha)].
- split; [apply vm_real; [intros b Hb; apply HDR; lia | exact HD0]|]. split; [apply vm_real; [intros b Hb; apply HDR; lia | exact HD4]|].
  intros a Ha. apply (ap_real _ _ a); [apply HDR; lia | exact (HDP a Ha)].
- apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact MUT].
- apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact SB].
- split; [apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact TS0]|].
  split; [apply vm_real; [intros b Hb; apply CB; lia | exact TS8]|]. apply vm_real; [intros b Hb; apply CB; lia | exact TS152].
- split; [apply vm_real; [intros b Hb; apply TB; clear - Hb; numconst; lia | exact JS40]|].
  split; [apply vm_real; [intros b Hb; apply TB; clear - Hb; numconst; lia | exact JS48]|].
  destruct JSR as (J1 & J2 & JP). split; [exact J1|]. split; [exact J2|].
  intros a Ha. apply (ap_real _ _ a); [apply TB; clear - Ha; numconst; lia | exact (JP a Ha)].
- apply (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO)). exact SEED.
Qed.
End gx.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The record of the munmap segment (lib/A/AFgv.v free_hyps, lib/A/AFf8.v segGD). Its one non-application field   *)
(*    is the presence of the shadow of the unmapped range (fh_sh_pres), whose bytes are off U by OFFS.              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section gd.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte).
Variables (map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 : Z) (own small : bool).
Local Notation E0 := (AFgv.E0 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation E2 := (AFgv.E2 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqT := (AFgv.EqT ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqC := (AFgv.EqC ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqMAP := (AFgv.EqMAP ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQI := (AFgv.EqQI ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQL := (AFgv.EqQL ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqLAST := (AFgv.EqLAST ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Hypothesis OFFS : forall a, AFgv.SHAv map <= a < AFgv.SHAv map + AFgv.CNTv len -> FAR.offU UP a.
Theorem fhD_real :
  AFgv.free_hyps W ly regs0 (FSP.unpoison UP mem0) map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small ->
  AFgv.free_hyps W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small.
Proof.
intros FH.
pose proof (AFgv.LYB W ly regs0 _ map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH) as (ZT & ZT2 & _ & ZC & ZC2 & _ & L7 & L8 & _).
destruct FH as [LY IMG HTP HRA RG HSP HAL PRS SV HMAP HDJ [MH0 [MH8 [MH24 MHP]]] HARR HQ [QI0 QIP] HQL HLST HOWN HLSTH HNS
  [J1 [J2 [J3 [J4 JR]]]] MUT [TS0 [TS8 TS152]] [JS88 [JS96 JSR]] SHP SEED].
set (sp0 := bv_unsigned (YK11.getr regs0 2)) in *.
pose proof HMAP as (HM1 & HM2 & HM3 & HM4 & HM5 & _). pose proof HARR as (HA1 & HA2 & HA3 & HA4 & HA5 & HA6 & HA7 & _).
pose proof HLST as (HL1 & HL2 & HL3).
assert (STK : forall b, ly_stk_lo ly <= b < ly_stk_hi ly -> appb b) by (intros b Hb; right; clear - Hb L7 L8; numconst; lia).
assert (LOW : forall b, 0 <= b < SHADOW_OFF -> appb b) by (intros b Hb; left; exact Hb).
assert (Z3 : forall x sz b, zone3 x sz -> x <= b < x + sz -> appb b) by (intros x sz b Z Hb; unfold appb; clear - Z Hb; numconst; lia).
assert (MB : forall b, map <= b < map + len -> appb b) by (intros b Hb; exact (Z3 _ _ b HM1 Hb)).
assert (QB : forall b, q <= b < q + kPtrArrayResv -> appb b) by (intros b Hb; exact (Z3 _ _ b HA5 Hb)).
assert (LB : forall b, lst <= b < lst + 8192 -> appb b) by (intros b Hb; exact (Z3 _ _ b HL1 Hb)).
assert (TB : forall b, ly_T ly <= b < ly_T ly + kThreadObjSize -> appb b) by (intros b Hb; exact (Z3 _ _ b ZT Hb)).
assert (CB : forall b, ly_C ly <= b < ly_C ly + 256 -> appb b) by (intros b Hb; exact (Z3 _ _ b ZC Hb)).
assert (QIB : forall b, qi <= b < qi + 8 -> appb b) by (intros b Hb; apply QB; clear - Hb HA1 HA2 HA3; unfold kPtrArrayResv; lia).
assert (QLB : forall b, ql <= b < ql + 8 -> appb b) by (intros b Hb; apply QB; clear - Hb HA1 HA2 HA4; unfold kPtrArrayResv; lia).
assert (U : forall x sz, zone3 x sz -> 0 <= sz -> 0 <= x < 2 ^ 64) by (intros x sz Z Hs; clear - Z Hs; numconst; lia).
assert (UA : forall b, appb b -> 0 <= b < 2 ^ 64) by (intros b [Hb|Hb]; unfold SHADOW_OFF, kHighMemBeg in *; lia).
assert (UMAP : 0 <= map < 2 ^ 64) by (apply (U _ _ HM1); lia).
assert (UT : 0 <= ly_T ly < 2 ^ 64) by (apply (U _ _ ZT); unfold kThreadObjSize; lia).
assert (UC : 0 <= ly_C ly < 2 ^ 64) by (apply (U _ _ ZC); lia).
assert (ULST : 0 <= lst < 2 ^ 64) by (apply (U _ _ HL1); lia).
assert (UQI : 0 <= qi < 2 ^ 64) by (apply UA, QIB; lia).
assert (UQL : 0 <= ql < 2 ^ 64) by (apply UA, QLB; lia).
assert (RO : FAR.regions_offU UP E0 (ss_mem (AFgv.SS0 own small))).
{ intros rg a Hr Ha. apply OFF.
  unfold AFgv.SS0, AFgv.REG0, AFgv.COMMON, AFgv.R_MAPH, AFgv.R_STK, AFgv.R_MW0, AFgv.R_NS, AFgv.R_J12, AFgv.R_J34, AFgv.R_QI, AFgv.R_CTX,
    AFgv.R_JST, AFgv.R_LASTH, AFgv.R_QL in Hr.
  cbn [ss_mem] in Hr. destruct own; cbn [app] in Hr; reg_split Hr; reg_open Ha;
  rewrite ?E2, ?EqMAP, ?EqQI, ?EqC, ?EqT, ?EqLAST, ?EqQL in Ha; unfold w64 in Ha; rewrite ?unsigned_lit_small in Ha by assumption;
  try fold sp0 in Ha;
  first [ apply LOW; clear - Ha; numconst; lia | apply STK; clear - Ha HSP; numconst; lia | apply MB; clear - Ha HM4; lia
        | apply QIB; clear - Ha; lia | apply QLB; clear - Ha; lia | apply TB; clear - Ha; numconst; lia | apply CB; clear - Ha; lia
        | apply LB; clear - Ha; lia ]. }
constructor; try assumption.
- intros a Ha. apply (ap_real _ _ a); [apply STK; clear - Ha HSP; numconst; lia | exact (PRS a Ha)].
- split; [apply vm_real; [intros b Hb; apply MB; lia | exact MH0]|]. split; [apply vm_real; [intros b Hb; apply MB; lia | exact MH8]|].
  split; [apply vm_real; [intros b Hb; apply MB; lia | exact MH24]|].
  intros a Ha. apply (ap_real _ _ a); [apply MB; lia | exact (MHP a Ha)].
- apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact HQ].
- split; [apply vm_real; [intros b Hb; apply QIB; lia | exact QI0]|].
  intros a Ha. apply (ap_real _ _ a); [apply QIB; lia | exact (QIP a Ha)].
- intros Ho. destruct (HQL Ho) as [QL0 QLP]. split; [apply vm_real; [intros b Hb; apply QLB; lia | exact QL0]|].
  intros a Ha. apply (ap_real _ _ a); [apply QLB; lia | exact (QLP a Ha)].
- intros Ho a Ha. apply (ap_real _ _ a); [apply LB; lia | exact (HLSTH Ho a Ha)].
- apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact HNS].
- refine (conj _ (conj _ (conj _ (conj _ JR)))); (apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | assumption]).
- apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact MUT].
- split; [apply vm_real; [intros b Hb; apply LOW; clear - Hb; numconst; lia | exact TS0]|].
  split; [apply vm_real; [intros b Hb; apply CB; lia | exact TS8]|]. apply vm_real; [intros b Hb; apply CB; lia | exact TS152].
- split; [apply vm_real; [intros b Hb; apply TB; clear - Hb; numconst; lia | exact JS88]|].
  split; [apply vm_real; [intros b Hb; apply TB; clear - Hb; numconst; lia | exact JS96]|].
  destruct JSR as (J5 & J6 & JP). split; [exact J5|]. split; [exact J6|].
  intros a Ha. apply (ap_real _ _ a); [apply TB; clear - Ha; numconst; lia | exact (JP a Ha)].
- intros a Ha. exact (FAR.apresent_of_unpoison _ UP _ a (OFFS a Ha) (SHP a Ha)).
- apply (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO)). exact SEED.
Qed.
End gd.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The return post of the munmap segment (lib/A/AFgv.v at_RET) read on unpoison UP: its frame and its zeroed      *)
(*    shadow move byte by byte; its values lie in the application window WIN. The real frame is kept too.           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem at_RET_unpoison : forall W ly regs0 mem0 map len idx n qi lst vra vs0 vs1 vs2 own md' W' c',
  (forall b, AFgv.WIN ly regs0 qi lst b -> FAR.offU UP b) ->
  AFgv.at_RET W ly regs0 mem0 map len idx n qi lst vra vs0 vs1 vs2 own md' W' c' ->
  exists regs' mem' mat,
    c' = mkCfg (YK11.mkst regs' (w64 vra) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md') mat md') /\
    (forall x : word, ~ AFgv.WIN3 ly regs0 map len qi lst (bv_unsigned x) -> mem' x = mem0 x) /\
    AFgv.at_RET W ly regs0 (FSP.unpoison UP mem0) map len idx n qi lst vra vs0 vs1 vs2 own md' W'
      (mkCfg (YK11.mkst regs' (w64 vra) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md') mat md')).
Proof.
intros W ly regs0 mem0 map len idx n qi lst vra vs0 vs1 vs2 own md' W' c' OW
  (EW & regs' & mem' & mat & Ec & CS & C2 & C8 & C9 & C18 & MQ & SH & PS & PQ & VALS).
cbv zeta in VALS. destruct VALS as (VMU & VNS & VSRT & [v1 V1] & [v2 V2] & [v3 V3] & [v4 V4] & VQI & VOWN).
assert (VU : forall a (w : nat) v, (forall b, a <= b < a + Z.of_nat w -> AFgv.WIN ly regs0 qi lst b) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem')) a w v).
{ intros a w v HW V. apply (FAR.val_mem_to_unpoison _ UP mem' a w v); [intros kk Hk; apply OW, HW; lia | exact V]. }
exists regs', mem', mat. split; [exact Ec|]. split; [exact MQ|].
split; [exact EW|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
split; [exact CS|]. split; [exact C2|]. split; [exact C8|]. split; [exact C9|]. split; [exact C18|].
split. { intros x Hx. apply unpoison_eq. exact (MQ x Hx). }
split. { intros x Hx. apply unpoison_zero. exact (SH x Hx). }
split. { intros a Ha. apply FAR.apresent_to_unpoison. exact (PS a Ha). }
split. { intros a Ha. apply FAR.apresent_to_unpoison. exact (PQ a Ha). }
cbv zeta. unfold AFgv.WIN in VU.
split; [apply VU; [intros b Hb; lia | exact VMU]|].
split; [apply VU; [intros b Hb; lia | exact VNS]|].
split; [apply VU; [intros b Hb; lia | exact VSRT]|].
split; [exists v1; apply VU; [intros b Hb; lia | exact V1]|].
split; [exists v2; apply VU; [intros b Hb; lia | exact V2]|].
split; [exists v3; apply VU; [intros b Hb; lia | exact V3]|].
split; [exists v4; apply VU; [intros b Hb; lia | exact V4]|].
split; [apply VU; [intros b Hb; lia | exact VQI]|].
intros Ho. destruct (VOWN Ho) as [VL PL]. split; [apply VU; [intros b Hb; lia | exact VL]|].
intros a Ha. apply FAR.apresent_to_unpoison. exact (PL a Ha).
Qed.
End x.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. Live blocks: each comes from an allocated chunk, so a state that keeps every allocated chunk keeps it.        *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma ablocks_alloc : forall B ly S p n, In (p, n) (ablocks B ly S) ->
  exists y, In y (st_chunks S) /\ is_alloc y = true /\ sptr_addr B ly (ck_user y) = p /\ ck_req y = n.
Proof.
intros B ly S p n H. unfold ablocks, blocks in H. apply in_map_iff in H as ([q m] & E & H). cbn [fst snd] in E.
injection E as E1 E2. apply in_map_iff in H as (y & E & H). injection E as E3 E4. apply filter_In in H as [Hy Ha].
exists y. subst. auto.
Qed.
Lemma ablocks_keep : forall B ly S S' p n, (forall y, In y (st_chunks S) -> is_alloc y = true -> In y (st_chunks S')) ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly S').
Proof.
intros B ly S S' p n K H. unfold ablocks, blocks in *. apply in_map_iff in H as ([q m] & E & H).
apply in_map_iff in H as (y & E2 & H). apply filter_In in H as [Hy Ha].
apply in_map_iff. exists (q, m). split; [exact E|]. apply in_map_iff. exists y. split; [exact E2|].
apply filter_In. split; [exact (K y Hy Ha) | exact Ha].
Qed.
End rs.

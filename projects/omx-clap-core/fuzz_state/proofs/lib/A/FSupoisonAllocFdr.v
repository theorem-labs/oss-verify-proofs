(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 11 address literal(s) rewritten, module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/AFhg.v, with its module paths changed; 373 of its 588 lines of code are new or changed and 298 lines of the source are left out. *)
(* free's do_recycle walk (lib/A/AFes.v) for any U (lane dr): the AFhd loop records and the AFhg call bridges and facts are reused at FSupoison.unpoison UP mem0 unchanged; the run transitions (AFhg.T_E / T_O / T_R / T_Q), ITEMS, LOOP and the arm are twinned. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: the loop states carry RAWd (the frame on the raw memory from mem0, FK.dr_leafU's last
   conjunct), the recycle_chunk / cache_dealloc calls compose their leaves' raw frames into it, and the arm returns it:
   raw memory frame re-exported for the ARU lift of route 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFi3 AFeq AFew AFeu AFf2 AFh9 AFha AFhc AFhb AFhe AFhi AFhk AFhj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFhf AFhd AFhl AFhg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonAllocR FSupoisonAllocFK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFK.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, AFhd.sp1, AFhd.sp0, AFhd.SY in *; numconst.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Where UP is not, for this walk. Every byte whose value or presence the walk's runs read or write is            *)
(*    application memory: the stack (the frame, the saved registers, the list cells at sp0), the batch slots in the   *)
(*    primary region (AFhf.slot_high), and the allocator's space-base cell in the image (AFhl.sb_cell).              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section t.
Variable B : asyms.
Variable UP : list (Z * Z).
Definition dorecycle_fixed (ly : alayout) (a : Z) : Prop :=
  (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) \/
  (A_ALLOCATOR + 32 <= a < A_ALLOCATOR + 40).
Lemma dorecycle_regions_off_ush : forall ly S W mem md, FSP.ARU tfibsegs B ly S UP W mem md ->
  forall a, dorecycle_fixed ly a -> FAR.offU UP a.
Proof.
intros ly S W mem md H a [Ha|[Ha|Ha]].
- exact (FAR.stack_offU B ly S UP W mem md a H Ha).
- pose proof (lo_high ly (am_layout _ _ _ _ (FSP.ARU_ARm tfibsegs B ly S UP W mem md H))) as [P1 P2].
  apply (FAR.offU_high B ly S UP W mem md a H). ceil. unfold kHighMemBeg, kPrimResvSize in *. lia.
- apply (FAR.offU_low B ly S UP W mem md a H). unfold A_ALLOCATOR, SHADOW_OFF in *. lia.
Qed.
(* A run's memory frame, read on both memories. *)
Lemma meq_unpoison : forall (P : Z -> Prop) (m m' : word -> option byte),
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  forall x : word, ~ P (bv_unsigned x) -> FSP.unpoison UP m' x = FSP.unpoison UP m x.
Proof. intros P m m' MQ x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MQ x Hx)]. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Seed transfer (unpoison UP mem -> mem) of the four walk-spec records (lib/A/AFh9.v, AFha.v, AFhb.v, AFhc.v):  *)
(*    the facts lemmas (AFhl.seed_E / seed_O / seed_Q / seed_R) run at unpoison UP mem; the runs need the record on   *)
(*    the real memory. Only presence, the cells and the seed's regions mention memory.                                *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma fh9_real : forall W ly regs mem sz, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  AFh9.free_hyps W ly regs (FSP.unpoison UP mem) sz -> AFh9.free_hyps W ly regs mem sz.
Proof.
intros W ly regs mem sz OFF FH. destruct FH as [LY IMG Htp Hsp Hal PRS RG RA SZ SEED].
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold DRSTACK in *; lia | exact (PRS a Ha)].
- assert (RO : FAR.regions_offU UP (AFh9.E0 ly regs sz) (YP0l.ss_mem AFh9.SS0)).
  { intros r a Hr Ha. cbn [AFh9.SS0 YP0l.ss_mem AFh9.REG0 In] in Hr. destruct Hr as [<-|[]].
    cbn [AFh9.R_STK YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite (AFh9.E2 ly regs sz) in Ha.
    apply STK. unfold AFh9.YFRAME, DRSTACK in *. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
Lemma fha_real : forall W ly regs mem b nx bb bc h0 sz qb lz, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  AFha.free_hyps W ly regs (FSP.unpoison UP mem) b nx bb bc h0 sz qb lz -> AFha.free_hyps W ly regs mem b nx bb bc h0 sz qb lz.
Proof.
intros W ly regs mem b nx bb bc h0 sz qb lz OFF FH.
pose proof (AFha.LYB W ly regs _ b nx bb bc h0 sz qb lz FH) as (L1 & L2 & _).
destruct FH as [LY IMG Htp Hsp Hal PRS RG HB NX BC BY SZ LZ H0 SEED].
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
assert (BS : forall a, b <= a < b + 32 -> FAR.offU UP a).
{ intros a Ha. apply OFF. right. left. destruct HB as (B1 & B2 & _). unfold kBatchBytes in B2. lia. }
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold AFha.YFRAME, DRSTACK in *; lia | exact (PRS a Ha)].
- destruct HB as (B1 & B2 & B3 & B4). refine (conj B1 (conj B2 (conj B3 _))). intros a Ha.
  exact (FAR.apresent_of_unpoison _ UP mem a (BS a Ha) (B4 a Ha)).
- assert (RO : FAR.regions_offU UP (AFha.E0 ly regs b nx bb bc h0 sz qb lz) (YP0l.ss_mem AFha.SS0)).
  { intros r a Hr Ha. cbn [AFha.SS0 YP0l.ss_mem AFha.REG0 In] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [AFha.R_STK AFha.R_B YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    + rewrite (AFha.E2 ly regs b nx bb bc h0 sz qb lz) in Ha. apply STK. unfold AFha.YFRAME, DRSTACK in *. lia.
    + rewrite (AFha.EqB ly regs b nx bb bc h0 sz qb lz) in Ha. unfold w64 in Ha. destruct HB as (B1 & B2 & _).
      rewrite FSP.wz in Ha by (ceil; unfold kHighMemBeg, kBatchBytes, kPrimResvSize in *; lia). apply BS. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
Lemma fhb_real : forall W ly regs mem sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  AFhb.free_hyps W ly regs (FSP.unpoison UP mem) sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 ->
  AFhb.free_hyps W ly regs mem sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9.
Proof.
intros W ly regs mem sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 OFF FH. destruct FH as [LY IMG Htp Hsp Hal PRS RG RA SZ VALS SEED].
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold AFhb.YFRAME, DRSTACK in *; lia | exact (PRS a Ha)].
- assert (RO : FAR.regions_offU UP (AFhb.E0 regs sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9) (YP0l.ss_mem AFhb.SS0)).
  { intros r a Hr Ha. cbn [AFhb.SS0 YP0l.ss_mem AFhb.REG0 In] in Hr. destruct Hr as [<-|[]].
    cbn [AFhb.R_STK YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    rewrite (AFhb.E2 regs sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9) in Ha.
    apply STK. unfold AFhb.YFRAME, DRSTACK in *. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
Lemma fhc_real : forall W ly regs mem b bc hi i, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  AFhc.free_hyps W ly regs (FSP.unpoison UP mem) b bc hi i -> AFhc.free_hyps W ly regs mem b bc hi i.
Proof.
intros W ly regs mem b bc hi i OFF FH.
pose proof (AFhc.LYB W ly regs _ b bc hi i FH) as (L1 & L2 & L3 & L4 & _).
destruct FH as [LY IMG Htp Hsp Hal PRS RG CB Hsb HB HI SLOT HHI SEED].
assert (RO24 : region_off kBatchClass = 24 * 2 ^ 32) by reflexivity.
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
assert (SLT : forall a, b <= a < b + kBatchBytes -> FAR.offU UP a).
{ intros a Ha. apply OFF. right. left. rewrite RO24 in HB. destruct HB as (B1 & B2 & _). unfold kSpaceSize, kBatchBytes, kFreeArrayOffset in *. lia. }
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold AFhc.YFRAME, DRSTACK in *; lia | exact (PRS a Ha)].
- apply (FAR.val_mem_of_unpoison _ UP); [|exact CB]. intros k Hk. apply STK. unfold AFhc.YFRAME, DRSTACK in *. lia.
- apply (FAR.val_mem_of_unpoison _ UP); [|exact Hsb]. intros k Hk. apply OFF. right. right. lia.
- intros HLT. destruct (SLOT HLT) as (V & P & R1 & R2 & R3). destruct HI as [HI1 HI2].
  assert (SL : forall a, b + 24 + 8 * i <= a < b + 32 + 8 * i -> FAR.offU UP a).
  { intros a Ha. apply SLT. unfold kBatchSlots, kBatchBytes in *. lia. }
  refine (conj _ (conj _ (conj R1 (conj R2 R3)))).
  + apply (FAR.val_mem_of_unpoison _ UP); [|exact V]. intros k Hk. apply SL. lia.
  + intros a Ha. exact (FAR.apresent_of_unpoison _ UP mem a (SL a Ha) (P a Ha)).
- assert (RO : FAR.regions_offU UP (AFhc.E0 ly regs b bc hi i) (YP0l.ss_mem AFhc.SS0)).
  { intros r a Hr Ha. cbn [AFhc.SS0 YP0l.ss_mem AFhc.REG0 In] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [AFhc.R_STK fatom8 YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    + rewrite (AFhc.E2 ly regs b bc hi i) in Ha. apply STK. unfold AFhc.YFRAME, DRSTACK in *. lia.
    + apply OFF. right. right. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
End t.

(* A configuration's memory can be swapped on both sides of an equation. *)
Lemma cfg_at_mem : forall pc pc' regs regs' (m m' m2 : word -> option byte) md md',
  cfg_at tfibsegs pc regs m md = cfg_at tfibsegs pc' regs' m' md' -> cfg_at tfibsegs pc regs m2 md = cfg_at tfibsegs pc' regs' m2 md'.
Proof. intros pc pc' regs regs' m m' m2 md md' E. unfold cfg_at, YK11.mkst in *. injection E; intros; subst; congruence. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The walk (lib/A/AFes.v section e, lib/A/AFhg.v T_E / T_O / T_R / T_Q) for any UP. The loop states are the     *)
(*    donor records (lib/A/AFhd.v, instantiated at mem0 := FSupoison.unpoison UP mem0) of the unpoisoned memory of   *)
(*    the real configuration, plus UP's two invariants.                                                               *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis RCCU : FK.tfib_rchunk_specU B.
Hypothesis CDU : forall ly X c off UP W regs mem md, FK.cd_preU B ly X c off UP W regs mem md -> ly_tsd ly = TFIB_TSD ->
  amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (FK.cd_leafU B ly X UP W regs mem md).
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (UP : list (Z * Z)) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PREU : FK.dr_preU B ly X0 P0 UP W0 regs0 mem0 md0.
Local Notation mu0 := (FSP.unpoison UP mem0).
Local Notation PRE := (proj1 PREU).
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Local Notation hdra := (AFhd.hdra B ly).
Local Notation zlen := (@AFhd.zlen _).
Local Notation SY := (AFhd.SY regs0).
Local Notation ost := (AFhd.ost B ly X0 W0 regs0 mu0 md0).
Local Notation rcst := (AFhd.rcst B ly X0 W0 regs0 mu0 md0).
Local Notation rst := (AFhd.rst B ly X0 W0 regs0 mu0 md0).
Local Notation cdst := (AFhd.cdst B ly X0 W0 regs0 mu0 md0).
Local Notation qst := (AFhd.qst B ly X0 W0 regs0 mu0 md0).
Local Notation FINU := (FK.dr_leafU B ly X0 UP W0 regs0 mem0 md0).
Local Notation entry_facts := (AFhl.entry_facts B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation sp_facts := (AFhl.sp_facts B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation RC_pre := (AFhg.RC_pre B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation RC_post := (AFhg.RC_post B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation CD_pre := (AFhg.CD_pre B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation CD_post := (AFhg.CD_post B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation HTSD := (AFhg.HTSD B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation OFF_at := (dorecycle_regions_off_ush B UP ly).
(* The frame of the walk so far on the raw memory, from mem0 (FK.dr_leafU's last conjunct at the state X). *)
Definition RAWd (X : astate) (mem : word -> option byte) : Prop :=
  forall x : word, ~ aowned B ly X0 (bv_unsigned x) -> ~ aowned B ly X (bv_unsigned x) ->
    ~ ascratch B DRSTACK regs0 (bv_unsigned x) -> ~ (spZ regs0 <= bv_unsigned x < spZ regs0 + 32) -> mem x = mem0 x.
Definition OSTU (X : astate) (rest : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x3408c regs mem md /\ ost X rest lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWd X mem.
Definition RCSTU (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_RChunk regs mem md /\ rcst X b t its i lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWd X mem.
Definition RSTU (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x340d8 regs mem md /\ rst X b t its i lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWd X mem.
Definition CDSTU (X : astate) (b : batch) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_CDealloc regs mem md /\ cdst X b t lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWd X mem.
Definition QSTU (X : astate) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x34110 regs mem md /\ qst X t lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWd X mem.
(* A donor loop state of the configuration whose memory is unpoison UP mem, plus UP's invariants, is the U state of
   the configuration whose memory is mem. *)
Lemma lift : forall (pc pc1 : Z) (R : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) X (W : world tfibsegs) regs mem md,
  (exists lz qb regs1 mem1 md1, cfg_at tfibsegs pc1 regs (FSP.unpoison UP mem) md = cfg_at tfibsegs pc regs1 mem1 md1 /\ R lz qb regs1 mem1 md1) ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWd X mem ->
  exists lz qb regs1 mem1 md1, cfg_at tfibsegs pc1 regs mem md = cfg_at tfibsegs pc regs1 mem1 md1 /\
    R lz qb regs1 (FSP.unpoison UP mem1) md1 /\ FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem1 UP /\ RAWd X mem1.
Proof.
intros pc pc1 R X W regs mem md (lz & qb & regs1 & mem1 & md1 & E & HR) OK PO RW.
pose proof (FK.cfg_at_inj _ _ _ _ _ _ _ _ E) as (E1 & E2 & E3). subst regs1 mem1 md1.
exists lz, qb, regs, mem, md. exact (conj (cfg_at_mem _ _ _ _ _ _ mem _ _ E) (conj HR (conj OK (conj PO RW)))).
Qed.
(* AFhg.T_E for any UP. *)
Lemma T_EU : forall W' c', AFh9.at_OE W0 ly regs0 mem0 md0 (zlen P0) W' c' -> OSTU X0 P0 W' c'.
Proof.
intros W' c' HP. destruct HP as (-> & NZ & regs & mem & mat & -> & R2 & CS & R8 & R9 & R18 & R19 & R21 & R10 & MQr & PRSr & CBr & SVr).
pose proof PREU as (_ & OK0 & PO0).
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof (FAR.ARU_intro B ly X0 UP W0 mem0 md0 HAR OK0 PO0) as HU. pose proof (OFF_at X0 W0 mem0 md0 HU) as OFF.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (RI_RIx U 0 0 0 X0 P0 HRI) as RX.
assert (WST : forall a, AFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold AFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, AFh9.WIN regs0 a \/ ~ AFh9.WIN regs0 a) by (intros a; unfold AFh9.WIN; apply ivl_dec).
assert (WSY : forall a, AFh9.WIN regs0 a -> SY a) by (intros a Ha; unfold AFh9.WIN in Ha; unfold AFhd.SY; clear - Ha; nsp; lia).
(* The run's post on the real memory, read on unpoison UP mem; UP keeps its 0xf7 bytes (off the window). *)
pose proof (meq_unpoison UP (AFh9.WIN regs0) mem0 mem MQr) as MQ.
assert (PRS : forall a, AFh9.WIN regs0 a -> apresent (w_H W0) (FSP.unpoison UP mem) a) by (intros a Ha; apply FAR.apresent_to_unpoison; exact (PRSr a Ha)).
assert (VX : forall a (n : nat) v, val_mem tfibsegs (mrestrict (w_H W0) mem) a n v -> (forall k, (k < n)%nat -> AFh9.WIN regs0 (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict (w_H W0) (FSP.unpoison UP mem)) a n v).
{ intros a n v V Hw. apply (FAR.val_mem_to_unpoison _ UP); [|exact V]. intros k Hk. apply OFF. left. exact (WST _ (Hw k Hk)). }
assert (CB := VX _ _ _ CBr ltac:(intros k Hk; unfold AFh9.WIN, AFh9.YFRAME; clear - Hk; lia)).
assert (SV : AFh9.saved_cells regs0 (mrestrict (w_H W0) (FSP.unpoison UP mem))).
{ intros k r Hk. apply (VX _ _ _ (SVr k r Hk)). intros j Hj.
  assert (K : (k < 11)%nat) by (change 11%nat with (length AFh9.SAVED); apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
  unfold AFh9.WIN, AFh9.YFRAME. clear - Hj K. lia. }
assert (PO' : FSP.upoisoned tfibsegs W0 mem UP)
  by (apply (FK.upoisoned_frame B ly X0 UP W0 mem0 md0 HU mem (AFh9.WIN regs0)); [intros a Ha; pose proof (WST a Ha) as Hs; clear - Hs E7; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact MQr]).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFh9.WIN regs0 a -> aview tfibsegs (w_H W0) (FSP.unpoison UP mem) a = aview tfibsegs (w_H W0) mu0 a).
{ intros a Ha Hn. exact (aview_after_write (w_H W0) mu0 (FSP.unpoison UP mem) _ a MQ Ha Hn). }
unfold plist_cells, qc_cells in CELLS. cbn [qc_list qc_bytes] in CELLS.
apply Forall_cons_iff in CELLS as [C0 CELLS]. apply Forall_cons_iff in CELLS as [C8 CELLS]. apply Forall_cons_iff in CELLS as [C16 CELLS]. apply Forall_cons_iff in CELLS as [C24 CB0].
assert (AGT : forall a, sp0 <= a < sp0 + 32 -> aview tfibsegs (w_H W0) (FSP.unpoison UP mem) a = aview tfibsegs (w_H W0) mu0 a).
{ intros a Ha. apply AG; [clear - Ha U0 S2; nsp; lia|]. unfold AFh9.WIN. clear - Ha. nsp. lia. }
assert (LZR : 0 <= lastaddr ly P0 < ASAN_CEIL).
{ unfold lastaddr. destruct (rev P0) as [|bl initr] eqn:ER; [ceil; unfold ASAN_CEIL; lia|].
assert (Hbl : In bl P0) by (apply in_rev; rewrite ER; left; reflexivity).
pose proof (slot_facts B ly X0 _ (b_self bl) M (rix_slot B X0 [] P0 [] bl RX (or_intror Hbl))) as (B1 & B2 & _).
clear - B1 B2. numconst. lia. }
assert (RW : RAWd X0 mem).
{ intros x _ _ NS _. apply MQr. intros Hw. apply NS. left. clear - Hw. unfold spZ, AFh9.WIN in *. nsp. lia. }
exists (lastaddr ly P0), (sum_bytes P0 mod 2 ^ 64), regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split; [reflexivity|].
refine (conj _ (conj OK0 (conj PO' RW))).
constructor.
-   constructor.
+ exact (AR_after_stack_write B ly X0 W0 mu0 (FSP.unpoison UP mem) md0 mat _ HAR WST WDEC MQ PRS).
+ apply wle_refl.
+ apply same_io_with_vm_backing.
+ intros a O; exact O.
+ intros a Ha _ _ NS _. apply AG; [exact Ha|]. intros Hw. apply NS. left. unfold spZ, AFh9.WIN in *. clear - Hw. nsp. lia.
+ intros a Ha. apply (presence_after_write W0 mu0 (FSP.unpoison UP mem) _ a WDEC MQ PRS); [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia|].
apply HPRES. unfold AFhd.SY, AFhd.sp0 in Ha. exact Ha.
+ exact INIT0.
- exact RX.
- intros ->. apply NZ. reflexivity.
- unfold AFhd.zlen. exact LENP.
- unfold AFhd.common_regs. splits; apply CS; cbn; tauto.
- unfold AFhd.loop_regs. splits; try assumption; rewrite R2; unfold AFhd.sp1; reflexivity.
- exact R10.
- split; [| exact SV]. eapply val_mem_addr; [exact CB | clear; nsp; lia].
- unfold AFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_keep; [|exact (cell_holds_val_mem B ly (w_H W0) mu0 _ 8 _ C0)]. cbn [aeval]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|pose proof (cell_holds_val_mem B ly (w_H W0) mu0 _ 8 _ C8) as V; cbn [aeval aoff] in V; destruct P0 as [|b0 P']; cbn [aeval batch_exp firstaddr] in V |- *; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|pose proof (cell_holds_val_mem B ly (w_H W0) mu0 _ 8 _ C16) as V; cbn [aeval aoff] in V; unfold lastaddr; destruct (rev P0) as [|bl initr]; cbn [aeval batch_exp] in V |- *; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|apply val_mem_mod64; pose proof (cell_holds_val_mem B ly (w_H W0) mu0 _ 8 _ C24) as V; cbn [aeval aoff] in V; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ exact LZR.
+ apply mod64_range.
- apply (batch_cells_xfer B ly P0 (aview tfibsegs (w_H W0) mu0)); [exact (rix_items_ok B X0 [] P0 [] RX) | | exact CB0].
intros b a Hb Hs. pose proof (rix_slot B X0 [] P0 [] b RX (or_intror Hb)) as SZ.
pose proof (slot_high B ly X0 _ (b_self b) M SZ a Hs) as (_ & _ & Ha). apply AG; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia|]. intros Hw.
exact (slot_not_stack B ly X0 _ (b_self b) M SZ a Hs (WST a Hw)).
Qed.
(* AFhg.T_O for any UP. *)
Lemma T_OU : forall X b t lz qb W regs mem md, ost X (b :: t) lz qb W regs (FSP.unpoison UP mem) md ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWd X mem ->
  SRr tfibsegs W (cfg_at tfibsegs 0x3408c regs mem md) (RCSTU X b t (b_items b) 0).
Proof.
intros X b t lz qb W regs mem md ST OK PO RW. pose proof ST as [AC RX NE LEN CR LR A0 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof (FAR.ARU_intro B ly X UP W mem md HAR OK PO) as HU. pose proof (OFF_at X W mem md HU) as OFF.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs LR) as SPV.
pose proof (RIx_open U 0 0 0 X b t RX) as [RXo BL].
destruct (b_items b) as [|k0 ks] eqn:Hk0; [cbn in BL; lia|]. rewrite <- Hk0 in *.
pose proof (fha_real UP W ly regs mem _ _ _ _ _ _ _ _ OFF (seed_O B TB ly X0 P0 W0 regs0 mu0 md0 PRE X b t lz qb W regs (FSP.unpoison UP mem) md k0 ks ST Hk0)) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhi.segYO W ly regs mem md _ _ _ _ _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. destruct HP as (-> & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R20 & R22 & R23 & R24 & R25 & MQr & PRSr & CELLS). cbv zeta in CELLS.
destruct CELLS as (V0 & V8 & V16 & V24). rewrite SPV in *.
set (WINP := AFha.WIN regs) in *.
assert (WE : forall a, WINP a <-> sp0 <= a < sp0 + 32) by (intros a; subst WINP; unfold AFha.WIN; rewrite SPV; clear - S5; nsp; lia).
assert (WST : forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; apply WE in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, WINP a \/ ~ WINP a) by (intros a; subst WINP; unfold AFha.WIN; apply ivl_dec).
(* The run's post on the real memory, read on unpoison UP mem'; UP keeps its 0xf7 bytes (off the window). *)
pose proof (meq_unpoison UP WINP mem mem' MQr) as MQ.
assert (PRS : forall a, WINP a -> apresent (w_H W) (FSP.unpoison UP mem') a) by (intros a Ha; apply FAR.apresent_to_unpoison; exact (PRSr a Ha)).
assert (VX : forall a v, val_mem tfibsegs (mrestrict (w_H W) mem') a 8 v -> sp0 <= a -> a + 8 <= sp0 + 32 ->
  val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem')) a 8 v).
{ intros a v V L1 L2. apply (FAR.val_mem_to_unpoison _ UP); [|exact V]. intros k Hk. apply OFF. left. apply WST, WE. lia. }
assert (V0u := VX _ _ V0 ltac:(clear - S5; nsp; lia) ltac:(clear - S5; nsp; lia)).
assert (V8u := VX _ _ V8 ltac:(clear - S5; nsp; lia) ltac:(clear - S5; nsp; lia)).
assert (V16u := VX _ _ V16 ltac:(clear - S5; nsp; lia) ltac:(clear - S5; nsp; lia)).
assert (V24u := VX _ _ V24 ltac:(clear - S5; nsp; lia) ltac:(clear - S5; nsp; lia)).
assert (PO' : FSP.upoisoned tfibsegs W mem' UP)
  by (apply (FK.upoisoned_frame B ly X UP W mem md HU mem' WINP); [intros a Ha; pose proof (WST a Ha) as Hs; clear - Hs E7; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact MQr]).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ WINP a -> aview tfibsegs (w_H W) (FSP.unpoison UP mem') a = aview tfibsegs (w_H W) (FSP.unpoison UP mem) a).
{ intros a Ha Hn. exact (aview_after_write (w_H W) (FSP.unpoison UP mem) (FSP.unpoison UP mem') _ a MQ Ha Hn). }
pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof CR as (C3 & C4 & C26 & C27).
assert (RW' : RAWd X mem').
{ intros x N0 N1 NS NE'. rewrite (MQr x); [exact (RW x N0 N1 NS NE')|]. intros Hw. apply NE'. apply WE in Hw. exact Hw. }
exists (AFha.LZn (firstaddr ly t) lz), (zcanon (qb - b_bytes b mod 2 ^ 64)), regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
refine (conj _ (conj OK (conj PO' RW'))).
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb).
constructor.
- constructor.
+ exact (AR_after_stack_write B ly X W (FSP.unpoison UP mem) (FSP.unpoison UP mem') md mat WINP HAR WST WDEC MQ PRS).
+ exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC).
+ eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing].
+ exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC).
+ intros a Ha N0 N1 NS NT. rewrite (AG a Ha) by (intros Hw; apply WE in Hw; exact (NT Hw)). exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT).
+ intros a Ha. apply (presence_after_write W (FSP.unpoison UP mem) (FSP.unpoison UP mem') WINP a WDEC MQ PRS); [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia|]. exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha).
+ exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- exact RXo.
- exists []. split; [reflexivity | reflexivity].
- rewrite Hk0. discriminate.
- exact BL.
- rewrite zlen_cons in LEN. clear - LEN. lia.
- unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
- unfold AFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
- unfold AFhd.batch_regs. splits; [exact R20 | exact R22 | exact R24].
- exact R1.
- exact R10.
- intros k ks' Hk. rewrite Hk0 in Hk. injection Hk as <- <-. exact R11.
- rewrite R23. f_equal. lia.
- rewrite R25. f_equal.
- apply (frame_cells_keep ly regs0 W W (FSP.unpoison UP mem) (FSP.unpoison UP mem')); [|exact FR]. intros a Ha. apply AG; [clear - Ha S5 U0 U1; nsp; lia|]. intros Hw. apply WE in Hw. clear - Ha Hw S5. nsp. lia.
- unfold AFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_addr; [exact V0u | rewrite zlen_cons; lia] || (replace (zlen t) with (zlen (b :: t) - 1) by (rewrite zlen_cons; lia); eapply val_mem_addr; [exact V0u | clear - S5; nsp; lia]).
+ eapply val_mem_addr; [exact V8u | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V16u | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V24u | clear - S5; nsp; lia].
+ unfold AFha.LZn. destruct (firstaddr ly t =? 0); [ceil; unfold ASAN_CEIL; lia | exact Rlz].
+ unfold zcanon, M64. apply Z.mod_pos_bound. lia.
- apply (batch_cells_xfer B ly (b :: t) (aview tfibsegs (w_H W) (FSP.unpoison UP mem))); [| | exact CE].
+ constructor; [exact BL | exact (rix_items_ok B X [] (b :: t) [] RX) ] || (unfold items_ok; constructor; [exact BL | exact (rix_items_ok B X _ t _ RXo)]).
+ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (apply (rix_slot B X [] (b :: t) [] b' RX); right; exact Hb).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha). apply AG; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia|]. intros Hw.
exact (slot_not_stack B ly X _ (b_self b') M SZ a Hs (WST a Hw)).
Qed.
(* A call at sp1 (recycle_chunk / cache_dealloc, stack KSTACK) composes its leaf's raw frame into the walk's. *)
Lemma raw_call : forall X X1 regs (mem mem' : word -> option byte),
  (forall a, aowned B ly X a -> aowned B ly X0 a) -> bv_unsigned (getr regs 2) = sp1 -> RAWd X mem ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly X1 (bv_unsigned x) ->
     ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x) ->
  RAWd X1 mem'.
Proof.
intros X X1 regs mem mem' OWN SPV RW RL x N0 N1 NS NE.
assert (NX : ~ aowned B ly X (bv_unsigned x)) by (intros O; exact (N0 (OWN _ O))).
rewrite (RL x NX N1); [exact (RW x N0 NX NS NE) | | intros []].
intros HS. apply NS. pose proof sp_facts as (_ & _ & _ & _ & S5 & _). unfold ascratch, spZ in HS |- *. rewrite SPV in HS.
destruct HS as [HS|HS]; [left | right; exact HS]. clear - HS S5. nsp. lia.
Qed.
(* AFhg.RC_post / CD_post through the U leaves of recycle_chunk / cache_dealloc. *)
Lemma RC_postU : forall X b t k ks i lz qb W regs mem md X1 ns W' c',
  rcst X b t (k :: ks) i lz qb W regs (FSP.unpoison UP mem) md -> FK.rcc_leafU B ly X k UP W regs mem md (tt, X1) W' c' ->
  recycle_post U 0 0 0 X k ns (tt, X1) -> RAWd X mem -> RSTU X1 b t ks (S i) W' c'.
Proof.
intros X b t k ks i lz qb W regs mem md X1 ns W' c' ST HL RP RW.
destruct HL as (regs' & mem' & md' & -> & (POST & OK1 & PO1) & FR & CI & RL).
assert (AC : AFhd.acc B ly X0 W0 regs0 mu0 md0 X W (FSP.unpoison UP mem) md) by (eapply rc_acc; exact ST).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs ltac:(eapply rc_lregs; exact ST)) as SPV.
pose proof (raw_call X X1 regs mem mem' (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) SPV RW RL) as RW1.
exact (lift 0x340d8 (raZ regs) (fun lz qb r m d => rst X1 b t ks (S i) lz qb W' r m d) X1 W' regs' mem' md'
  (RC_post X b t k ks i lz qb W regs (FSP.unpoison UP mem) md X1 ns W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison UP mem') md') ST
     (ex_intro _ regs' (ex_intro _ (FSP.unpoison UP mem') (ex_intro _ md' (conj eq_refl (conj POST (conj FR CI)))))) RP) OK1 PO1 RW1).
Qed.
Lemma CD_postU : forall X b t lz qb W regs mem md X2 ns W' c',
  cdst X b t lz qb W regs (FSP.unpoison UP mem) md -> FK.cd_leafU B ly X UP W regs mem md (tt, X2) W' c' ->
  cache_dealloc_post U 0 0 0 X kBatchClass (b_self b - region_off kBatchClass) ns (tt, X2) -> RAWd X mem -> QSTU X2 t W' c'.
Proof.
intros X b t lz qb W regs mem md X2 ns W' c' ST HL CP RW.
destruct HL as (regs' & mem' & md' & -> & (POST & OK2 & PO2) & FR & CI & RL).
assert (AC : AFhd.acc B ly X0 W0 regs0 mu0 md0 X W (FSP.unpoison UP mem) md) by (eapply cd_acc; exact ST).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs ltac:(eapply cd_lregs; exact ST)) as SPV.
pose proof (raw_call X X2 regs mem mem' (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) SPV RW RL) as RW2.
exact (lift 0x34110 (raZ regs) (fun lz qb r m d => qst X2 t lz qb W' r m d) X2 W' regs' mem' md'
  (CD_post X b t lz qb W regs (FSP.unpoison UP mem) md X2 ns W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison UP mem') md') ST
     (ex_intro _ regs' (ex_intro _ (FSP.unpoison UP mem') (ex_intro _ md' (conj eq_refl (conj POST (conj FR CI)))))) CP) OK2 PO2 RW2).
Qed.
(* AFhg.T_R for any UP. *)
Definition postRIU (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfibsegs) (c' : config) : Prop :=
match its with [] => CDSTU X b t W' c' | _ :: _ => RCSTU X b t its i W' c' end.
Lemma T_RU : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs (FSP.unpoison UP mem) md ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWd X mem ->
  SRr tfibsegs W (cfg_at tfibsegs 0x340d8 regs mem md) (postRIU X b t its i).
Proof.
intros X b t its i lz qb W regs mem md ST OK PO RW. pose proof ST as [AC RX ITS Hi BL LEN CR LR BR S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof (OFF_at X W mem md (FAR.ARU_intro B ly X UP W mem md HAR OK PO)) as OFF.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (fhc_real UP W ly regs mem _ _ _ _ OFF (seed_R B TB ly X0 P0 W0 regs0 mu0 md0 PRE X b t its i lz qb W regs (FSP.unpoison UP mem) md ST)) as FH.
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (rewrite Hits, zlen_app; unfold AFhd.zlen; rewrite Hdone; lia).
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhk.segYR W ly regs mem md _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold AFhc.postR in HP. unfold postRIU.
destruct its as [|k ks].
-
rewrite zlen_nil in LENi. replace (Z.of_nat i <? zlen (b_items b)) with false in HP by (symmetry; apply Z.ltb_ge; lia).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R12 & R13 & MQ).
assert (MM : mem' = mem) by (apply functional_extensionality; intros x; apply MQ; intros []). subst mem'.
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
refine (conj _ (conj OK (conj PO RW))).
constructor.
+ constructor; [apply AR_wvb; exact HAR | exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]
| exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC)].
+ exact RX.
+ exact LEN.
+ unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold AFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ exact R1.
+ exact R10.
+ exact R11.
+ exact R12.
+ exact R13.
+ exact FR.
+ exact TM.
+ exact (batch_cells_tail B ly _ b t CE).
-
rewrite zlen_cons in LENi. replace (Z.of_nat i <? zlen (b_items b)) with true in HP by (symmetry; apply Z.ltb_lt; unfold AFhd.zlen in *; lia).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R23 & R25 & MQ).
assert (MM : mem' = mem) by (apply functional_extensionality; intros x; apply MQ; intros []). subst mem'.
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
refine (conj _ (conj OK (conj PO RW))).
constructor.
+ constructor; [apply AR_wvb; exact HAR | exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]
| exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC)].
+ exact RX.
+ exists done. split; [exact Hits | exact Hdone].
+ discriminate.
+ exact BL.
+ exact LEN.
+ unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold AFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ unfold AFhd.batch_regs. rewrite <- R20, <- R22, <- R24. splits; apply CS; cbn; tauto.
+ exact R1.
+ rewrite R10, SPV. reflexivity.
+ intros k' ks' Hk. injection Hk as <- <-. exact R11.
+ rewrite R23. unfold AFhc.S7v. f_equal. lia.
+ rewrite R25. f_equal. lia.
+ exact FR.
+ exact TM.
+ exact CE.
Qed.
(* AFhg.T_Q for any UP; the last batch returns through dr_leafU (FK.dr_leafU_intro's form, inlined). *)
Definition postQOU (X : astate) (t : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
match t with [] => FINU (tt, X) W' c' | _ :: _ => OSTU X t W' c' end.
Local Notation v1 := (AFhl.v1 regs0).   Local Notation v8 := (AFhl.v8 regs0).   Local Notation v9 := (AFhl.v9 regs0).
Local Notation v18 := (AFhl.v18 regs0). Local Notation v19 := (AFhl.v19 regs0). Local Notation v20 := (AFhl.v20 regs0).
Local Notation v21 := (AFhl.v21 regs0). Local Notation v22 := (AFhl.v22 regs0). Local Notation v23 := (AFhl.v23 regs0).
Local Notation v24 := (AFhl.v24 regs0). Local Notation v25 := (AFhl.v25 regs0).
Lemma T_QU : forall X t lz qb W regs mem md, qst X t lz qb W regs (FSP.unpoison UP mem) md ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWd X mem ->
  SRr tfibsegs W (cfg_at tfibsegs 0x34110 regs mem md) (postQOU X t).
Proof.
intros X t lz qb W regs mem md ST OK PO RW. pose proof ST as [AC RX LEN CR LR FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof (OFF_at X W mem md (FAR.ARU_intro B ly X UP W mem md HAR OK PO)) as OFF.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof (fhb_real UP W ly regs mem _ _ _ _ _ _ _ _ _ _ _ _ OFF (seed_Q B TB ly X0 P0 W0 regs0 mu0 md0 PRE X t lz qb W regs (FSP.unpoison UP mem) md ST)) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhj.segYQ W ly regs mem md (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold AFhb.postQ in HP. unfold postQOU.
destruct t as [|b t'].
-
rewrite zlen_nil, Z.eqb_refl in HP.
destruct HP as (-> & _ & regs' & mat & -> & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & CS).
exists regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, AFhl.v1. reflexivity. }
split.
+ split; [|exact (conj OK PO)].
split; [apply AR_wvb; exact HAR|]. split; [apply layout_le_refl|]. split; [exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)|]. split.
{ unfold AFhl.v8, AFhl.v9, AFhl.v18, AFhl.v19, AFhl.v20, AFhl.v21, AFhl.v22,
AFhl.v23, AFhl.v24, AFhl.v25, w64 in *. rewrite !Z_to_bv_bv_unsigned in *.
apply aregs_intro; try assumption.
- rewrite R2, SPV, S5. unfold AFhb.YFRAME, AFhd.sp0. replace (bv_unsigned (getr regs0 2) - 112 + 112) with (bv_unsigned (getr regs0 2)) by lia. apply Z_to_bv_bv_unsigned.
- rewrite <- C3; apply CS; cbn; tauto.
- rewrite <- C4; apply CS; cbn; tauto.
- rewrite <- C26; apply CS; cbn; tauto.
- rewrite <- C27; apply CS; cbn; tauto. }
split; [eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]|]. split.
{ intros a Ha N0 N1 NS NT. exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT). }
intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold AFhd.SY. unfold spZ in Ha. clear - Ha. nsp. lia.
+ split; [intros a Ha; apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC); unfold AFhd.SY; unfold spZ in Ha; clear - Ha; nsp; lia | exact RW].
-
replace (zlen (b :: t') =? 0) with false in HP by (symmetry; apply Z.eqb_neq; rewrite zlen_cons; unfold AFhd.zlen; lia).
destruct HP as (-> & _ & regs' & mat & -> & R2 & CS & R10).
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
refine (conj _ (conj OK (conj PO RW))).
constructor.
+ constructor; [apply AR_wvb; exact HAR | exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]
| exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC)].
+ exact RX.
+ discriminate.
+ exact LEN.
+ unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold AFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ exact R10.
+ exact FR.
+ exact TM.
+ exact CE.
Qed.
(* lib/A/AFes.v ITEMS / LOOP / tfib_dorecycle_arm for any UP. *)
Lemma ITEMSU : forall b t its i fuel X W c, RCSTU X b t its i W c -> (length its <= fuel)%nat ->
amreal tfibsegs (recycle_items fuel its X) W c (fun r W' c' => CDSTU (snd r) b t W' c').
Proof.
intros b t its. induction its as [|k ks IH]; intros i fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST & _). exfalso. eapply rc_ne; [exact ST | reflexivity].
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [recycle_items].
apply (amreal_mbind tfibsegs (recycle_chunk k) (fun _ => recycle_items f ks) X W c (fun r W' c' => RSTU (snd r) b t ks (S i) W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST & OK & PO & RW).
pose proof (RIx_head U 0 0 0 X k ks t [b_self b] ltac:(eapply rc_rix; exact ST)) as (WP & Hk & Hst & Hni).
apply (amreal_atok _ _ _ _ _ _ (recycle_chunk_ok U 0 0 0 X k true WP Hk Hst Hni)).
eapply amreal_mono; [| exact (RCCU ly X k (sp1 + 8) UP W regs mem md (conj (RC_pre X b t k ks i lz qb W regs (FSP.unpoison UP mem) md ST) (conj OK PO)))].
intros [[] X1] W' c' HL [ns' RP]. cbn [snd]. exact (RC_postU X b t k ks i lz qb W regs mem md X1 ns' W' c' ST HL RP RW).
+ intros [] X1 W1 c1 ST1. destruct ST1 as (lz & qb & regs & mem & md & -> & ST1 & OK1 & PO1 & RW1).
eapply amreal_SRr_pre; [exact (T_RU X1 b t ks (S i) lz qb W1 regs mem md ST1 OK1 PO1 RW1)|].
intros W2 c2 _ HP. unfold postRIU in HP. destruct ks as [|k' ks'].
* destruct f; cbn [recycle_items]; apply amreal_ret; cbn [snd]; exact HP.
* apply (IH (S i) f X1 W2 c2 HP). cbn in Hfuel |- *. lia.
Qed.
Lemma LOOPU : forall rest fuel X W c, OSTU X rest W c -> (length rest <= fuel)%nat ->
amreal tfibsegs (do_recycle fuel rest X) W c FINU.
Proof.
induction rest as [|b t IH]; intros fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST & _). exfalso. eapply o_ne; [exact ST | reflexivity].
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [do_recycle].
apply (amreal_mbind tfibsegs (recycle_items 1100 (b_items b)) (fun _ => YG00.bind (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t)) X W c
(fun r W' c' => CDSTU (snd r) b t W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST & OK & PO & RW).
eapply amreal_SRr_pre; [exact (T_OU X b t lz qb W regs mem md ST OK PO RW)|].
intros W1 c1 _ H1. apply (ITEMSU b t (b_items b) 0 1100 X W1 c1 H1).
destruct H1 as (lz1 & qb1 & regs1 & mem1 & md1 & _ & ST1 & _). assert (BL : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) by (eapply rc_blen; exact ST1). unfold kBatchSlots in BL. cbn in BL. lia.
+ intros [] X1 W1 c1 ST1.
apply (amreal_mbind tfibsegs (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t) X1 W1 c1 (fun r W' c' => QSTU (snd r) t W' c')).
* destruct ST1 as (lz & qb & regs & mem & md & -> & ST1 & OK1 & PO1 & RW1).
pose proof (RIx_cd_pre U 0 0 0 X1 t (b_self b) [] ltac:(eapply cd_rix; exact ST1)) as (WP & Z1 & Z2 & Z3 & RM).
apply (amreal_atok _ _ _ _ _ _ (cache_dealloc_ok U 0 0 0 X1 kBatchClass (b_self b) true WP ltac:(unfold kBatchClass; lia) Z1 Z2 Z3 RM)).
eapply amreal_mono; [| exact (CDU ly X1 kBatchClass (b_self b) UP W1 regs mem md (conj (CD_pre X1 b t lz qb W1 regs (FSP.unpoison UP mem) md ST1) (conj OK1 PO1)) HTSD)].
intros [[] X2] W' c' HL [ns' CP]. cbn [snd]. exact (CD_postU X1 b t lz qb W1 regs mem md X2 ns' W' c' ST1 HL CP RW1).
* intros [] X2 W2 c2 ST2. destruct ST2 as (lz & qb & regs & mem & md & -> & ST2 & OK2 & PO2 & RW2).
eapply amreal_SRr_pre; [exact (T_QU X2 t lz qb W2 regs mem md ST2 OK2 PO2 RW2)|].
intros W3 c3 _ HP. unfold postQOU in HP. destruct t as [|b' t'].
-- destruct f; cbn [do_recycle]; apply amreal_ret; exact HP.
-- apply (IH f X2 W3 c3 HP). cbn in Hfuel |- *. lia.
Qed.
Lemma tfib_dorecycle_armU : amreal tfibsegs (do_recycle 100000%nat P0 X0) W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) FINU.
Proof.
pose proof PREU as (_ & OK0 & PO0).
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof (FAR.ARU_intro B ly X0 UP W0 mem0 md0 HAR OK0 PO0) as HU.
pose proof (fh9_real UP W0 ly regs0 mem0 (zlen P0) (OFF_at X0 W0 mem0 md0 HU) (seed_E B TB ly X0 P0 W0 regs0 mu0 md0 PRE)) as FH.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
assert (WALK : SRr tfibsegs W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) (AFh9.postE W0 ly regs0 mem0 md0 (zlen P0))).
{ unfold cfg_at. rewrite <- (wvb_self md0) at 1. exact (AFhe.segYE W0 ly regs0 mem0 md0 (zlen P0) (m_vm_materialized md0) FH). }
unfold AFh9.postE in WALK.
assert (CASES : P0 = [] \/ exists b t, P0 = b :: t) by (clear; destruct P0 as [|b t]; [left; reflexivity | right; exists b, t; reflexivity]).
destruct CASES as [EP|(b & t & EP)].
-
rewrite EP. rewrite EP, zlen_nil, Z.eqb_refl in WALK. cbn [do_recycle amreal ret].
eapply SRr_mono; [exact WALK|]. intros W' c' _ HP.
destruct HP as (-> & _ & regs & mem & mat & -> & R2 & CS & MQr & PRSr).
assert (WST : forall a, AFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold AFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, AFh9.WIN regs0 a \/ ~ AFh9.WIN regs0 a) by (intros a; unfold AFh9.WIN; apply ivl_dec).
(* The run's post on the real memory, read on unpoison UP mem; UP keeps its 0xf7 bytes (off the window). *)
pose proof (meq_unpoison UP (AFh9.WIN regs0) mem0 mem MQr) as MQ.
assert (PRS : forall a, AFh9.WIN regs0 a -> apresent (w_H W0) (FSP.unpoison UP mem) a) by (intros a Ha; apply FAR.apresent_to_unpoison; exact (PRSr a Ha)).
assert (PO' : FSP.upoisoned tfibsegs W0 mem UP)
  by (apply (FK.upoisoned_frame B ly X0 UP W0 mem0 md0 HU mem (AFh9.WIN regs0)); [intros a Ha; pose proof (WST a Ha) as Hs; clear - Hs E7; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact MQr]).
exists regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split.
{ unfold cfg_at, raZ. rewrite Z_to_bv_bv_unsigned || (unfold w64; rewrite Z_to_bv_bv_unsigned). reflexivity. }
split.
+ split; [|exact (conj OK0 PO')].
split; [exact (AR_after_stack_write B ly X0 W0 mu0 (FSP.unpoison UP mem) md0 mat _ HAR WST WDEC MQ PRS)|].
split; [apply layout_le_refl|]. split; [apply wle_refl|]. split.
{ apply aregs_intro; first [exact R2 | apply CS; cbn; tauto]. }
split; [apply same_io_with_vm_backing|]. split.
{ intros a Ha _ _ NS _. apply (aview_after_write (w_H W0) mu0 (FSP.unpoison UP mem) _ a MQ Ha).
intros Hw. apply NS. left. unfold AFh9.WIN in Hw. clear - Hw. nsp. lia. }
intros a Ha. apply (presence_after_write W0 mu0 (FSP.unpoison UP mem) _ a WDEC MQ PRS); [clear - Ha S1 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
+ split.
++ intros a Ha. apply (presence_after_write W0 mu0 (FSP.unpoison UP mem) _ a WDEC MQ PRS); [clear - Ha S1 S2 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
++ intros x _ _ NS _. apply MQr. intros Hw. apply NS. left. clear - Hw. unfold AFh9.WIN in Hw. nsp. lia.
-
replace (zlen P0 =? 0) with false in WALK by (symmetry; apply Z.eqb_neq; rewrite EP, zlen_cons; unfold AFhd.zlen; lia).
eapply amreal_SRr_pre; [exact WALK|]. intros W' c' _ HP.
apply (LOOPU P0 100000%nat X0 W' c' (T_EU W' c' HP)).
apply Nat2Z.inj_le. rewrite of_nat_100000. clear - LENP. lia.
Qed.
End e.
(* lib/A/AFes.v tfib_dorecycle_ok for any U; the cache_dealloc premise has the shape of lane cd's tfib_cdealloc_okU. *)
Theorem tfib_dorecycle_okU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FK.tfib_rchunk_specU B ->
  (forall ly X c off UP W regs mem md, FK.cd_preU B ly X c off UP W regs mem md -> ly_tsd ly = TFIB_TSD ->
     amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (FK.cd_leafU B ly X UP W regs mem md)) ->
  FK.tfib_dorecycle_specU B.
Proof. intros B _ TB RCCU CDU ly X P UP W regs mem md PREU. exact (tfib_dorecycle_armU B TB RCCU CDU ly X P UP W regs mem md PREU). Qed.
End d.

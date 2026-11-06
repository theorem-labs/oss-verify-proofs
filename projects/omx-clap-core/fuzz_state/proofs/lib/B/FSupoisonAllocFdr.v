(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Reusable/YFhg.v, with its module paths changed; 377 of its 592 lines of code are new or changed and 295 lines of the source are left out. *)
(* free's do_recycle walk (lib/A/AFes.v) for any U (lane dr): the AFhd loop records and the AFhg call bridges and facts are reused at FSupoison.unpoison UP mem0 unchanged; the run transitions (AFhg.T_E / T_O / T_R / T_Q), ITEMS, LOOP and the arm are twinned. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFdr.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt; the pcs are by name: PC_DR_O, PC_DR_Q, PC_DR_R. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFi3 YFeq YFew YFeu YFf2 YFh9 YFha YFhc YFhb YFhe YFhi YFhk YFhj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFhf YFhd YFhl YFhg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocFK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* The pcs inside a function, by name: the entry is lib/B/YFeu.v / lib/B/YFew.v A_xxx or the lib/B/YB1w.v row, the offset is the B donor's pc minus that entry. *)
(* the DoRecycle outer loop head (lib/B/YFha.v:85, SS0's pc). *)
Definition PC_DR_O : Z := A_DoRecycle + 0x78.
(* the DoRecycle batch-release point (lib/B/YFhb.v:80, SS0's pc). *)
Definition PC_DR_Q : Z := A_DoRecycle + 0xfc.
(* the DoRecycle item loop head (lib/B/YFhc.v:79, SS0's pc). *)
Definition PC_DR_R : Z := A_DoRecycle + 0xc4.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFK.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, YFh9.YFRAME, YFha.YFRAME, YFhc.YFRAME, YFhb.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, YFhd.sp1, YFhd.sp0, YFhd.SY in *; numconst.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Where UP is not, for this walk. Every byte whose value or presence the walk's runs read or write is            *)
(*    application memory: the stack (the frame, the saved registers, the list cells at sp0), the batch slots in the   *)
(*    primary region (YFhf.slot_high), and the allocator's space-base cell in the image (YFhl.sb_cell).              *)
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
(* 2. Seed transfer (unpoison UP mem -> mem) of the four walk-spec records (lib/B/YFh9.v, YFha.v, YFhb.v, YFhc.v):  *)
(*    the facts lemmas (YFhl.seed_E / seed_O / seed_Q / seed_R) run at unpoison UP mem; the runs need the record on   *)
(*    the real memory. Only presence, the cells and the seed's regions mention memory.                                *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma fh9_real : forall W ly regs mem sz, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  YFh9.free_hyps W ly regs (FSP.unpoison UP mem) sz -> YFh9.free_hyps W ly regs mem sz.
Proof.
intros W ly regs mem sz OFF FH. destruct FH as [LY IMG Htp Hsp Hal PRS RG RA SZ SEED].
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold DRSTACK in *; lia | exact (PRS a Ha)].
- assert (RO : FAR.regions_offU UP (YFh9.E0 ly regs sz) (YP0l.ss_mem YFh9.SS0)).
  { intros r a Hr Ha. cbn [YFh9.SS0 YP0l.ss_mem YFh9.REG0 In] in Hr. destruct Hr as [<-|[]].
    cbn [YFh9.R_STK YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite (YFh9.E2 ly regs sz) in Ha.
    apply STK. unfold YFh9.YFRAME, DRSTACK in *. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
Lemma fha_real : forall W ly regs mem b nx bb bc h0 sz qb lz, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  YFha.free_hyps W ly regs (FSP.unpoison UP mem) b nx bb bc h0 sz qb lz -> YFha.free_hyps W ly regs mem b nx bb bc h0 sz qb lz.
Proof.
intros W ly regs mem b nx bb bc h0 sz qb lz OFF FH.
pose proof (YFha.LYB W ly regs _ b nx bb bc h0 sz qb lz FH) as (L1 & L2 & _).
destruct FH as [LY IMG Htp Hsp Hal PRS RG HB NX BC BY SZ LZ H0 SEED].
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
assert (BS : forall a, b <= a < b + 32 -> FAR.offU UP a).
{ intros a Ha. apply OFF. right. left. destruct HB as (B1 & B2 & _). unfold kBatchBytes in B2. lia. }
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold YFha.YFRAME, DRSTACK in *; lia | exact (PRS a Ha)].
- destruct HB as (B1 & B2 & B3 & B4). refine (conj B1 (conj B2 (conj B3 _))). intros a Ha.
  exact (FAR.apresent_of_unpoison _ UP mem a (BS a Ha) (B4 a Ha)).
- assert (RO : FAR.regions_offU UP (YFha.E0 ly regs b nx bb bc h0 sz qb lz) (YP0l.ss_mem YFha.SS0)).
  { intros r a Hr Ha. cbn [YFha.SS0 YP0l.ss_mem YFha.REG0 In] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [YFha.R_STK YFha.R_B YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    + rewrite (YFha.E2 ly regs b nx bb bc h0 sz qb lz) in Ha. apply STK. unfold YFha.YFRAME, DRSTACK in *. lia.
    + rewrite (YFha.EqB ly regs b nx bb bc h0 sz qb lz) in Ha. unfold w64 in Ha. destruct HB as (B1 & B2 & _).
      rewrite FSP.wz in Ha by (ceil; unfold kHighMemBeg, kBatchBytes, kPrimResvSize in *; lia). apply BS. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
Lemma fhb_real : forall W ly regs mem sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  YFhb.free_hyps W ly regs (FSP.unpoison UP mem) sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 ->
  YFhb.free_hyps W ly regs mem sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9.
Proof.
intros W ly regs mem sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 OFF FH. destruct FH as [LY IMG Htp Hsp Hal PRS RG RA SZ VALS SEED].
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold YFhb.YFRAME, DRSTACK in *; lia | exact (PRS a Ha)].
- assert (RO : FAR.regions_offU UP (YFhb.E0 regs sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9) (YP0l.ss_mem YFhb.SS0)).
  { intros r a Hr Ha. cbn [YFhb.SS0 YP0l.ss_mem YFhb.REG0 In] in Hr. destruct Hr as [<-|[]].
    cbn [YFhb.R_STK YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    rewrite (YFhb.E2 regs sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9) in Ha.
    apply STK. unfold YFhb.YFRAME, DRSTACK in *. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
Lemma fhc_real : forall W ly regs mem b bc hi i, (forall a, dorecycle_fixed ly a -> FAR.offU UP a) ->
  YFhc.free_hyps W ly regs (FSP.unpoison UP mem) b bc hi i -> YFhc.free_hyps W ly regs mem b bc hi i.
Proof.
intros W ly regs mem b bc hi i OFF FH.
pose proof (YFhc.LYB W ly regs _ b bc hi i FH) as (L1 & L2 & L3 & L4 & _).
destruct FH as [LY IMG Htp Hsp Hal PRS RG CB Hsb HB HI SLOT HHI SEED].
assert (RO24 : region_off kBatchClass = 24 * 2 ^ 32) by reflexivity.
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; left; exact Ha).
assert (SLT : forall a, b <= a < b + kBatchBytes -> FAR.offU UP a).
{ intros a Ha. apply OFF. right. left. rewrite RO24 in HB. destruct HB as (B1 & B2 & _). unfold kSpaceSize, kBatchBytes, kFreeArrayOffset in *. lia. }
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply STK; unfold YFhc.YFRAME, DRSTACK in *; lia | exact (PRS a Ha)].
- apply (FAR.val_mem_of_unpoison _ UP); [|exact CB]. intros k Hk. apply STK. unfold YFhc.YFRAME, DRSTACK in *. lia.
- apply (FAR.val_mem_of_unpoison _ UP); [|exact Hsb]. intros k Hk. apply OFF. right. right. lia.
- intros HLT. destruct (SLOT HLT) as (V & P & R1 & R2 & R3). destruct HI as [HI1 HI2].
  assert (SL : forall a, b + 24 + 8 * i <= a < b + 32 + 8 * i -> FAR.offU UP a).
  { intros a Ha. apply SLT. unfold kBatchSlots, kBatchBytes in *. lia. }
  refine (conj _ (conj _ (conj R1 (conj R2 R3)))).
  + apply (FAR.val_mem_of_unpoison _ UP); [|exact V]. intros k Hk. apply SL. lia.
  + intros a Ha. exact (FAR.apresent_of_unpoison _ UP mem a (SL a Ha) (P a Ha)).
- assert (RO : FAR.regions_offU UP (YFhc.E0 ly regs b bc hi i) (YP0l.ss_mem YFhc.SS0)).
  { intros r a Hr Ha. cbn [YFhc.SS0 YP0l.ss_mem YFhc.REG0 In] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [YFhc.R_STK fatom8 YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    + rewrite (YFhc.E2 ly regs b bc hi i) in Ha. apply STK. unfold YFhc.YFRAME, DRSTACK in *. lia.
    + apply OFF. right. right. lia. }
  exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ _ _ RO) SEED).
Qed.
End t.

(* A configuration's memory can be swapped on both sides of an equation. *)
Lemma cfg_at_mem : forall pc pc' regs regs' (m m' m2 : word -> option byte) md md',
  cfg_at tfibsegs pc regs m md = cfg_at tfibsegs pc' regs' m' md' -> cfg_at tfibsegs pc regs m2 md = cfg_at tfibsegs pc' regs' m2 md'.
Proof. intros pc pc' regs regs' m m' m2 md md' E. unfold cfg_at, YK11.mkst in *. injection E; intros; subst; congruence. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The walk (lib/B/YFes.v section e, lib/B/YFhg.v T_E / T_O / T_R / T_Q) for any UP. The loop states are the     *)
(*    donor records (lib/B/YFhd.v, instantiated at mem0 := FSupoison.unpoison UP mem0) of the unpoisoned memory of   *)
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
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Local Notation hdra := (YFhd.hdra B ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation SY := (YFhd.SY regs0).
Local Notation ost := (YFhd.ost B ly X0 W0 regs0 mu0 md0).
Local Notation rcst := (YFhd.rcst B ly X0 W0 regs0 mu0 md0).
Local Notation rst := (YFhd.rst B ly X0 W0 regs0 mu0 md0).
Local Notation cdst := (YFhd.cdst B ly X0 W0 regs0 mu0 md0).
Local Notation qst := (YFhd.qst B ly X0 W0 regs0 mu0 md0).
Local Notation FINU := (FK.dr_leafU B ly X0 UP W0 regs0 mem0 md0).
Local Notation entry_facts := (YFhl.entry_facts B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation sp_facts := (YFhl.sp_facts B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation RC_pre := (YFhg.RC_pre B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation RC_post := (YFhg.RC_post B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation CD_pre := (YFhg.CD_pre B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation CD_post := (YFhg.CD_post B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation HTSD := (YFhg.HTSD B TB ly X0 P0 W0 regs0 mu0 md0 PRE).
Local Notation OFF_at := (dorecycle_regions_off_ush B UP ly).
(* The raw frame so far (dr_leafU's last conjunct, on the raw memories): every byte off X0's and X's owned bytes, off
   do_recycle's scratch and off its 32-byte out-parameter window keeps its value of mem0. Each state's owned bytes are
   owned by X0 (acc_own), so the callees' raw frames compose. *)
Definition RAWF (X : astate) (mem : word -> option byte) : Prop :=
forall x : word, ~ aowned B ly X0 (bv_unsigned x) -> ~ aowned B ly X (bv_unsigned x) ->
  ~ ascratch B DRSTACK regs0 (bv_unsigned x) -> ~ (spZ regs0 <= bv_unsigned x < spZ regs0 + 32) -> mem x = mem0 x.
(* A callee's raw frame (recycle_chunk's or cache_dealloc's, at the loop's sp1) after RAWF. *)
Lemma rawf_step : forall X X1 (regs : bvmap 5 word) (mem mem' : word -> option byte),
  (forall a, aowned B ly X a -> aowned B ly X0 a) -> bv_unsigned (getr regs 2) = sp1 -> RAWF X mem ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly X1 (bv_unsigned x) ->
     ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x) ->
  RAWF X1 mem'.
Proof.
intros X X1 regs mem mem' OWN SPV RW RC x N0 N1 NS NT.
assert (NX : ~ aowned B ly X (bv_unsigned x)) by (intros O; exact (N0 (OWN _ O))).
rewrite (RC x NX N1); [exact (RW x N0 NX NS NT) | | intros F; exact F].
pose proof sp_facts as (_ & _ & _ & _ & S5 & _).
intros C. unfold ascratch in C. destruct C as [C|C]; apply NS; [left | right; exact C]. unfold spZ in C. rewrite SPV in C. clear - C S5. nsp. lia.
Qed.
Definition OSTU (X : astate) (rest : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs PC_DR_O regs mem md /\ ost X rest lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWF X mem.
Definition RCSTU (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_RChunk regs mem md /\ rcst X b t its i lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWF X mem.
Definition RSTU (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs PC_DR_R regs mem md /\ rst X b t its i lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWF X mem.
Definition CDSTU (X : astate) (b : batch) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_CDealloc regs mem md /\ cdst X b t lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWF X mem.
Definition QSTU (X : astate) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs PC_DR_Q regs mem md /\ qst X t lz qb W regs (FSP.unpoison UP mem) md /\
FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem UP /\ RAWF X mem.
(* A donor loop state of the configuration whose memory is unpoison UP mem, plus UP's invariants and the raw frame,
   is the U state of the configuration whose memory is mem. *)
Lemma lift : forall (pc pc1 : Z) (R : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) X (W : world tfibsegs) regs mem md,
  (exists lz qb regs1 mem1 md1, cfg_at tfibsegs pc1 regs (FSP.unpoison UP mem) md = cfg_at tfibsegs pc regs1 mem1 md1 /\ R lz qb regs1 mem1 md1) ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWF X mem ->
  exists lz qb regs1 mem1 md1, cfg_at tfibsegs pc1 regs mem md = cfg_at tfibsegs pc regs1 mem1 md1 /\
    R lz qb regs1 (FSP.unpoison UP mem1) md1 /\ FSP.upoison_ok B ly X UP /\ FSP.upoisoned tfibsegs W mem1 UP /\ RAWF X mem1.
Proof.
intros pc pc1 R X W regs mem md (lz & qb & regs1 & mem1 & md1 & E & HR) OK PO RW.
pose proof (FK.cfg_at_inj _ _ _ _ _ _ _ _ E) as (E1 & E2 & E3). subst regs1 mem1 md1.
exists lz, qb, regs, mem, md. exact (conj (cfg_at_mem _ _ _ _ _ _ mem _ _ E) (conj HR (conj OK (conj PO RW)))).
Qed.
(* YFhg.T_E for any UP. *)
Lemma T_EU : forall W' c', YFh9.at_OE W0 ly regs0 mem0 md0 (zlen P0) W' c' -> OSTU X0 P0 W' c'.
Proof.
intros W' c' HP. destruct HP as (-> & NZ & regs & mem & mat & -> & R2 & CS & R8 & R9 & R18 & R19 & R21 & R10 & MQr & PRSr & CBr & SVr).
pose proof PREU as (_ & OK0 & PO0).
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof (FAR.ARU_intro B ly X0 UP W0 mem0 md0 HAR OK0 PO0) as HU. pose proof (OFF_at X0 W0 mem0 md0 HU) as OFF.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (RI_RIx U 0 0 0 X0 P0 HRI) as RX.
assert (WST : forall a, YFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold YFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, YFh9.WIN regs0 a \/ ~ YFh9.WIN regs0 a) by (intros a; unfold YFh9.WIN; apply ivl_dec).
assert (WSY : forall a, YFh9.WIN regs0 a -> SY a) by (intros a Ha; unfold YFh9.WIN in Ha; unfold YFhd.SY; clear - Ha; nsp; lia).
(* The run's post on the real memory, read on unpoison UP mem; UP keeps its 0xf7 bytes (off the window). *)
pose proof (meq_unpoison UP (YFh9.WIN regs0) mem0 mem MQr) as MQ.
assert (PRS : forall a, YFh9.WIN regs0 a -> apresent (w_H W0) (FSP.unpoison UP mem) a) by (intros a Ha; apply FAR.apresent_to_unpoison; exact (PRSr a Ha)).
assert (VX : forall a (n : nat) v, val_mem tfibsegs (mrestrict (w_H W0) mem) a n v -> (forall k, (k < n)%nat -> YFh9.WIN regs0 (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict (w_H W0) (FSP.unpoison UP mem)) a n v).
{ intros a n v V Hw. apply (FAR.val_mem_to_unpoison _ UP); [|exact V]. intros k Hk. apply OFF. left. exact (WST _ (Hw k Hk)). }
assert (CB := VX _ _ _ CBr ltac:(intros k Hk; unfold YFh9.WIN, YFh9.YFRAME; clear - Hk; lia)).
assert (SV : YFh9.saved_cells regs0 (mrestrict (w_H W0) (FSP.unpoison UP mem))).
{ intros k r Hk. apply (VX _ _ _ (SVr k r Hk)). intros j Hj.
  assert (K : (k < 11)%nat) by (change 11%nat with (length YFh9.SAVED); apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
  unfold YFh9.WIN, YFh9.YFRAME. clear - Hj K. lia. }
assert (PO' : FSP.upoisoned tfibsegs W0 mem UP)
  by (apply (FK.upoisoned_frame B ly X0 UP W0 mem0 md0 HU mem (YFh9.WIN regs0)); [intros a Ha; pose proof (WST a Ha) as Hs; clear - Hs E7; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact MQr]).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YFh9.WIN regs0 a -> aview tfibsegs (w_H W0) (FSP.unpoison UP mem) a = aview tfibsegs (w_H W0) mu0 a).
{ intros a Ha Hn. exact (aview_after_write (w_H W0) mu0 (FSP.unpoison UP mem) _ a MQ Ha Hn). }
unfold plist_cells, qc_cells in CELLS. cbn [qc_list qc_bytes] in CELLS.
apply Forall_cons_iff in CELLS as [C0 CELLS]. apply Forall_cons_iff in CELLS as [C8 CELLS]. apply Forall_cons_iff in CELLS as [C16 CELLS]. apply Forall_cons_iff in CELLS as [C24 CB0].
assert (AGT : forall a, sp0 <= a < sp0 + 32 -> aview tfibsegs (w_H W0) (FSP.unpoison UP mem) a = aview tfibsegs (w_H W0) mu0 a).
{ intros a Ha. apply AG; [clear - Ha U0 S2; nsp; lia|]. unfold YFh9.WIN. clear - Ha. nsp. lia. }
assert (LZR : 0 <= lastaddr ly P0 < ASAN_CEIL).
{ unfold lastaddr. destruct (rev P0) as [|bl initr] eqn:ER; [ceil; unfold ASAN_CEIL; lia|].
assert (Hbl : In bl P0) by (apply in_rev; rewrite ER; left; reflexivity).
pose proof (slot_facts B ly X0 _ (b_self bl) M (rix_slot B X0 [] P0 [] bl RX (or_intror Hbl))) as (B1 & B2 & _).
clear - B1 B2. numconst. lia. }
(* The raw frame: the run writes only its frame (YFh9.WIN), in do_recycle's scratch. *)
assert (RW0 : RAWF X0 mem).
{ intros x _ _ NS _. apply MQr. intros Hw. apply NS. left. unfold spZ, YFh9.WIN in *. clear - Hw. nsp. lia. }
exists (lastaddr ly P0), (sum_bytes P0 mod 2 ^ 64), regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split; [reflexivity|].
refine (conj _ (conj OK0 (conj PO' RW0))).
constructor.
-   constructor.
+ exact (AR_after_stack_write B ly X0 W0 mu0 (FSP.unpoison UP mem) md0 mat _ HAR WST WDEC MQ PRS).
+ apply wle_refl.
+ apply same_io_with_vm_backing.
+ intros a O; exact O.
+ intros a Ha _ _ NS _. apply AG; [exact Ha|]. intros Hw. apply NS. left. unfold spZ, YFh9.WIN in *. clear - Hw. nsp. lia.
+ intros a Ha. apply (presence_after_write W0 mu0 (FSP.unpoison UP mem) _ a WDEC MQ PRS); [unfold YFhd.SY in Ha; clear - Ha S1 S2; nsp; lia|].
apply HPRES. unfold YFhd.SY, YFhd.sp0 in Ha. exact Ha.
+ exact INIT0.
- exact RX.
- intros ->. apply NZ. reflexivity.
- unfold YFhd.zlen. exact LENP.
- unfold YFhd.common_regs. splits; apply CS; cbn; tauto.
- unfold YFhd.loop_regs. splits; try assumption; rewrite R2; unfold YFhd.sp1; reflexivity.
- exact R10.
- split; [| exact SV]. eapply val_mem_addr; [exact CB | clear; nsp; lia].
- unfold YFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
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
(* YFhg.T_O for any UP. *)
Lemma T_OU : forall X b t lz qb W regs mem md, ost X (b :: t) lz qb W regs (FSP.unpoison UP mem) md ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWF X mem ->
  SRr tfibsegs W (cfg_at tfibsegs PC_DR_O regs mem md) (RCSTU X b t (b_items b) 0).
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
eapply SRr_mono; [exact (YFhi.segYO W ly regs mem md _ _ _ _ _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. destruct HP as (-> & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R20 & R22 & R23 & R24 & R25 & MQr & PRSr & CELLS). cbv zeta in CELLS.
destruct CELLS as (V0 & V8 & V16 & V24). rewrite SPV in *.
set (WINP := YFha.WIN regs) in *.
assert (WE : forall a, WINP a <-> sp0 <= a < sp0 + 32) by (intros a; subst WINP; unfold YFha.WIN; rewrite SPV; clear - S5; nsp; lia).
assert (WST : forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; apply WE in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, WINP a \/ ~ WINP a) by (intros a; subst WINP; unfold YFha.WIN; apply ivl_dec).
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
(* The raw frame: the run writes only the 32-byte window at sp0 (WE), do_recycle's E. *)
assert (RW' : RAWF X mem').
{ intros x N0 N1 NS NT. rewrite (MQr x) by (intros Hw; apply WE in Hw; exact (NT Hw)). exact (RW x N0 N1 NS NT). }
exists (YFha.LZn (firstaddr ly t) lz), (zcanon (qb - b_bytes b mod 2 ^ 64)), regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
refine (conj _ (conj OK (conj PO' RW'))).
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb).
constructor.
- constructor.
+ exact (AR_after_stack_write B ly X W (FSP.unpoison UP mem) (FSP.unpoison UP mem') md mat WINP HAR WST WDEC MQ PRS).
+ exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC).
+ eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing].
+ exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC).
+ intros a Ha N0 N1 NS NT. rewrite (AG a Ha) by (intros Hw; apply WE in Hw; exact (NT Hw)). exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT).
+ intros a Ha. apply (presence_after_write W (FSP.unpoison UP mem) (FSP.unpoison UP mem') WINP a WDEC MQ PRS); [unfold YFhd.SY in Ha; clear - Ha S1 S2; nsp; lia|]. exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha).
+ exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- exact RXo.
- exists []. split; [reflexivity | reflexivity].
- rewrite Hk0. discriminate.
- exact BL.
- rewrite zlen_cons in LEN. clear - LEN. lia.
- unfold YFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
- unfold YFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
- unfold YFhd.batch_regs. splits; [exact R20 | exact R22 | exact R24].
- exact R1.
- exact R10.
- intros k ks' Hk. rewrite Hk0 in Hk. injection Hk as <- <-. exact R11.
- rewrite R23. f_equal. lia.
- rewrite R25. f_equal.
- apply (frame_cells_keep ly regs0 W W (FSP.unpoison UP mem) (FSP.unpoison UP mem')); [|exact FR]. intros a Ha. apply AG; [clear - Ha S5 U0 U1; nsp; lia|]. intros Hw. apply WE in Hw. clear - Ha Hw S5. nsp. lia.
- unfold YFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_addr; [exact V0u | rewrite zlen_cons; lia] || (replace (zlen t) with (zlen (b :: t) - 1) by (rewrite zlen_cons; lia); eapply val_mem_addr; [exact V0u | clear - S5; nsp; lia]).
+ eapply val_mem_addr; [exact V8u | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V16u | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V24u | clear - S5; nsp; lia].
+ unfold YFha.LZn. destruct (firstaddr ly t =? 0); [ceil; unfold ASAN_CEIL; lia | exact Rlz].
+ unfold zcanon, M64. apply Z.mod_pos_bound. lia.
- apply (batch_cells_xfer B ly (b :: t) (aview tfibsegs (w_H W) (FSP.unpoison UP mem))); [| | exact CE].
+ constructor; [exact BL | exact (rix_items_ok B X [] (b :: t) [] RX) ] || (unfold items_ok; constructor; [exact BL | exact (rix_items_ok B X _ t _ RXo)]).
+ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (apply (rix_slot B X [] (b :: t) [] b' RX); right; exact Hb).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha). apply AG; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia|]. intros Hw.
exact (slot_not_stack B ly X _ (b_self b') M SZ a Hs (WST a Hw)).
Qed.
(* YFhg.RC_post / CD_post through the U leaves of recycle_chunk / cache_dealloc; the raw frame by rawf_step. *)
Lemma RC_postU : forall X b t k ks i lz qb W regs mem md X1 ns W' c',
  rcst X b t (k :: ks) i lz qb W regs (FSP.unpoison UP mem) md -> RAWF X mem -> FK.rcc_leafU B ly X k UP W regs mem md (tt, X1) W' c' ->
  recycle_post U 0 0 0 X k ns (tt, X1) -> RSTU X1 b t ks (S i) W' c'.
Proof.
intros X b t k ks i lz qb W regs mem md X1 ns W' c' ST RW HL RP.
pose proof ST as [AC _ _ _ _ _ _ LR _ _ _ _ _ _ _ _ _].
destruct HL as (regs' & mem' & md' & -> & (POST & OK1 & PO1) & FR & CI & RC).
exact (lift PC_DR_R (raZ regs) (fun lz qb r m d => rst X1 b t ks (S i) lz qb W' r m d) X1 W' regs' mem' md'
  (RC_post X b t k ks i lz qb W regs (FSP.unpoison UP mem) md X1 ns W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison UP mem') md') ST
     (ex_intro _ regs' (ex_intro _ (FSP.unpoison UP mem') (ex_intro _ md' (conj eq_refl (conj POST (conj FR CI)))))) RP) OK1 PO1
  (rawf_step X X1 regs mem mem' (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs LR) RW RC)).
Qed.
Lemma CD_postU : forall X b t lz qb W regs mem md X2 ns W' c',
  cdst X b t lz qb W regs (FSP.unpoison UP mem) md -> RAWF X mem -> FK.cd_leafU B ly X UP W regs mem md (tt, X2) W' c' ->
  cache_dealloc_post U 0 0 0 X kBatchClass (b_self b - region_off kBatchClass) ns (tt, X2) -> QSTU X2 t W' c'.
Proof.
intros X b t lz qb W regs mem md X2 ns W' c' ST RW HL CP.
pose proof ST as [AC _ _ _ LR _ _ _ _ _ _ _ _].
destruct HL as (regs' & mem' & md' & -> & (POST & OK2 & PO2) & FR & CI & RC).
exact (lift PC_DR_Q (raZ regs) (fun lz qb r m d => qst X2 t lz qb W' r m d) X2 W' regs' mem' md'
  (CD_post X b t lz qb W regs (FSP.unpoison UP mem) md X2 ns W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison UP mem') md') ST
     (ex_intro _ regs' (ex_intro _ (FSP.unpoison UP mem') (ex_intro _ md' (conj eq_refl (conj POST (conj FR CI)))))) CP) OK2 PO2
  (rawf_step X X2 regs mem mem' (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs LR) RW RC)).
Qed.
(* YFhg.T_R for any UP. *)
Definition postRIU (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfibsegs) (c' : config) : Prop :=
match its with [] => CDSTU X b t W' c' | _ :: _ => RCSTU X b t its i W' c' end.
Lemma T_RU : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs (FSP.unpoison UP mem) md ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWF X mem ->
  SRr tfibsegs W (cfg_at tfibsegs PC_DR_R regs mem md) (postRIU X b t its i).
Proof.
intros X b t its i lz qb W regs mem md ST OK PO RW. pose proof ST as [AC RX ITS Hi BL LEN CR LR BR S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof (OFF_at X W mem md (FAR.ARU_intro B ly X UP W mem md HAR OK PO)) as OFF.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (fhc_real UP W ly regs mem _ _ _ _ OFF (seed_R B TB ly X0 P0 W0 regs0 mu0 md0 PRE X b t its i lz qb W regs (FSP.unpoison UP mem) md ST)) as FH.
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (rewrite Hits, zlen_app; unfold YFhd.zlen; rewrite Hdone; lia).
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (YFhk.segYR W ly regs mem md _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold YFhc.postR in HP. unfold postRIU.
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
+ unfold YFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold YFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ exact R1.
+ exact R10.
+ exact R11.
+ exact R12.
+ exact R13.
+ exact FR.
+ exact TM.
+ exact (batch_cells_tail B ly _ b t CE).
-
rewrite zlen_cons in LENi. replace (Z.of_nat i <? zlen (b_items b)) with true in HP by (symmetry; apply Z.ltb_lt; unfold YFhd.zlen in *; lia).
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
+ unfold YFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold YFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ unfold YFhd.batch_regs. rewrite <- R20, <- R22, <- R24. splits; apply CS; cbn; tauto.
+ exact R1.
+ rewrite R10, SPV. reflexivity.
+ intros k' ks' Hk. injection Hk as <- <-. exact R11.
+ rewrite R23. unfold YFhc.S7v. f_equal. lia.
+ rewrite R25. f_equal. lia.
+ exact FR.
+ exact TM.
+ exact CE.
Qed.
(* YFhg.T_Q for any UP; the last batch returns through dr_leafU (FK.dr_leafU_intro's form, inlined). *)
Definition postQOU (X : astate) (t : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
match t with [] => FINU (tt, X) W' c' | _ :: _ => OSTU X t W' c' end.
Local Notation v1 := (YFhl.v1 regs0).   Local Notation v8 := (YFhl.v8 regs0).   Local Notation v9 := (YFhl.v9 regs0).
Local Notation v18 := (YFhl.v18 regs0). Local Notation v19 := (YFhl.v19 regs0). Local Notation v20 := (YFhl.v20 regs0).
Local Notation v21 := (YFhl.v21 regs0). Local Notation v22 := (YFhl.v22 regs0). Local Notation v23 := (YFhl.v23 regs0).
Local Notation v24 := (YFhl.v24 regs0). Local Notation v25 := (YFhl.v25 regs0).
Lemma T_QU : forall X t lz qb W regs mem md, qst X t lz qb W regs (FSP.unpoison UP mem) md ->
  FSP.upoison_ok B ly X UP -> FSP.upoisoned tfibsegs W mem UP -> RAWF X mem ->
  SRr tfibsegs W (cfg_at tfibsegs PC_DR_Q regs mem md) (postQOU X t).
Proof.
intros X t lz qb W regs mem md ST OK PO RW. pose proof ST as [AC RX LEN CR LR FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof (OFF_at X W mem md (FAR.ARU_intro B ly X UP W mem md HAR OK PO)) as OFF.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mu0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof (fhb_real UP W ly regs mem _ _ _ _ _ _ _ _ _ _ _ _ OFF (seed_Q B TB ly X0 P0 W0 regs0 mu0 md0 PRE X t lz qb W regs (FSP.unpoison UP mem) md ST)) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (YFhj.segYQ W ly regs mem md (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold YFhb.postQ in HP. unfold postQOU.
destruct t as [|b t'].
-
rewrite zlen_nil, Z.eqb_refl in HP.
destruct HP as (-> & _ & regs' & mat & -> & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & CS).
exists regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, YFhl.v1. reflexivity. }
split.
+ split; [|exact (conj OK PO)].
split; [apply AR_wvb; exact HAR|]. split; [apply layout_le_refl|]. split; [exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)|]. split.
{ unfold YFhl.v8, YFhl.v9, YFhl.v18, YFhl.v19, YFhl.v20, YFhl.v21, YFhl.v22,
YFhl.v23, YFhl.v24, YFhl.v25, w64 in *. rewrite !Z_to_bv_bv_unsigned in *.
apply aregs_intro; try assumption.
- rewrite R2, SPV, S5. unfold YFhb.YFRAME, YFhd.sp0. replace (bv_unsigned (getr regs0 2) - 112 + 112) with (bv_unsigned (getr regs0 2)) by lia. apply Z_to_bv_bv_unsigned.
- rewrite <- C3; apply CS; cbn; tauto.
- rewrite <- C4; apply CS; cbn; tauto.
- rewrite <- C26; apply CS; cbn; tauto.
- rewrite <- C27; apply CS; cbn; tauto. }
split; [eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]|]. split.
{ intros a Ha N0 N1 NS NT. exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT). }
intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YFhd.SY. unfold spZ in Ha. clear - Ha. nsp. lia.
(* the 32-byte window's presence, and the raw frame: this run writes nothing, so RAWF is it. *)
+ split; [|exact RW].
  intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YFhd.SY. unfold spZ in Ha. clear - Ha. nsp. lia.
-
replace (zlen (b :: t') =? 0) with false in HP by (symmetry; apply Z.eqb_neq; rewrite zlen_cons; unfold YFhd.zlen; lia).
destruct HP as (-> & _ & regs' & mat & -> & R2 & CS & R10).
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
refine (conj _ (conj OK (conj PO RW))).
constructor.
+ constructor; [apply AR_wvb; exact HAR | exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]
| exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC)].
+ exact RX.
+ discriminate.
+ exact LEN.
+ unfold YFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold YFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ exact R10.
+ exact FR.
+ exact TM.
+ exact CE.
Qed.
(* lib/B/YFes.v ITEMS / LOOP / tfib_dorecycle_arm for any UP. *)
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
intros [[] X1] W' c' HL [ns' RP]. cbn [snd]. exact (RC_postU X b t k ks i lz qb W regs mem md X1 ns' W' c' ST RW HL RP).
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
intros [[] X2] W' c' HL [ns' CP]. cbn [snd]. exact (CD_postU X1 b t lz qb W1 regs mem md X2 ns' W' c' ST1 RW1 HL CP).
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
assert (WALK : SRr tfibsegs W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) (YFh9.postE W0 ly regs0 mem0 md0 (zlen P0))).
{ unfold cfg_at. rewrite <- (wvb_self md0) at 1. exact (YFhe.segYE W0 ly regs0 mem0 md0 (zlen P0) (m_vm_materialized md0) FH). }
unfold YFh9.postE in WALK.
assert (CASES : P0 = [] \/ exists b t, P0 = b :: t) by (clear; destruct P0 as [|b t]; [left; reflexivity | right; exists b, t; reflexivity]).
destruct CASES as [EP|(b & t & EP)].
-
rewrite EP. rewrite EP, zlen_nil, Z.eqb_refl in WALK. cbn [do_recycle amreal ret].
eapply SRr_mono; [exact WALK|]. intros W' c' _ HP.
destruct HP as (-> & _ & regs & mem & mat & -> & R2 & CS & MQr & PRSr).
assert (WST : forall a, YFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold YFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, YFh9.WIN regs0 a \/ ~ YFh9.WIN regs0 a) by (intros a; unfold YFh9.WIN; apply ivl_dec).
(* The run's post on the real memory, read on unpoison UP mem; UP keeps its 0xf7 bytes (off the window). *)
pose proof (meq_unpoison UP (YFh9.WIN regs0) mem0 mem MQr) as MQ.
assert (PRS : forall a, YFh9.WIN regs0 a -> apresent (w_H W0) (FSP.unpoison UP mem) a) by (intros a Ha; apply FAR.apresent_to_unpoison; exact (PRSr a Ha)).
assert (PO' : FSP.upoisoned tfibsegs W0 mem UP)
  by (apply (FK.upoisoned_frame B ly X0 UP W0 mem0 md0 HU mem (YFh9.WIN regs0)); [intros a Ha; pose proof (WST a Ha) as Hs; clear - Hs E7; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact MQr]).
exists regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split.
{ unfold cfg_at, raZ. rewrite Z_to_bv_bv_unsigned || (unfold w64; rewrite Z_to_bv_bv_unsigned). reflexivity. }
split.
+ split; [|exact (conj OK0 PO')].
split; [exact (AR_after_stack_write B ly X0 W0 mu0 (FSP.unpoison UP mem) md0 mat _ HAR WST WDEC MQ PRS)|].
split; [apply layout_le_refl|]. split; [apply wle_refl|]. split.
{ apply aregs_intro; first [exact R2 | apply CS; cbn; tauto]. }
split; [apply same_io_with_vm_backing|]. split.
{ intros a Ha _ _ NS _. apply (aview_after_write (w_H W0) mu0 (FSP.unpoison UP mem) _ a MQ Ha).
intros Hw. apply NS. left. unfold YFh9.WIN in Hw. clear - Hw. nsp. lia. }
intros a Ha. apply (presence_after_write W0 mu0 (FSP.unpoison UP mem) _ a WDEC MQ PRS); [clear - Ha S1 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
+ split.
  * intros a Ha. apply (presence_after_write W0 mu0 (FSP.unpoison UP mem) _ a WDEC MQ PRS); [clear - Ha S1 S2 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
  * (* the raw frame: the run writes only its frame (YFh9.WIN), in do_recycle's scratch. *)
    intros x _ _ NS _. apply MQr. intros Hw. apply NS. left. unfold spZ, YFh9.WIN in *. clear - Hw. nsp. lia.
-
replace (zlen P0 =? 0) with false in WALK by (symmetry; apply Z.eqb_neq; rewrite EP, zlen_cons; unfold YFhd.zlen; lia).
eapply amreal_SRr_pre; [exact WALK|]. intros W' c' _ HP.
apply (LOOPU P0 100000%nat X0 W' c' (T_EU W' c' HP)).
apply Nat2Z.inj_le. rewrite of_nat_100000. clear - LENP. lia.
Qed.
End e.
(* lib/B/YFes.v tfib_dorecycle_ok for any U; the cache_dealloc premise has the shape of lane cd's tfib_cdealloc_okU. *)
Theorem tfib_dorecycle_okU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FK.tfib_rchunk_specU B ->
  (forall ly X c off UP W regs mem md, FK.cd_preU B ly X c off UP W regs mem md -> ly_tsd ly = TFIB_TSD ->
     amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (FK.cd_leafU B ly X UP W regs mem md)) ->
  FK.tfib_dorecycle_specU B.
Proof. intros B _ TB RCCU CDU ly X P UP W regs mem md PREU. exact (tfib_dorecycle_armU B TB RCCU CDU ly X P UP W regs mem md PREU). Qed.
End d.

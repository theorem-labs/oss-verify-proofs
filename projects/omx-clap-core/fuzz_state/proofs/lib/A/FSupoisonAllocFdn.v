(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 5 address literal(s) rewritten, module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/AFet.v, with its module paths changed; 642 of its 891 lines of code are new or changed and 481 lines of the source are left out. *)
(* The drain walk of free (lib/A/AFet.v tfib_drain_ok, over AFer.v, AFev.v, AFey.v and the walk specs AFgg-AFh8) for any U: tfib_drain_okU. The runs (AFgg.segDE / AFgh.segDN, AFh0.segL, AFh8.segX) go on the real memory with real records; the facts, FIN_a and DRPRE are the donor's at unpoison U mem. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: RETD_ug returns the early return's run frame, FIN_aU and EPIU prove drain_leafU's raw conjunct (WIN_own, DW_own: AFet.v's WD with AFey.D_owned; EPIU takes the loop's frame and do_recycle's raw leaf): raw memory frame re-exported for the ARU lift of route 1. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFew AFff AFeu AFey AFgj AFgg AFgh AFgl AFh0 AFgt AFh8 AFev AFer AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AFet FSupoison FSupoisonU FSupoisonAllocR FSupoisonAllocFK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFK.
(* Some module of the kit's closure leaves lia without div/mod reasoning (zify's euclidean-division flag false); the
   donor text (lib/A/AFet.v, AFer.v) is proved with it on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section dn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Where U is not, for the drain walk. drain_fixed: every byte the drain walk transfers between the two readings *)
(*    or writes (the stack, the quarantine object in the image, the thread object's qc, the batch headers in the    *)
(*    primary region). All of it is application memory, so off U (drain_regions_off_ush). The lemmas of this section *)
(*    take the donor facts they need (AFev.HI, AFev.HSP) as hypotheses and use only built walk-spec files.          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section rg.
Variable B : asyms.
Variables (ly : alayout) (X : astate) (UP : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model).
Hypothesis ARU0 : FSP.ARU tfibsegs B ly X UP W mem md.
(* AFev.HI *)
Hypothesis HI0 : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_T ly) kThreadObjSize /\
  ly_T ly + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
  ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
  (forall b2, In b2 (all_batches X) -> ly_prim ly <= ly_space ly + b_self b2 /\ ly_space ly + b_self b2 + kBatchBytes <= ly_space ly + kSpaceSize) /\
  4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd.
(* AFev.HSP *)
Hypothesis HSP0 : ly_stk_lo ly + DSTACK <= bv_unsigned (YK11.getr regs 2) <= ly_stk_hi ly.
Let mu : word -> option byte := FSP.unpoison UP mem.
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation GLv := (AFgj.GLv ly gq).

Definition drain_fixed (a : Z) : Prop :=
  (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END) \/
  (T <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).

Lemma drain_regions_off_ush : forall a, drain_fixed a -> FAR.offU UP a.
Proof using All.
intros a Ha. destruct HI0 as (hP1 & hP2 & hT1 & _). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- exact (FAR.stack_offU B ly X UP W mem md a ARU0 Ha).
- apply (FAR.offU_low B ly X UP W mem md a ARU0). unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *. lia.
- exact (FK.offU_zone3 B ly X UP W mem md ARU0 T kThreadObjSize a hT1 Ha).
- apply (FAR.offU_high B ly X UP W mem md a ARU0). unfold kHighMemBeg, kPrimResvSize in *. lia.
Qed.

Lemma ush_not_fixed : forall s, FSP.in_ush UP s = true -> ~ drain_fixed s.
Proof using All.
intros s Hs Hf. pose proof (drain_regions_off_ush s Hf) as O. unfold FAR.offU in O.
pose proof (FSP.ush_range tfibsegs B ly X UP W mem md s ARU0 Hs) as R. rewrite Z.mod_small in O by exact R. congruence.
Qed.

Lemma vm_of_u : forall (H : word -> bool) (m : word -> option byte) a (w : nat) v,
  (forall k, 0 <= k < Z.of_nat w -> drain_fixed (a + k)) ->
  val_mem tfibsegs (mrestrict H (FSP.unpoison UP m)) a w v -> val_mem tfibsegs (mrestrict H m) a w v.
Proof using All.
intros H m a w v F V. apply (FAR.val_mem_of_unpoison H UP m a w v); [|exact V].
intros k Hk. apply drain_regions_off_ush. apply F. lia.
Qed.

Lemma vm_to_u : forall (H : word -> bool) (m : word -> option byte) a (w : nat) v,
  (forall k, 0 <= k < Z.of_nat w -> drain_fixed (a + k)) ->
  val_mem tfibsegs (mrestrict H m) a w v -> val_mem tfibsegs (mrestrict H (FSP.unpoison UP m)) a w v.
Proof using All.
intros H m a w v F V. apply (FAR.val_mem_to_unpoison H UP m a w v); [|exact V].
intros k Hk. apply drain_regions_off_ush. apply F. lia.
Qed.

Lemma pres_of_u : forall (H : word -> bool) (m : word -> option byte) a, drain_fixed a ->
  apresent H (FSP.unpoison UP m) a -> apresent H m a.
Proof using All. intros H m a F P. exact (FAR.apresent_of_unpoison H UP m a (drain_regions_off_ush a F) P). Qed.

Lemma mbyte_to_u : forall (H : word -> bool) (m : word -> option byte) a, drain_fixed a ->
  mbyte tfibsegs (mrestrict H (FSP.unpoison UP m)) a = mbyte tfibsegs (mrestrict H m) a.
Proof using All. intros H m a F. exact (FAR.mbyte_unpoison H UP m a (drain_regions_off_ush a F)). Qed.

(* A frame against mem is a frame against unpoison U mem, for unpoison U of the new memory. *)
Lemma unpoison_frame : forall (m : word -> option byte) (P : Z -> Prop),
  (forall x : word, ~ P (bv_unsigned x) -> m x = mem x) -> forall x : word, ~ P (bv_unsigned x) -> FSP.unpoison UP m x = mu x.
Proof using All. intros m P F x Hx. unfold mu, FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (F x Hx)]. Qed.

(* drain_fixed misses the shadow band (for FSupoisonAllocFK.upoisoned_frame). *)
Lemma fixed_noshadow : forall a, drain_fixed a -> ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof using All.
intros a Ha. destruct HI0 as (hP1 & hP2 & hT1 & _ & hS1 & _). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- lia.
- unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in *. lia.
- unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
- lia.
Qed.

Lemma stk_fixed : forall a, bv_unsigned (YK11.getr regs 2) - DSTACK <= a < bv_unsigned (YK11.getr regs 2) -> drain_fixed a.
Proof using All. intros a Ha. left. unfold DSTACK in *. lia. Qed.

Lemma Q_fixed : forall k, 0 <= k < 192 -> drain_fixed (A_QUAR + k).
Proof using All. intros k Hk. right; left. unfold A_QUAR, A_ALLOCATOR, o_quar, TFIB_IMG_LO, TFIB_IMG_END. lia. Qed.

Lemma T_fixed : forall k, 0 <= k < 32 -> drain_fixed (T + t_qc + k).
Proof using All. intros k Hk. right; right; left. unfold t_qc, kThreadObjSize. lia. Qed.

Lemma batch_fixed : forall b2 k, In b2 (all_batches X) -> 0 <= k < kBatchBytes -> drain_fixed (SB + b_self b2 + k).
Proof using All.
intros b2 k Hb Hk. destruct HI0 as (_ & _ & _ & _ & _ & _ & hSP1 & hSP2 & HB & _). destruct (HB b2 Hb) as (L1 & L2).
do 3 right. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
Qed.

Lemma glast_in : forall lb initr, rev G = lb :: initr -> In lb (all_batches X).
Proof using All.
intros lb initr Hrev. unfold all_batches. apply in_app_iff. right. rewrite <- (rev_involutive G), Hrev. cbn [rev].
apply in_app_iff. right. left. reflexivity.
Qed.

Lemma GLv_fixed : forall lb initr, rev G = lb :: initr -> forall k, 0 <= k < kBatchBytes -> drain_fixed (GLv + k).
Proof using All.
intros lb initr Hrev k Hk. unfold AFgj.GLv. rewrite Hrev. exact (batch_fixed lb k (glast_in lb initr Hrev) Hk).
Qed.

Lemma WIN_fixed : forall a, AFgj.WIN ly regs gq a -> drain_fixed a.
Proof using All.
intros a Hw. unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hq Hw]]].
- apply stk_fixed. unfold DSTACK. lia.
- replace a with (A_QUAR + (a - A_QUAR)) by lia. apply Q_fixed. lia.
- replace a with (A_QUAR + (a - A_QUAR)) by lia. apply Q_fixed. lia.
- replace a with (T + t_qc + (a - (T + t_qc))) by lia. apply T_fixed. lia.
- destruct (rev G) as [|lb initr] eqn:Hrev; [exfalso; apply Hq; rewrite <- (rev_involutive G), Hrev; reflexivity|].
  replace a with (GLv + (a - GLv)) by lia. apply (GLv_fixed lb initr Hrev). unfold kBatchBytes. lia.
Qed.

(* The seed's regions (AFgj.SS0) are off U. *)
Lemma SEED_regions_offU : FAR.regions_offU UP (AFgj.E0 ly regs gq tq) (ss_mem AFgj.SS0).
Proof using All.
pose proof HI0 as (hP1 & hP2 & hT1 & _). pose proof HSP0 as [S1 S2].
assert (ET : bv_unsigned (ew (AFgj.E0 ly regs gq tq) 32) = T).
{ rewrite AFgj.EqT. unfold w64. apply unsigned_lit_small. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. clear - hT1 CR. unfold zone3, kThreadObjSize in hT1. lia. }
assert (E2 : bv_unsigned (ew (AFgj.E0 ly regs gq tq) 2) = bv_unsigned (YK11.getr regs 2)) by (rewrite AFgj.E2; reflexivity).
intros r a Hr Ha. apply drain_regions_off_ush. unfold drain_fixed.
unfold AFgj.SS0, AFgj.REG0, AFgj.R_QW, AFgj.R_QG, AFgj.R_QT, flit8 in Hr. cbn [ss_mem In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?ET, ?E2 in Ha;
  unfold A_QUAR, A_ALLOCATOR, o_quar, t_qc, kThreadObjSize, DSTACK, TFIB_IMG_LO, TFIB_IMG_END in *; lia|]).
destruct Hr.
Qed.

(* Seed transfer (unpoison U mem -> mem): AFgj.free_hyps, the record of the drain prologue walks AFgg / AFgh. *)
Lemma FH_realg : AFgj.free_hyps W ly regs mu gq tq -> AFgj.free_hyps W ly regs mem gq tq.
Proof using All.
intros FH. destruct FH as [LY IM Htp Hra Hra4 Hsp Hal Hpres Hg Ht Hglast SEED].
constructor; try assumption.
- intros a Ha. apply (pres_of_u _ _ a); [apply stk_fixed; exact Ha | exact (Hpres a Ha)].
- intros lb initr Hrev. destruct (Hglast lb initr Hrev) as (L1 & L2 & L3 & L4 & L5). pose proof (GLv_fixed lb initr Hrev) as GF.
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  split; [apply vm_of_u; [intros k Hk; apply GF; unfold kBatchBytes; lia | exact L4]|].
  intros a Ha. apply (pres_of_u _ _ a); [replace a with (GLv + (a - GLv)) by lia; apply GF; unfold kBatchBytes; lia | exact (L5 a Ha)].
- exact (proj1 (FAR.st_ok_unpoison_iff UP (AFgj.E0 ly regs gq tq) AFgj.SS0 (w_H W) regs (w64 0x33b08) mem (YK11.seg_rom tfibsegs)
    SEED_regions_offU) SEED).
Qed.

(* Post transfer (mem -> unpoison U mem) at the drain's early return (AFgj.at_RETD), and U's bytes there. *)
Lemma RETD_ug : forall W' c', AFgj.at_RETD W ly regs mem md gq tq W' c' ->
  exists regs' mem' mat, W' = W /\
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    AFgj.at_RETD W ly regs mu md gq tq W
      (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    FSP.upoisoned tfibsegs W mem' UP /\ (forall x : word, ~ AFgj.WIN ly regs gq (bv_unsigned x) -> mem' x = mem x).
Proof using All.
intros W' c' (-> & regs' & mem' & mat & -> & R2 & CS & MQ & PRESW & CELLS). cbv zeta in CELLS.
destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CGL).
assert (QF : forall o j, 152 <= o -> o + 8 <= 192 -> 0 <= j < 8 -> drain_fixed (A_QUAR + o + j)).
{ intros o j H1 H2 Hj. replace (A_QUAR + o + j) with (A_QUAR + (o + j)) by lia. apply Q_fixed. lia. }
assert (TF : forall o j, 0 <= o -> o + 8 <= 32 -> 0 <= j < 8 -> drain_fixed (T + t_qc + o + j)).
{ intros o j H1 H2 Hj. replace (T + t_qc + o + j) with (T + t_qc + (o + j)) by lia. apply T_fixed. lia. }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split.
- split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
  split; [exact R2|]. split; [exact CS|].
  split; [exact (unpoison_frame mem' (AFgj.WIN ly regs gq) MQ)|].
  split; [intros a Hw Hh; apply FAR.apresent_to_unpoison; exact (PRESW a Hw Hh)|].
  cbv zeta.
  split; [intros a Ha; rewrite mbyte_to_u by (replace a with (A_QUAR + (a - A_QUAR)) by lia; apply Q_fixed; lia); exact (C152 a Ha)|].
  split; [apply vm_to_u; [intros k Hk; apply (QF 160); lia | exact C160]|].
  split; [apply vm_to_u; [intros k Hk; apply (QF 168); lia | exact C168]|].
  split; [apply vm_to_u; [intros k Hk; apply (QF 176); lia | exact C176]|].
  split; [apply vm_to_u; [intros k Hk; apply (QF 184); lia | exact C184]|].
  split; [apply vm_to_u; [intros k Hk; apply T_fixed; lia | exact Cq0]|].
  split; [apply vm_to_u; [intros k Hk; apply (TF 8); lia | exact Cq8]|].
  split; [apply vm_to_u; [intros k Hk; apply (TF 16); lia | exact Cq16]|].
  split; [apply vm_to_u; [intros k Hk; apply (TF 24); lia | exact Cq24]|].
  intros lb initr Hrev. apply vm_to_u; [intros k Hk; apply (GLv_fixed lb initr Hrev); unfold kBatchBytes; lia | exact (CGL lb initr Hrev)].
- split; [exact (FK.upoisoned_frame B ly X UP W mem md ARU0 mem' (AFgj.WIN ly regs gq) (fun a Ha => fixed_noshadow a (WIN_fixed a Ha)) MQ) | exact MQ].
Qed.
End rg.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The drain walk for any U. mu := unpoison U mem; the donor facts and leaves run at mu (PRE_u), the runs on mem. *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis DRU : FK.tfib_dorecycle_specU B.
Variables (ly : alayout) (X : astate) (UP : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model).
Hypothesis PREU : FK.drain_preU B ly X UP W regs mem md.
Let mu : word -> option byte := FSP.unpoison UP mem.
Let PRE_u : drain_pre B ly X W regs mu md := proj1 PREU.
Let sp0 : Z := bv_unsigned (YK11.getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mu).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Local Notation GLv := (AFgj.GLv ly gq).
Local Notation TFv := (AFgj.TFv ly tq).
Local Notation TLv := (AFgj.TLv ly tq).
Local Notation M := (AFev.M B ly X W regs mu md PRE_u).
Local Notation HSP := (AFev.HSP B ly X W regs mu md PRE_u).
Local Notation HI := (AFev.HI B ly X W regs mu md PRE_u).
Local Notation IMG := (AFev.IMG B ly X W regs mu md PRE_u).
Local Notation batch_facts := (AFev.batch_facts B ly X W regs mu md PRE_u).
Local Notation g_facts := (AFev.g_facts B ly X W regs mu md PRE_u).
Local Notation t_facts := (AFev.t_facts B ly X W regs mu md PRE_u).
Local Notation L := (AFer.L X).
Local Notation L_all := (AFer.L_all X).
Local Notation addr := (AFer.addr ly).
Local Notation firstaddr := (AFer.firstaddr ly).
Local Notation lastaddr := (AFer.lastaddr ly).
Local Notation zlen := AFer.zlen.
Local Notation sp1 := (AFer.sp1 regs).
Local Notation DW := (AFer.DW ly X regs).
(* The loop's invariants on the REAL memory (their frame is against mem). *)
Local Notation LST := (AFer.LST ly X W regs mem md).
Local Notation ATDR := (AFer.ATDR ly X W regs mem md).
(* do_recycle's call point read at mu (the input of the donor's DRPRE). *)
Local Notation ATDRu := (AFer.ATDR ly X W regs mu md).
Local Notation XT := (AFey.XT X).
Let OK0 : FSP.upoison_ok B ly X UP := proj1 (proj2 PREU).
Let ARU0 : FSP.ARU tfibsegs B ly X UP W mem md := conj (proj1 PRE_u) (proj2 PREU).
Local Notation VMOF := (vm_of_u B ly X UP W regs mem md ARU0 HI HSP).
Local Notation VMTO := (vm_to_u B ly X UP W regs mem md ARU0 HI HSP).
Local Notation PRESOF := (pres_of_u B ly X UP W regs mem md ARU0 HI HSP).
Local Notation MBTO := (mbyte_to_u B ly X UP W regs mem md ARU0 HI HSP).
Local Notation UFRAME := (unpoison_frame B ly X UP W regs mem md ARU0 HI HSP).
Local Notation FNS := (fixed_noshadow B ly X UP W regs mem md ARU0 HI HSP).
Local Notation STKF := (stk_fixed B ly X UP W regs mem md ARU0 HI HSP).
Local Notation QF := (Q_fixed B ly X UP W regs mem md ARU0 HI HSP).
Local Notation TF := (T_fixed B ly X UP W regs mem md ARU0 HI HSP).
Local Notation BFX := (batch_fixed B ly X UP W regs mem md ARU0 HI HSP).
Local Notation GLIN := (glast_in B ly X UP W regs mem md ARU0 HI HSP).

(* The record of the prologue walks on the real memory. *)
Lemma FH_real : AFgj.free_hyps W ly regs mem gq tq.
Proof. exact (FH_realg B ly X UP W regs mem md ARU0 HI HSP (AFev.FH_ok B TB ly X W regs mu md PRE_u)). Qed.

(* The caller's stack frame is present in the real memory. *)
Lemma HPRESr : forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem a.
Proof.
intros a Ha. pose proof PRE_u as (_ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES.
apply (PRESOF _ _ a); [apply STKF; exact Ha | apply HPRES; exact Ha].
Qed.

(* The drain's write window in the loop (AFer.DW) lies in drain_fixed. *)
Lemma DW_fixed : forall P a, (forall b2, In b2 P -> In b2 (all_batches X)) -> DW P a -> drain_fixed ly a.
Proof.
intros P a PL Hw. unfold AFer.DW, AFgj.WINF in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[[Hq Hw]|(b2 & Hb2 & Hw)]]].
- apply STKF. unfold LFRAME, DSTACK in *. lia.
- replace a with (A_QUAR + (a - A_QUAR)) by lia. apply QF. lia.
- replace a with (A_QUAR + (a - A_QUAR)) by lia. apply QF. lia.
- replace a with (T + t_qc + (a - (T + t_qc))) by lia. apply TF. lia.
- destruct (rev G) as [|lb initr] eqn:Hrev; [exfalso; apply Hq; rewrite <- (rev_involutive G), Hrev; reflexivity|].
  assert (EQ : GLv = SB + b_self lb) by (unfold AFgj.GLv; rewrite Hrev; reflexivity). rewrite EQ in Hw.
  replace a with (SB + b_self lb + (a - (SB + b_self lb))) by lia.
  apply BFX; [exact (GLIN lb initr Hrev) | unfold kBatchBytes; lia].
- unfold AFer.addr in Hw. replace a with (SB + b_self b2 + (a - (SB + b_self b2))) by lia.
  apply BFX; [exact (PL b2 Hb2) | unfold kBatchBytes; lia].
Qed.

(* AFet.v FIN_a's WD and AFey.D_owned: every byte of the early return's write window is owned or in the stack window. *)
Lemma WIN_own : forall a, 0 <= a < 2 ^ 64 -> AFgj.WIN ly regs gq a -> aowned B ly X a \/ (spZ regs - DSTACK <= a < spZ regs) \/ False.
Proof.
intros a Ha Hw. pose proof HSP as HSP'. pose proof (AFev.AQ B TB) as EAQ.
assert (WD : AFey.D B ly X [] sp0 a).
{ unfold AFey.D, AFey.DT, AFey.DQ, AFey.DL, AFey.DS.
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in Hw. fold sp0 in Hw. rewrite EAQ in Hw.
unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hq Hw]]].
- do 4 right. clear - Hw. unfold DSTACK. lia.
- right; left. left. lia.
- right; left. right. lia.
- left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFey.GLv, AFey.addr. unfold AFgj.GLv in Hw. destruct (rev G); [exact Hw | exact Hw]. }
destruct (AFey.D_owned B ly X _ M [] L eq_refl sp0 HSP' IMG a (proj1 Ha) WD) as [O|O]; [left; exact O | right; left; unfold spZ; exact O].
Qed.

(* AFet.v DRPRE's WD and AFey.D_owned: every byte of the loop's write window (AFer.DW) is owned or in the stack window. *)
Lemma DW_own : forall P R, L = P ++ R -> forall a, 0 <= a < 2 ^ 64 -> DW P a -> aowned B ly X a \/ (sp0 - DSTACK <= a < sp0).
Proof.
intros P R HL a Ha Hw. pose proof HSP as HSP'. pose proof (AFev.AQ B TB) as EAQ.
assert (WD : AFey.D B ly X P sp0 a).
{ unfold AFey.D, AFey.DT, AFey.DQ, AFey.DL, AFey.DP, AFey.DS.
unfold AFer.DW, AFgj.WINF in Hw. fold sp0 in Hw. rewrite EAQ in Hw. unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[[Hq Hw]|(b & Hb & Hw)]]].
- do 4 right. clear - Hw. unfold DSTACK, LFRAME in *. lia.
- right; left. left. lia.
- right; left. right. lia.
- left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFey.GLv, AFey.addr. unfold AFgj.GLv in Hw. destruct (rev G); [exact Hw | exact Hw].
- right; right; right; left. exists b. split; [exact Hb|]. unfold AFey.addr. unfold AFer.addr in Hw. exact Hw. }
exact (AFey.D_owned B ly X _ M P R HL sp0 HSP' IMG a (proj1 Ha) WD).
Qed.

(* Leaf of the early return: FIN_a at mu, then U's two invariants (drain moves batches between the quarantines and
   keeps the allocated chunks; its window is off U), and the raw frame from the run's frame (WIN_own). *)
Lemma FIN_aU : forall W' c', AFgj.at_RETD W ly regs mem md gq tq W' c' -> FK.drain_leafU B ly X UP W regs mem md (tt, XT) W' c'.
Proof.
intros W' c' HR. destruct (RETD_ug B ly X UP W regs mem md ARU0 HI HSP W' c' HR) as (regs' & mem' & mat & -> & -> & HRu & PO' & MQ).
pose proof (AFet.FIN_a B TB ly X W regs mu md PRE_u W _ HRu) as HL.
assert (EC : forall m, mkCfg (YK11.mkst regs' (YK11.getr regs 1) m (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) =
  cfg_at tfibsegs (raZ regs) regs' m (with_vm_backing (m_vm_lazy md) mat md)).
{ intros m. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite EC in HL. rewrite EC.
apply FK.drain_leafU_intro; [exact HL | | exact PO' | exact (FK.raw_of_meq B ly X XT DSTACK regs (fun _ => False) (AFgj.WIN ly regs gq) mem mem' MQ WIN_own)].
cbn [snd]. apply (FAR.upoison_ok_keep B ly X ly XT UP OK0). intros r p n _ Hb _ _. exact Hb.
Qed.

(* Post transfer (mem -> mu) at do_recycle's call point. *)
Lemma ATDR_u : forall P R W' c', ATDR P R W' c' -> L = P ++ R ->
  exists regs' mem' mat, W' = W /\ c' = cfg_at tfibsegs A_DoRecycle regs' mem' (with_vm_backing (m_vm_lazy md) mat md) /\
    (forall x : word, ~ DW P (bv_unsigned x) -> mem' x = mem x) /\
    ATDRu P R W (cfg_at tfibsegs A_DoRecycle regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros P R W' c' (-> & regs' & mem' & mat & -> & R2 & R10 & R11 & R12 & R13 & R1 & CS & MQ & PRS & CELLS) HL. cbv zeta in CELLS.
destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CG & CP & Ct0 & Ct8 & Ct16 & Ct24 & Cs32 & Cs40 & Cs48 & Cs56 & Cs64 & Cs72).
assert (PL : forall b2, In b2 P -> In b2 (all_batches X)) by (intros b2 Hb2; apply L_all; rewrite HL; apply in_app_iff; left; exact Hb2).
assert (QF' : forall o j, 152 <= o -> o + 8 <= 192 -> 0 <= j < 8 -> drain_fixed ly (A_QUAR + o + j)).
{ intros o j H1 H2 Hj. replace (A_QUAR + o + j) with (A_QUAR + (o + j)) by lia. apply QF. lia. }
assert (TF' : forall o j, 0 <= o -> o + 8 <= 32 -> 0 <= j < 8 -> drain_fixed ly (T + t_qc + o + j)).
{ intros o j H1 H2 Hj. replace (T + t_qc + o + j) with (T + t_qc + (o + j)) by lia. apply TF. lia. }
assert (SF : forall o j, 0 <= o -> o + 8 <= 80 -> 0 <= j < 8 -> drain_fixed ly (sp1 + o + j)).
{ intros o j H1 H2 Hj. apply STKF. unfold AFer.sp1, LFRAME, DSTACK in *. lia. }
assert (SF0 : forall j, 0 <= j < 8 -> drain_fixed ly (sp1 + j)).
{ intros j Hj. apply STKF. unfold AFer.sp1, LFRAME, DSTACK in *. lia. }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [exact MQ|].
split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|]. split; [exact R1|]. split; [exact CS|].
split; [exact (UFRAME mem' (DW P) MQ)|].
split; [intros a Ha; apply FAR.apresent_to_unpoison; exact (PRS a Ha)|].
cbv zeta.
split; [intros a Ha; rewrite MBTO by (replace a with (A_QUAR + (a - A_QUAR)) by lia; apply QF; lia); exact (C152 a Ha)|].
split; [apply VMTO; [intros k Hk; apply (QF' 160); lia | exact C160]|].
split; [apply VMTO; [intros k Hk; apply (QF' 168); lia | exact C168]|].
split; [apply VMTO; [intros k Hk; apply (QF' 176); lia | exact C176]|].
split; [apply VMTO; [intros k Hk; apply (QF' 184); lia | exact C184]|].
split; [apply VMTO; [intros k Hk; apply TF; lia | exact Cq0]|].
split; [apply VMTO; [intros k Hk; apply (TF' 8); lia | exact Cq8]|].
split; [apply VMTO; [intros k Hk; apply (TF' 16); lia | exact Cq16]|].
split; [apply VMTO; [intros k Hk; apply (TF' 24); lia | exact Cq24]|].
split. { intros LT lb initr Hrev. apply VMTO; [|exact (CG LT lb initr Hrev)].
  intros k Hk. unfold AFer.addr. apply BFX; [exact (GLIN lb initr Hrev) | unfold kBatchBytes; lia]. }
split. { intros i b2 Hi. apply VMTO; [|exact (CP i b2 Hi)].
  intros k Hk. unfold AFer.addr. apply BFX; [exact (PL b2 (nth_error_In _ _ Hi)) | unfold kBatchBytes; lia]. }
split; [apply VMTO; [intros k Hk; apply SF0; lia | exact Ct0]|].
split; [apply VMTO; [intros k Hk; apply (SF 8); lia | exact Ct8]|].
split; [apply VMTO; [intros k Hk; apply (SF 16); lia | exact Ct16]|].
split; [apply VMTO; [intros k Hk; apply (SF 24); lia | exact Ct24]|].
split; [apply VMTO; [intros k Hk; apply (SF 32); lia | exact Cs32]|].
split; [apply VMTO; [intros k Hk; apply (SF 40); lia | exact Cs40]|].
split; [apply VMTO; [intros k Hk; apply (SF 48); lia | exact Cs48]|].
split; [apply VMTO; [intros k Hk; apply (SF 56); lia | exact Cs56]|].
split; [apply VMTO; [intros k Hk; apply (SF 64); lia | exact Cs64]|].
apply VMTO; [intros k Hk; apply (SF 72); lia | exact Cs72].
Qed.

(* The loop's entry (AFet.v L0_LST): the donor text, with the batch cells read at mu and moved to mem (off U). *)
Lemma L0_LSTU : forall W' c', AFgj.at_L0 W ly regs mem md gq tq W' c' -> LST [] L W' c'.
Proof.
intros W' c' (-> & regs' & mem' & mat & -> & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R5 & R1 & RS & MQ & PRES & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CGL & Cs80 & Cs72 & Cs64 & Cs56 & Cs48 & Cs40 & Cs32 & Cs24 & Cs16 & Cs8).
pose proof HSP as [S1 S2]. fold sp0 in S1, S2. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & EG). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & ET).
split; [reflexivity|]. exists regs', mem', mat. split; [reflexivity|].
split; [rewrite R2; unfold AFer.sp1, LFRAME; reflexivity|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
split; [rewrite R14; reflexivity|]. split; [rewrite R15; reflexivity|].
split; [rewrite R16; unfold AFgj.LSZv, AFgj.GSZv, AFgj.TSZv, AFer.zlen, AFer.L; rewrite length_app, Nat2Z.inj_add; reflexivity|].
split; [rewrite R5; unfold AFgj.LFv, AFgj.GFv, AFgj.TFv, AFer.firstaddr, AFer.L, AFer.addr; destruct G; [destruct Tq; reflexivity | reflexivity]|].
split; [exact R1|]. split; [exact RS|].
split. { intros x Hx. apply MQ. intros Hw. apply Hx. unfold AFer.DW. unfold AFgj.WIN, AFgj.WINA in Hw. fold sp0 in Hw. unfold LFRAME. fold sp0.
destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw]. }
split. { intros a Ha. destruct (AFev.WIN_dec ly X regs a) as [Hw|Hw].
- apply PRES; [exact Hw | unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia].
- pose proof HPRESr as HPRES.
apply (apresent_same H0 mem); [apply MQ; rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; lia); exact Hw | apply HPRES; exact Ha]. }
cbv zeta.
split; [exact C152|].
split; [unfold AFgj.LSZv, AFgj.GSZv, AFgj.TSZv in C160; unfold AFer.zlen, AFer.L; rewrite length_app, Nat2Z.inj_add; exact C160|].
split; [unfold AFgj.LFv, AFgj.GFv, AFgj.TFv in C168; unfold AFer.firstaddr, AFer.L, AFer.addr; destruct G; [destruct Tq; exact C168 | exact C168]|].
split; [exact C176|].
split; [unfold AFgj.LBv, AFgj.GBv, AFgj.TBv in C184; rewrite (AFer.sum_L B ly X W regs mu md PRE_u); exact C184|].
split; [exact Cq0|]. split; [exact Cq8|]. split; [exact Cq16|]. split; [exact Cq24|].
split. { intros _ lb initr Hrev. destruct (AFev.glast_facts B ly X W regs mu md PRE_u lb initr Hrev) as (_ & EQ & _). unfold AFer.addr. rewrite <- EQ. exact (CGL lb initr Hrev). }
split. { intros i b Hi. destruct i; discriminate Hi. }
split. {
intros i b Hi. pose proof (nth_error_In _ _ Hi) as INb. apply AFer.L_all in INb.
destruct (batch_facts b INb) as (L1 & L2 & L3 & L4 & L5 & _).
pose proof (AFey.batches_nodup B ly X _ M) as ND. unfold all_batches in ND.
assert (OLDQ : Forall (cell_holds B ly rd0) (quar_cells X)).
{ apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M)). unfold acells. rewrite !in_app_iff. do 4 right; left. exact Hc. }
unfold quar_cells, qc_cells in OLDQ. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_app in OLDQ as [OT OG].
do 4 (apply Forall_cons_iff in OT as [_ OT]). do 4 (apply Forall_cons_iff in OG as [_ OG]).
assert (VMQ : forall a (n : nat) v, (forall j, 0 <= j < Z.of_nat n -> ~ AFgj.WIN ly regs gq (a + j) /\ 0 <= a + j < 2 ^ 64) ->
val_mem tfibsegs (mrestrict H0 mem) a n v -> val_mem tfibsegs (mrestrict H0 mem') a n v).
{ intros a n v Hn Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(lia)) as [N1 N2]. apply MQ. rewrite unsigned_lit_small by exact N2. exact N1. }
assert (NW : forall j, 0 <= j < 16 -> (forall lb initr, rev G = lb :: initr -> b_self b <> b_self lb \/ 8 <= j) -> ~ AFgj.WIN ly regs gq (addr b + j) /\ 0 <= addr b + j < 2 ^ 64).
{ intros j Hj NL. pose proof (AFev.GEO B ly X W regs mu md PRE_u) as (G_PT & _ & _ & G_PS & _). pose proof (AFev.AQ B TB) as EAQ. unfold o_quar in EAQ.
split; [| ceil; unfold AFer.addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA. fold sp0. unfold AFer.addr. intros [Y|[[Y|[Y|Y]]|[NE Y]]].
- unfold DSTACK, kPrimResvSize, kSpaceSize, kBatchBytes in *. lia.
- rewrite EAQ in Y. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. lia.
- rewrite EAQ in Y. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. lia.
- unfold t_qc, kThreadObjSize, kPrimResvSize, kSpaceSize, kBatchBytes in *. lia.
- destruct (rev G) as [|lb initr] eqn:Hrev; [apply NE; rewrite <- (rev_involutive G), Hrev; reflexivity|].
destruct (AFev.glast_facts B ly X W regs mu md PRE_u lb initr Hrev) as (INlb & EQ & _). rewrite EQ in Y.
destruct (NL lb initr eq_refl) as [NEQ|J8]; [|unfold kBatchBytes in *; lia].
pose proof (AFey.batches_apart B ly X _ M _ HSP b lb INb INlb NEQ) as D. unfold zdisjoint, AFey.addr, kBatchBytes in D. cbn [fst snd] in D. lia. }
split.
-
destruct (AFey.cat_next X [] L ltac:(reflexivity) i b Hi) as [(i' & Hi' & EN)|[(i' & Hi' & Si & EN)|(initr & Hrev & Sj & EN)]].
+   unfold next_addr. change (AFer.L X) with (G ++ Tq). fold (next_exp (G ++ Tq) i).
pose proof (proj1 (Forall_forall _ _) OT _ (proj2 (In_batch_cells Tq _) (ex_intro _ i' (ex_intro _ b (conj Hi' (or_introl eq_refl)))))) as C.
pose proof (cell_holds_val_mem B ly H0 mu (batch_exp b) 8 (next_exp Tq i') C) as V. cbn [aeval] in V. rewrite <- EN in V.
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with (aeval B ly (next_exp (G ++ Tq) i)) by (unfold next_exp; destruct (nth_error (G ++ Tq) (S i)); reflexivity).
apply (VMQ _ 8%nat); [|apply VMOF; [intros j Hj; unfold AFer.addr; apply BFX; [exact INb | unfold kBatchBytes; lia] | exact V]].
intros j Hj. apply NW; [lia|]. intros lb initr Hrev. left.
destruct (AFev.glast_facts B ly X W regs mu md PRE_u lb initr Hrev) as (_ & _ & _). assert (EGr : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
rewrite EGr, map_app, map_app in ND. cbn [map] in ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & _ & N3).
intros E. apply (N3 (b_self b)); [apply in_app_iff; left; apply in_map; eapply nth_error_In; exact Hi' | left; symmetry; exact E].
+   unfold next_addr. change (AFer.L X) with (G ++ Tq). fold (next_exp (G ++ Tq) i).
pose proof (proj1 (Forall_forall _ _) OG _ (proj2 (In_batch_cells G _) (ex_intro _ i' (ex_intro _ b (conj Hi' (or_introl eq_refl)))))) as C.
pose proof (cell_holds_val_mem B ly H0 mu (batch_exp b) 8 (next_exp G i') C) as V. cbn [aeval] in V. rewrite <- EN in V.
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with (aeval B ly (next_exp (G ++ Tq) i)) by (unfold next_exp; destruct (nth_error (G ++ Tq) (S i)); reflexivity).
apply (VMQ _ 8%nat); [|apply VMOF; [intros j Hj; unfold AFer.addr; apply BFX; [exact INb | unfold kBatchBytes; lia] | exact V]].
intros j Hj. apply NW; [lia|]. intros lb initr Hrev. left.
assert (EGr : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
rewrite EGr, map_app, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (_ & N2 & _). apply NoDup_app_iff in N2 as (_ & _ & N4).
rewrite EGr in Hi', Si. rewrite length_app in Si. cbn [length] in Si. rewrite nth_error_app1 in Hi' by lia.
intros E. apply (N4 (b_self b)); [apply in_map; eapply nth_error_In; exact Hi' | left; symmetry; exact E].
+   unfold next_addr. change (AFer.L X) with (G ++ Tq).
destruct (AFev.glast_facts B ly X W regs mu md PRE_u b initr Hrev) as (_ & EQ & _).
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with TFv.
2:{ unfold AFgj.TFv. rewrite nth_error_app2 by lia. rewrite Sj, Nat.sub_diag. destruct Tq; reflexivity. }
unfold AFer.addr. rewrite <- EQ. exact (CGL b initr Hrev).
-
assert (C : cell_holds B ly rd0 (z8 (aoff (batch_exp b) 8) (b_bytes b))).
{ unfold all_batches in INb. apply in_app_iff in INb as [INb'|INb'].
- apply In_nth_error in INb' as [i' Hi']. apply (proj1 (Forall_forall _ _) OT). apply In_batch_cells. exists i', b. split; [exact Hi'|]. right. left. reflexivity.
- apply In_nth_error in INb' as [i' Hi']. apply (proj1 (Forall_forall _ _) OG). apply In_batch_cells. exists i', b. split; [exact Hi'|]. right. left. reflexivity. }
pose proof (cell_holds_val_mem B ly H0 mu _ 8 (ANum (b_bytes b)) C) as V. cbn [aeval aoff batch_exp] in V.
replace (SB + (b_self b + 8)) with (addr b + 8) in V by (unfold AFer.addr; lia).
apply (VMQ _ 8%nat); [|apply VMOF; [intros j Hj; unfold AFer.addr; replace (SB + b_self b + 8 + j) with (SB + b_self b + (8 + j)) by lia;
apply BFX; [exact INb | unfold kBatchBytes; lia] | exact V]].
intros j Hj. replace (addr b + 8 + j) with (addr b + (8 + j)) by lia. apply NW; [lia|]. intros; right; lia. }
unfold AFer.sp1, LFRAME. fold sp0.
split; [replace (sp0 - 80 + 8) with (sp0 - 72) by lia; exact Cs72|]. split; [replace (sp0 - 80 + 24) with (sp0 - 56) by lia; exact Cs56|].
split; [replace (sp0 - 80 + 32) with (sp0 - 48) by lia; exact Cs48|]. split; [replace (sp0 - 80 + 40) with (sp0 - 40) by lia; exact Cs40|].
split; [replace (sp0 - 80 + 48) with (sp0 - 32) by lia; exact Cs32|]. split; [replace (sp0 - 80 + 56) with (sp0 - 24) by lia; exact Cs24|].
split; [replace (sp0 - 80 + 64) with (sp0 - 16) by lia; exact Cs16|]. replace (sp0 - 80 + 72) with (sp0 - 8) by lia; exact Cs8.
Qed.
(* The loop (AFer.v) on the real memory: the glue whose frame is against mem (LST_cont, LST_exit, ITER_step, LOOP) is
   the donor text; the facts and FHL_ok are the donor's, applied at mu. *)
Section e.
Variables (P1 R' : list batch) (b : batch) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Hypothesis HL : L = P1 ++ b :: R'.
Let R : list batch := b :: R'.
Hypothesis Q2 : YK11.getr regs' 2 = w64 sp1.
Hypothesis Q10 : YK11.getr regs' 10 = w64 A_QUAR.
Hypothesis Q11 : YK11.getr regs' 11 = w64 kQuarantineMin.
Hypothesis Q12 : YK11.getr regs' 12 = w64 (T + t_cache).
Hypothesis Q14 : YK11.getr regs' 14 = w64 (zlen P1).
Hypothesis Q15 : YK11.getr regs' 15 = w64 (lastaddr P1).
Hypothesis Q16 : YK11.getr regs' 16 = w64 (zlen R).
Hypothesis Q5 : YK11.getr regs' 5 = w64 (firstaddr R).
Hypothesis Q1 : YK11.getr regs' 1 = YK11.getr regs 1.
Hypothesis QS : forall r : bv 5, In r SREGS -> YK11.getr regs' r = YK11.getr regs r.
Hypothesis FRM : forall x : word, ~ DW P1 (bv_unsigned x) -> mem' x = mem x.
Hypothesis PRS : forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem' a.
Let m := mrestrict H0 mem'.
Hypothesis VQW : val_mem tfibsegs m (A_QUAR + 152) 4 257.
Hypothesis VQS : val_mem tfibsegs m (A_QUAR + 160) 8 (zlen R).
Hypothesis VQF : val_mem tfibsegs m (A_QUAR + 168) 8 (firstaddr R).
Hypothesis VQL : val_mem tfibsegs m (A_QUAR + 176) 8 TLv.
Hypothesis VQB : val_mem tfibsegs m (A_QUAR + 184) 8 (sum_bytes R).
Hypothesis VRL : forall i b2, nth_error R i = Some b2 -> val_mem tfibsegs m (addr b2) 8 (next_addr ly R i) /\ val_mem tfibsegs m (addr b2 + 8) 8 (b_bytes b2).
Hypothesis VPL : forall i b2, nth_error P1 i = Some b2 -> val_mem tfibsegs m (addr b2) 8 (next_addr ly P1 i).
Hypothesis VT8 : val_mem tfibsegs m (sp1 + 8) 8 (firstaddr P1).
Hypothesis VT24 : val_mem tfibsegs m (sp1 + 24) 8 (sum_bytes P1).
Hypothesis Q13 : YK11.getr regs' 13 = YK11.getr regs 13.
Hypothesis VQ0 : val_mem tfibsegs m (T + t_qc) 8 0.
Hypothesis VQ8 : val_mem tfibsegs m (T + t_qc + 8) 8 0.
Hypothesis VQ16 : val_mem tfibsegs m (T + t_qc + 16) 8 0.
Hypothesis VQ24 : val_mem tfibsegs m (T + t_qc + 24) 8 0.
Hypothesis VG : (length P1 < length G)%nat -> forall lb initr, rev G = lb :: initr -> val_mem tfibsegs m (addr lb) 8 TFv.
Hypothesis VS32 : val_mem tfibsegs m (sp1 + 32) 8 (bv_unsigned (YK11.getr regs 20)).
Hypothesis VS40 : val_mem tfibsegs m (sp1 + 40) 8 (bv_unsigned (YK11.getr regs 19)).
Hypothesis VS48 : val_mem tfibsegs m (sp1 + 48) 8 (bv_unsigned (YK11.getr regs 18)).
Hypothesis VS56 : val_mem tfibsegs m (sp1 + 56) 8 (bv_unsigned (YK11.getr regs 9)).
Hypothesis VS64 : val_mem tfibsegs m (sp1 + 64) 8 (bv_unsigned (YK11.getr regs 8)).
Hypothesis VS72 : val_mem tfibsegs m (sp1 + 72) 8 (bv_unsigned (YK11.getr regs 1)).
Local Notation pb := (AFer.pb ly b).
Local Notation pnx := (AFer.pnx ly R').
Local Notation pbs := (AFer.pbs b).
Local Notation pqb := (AFer.pqb R' b).
Local Notation pnr := (AFer.pnr R' b).
Local Notation pnp := (AFer.pnp P1).
Local Notation plp := (AFer.plp ly P1).
Local Notation ptby := (AFer.ptby P1).
Local Notation ptfi := (AFer.ptfi ly P1).
Local Notation pgl := (AFer.pgl ly X).
Hypothesis Q4 : YK11.getr regs' 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Local Notation WINL := (AFgl.WIN regs' pb pnp plp).
Lemma InL_b : In b L. Proof. rewrite HL. apply in_app_iff. right. left. reflexivity. Qed.
Lemma InL_P1 : forall b2, In b2 P1 -> In b2 L. Proof. intros b2 Hb2. rewrite HL. apply in_app_iff. left. exact Hb2. Qed.
Lemma InL_R' : forall b2, In b2 R' -> In b2 L. Proof. intros b2 Hb2. rewrite HL. apply in_app_iff. right. right. exact Hb2. Qed.
Lemma Usp1 : kHighMemBeg + DRSTACK <= sp1 /\ sp1 + LFRAME <= kHighMemEnd /\ ly_stk_lo ly + DRSTACK <= sp1 /\ sp1 + LFRAME <= ly_stk_hi ly /\ 0 <= sp1 < 2 ^ 64.
Proof. eapply AFer.Usp1; eassumption. Qed.
Lemma b_facts : ly_prim ly <= pb /\ pb + kBatchBytes <= SB + kSpaceSize /\ pb mod 8192 = 0 /\ kHighMemBeg <= pb /\ pb + kBatchBytes <= ASAN_CEIL /\ kBatchBytes <= pbs /\ pbs <= pqb /\ pqb <= sum_bytes L.
Proof. eapply AFer.b_facts; eassumption. Qed.
Lemma lp_facts : 0 <= plp < ASAN_CEIL /\ plp mod 8192 = 0 /\
(pnp <> 0 -> exists lb ini, rev P1 = lb :: ini /\ plp = addr lb /\ ly_prim ly <= plp /\ plp + kBatchBytes <= SB + kSpaceSize /\ (plp + kBatchBytes <= pb \/ pb + kBatchBytes <= plp) /\ In lb P1).
Proof. eapply AFer.lp_facts; eassumption. Qed.
Lemma ND3 : (forall x, In x P1 -> b_self x <> b_self b) /\ (forall y, In y R' -> b_self y <> b_self b) /\
(forall x y, In x P1 -> In y R' -> b_self x <> b_self y) /\ List.NoDup (map b_self P1) /\ List.NoDup (map b_self R').
Proof. eapply AFer.ND3; eassumption. Qed.
Lemma NW_T : forall k, 0 <= k < 32 -> ~ WINL (T + t_qc + k).
Proof. intros k Hk. eapply AFer.NW_T; eassumption. Qed.
Lemma NW_S : forall k, 32 <= k < 80 -> ~ WINL (sp1 + k).
Proof. intros k Hk. eapply AFer.NW_S; eassumption. Qed.
Lemma NW_batch : forall b2 k, In b2 L -> b_self b2 <> b_self b -> (forall lb ini, rev P1 = lb :: ini -> b_self b2 <> b_self lb) ->
0 <= k < kBatchBytes -> ~ WINL (addr b2 + k).
Proof. intros b2 k H1 H2 H3 H4. eapply AFer.NW_batch; eassumption. Qed.
Lemma WINL_dec : forall a, WINL a \/ ~ WINL a.
Proof. intros a. eapply AFer.WINL_dec; eassumption. Qed.
Lemma keep : forall mem'' a (n : nat) v, (forall x : word, ~ WINL (bv_unsigned x) -> mem'' x = mem' x) ->
(forall i, 0 <= i < Z.of_nat n -> ~ WINL (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfibsegs m a n v -> val_mem tfibsegs (mrestrict H0 mem'') a n v.
Proof. intros mem2 a n v HM Hn Hv. eapply AFer.keep; eassumption. Qed.
Lemma DW_mono : forall a, DW P1 a -> DW (P1 ++ [b]) a.
Proof. intros a H. eapply AFer.DW_mono; eassumption. Qed.
Lemma WINL_DW : forall a, WINL a -> DW (P1 ++ [b]) a.
Proof. intros a H. eapply AFer.WINL_DW; eassumption. Qed.
Lemma zlen_snoc : zlen (P1 ++ [b]) = pnp + 1.
Proof. eapply AFer.zlen_snoc; eassumption. Qed.
Lemma lastaddr_snoc : lastaddr (P1 ++ [b]) = pb.
Proof. eapply AFer.lastaddr_snoc; eassumption. Qed.
Lemma firstaddr_snoc : firstaddr (P1 ++ [b]) = AFgl.TFIn pb pnp ptfi.
Proof. eapply AFer.firstaddr_snoc; eassumption. Qed.
Lemma sum_snoc : sum_bytes (P1 ++ [b]) = ptby + pbs.
Proof. eapply AFer.sum_snoc; eassumption. Qed.
Lemma zlen_R' : zlen R' = pnr - 1.
Proof. eapply AFer.zlen_R'; eassumption. Qed.
Lemma sum_R' : sum_bytes R' = pqb - pbs.
Proof. eapply AFer.sum_R'; eassumption. Qed.
Lemma R'_ne : kQuarantineMin < pqb - pbs -> R' <> [].
Proof. intros H. eapply AFer.R'_ne; eassumption. Qed.
Lemma GLn_cont : R' <> [] -> AFgl.GLn pnx pgl = TLv.
Proof. intros H. eapply AFer.GLn_cont; eassumption. Qed.
Lemma GLn_exit : AFgl.GLn pnx pgl = lastaddr R'.
Proof. eapply AFer.GLn_exit; eassumption. Qed.
Lemma FHL_ok : AFgl.free_hyps W ly regs' mem' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl.
Proof. eapply AFer.FHL_ok; eassumption. Qed.
Lemma LST_cont : forall W' c', AFgl.at_CONT W regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl W' c' -> LST (P1 ++ [b]) R' W' c'.
Proof.
intros W' c' (-> & HLT & regs2 & mem2 & mat2 & -> & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R5 & R1 & RS & MQ & PRES2 & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C153 & C154 & C160 & C168 & C176 & C184 & Cb & Clp & Ct8 & Ct24).
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & _). pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2).
pose proof ND3 as (D1 & D2 & D3 & D4 & D5). pose proof (R'_ne HLT) as RNE.
split; [reflexivity|]. exists regs2, mem2, mat2. split; [reflexivity|].
split; [rewrite R2; exact Q2|]. split; [exact R10|]. split; [exact R11|]. split; [rewrite R12; exact Q12|]. split; [rewrite R13; exact Q13|].
split; [rewrite R14, zlen_snoc; reflexivity|]. split; [rewrite R15, lastaddr_snoc; reflexivity|]. split; [rewrite R16, zlen_R'; reflexivity|].
split; [rewrite R5; reflexivity|]. split; [rewrite R1; exact Q1|]. split; [intros r Hr; rewrite (RS r Hr); apply QS; exact Hr|].
split. { intros x Hx. rewrite (MQ x ltac:(intros Hw; exact (Hx (WINL_DW _ Hw)))). apply FRM. intros HD. exact (Hx (DW_mono _ HD)). }
split. { intros a Ha. destruct (WINL_dec a) as [Hw|Hw].
- apply PRES2; [exact Hw|]. pose proof HSP as [S1 S2]. fold sp0 in S1, S2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *. lia.
- pose proof HSP as [S1 S2]. fold sp0 in S1, S2. apply (apresent_same H0 mem'); [apply MQ; rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; lia); exact Hw | apply PRS; exact Ha]. }
cbv zeta.
split. { apply (proj2 (val_mem4_bytes _ _ _)). change (YO0f.le_byte 257 4 0) with 1. change (YO0f.le_byte 257 4 1) with 1. change (YO0f.le_byte 257 4 2) with 0. change (YO0f.le_byte 257 4 3) with 0.
pose proof (proj1 (val_mem1_byte _ _ _) C152) as E0. pose proof (proj1 (val_mem1_byte _ _ _) C153) as E1'.
splits; [exact E0 | replace (A_QUAR + 152 + 1) with (A_QUAR + 153) by lia; exact E1' | apply C154; lia | apply C154; lia]. }
split; [rewrite zlen_R'; exact C160|]. split; [exact C168|]. split; [rewrite <- (GLn_cont RNE); exact C176|]. split; [rewrite sum_R'; exact C184|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ0]|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 8 + i) with (T + t_qc + (8 + i)) by lia; apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ8]|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 16 + i) with (T + t_qc + (16 + i)) by lia; apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ16]|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 24 + i) with (T + t_qc + (24 + i)) by lia; apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ24]|].
split. {
intros LT lb initr Hrev. rewrite length_app in LT. cbn [length] in LT.
destruct (AFev.glast_facts B ly X W regs mu md PRE_u lb initr Hrev) as (INlb & _ & L1 & L2 & _).
assert (EG : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
assert (INR : In lb R').
{ assert (NL : nth_error L (length (rev initr)) = Some lb) by (unfold L; rewrite EG, <- app_assoc; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
rewrite HL in NL. rewrite nth_error_app2 in NL by (rewrite EG, length_app in LT; cbn [length] in LT; lia).
destruct (length (rev initr) - length P1)%nat as [|k] eqn:EK; [rewrite EG, length_app in LT; cbn [length] in LT; lia|]. cbn [nth_error] in NL. eapply nth_error_In. exact NL. }
destruct (batch_facts lb INlb) as (_ & _ & _ & L4 & L5 & _).
apply (keep _ _ _ _ MQ); [| exact (VG ltac:(lia) lb initr Hrev)]. intros i Hi. split; [apply (NW_batch lb i (proj2 (L_all _) INlb) (D2 _ INR)); [|unfold kBatchBytes; lia] | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
intros lb' ini' ER E. apply (D3 lb' lb); [rewrite <- (rev_involutive P1), ER; cbn; apply in_app_iff; right; left; reflexivity | exact INR | symmetry; exact E]. }
split. {
intros i b2 Hi. destruct (Nat.lt_ge_cases i (length P1)) as [LT|GE].
- rewrite nth_error_app1 in Hi by exact LT. pose proof (nth_error_In _ _ Hi) as IN1.
destruct (Nat.eq_dec (S i) (length P1)) as [LAST|NL].
+
assert (NE0 : pnp <> 0) by (unfold AFer.pnp, AFer.zlen; lia). pose proof lp_facts as (_ & _ & P3a). destruct (P3a NE0) as (lb & ini & ER & EL & _ & _ & _ & _).
assert (EP1 : P1 = rev ini ++ [lb]) by (rewrite <- (rev_involutive P1), ER; reflexivity).
assert (Eb2 : b2 = lb). { rewrite EP1 in Hi. rewrite nth_error_app2 in Hi by (rewrite EP1, length_app in LAST; cbn [length] in LAST; lia).
replace (i - length (rev ini))%nat with 0%nat in Hi by (rewrite EP1, length_app in LAST; cbn [length] in LAST; lia). cbn in Hi. congruence. }
subst b2. unfold next_addr. rewrite nth_error_app2 by lia. rewrite <- LAST, Nat.sub_diag. cbn [nth_error]. fold (addr b). fold pb. rewrite <- EL. exact (Clp NE0).
+
unfold next_addr. rewrite nth_error_app1 by lia. pose proof (VPL i b2 Hi) as V. unfold next_addr in V.
destruct (batch_facts b2 (proj1 (L_all _) (InL_P1 _ IN1))) as (_ & _ & _ & L4 & L5 & _).
apply (keep _ _ _ _ MQ); [| exact V]. intros j Hj. split; [apply (NW_batch b2 j (InL_P1 _ IN1) (D1 _ IN1)); [|unfold kBatchBytes; lia] | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
intros lb ini ER E. assert (EP1 : P1 = rev ini ++ [lb]) by (rewrite <- (rev_involutive P1), ER; reflexivity).
pose proof D4 as ND. rewrite EP1, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (_ & _ & ND). apply (ND (b_self b2)); [|left; symmetry; exact E].
apply in_map. rewrite EP1 in Hi. rewrite nth_error_app1 in Hi by (rewrite EP1, length_app in NL, LT; cbn [length] in NL, LT; lia). eapply nth_error_In. exact Hi.
-
rewrite nth_error_app2 in Hi by exact GE. destruct (i - length P1)%nat as [|k] eqn:EK; [|cbn in Hi; destruct k; discriminate]. cbn in Hi. injection Hi as <-.
unfold next_addr. rewrite nth_error_app2 by lia. replace (S i - length P1)%nat with 1%nat by lia. cbn [nth_error]. exact Cb. }
split. {
intros i b2 Hi. pose proof (nth_error_In _ _ Hi) as IN2. destruct (VRL (S i) b2 Hi) as [V1 V2].
assert (EN : next_addr ly R (S i) = next_addr ly R' i) by reflexivity. rewrite EN in V1.
destruct (batch_facts b2 (proj1 (L_all _) (InL_R' _ IN2))) as (_ & _ & _ & L4 & L5 & _).
assert (NWb : forall j, 0 <= j < 16 -> ~ WINL (addr b2 + j) /\ 0 <= addr b2 + j < 2 ^ 64).
{ intros j Hj. split; [apply (NW_batch b2 j (InL_R' _ IN2) (D2 _ IN2)); [|unfold kBatchBytes; lia] | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
intros lb ini ER E. apply (D3 lb b2); [rewrite <- (rev_involutive P1), ER; cbn; apply in_app_iff; right; left; reflexivity | exact IN2 | symmetry; exact E]. }
split; [apply (keep _ _ _ _ MQ); [intros j Hj; apply NWb; lia | exact V1] | apply (keep _ _ _ _ MQ); [intros j Hj; replace (addr b2 + 8 + j) with (addr b2 + (8 + j)) by lia; apply NWb; lia | exact V2]]. }
split; [rewrite firstaddr_snoc; rewrite Q2 in Ct8; unfold w64 in Ct8; rewrite unsigned_lit_small in Ct8 by lia; exact Ct8|].
split; [rewrite sum_snoc; rewrite Q2 in Ct24; unfold w64 in Ct24; rewrite unsigned_lit_small in Ct24 by lia; exact Ct24|].
assert (KS : forall k v, 32 <= k -> k + 8 <= 80 -> val_mem tfibsegs m (sp1 + k) 8 v -> val_mem tfibsegs (mrestrict H0 mem2) (sp1 + k) 8 v).
{ intros k v Hk1 Hk2 V. apply (keep _ _ _ _ MQ); [|exact V]. intros i Hi. split; [replace (sp1 + k + i) with (sp1 + (k + i)) by lia; apply NW_S; lia | unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DRSTACK, LFRAME, kHighMemBeg, kHighMemEnd in *; lia]. }
splits; (apply KS; [lia | lia | assumption]).
Qed.
Lemma LST_exit : forall W' c', AFgl.at_EXIT W regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl W' c' -> ATDR (P1 ++ [b]) R' W' c'.
Proof.
intros W' c' (-> & HLE & regs2 & mem2 & mat2 & -> & R2 & R10 & R11 & R12 & R13 & R1 & RS & MQ & PRES2 & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cb & Clp & Ct0 & Ct8 & Ct16 & Ct24).
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & _). pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2).
pose proof ND3 as (D1 & D2 & D3 & D4 & D5).
split; [reflexivity|]. exists regs2, mem2, mat2. split; [reflexivity|].
split; [rewrite R2; exact Q2|]. split; [exact R10|]. split; [rewrite R11; exact Q2|]. split; [rewrite R12; exact Q12|]. split; [rewrite R13; exact Q13|].
split; [exact R1|]. split; [intros r Hr; rewrite (RS r Hr); apply QS; exact Hr|].
split. { intros x Hx. rewrite (MQ x ltac:(intros Hw; exact (Hx (WINL_DW _ Hw)))). apply FRM. intros HD. exact (Hx (DW_mono _ HD)). }
split. { intros a Ha. destruct (WINL_dec a) as [Hw|Hw].
- apply PRES2; [exact Hw|]. pose proof HSP as [S1 S2]. fold sp0 in S1, S2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *. lia.
- pose proof HSP as [S1 S2]. fold sp0 in S1, S2. apply (apresent_same H0 mem'); [apply MQ; rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; lia); exact Hw | apply PRS; exact Ha]. }
cbv zeta.
split; [exact C152|].
split; [rewrite zlen_R'; exact C160|]. split; [exact C168|]. split; [rewrite <- GLn_exit; exact C176|]. split; [rewrite sum_R'; exact C184|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ0]|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 8 + i) with (T + t_qc + (8 + i)) by lia; apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ8]|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 16 + i) with (T + t_qc + (16 + i)) by lia; apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ16]|].
split; [apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 24 + i) with (T + t_qc + (24 + i)) by lia; apply NW_T; lia | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia] | exact VQ24]|].
split. { intros LT lb initr Hrev. rewrite length_app in LT. cbn [length] in LT.
destruct (AFev.glast_facts B ly X W regs mu md PRE_u lb initr Hrev) as (INlb & _ & L1 & L2 & _).
assert (EG : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
assert (INR : In lb R').
{ assert (NL : nth_error L (length (rev initr)) = Some lb) by (unfold L; rewrite EG, <- app_assoc; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
rewrite HL in NL. rewrite nth_error_app2 in NL by (rewrite EG, length_app in LT; cbn [length] in LT; lia).
destruct (length (rev initr) - length P1)%nat as [|k] eqn:EK; [rewrite EG, length_app in LT; cbn [length] in LT; lia|]. cbn [nth_error] in NL. eapply nth_error_In. exact NL. }
destruct (batch_facts lb INlb) as (_ & _ & _ & L4 & L5 & _).
apply (keep _ _ _ _ MQ); [| exact (VG ltac:(lia) lb initr Hrev)]. intros i Hi. split; [apply (NW_batch lb i (proj2 (L_all _) INlb) (D2 _ INR)); [|unfold kBatchBytes; lia] | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
intros lb' ini' ER E. apply (D3 lb' lb); [rewrite <- (rev_involutive P1), ER; cbn; apply in_app_iff; right; left; reflexivity | exact INR | symmetry; exact E]. }
split. { intros i b2 Hi. destruct (Nat.lt_ge_cases i (length P1)) as [LT|GE].
- rewrite nth_error_app1 in Hi by exact LT. pose proof (nth_error_In _ _ Hi) as IN1.
destruct (Nat.eq_dec (S i) (length P1)) as [LAST|NL].
+ assert (NE0 : pnp <> 0) by (unfold AFer.pnp, AFer.zlen; lia). pose proof lp_facts as (_ & _ & P3a). destruct (P3a NE0) as (lb & ini & ER & EL & _ & _ & _ & _).
assert (EP1 : P1 = rev ini ++ [lb]) by (rewrite <- (rev_involutive P1), ER; reflexivity).
assert (Eb2 : b2 = lb). { rewrite EP1 in Hi. rewrite nth_error_app2 in Hi by (rewrite EP1, length_app in LAST; cbn [length] in LAST; lia).
replace (i - length (rev ini))%nat with 0%nat in Hi by (rewrite EP1, length_app in LAST; cbn [length] in LAST; lia). cbn in Hi. congruence. }
subst b2. unfold next_addr. rewrite nth_error_app2 by lia. rewrite <- LAST, Nat.sub_diag. cbn [nth_error]. fold (addr b). fold pb. rewrite <- EL. exact (Clp NE0).
+ unfold next_addr. rewrite nth_error_app1 by lia. pose proof (VPL i b2 Hi) as V. unfold next_addr in V.
destruct (batch_facts b2 (proj1 (L_all _) (InL_P1 _ IN1))) as (_ & _ & _ & L4 & L5 & _).
apply (keep _ _ _ _ MQ); [| exact V]. intros j Hj. split; [apply (NW_batch b2 j (InL_P1 _ IN1) (D1 _ IN1)); [|unfold kBatchBytes; lia] | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
intros lb ini ER E. assert (EP1 : P1 = rev ini ++ [lb]) by (rewrite <- (rev_involutive P1), ER; reflexivity).
pose proof D4 as ND. rewrite EP1, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (_ & _ & ND). apply (ND (b_self b2)); [|left; symmetry; exact E].
apply in_map. rewrite EP1 in Hi. rewrite nth_error_app1 in Hi by (rewrite EP1, length_app in NL, LT; cbn [length] in NL, LT; lia). eapply nth_error_In. exact Hi.
- rewrite nth_error_app2 in Hi by exact GE. destruct (i - length P1)%nat as [|k] eqn:EK; [|cbn in Hi; destruct k; discriminate]. cbn in Hi. injection Hi as <-.
unfold next_addr. rewrite nth_error_app2 by lia. replace (S i - length P1)%nat with 1%nat by lia. cbn [nth_error]. exact Cb. }
rewrite Q2 in Ct0, Ct8, Ct16, Ct24. unfold w64 in Ct0, Ct8, Ct16, Ct24. rewrite unsigned_lit_small in Ct0, Ct8, Ct16, Ct24 by lia.
split; [rewrite zlen_snoc; exact Ct0|]. split; [rewrite firstaddr_snoc; exact Ct8|]. split; [rewrite lastaddr_snoc; exact Ct16|]. split; [rewrite sum_snoc; exact Ct24|].
assert (KS : forall k v, 32 <= k -> k + 8 <= 80 -> val_mem tfibsegs m (sp1 + k) 8 v -> val_mem tfibsegs (mrestrict H0 mem2) (sp1 + k) 8 v).
{ intros k v Hk1 Hk2 V. apply (keep _ _ _ _ MQ); [|exact V]. intros i Hi. split; [replace (sp1 + k + i) with (sp1 + (k + i)) by lia; apply NW_S; lia | unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DRSTACK, LFRAME, kHighMemBeg, kHighMemEnd in *; lia]. }
splits; (apply KS; [lia | lia | assumption]).
Qed.
Theorem ITER_step :
SRr tfibsegs W (mkCfg (YK11.mkst regs' (w64 0x33da8) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => if kQuarantineMin <? pqb - pbs then LST (P1 ++ [b]) R' W' c' else ATDR (P1 ++ [b]) R' W' c').
Proof.
eapply SRr_mono; [exact (AFh0.segL W ly regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl mat FHL_ok)|].
intros W' c' _ HP. unfold AFgl.postL in HP. destruct (kQuarantineMin <? pqb - pbs); [exact (LST_cont W' c' HP) | exact (LST_exit W' c' HP)].
Qed.
End e.
Theorem LOOPU : forall R P1 fuel W' c',
LST P1 R W' c' -> L = P1 ++ R -> kQuarantineMin < sum_bytes R -> (length R < fuel)%nat ->
SRr tfibsegs W' c' (fun W'' c'' => let gp := pop_batches fuel (mkQC R (sum_bytes R)) (rev P1) in ATDR (snd gp) (qc_list (fst gp)) W'' c'').
Proof.
induction R as [|b R' IH]; intros P1 fuel W' c' HLST HL HGT Hfuel.
- exfalso. cbn in HGT. unfold kQuarantineMin in HGT. lia.
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. rewrite (AFer.pop_step regs f b R' _ _ HGT).
pose proof PRE_u as PRE'. destruct PRE' as (_ & _ & _ & Hra & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
destruct HLST as (-> & regs' & mem' & mat & -> & Q2 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q5 & Q1 & QS & FRM & PRS & CELLS).
cbv zeta in CELLS. destruct CELLS as (VQW & VQS & VQF & VQL & VQB & VQ0 & VQ8 & VQ16 & VQ24 & VG & VPL & VRL & VT8 & VT24 & VS32 & VS40 & VS48 & VS56 & VS64 & VS72).
assert (Q4 : YK11.getr regs' 4 = w64 TFIB_TP) by (rewrite (QS 4%bv ltac:(cbn; tauto)); exact Htp).
pose proof (ITER_step P1 R' b regs' mem' mat) as STEP.
repeat match type of STEP with ?A -> _ => let h := fresh "h" in assert (h : A) by assumption; specialize (STEP h); clear h end.
unfold AFer.pqb, AFer.pbs in STEP. rewrite sum_bytes_cons in STEP |- *. replace (b_bytes b + sum_bytes R' - b_bytes b) with (sum_bytes R') in STEP |- * by lia.
destruct (Z.ltb_spec kQuarantineMin (sum_bytes R')) as [GT|LE].
+
eapply SRr_bind; [exact STEP|]. intros W2 c2 _ HL2. cbn beta in HL2.
pose proof (IH (P1 ++ [b]) f W2 c2 HL2 ltac:(rewrite <- app_assoc; exact HL) GT ltac:(cbn in Hfuel; lia)) as K.
rewrite AFer.rev_last in K. exact K.
+
rewrite (AFer.pop_stop regs f R' _ _ LE). cbn [fst snd qc_list rev]. rewrite rev_involutive. exact STEP.
Qed.
(* After do_recycle (AFet.v EPI): the epilogue walk runs on the real memory; the leaf is the donor text at mu. The raw
   frame composes the loop's run frame on the real memory (ATDR_u) with do_recycle's raw leaf; the epilogue writes none. *)
Lemma EPIU : forall P R regs2 mem2r mat r W6 c6,
L = P ++ R ->
YK11.getr regs2 2 = w64 sp1 -> YK11.getr regs2 1 = w64 0x33e1c -> (forall r5 : bv 5, In r5 AFer.SREGS -> YK11.getr regs2 r5 = YK11.getr regs r5) ->
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 (FSP.unpoison UP mem2r) a) ->
(let m := mrestrict H0 (FSP.unpoison UP mem2r) in
val_mem tfibsegs m (sp1 + 32) 8 (bv_unsigned (YK11.getr regs 20)) /\ val_mem tfibsegs m (sp1 + 40) 8 (bv_unsigned (YK11.getr regs 19)) /\
val_mem tfibsegs m (sp1 + 48) 8 (bv_unsigned (YK11.getr regs 18)) /\ val_mem tfibsegs m (sp1 + 56) 8 (bv_unsigned (YK11.getr regs 9)) /\
val_mem tfibsegs m (sp1 + 64) 8 (bv_unsigned (YK11.getr regs 8)) /\ val_mem tfibsegs m (sp1 + 72) 8 (bv_unsigned (YK11.getr regs 1))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X P sp0 a -> aview tfibsegs H0 (FSP.unpoison UP mem2r) a = rd0 a) ->
AR tfibsegs B ly (AFey.S' X P R) W (FSP.unpoison UP mem2r) (with_vm_backing (m_vm_lazy md) mat md) ->
(forall x : word, ~ DW P (bv_unsigned x) -> mem2r x = mem x) ->
FK.dr_leafU B ly (AFey.S' X P R) UP W regs2 mem2r (with_vm_backing (m_vm_lazy md) mat md) r W6 c6 ->
SRr tfibsegs W6 c6 (FK.drain_leafU B ly X UP W regs mem md r).
Proof.
intros P R regs2 mem2r mat [ru X3] W6 c6 HL R2 R1 CS PRS2 SLOTS AG2 AR2 MQ2 HDL. set (mem2 := FSP.unpoison UP mem2r) in *. cbv zeta in SLOTS. destruct SLOTS as (Cs32 & Cs40 & Cs48 & Cs56 & Cs64 & Cs72).
pose proof PRE_u as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
assert (Usp1 : 0 <= sp1 < 2 ^ 64) by (unfold AFer.sp1, LFRAME; fold sp0; clear - Usp HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia).
assert (SP1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; rewrite unsigned_lit_small by exact Usp1; reflexivity).
destruct HDL as (regs3 & mem3r & md3 & -> & ((AR3 & LLE & WLE & CS3 & SIO & FR3 & PRS3) & OK3 & PO3) & PRE3 & RAW3).
set (mem3 := FSP.unpoison UP mem3r) in *. cbn [fst snd] in *.
unfold spZ, raZ, ascratch in FR3, PRS3, PRE3. rewrite R2, SP1 in FR3, PRS3, PRE3. unfold spZ in FR3. rewrite R2, SP1 in FR3.
unfold ascratch in RAW3. unfold spZ in RAW3. rewrite R2, SP1 in RAW3.
(* The raw frame of the drain: do_recycle's raw leaf at sp1 (AFey.S' owns what X owns, aowned_same_cf; its scratch and
   its E lie in the drain's stack window), then the loop's run frame (window DW P, owned or on the stack: DW_own). *)
assert (RAWD : forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly X3 (bv_unsigned x) ->
  ~ ascratch B DSTACK regs (bv_unsigned x) -> ~ False -> mem3r x = mem x).
{ intros x NO NO3 NS _. unfold ascratch, spZ in NS. fold sp0 in NS.
  assert (NOS : ~ aowned B ly (AFey.S' X P R) (bv_unsigned x)).
  { intros O. apply NO. exact (aowned_same_cf B ly X _ _ (AFey.S'_chunks X P R) (AFey.S'_fs X P R) O). }
  transitivity (mem2r x).
  - apply RAW3; [exact NOS | exact NO3 | | intros HE; apply NS; left; unfold AFer.sp1, LFRAME in HE; fold sp0 in HE; clear - HE; unfold DSTACK; lia].
    intros [Hs|Hs]; apply NS; [left; unfold AFer.sp1, LFRAME, DRSTACK in Hs; fold sp0 in Hs; clear - Hs; unfold DSTACK; lia | right; exact Hs].
  - apply MQ2. intros HW. destruct (DW_own P R HL (bv_unsigned x) (u64_range x) HW) as [O|O]; [exact (NO O) | apply NS; left; exact O]. }
assert (NOWN : forall a, sp0 - DSTACK <= a < sp0 -> ~ aowned B ly (AFey.S' X P R) a /\ ~ aowned B ly X3 a).
{ intros a Ha. split.
- apply (AR_stack_law_ok tfibsegs B ly _ W mem2 _ a AR2). clear - Ha Hlo Hhi. unfold DSTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X3 W6 mem3 md3 a AR3). clear - Ha Hlo Hhi. unfold DSTACK in *. lia. }
assert (AGS : forall a, sp0 - DSTACK <= a < sp0 -> ~ (sp1 - DRSTACK <= a < sp1 + 32) -> aview tfibsegs (w_H W6) mem3 a = aview tfibsegs H0 mem2 a).
{ intros a Ha Hn. destruct (NOWN a Ha) as [N1 N2]. apply FR3; [clear - Ha Usp hS1 HSP'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia | exact N1 | exact N2 | | clear - Hn; unfold DRSTACK in *; lia].
intros [Hs|Hs]; [clear - Hs Hn; unfold DRSTACK in *; lia|]. rewrite (ts_errno _ TB) in Hs. clear - Hs Ha hS1 HSP'. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, DSTACK, kHighMemBeg in *. lia. }
assert (PRS6 : forall a, sp0 - DSTACK <= a < sp0 -> apresent (w_H W6) mem3 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp1 - DRSTACK)) as [L1|L1]; [|destruct (Z_lt_le_dec a sp1) as [L2|L2]; [apply PRS3; lia | destruct (Z_lt_le_dec a (sp1 + 32)) as [L3|L3]; [apply PRE3; lia|]]].
all: pose proof (PRS2 a Ha) as P0; apply apresent_mbyte in P0 as [b Hb];
assert (A : aview tfibsegs H0 mem2 a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- (AGS a Ha ltac:(lia)) in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W6) mem3 a b' ltac:(clear - Ha Usp hS1 HSP'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, TFIB_IMG_END in *; lia) Hb'). }
set (vra := bv_unsigned (YK11.getr regs 1)). set (vs0 := bv_unsigned (YK11.getr regs 8)). set (vs1 := bv_unsigned (YK11.getr regs 9)).
set (vs2 := bv_unsigned (YK11.getr regs 18)). set (vs3 := bv_unsigned (YK11.getr regs 19)). set (vs4 := bv_unsigned (YK11.getr regs 20)).
assert (CS3' : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> YK11.getr regs3 r = YK11.getr regs2 r) by (intros r5 z Hz <-; exact (CS3 z Hz)).
assert (Q2 : YK11.getr regs3 2 = w64 sp1) by (rewrite (CS3' 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact R2).
assert (Q4 : YK11.getr regs3 4 = w64 TFIB_TP).
{ rewrite (CS3' 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)), (CS 4%bv ltac:(cbn; tauto)), Htp, (ts_tp _ TB). reflexivity. }
assert (XF : forall a (n : nat) v, sp1 + 32 <= a -> a + Z.of_nat n <= sp0 -> val_mem tfibsegs (mrestrict H0 mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W6) mem3) a n v).
{ intros a n v H1 H2 Hv. eapply AFet.val_mem_aview_xfer; [|exact Hv]. intros k Hk. apply AGS; unfold AFer.sp1, LFRAME, DRSTACK in *; fold sp0 in H1 |- *; clear - H1 H2 Hk HSP' hS1; unfold DSTACK in *; lia. }
assert (FHX : AFgt.free_hyps W6 regs3 mem3r vra vs0 vs1 vs2 vs3 vs4).
{ constructor.
- exact Q4.
- subst vra. unfold w64. rewrite Z_to_bv_bv_unsigned. exact Hra.
- rewrite Q2, SP1. unfold AFer.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. lia.
- rewrite Q2, SP1. replace sp1 with (sp0 + (-5) * 16) by (unfold AFer.sp1, LFRAME; fold sp0; lia). rewrite Z_mod_plus_full. exact Hal.
- subst vra vs0 vs1 vs2 vs3 vs4. splits; apply u64_range.
-
rewrite restrict_mkst_fx. unfold AFgt.SS0, AFgt.SR0, sr_set. cbn [bv_eqb]. unfold AFgt.E0, w64. apply (entry_st_ok_full tfibsegs).
+ apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Q4].
+ vm_compute. reflexivity.
+ cbn [ms_mem YK11.mkst]. fold (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). unfold AFgt.REG0, AFgt.R_STK. apply Forall_cons; [|apply Forall_nil].
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (AFgt.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2, SP1. unfold LFRAME.
split; [clear - Usp1; lia|]. split; [unfold AFer.sp1, LFRAME; fold sp0; clear - HSP' hS2; unfold kHighMemEnd in *; lia|]. split; [intros o Ho; lia|].
assert (CA : forall a k0 x, ew (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W6) mem3r) (sp1 + a) (N.to_nat 8) x ->
YP09.chunk_ok tfibsegs (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) (mrestrict (w_H W6) mem3r) sp1 (YP09.mkChunk a (CVal 8 (SOff k0 0)))).
{ intros a k0 x Hk0 Hr Hm. eapply chunk_ok_val; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr | cbn; lia | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia. }
repeat apply Forall_cons; try apply Forall_nil.
* apply (CA 72 32%nat vra); [reflexivity | subst vra; apply u64_range | apply VMOF; [intros k Hk; apply STKF; change (Z.of_nat (N.to_nat 8)) with 8 in Hk; unfold AFer.sp1, LFRAME, DSTACK; lia
  | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs72]]].
* apply (CA 64 33%nat vs0); [reflexivity | subst vs0; apply u64_range | apply VMOF; [intros k Hk; apply STKF; change (Z.of_nat (N.to_nat 8)) with 8 in Hk; unfold AFer.sp1, LFRAME, DSTACK; lia
  | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs64]]].
* apply (CA 56 34%nat vs1); [reflexivity | subst vs1; apply u64_range | apply VMOF; [intros k Hk; apply STKF; change (Z.of_nat (N.to_nat 8)) with 8 in Hk; unfold AFer.sp1, LFRAME, DSTACK; lia
  | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs56]]].
* apply (CA 48 35%nat vs2); [reflexivity | subst vs2; apply u64_range | apply VMOF; [intros k Hk; apply STKF; change (Z.of_nat (N.to_nat 8)) with 8 in Hk; unfold AFer.sp1, LFRAME, DSTACK; lia
  | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs48]]].
* apply (CA 40 36%nat vs3); [reflexivity | subst vs3; apply u64_range | apply VMOF; [intros k Hk; apply STKF; change (Z.of_nat (N.to_nat 8)) with 8 in Hk; unfold AFer.sp1, LFRAME, DSTACK; lia
  | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs40]]].
* apply (CA 32 37%nat vs4); [reflexivity | subst vs4; apply u64_range | apply VMOF; [intros k Hk; apply STKF; change (Z.of_nat (N.to_nat 8)) with 8 in Hk; unfold AFer.sp1, LFRAME, DSTACK; lia
  | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs32]]].
+   cbn [pairwise_disjoint all_disjoint AFgt.REG0]. split; exact I.
+ fold (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). split; [|split; exact I].
assert (AF : forall k0 Xv lo hi al, ew (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (SAL : sp1 mod 16 = 0) by (replace sp1 with (sp0 + (-5) * 16) by (unfold AFer.sp1, LFRAME; fold sp0; lia); rewrite Z_mod_plus_full; exact Hal).
cbn [AFgt.FFX f_atoms atoms_ok].
split. { apply (AF 2%nat sp1); [rewrite (AFgt.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2; reflexivity | exact Usp1 | | change (2 ^ 4) with 16; exact SAL | lia].
unfold AFer.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. lia. }
split. { apply (AF 32%nat vra); [reflexivity | subst vra; apply u64_range | pose proof (u64_range (YK11.getr regs 1)); subst vra; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 33%nat vs0); [reflexivity | subst vs0; apply u64_range | pose proof (u64_range (YK11.getr regs 8)); subst vs0; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 34%nat vs1); [reflexivity | subst vs1; apply u64_range | pose proof (u64_range (YK11.getr regs 9)); subst vs1; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 35%nat vs2); [reflexivity | subst vs2; apply u64_range | pose proof (u64_range (YK11.getr regs 18)); subst vs2; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 36%nat vs3); [reflexivity | subst vs3; apply u64_range | pose proof (u64_range (YK11.getr regs 19)); subst vs3; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split; [|exact I]. { apply (AF 37%nat vs4); [reflexivity | subst vs4; apply u64_range | pose proof (u64_range (YK11.getr regs 20)); subst vs4; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. } }
unfold cfg_at, raZ. rewrite <- (AFet.wvb_self md3) at 1. rewrite R1. unfold w64 at 2. rewrite (unsigned_lit_small 0x33e1c) by (clear; lia).
eapply SRr_mono; [exact (AFh8.segX W6 regs3 mem3r md3 vra vs0 vs1 vs2 vs3 vs4 (m_vm_materialized md3) FHX)|].
intros W7 c7 _ (-> & regs4 & mat4 & -> & T2 & T1 & T8 & T9 & T18 & T19 & T20 & TS).
rewrite Q2, SP1 in T2. unfold LFRAME in T2.
exists regs4, mem3r, (with_vm_backing (m_vm_lazy md3) mat4 md3). split; [subst vra; reflexivity|].
split; [split; [|exact (conj OK3 PO3)] | exact RAWD].
assert (CSx : forall z (r5 : bv 5), Z_to_bv 5 z = r5 -> YK11.getr regs4 r5 = YK11.getr regs r5 -> YK11.getr regs4 (Z_to_bv 5 z) = YK11.getr regs (Z_to_bv 5 z)) by (intros z r5 <- E; exact E).
assert (VIA3 : forall (r5 : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r5 -> In r5 AFgt.SREGS -> In r5 AFer.SREGS -> YK11.getr regs4 r5 = YK11.getr regs r5).
{ intros r5 z Hz Ez I1 I2. rewrite (TS r5 I1), (CS3' r5 z Hz Ez). apply CS. exact I2. }
split; [|split; [apply layout_le_refl | split; [exact WLE | split; [|split; [|split]]]]].
- apply (AFet.AR_model_same B ly X3 W6 mem3 md3); [exact AR3 | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
- intros r Hr. pose proof Hr as Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr'.
repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; subst r.
+ apply (CSx _ 2%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T2. unfold AFer.sp1, LFRAME. fold sp0. replace (sp0 - 80 + 80) with sp0 by lia. unfold sp0, w64. apply Z_to_bv_bv_unsigned.
+ apply (VIA3 3%bv 3 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 4%bv 4 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (CSx _ 8%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T8. subst vs0. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 9%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T9. subst vs1. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 18%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T18. subst vs2. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 19%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T19. subst vs3. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 20%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T20. subst vs4. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (VIA3 21%bv 21 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 22%bv 22 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 23%bv 23 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 24%bv 24 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 25%bv 25 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 26%bv 26 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 27%bv 27 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
- eapply AFet.same_io_trans; [apply AFet.same_io_with_vm_backing|]. eapply AFet.same_io_trans; [exact SIO | apply AFet.same_io_with_vm_backing].
-
intros a Ha NO NO3 NS NF. unfold ascratch, spZ in NS. fold sp0 in NS.
assert (NOS : ~ aowned B ly (AFey.S' X P R) a).
{ intros O. apply NO. exact (aowned_same_cf B ly X _ a (AFey.S'_chunks X P R) (AFey.S'_fs X P R) O). }
transitivity (aview tfibsegs H0 mem2 a).
+ apply FR3; [exact Ha | exact NOS | exact NO3 | | intros HE; apply NS; left; unfold AFer.sp1, LFRAME in HE; fold sp0 in HE; clear - HE; unfold DSTACK; lia].
intros [Hs|Hs]; apply NS; [left; unfold AFer.sp1, LFRAME, DRSTACK in Hs; fold sp0 in Hs; clear - Hs; unfold DSTACK; lia | right; exact Hs].
+ apply AG2; [exact Ha|]. intros HD.
destruct (AFey.D_owned B ly X _ M P R HL sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; left; exact O].
- intros a Ha. apply PRS6. unfold spZ in Ha. exact Ha.
Qed.
(* AFet.v tfib_drain_arm, for any U. *)
Theorem tfib_drain_armU : amreal tfibsegs (drain_body X X) W (cfg_at tfibsegs A_Drain regs mem md) (FK.drain_leafU B ly X UP W regs mem md).
Proof.
pose proof FH_real as FH.
pose proof (AFer.sum_L B ly X W regs mu md PRE_u) as SL. pose proof (AFer.len_L B ly X W regs mu md PRE_u) as LL.
assert (WALK : (kQuarantineMax < qc_bytes gq + qc_bytes tq -> 2 * (kBatchBytes * Z.of_nat (length L)) <= qc_bytes gq + qc_bytes tq) ->
SRr tfibsegs W (cfg_at tfibsegs A_Drain regs mem md) (AFgj.postD W ly regs mem md gq tq)).
{ intros HM. unfold cfg_at, A_Drain. rewrite <- (AFet.wvb_self md) at 1.
assert (HM' : kQuarantineMax < AFgj.LBv gq tq -> 2 * (kBatchBytes * AFgj.LSZv gq tq) <= AFgj.LBv gq tq).
{ unfold AFgj.LBv, AFgj.GBv, AFgj.TBv, AFgj.LSZv, AFgj.GSZv, AFgj.TSZv. intros H1.
unfold AFer.L in HM. rewrite length_app, Nat2Z.inj_add in HM. exact (HM H1). }
destruct G as [|g0 G'] eqn:EG.
- apply (AFgg.segDE W ly regs mem md gq tq (m_vm_materialized md) FH); [exact EG | exact HM'].
- apply (AFgh.segDN W ly regs mem md gq tq (m_vm_materialized md) FH); [rewrite EG; discriminate | exact HM']. }
rewrite AFet.drain_body_unfold. unfold AFgj.postD, AFgj.LBv, AFgj.GBv, AFgj.TBv in WALK.
destruct (Z.leb_spec (qc_bytes gq + qc_bytes tq) kQuarantineMax) as [LE|GT].
-
cbn [amreal ret]. eapply SRr_mono; [exact (WALK ltac:(intros; lia))|]. intros W' c' _ HR. exact (FIN_aU W' c' HR).
-
unfold recycle_body, mcheck. cbn [qc_list qc_bytes transfer_g].
destruct (Z.leb_spec (2 * (kBatchBytes * Z.of_nat (length (G ++ Tq)))) (qc_bytes gq + qc_bytes tq)) as [MC|MC].
2:{   unfold bind, fail. cbn [ibind amreal]. exact I. }
unfold bind at 1. unfold ret. cbn [ibind].
destruct (pop_batches 100000 (transfer_g X) []) as [g' P] eqn:EP.
pose proof (pop_batches_spec _ _ _ _ _ EP) as (P0 & EP0 & EL & EB). cbn [rev app] in EP0. subst P0. cbn [transfer_g qc_list qc_bytes] in EL, EB.
assert (LEN : (length (qc_list (transfer_g X)) < 100000)%nat).
{ cbn [transfer_g qc_list]. unfold AFer.zlen, AFer.L, EV_MAX in LL. apply Nat2Z.inj_lt. rewrite of_nat_100000. lia. }
pose proof (pop_batches_stop _ _ _ _ _ EP LEN) as STOP.
destruct g' as [R s]. cbn [qc_list qc_bytes] in EL, EB, STOP.
assert (HL : L = P ++ R) by exact EL.
assert (SR : sum_bytes R <= kQuarantineMax).
{ rewrite HL, sum_bytes_app in SL. destruct STOP as [S1|S1]; [unfold kQuarantineMin, kQuarantineMax in *; lia | subst R; cbn; unfold kQuarantineMax; lia]. }
unfold bind, modify. cbn [ibind].
change (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (AFey.S' X P R) || (replace (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (AFey.S' X P R) by (unfold AFey.S'; cbn [st_qglobal qc_bytes AFey.XT set_qglobal]; rewrite EB; reflexivity)).
apply amreal_after_SRr.
eapply SRr_bind; [exact (WALK ltac:(intros _; unfold AFer.L; exact MC))|]. intros W1 c1 _ H1.
pose proof (L0_LSTU W1 c1 H1) as H2.
eapply SRr_bind.
{ apply (LOOPU L [] 100000%nat W1 c1 H2 eq_refl); [rewrite SL; unfold kQuarantineMin, kQuarantineMax in *; lia | exact LEN]. }
intros W2 c2 _ H3. cbn beta zeta in H3. cbn [rev] in H3. rewrite SL in H3. change (AFer.L X) with (G ++ Tq) in H3. unfold transfer_g in EP. rewrite EP in H3. cbn [fst snd qc_list] in H3.
destruct (ATDR_u P R W2 c2 H3 HL) as (regs2 & mem2 & mat & -> & -> & MQ2 & HAu).
destruct (AFet.DRPRE B TB ly X W regs mu md PRE_u P R W _ HAu HL SR) as (regs2' & mem2u & mat' & _ & EC & R2 & R1 & R13 & CS & MQ & PRS & SLOTS & AG & DPRE).
apply FK.cfg_at_inj in EC as (E1 & E2 & E3). subst regs2' mem2u. rewrite <- E3 in DPRE.
assert (PL : forall b2, In b2 P -> In b2 (all_batches X)) by (intros b2 Hb2; apply L_all; rewrite HL; apply in_app_iff; left; exact Hb2).
assert (DPREU : FK.dr_preU B ly (AFey.S' X P R) P UP W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md)).
{ split; [exact DPRE|]. split.
  - apply (FAR.upoison_ok_keep B ly X ly (AFey.S' X P R) UP OK0). intros r p n _ Hb _ _. exact Hb.
  - exact (FK.upoisoned_frame B ly X UP W mem md ARU0 mem2 (DW P) (fun a Ha => FNS a (DW_fixed P a PL Ha)) MQ2). }
apply SRr_ret. eapply amreal_then_SRr; [exact (DRU ly _ P UP W regs2 mem2 _ DPREU)|].
intros r W6 c6 HDL. exact (EPIU P R regs2 mem2 mat r W6 c6 HL R2 R1 CS PRS SLOTS AG (proj1 DPRE) MQ2 HDL).
Qed.
End f.

Theorem tfib_drain_okU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FK.tfib_dorecycle_specU B -> FK.tfib_drain_specU B.
Proof. intros B LAWS TB DR ly X UP W regs mem md PRE. exact (tfib_drain_armU B TB DR ly X UP W regs mem md PRE). Qed.
End dn.

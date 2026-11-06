(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFet.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AFet.v, with its module paths and module names changed; 425 of its 462 lines of code are new or changed and 693 lines of the source are left out. *)
(* The enqueue family of the free walks over ARU (lib/A/AFg4.v room, AFg5.v hit, AFg6.v miss): the seed and post transfers. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The two transfers the method needs, in the only place they touch memory. Seed transfer (unpoison UP mem -> mem):
   the walk-spec records AFgp.free_hyps / AFgq.free_hyps / AFgr.free_hyps hold of the REAL memory, since every byte they
   read and every region of their seed state lies in application memory (stack, thread object, primary reservation,
   image), where UP is not. Post transfer (mem -> unpoison UP mem): the post of each run (AFh3.segP, AFh4.segQH,
   AFh5.segR1, AFh6.segT) on the real final memory gives the same post for the unpoisoned reading, and UP keeps its 0xf7
   bytes, since each run's write window misses the shadow band. FSupoisonAllocFeq.v is the twin itself. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFeqR.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt; the pcs are by name: A_Enqueue, A_Refill, PC_ENQ_RA. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFeq YFew.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFgp YFgq YFgr YFh3 YFh4 YFh5 YFh6.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocFK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* The pcs inside a function, by name: the entry is lib/B/YFeu.v / lib/B/YFew.v A_xxx or the lib/B/YB1w.v row, the offset is the B donor's pc minus that entry. *)
(* the return address of Enqueue's new-batch call (lib/B/YFgr.v:128, SS0's pc; lib/B/YFg6.v:276 R_ra). *)
Definition PC_ENQ_RA : Z := A_Enqueue + 0x154.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFK.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac nums := ceil; unfold kHighMemBeg, kHighMemEnd, SHADOW_OFF, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END, ASAN_CEIL,
  kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kFreeArrayOffset, EV_MAX,
  t_qc, t_cache, t_cache_stats, QSTACK, RSTACK in *.

Section b.
Variable B : asyms.
Variables (ly : alayout) (S : astate) (UP : list (Z * Z)) (W : world tfibsegs) (mem : word -> option byte) (md : Model).
Hypothesis ARU : FSP.ARU tfibsegs B ly S UP W mem md.
Local Notation mu := (FSP.unpoison UP mem).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Where UP is not: application memory. A zone3 extent is below the shadow or above kHighMemBeg, and so is every  *)
(*    byte of it (FSupoisonAllocFK.offU_zone3); the image is below the shadow; the primary reservation and the stack  *)
(*    are above kHighMemBeg.                                                                                         *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Local Notation offU_zone3 := (FK.offU_zone3 B ly S UP W mem md ARU).

Lemma offU_himem : forall a, kHighMemBeg <= a -> a < 2 ^ 64 -> FAR.offU UP a.
Proof. intros a H1 H2. exact (FAR.offU_high B ly S UP W mem md a ARU (conj H1 H2)). Qed.

Lemma offU_imglow : forall a, 0 <= a -> a < SHADOW_OFF -> FAR.offU UP a.
Proof. intros a H1 H2. exact (FAR.offU_low B ly S UP W mem md a ARU (conj H1 H2)). Qed.

Lemma offU_stk : forall a, ly_stk_lo ly <= a -> a < ly_stk_hi ly -> FAR.offU UP a.
Proof. intros a H1 H2. exact (FAR.stack_offU B ly S UP W mem md a ARU (conj H1 H2)). Qed.

(* The same three, byte by byte over a width-w window, as val_mem_of_unpoison / val_mem_to_unpoison want them. *)
Lemma offU_win_zone3 : forall x sz a0 (w : nat), zone3 x sz -> x <= a0 -> a0 + Z.of_nat w <= x + sz ->
  forall kk, (kk < w)%nat -> FAR.offU UP (a0 + Z.of_nat kk).
Proof. intros x sz a0 w Hz H1 H2 kk Hk. apply (offU_zone3 x sz); [exact Hz | lia]. Qed.

Lemma offU_win_high : forall a0 (w : nat), kHighMemBeg <= a0 -> a0 + Z.of_nat w < 2 ^ 64 ->
  forall kk, (kk < w)%nat -> FAR.offU UP (a0 + Z.of_nat kk).
Proof. intros a0 w H1 H2 kk Hk. apply offU_himem; lia. Qed.

(* UP's shadow bytes live in the shadow band, so a run whose write window misses that band keeps them 0xf7. *)
Local Notation upoisoned_frame := (FK.upoisoned_frame B ly S UP W mem md ARU).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The room walk (lib/B/YFgp.v, run lib/B/YFh3.v).                                                                *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma regions_offU_p : forall regs u nn qsz ql qb cnt bsz,
  YFgp.free_hyps W ly regs mu u nn qsz ql qb cnt bsz ->
  FAR.regions_offU UP (YFgp.E0 ly regs u nn qsz ql qb cnt bsz) YFgp.REG0.
Proof.
intros regs u nn qsz ql qb cnt bsz FH.
pose proof (YFgp.derived_ranges W ly regs mu u nn qsz ql qb cnt bsz FH) as DR.
pose proof (YFgp.LYB W ly regs mu u nn qsz ql qb cnt bsz FH) as LB.
pose proof (YFgp.fh_Hsp W ly regs mu u nn qsz ql qb cnt bsz FH) as HSP.
destruct DR as (dU1 & dU2 & dN & dQSZ & dQB1 & dQB2 & dQL1 & dQL2 & dQLal & dCNT & dBSZ1 & dBSZ2 & dSL & dT1 & dT2 & dS1 & dS2).
destruct LB as (ZT & T2 & P1 & P2 & P3 & P4 & K1 & K2 & _).
ceil. intros r a Hr Ha. unfold YFgp.REG0 in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
  unfold YFgp.R_ROOT, YFgp.R_LAST, YFgp.R_SLOT in Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha.
- rewrite (YFgp.E2 ly regs u nn qsz ql qb cnt bsz) in Ha. apply offU_stk; nums; lia.
- rewrite (YFgp.EqT ly regs u nn qsz ql qb cnt bsz) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (ly_T ly) ltac:(nums; lia)) in Ha.
  apply (offU_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia].
- rewrite (YFgp.EqQL ly regs u nn qsz ql qb cnt bsz) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small ql ltac:(nums; lia)) in Ha. apply offU_himem; nums; lia.
- rewrite (YFgp.EqSL ly regs u nn qsz ql qb cnt bsz) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (YFgp.SLv ql cnt) ltac:(nums; lia)) in Ha. apply offU_himem; nums; lia.
Qed.

Lemma FHp_real : forall regs u nn qsz ql qb cnt bsz,
  YFgp.free_hyps W ly regs mu u nn qsz ql qb cnt bsz -> YFgp.free_hyps W ly regs mem u nn qsz ql qb cnt bsz.
Proof.
intros regs u nn qsz ql qb cnt bsz FH.
pose proof (YFgp.derived_ranges W ly regs mu u nn qsz ql qb cnt bsz FH) as DR.
pose proof (YFgp.LYB W ly regs mu u nn qsz ql qb cnt bsz FH) as LB.
pose proof (YFgp.fh_Hsp W ly regs mu u nn qsz ql qb cnt bsz FH) as HSP.
pose proof (YFgp.fh_last W ly regs mu u nn qsz ql qb cnt bsz FH) as HLAST.
pose proof FH as FH'. destruct FH' as [LY Htp Hra Hra4 Hsp Hal Hpres Hu IMG Hnn Hq Hlast SEED].
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQB1 & dQB2 & dQL1 & dQL2 & dQLal & dCNT & dBSZ1 & dBSZ2 & dSL & dT1 & dT2 & dS1 & dS2).
pose proof LB as (ZT & T2 & P1 & P2 & P3 & P4 & K1 & K2 & _).
destruct HLAST as (L1 & L2 & L3 & L4 & L5 & L6 & LP1 & LP2). ceil.
constructor.
- exact LY.
- exact Htp.
- exact Hra.
- exact Hra4.
- exact Hsp.
- exact Hal.
- intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_stk; nums; lia | exact (Hpres a Ha)].
- exact Hu.
- exact IMG.
- exact Hnn.
- exact Hq.
- split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split.
  + intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_himem; nums; lia | exact (LP1 a Ha)].
  + intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_himem; nums; lia | exact (LP2 a Ha)].
- exact (proj1 (FAR.st_ok_unpoison_iff UP (YFgp.E0 ly regs u nn qsz ql qb cnt bsz) YFgp.SS0 (w_H W) regs (w64 A_Enqueue) mem (YK11.seg_rom tfibsegs)
    (regions_offU_p regs u nn qsz ql qb cnt bsz FH)) SEED).
Qed.

Lemma at_RETP_u : forall regs u nn qsz ql qb cnt bsz W' c',
  YFgp.free_hyps W ly regs mu u nn qsz ql qb cnt bsz ->
  YFgp.at_RETP W ly regs mem md u nn ql qb cnt bsz W' c' ->
  exists regs' mem' mat,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    W' = W /\
    YFgp.at_RETP W ly regs mu md u nn ql qb cnt bsz W
      (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    FSP.upoisoned tfibsegs W mem' UP /\
    (forall x : word, ~ YFgp.WIN ly regs ql cnt (bv_unsigned x) -> mem' x = mem x).
Proof.
intros regs u nn qsz ql qb cnt bsz W' c' FH HR.
pose proof (YFgp.derived_ranges W ly regs mu u nn qsz ql qb cnt bsz FH) as DR.
pose proof (YFgp.LYB W ly regs mu u nn qsz ql qb cnt bsz FH) as LB.
pose proof (YFgp.fh_Hsp W ly regs mu u nn qsz ql qb cnt bsz FH) as HSP.
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQB1 & dQB2 & dQL1 & dQL2 & dQLal & dCNT & dBSZ1 & dBSZ2 & dSL & dT1 & dT2 & dS1 & dS2).
pose proof LB as (ZT & T2 & P1 & P2 & P3 & P4 & K1 & K2 & _). ceil.
pose proof HR as HR0. destruct HR0 as (-> & regs' & mem' & mat & -> & CS & MEQ' & PRESW & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4).
assert (PO : FSP.upoisoned tfibsegs W mem' UP).
{ apply (upoisoned_frame mem' (YFgp.WIN ly regs ql cnt)); [| exact MEQ'].
  intros a Hw. exact (proj1 (proj2 (YFgp.WIN_zone W ly regs mu u nn qsz ql qb cnt bsz FH a Hw))). }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [|exact (conj PO MEQ')].
split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
split; [exact CS|].
split.
{ intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MEQ' x Hx)]. }
split.
{ intros a Hw. apply FAR.apresent_to_unpoison. exact (PRESW a Hw). }
cbv zeta. split; [|split; [|split]].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [|exact V1].
  apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [|exact V2]. apply offU_win_high; nums; lia.
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [|exact V3]. apply offU_win_high; nums; lia.
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [|exact V4]. apply offU_win_high; nums; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The hit and miss walks' shared record (lib/B/YFgq.v, runs lib/B/YFh4.v and lib/B/YFh5.v).                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma regions_offU_q : forall regs u nn q cnt coff jst,
  YFgq.free_hyps W ly regs mu u nn q cnt coff jst ->
  FAR.regions_offU UP (YFgq.E0 ly regs u nn q cnt coff jst) YFgq.REG0.
Proof.
intros regs u nn q cnt coff jst FH.
pose proof (YFgq.derived_ranges W ly regs mu u nn q cnt coff jst FH) as DR.
pose proof (YFgq.LYB W ly regs mu u nn q cnt coff jst FH) as LB.
pose proof (YFgq.fh_Hsp W ly regs mu u nn q cnt coff jst FH) as HSP.
destruct DR as (dU1 & dU2 & dN & dQSZ & dQF & dQL & dQB1 & dQB2 & dCNT & dJST & dT1 & dT2 & dSB1 & dSB2 & dS1 & dS2).
destruct LB as (ZT & T2 & P1 & P2 & P3 & P4 & _).
ceil. intros r a Hr Ha. unfold YFgq.REG0 in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
  unfold YFgq.R_ROOT, YFgq.R_CNT, YFgq.R_JST, fatom8, flit8, flit4 in Ha;
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha.
- rewrite (YFgq.E2 ly regs u nn q cnt coff jst) in Ha. apply offU_stk; nums; lia.
- rewrite (YFgq.EqT ly regs u nn q cnt coff jst) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (ly_T ly) ltac:(nums; lia)) in Ha.
  apply (offU_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia].
- rewrite (YFgq.EqT ly regs u nn q cnt coff jst) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (ly_T ly) ltac:(nums; lia)) in Ha.
  apply (offU_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia].
- rewrite (YFgq.EqT ly regs u nn q cnt coff jst) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (ly_T ly) ltac:(nums; lia)) in Ha.
  apply (offU_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia].
- apply offU_imglow; nums; lia.
- apply offU_imglow; nums; lia.
- apply offU_imglow; nums; lia.
- apply offU_imglow; nums; lia.
Qed.

Lemma FHq_real : forall regs u nn q cnt coff jst,
  YFgq.free_hyps W ly regs mu u nn q cnt coff jst -> YFgq.free_hyps W ly regs mem u nn q cnt coff jst.
Proof.
intros regs u nn q cnt coff jst FH.
pose proof (YFgq.derived_ranges W ly regs mu u nn q cnt coff jst FH) as DR.
pose proof (YFgq.LYB W ly regs mu u nn q cnt coff jst FH) as LB.
pose proof (YFgq.fh_Hsp W ly regs mu u nn q cnt coff jst FH) as HSP.
pose proof (YFgq.fh_last W ly regs mu u nn q cnt coff jst FH) as HLAST.
pose proof (YFgq.fh_hit W ly regs mu u nn q cnt coff jst FH) as HHIT.
pose proof (YFgq.hit_ranges W ly regs mu u nn q cnt coff jst FH) as HRNG.
pose proof FH as FH'. destruct FH' as [LY Htp Hra Hra4 Hsp Hal Hpres Hu IMG Hnn Hq Hnb Hlast Hcnt Hhit Hjst SEED].
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQF & dQL & dQB1 & dQB2 & dCNT & dJST & dT1 & dT2 & dSB1 & dSB2 & dS1 & dS2).
pose proof LB as (ZT & T2 & P1 & P2 & P3 & P4 & _). ceil.
constructor.
- exact LY.
- exact Htp.
- exact Hra.
- exact Hra4.
- exact Hsp.
- exact Hal.
- intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_stk; nums; lia | exact (Hpres a Ha)].
- exact Hu.
- exact IMG.
- exact Hnn.
- exact Hq.
- exact Hnb.
- intros lastb initr Hrev. destruct (HLAST lastb initr Hrev) as (L1 & L2 & L3 & L4 & L5).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split.
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [|exact L4]. apply offU_win_high; nums; lia.
  + intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_himem; nums; lia | exact (L5 a Ha)].
- exact Hcnt.
- intros Hc. destruct (HHIT Hc) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  destruct (HRNG Hc) as (N1 & N2 & N3 & N4 & N5 & C1 & C2 & C3 & C4 & _).
  split.
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [|exact H1].
    apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia].
  + split.
    { apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 4%nat); [|exact H2].
      apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia]. }
    split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
    split; [|exact H10].
    intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_himem; nums; lia | exact (H9 a Ha)].
- exact Hjst.
- exact (proj1 (FAR.st_ok_unpoison_iff UP (YFgq.E0 ly regs u nn q cnt coff jst) YFgq.SS0 (w_H W) regs (w64 A_Enqueue) mem (YK11.seg_rom tfibsegs)
    (regions_offU_q regs u nn q cnt coff jst FH)) SEED).
Qed.

Lemma at_RETQ_u : forall regs u nn q cnt coff jst W' c',
  YFgq.free_hyps W ly regs mu u nn q cnt coff jst -> 1 <= cnt ->
  YFh4.at_RETQ W ly regs mem md u nn q cnt coff W' c' ->
  exists regs' mem' mat,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    W' = W /\
    YFh4.at_RETQ W ly regs mu md u nn q cnt coff W
      (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    FSP.upoisoned tfibsegs W mem' UP /\
    (forall x : word, ~ YFgq.WIN ly regs q cnt coff (bv_unsigned x) -> mem' x = mem x).
Proof.
intros regs u nn q cnt coff jst W' c' FH Hc HR.
pose proof (YFgq.derived_ranges W ly regs mu u nn q cnt coff jst FH) as DR.
pose proof (YFgq.LYB W ly regs mu u nn q cnt coff jst FH) as LB.
pose proof (YFgq.fh_last W ly regs mu u nn q cnt coff jst FH) as HLAST.
pose proof (YFgq.hit_ranges W ly regs mu u nn q cnt coff jst FH Hc) as HRNG.
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQF & dQL & dQB1 & dQB2 & dCNT & dJST & dT1 & dT2 & dSB1 & dSB2 & dS1 & dS2).
pose proof LB as (ZT & T2 & P1 & P2 & P3 & P4 & _).
pose proof HRNG as (N1 & N2 & N3 & N4 & N5 & C1 & C2 & C3 & C4 & _). ceil.
pose proof HR as HR0. destruct HR0 as (-> & regs' & mem' & mat & -> & CS & MEQ' & PRESW & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VL).
assert (PO : FSP.upoisoned tfibsegs W mem' UP).
{ apply (upoisoned_frame mem' (YFgq.WIN ly regs q cnt coff)); [| exact MEQ'].
  intros a Hw. exact (proj1 (proj2 (YFgq.WIN_zone W ly regs mu u nn q cnt coff jst FH a Hw))). }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [|exact (conj PO MEQ')].
split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
split; [exact CS|].
split.
{ intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MEQ' x Hx)]. }
split.
{ intros a Hw. apply FAR.apresent_to_unpoison. exact (PRESW a Hw). }
cbv zeta.
assert (TH8 : forall a0, ly_T ly <= a0 -> a0 + 8 <= ly_T ly + kThreadObjSize ->
  forall kk, (kk < 8)%nat -> FAR.offU UP (a0 + Z.of_nat kk)).
{ intros a0 Y1 Y2. apply (offU_win_zone3 (ly_T ly) kThreadObjSize a0 8%nat); [exact ZT | exact Y1 | cbn; lia]. }
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V1].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V2].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V3].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V4].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 4%nat); [|exact V5].
  apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V6].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V7].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V8].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V9].
- intros lastb initr Hrev. destruct (HLAST lastb initr Hrev) as (L1 & L2 & _).
  apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact (VL lastb initr Hrev)].
Qed.

Lemma at_CALLR_u : forall regs u nn q cnt coff jst W' c',
  YFgq.free_hyps W ly regs mu u nn q cnt coff jst ->
  YFh5.at_CALLR W ly regs mem md u nn q cnt jst W' c' ->
  exists regs1 mem1 mat,
    c' = mkCfg (YK11.mkst regs1 (w64 A_Refill) mem1 (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    W' = W /\
    YFh5.at_CALLR W ly regs mu md u nn q cnt jst W
      (mkCfg (YK11.mkst regs1 (w64 A_Refill) (FSP.unpoison UP mem1) (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    FSP.upoisoned tfibsegs W mem1 UP /\
    (forall x : word, ~ YFgq.WIN0 ly regs (bv_unsigned x) -> mem1 x = mem x).
Proof.
intros regs u nn q cnt coff jst W' c' FH HR.
pose proof (YFgq.derived_ranges W ly regs mu u nn q cnt coff jst FH) as DR.
pose proof (YFgq.LYB W ly regs mu u nn q cnt coff jst FH) as LB.
pose proof (YFgq.fh_Hsp W ly regs mu u nn q cnt coff jst FH) as HSP.
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQF & dQL & dQB1 & dQB2 & dCNT & dJST & dT1 & dT2 & dSB1 & dSB2 & dS1 & dS2).
pose proof LB as (ZT & T2 & P1 & P2 & P3 & P4 & Y1 & Y2 & Y3 & Y4 & Y5 & _). ceil.
pose proof HR as HR0.
destruct HR0 as (-> & regs1 & mem1 & mat & -> & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 & R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
assert (PO : FSP.upoisoned tfibsegs W mem1 UP).
{ apply (upoisoned_frame mem1 (YFgq.WIN0 ly regs)); [| exact MQ1].
  intros a Hw. exact (proj1 (proj2 (YFgq.WIN_zone W ly regs mu u nn q cnt coff jst FH a (YFgq.WIN0_WIN ly regs q cnt coff a Hw)))). }
assert (STK8 : forall a0, ly_stk_lo ly <= a0 -> a0 + 8 <= ly_stk_hi ly ->
  forall kk, (kk < 8)%nat -> FAR.offU UP (a0 + Z.of_nat kk)).
{ intros a0 Z1 Z2 kk Hk. apply offU_stk; lia. }
assert (TH8 : forall a0, ly_T ly <= a0 -> a0 + 8 <= ly_T ly + kThreadObjSize ->
  forall kk, (kk < 8)%nat -> FAR.offU UP (a0 + Z.of_nat kk)).
{ intros a0 Z1 Z2. apply (offU_win_zone3 (ly_T ly) kThreadObjSize a0 8%nat); [exact ZT | exact Z1 | cbn; lia]. }
exists regs1, mem1, mat. split; [reflexivity|]. split; [reflexivity|]. split; [|exact (conj PO MQ1)].
split; [reflexivity|]. exists regs1, (FSP.unpoison UP mem1), mat. split; [reflexivity|].
split; [exact R_ra|]. split; [exact R_sp|]. split; [exact R_gp|]. split; [exact R_tp|].
split; [exact R_a0|]. split; [exact R_a1|]. split; [exact R_a2|]. split; [exact R_a3|].
split; [exact R_s0|]. split; [exact R_s1|]. split; [exact R_s2|]. split; [exact R_s3|].
split; [exact R_s4|]. split; [exact R_s5|]. split; [exact R_hi|].
split.
{ intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MQ1 x Hx)]. }
split.
{ intros a Ha. apply FAR.apresent_to_unpoison. exact (PR1 a Ha). }
cbv zeta. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply TH8; nums; lia | exact V1].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply TH8; nums; lia | exact V2].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply TH8; nums; lia | exact V3].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply TH8; nums; lia | exact V4].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 4%nat); [|exact V5].
  apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply TH8; nums; lia | exact V6].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply STK8; nums; lia | exact F1].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply STK8; nums; lia | exact F2].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply STK8; nums; lia | exact F3].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply STK8; nums; lia | exact F4].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply STK8; nums; lia | exact F5].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply STK8; nums; lia | exact F6].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem1 _ 8%nat); [apply STK8; nums; lia | exact F7].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The miss walk's tail record (lib/B/YFgr.v, run lib/B/YFh6.v), at the state the refill call returns.             *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma regions_offU_r : forall regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50,
  YFgr.free_hyps W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 ->
  FAR.regions_offU UP (YFgr.E0 ly regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50) YFgr.REG0.
Proof.
intros regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH.
pose proof (YFgr.derived_ranges W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as DR.
pose proof (YFgr.LYB W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as LB.
pose proof (YFgr.fh_Hsp W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as HSP.
destruct DR as (dU1 & dU2 & dN & dQSZ & dQF & dQL & dQB1 & dQB2 & dCNT & dJST & dT1 & dT2 & dSB1 & dSB2 & dS1 & dS2).
destruct LB as (ZT & T2 & P1 & P2 & P3 & P4 & _).
ceil. intros r a Hr Ha. unfold YFgr.REG0 in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
  unfold YFgr.R_FRAME, YFgr.R_ROOT, YFgr.R_CNT, YFgr.R_JST, fatom8, flit8, flit4 in Ha;
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha.
- rewrite (YFgr.E2 ly regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50) in Ha. apply offU_stk; nums; lia.
- rewrite (YFgr.EqT ly regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (ly_T ly) ltac:(nums; lia)) in Ha.
  apply (offU_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia].
- rewrite (YFgr.EqT ly regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (ly_T ly) ltac:(nums; lia)) in Ha.
  apply (offU_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia].
- rewrite (YFgr.EqT ly regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50) in Ha. unfold w64 in Ha.
  rewrite (unsigned_lit_small (ly_T ly) ltac:(nums; lia)) in Ha.
  apply (offU_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia].
- apply offU_imglow; nums; lia.
- apply offU_imglow; nums; lia.
- apply offU_imglow; nums; lia.
- apply offU_imglow; nums; lia.
Qed.

Lemma FHr_real : forall regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50,
  YFgr.free_hyps W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 ->
  YFgr.free_hyps W ly regs mem u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50.
Proof.
intros regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH.
pose proof (YFgr.derived_ranges W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as DR.
pose proof (YFgr.LYB W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as LB.
pose proof (YFgr.fh_Hsp W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as HSP.
pose proof (YFgr.fh_last W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as HLAST.
pose proof (YFgr.fh_hit W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as HHIT.
pose proof (YFgr.hit_ranges W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as HRNG.
pose proof FH as FH'.
destruct FH' as [LY Htp Hra Hra4 Hsp Hal Hpres Hframe Hsv Hu IMG Hnn Hq Hnb Hlast Hcnt Hhit Hjst SEED].
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQF & dQL & dQB1 & dQB2 & dCNT & dJST & dT1 & dT2 & dSB1 & dSB2 & dS1 & dS2).
pose proof LB as (ZT & T2 & P1 & P2 & P3 & P4 & _). ceil.
assert (STK8 : forall a0, ly_stk_lo ly <= a0 -> a0 + 8 <= ly_stk_hi ly ->
  forall kk, (kk < 8)%nat -> FAR.offU UP (a0 + Z.of_nat kk)).
{ intros a0 Z1 Z2 kk Hk. apply offU_stk; lia. }
destruct Hframe as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
constructor.
- exact LY.
- exact Htp.
- exact Hra.
- exact Hra4.
- exact Hsp.
- exact Hal.
- intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_stk; nums; lia | exact (Hpres a Ha)].
- split; [|split; [|split; [|split; [|split; [|split]]]]].
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [apply STK8; nums; lia | exact G1].
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [apply STK8; nums; lia | exact G2].
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [apply STK8; nums; lia | exact G3].
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [apply STK8; nums; lia | exact G4].
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [apply STK8; nums; lia | exact G5].
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [apply STK8; nums; lia | exact G6].
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [apply STK8; nums; lia | exact G7].
- exact Hsv.
- exact Hu.
- exact IMG.
- exact Hnn.
- exact Hq.
- exact Hnb.
- intros lastb initr Hrev. destruct (HLAST lastb initr Hrev) as (L1 & L2 & L3 & L4 & L5).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split.
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [|exact L4]. apply offU_win_high; nums; lia.
  + intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_himem; nums; lia | exact (L5 a Ha)].
- exact Hcnt.
- intros Hc. destruct (HHIT Hc) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  destruct (HRNG Hc) as (N1 & N2 & N3 & N4 & N5 & C1 & C2 & C3 & C4 & _).
  split.
  + apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 8%nat); [|exact H1].
    apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia].
  + split.
    { apply (FAR.val_mem_of_unpoison (w_H W) UP mem _ 4%nat); [|exact H2].
      apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia]. }
    split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
    split; [|exact H10].
    intros a Ha. apply (FAR.apresent_of_unpoison (w_H W) UP mem a); [apply offU_himem; nums; lia | exact (H9 a Ha)].
- exact Hjst.
- exact (proj1 (FAR.st_ok_unpoison_iff UP (YFgr.E0 ly regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50) YFgr.SS0 (w_H W) regs (w64 PC_ENQ_RA) mem (YK11.seg_rom tfibsegs)
    (regions_offU_r regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH)) SEED).
Qed.

Lemma at_RETR_u : forall regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 W' c',
  YFgr.free_hyps W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 ->
  YFh6.at_RETR W ly regs mem md u nn q cnt coff ra0 s00 s10 s20 s30 s40 s50 W' c' ->
  exists regs' mem' mat,
    c' = mkCfg (YK11.mkst regs' (w64 ra0) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    W' = W /\
    YFh6.at_RETR W ly regs mu md u nn q cnt coff ra0 s00 s10 s20 s30 s40 s50 W
      (mkCfg (YK11.mkst regs' (w64 ra0) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    FSP.upoisoned tfibsegs W mem' UP /\
    (forall x : word, ~ YFgr.WIN ly q cnt coff (bv_unsigned x) -> mem' x = mem x).
Proof.
intros regs u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 W' c' FH HR.
pose proof (YFgr.derived_ranges W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as DR.
pose proof (YFgr.LYB W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as LB.
pose proof (YFgr.fh_last W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as HLAST.
pose proof (YFgr.fh_Hcnt W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH) as HCNT.
pose proof (YFgr.hit_ranges W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH ltac:(lia)) as HRNG.
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQF & dQL & dQB1 & dQB2 & dCNT & dJST & dT1 & dT2 & dSB1 & dSB2 & dS1 & dS2).
pose proof LB as (ZT & T2 & P1 & P2 & P3 & P4 & _).
pose proof HRNG as (N1 & N2 & N3 & N4 & N5 & C1 & C2 & C3 & C4 & _). ceil.
pose proof HR as HR0.
destruct HR0 as (-> & regs' & mem' & mat & -> & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QCS & MEQ6 & PRESW & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VL).
assert (PO : FSP.upoisoned tfibsegs W mem' UP).
{ apply (upoisoned_frame mem' (YFgr.WIN ly q cnt coff)); [| exact MEQ6].
  intros a Hw. exact (proj1 (proj2 (YFgr.WIN_zone W ly regs mu u nn q cnt coff jst ra0 s00 s10 s20 s30 s40 s50 FH a Hw))). }
assert (TH8 : forall a0, ly_T ly <= a0 -> a0 + 8 <= ly_T ly + kThreadObjSize ->
  forall kk, (kk < 8)%nat -> FAR.offU UP (a0 + Z.of_nat kk)).
{ intros a0 Z1 Z2. apply (offU_win_zone3 (ly_T ly) kThreadObjSize a0 8%nat); [exact ZT | exact Z1 | cbn; lia]. }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [|exact (conj PO MEQ6)].
split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|].
split; [exact Q20|]. split; [exact Q21|]. split; [exact QCS|].
split.
{ intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MEQ6 x Hx)]. }
split.
{ intros a Hw. apply FAR.apresent_to_unpoison. exact (PRESW a Hw). }
cbv zeta. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V1].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V2].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V3].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply TH8; nums; lia | exact V4].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 4%nat); [|exact V5].
  apply (offU_win_zone3 (ly_T ly) kThreadObjSize); [exact ZT | nums; lia | nums; lia].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V6].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V7].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V8].
- apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact V9].
- intros lastb initr Hrev. destruct (HLAST lastb initr Hrev) as (L1 & L2 & _).
  apply (FAR.val_mem_to_unpoison (w_H W) UP mem' _ 8%nat); [apply offU_win_high; nums; lia | exact (VL lastb initr Hrev)].
Qed.
End b.
End k.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF0w YF34 YF35 YF37 YF36 YF39 YF3d YF3f YF3e YF3c YF3a YF38 YF3g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFX_IMG_END, TFX_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, YF34.YFRAME, YF35.YFRAME, YF37.YFRAME, YF36.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, YF38.sp1, YF38.sp0, YF38.SY in *; numconst.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ivl_dec : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. destruct (Z_le_gt_dec lo a); [img_try (destruct (Z_lt_ge_dec a hi); [left; img_lia | right; img_lia]) | img_try (right; img_lia)]. Qed.
Section d. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Hypothesis RCC : tfx_rchunk_spec B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : dr_pre B ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (YF38.sp0 regs0).
Local Notation sp1 := (YF38.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Local Notation hdra := (YF38.hdra B ly).
Local Notation zlen := (@YF38.zlen _).
Local Notation SY := (YF38.SY regs0).
Local Notation acc := (YF38.acc B ly X0 W0 regs0 mem0 md0).
Local Notation common_regs := (YF38.common_regs regs0).
Local Notation loop_regs := (YF38.loop_regs regs0).
Local Notation frame_cells := (YF38.frame_cells ly regs0).
Local Notation tmp_cells := (YF38.tmp_cells ly regs0).
Local Notation ost := (YF38.ost B ly X0 W0 regs0 mem0 md0).
Local Notation rcst := (YF38.rcst B ly X0 W0 regs0 mem0 md0).
Local Notation rst := (YF38.rst B ly X0 W0 regs0 mem0 md0).
Local Notation cdst := (YF38.cdst B ly X0 W0 regs0 mem0 md0).
Local Notation qst := (YF38.qst B ly X0 W0 regs0 mem0 md0).
Local Notation OST := (YF38.OST B ly X0 W0 regs0 mem0 md0).
Local Notation RCST := (YF38.RCST B ly X0 W0 regs0 mem0 md0).
Local Notation RST := (YF38.RST B ly X0 W0 regs0 mem0 md0).
Local Notation CDST := (YF38.CDST B ly X0 W0 regs0 mem0 md0).
Local Notation QST := (YF38.QST B ly X0 W0 regs0 mem0 md0).
Local Notation entry_facts := (YF3g.entry_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (YF3g.sp_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Lemma AR_after_stack_write : forall X (W : world tfxsegs) mem mem' md mat (WINP : Z -> Prop),
AR tfxsegs B ly X W mem md ->
(forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) -> (forall a, WINP a \/ ~ WINP a) ->
(forall x : word, ~ WINP (bv_unsigned x) -> mem' x = mem x) ->
(forall a, WINP a -> apresent (w_H W) mem' a) ->
AR tfxsegs B ly X W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros X W mem mem' md mat WINP HA HST DEC MQ PRS. pose proof (lo_top ly (am_layout _ _ _ _ (proj1 HA))) as (_ & _ & _ & T4 & _ & _ & T7).
img_apply (AR_frame_law_ok tfxsegs B ly X W mem md mem' _ HA).
- intros a Ha O. img_apply aview_same. img_apply MQ. rewrite unsigned_lit_small by img_exact Ha. intros Hw. img_exact (AR_stack_law_ok tfxsegs B ly X W mem md a HA (HST a Hw) O).
- intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (mem' x) as [b'|] eqn:E'; [img_try (cbn in HN; discriminate)|].
destruct (mem x) as [b0|] eqn:E0; [|img_try (img_exact (Hv HN))].
destruct (DEC a') as [C|C].
+ destruct (PRS a' C) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
+ rewrite (MQ x C) in E'. congruence.
- img_apply m_vmmaps_wvb.
- img_apply m_vm_lazy_wvb.
- img_apply eager_used_wvb.
- intros a Ha Hx. img_apply MQ. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)).
intros Hw. pose proof (HST a Hw). clear - Ha H T7. unfold in_band_rw, zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. img_lia.
Qed.
Lemma presence_after_write : forall (W : world tfxsegs) mem mem' (WINP : Z -> Prop) a,
(forall a, WINP a \/ ~ WINP a) -> (forall x : word, ~ WINP (bv_unsigned x) -> mem' x = mem x) ->
(forall a, WINP a -> apresent (w_H W) mem' a) -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a -> apresent (w_H W) mem' a.
Proof.
intros W mem mem' WINP a DEC MQ PRS Ha HP. destruct (DEC a) as [C|C]; [img_try (img_exact (PRS a C))|].
img_apply (apresent_same (w_H W) mem mem' a); [|img_try (img_exact HP)]. img_apply MQ. rewrite unsigned_lit_small by img_exact Ha. img_exact C.
Qed.
Lemma aview_after_write : forall (H : word -> bool) mem mem' (WINP : Z -> Prop) a,
(forall x : word, ~ WINP (bv_unsigned x) -> mem' x = mem x) -> 0 <= a < 2 ^ 64 -> ~ WINP a ->
aview tfxsegs H mem' a = aview tfxsegs H mem a.
Proof. intros H mem mem' WINP a MQ Ha Hn. img_apply aview_same. img_apply MQ. rewrite unsigned_lit_small by img_exact Ha. img_exact Hn. Qed.
Lemma HTSD : ly_tsd ly = TFX_TSD.
Proof. destruct PRE as ((M & _) & _). rewrite (am_tsd B ly X0 _ M). img_apply (ts_tsd _ TB). Qed.
Lemma rix_slot : forall X its P selfs b, RIx U 0 0 0 X its P selfs -> (In (b_self b) selfs \/ In b P) -> slot_ok X (b_self b).
Proof.
intros X its P selfs b RX Hb. img_apply (RIx_slots U 0 0 0 X its P selfs _ RX). img_apply in_app_iff.
destruct Hb as [Hb|Hb]; [img_try (left; img_exact Hb) | img_try (right; img_apply in_map; img_exact Hb)].
Qed.
Lemma rix_items_ok : forall X its P selfs, RIx U 0 0 0 X its P selfs -> items_ok P.
Proof. intros X its P selfs (_ & _ & _ & BL & _). img_exact BL. Qed.
Definition lastaddr (l : list batch) : Z := match rev l with [] => 0 | b :: _ => SB + b_self b end.
Lemma T_E : forall W' c', YF34.at_OE W0 ly regs0 mem0 md0 (zlen P0) W' c' -> OST X0 P0 W' c'.
Proof.
intros W' c' HP. destruct HP as (-> & NZ & regs & mem & mat & -> & R2 & CS & R8 & R9 & R18 & R19 & R21 & R10 & MQ & PRS & CB & SV).
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (RI_RIx U 0 0 0 X0 P0 HRI) as RX.
assert (WST : forall a, YF34.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (img_try (intros a Ha; unfold YF34.WIN in Ha; clear - Ha E1 E2; nsp; img_lia)).
assert (WDEC : forall a, YF34.WIN regs0 a \/ ~ YF34.WIN regs0 a) by (img_try (intros a; unfold YF34.WIN; img_apply ivl_dec)).
assert (WSY : forall a, YF34.WIN regs0 a -> SY a) by (img_try (intros a Ha; unfold YF34.WIN in Ha; unfold YF38.SY; clear - Ha; nsp; img_lia)).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF34.WIN regs0 a -> aview tfxsegs (w_H W0) mem a = aview tfxsegs (w_H W0) mem0 a).
{ intros a Ha Hn. img_exact (aview_after_write (w_H W0) mem0 mem _ a MQ Ha Hn). }
unfold plist_cells, qc_cells in CELLS. cbn [qc_list qc_bytes] in CELLS.
apply Forall_cons_iff in CELLS as [C0 CELLS]. apply Forall_cons_iff in CELLS as [C8 CELLS]. apply Forall_cons_iff in CELLS as [C16 CELLS]. apply Forall_cons_iff in CELLS as [C24 CB0].
assert (AGT : forall a, sp0 <= a < sp0 + 32 -> aview tfxsegs (w_H W0) mem a = aview tfxsegs (w_H W0) mem0 a).
{ intros a Ha. img_apply AG; [img_try (clear - Ha U0 S2; nsp; img_lia)|]. unfold YF34.WIN. clear - Ha. nsp. img_lia. }
assert (LZR : 0 <= lastaddr P0 < ASAN_CEIL).
{ unfold lastaddr. destruct (rev P0) as [|bl initr] eqn:ER; [img_try (ceil; unfold ASAN_CEIL; img_lia)|].
assert (Hbl : In bl P0) by (img_try (img_apply in_rev; rewrite ER; left; img_refl)).
pose proof (slot_facts B ly X0 _ (b_self bl) M (rix_slot X0 [] P0 [] bl RX (or_intror Hbl))) as (B1 & B2 & _).
clear - B1 B2. numconst. img_lia. }
exists (lastaddr P0), (sum_bytes P0 mod 2 ^ 64), regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split; [img_refl|].
constructor.
-   constructor.
+ img_exact (AR_after_stack_write X0 W0 mem0 mem md0 mat _ HAR WST WDEC MQ PRS).
+ img_apply wle_refl.
+ img_apply same_io_with_vm_backing.
+ intros a O; img_exact O.
+ intros a Ha _ _ NS _. img_apply AG; [img_try (img_exact Ha)|]. intros Hw. img_apply NS. left. unfold spZ, YF34.WIN in *. clear - Hw. nsp. img_lia.
+ intros a Ha. img_apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [img_try (unfold YF38.SY in Ha; clear - Ha S1 S2; nsp; img_lia)|].
img_apply HPRES. unfold YF38.SY, YF38.sp0 in Ha. img_exact Ha.
+ img_exact INIT0.
- img_exact RX.
- intros ->. img_apply NZ. img_refl.
- unfold YF38.zlen. img_exact LENP.
- unfold YF38.common_regs. splits; img_apply CS; cbn; tauto.
- unfold YF38.loop_regs. splits; try assumption; rewrite R2; unfold YF38.sp1; img_refl.
- img_exact R10.
- split; [| img_try (img_exact SV)]. eapply val_mem_addr; [img_try (img_exact CB) | img_try (clear; nsp; img_lia)].
- unfold YF38.tmp_cells. cbv zeta. split; [|img_try (split; [|split; [|split; [|split]]])].
+ eapply val_mem_keep; [|img_try (img_exact (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C0))]. cbn [aeval]. intros a' Ha'. img_apply AGT. cbn in Ha'. img_lia.
+ eapply val_mem_keep; [|pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C8) as V; cbn [aeval aoff] in V; destruct P0 as [|b0 P']; cbn [aeval batch_exp firstaddr] in V |- *; img_exact V]. cbn [aeval aoff]. intros a' Ha'. img_apply AGT. cbn in Ha'. img_lia.
+ eapply val_mem_keep; [|pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C16) as V; cbn [aeval aoff] in V; unfold lastaddr; destruct (rev P0) as [|bl initr]; cbn [aeval batch_exp] in V |- *; img_exact V]. cbn [aeval aoff]. intros a' Ha'. img_apply AGT. cbn in Ha'. img_lia.
+ eapply val_mem_keep; [|img_try (img_apply val_mem_mod64; pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C24) as V; cbn [aeval aoff] in V; img_exact V)]. cbn [aeval aoff]. intros a' Ha'. img_apply AGT. cbn in Ha'. img_lia.
+ img_exact LZR.
+ img_apply mod64_range.
- img_apply (batch_cells_xfer B ly P0 (aview tfxsegs (w_H W0) mem0)); [img_try (img_exact (rix_items_ok X0 [] P0 [] RX)) | | img_try (img_exact CB0)].
intros b a Hb Hs. pose proof (rix_slot X0 [] P0 [] b RX (or_intror Hb)) as SZ.
pose proof (slot_high B ly X0 _ (b_self b) M SZ a Hs) as (_ & _ & Ha). img_apply AG; [img_try (clear - Ha; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in Ha; img_lia)|]. intros Hw.
img_exact (slot_not_stack B ly X0 _ (b_self b) M SZ a Hs (WST a Hw)).
Qed.
Lemma csv_get : forall regs regs', aregs_preserved regs regs' -> forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' CS r z Hz <-. img_exact (CS z Hz). Qed.
Ltac csv CS r z := rewrite (csv_get _ _ CS r z ltac:(img_try (unfold acallee_saved; img_lia)) ltac:(img_try (img_apply bv_eq; (img_case; vm_compute); img_refl))).
Lemma T_O : forall X b t lz qb W regs mem md, ost X (b :: t) lz qb W regs mem md ->
SRr tfxsegs W (cfg_at tfxsegs (0x33ab4 + D_150) regs mem md) (RCST X b t (b_items b) 0).
Proof.
intros X b t lz qb W regs mem md ST. pose proof ST as [AC RX NE LEN CR LR A0 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV.
pose proof (RIx_open U 0 0 0 X b t RX) as [RXo BL].
destruct (b_items b) as [|k0 ks] eqn:Hk0; [img_try (cbn in BL; img_lia)|]. rewrite <- Hk0 in *.
pose proof (seed_O B TB ly X0 P0 W0 regs0 mem0 md0 PRE X b t lz qb W regs mem md k0 ks ST Hk0) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [img_try (img_exact (YF3d.segYO W ly regs mem md _ _ _ _ _ _ _ _ (m_vm_materialized md) FH))|].
intros W' c' _ HP. destruct HP as (-> & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R20 & R22 & R23 & R24 & R25 & MQ & PRS & CELLS). cbv zeta in CELLS.
destruct CELLS as (V0 & V8 & V16 & V24). rewrite SPV in *.
set (WINP := YF35.WIN regs) in *.
assert (WE : forall a, WINP a <-> sp0 <= a < sp0 + 32) by (img_try (intros a; (subst WINP; cbv beta); unfold YF35.WIN; rewrite SPV; clear - S5; nsp; img_lia)).
assert (WST : forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (img_try (intros a Ha; apply WE in Ha; clear - Ha E1 E2; nsp; img_lia)).
assert (WDEC : forall a, WINP a \/ ~ WINP a) by (img_try (intros a; (subst WINP; cbv beta); unfold YF35.WIN; img_apply ivl_dec)).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ WINP a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a).
{ intros a Ha Hn. img_exact (aview_after_write (w_H W) mem mem' _ a MQ Ha Hn). }
pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof CR as (C3 & C4 & C26 & C27).
exists (YF35.LZn (firstaddr ly t) lz), (zcanon (qb - b_bytes b mod 2 ^ 64)), regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [img_refl|].
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb).
constructor.
- constructor.
+ img_exact (AR_after_stack_write X W mem mem' md mat WINP HAR WST WDEC MQ PRS).
+ img_exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC).
+ eapply same_io_trans; [img_try (img_exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_apply same_io_with_vm_backing)].
+ img_exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC).
+ intros a Ha N0 N1 NS NT. rewrite (AG a Ha) by (img_try (intros Hw; apply WE in Hw; img_exact (NT Hw))). img_exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT).
+ intros a Ha. img_apply (presence_after_write W mem mem' WINP a WDEC MQ PRS); [img_try (unfold YF38.SY in Ha; clear - Ha S1 S2; nsp; img_lia)|]. img_exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha).
+ img_exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- img_exact RXo.
- exists []. split; [img_refl | img_refl].
- rewrite Hk0. discriminate.
- img_exact BL.
- rewrite zlen_cons in LEN. clear - LEN. img_lia.
- unfold YF38.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; img_apply CS; cbn; tauto.
- unfold YF38.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [img_try (img_exact Q2) | img_try (img_apply CS; cbn; tauto) ..].
- unfold YF38.batch_regs. splits; [img_try (img_exact R20) | img_try (img_exact R22) | img_try (img_exact R24)].
- img_exact R1.
- img_exact R10.
- intros k ks' Hk. rewrite Hk0 in Hk. injection Hk as <- <-. img_exact R11.
- rewrite R23. f_equal. img_lia.
- rewrite R25. f_equal.
- img_apply (frame_cells_keep ly regs0 W W mem mem'); [|img_try (img_exact FR)]. intros a Ha. img_apply AG; [img_try (clear - Ha S5 U0 U1; nsp; img_lia)|]. intros Hw. apply WE in Hw. clear - Ha Hw S5. nsp. img_lia.
- unfold YF38.tmp_cells. cbv zeta. split; [|img_try (split; [|split; [|split; [|split]]])].
+ eapply val_mem_addr; [img_try (img_exact V0) | img_try (rewrite zlen_cons; img_lia)] || (replace (zlen t) with (zlen (b :: t) - 1) by (img_try (rewrite zlen_cons; img_lia)); eapply val_mem_addr; [img_try (img_exact V0) | img_try (clear - S5; nsp; img_lia)]).
+ eapply val_mem_addr; [img_try (img_exact V8) | img_try (clear - S5; nsp; img_lia)].
+ eapply val_mem_addr; [img_try (img_exact V16) | img_try (clear - S5; nsp; img_lia)].
+ eapply val_mem_addr; [img_try (img_exact V24) | img_try (clear - S5; nsp; img_lia)].
+ unfold YF35.LZn. destruct (firstaddr ly t =? 0); [img_try (ceil; unfold ASAN_CEIL; img_lia) | img_try (img_exact Rlz)].
+ unfold zcanon, M64. img_apply Z.mod_pos_bound. img_lia.
- img_apply (batch_cells_xfer B ly (b :: t) (aview tfxsegs (w_H W) mem)); [| | img_try (img_exact CE)].
+ constructor; [img_try (img_exact BL) | img_try (img_exact (rix_items_ok X [] (b :: t) [] RX)) ] || (unfold items_ok; constructor; [img_try (img_exact BL) | img_try (img_exact (rix_items_ok X _ t _ RXo))]).
+ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (img_try (img_apply (rix_slot X [] (b :: t) [] b' RX); right; img_exact Hb)).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha). img_apply AG; [img_try (clear - Ha; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in Ha; img_lia)|]. intros Hw.
img_exact (slot_not_stack B ly X _ (b_self b') M SZ a Hs (WST a Hw)).
Qed.
Lemma RC_pre : forall X b t k ks i lz qb W regs mem md, rcst X b t (k :: ks) i lz qb W regs mem md -> rcc_pre B ly X k (sp1 + 8) W regs mem md.
Proof.
intros X b t k ks i lz qb W regs mem md ST. destruct ST as [AC RX ITS NE BL LEN CR LR BR RA A0 A1 S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27).
pose proof (RIx_head U 0 0 0 X k ks t [b_self b] RX) as (WP & Hk & Hst & Hni).
pose proof (item_facts B ly X _ k M Hk) as (I0 & I1 & I2 & I3 & I4).
destruct FR as [CB SV].
unfold rcc_pre, spZ, raZ. rewrite SPV, RA. img_change (bv_unsigned (w64 (0x33b00 + D_150))) with (0x33b00 + D_150).
splits.
- img_exact HAR.
- img_exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- img_exact Hk.
- img_exact Hst.
- img_exact Hni.
- img_case; vm_compute. all: img_refl.
- img_lia.
- img_exact S7.
- clear - E1 S5. nsp. img_lia.
- img_lia.
- clear - E2 S5. nsp. img_lia.
- rewrite S5. replace (sp0 - 112 + 8) with (sp0 + (-13) * 8) by img_lia. rewrite Z_mod_plus_full. clear - S6. img_apply Z.mod_divide; [img_lia|]. apply Z.mod_divide in S6 as [q Hq]; [|img_lia]. exists (2 * q). img_lia.
- intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. clear - Ha S5. nsp. img_lia.
- intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. clear - Ha S5. nsp. img_lia.
- eapply val_mem_addr; [img_try (img_exact CB) | img_refl].
- rewrite C3. img_exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). img_refl.
- img_exact A0.
- rewrite (A1 k ks eq_refl). f_equal. unfold kChunkHeaderSize in I0. unfold kChunkHeaderSize. img_lia.
Qed.
Lemma RC_post : forall X b t k ks i lz qb W regs mem md X1 ns W' c',
rcst X b t (k :: ks) i lz qb W regs mem md -> rcc_leaf B ly X k W regs mem md (tt, X1) W' c' -> recycle_post U 0 0 0 X k ns (tt, X1) ->
RST X1 b t ks (S i) W' c'.
Proof.
intros X b t k ks i lz qb W regs mem md X1 ns W' c' ST HL RP. destruct ST as [AC RX ITS NE BL LEN CR LR BR RA A0 A1 S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (RIx_head U 0 0 0 X k ks t [b_self b] RX) as (WP & Hk & Hst & Hni).
pose proof (RIx_rc_step U 0 0 0 X k ks t [b_self b] ns X1 RX RP) as (RX1 & FF & Hqt & Hqg & Hunq).
destruct HL as (regs' & mem' & md' & -> & (AR1 & LLE & WLE & CSV & SIO & FRM & PRS) & PU & INI). cbn [fst snd] in *.
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. img_change (bv_unsigned (w64 (0x33b00 + D_150))) with (0x33b00 + D_150). rewrite SPV in FRM, PRS.
pose proof AR1 as (M1 & _).
assert (OWN1 : forall a, aowned B ly X1 a -> aowned B ly X a) by (img_try (intros a; img_exact (aowned_rc_back B ly U 0 0 0 X k ns X1 Hst RP a))).
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK <= a < sp1) -> aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a).
{ intros a Ha Hs Hn. img_apply FRM; [img_try (img_exact Ha) | img_try (img_exact (AR_stack_law_ok tfxsegs B ly X W mem md a HAR Hs)) | img_try (img_exact (AR_stack_law_ok tfxsegs B ly X1 W' mem' md' a AR1 Hs)) | | img_try (intros F; img_exact F)].
intros [C|C]; [img_try (img_exact (Hn C))|]. rewrite (ts_errno _ TB) in C. clear - C Hs E7. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_ERRNO, kHighMemBeg in *. img_lia. }
assert (AGB : forall b' a, In b' (b :: t) -> bslot ly (b_self b') a -> aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a).
{ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (img_try (img_apply (rix_slot X (k :: ks) t [b_self b] b' RX); destruct Hb as [<-|Hb]; [img_try (left; left; img_refl) | img_try (right; img_exact Hb)])).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha).
img_apply PU; [img_try (clear - Ha; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in Ha; img_lia) | img_try (img_exact (slot_puser B ly X _ (b_self b') M SZ a Hs)) | img_try (img_exact (slot_vs_chunk B ly X _ (b_self b') k M SZ Hk a Hs))]. }
exists lz, qb, regs', mem', md'. split; [img_refl|].
destruct ITS as (done & Hits & Hdone).
constructor.
- constructor.
+ img_exact AR1.
+ eapply wle_trans; [img_try (img_exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact WLE)].
+ img_exact (same_io_trans _ _ _ (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) SIO).
+ intros a O. img_exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a (OWN1 a O)).
+ intros a Ha N0 N1 NS NT. rewrite (FRM a Ha); [img_try (img_exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 ltac:(intros O; img_exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O))) NS NT)) | img_try (intros O; img_exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O))) | img_try (img_exact N1) | | img_try (intros F; img_exact F)].
intros [C|C]; img_apply NS; [img_try (left; clear - C S5; nsp; img_lia) | img_try (right; img_exact C)].
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK) sp1 a) as [C|C]; [img_try (img_exact (PRS a C))|].
img_apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [img_try (unfold YF38.SY in Ha; clear - Ha S1 S2; nsp; img_lia) | | img_try (img_exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha))].
img_apply AGS; [img_try (unfold YF38.SY in Ha; clear - Ha S1 S2; nsp; img_lia) | img_try (unfold YF38.SY in Ha; clear - Ha E1 E2; nsp; img_lia) | img_try (img_exact C)].
+ img_exact INI.
- img_exact RX1.
- exists (done ++ [k]). split; [img_try (rewrite Hits, <- app_assoc; img_refl) | img_try (rewrite length_app, Hdone; cbn; img_lia)].
- img_lia.
- img_exact BL.
- img_exact LEN.
- unfold YF38.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; [img_try (csv CSV (3%bv : bv 5) 3) | img_try (csv CSV (4%bv : bv 5) 4) | img_try (csv CSV (26%bv : bv 5) 26) | img_try (csv CSV (27%bv : bv 5) 27)]; img_refl.
- unfold YF38.loop_regs. rewrite <- Q2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21.
splits; [img_try (csv CSV (2%bv : bv 5) 2) | img_try (csv CSV (8%bv : bv 5) 8) | img_try (csv CSV (9%bv : bv 5) 9) | img_try (csv CSV (18%bv : bv 5) 18) | img_try (csv CSV (19%bv : bv 5) 19) | img_try (csv CSV (21%bv : bv 5) 21)]; img_refl.
- unfold YF38.batch_regs. rewrite <- R20, <- R22, <- R24. splits; [img_try (csv CSV (20%bv : bv 5) 20) | img_try (csv CSV (22%bv : bv 5) 22) | img_try (csv CSV (24%bv : bv 5) 24)]; img_refl.
- csv CSV (23%bv : bv 5) 23. rewrite S7r. f_equal. img_lia.
- csv CSV (25%bv : bv 5) 25. rewrite S9r. f_equal. img_lia.
- img_apply (frame_cells_keep ly regs0 W W' mem mem'); [|img_try (img_exact FR)]. intros a Ha. img_apply AGS; [img_try (clear - Ha U0 U1 S5; nsp; img_lia) | img_try (clear - Ha E1 E2 S5; nsp; img_lia) | img_try (clear - Ha; img_lia)].
- img_apply (tmp_cells_keep ly regs0 W W' mem mem'); [|img_try (img_exact TM)]. intros a Ha. img_apply AGS; [img_try (clear - Ha U0 S2; nsp; img_lia) | img_try (clear - Ha E1 E2; nsp; img_lia) | img_try (clear - Ha S5; img_lia)].
- img_apply (batch_cells_xfer B ly (b :: t) (aview tfxsegs (w_H W) mem)); [| img_try (img_exact AGB) | img_try (img_exact CE)].
unfold items_ok. constructor; [img_try (img_exact BL) | img_try (img_exact (rix_items_ok X _ t _ RX))].
Qed.
Definition postRI (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfxsegs) (c' : config) : Prop :=
match its with [] => CDST X b t W' c' | _ :: _ => RCST X b t its i W' c' end.
Lemma T_R : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs mem md ->
SRr tfxsegs W (cfg_at tfxsegs (0x33b00 + D_150) regs mem md) (postRI X b t its i).
Proof.
intros X b t its i lz qb W regs mem md ST. pose proof ST as [AC RX ITS Hi BL LEN CR LR BR S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (seed_R B TB ly X0 P0 W0 regs0 mem0 md0 PRE X b t its i lz qb W regs mem md ST) as FH.
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (img_try (rewrite Hits, zlen_app; unfold YF38.zlen; rewrite Hdone; img_lia)).
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [img_try (img_exact (YF3f.segYR W ly regs mem md _ _ _ _ (m_vm_materialized md) FH))|].
intros W' c' _ HP. unfold YF37.postR in HP. unfold postRI.
destruct its as [|k ks].
-
rewrite zlen_nil in LENi. replace (Z.of_nat i <? zlen (b_items b)) with false in HP by (img_try (symmetry; img_apply Z.ltb_ge; img_lia)).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R12 & R13 & MQ).
assert (MM : mem' = mem) by (img_try (img_apply functional_extensionality; intros x; img_apply MQ; intros [])). (subst mem'; cbv beta).
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [img_refl|].
constructor.
+ constructor; [img_try (img_apply AR_wvb; img_exact HAR) | img_try (img_exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (eapply same_io_trans; [img_exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | img_apply same_io_with_vm_backing])
| img_try (img_exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC))].
+ img_exact RX.
+ img_exact LEN.
+ unfold YF38.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; img_apply CS; cbn; tauto.
+ unfold YF38.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [img_try (img_exact Q2) | img_try (img_apply CS; cbn; tauto) ..].
+ img_exact R1.
+ img_exact R10.
+ img_exact R11.
+ img_exact R12.
+ img_exact R13.
+ img_exact FR.
+ img_exact TM.
+ img_exact (batch_cells_tail B ly _ b t CE).
-
rewrite zlen_cons in LENi. replace (Z.of_nat i <? zlen (b_items b)) with true in HP by (img_try (symmetry; img_apply Z.ltb_lt; unfold YF38.zlen in *; img_lia)).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R23 & R25 & MQ).
assert (MM : mem' = mem) by (img_try (img_apply functional_extensionality; intros x; img_apply MQ; intros [])). (subst mem'; cbv beta).
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [img_refl|].
constructor.
+ constructor; [img_try (img_apply AR_wvb; img_exact HAR) | img_try (img_exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (eapply same_io_trans; [img_exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | img_apply same_io_with_vm_backing])
| img_try (img_exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC))].
+ img_exact RX.
+ exists done. split; [img_try (img_exact Hits) | img_try (img_exact Hdone)].
+ discriminate.
+ img_exact BL.
+ img_exact LEN.
+ unfold YF38.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; img_apply CS; cbn; tauto.
+ unfold YF38.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [img_try (img_exact Q2) | img_try (img_apply CS; cbn; tauto) ..].
+ unfold YF38.batch_regs. rewrite <- R20, <- R22, <- R24. splits; img_apply CS; cbn; tauto.
+ img_exact R1.
+ rewrite R10, SPV. img_refl.
+ intros k' ks' Hk. injection Hk as <- <-. img_exact R11.
+ rewrite R23. unfold YF37.S7v. f_equal. img_lia.
+ rewrite R25. f_equal. img_lia.
+ img_exact FR.
+ img_exact TM.
+ img_exact CE.
Qed.
Lemma CD_pre : forall X b t lz qb W regs mem md, cdst X b t lz qb W regs mem md -> cd_pre B ly X kBatchClass (b_self b) W regs mem md.
Proof.
intros X b t lz qb W regs mem md ST. destruct ST as [AC RX LEN CR LR RA A0 A1 A2 A3 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27).
pose proof (RIx_cd_pre U 0 0 0 X t (b_self b) [] RX) as (WP & Z1 & Z2 & Z3 & RM).
unfold cd_pre, spZ, raZ. rewrite SPV, RA. img_change (bv_unsigned (w64 (0x33b38 + D_150))) with (0x33b38 + D_150). rewrite bslack_24.
splits.
- img_exact HAR.
- img_exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- unfold kBatchClass; img_lia.
- unfold kBatchClass; img_lia.
- img_exact (proj1 Z1).
- img_exact (proj2 Z1).
- img_exact Z2.
- img_exact Z3.
- img_exact RM.
- img_case; vm_compute. all: img_refl.
- img_lia.
- img_exact S7.
- clear - E1 S5. nsp. img_lia.
- clear - E2 S5. nsp. img_lia.
- intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. clear - Ha S5. nsp. img_lia.
- rewrite C3. img_exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). img_refl.
- img_exact A0.
- img_exact A1.
- img_exact A2.
- img_exact A3.
Qed.
Lemma CD_post : forall X b t lz qb W regs mem md X2 ns W' c',
cdst X b t lz qb W regs mem md -> cd_leaf B ly X W regs mem md (tt, X2) W' c' ->
cache_dealloc_post U 0 0 0 X kBatchClass (b_self b - region_off kBatchClass) ns (tt, X2) -> QST X2 t W' c'.
Proof.
intros X b t lz qb W regs mem md X2 ns W' c' ST HL CP. destruct ST as [AC RX LEN CR LR RA A0 A1 A2 A3 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof (RIx_cd_step U 0 0 0 X t (b_self b) ns X2 RX CP) as (RX2 & FF & Hqt & Hqg & Hunq & Hck).
destruct HL as (regs' & mem' & md' & -> & (AR2 & LLE & WLE & CSV & SIO & FRM & PRS) & PU & INI). cbn [fst snd] in *.
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. img_change (bv_unsigned (w64 (0x33b38 + D_150))) with (0x33b38 + D_150). rewrite SPV in FRM, PRS.
assert (OWN2 : forall a, aowned B ly X2 a <-> aowned B ly X a) by (img_try (intros a; img_exact (aowned_cd_same B ly U 0 0 0 X kBatchClass _ ns X2 CP a))).
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK <= a < sp1) -> aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a).
{ intros a Ha Hs Hn. img_apply FRM; [img_try (img_exact Ha) | img_try (img_exact (AR_stack_law_ok tfxsegs B ly X W mem md a HAR Hs)) | img_try (img_exact (AR_stack_law_ok tfxsegs B ly X2 W' mem' md' a AR2 Hs)) | | img_try (intros F; img_exact F)].
intros [C|C]; [img_try (img_exact (Hn C))|]. rewrite (ts_errno _ TB) in C. clear - C Hs E7. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_ERRNO, kHighMemBeg in *. img_lia. }
assert (AGB : forall b' a, In b' t -> bslot ly (b_self b') a -> aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a).
{ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (img_try (img_apply (rix_slot X [] t [b_self b] b' RX); right; img_exact Hb)).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha).
img_apply PU; [img_try (clear - Ha; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in Ha; img_lia) | img_try (img_exact (slot_puser B ly X _ (b_self b') M SZ a Hs))]. }
exists lz, qb, regs', mem', md'. split; [img_refl|].
constructor.
- constructor.
+ img_exact AR2.
+ eapply wle_trans; [img_try (img_exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact WLE)].
+ img_exact (same_io_trans _ _ _ (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) SIO).
+ intros a O. img_exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a (proj1 (OWN2 a) O)).
+ intros a Ha N0 N2 NS NT. rewrite (FRM a Ha); [img_try (img_exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 ltac:(intros O; img_exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O))) NS NT)) | img_try (intros O; img_exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O))) | img_try (img_exact N2) | | img_try (intros F; img_exact F)].
intros [C|C]; img_apply NS; [img_try (left; clear - C S5; nsp; img_lia) | img_try (right; img_exact C)].
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK) sp1 a) as [C|C]; [img_try (img_exact (PRS a C))|].
img_apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [img_try (unfold YF38.SY in Ha; clear - Ha S1 S2; nsp; img_lia) | | img_try (img_exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha))].
img_apply AGS; [img_try (unfold YF38.SY in Ha; clear - Ha S1 S2; nsp; img_lia) | img_try (unfold YF38.SY in Ha; clear - Ha E1 E2; nsp; img_lia) | img_try (img_exact C)].
+ img_exact INI.
- img_exact RX2.
- img_exact LEN.
- unfold YF38.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; [img_try (csv CSV (3%bv : bv 5) 3) | img_try (csv CSV (4%bv : bv 5) 4) | img_try (csv CSV (26%bv : bv 5) 26) | img_try (csv CSV (27%bv : bv 5) 27)]; img_refl.
- unfold YF38.loop_regs. rewrite <- Q2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21.
splits; [img_try (csv CSV (2%bv : bv 5) 2) | img_try (csv CSV (8%bv : bv 5) 8) | img_try (csv CSV (9%bv : bv 5) 9) | img_try (csv CSV (18%bv : bv 5) 18) | img_try (csv CSV (19%bv : bv 5) 19) | img_try (csv CSV (21%bv : bv 5) 21)]; img_refl.
- img_apply (frame_cells_keep ly regs0 W W' mem mem'); [|img_try (img_exact FR)]. intros a Ha. img_apply AGS; [img_try (clear - Ha U0 U1 S5; nsp; img_lia) | img_try (clear - Ha E1 E2 S5; nsp; img_lia) | img_try (clear - Ha; img_lia)].
- img_apply (tmp_cells_keep ly regs0 W W' mem mem'); [|img_try (img_exact TM)]. intros a Ha. img_apply AGS; [img_try (clear - Ha U0 S2; nsp; img_lia) | img_try (clear - Ha E1 E2; nsp; img_lia) | img_try (clear - Ha S5; img_lia)].
- img_apply (batch_cells_xfer B ly t (aview tfxsegs (w_H W) mem)); [img_try (img_exact (rix_items_ok X _ t _ RX)) | img_try (img_exact AGB) | img_try (img_exact CE)].
Qed.
Lemma aregs_intro : forall regs regs',
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
aregs_preserved regs regs'.
Proof.
intros regs regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr. unfold acallee_saved in Hr.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia. clear Hr.
repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; (subst r; cbv beta).
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H2.
- replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H3.
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H4.
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H8.
- replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H9.
- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H18.
- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H19.
- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H20.
- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H21.
- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H22.
- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H23.
- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H24.
- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H25.
- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H26.
- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)). img_exact H27.
Qed.
Definition postQO (X : astate) (t : list batch) (W' : world tfxsegs) (c' : config) : Prop :=
match t with [] => dr_leaf B ly X0 W0 regs0 mem0 md0 (tt, X) W' c' | _ :: _ => OST X t W' c' end.
Local Notation v1 := (YF3g.v1 regs0).   Local Notation v8 := (YF3g.v8 regs0).   Local Notation v9 := (YF3g.v9 regs0).
Local Notation v18 := (YF3g.v18 regs0). Local Notation v19 := (YF3g.v19 regs0). Local Notation v20 := (YF3g.v20 regs0).
Local Notation v21 := (YF3g.v21 regs0). Local Notation v22 := (YF3g.v22 regs0). Local Notation v23 := (YF3g.v23 regs0).
Local Notation v24 := (YF3g.v24 regs0). Local Notation v25 := (YF3g.v25 regs0).
Lemma T_Q : forall X t lz qb W regs mem md, qst X t lz qb W regs mem md ->
SRr tfxsegs W (cfg_at tfxsegs (0x33b38 + D_150) regs mem md) (postQO X t).
Proof.
intros X t lz qb W regs mem md ST. pose proof ST as [AC RX LEN CR LR FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof (seed_Q B TB ly X0 P0 W0 regs0 mem0 md0 PRE X t lz qb W regs mem md ST) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [img_try (img_exact (YF3e.segYQ W ly regs mem md (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 (m_vm_materialized md) FH))|].
intros W' c' _ HP. unfold YF36.postQ in HP. unfold postQO.
destruct t as [|b t'].
-
rewrite zlen_nil, Z.eqb_refl in HP.
destruct HP as (-> & _ & regs' & mat & -> & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & CS).
exists regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, YF3g.v1. img_refl. }
split.
+ split; [img_try (img_apply AR_wvb; img_exact HAR)|]. split; [img_try (img_apply layout_le_refl)|]. split; [img_try (img_exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC))|]. split.
{ unfold YF3g.v8, YF3g.v9, YF3g.v18, YF3g.v19, YF3g.v20, YF3g.v21, YF3g.v22,
YF3g.v23, YF3g.v24, YF3g.v25, w64 in *. rewrite !Z_to_bv_bv_unsigned in *.
img_apply aregs_intro; try assumption.
- rewrite R2, SPV, S5. unfold YF36.YFRAME, YF38.sp0. replace (bv_unsigned (getr regs0 2) - 112 + 112) with (bv_unsigned (getr regs0 2)) by img_lia. img_apply Z_to_bv_bv_unsigned.
- rewrite <- C3; img_apply CS; cbn; tauto.
- rewrite <- C4; img_apply CS; cbn; tauto.
- rewrite <- C26; img_apply CS; cbn; tauto.
- rewrite <- C27; img_apply CS; cbn; tauto. }
split; [img_try (eapply same_io_trans; [img_exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | img_apply same_io_with_vm_backing])|]. split.
{ intros a Ha N0 N1 NS NT. img_exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT). }
intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. unfold spZ in Ha. clear - Ha. nsp. img_lia.
+ intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. unfold spZ in Ha. clear - Ha. nsp. img_lia.
-
replace (zlen (b :: t') =? 0) with false in HP by (img_try (symmetry; img_apply Z.eqb_neq; rewrite zlen_cons; unfold YF38.zlen; img_lia)).
destruct HP as (-> & _ & regs' & mat & -> & R2 & CS & R10).
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [img_refl|].
constructor.
+ constructor; [img_try (img_apply AR_wvb; img_exact HAR) | img_try (img_exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (eapply same_io_trans; [img_exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | img_apply same_io_with_vm_backing])
| img_try (img_exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC)) | img_try (img_exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC))].
+ img_exact RX.
+ discriminate.
+ img_exact LEN.
+ unfold YF38.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; img_apply CS; cbn; tauto.
+ unfold YF38.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [img_try (img_exact Q2) | img_try (img_apply CS; cbn; tauto) ..].
+ img_exact R10.
+ img_exact FR.
+ img_exact TM.
+ img_exact CE.
Qed.
End d.
End c.

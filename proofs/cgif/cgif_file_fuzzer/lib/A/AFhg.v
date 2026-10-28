(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFf2 AFh9 AFha AFhc AFhb AFhe AFhi AFhk AFhj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFhh.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhf AFhd AFhl.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, AFhd.sp1, AFhd.sp0, AFhd.SY in *; numconst.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ivl_dec : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. destruct (Z_le_gt_dec lo a); [destruct (Z_lt_ge_dec a hi); [left; lia | right; lia] | right; lia]. Qed.
Section d.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis RCC : tfib_rchunk_spec B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : dr_pre B ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Local Notation hdra := (AFhd.hdra B ly).
Local Notation zlen := (@AFhd.zlen _).
Local Notation SY := (AFhd.SY regs0).
Local Notation acc := (AFhd.acc B ly X0 W0 regs0 mem0 md0).
Local Notation common_regs := (AFhd.common_regs regs0).
Local Notation loop_regs := (AFhd.loop_regs regs0).
Local Notation frame_cells := (AFhd.frame_cells ly regs0).
Local Notation tmp_cells := (AFhd.tmp_cells ly regs0).
Local Notation ost := (AFhd.ost B ly X0 W0 regs0 mem0 md0).
Local Notation rcst := (AFhd.rcst B ly X0 W0 regs0 mem0 md0).
Local Notation rst := (AFhd.rst B ly X0 W0 regs0 mem0 md0).
Local Notation cdst := (AFhd.cdst B ly X0 W0 regs0 mem0 md0).
Local Notation qst := (AFhd.qst B ly X0 W0 regs0 mem0 md0).
Local Notation OST := (AFhd.OST B ly X0 W0 regs0 mem0 md0).
Local Notation RCST := (AFhd.RCST B ly X0 W0 regs0 mem0 md0).
Local Notation RST := (AFhd.RST B ly X0 W0 regs0 mem0 md0).
Local Notation CDST := (AFhd.CDST B ly X0 W0 regs0 mem0 md0).
Local Notation QST := (AFhd.QST B ly X0 W0 regs0 mem0 md0).
Local Notation entry_facts := (AFhl.entry_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (AFhl.sp_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Lemma AR_after_stack_write : forall X (W : world tfibsegs) mem mem' md mat (WINP : Z -> Prop),
AR tfibsegs B ly X W mem md ->
(forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) -> (forall a, WINP a \/ ~ WINP a) ->
(forall x : word, ~ WINP (bv_unsigned x) -> mem' x = mem x) ->
(forall a, WINP a -> apresent (w_H W) mem' a) ->
AR tfibsegs B ly X W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros X W mem mem' md mat WINP HA HST DEC MQ PRS. pose proof (lo_top ly (am_layout _ _ _ _ (proj1 HA))) as (_ & _ & _ & T4 & _ & _ & T7).
apply (AR_frame_law_ok tfibsegs B ly X W mem md mem' _ HA).
- intros a Ha O. apply aview_same. apply MQ. rewrite unsigned_lit_small by exact Ha. intros Hw. exact (AR_stack_law_ok tfibsegs B ly X W mem md a HA (HST a Hw) O).
- intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (mem' x) as [b'|] eqn:E'; [cbn in HN; discriminate|].
destruct (mem x) as [b0|] eqn:E0; [|exact (Hv HN)].
destruct (DEC a') as [C|C].
+ destruct (PRS a' C) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
+ rewrite (MQ x C) in E'. congruence.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. apply MQ. unfold w64. rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
intros Hw. pose proof (HST a Hw). clear - Ha H T7. unfold in_band_rw, zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.
Lemma presence_after_write : forall (W : world tfibsegs) mem mem' (WINP : Z -> Prop) a,
(forall a, WINP a \/ ~ WINP a) -> (forall x : word, ~ WINP (bv_unsigned x) -> mem' x = mem x) ->
(forall a, WINP a -> apresent (w_H W) mem' a) -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a -> apresent (w_H W) mem' a.
Proof.
intros W mem mem' WINP a DEC MQ PRS Ha HP. destruct (DEC a) as [C|C]; [exact (PRS a C)|].
apply (apresent_same (w_H W) mem mem' a); [|exact HP]. apply MQ. rewrite unsigned_lit_small by exact Ha. exact C.
Qed.
Lemma aview_after_write : forall (H : word -> bool) mem mem' (WINP : Z -> Prop) a,
(forall x : word, ~ WINP (bv_unsigned x) -> mem' x = mem x) -> 0 <= a < 2 ^ 64 -> ~ WINP a ->
aview tfibsegs H mem' a = aview tfibsegs H mem a.
Proof. intros H mem mem' WINP a MQ Ha Hn. apply aview_same. apply MQ. rewrite unsigned_lit_small by exact Ha. exact Hn. Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD.
Proof. destruct PRE as ((M & _) & _). rewrite (am_tsd B ly X0 _ M). apply (ts_tsd _ TB). Qed.
Lemma rix_slot : forall X its P selfs b, RIx U 0 0 0 X its P selfs -> (In (b_self b) selfs \/ In b P) -> slot_ok X (b_self b).
Proof.
intros X its P selfs b RX Hb. apply (RIx_slots U 0 0 0 X its P selfs _ RX). apply in_app_iff.
destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_map; exact Hb].
Qed.
Lemma rix_items_ok : forall X its P selfs, RIx U 0 0 0 X its P selfs -> items_ok P.
Proof. intros X its P selfs (_ & _ & _ & BL & _). exact BL. Qed.
Definition lastaddr (l : list batch) : Z := match rev l with [] => 0 | b :: _ => SB + b_self b end.
Lemma T_E : forall W' c', AFh9.at_OE W0 ly regs0 mem0 md0 (zlen P0) W' c' -> OST X0 P0 W' c'.
Proof.
intros W' c' HP. destruct HP as (-> & NZ & regs & mem & mat & -> & R2 & CS & R8 & R9 & R18 & R19 & R21 & R10 & MQ & PRS & CB & SV).
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (RI_RIx U 0 0 0 X0 P0 HRI) as RX.
assert (WST : forall a, AFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold AFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, AFh9.WIN regs0 a \/ ~ AFh9.WIN regs0 a) by (intros a; unfold AFh9.WIN; apply ivl_dec).
assert (WSY : forall a, AFh9.WIN regs0 a -> SY a) by (intros a Ha; unfold AFh9.WIN in Ha; unfold AFhd.SY; clear - Ha; nsp; lia).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFh9.WIN regs0 a -> aview tfibsegs (w_H W0) mem a = aview tfibsegs (w_H W0) mem0 a).
{ intros a Ha Hn. exact (aview_after_write (w_H W0) mem0 mem _ a MQ Ha Hn). }
unfold plist_cells, qc_cells in CELLS. cbn [qc_list qc_bytes] in CELLS.
apply Forall_cons_iff in CELLS as [C0 CELLS]. apply Forall_cons_iff in CELLS as [C8 CELLS]. apply Forall_cons_iff in CELLS as [C16 CELLS]. apply Forall_cons_iff in CELLS as [C24 CB0].
assert (AGT : forall a, sp0 <= a < sp0 + 32 -> aview tfibsegs (w_H W0) mem a = aview tfibsegs (w_H W0) mem0 a).
{ intros a Ha. apply AG; [clear - Ha U0 S2; nsp; lia|]. unfold AFh9.WIN. clear - Ha. nsp. lia. }
assert (LZR : 0 <= lastaddr P0 < ASAN_CEIL).
{ unfold lastaddr. destruct (rev P0) as [|bl initr] eqn:ER; [ceil; unfold ASAN_CEIL; lia|].
assert (Hbl : In bl P0) by (apply in_rev; rewrite ER; left; reflexivity).
pose proof (slot_facts B ly X0 _ (b_self bl) M (rix_slot X0 [] P0 [] bl RX (or_intror Hbl))) as (B1 & B2 & _).
clear - B1 B2. numconst. lia. }
exists (lastaddr P0), (sum_bytes P0 mod 2 ^ 64), regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split; [reflexivity|].
constructor.
-   constructor.
+ exact (AR_after_stack_write X0 W0 mem0 mem md0 mat _ HAR WST WDEC MQ PRS).
+ apply wle_refl.
+ apply same_io_with_vm_backing.
+ intros a O; exact O.
+ intros a Ha _ _ NS _. apply AG; [exact Ha|]. intros Hw. apply NS. left. unfold spZ, AFh9.WIN in *. clear - Hw. nsp. lia.
+ intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia|].
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
+ eapply val_mem_keep; [|exact (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C0)]. cbn [aeval]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C8) as V; cbn [aeval aoff] in V; destruct P0 as [|b0 P']; cbn [aeval batch_exp firstaddr] in V |- *; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C16) as V; cbn [aeval aoff] in V; unfold lastaddr; destruct (rev P0) as [|bl initr]; cbn [aeval batch_exp] in V |- *; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|apply val_mem_mod64; pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C24) as V; cbn [aeval aoff] in V; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ exact LZR.
+ apply mod64_range.
- apply (batch_cells_xfer B ly P0 (aview tfibsegs (w_H W0) mem0)); [exact (rix_items_ok X0 [] P0 [] RX) | | exact CB0].
intros b a Hb Hs. pose proof (rix_slot X0 [] P0 [] b RX (or_intror Hb)) as SZ.
pose proof (slot_high B ly X0 _ (b_self b) M SZ a Hs) as (_ & _ & Ha). apply AG; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia|]. intros Hw.
exact (slot_not_stack B ly X0 _ (b_self b) M SZ a Hs (WST a Hw)).
Qed.
Lemma csv_get : forall regs regs', aregs_preserved regs regs' -> forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' CS r z Hz <-. exact (CS z Hz). Qed.
Ltac csv CS r z := rewrite (csv_get _ _ CS r z ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
Lemma T_O : forall X b t lz qb W regs mem md, ost X (b :: t) lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x334ac regs mem md) (RCST X b t (b_items b) 0).
Proof.
intros X b t lz qb W regs mem md ST. pose proof ST as [AC RX NE LEN CR LR A0 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV.
pose proof (RIx_open U 0 0 0 X b t RX) as [RXo BL].
destruct (b_items b) as [|k0 ks] eqn:Hk0; [cbn in BL; lia|]. rewrite <- Hk0 in *.
pose proof (seed_O B TB ly X0 P0 W0 regs0 mem0 md0 PRE X b t lz qb W regs mem md k0 ks ST Hk0) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhi.segYO W ly regs mem md _ _ _ _ _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. destruct HP as (-> & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R20 & R22 & R23 & R24 & R25 & MQ & PRS & CELLS). cbv zeta in CELLS.
destruct CELLS as (V0 & V8 & V16 & V24). rewrite SPV in *.
set (WINP := AFha.WIN regs) in *.
assert (WE : forall a, WINP a <-> sp0 <= a < sp0 + 32) by (intros a; subst WINP; unfold AFha.WIN; rewrite SPV; clear - S5; nsp; lia).
assert (WST : forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; apply WE in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, WINP a \/ ~ WINP a) by (intros a; subst WINP; unfold AFha.WIN; apply ivl_dec).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ WINP a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. exact (aview_after_write (w_H W) mem mem' _ a MQ Ha Hn). }
pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof CR as (C3 & C4 & C26 & C27).
exists (AFha.LZn (firstaddr ly t) lz), (zcanon (qb - b_bytes b mod 2 ^ 64)), regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb).
constructor.
- constructor.
+ exact (AR_after_stack_write X W mem mem' md mat WINP HAR WST WDEC MQ PRS).
+ exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC).
+ eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing].
+ exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC).
+ intros a Ha N0 N1 NS NT. rewrite (AG a Ha) by (intros Hw; apply WE in Hw; exact (NT Hw)). exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT).
+ intros a Ha. apply (presence_after_write W mem mem' WINP a WDEC MQ PRS); [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia|]. exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha).
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
- apply (frame_cells_keep ly regs0 W W mem mem'); [|exact FR]. intros a Ha. apply AG; [clear - Ha S5 U0 U1; nsp; lia|]. intros Hw. apply WE in Hw. clear - Ha Hw S5. nsp. lia.
- unfold AFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_addr; [exact V0 | rewrite zlen_cons; lia] || (replace (zlen t) with (zlen (b :: t) - 1) by (rewrite zlen_cons; lia); eapply val_mem_addr; [exact V0 | clear - S5; nsp; lia]).
+ eapply val_mem_addr; [exact V8 | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V16 | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V24 | clear - S5; nsp; lia].
+ unfold AFha.LZn. destruct (firstaddr ly t =? 0); [ceil; unfold ASAN_CEIL; lia | exact Rlz].
+ unfold zcanon, M64. apply Z.mod_pos_bound. lia.
- apply (batch_cells_xfer B ly (b :: t) (aview tfibsegs (w_H W) mem)); [| | exact CE].
+ constructor; [exact BL | exact (rix_items_ok X [] (b :: t) [] RX) ] || (unfold items_ok; constructor; [exact BL | exact (rix_items_ok X _ t _ RXo)]).
+ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (apply (rix_slot X [] (b :: t) [] b' RX); right; exact Hb).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha). apply AG; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia|]. intros Hw.
exact (slot_not_stack B ly X _ (b_self b') M SZ a Hs (WST a Hw)).
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
unfold rcc_pre, spZ, raZ. rewrite SPV, RA. change (bv_unsigned (w64 0x334f8)) with 0x334f8.
splits.
- exact HAR.
- exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- exact Hk.
- exact Hst.
- exact Hni.
- vm_compute. reflexivity.
- lia.
- exact S7.
- clear - E1 S5. nsp. lia.
- lia.
- clear - E2 S5. nsp. lia.
- rewrite S5. replace (sp0 - 112 + 8) with (sp0 + (-13) * 8) by lia. rewrite Z_mod_plus_full. clear - S6. apply Z.mod_divide; [lia|]. apply Z.mod_divide in S6 as [q Hq]; [|lia]. exists (2 * q). lia.
- intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold AFhd.SY. clear - Ha S5. nsp. lia.
- intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold AFhd.SY. clear - Ha S5. nsp. lia.
- eapply val_mem_addr; [exact CB | reflexivity].
- rewrite C3. exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). reflexivity.
- exact A0.
- rewrite (A1 k ks eq_refl). f_equal. unfold kChunkHeaderSize in I0. unfold kChunkHeaderSize. lia.
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
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. change (bv_unsigned (w64 0x334f8)) with 0x334f8. rewrite SPV in FRM, PRS.
pose proof AR1 as (M1 & _).
assert (OWN1 : forall a, aowned B ly X1 a -> aowned B ly X a) by (intros a; exact (aowned_rc_back B ly U 0 0 0 X k ns X1 Hst RP a)).
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK <= a < sp1) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hs Hn. apply FRM; [exact Ha | exact (AR_stack_law_ok tfibsegs B ly X W mem md a HAR Hs) | exact (AR_stack_law_ok tfibsegs B ly X1 W' mem' md' a AR1 Hs) | | intros F; exact F].
intros [C|C]; [exact (Hn C)|]. rewrite (ts_errno _ TB) in C. clear - C Hs E7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, kHighMemBeg in *. lia. }
assert (AGB : forall b' a, In b' (b :: t) -> bslot ly (b_self b') a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (apply (rix_slot X (k :: ks) t [b_self b] b' RX); destruct Hb as [<-|Hb]; [left; left; reflexivity | right; exact Hb]).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha).
apply PU; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia | exact (slot_puser B ly X _ (b_self b') M SZ a Hs) | exact (slot_vs_chunk B ly X _ (b_self b') k M SZ Hk a Hs)]. }
exists lz, qb, regs', mem', md'. split; [reflexivity|].
destruct ITS as (done & Hits & Hdone).
constructor.
- constructor.
+ exact AR1.
+ eapply wle_trans; [exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | exact WLE].
+ exact (same_io_trans _ _ _ (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) SIO).
+ intros a O. exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a (OWN1 a O)).
+ intros a Ha N0 N1 NS NT. rewrite (FRM a Ha); [exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 ltac:(intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O))) NS NT) | intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O)) | exact N1 | | intros F; exact F].
intros [C|C]; apply NS; [left; clear - C S5; nsp; lia | right; exact C].
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK) sp1 a) as [C|C]; [exact (PRS a C)|].
apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia | | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha)].
apply AGS; [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia | unfold AFhd.SY in Ha; clear - Ha E1 E2; nsp; lia | exact C].
+ exact INI.
- exact RX1.
- exists (done ++ [k]). split; [rewrite Hits, <- app_assoc; reflexivity | rewrite length_app, Hdone; cbn; lia].
- lia.
- exact BL.
- exact LEN.
- unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; [csv CSV (3%bv : bv 5) 3 | csv CSV (4%bv : bv 5) 4 | csv CSV (26%bv : bv 5) 26 | csv CSV (27%bv : bv 5) 27]; reflexivity.
- unfold AFhd.loop_regs. rewrite <- Q2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21.
splits; [csv CSV (2%bv : bv 5) 2 | csv CSV (8%bv : bv 5) 8 | csv CSV (9%bv : bv 5) 9 | csv CSV (18%bv : bv 5) 18 | csv CSV (19%bv : bv 5) 19 | csv CSV (21%bv : bv 5) 21]; reflexivity.
- unfold AFhd.batch_regs. rewrite <- R20, <- R22, <- R24. splits; [csv CSV (20%bv : bv 5) 20 | csv CSV (22%bv : bv 5) 22 | csv CSV (24%bv : bv 5) 24]; reflexivity.
- csv CSV (23%bv : bv 5) 23. rewrite S7r. f_equal. lia.
- csv CSV (25%bv : bv 5) 25. rewrite S9r. f_equal. lia.
- apply (frame_cells_keep ly regs0 W W' mem mem'); [|exact FR]. intros a Ha. apply AGS; [clear - Ha U0 U1 S5; nsp; lia | clear - Ha E1 E2 S5; nsp; lia | clear - Ha; lia].
- apply (tmp_cells_keep ly regs0 W W' mem mem'); [|exact TM]. intros a Ha. apply AGS; [clear - Ha U0 S2; nsp; lia | clear - Ha E1 E2; nsp; lia | clear - Ha S5; lia].
- apply (batch_cells_xfer B ly (b :: t) (aview tfibsegs (w_H W) mem)); [| exact AGB | exact CE].
unfold items_ok. constructor; [exact BL | exact (rix_items_ok X _ t _ RX)].
Qed.
Definition postRI (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfibsegs) (c' : config) : Prop :=
match its with [] => CDST X b t W' c' | _ :: _ => RCST X b t its i W' c' end.
Lemma T_R : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x334f8 regs mem md) (postRI X b t its i).
Proof.
intros X b t its i lz qb W regs mem md ST. pose proof ST as [AC RX ITS Hi BL LEN CR LR BR S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (seed_R B TB ly X0 P0 W0 regs0 mem0 md0 PRE X b t its i lz qb W regs mem md ST) as FH.
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (rewrite Hits, zlen_app; unfold AFhd.zlen; rewrite Hdone; lia).
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhk.segYR W ly regs mem md _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold AFhc.postR in HP. unfold postRI.
destruct its as [|k ks].
-
rewrite zlen_nil in LENi. replace (Z.of_nat i <? zlen (b_items b)) with false in HP by (symmetry; apply Z.ltb_ge; lia).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R12 & R13 & MQ).
assert (MM : mem' = mem) by (apply functional_extensionality; intros x; apply MQ; intros []). subst mem'.
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
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
Lemma CD_pre : forall X b t lz qb W regs mem md, cdst X b t lz qb W regs mem md -> cd_pre B ly X kBatchClass (b_self b) W regs mem md.
Proof.
intros X b t lz qb W regs mem md ST. destruct ST as [AC RX LEN CR LR RA A0 A1 A2 A3 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27).
pose proof (RIx_cd_pre U 0 0 0 X t (b_self b) [] RX) as (WP & Z1 & Z2 & Z3 & RM).
unfold cd_pre, spZ, raZ. rewrite SPV, RA. change (bv_unsigned (w64 0x33530)) with 0x33530. rewrite bslack_24.
splits.
- exact HAR.
- exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- unfold kBatchClass; lia.
- unfold kBatchClass; lia.
- exact (proj1 Z1).
- exact (proj2 Z1).
- exact Z2.
- exact Z3.
- exact RM.
- vm_compute. reflexivity.
- lia.
- exact S7.
- clear - E1 S5. nsp. lia.
- clear - E2 S5. nsp. lia.
- intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold AFhd.SY. clear - Ha S5. nsp. lia.
- rewrite C3. exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). reflexivity.
- exact A0.
- exact A1.
- exact A2.
- exact A3.
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
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. change (bv_unsigned (w64 0x33530)) with 0x33530. rewrite SPV in FRM, PRS.
assert (OWN2 : forall a, aowned B ly X2 a <-> aowned B ly X a) by (intros a; exact (aowned_cd_same B ly U 0 0 0 X kBatchClass _ ns X2 CP a)).
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK <= a < sp1) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hs Hn. apply FRM; [exact Ha | exact (AR_stack_law_ok tfibsegs B ly X W mem md a HAR Hs) | exact (AR_stack_law_ok tfibsegs B ly X2 W' mem' md' a AR2 Hs) | | intros F; exact F].
intros [C|C]; [exact (Hn C)|]. rewrite (ts_errno _ TB) in C. clear - C Hs E7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, kHighMemBeg in *. lia. }
assert (AGB : forall b' a, In b' t -> bslot ly (b_self b') a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (apply (rix_slot X [] t [b_self b] b' RX); right; exact Hb).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha).
apply PU; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia | exact (slot_puser B ly X _ (b_self b') M SZ a Hs)]. }
exists lz, qb, regs', mem', md'. split; [reflexivity|].
constructor.
- constructor.
+ exact AR2.
+ eapply wle_trans; [exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | exact WLE].
+ exact (same_io_trans _ _ _ (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) SIO).
+ intros a O. exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a (proj1 (OWN2 a) O)).
+ intros a Ha N0 N2 NS NT. rewrite (FRM a Ha); [exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 ltac:(intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O))) NS NT) | intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O)) | exact N2 | | intros F; exact F].
intros [C|C]; apply NS; [left; clear - C S5; nsp; lia | right; exact C].
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK) sp1 a) as [C|C]; [exact (PRS a C)|].
apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia | | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha)].
apply AGS; [unfold AFhd.SY in Ha; clear - Ha S1 S2; nsp; lia | unfold AFhd.SY in Ha; clear - Ha E1 E2; nsp; lia | exact C].
+ exact INI.
- exact RX2.
- exact LEN.
- unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; [csv CSV (3%bv : bv 5) 3 | csv CSV (4%bv : bv 5) 4 | csv CSV (26%bv : bv 5) 26 | csv CSV (27%bv : bv 5) 27]; reflexivity.
- unfold AFhd.loop_regs. rewrite <- Q2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21.
splits; [csv CSV (2%bv : bv 5) 2 | csv CSV (8%bv : bv 5) 8 | csv CSV (9%bv : bv 5) 9 | csv CSV (18%bv : bv 5) 18 | csv CSV (19%bv : bv 5) 19 | csv CSV (21%bv : bv 5) 21]; reflexivity.
- apply (frame_cells_keep ly regs0 W W' mem mem'); [|exact FR]. intros a Ha. apply AGS; [clear - Ha U0 U1 S5; nsp; lia | clear - Ha E1 E2 S5; nsp; lia | clear - Ha; lia].
- apply (tmp_cells_keep ly regs0 W W' mem mem'); [|exact TM]. intros a Ha. apply AGS; [clear - Ha U0 S2; nsp; lia | clear - Ha E1 E2; nsp; lia | clear - Ha S5; lia].
- apply (batch_cells_xfer B ly t (aview tfibsegs (w_H W) mem)); [exact (rix_items_ok X _ t _ RX) | exact AGB | exact CE].
Qed.
Lemma aregs_intro : forall regs regs',
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
aregs_preserved regs regs'.
Proof.
intros regs regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr. unfold acallee_saved in Hr.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; subst r.
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H2.
- replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H3.
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H4.
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H8.
- replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H9.
- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H18.
- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H19.
- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H20.
- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H21.
- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H22.
- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H23.
- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H24.
- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H25.
- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H26.
- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H27.
Qed.
Definition postQO (X : astate) (t : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
match t with [] => dr_leaf B ly X0 W0 regs0 mem0 md0 (tt, X) W' c' | _ :: _ => OST X t W' c' end.
Local Notation v1 := (AFhl.v1 regs0).   Local Notation v8 := (AFhl.v8 regs0).   Local Notation v9 := (AFhl.v9 regs0).
Local Notation v18 := (AFhl.v18 regs0). Local Notation v19 := (AFhl.v19 regs0). Local Notation v20 := (AFhl.v20 regs0).
Local Notation v21 := (AFhl.v21 regs0). Local Notation v22 := (AFhl.v22 regs0). Local Notation v23 := (AFhl.v23 regs0).
Local Notation v24 := (AFhl.v24 regs0). Local Notation v25 := (AFhl.v25 regs0).
Lemma T_Q : forall X t lz qb W regs mem md, qst X t lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x33530 regs mem md) (postQO X t).
Proof.
intros X t lz qb W regs mem md ST. pose proof ST as [AC RX LEN CR LR FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof (seed_Q B TB ly X0 P0 W0 regs0 mem0 md0 PRE X t lz qb W regs mem md ST) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhj.segYQ W ly regs mem md (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold AFhb.postQ in HP. unfold postQO.
destruct t as [|b t'].
-
rewrite zlen_nil, Z.eqb_refl in HP.
destruct HP as (-> & _ & regs' & mat & -> & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & CS).
exists regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, AFhl.v1. reflexivity. }
split.
+ split; [apply AR_wvb; exact HAR|]. split; [apply layout_le_refl|]. split; [exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)|]. split.
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
+ intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold AFhd.SY. unfold spZ in Ha. clear - Ha. nsp. lia.
-
replace (zlen (b :: t') =? 0) with false in HP by (symmetry; apply Z.eqb_neq; rewrite zlen_cons; unfold AFhd.zlen; lia).
destruct HP as (-> & _ & regs' & mat & -> & R2 & CS & R10).
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
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
End d.
End c.

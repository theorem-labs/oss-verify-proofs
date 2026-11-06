(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1dc.v (a working branch ced28ed2383, file sha256 f756f365d156) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 11 image addresses moved by code-verified function pairs (11 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: moved from ced28ed2383 to a Theorem Labs lane's c5 install head a working branch 57e82b93d43 (cgif file sha256 26d66d72d22f; the errno-kept twins of ad994c27165, additive). By 3-way merge (base = agreloc of ced28ed2383, theirs = agreloc of 57e82b93d43 with port_addr_check 16f8a030c869 PREDICT rows for it, ours = this file's image-B rows and L edits). *)
(* Modified by Theorem Labs, 2026-10: the transitions of cgif_file's released DoRecycle walk (YFhg.v: T_E, T_O, T_R,
   T_Q, RC_pre / RC_post, CD_pre / CD_post) restated over the states of DGif1da.v: each transition also carries the raw
   frame (from the segments' raw MEQ, or the callee's raw frame clause), and the recycle callees are entered and left
   in the types of DMiface.di_rchunk_t / di_cdealloc_t at the cgif instantiation (KSTACK_CF window, no model
   conjuncts; the recycle invariant in DRq's folded form). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFeq YFew YFeu YFf2 YFh9 YFha YFhc YFhb YFhe YFhi YFhk YFhj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFhf YFhd YFhl YFhg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DGif1da DGif1db.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, DRSTACK_X, KSTACK, KSTACK_CF, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, YFh9.YFRAME, YFha.YFRAME, YFhc.YFRAME, YFhb.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, YFhd.sp1, YFhd.sp0, DGif1da.SY in *; numconst.
Ltac csv CS r z := rewrite (YFhg.csv_get _ _ CS r z ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : dr_pre B ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Hypothesis HSTK : ly_stk_lo ly + DRSTACK_X <= sp0.
Hypothesis HPRX : forall a, sp0 - DRSTACK_X <= a < sp0 -> apresent (w_H W0) mem0 a.
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Local Notation hdra := (YFhd.hdra B ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation SY := (DGif1da.SY regs0).
Local Notation acc := (DGif1da.acc B ly X0 W0 regs0 mem0 md0).
Local Notation common_regs := (YFhd.common_regs regs0).
Local Notation loop_regs := (YFhd.loop_regs regs0).
Local Notation frame_cells := (YFhd.frame_cells ly regs0).
Local Notation tmp_cells := (YFhd.tmp_cells ly regs0).
Local Notation ost := (DGif1da.ost B ly X0 W0 regs0 mem0 md0).
Local Notation rcst := (DGif1da.rcst B ly X0 W0 regs0 mem0 md0).
Local Notation rst := (DGif1da.rst B ly X0 W0 regs0 mem0 md0).
Local Notation cdst := (DGif1da.cdst B ly X0 W0 regs0 mem0 md0).
Local Notation qst := (DGif1da.qst B ly X0 W0 regs0 mem0 md0).
Local Notation OST := (DGif1da.OST B ly X0 W0 regs0 mem0 md0).
Local Notation RCST := (DGif1da.RCST B ly X0 W0 regs0 mem0 md0).
Local Notation RST := (DGif1da.RST B ly X0 W0 regs0 mem0 md0).
Local Notation CDST := (DGif1da.CDST B ly X0 W0 regs0 mem0 md0).
Local Notation QST := (DGif1da.QST B ly X0 W0 regs0 mem0 md0).
Local Notation entry_facts := (YFhl.entry_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (YFhl.sp_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation AR_after_stack_write := (YFhg.AR_after_stack_write B ly).
Local Notation rix_slot := (YFhg.rix_slot B).
Local Notation rix_items_ok := (YFhg.rix_items_ok B).
Local Notation lastaddr := (YFhg.lastaddr ly).
Local Notation HTSD := (YFhg.HTSD B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Lemma T_E : forall W' c', YFh9.at_OE W0 ly regs0 mem0 md0 (zlen P0) W' c' -> OST X0 P0 W' c'.
Proof.
intros W' c' HP. destruct HP as (-> & NZ & regs & mem & mat & -> & R2 & CS & R8 & R9 & R18 & R19 & R21 & R10 & MQ & PRS & CB & SV).
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (RI_RIx U 0 0 0 X0 P0 HRI) as RX.
assert (WST : forall a, YFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold YFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, YFh9.WIN regs0 a \/ ~ YFh9.WIN regs0 a) by (intros a; unfold YFh9.WIN; apply ivl_dec).
assert (WSY : forall a, YFh9.WIN regs0 a -> SY a) by (intros a Ha; unfold YFh9.WIN in Ha; unfold DGif1da.SY; clear - Ha; nsp; lia).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YFh9.WIN regs0 a -> aview tfibsegs (w_H W0) mem a = aview tfibsegs (w_H W0) mem0 a).
{ intros a Ha Hn. exact (aview_after_write (w_H W0) mem0 mem _ a MQ Ha Hn). }
unfold plist_cells, qc_cells in CELLS. cbn [qc_list qc_bytes] in CELLS.
apply Forall_cons_iff in CELLS as [C0 CELLS]. apply Forall_cons_iff in CELLS as [C8 CELLS]. apply Forall_cons_iff in CELLS as [C16 CELLS]. apply Forall_cons_iff in CELLS as [C24 CB0].
assert (AGT : forall a, sp0 <= a < sp0 + 32 -> aview tfibsegs (w_H W0) mem a = aview tfibsegs (w_H W0) mem0 a).
{ intros a Ha. apply AG; [clear - Ha U0 S2; nsp; lia|]. unfold YFh9.WIN. clear - Ha. nsp. lia. }
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
+ intros a Ha _ _ NS _. apply AG; [exact Ha|]. intros Hw. apply NS. left. unfold spZ, YFh9.WIN in *. clear - Hw. nsp. lia.
+ intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [unfold DGif1da.SY in Ha; clear - Ha S1 S2; nsp; lia|].
unfold DGif1da.SY in Ha. destruct (Z_lt_le_dec a (sp0 - DRSTACK)) as [LA|LA]; [apply HPRX; clear - Ha LA; nsp; lia | apply HPRES; unfold YFhd.sp0 in *; clear - Ha LA; nsp; lia].
+ exact INIT0.
+ intros x _ _ NS _. apply MQ. intros Hw. apply NS. left. unfold spZ, YFh9.WIN in *. clear - Hw. nsp. lia.
- exact RX.
- intros ->. apply NZ. reflexivity.
- unfold YFhd.zlen. exact LENP.
- unfold YFhd.common_regs. splits; apply CS; cbn; tauto.
- unfold YFhd.loop_regs. splits; try assumption; rewrite R2; unfold YFhd.sp1; reflexivity.
- exact R10.
- split; [| exact SV]. eapply val_mem_addr; [exact CB | clear; nsp; lia].
- unfold YFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
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
(* T_O with the segment's raw MEQ exported: outside the 32 bytes at sp0 the memory is unchanged. *)
Lemma T_O_m : forall X b t lz qb W regs mem md, ost X (b :: t) lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x340fc regs mem md) (fun W' c' => RCST X b t (b_items b) 0 W' c' /\
  forall x : word, ~ (sp0 <= bv_unsigned x < sp0 + 32) -> ms_mem (cfg_ms c') x = mem x).
Proof.
intros X b t lz qb W regs mem md ST. pose proof ST as [AC RX NE LEN CR LR A0 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV.
pose proof (RIx_open U 0 0 0 X b t RX) as [RXo BL].
destruct (b_items b) as [|k0 ks] eqn:Hk0; [cbn in BL; lia|]. rewrite <- Hk0 in *.
pose proof (seed_O B TB ly X0 P0 W0 regs0 mem0 md0 PRE X b t lz qb W regs mem md k0 ks ST Hk0) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (YFhi.segYO W ly regs mem md _ _ _ _ _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. destruct HP as (-> & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R20 & R22 & R23 & R24 & R25 & MQ & PRS & CELLS). cbv zeta in CELLS.
destruct CELLS as (V0 & V8 & V16 & V24). rewrite SPV in *.
set (WINP := YFha.WIN regs) in *.
assert (WE : forall a, WINP a <-> sp0 <= a < sp0 + 32) by (intros a; subst WINP; unfold YFha.WIN; rewrite SPV; clear - S5; nsp; lia).
assert (WST : forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; apply WE in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, WINP a \/ ~ WINP a) by (intros a; subst WINP; unfold YFha.WIN; apply ivl_dec).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ WINP a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. exact (aview_after_write (w_H W) mem mem' _ a MQ Ha Hn). }
split; [|intros x Hx; change (mem' x = mem x); apply MQ; intros Hw; apply WE in Hw; exact (Hx Hw)].
pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof CR as (C3 & C4 & C26 & C27).
exists (YFha.LZn (firstaddr ly t) lz), (zcanon (qb - b_bytes b mod 2 ^ 64)), regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb).
constructor.
- constructor.
+ exact (AR_after_stack_write X W mem mem' md mat WINP HAR WST WDEC MQ PRS).
+ exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC).
+ eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing].
+ exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC).
+ intros a Ha N0 N1 NS NT. rewrite (AG a Ha) by (intros Hw; apply WE in Hw; exact (NT Hw)). exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 N1 NS NT).
+ intros a Ha. apply (presence_after_write W mem mem' WINP a WDEC MQ PRS); [unfold DGif1da.SY in Ha; clear - Ha S1 S2; nsp; lia|]. exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha).
+ exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
+ intros x N0 N1 NS NT. rewrite (MQ x) by (intros Hw; apply WE in Hw; exact (NT Hw)). exact (acc_raw _ _ _ _ _ _ _ _ _ _ _ AC x N0 N1 NS NT).
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
- apply (frame_cells_keep ly regs0 W W mem mem'); [|exact FR]. intros a Ha. apply AG; [clear - Ha S5 U0 U1; nsp; lia|]. intros Hw. apply WE in Hw. clear - Ha Hw S5. nsp. lia.
- unfold YFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_addr; [exact V0 | rewrite zlen_cons; lia] || (replace (zlen t) with (zlen (b :: t) - 1) by (rewrite zlen_cons; lia); eapply val_mem_addr; [exact V0 | clear - S5; nsp; lia]).
+ eapply val_mem_addr; [exact V8 | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V16 | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V24 | clear - S5; nsp; lia].
+ unfold YFha.LZn. destruct (firstaddr ly t =? 0); [ceil; unfold ASAN_CEIL; lia | exact Rlz].
+ unfold zcanon, M64. apply Z.mod_pos_bound. lia.
- apply (batch_cells_xfer B ly (b :: t) (aview tfibsegs (w_H W) mem)); [| | exact CE].
+ constructor; [exact BL | exact (rix_items_ok X [] (b :: t) [] RX) ] || (unfold items_ok; constructor; [exact BL | exact (rix_items_ok X _ t _ RXo)]).
+ intros b' a Hb Hs. assert (SZ : slot_ok X (b_self b')) by (apply (rix_slot X [] (b :: t) [] b' RX); right; exact Hb).
pose proof (slot_high B ly X _ (b_self b') M SZ a Hs) as (_ & _ & Ha). apply AG; [clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ha; lia|]. intros Hw.
exact (slot_not_stack B ly X _ (b_self b') M SZ a Hs (WST a Hw)).
Qed.
Lemma T_O : forall X b t lz qb W regs mem md, ost X (b :: t) lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x340fc regs mem md) (RCST X b t (b_items b) 0).
Proof.
intros X b t lz qb W regs mem md ST.
eapply SRr_mono; [exact (T_O_m X b t lz qb W regs mem md ST)|]. intros W' c' _ [HR _]. exact HR.
Qed.
Lemma RC_pre_x : forall X b t k ks i lz qb W regs mem md, rcst X b t (k :: ks) i lz qb W regs mem md ->
rcc_pre_x B (ARX_cgif B) TFIB_INST ly X k (sp1 + 8) W regs mem md /\
RIx U 0 0 0 X (k :: (ks ++ flat_map b_items t)) [] (b_self b :: map b_self t).
Proof.
intros X b t k ks i lz qb W regs mem md ST. destruct ST as [AC RX ITS NE BL LEN CR LR BR RA A0 A1 S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27).
pose proof (RIx_head U 0 0 0 X k ks t [b_self b] RX) as (WP & Hk & Hst & Hni).
pose proof (item_facts B ly X _ k M Hk) as (I0 & I1 & I2 & I3 & I4).
destruct FR as [CB SV].
split; [|exact (RIx_fold U X (k :: ks) t [b_self b] RX)].
unfold rcc_pre_x, spZ, raZ. rewrite SPV, RA. change (bv_unsigned (w64 0x34148)) with 0x34148.
splits.
- split; [reflexivity | exact HAR].
- exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- vm_compute. reflexivity.
- lia.
- exact S7.
- clear - HSTK S5. nsp. lia.
- lia.
- clear - E2 S5. nsp. lia.
- rewrite S5. replace (sp0 - 112 + 8) with (sp0 + (-13) * 8) by lia. rewrite Z_mod_plus_full. clear - S6. apply Z.mod_divide; [lia|]. apply Z.mod_divide in S6 as [q Hq]; [|lia]. exists (2 * q). lia.
- intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. clear - Ha S5. nsp. lia.
- intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. clear - Ha S5. nsp. lia.
- eapply val_mem_addr; [exact CB | reflexivity].
- rewrite C3. exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). reflexivity.
- exact A0.
- rewrite (A1 k ks eq_refl). f_equal. unfold kChunkHeaderSize in I0. unfold kChunkHeaderSize. lia.
Qed.
Lemma RC_post_x : forall X b t k ks i lz qb W regs mem md (r : unit * astate) W' c',
rcst X b t (k :: ks) i lz qb W regs mem md ->
(exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B (ARX_cgif B) (aowned B) TFIB_INST KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B (aowned B) TFIB_INST KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, puser ly X a -> puser ly (snd r) a) /\
  RIx U 0 0 0 (snd r) (ks ++ flat_map b_items t) [] (b_self b :: map b_self t) /\ st_cache_inited (snd r) = true /\
  (forall a, aowned B ly (snd r) a -> aowned B ly X a)) ->
RST (snd r) b t ks (S i) W' c'.
Proof.
intros X b t k ks i lz qb W regs mem md [ru X1] W' c' ST HL. destruct ST as [AC RX ITS NE BL LEN CR LR BR RA A0 A1 S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (RIx_head U 0 0 0 X k ks t [b_self b] RX) as (WP & Hk & Hst & Hni).
destruct HL as (regs' & mem' & md' & -> & ([_ AR1] & LLE & WLE & CSV & SIO & FRM & PRS) & RAW & PU & PM & DRQ & INI & OWN1). cbn [fst snd] in *.
unfold acall_raw_x in RAW.
pose proof (RIx_unfold U X1 ks t [b_self b] DRQ (rix_items_ok X _ t _ RX)) as RX1.
cbn [ImgBase.im_segs AImg_cgif] in FRM.
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. change (bv_unsigned (w64 0x34148)) with 0x34148. rewrite SPV in FRM, RAW, PRS.
pose proof AR1 as (M1 & _).
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK_CF <= a < sp1) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
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
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK_CF) sp1 a) as [C|C]; [exact (PRS a C)|].
apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [unfold DGif1da.SY in Ha; clear - Ha S1 S2; nsp; lia | | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha)].
apply AGS; [unfold DGif1da.SY in Ha; clear - Ha S1 S2; nsp; lia | unfold DGif1da.SY in Ha; clear - Ha E1 E2 HSTK; nsp; lia | exact C].
+ exact INI.
+ intros x N0 N1 NS NT. rewrite (RAW x); [exact (acc_raw _ _ _ _ _ _ _ _ _ _ _ AC x N0 ltac:(intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC _ O))) NS NT) | intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC _ O)) | exact N1 | | intros F; exact F].
intros [C|C]; apply NS; [left; clear - C S5; nsp; lia | right; exact C].
- exact RX1.
- exists (done ++ [k]). split; [rewrite Hits, <- app_assoc; reflexivity | rewrite length_app, Hdone; cbn; lia].
- lia.
- exact BL.
- exact LEN.
- unfold YFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; [csv CSV (3%bv : bv 5) 3 | csv CSV (4%bv : bv 5) 4 | csv CSV (26%bv : bv 5) 26 | csv CSV (27%bv : bv 5) 27]; reflexivity.
- unfold YFhd.loop_regs. rewrite <- Q2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21.
splits; [csv CSV (2%bv : bv 5) 2 | csv CSV (8%bv : bv 5) 8 | csv CSV (9%bv : bv 5) 9 | csv CSV (18%bv : bv 5) 18 | csv CSV (19%bv : bv 5) 19 | csv CSV (21%bv : bv 5) 21]; reflexivity.
- unfold YFhd.batch_regs. rewrite <- R20, <- R22, <- R24. splits; [csv CSV (20%bv : bv 5) 20 | csv CSV (22%bv : bv 5) 22 | csv CSV (24%bv : bv 5) 24]; reflexivity.
- csv CSV (23%bv : bv 5) 23. rewrite S7r. f_equal. lia.
- csv CSV (25%bv : bv 5) 25. rewrite S9r. f_equal. lia.
- apply (frame_cells_keep ly regs0 W W' mem mem'); [|exact FR]. intros a Ha. apply AGS; [clear - Ha U0 U1 S5; nsp; lia | clear - Ha E1 E2 S5; nsp; lia | clear - Ha; lia].
- apply (tmp_cells_keep ly regs0 W W' mem mem'); [|exact TM]. intros a Ha. apply AGS; [clear - Ha U0 S2; nsp; lia | clear - Ha E1 E2; nsp; lia | clear - Ha S5; nsp; lia].
- apply (batch_cells_xfer B ly (b :: t) (aview tfibsegs (w_H W) mem)); [| exact AGB | exact CE].
unfold items_ok. constructor; [exact BL | exact (rix_items_ok X _ t _ RX)].
Qed.

Definition postRI (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfibsegs) (c' : config) : Prop :=
match its with [] => CDST X b t W' c' | _ :: _ => RCST X b t its i W' c' end.
(* T_R with the segment's raw MEQ exported: the memory is unchanged. *)
Lemma T_R_m : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x34148 regs mem md) (fun W' c' => postRI X b t its i W' c' /\ ms_mem (cfg_ms c') = mem).
Proof.
intros X b t its i lz qb W regs mem md ST. pose proof ST as [AC RX ITS Hi BL LEN CR LR BR S7r S9r FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (seed_R B TB ly X0 P0 W0 regs0 mem0 md0 PRE X b t its i lz qb W regs mem md ST) as FH.
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (rewrite Hits, zlen_app; unfold YFhd.zlen; rewrite Hdone; lia).
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (YFhk.segYR W ly regs mem md _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold YFhc.postR in HP. unfold postRI.
destruct its as [|k ks].
-
rewrite zlen_nil in LENi. replace (Z.of_nat i <? zlen (b_items b)) with false in HP by (symmetry; apply Z.ltb_ge; lia).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R12 & R13 & MQ).
assert (MM : mem' = mem) by (apply functional_extensionality; intros x; apply MQ; intros []). subst mem'.
split; [|reflexivity].
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
constructor.
+ constructor; [apply AR_wvb; exact HAR | exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]
| exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_raw _ _ _ _ _ _ _ _ _ _ _ AC)].
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
split; [|reflexivity].
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
constructor.
+ constructor; [apply AR_wvb; exact HAR | exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]
| exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_raw _ _ _ _ _ _ _ _ _ _ _ AC)].
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
Lemma T_R : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x34148 regs mem md) (postRI X b t its i).
Proof.
intros X b t its i lz qb W regs mem md ST.
eapply SRr_mono; [exact (T_R_m X b t its i lz qb W regs mem md ST)|]. intros W' c' _ [HP _]. exact HP.
Qed.
Lemma CD_pre_x : forall X b t lz qb W regs mem md, cdst X b t lz qb W regs mem md ->
cd_pre_x B (ARX_cgif B) TFIB_INST ly X (b_self b) W regs mem md /\
RIx U 0 0 0 X (flat_map b_items t) [] (b_self b :: map b_self t).
Proof.
intros X b t lz qb W regs mem md ST. destruct ST as [AC RX LEN CR LR RA A0 A1 A2 A3 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27).
split; [|exact (RIx_fold U X [] t [b_self b] RX)].
unfold cd_pre_x, spZ, raZ. rewrite SPV, RA. change (bv_unsigned (w64 0x34180)) with 0x34180.
splits.
- split; [reflexivity | exact HAR].
- exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC).
- vm_compute. reflexivity.
- lia.
- exact S7.
- clear - HSTK S5. nsp. lia.
- clear - E2 S5. nsp. lia.
- intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. clear - Ha S5. nsp. lia.
- rewrite C3. exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). reflexivity.
- exact A0.
- exact A1.
- exact A2.
- exact A3.
Qed.
Lemma CD_post_x : forall X b t lz qb W regs mem md (r : unit * astate) W' c',
cdst X b t lz qb W regs mem md ->
(exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B (ARX_cgif B) (aowned B) TFIB_INST KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B (aowned B) TFIB_INST KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, puser ly X a -> puser ly (snd r) a) /\
  RIx U 0 0 0 (snd r) (flat_map b_items t) [] (map b_self t) /\ st_cache_inited (snd r) = true /\
  (forall a, aowned B ly (snd r) a -> aowned B ly X a)) ->
QST (snd r) t W' c'.
Proof.
intros X b t lz qb W regs mem md [ru X2] W' c' ST HL. destruct ST as [AC RX LEN CR LR RA A0 A1 A2 A3 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
destruct HL as (regs' & mem' & md' & -> & ([_ AR2] & LLE & WLE & CSV & SIO & FRM & PRS) & RAW & PU & PM & DRQ & INI & OWN2). cbn [fst snd] in *.
unfold acall_raw_x in RAW.
pose proof (RIx_unfold U X2 [] t [] DRQ (rix_items_ok X _ t _ RX)) as RX2.
cbn [ImgBase.im_segs AImg_cgif] in FRM.
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. change (bv_unsigned (w64 0x34180)) with 0x34180. rewrite SPV in FRM, RAW, PRS.
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK_CF <= a < sp1) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
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
+ intros a O. exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a (OWN2 a O)).
+ intros a Ha N0 N2 NS NT. rewrite (FRM a Ha); [exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC a Ha N0 ltac:(intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O))) NS NT) | intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC a O)) | exact N2 | | intros F; exact F].
intros [C|C]; apply NS; [left; clear - C S5; nsp; lia | right; exact C].
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK_CF) sp1 a) as [C|C]; [exact (PRS a C)|].
apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [unfold DGif1da.SY in Ha; clear - Ha S1 S2; nsp; lia | | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC a Ha)].
apply AGS; [unfold DGif1da.SY in Ha; clear - Ha S1 S2; nsp; lia | unfold DGif1da.SY in Ha; clear - Ha E1 E2 HSTK; nsp; lia | exact C].
+ exact INI.
+ intros x N0 N2 NS NT. rewrite (RAW x); [exact (acc_raw _ _ _ _ _ _ _ _ _ _ _ AC x N0 ltac:(intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC _ O))) NS NT) | intros O; exact (N0 (acc_own _ _ _ _ _ _ _ _ _ _ _ AC _ O)) | exact N2 | | intros F; exact F].
intros [C|C]; apply NS; [left; clear - C S5; nsp; lia | right; exact C].
- exact RX2.
- exact LEN.
- unfold YFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; [csv CSV (3%bv : bv 5) 3 | csv CSV (4%bv : bv 5) 4 | csv CSV (26%bv : bv 5) 26 | csv CSV (27%bv : bv 5) 27]; reflexivity.
- unfold YFhd.loop_regs. rewrite <- Q2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21.
splits; [csv CSV (2%bv : bv 5) 2 | csv CSV (8%bv : bv 5) 8 | csv CSV (9%bv : bv 5) 9 | csv CSV (18%bv : bv 5) 18 | csv CSV (19%bv : bv 5) 19 | csv CSV (21%bv : bv 5) 21]; reflexivity.
- apply (frame_cells_keep ly regs0 W W' mem mem'); [|exact FR]. intros a Ha. apply AGS; [clear - Ha U0 U1 S5; nsp; lia | clear - Ha E1 E2 S5; nsp; lia | clear - Ha; lia].
- apply (tmp_cells_keep ly regs0 W W' mem mem'); [|exact TM]. intros a Ha. apply AGS; [clear - Ha U0 S2; nsp; lia | clear - Ha E1 E2; nsp; lia | clear - Ha S5; nsp; lia].
- apply (batch_cells_xfer B ly t (aview tfibsegs (w_H W) mem)); [exact (rix_items_ok X _ t _ RX) | exact AGB | exact CE].
Qed.

Definition postQO (X : astate) (t : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
match t with [] => dr_leaf_x B ly X0 W0 regs0 mem0 md0 (tt, X) W' c' | _ :: _ => OST X t W' c' end.
Local Notation v1 := (YFhl.v1 regs0).   Local Notation v8 := (YFhl.v8 regs0).   Local Notation v9 := (YFhl.v9 regs0).
Local Notation v18 := (YFhl.v18 regs0). Local Notation v19 := (YFhl.v19 regs0). Local Notation v20 := (YFhl.v20 regs0).
Local Notation v21 := (YFhl.v21 regs0). Local Notation v22 := (YFhl.v22 regs0). Local Notation v23 := (YFhl.v23 regs0).
Local Notation v24 := (YFhl.v24 regs0). Local Notation v25 := (YFhl.v25 regs0).
(* T_Q with the segment's raw MEQ exported: the memory is unchanged. *)
Lemma T_Q_m : forall X t lz qb W regs mem md, qst X t lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x34180 regs mem md) (fun W' c' => postQO X t W' c' /\ ms_mem (cfg_ms c') = mem).
Proof.
intros X t lz qb W regs mem md ST. pose proof ST as [AC RX LEN CR LR FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof (seed_Q B TB ly X0 P0 W0 regs0 mem0 md0 PRE X t lz qb W regs mem md ST) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (YFhj.segYQ W ly regs mem md (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold YFhb.postQ in HP. unfold postQO.
destruct t as [|b t'].
-
rewrite zlen_nil, Z.eqb_refl in HP.
destruct HP as (-> & _ & regs' & mat & -> & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & CS).
split; [|reflexivity].
exists regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, YFhl.v1. reflexivity. }
split.
+ split; [split; [reflexivity | apply AR_wvb; exact HAR]|]. split; [apply layout_le_refl|]. split; [exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC)|]. split.
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
intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. unfold spZ in Ha. clear - Ha. nsp. lia.
+ split. { intros x N0 N1 NS NT. exact (acc_raw _ _ _ _ _ _ _ _ _ _ _ AC x N0 N1 NS NT). }
intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. unfold spZ in Ha. clear - Ha. nsp. lia.
-
replace (zlen (b :: t') =? 0) with false in HP by (symmetry; apply Z.eqb_neq; rewrite zlen_cons; unfold YFhd.zlen; lia).
destruct HP as (-> & _ & regs' & mat & -> & R2 & CS & R10).
split; [|reflexivity].
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
constructor.
+ constructor; [apply AR_wvb; exact HAR | exact (acc_wle _ _ _ _ _ _ _ _ _ _ _ AC) | eapply same_io_trans; [exact (acc_io _ _ _ _ _ _ _ _ _ _ _ AC) | apply same_io_with_vm_backing]
| exact (acc_own _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_frame _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_inited _ _ _ _ _ _ _ _ _ _ _ AC) | exact (acc_raw _ _ _ _ _ _ _ _ _ _ _ AC)].
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
Lemma T_Q : forall X t lz qb W regs mem md, qst X t lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x34180 regs mem md) (postQO X t).
Proof.
intros X t lz qb W regs mem md ST.
eapply SRr_mono; [exact (T_Q_m X t lz qb W regs mem md ST)|]. intros W' c' _ [HP _]. exact HP.
Qed.
(* The entry segment of DoRecycle (YFhe.segYE). *)
Lemma walk_E_x : SRr tfibsegs W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) (YFh9.postE W0 ly regs0 mem0 md0 (zlen P0)).
Proof.
pose proof (seed_E B TB ly X0 P0 W0 regs0 mem0 md0 PRE) as FH.
unfold cfg_at. rewrite <- (wvb_self md0) at 1. exact (YFhe.segYE W0 ly regs0 mem0 md0 (zlen P0) (m_vm_materialized md0) FH).
Qed.
(* DoRecycle's return on an empty batch list (the entry segment's at_RETE). *)
Lemma RETE_x : forall sz W' c', YFh9.at_RETE W0 regs0 mem0 md0 sz W' c' -> dr_leaf_x B ly X0 W0 regs0 mem0 md0 (tt, X0) W' c'.
Proof.
intros sz W' c' HP.
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
destruct HP as (-> & _ & regs & mem & mat & -> & R2 & CS & MQ & PRS).
assert (WST : forall a, YFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold YFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, YFh9.WIN regs0 a \/ ~ YFh9.WIN regs0 a) by (intros a; unfold YFh9.WIN; apply ivl_dec).
exists regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split.
{ unfold cfg_at, raZ. rewrite Z_to_bv_bv_unsigned || (unfold w64; rewrite Z_to_bv_bv_unsigned). reflexivity. }
split.
+ split; [split; [reflexivity | exact (AR_after_stack_write X0 W0 mem0 mem md0 mat _ HAR WST WDEC MQ PRS)]|].
split; [apply layout_le_refl|]. split; [apply wle_refl|]. split.
{ apply aregs_intro; first [exact R2 | apply CS; cbn; tauto]. }
split; [apply same_io_with_vm_backing|]. split.
{ intros a Ha _ _ NS _. apply (aview_after_write (w_H W0) mem0 mem _ a MQ Ha).
intros Hw. apply NS. left. unfold YFh9.WIN in Hw. clear - Hw. nsp. lia. }
intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [clear - Ha S1 U0; nsp; lia|].
destruct (Z_lt_le_dec a (sp0 - DRSTACK)) as [LA|LA]; [apply HPRX; clear - Ha LA; nsp; lia | apply HPRES; clear - Ha LA; nsp; lia].
+ split. { intros x _ _ NS _. apply MQ. intros Hw. apply NS. left. unfold YFh9.WIN in Hw. clear - Hw. nsp. lia. }
intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [clear - Ha S1 S2 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* DoRecycle (YFes.v), with the recycle callees in DIface's types.                                                  *)
Hypothesis RCH : rch_cgif B.
Hypothesis CDH : cdh_cgif B.
Local Notation FIN := (dr_leaf_x B ly X0 W0 regs0 mem0 md0).
Lemma ITEMS_x : forall b t its i fuel X W c, RCST X b t its i W c -> (length its <= fuel)%nat ->
amreal tfibsegs (recycle_items fuel its X) W c (fun r W' c' => CDST (snd r) b t W' c').
Proof.
intros b t its. induction its as [|k ks IH]; intros i fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. eapply rc_ne; [exact ST | reflexivity].
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [recycle_items].
apply (amreal_mbind tfibsegs (recycle_chunk k) (fun _ => recycle_items f ks) X W c (fun r W' c' => RST (snd r) b t ks (S i) W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
destruct (RC_pre_x X b t k ks i lz qb W regs mem md ST) as [RP DQ].
eapply amreal_mono; [| exact (RCH TFIB_INST ly X k (ks ++ flat_map b_items t) (b_self b :: map b_self t) (sp1 + 8) W regs mem md RP DQ)].
intros r W' c' HL. exact (RC_post_x X b t k ks i lz qb W regs mem md r W' c' ST HL).
+ intros [] X1 W1 c1 ST1. destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
eapply amreal_SRr_pre; [exact (T_R X1 b t ks (S i) lz qb W1 regs mem md ST1)|].
intros W2 c2 _ HP. unfold postRI in HP. destruct ks as [|k' ks'].
* destruct f; cbn [recycle_items]; apply amreal_ret; cbn [snd]; exact HP.
* apply (IH (S i) f X1 W2 c2 HP). cbn in Hfuel |- *. lia.
Qed.
Lemma LOOP_x : forall rest fuel X W c, OST X rest W c -> (length rest <= fuel)%nat ->
amreal tfibsegs (do_recycle fuel rest X) W c FIN.
Proof.
induction rest as [|b t IH]; intros fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. eapply o_ne; [exact ST | reflexivity].
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [do_recycle].
apply (amreal_mbind tfibsegs (recycle_items 1100 (b_items b)) (fun _ => YG00.bind (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t)) X W c
(fun r W' c' => CDST (snd r) b t W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
eapply amreal_SRr_pre; [exact (T_O X b t lz qb W regs mem md ST)|].
intros W1 c1 _ H1. apply (ITEMS_x b t (b_items b) 0 1100 X W1 c1 H1).
destruct H1 as (lz1 & qb1 & regs1 & mem1 & md1 & _ & ST1). assert (BL : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) by (eapply rc_blen; exact ST1). unfold kBatchSlots in BL. cbn in BL. lia.
+ intros [] X1 W1 c1 ST1.
apply (amreal_mbind tfibsegs (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t) X1 W1 c1 (fun r W' c' => QST (snd r) t W' c')).
* destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
destruct (CD_pre_x X1 b t lz qb W1 regs mem md ST1) as [CP DQ].
eapply amreal_mono; [| exact (CDH TFIB_INST ly X1 (flat_map b_items t) (b_self b) (map b_self t) W1 regs mem md CP DQ)].
intros r W' c' HL. exact (CD_post_x X1 b t lz qb W1 regs mem md r W' c' ST1 HL).
* intros [] X2 W2 c2 ST2. destruct ST2 as (lz & qb & regs & mem & md & -> & ST2).
eapply amreal_SRr_pre; [exact (T_Q X2 t lz qb W2 regs mem md ST2)|].
intros W3 c3 _ HP. unfold postQO in HP. destruct t as [|b' t'].
-- destruct f; cbn [do_recycle]; apply amreal_ret; exact HP.
-- apply (IH f X2 W3 c3 HP). cbn in Hfuel |- *. lia.
Qed.
Theorem tfib_dorecycle_arm_x : amreal tfibsegs (do_recycle 100000%nat P0 X0) W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) FIN.
Proof.
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof walk_E_x as WALK.
unfold YFh9.postE in WALK.
assert (CASES : P0 = [] \/ exists b t, P0 = b :: t) by (clear; destruct P0 as [|b t]; [left; reflexivity | right; exists b, t; reflexivity]).
destruct CASES as [EP|(b & t & EP)].
-
rewrite EP. rewrite EP, zlen_nil, Z.eqb_refl in WALK. cbn [do_recycle amreal ret].
eapply SRr_mono; [exact WALK|]. intros W' c' _ HP. exact (RETE_x 0 W' c' HP).
-
replace (zlen P0 =? 0) with false in WALK by (symmetry; apply Z.eqb_neq; rewrite EP, zlen_cons; unfold YFhd.zlen; lia).
eapply amreal_SRr_pre; [exact WALK|]. intros W' c' _ HP.
apply (LOOP_x P0 100000%nat X0 W' c' (T_E W' c' HP)).
apply Nat2Z.inj_le. rewrite of_nat_100000. clear - LENP. lia.
Qed.
End d.
Theorem tfib_dorecycle_ok_x : forall B, TfibSyms B -> rch_cgif B -> cdh_cgif B -> tfib_dorecycle_spec_x B.
Proof. intros B TB RCH CDH ly X P W regs mem md [PRE [HSTK HPRX]]. eapply tfib_dorecycle_arm_x; eassumption. Qed.
End c.

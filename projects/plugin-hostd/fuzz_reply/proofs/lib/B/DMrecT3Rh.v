(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecT3.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 4ecf1a4b4587) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecT3.v, with its module paths and module names changed; 10 of its 133 lines of code are new or changed and 9 lines of the source are left out. *)
(* F1 priming row R3 (re-hide at a secondary recycle): Quarantine::DoRecycle (0x33cf8), the outer loop's pop to the first Recycle call, at the re-hide
   twins (DMrecLRh's states), made from lib/A/DMrecT3.v (T_O_r).  T_O_rh: DMrecT3.T_O_r with the states -> DMrecLRh's; the segment keeps the world and the model state, so the accumulated frame's clauses carry through unchanged.
   A new file, so that the released DMrec* files stay byte-unchanged.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (the outer loop's pop to the first Recycle call at
   the re-hide twins). *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane): the image-B (asan-ubsan) twin of lib/A/DMrecT3Rh.v at a working branch 2612386275a5, relocated by a Theorem Labs lane's alreloc a5c53bb2bed4ad03 (every moved numeral a Quarantine::DoRecycle pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFf2 YFh9 YFha YFhc YFhb.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFhf YFhd YFhl YFhg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DIfaceR DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFhi DMwalkIF DMrecS DMrecL DMrecS2 DMrecS3 DMrecT1 MemnormT MemnormHitG MemnormLocG DMrecT3 DMrecLRh DMrecS3Rh YGcfRehidePost YGcfRecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ErrnoG ErrnoApart ErrnoApartreply.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, YFh9.YFRAME, YFha.YFRAME, YFhc.YFRAME, YFhb.YFRAME, DMwalkIF.DRSTACK_X in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis HRM : DMwalkIF.rmaxd_ok RMAXD.
Hypothesis RV : DMwalkIF.di_rview_x_t B ARXr DRq RMAXD.
Hypothesis FR : di_frame_t ARXr AOX.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : DMwalkIF.dr_pre_r B ARXr AOX DRq (as_inst B) ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation SB := (ly_space ly).
Local Notation hdra := (YFhd.hdra B ly).
Local Notation accrh := (DMrecLRh.accrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation ostrh := (DMrecLRh.ostrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation OSTrh := (DMrecLRh.OSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Ltac open_PRE := pose proof PRE as (HAR0 & Hinst & HDQ & LY & IMG & HSTK & HBL & LENP & INIT & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & CELLS).
Local Notation entry_facts := (DMrecS2.entry_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (DMrecS2.sp_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation HLY := (DMrecS3.HLY B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation slot_facts := (DMrecS.slot_facts_r B ARXr DRq RMAXD HRM RV ly HLY).
Local Notation lastaddr := (YFhg.lastaddr ly).
Local Notation DRSTACK_X := DMwalkIF.DRSTACK_X.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, YFhd.sp1, YFhd.sp0, DMrecL.SYr in *; numconst.

Local Notation ARXr_after_stack_write := (DMrecT1.ARXr_after_stack_write B ARXr AOX DRq FR ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation ek_stk := (DMrecT1.ek_stk B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation mk_stk := (DMrecT1.mk_stk B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation batch_cells_xfer_r := (DMrecT1.batch_cells_xfer_r B ly).

Local Notation sp1_val := (DMrecS2.sp1_val_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation RCSTrh := (DMrecLRh.RCSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation seed_O := (DMrecS3Rh.seed_O_rh B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE).

Lemma T_O_rh : forall X b t lz qb W regs mem md k0 ks, ostrh X (b :: t) lz qb W regs mem md -> b_items b = k0 :: ks ->
SRr tfibsegs W (cfg_at tfibsegs 0x33dc8 regs mem md) (fun W' c' => RCSTrh X b t (b_items b) 0 W' c' /\
  forall x : word, ~ (sp0 <= bv_unsigned x < sp0 + 32) -> ms_mem (cfg_ms c') x = mem x).
Proof.
intros X b t lz qb W regs mem md k0 ks ST Hk0. pose proof ST as [AC DQ BLr NE LEN CR LR A0 FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK aSTP].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV.
pose proof BLr as BLc. apply DMrecL.blen_ok_cons in BLc as [BLb BLt].
assert (BL : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) by (rewrite Hk0 in *; cbn [length] in *; lia).
pose proof (seed_O X b t lz qb W regs mem md k0 ks ST Hk0) as FH.
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
assert (MQ' : forall x : word, ~ (sp0 <= bv_unsigned x < sp0 + 32) -> mem' x = mem x) by (intros x Hx; apply MQ; intros Hw; apply WE in Hw; exact (Hx Hw)).
split; [|exact MQ'].
pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof CR as (C3 & C4 & C26 & C27).
exists (YFha.LZn (firstaddr ly t) lz), (zcanon (qb - b_bytes b mod 2 ^ 64)), regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb).
constructor.
- constructor.
+ exact (ARXr_after_stack_write X W mem mem' md mat WINP aAR aOWN WST WDEC MQ PRS).
+ exact aWLE.
+ eapply same_io_trans; [exact aIO | apply same_io_with_vm_backing].
+ exact aOWN.
+ intros a Ha N0 N1 NS NT. rewrite (AG a Ha) by (intros Hw; apply WE in Hw; exact (NT Hw)). exact (aFR a Ha N0 N1 NS NT).
+ intros a Ha. apply (presence_after_write W mem mem' WINP a WDEC MQ PRS); [unfold DMrecL.SYr in Ha; clear - Ha S1 S2; nsp; lia|]. exact (aPRS a Ha).
+ exact aINI.
+ intros x N0 N1 NS NT. rewrite (MQ' x NT). exact (aRAW x N0 N1 NS NT).
+ apply (DMrecT1.ek_trans B mem0 mem mem' aEK). apply (ek_stk sp0 (sp0 + 32)); [clear - E1; nsp; lia | exact MQ'].
+ apply (MemnormLocG.memnorm_keep_trans tfibsegs mem0 mem mem' aMK). apply (mk_stk sp0 (sp0 + 32)); [clear - E1; nsp; lia | clear - E2; nsp; lia | exact MQ'].
+ exact aSTP.
- exact DQ.
- exact BLt.
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
- apply (frame_cells_keep ly regs0 W W mem mem'); [|exact FRc]. intros a Ha. apply AG; [clear - Ha S5 U0 U1; nsp; lia|]. intros Hw. apply WE in Hw. clear - Ha Hw S5. nsp. lia.
- unfold YFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_addr; [exact V0 | rewrite zlen_cons; lia] || (replace (zlen t) with (zlen (b :: t) - 1) by (rewrite zlen_cons; lia); eapply val_mem_addr; [exact V0 | clear - S5; nsp; lia]).
+ eapply val_mem_addr; [exact V8 | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V16 | clear - S5; nsp; lia].
+ eapply val_mem_addr; [exact V24 | clear - S5; nsp; lia].
+ unfold YFha.LZn. destruct (firstaddr ly t =? 0); [ceil; unfold ASAN_CEIL; lia | exact Rlz].
+ unfold zcanon, M64. apply Z.mod_pos_bound. lia.
- apply (batch_cells_xfer_r (b :: t) (aview tfibsegs (w_H W) mem)); [exact BLr | | exact CE].
intros b' a Hb Hs. pose proof (slot_facts X W mem md _ _ (b_self b') aAR DQ (in_map b_self _ _ Hb)) as (B1 & B2 & _ & _ & _ & _ & _ & _ & BNS).
apply AG; [unfold bslot, kBatchBytes in Hs; clear - Hs B1 B2; numconst; lia|]. intros Hw.
exact (BNS a Hs (WST a Hw)).
Qed.
End e.
End c.

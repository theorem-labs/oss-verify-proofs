(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecM.v (commit 67deba317dfb, blob f1a3dd7cd463) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFf2 AFh9 AFha AFhc AFhb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFhf AFhd AFhl AFhg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFhe AFhi AFhj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MnRecycle.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrecS DMrecL DMrecS2 DMrecS3 DMrecT1 DMrecT2 DMrecT3 DMrecT4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ErrnoApartpreset.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME, DMwalkIFA.DRSTACK_X in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis HRM : DMwalkIFA.rmaxd_ok RMAXD.
Hypothesis RV : DMwalkIFA.di_rview_x_t B ARXr DRq RMAXD.
Hypothesis FR : di_frame_t ARXr AOX.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : DMwalkIFA.dr_pre_r B ARXr AOX DRq (as_inst B) ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation T := (ly_T ly).
Local Notation zlen := (@AFhd.zlen _).
Local Notation SB := (ly_space ly).
Local Notation hdra := (AFhd.hdra B ly).
Local Notation accr := (DMrecL.accr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation ostr := (DMrecL.ostr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation OSTr := (DMrecL.OSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Ltac open_PRE := pose proof PRE as (HAR0 & Hinst & HDQ & LY & IMG & HSTK & HBL & LENP & INIT & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & CELLS).
Local Notation entry_facts := (DMrecS2.entry_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (DMrecS2.sp_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation HLY := (DMrecS3.HLY B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation slot_facts := (DMrecS.slot_facts_r B ARXr DRq RMAXD HRM RV ly HLY).
Local Notation lastaddr := (AFhg.lastaddr ly).
Local Notation DRSTACK_X := DMwalkIFA.DRSTACK_X.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, AFhd.sp1, AFhd.sp0, DMrecL.SYr in *; numconst.

Local Notation ARXr_after_stack_write := (DMrecT1.ARXr_after_stack_write B ARXr AOX DRq FR ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation ek_stk := (DMrecT1.ek_stk B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation mk_stk := (DMrecT1.mk_stk B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation batch_cells_xfer_r := (DMrecT1.batch_cells_xfer_r B ly).

Local Notation sp1_val := (DMrecS2.sp1_val_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation RCSTr := (DMrecL.RCSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation seed_O := (DMrecS3.seed_O_r B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE).

Local Notation rstr := (DMrecL.rstr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation CDSTr := (DMrecL.CDSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation RSTr := (DMrecL.RSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation QSTr := (DMrecL.QSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation FIN := (DMwalkIFA.dr_leaf_r B ARXr AOX DRq (as_inst B) ly X0 W0 regs0 mem0 md0).
Definition postRIr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfibsegs) (c' : config) : Prop :=
match its with [] => CDSTr X b t W' c' | _ :: _ => RCSTr X b t its i W' c' end.

Hypothesis HT_R : forall X b t its i lz qb W regs mem md, rstr X b t its i lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x3479c regs mem md) (postRIr X b t its i).
Hypothesis HT_O0 : forall X b t lz qb W regs mem md, ostr X (b :: t) lz qb W regs mem md -> b_items b = [] ->
SRr tfibsegs W (cfg_at tfibsegs 0x34750 regs mem md) (CDSTr X b t).
Hypothesis RCH : MnRecycle.de_rchunk_m_t B ARXr AOX DRq.
Hypothesis CDH : MnRecycle.de_cdealloc_m_t B ARXr AOX DRq.
Local Notation sp1 := (AFhd.sp1 regs0).

Lemma walk_E_r : SRr tfibsegs W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) (AFh9.postE W0 ly regs0 mem0 md0 (zlen P0)).
Proof.
pose proof (DMrecS2.seed_E_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE) as FH.
unfold cfg_at. rewrite <- (wvb_self md0) at 1. exact (AFhe.segYE W0 ly regs0 mem0 md0 (zlen P0) (m_vm_materialized md0) FH).
Qed.

Lemma ITEMS_r : forall b t its i fuel X W c, RCSTr X b t its i W c -> (length its <= fuel)%nat ->
amreal tfibsegs (recycle_items fuel its X) W c (fun r W' c' => CDSTr (snd r) b t W' c').
Proof.
intros b t its. induction its as [|k ks IH]; intros i fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. pose proof ST as [_ _ _ _ NE]. exact (NE eq_refl).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [recycle_items].
apply (amreal_mbind tfibsegs (recycle_chunk k) (fun _ => recycle_items f ks) X W c (fun r W' c' => RSTr (snd r) b t ks (S i) W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
destruct (DMrecT4.RC_pre_r B ARXr AOX DRq RMAXD TB RV ly X0 P0 W0 regs0 mem0 md0 PRE X b t k ks i lz qb W regs mem md ST) as [RP DQ].
eapply amreal_mono; [| exact (RCH (as_inst B) ly X k (ks ++ flat_map b_items t) (b_self b :: map b_self t) (sp1 + 8) W regs mem md RP DQ)].
intros r W' c' HL. exact (DMrecT4.RC_post_r B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE X b t k ks i lz qb W regs mem md r W' c' ST HL).
+ intros [] X1 W1 c1 ST1. destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
eapply amreal_SRr_pre; [exact (HT_R X1 b t ks (S i) lz qb W1 regs mem md ST1)|].
intros W2 c2 _ HP. unfold postRIr in HP. destruct ks as [|k' ks'].
* destruct f; cbn [recycle_items]; apply amreal_ret; cbn [snd]; exact HP.
* apply (IH (S i) f X1 W2 c2 HP). cbn in Hfuel |- *. lia.
Qed.

Lemma LOOP_r : forall rest fuel X W c, OSTr X rest W c -> (length rest <= fuel)%nat ->
amreal tfibsegs (do_recycle fuel rest X) W c FIN.
Proof.
induction rest as [|b t IH]; intros fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. pose proof ST as [_ _ _ NE]. exact (NE eq_refl).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [do_recycle].
apply (amreal_mbind tfibsegs (recycle_items 1100 (b_items b)) (fun _ => YG00.bind (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t)) X W c
(fun r W' c' => CDSTr (snd r) b t W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
destruct (b_items b) as [|k0 ks] eqn:Hk.
*
eapply amreal_SRr_pre; [exact (HT_O0 X b t lz qb W regs mem md ST Hk)|].
intros W1 c1 _ H1. cbn [recycle_items]. apply amreal_ret. cbn [snd]. exact H1.
* eapply amreal_SRr_pre; [exact (DMrecT3.T_O_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X0 P0 W0 regs0 mem0 md0 PRE X b t lz qb W regs mem md k0 ks ST Hk)|].
intros W1 c1 _ [H1 _]. rewrite <- Hk. apply (ITEMS_r b t (b_items b) 0 1100 X W1 c1 H1).
destruct H1 as (lz1 & qb1 & regs1 & mem1 & md1 & _ & ST1). pose proof ST1 as [_ _ _ _ _ BL]. unfold kBatchSlots in BL. cbn in BL. lia.
+ intros [] X1 W1 c1 ST1.
apply (amreal_mbind tfibsegs (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t) X1 W1 c1 (fun r W' c' => QSTr (snd r) t W' c')).
* destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
destruct (DMrecT4.CD_pre_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE X1 b t lz qb W1 regs mem md ST1) as [CP DQ].
eapply amreal_mono; [| exact (CDH (as_inst B) ly X1 (flat_map b_items t) (b_self b) (map b_self t) W1 regs mem md CP DQ)].
intros r W' c' HL. exact (DMrecT4.CD_post_r B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE X1 b t lz qb W1 regs mem md r W' c' ST1 HL).
* intros [] X2 W2 c2 ST2. destruct ST2 as (lz & qb & regs & mem & md & -> & ST2).
eapply amreal_SRr_pre; [exact (DMrecT4.T_Q_r B ARXr AOX DRq TB FR ly X0 P0 W0 regs0 mem0 md0 PRE X2 t lz qb W2 regs mem md ST2)|].
intros W3 c3 _ [HP _]. unfold DMrecT4.postQOr in HP. destruct t as [|b' t'].
-- destruct f; cbn [do_recycle]; apply amreal_ret; exact HP.
-- apply (IH f X2 W3 c3 HP). cbn in Hfuel |- *. lia.
Qed.

Theorem dorecycle_arm_r : amreal tfibsegs (do_recycle (length P0) P0 X0) W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) FIN.
Proof.
pose proof walk_E_r as WALK. unfold AFh9.postE in WALK.
assert (CASES : P0 = [] \/ exists b t, P0 = b :: t) by (clear; destruct P0 as [|b t]; [left; reflexivity | right; exists b, t; reflexivity]).
destruct CASES as [EP|(b & t & EP)].
- rewrite EP in WALK |- *. rewrite zlen_nil, Z.eqb_refl in WALK. cbn [length do_recycle amreal ret].
eapply SRr_mono; [exact WALK|]. intros W' c' _ HP. exact (DMrecT2.RETE_r B ARXr AOX DRq TB FR ly X0 P0 W0 regs0 mem0 md0 PRE 0 W' c' EP HP).
- replace (zlen P0 =? 0) with false in WALK by (symmetry; apply Z.eqb_neq; rewrite EP, zlen_cons; unfold AFhd.zlen; lia).
eapply amreal_SRr_pre; [exact WALK|]. intros W' c' _ HP.
apply (LOOP_r P0 (length P0) X0 W' c' (DMrecT2.T_E_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X0 P0 W0 regs0 mem0 md0 PRE W' c' HP)). lia.
Qed.
End e.
End c.

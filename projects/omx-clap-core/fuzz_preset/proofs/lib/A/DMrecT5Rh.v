(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecT5Rh.v (commit 67deba317dfb, blob ffb76a1a1e83) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 1 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFhi AFhj AFhk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MnRecycle.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrecS DMrecL DMrecS2 DMrecS3 DMrecT1 DMrecT4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrecT5 DMrecLRh DMrecS3Rh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRecStep.
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
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation zlen := (@AFhd.zlen _).
Local Notation SB := (ly_space ly).
Local Notation hdra := (AFhd.hdra B ly).
Local Notation accrh := (DMrecLRh.accrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation ostrh := (DMrecLRh.ostrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation OSTrh := (DMrecLRh.OSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
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
Local Notation RCSTrh := (DMrecLRh.RCSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation seed_O := (DMrecS3Rh.seed_O_rh B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE).

Ltac numconst2 := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, DMwalkIFA.DRSTACK_X, KSTACK, KSTACK_CF, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME in *.
Ltac nsp2 := unfold ascratch in *; unfold DMrecL.SYr in *; unfold spZ, raZ, AFhd.sp1, AFhd.sp0 in *; numconst2.
Ltac csv CS r z := rewrite (AFhg.csv_get _ _ CS r z ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
Local Notation rcstrh := (DMrecLRh.rcstrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation rstrh := (DMrecLRh.rstrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation cdstrh := (DMrecLRh.cdstrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation qstrh := (DMrecLRh.qstrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation RSTrh := (DMrecLRh.RSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation QSTrh := (DMrecLRh.QSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation snot := (DMrecS2.stack_not_owned_r B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation item_facts := (DMrecS.item_facts_r B ARXr DRq RMAXD RV ly).
Local Notation slot_puser := (DMrecS.slot_puser_r B ARXr DRq RMAXD RV ly).
Local Notation slot_vs_chunk := (DMrecS.slot_vs_chunk_r B ARXr DRq RMAXD RV ly).
Local Notation ARXr_wvb := (DMrecT4.ARXr_wvb B ARXr AOX DRq FR ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sb_cell := (DMrecS.sb_cell_r B ARXr DRq RMAXD TB RV ly).
Local Notation CDSTrh := (DMrecLRh.CDSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation next_hdr := (AFhl.next_hdr B ly).

Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma seed_R_rh : forall X b t its i lz qb W regs mem md, rstrh X b t its i lz qb W regs mem md ->
AFhc.free_hyps W ly regs mem (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i).
Proof.
intros X b t its i lz qb W regs mem md ST. destruct ST as [AC DQ BLt ITS Hi BL LEN CR LR BR S7 S9 FRc TM CE].
pose proof AC as [aAR _ _ _ _ aPRS _ _ _ _ _]. open_PRE.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27). pose proof BR as (R20 & R22 & R24).
pose proof (DMrecS.ly_facts ly LY IMG) as (L1 & L2 & L3 & L4 & _ & _ & _ & FS3 & FT1 & FT2 & FT3).
assert (FS1 : kHighMemBeg <= SB) by (clear - L1 L3; lia).
assert (FS2 : SB + kSpaceSize <= ASAN_CEIL) by (clear - L2 L4; unfold kSpaceSize, kPrimResvSize in *; lia).
pose proof (slot_facts X W mem md _ _ (b_self b) aAR DQ (or_introl eq_refl)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BNS).
assert (B7' : SB + b_self b + kBatchBytes <= SB + region_off kBatchClass + kFreeArrayOffset) by (destruct HRM as [_ HR2]; clear - B7 HR2; lia).
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (rewrite Hits, zlen_app; unfold AFhd.zlen; rewrite Hdone; lia).
assert (LENb : 1 <= zlen (b_items b) <= kBatchSlots) by (clear - BL; unfold AFhd.zlen, kBatchSlots in *; lia).
assert (Hi1 : 1 <= Z.of_nat i) by (clear - Hi; lia).
assert (Hzi : 0 <= zlen its) by (unfold AFhd.zlen; clear; lia).
pose proof (batch_head_cells B ly (w_H W) mem b t CE) as (V0 & V8 & V16 & VI). cbv zeta in V0, V8, V16, VI.
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FRc as [CB SV].
assert (NH : 0 <= next_hdr its < ASAN_CEIL /\ next_hdr its mod 16 = 0 /\ 0 <= next_hdr its < 2 ^ 64 /\
(Z.of_nat i < zlen (b_items b) -> exists k ks, its = k :: ks /\ In k (its ++ flat_map b_items t) /\ nth_error (b_items b) i = Some k)).
{ destruct its as [|k ks].
- cbn [AFhl.next_hdr]. rewrite zlen_nil in LENi. ceil; unfold ASAN_CEIL. splits; try lia; try reflexivity; (intros HH; exfalso; clear - HH LENi; lia).
- cbn [AFhl.next_hdr]. assert (Hk : In k ((k :: ks) ++ flat_map b_items t)) by (left; reflexivity).
pose proof (item_facts X W mem md _ _ k aAR DQ Hk) as (I0 & I1 & I2 & I3 & I4). splits; try assumption; [clear - I4; lia | clear - I2; lia | clear - I4; lia | clear - I4; lia |].
intros _. exists k, ks. splits; [reflexivity | exact Hk |]. rewrite Hits. rewrite nth_error_app2 by lia. rewrite Hdone, Nat.sub_diag. reflexivity. }
destruct NH as (NH1 & NH2 & NH3 & NHk).
assert (S7R : kHighMemBeg <= AFhc.S7v (SB + b_self b) (Z.of_nat i) /\ AFhc.S7v (SB + b_self b) (Z.of_nat i) + 8 <= ASAN_CEIL /\
AFhc.S7v (SB + b_self b) (Z.of_nat i) mod 8 = 0).
{ unfold AFhc.S7v. rewrite region_off_24 in B6, B7'. unfold kFreeArrayOffset in B7'. clear - B1 B3 B6 B7' LENi LENb Hzi FS2 Hi1. numconst. splits; lia. }
destruct S7R as (Q1 & Q2 & Q3).
constructor.
- exact LY.
- exact IMG.
- rewrite C4. exact Etp.
- rewrite SPV. unfold AFhc.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. split; [exact E1 | exact E2].
- rewrite SPV. exact S7'.
- rewrite SPV. intros a Ha. apply aPRS. unfold DMrecL.SYr. unfold AFhc.YFRAME in Ha. clear - Ha S5; nsp; lia.
- rewrite SPV. unfold AFhc.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia.
splits; try assumption; first [rewrite S7; unfold AFhc.S7v; f_equal; lia | rewrite S9; f_equal; lia].
- rewrite SPV. eapply val_mem_addr; [exact CB | reflexivity].
- exact (sb_cell X W mem md _ _ aAR DQ).
- splits; [exact B6 | exact B7' | exact B3].
- clear - LENi LENb Hi1 Hzi. lia.
- intros HLT. destruct (NHk HLT) as (k & ks & -> & Hk & Hnth). cbn [AFhl.next_hdr]. pose proof (item_facts X W mem md _ _ k aAR DQ Hk) as (I0 & I1 & I2 & I3 & I4).
pose proof (VI i k Hnth) as V. fold (hdra k) in V. splits; [eapply val_mem_addr; [exact V | lia] | | exact I1 | exact I2 | exact I3].
intros a Ha. apply (val_mem_apresent _ _ _ 8 _ a V); [clear - Ha; cbn; lia | clear - Ha B1 B2 LENi LENb Hzi Hi1; numconst; lia].
- split; [exact NH1 | exact NH2].
-
rewrite restrict_mkst_fx. unfold AFhc.SS0, AFhc.SR0, sr_set. cbn [bv_eqb]. unfold AFhc.E0, w64. apply (entry_st_ok_full tfibsegs).
+ set (E0 := Ereg regs (AFhc.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))).
assert (HE2 : ew E0 2 = Z_to_bv 64 sp1) by (rewrite (AFhc.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew E0 2 = getr regs 2); exact R2).
repeat (apply regs_ok_pin; [| intros XX; discriminate |]); [apply regs_ok_Ereg | ..]; cbn [sv_denot].
* rewrite C4, Etp. reflexivity.
* rewrite HE2, R8. unfold AFhc.YFRAME, w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* rewrite R9. reflexivity.
* rewrite R18. reflexivity.
* rewrite R19. reflexivity.
* rewrite R21. reflexivity.
* change (ew E0 40) with (Z_to_bv 64 (SB + b_self b)). rewrite R20. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* change (ew E0 43) with (Z_to_bv 64 (zlen (b_items b))). rewrite R22. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* change (ew E0 45) with (Z_to_bv 64 (AFhc.S7v (SB + b_self b) (Z.of_nat i))). rewrite S7. unfold AFhc.S7v, w64. rewrite Zbv_add_unsigned. f_equal. lia.
* change (ew E0 43) with (Z_to_bv 64 (zlen (b_items b))). rewrite R24. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
* change (ew E0 52) with (Z_to_bv 64 (Z.of_nat i)). rewrite S9. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. set (E0 := Ereg regs (AFhc.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (rewrite (AFhc.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew E0 2 = getr regs 2); exact SPV).
unfold AFhc.REG0, AFhc.R_STK, fatom8, AFhc.YFRAME. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* reg_intro. rewrite BV2. split; [lia|]. split; [clear - S2 S5; numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom8d E0 _ _ _ 32%nat t_cache T); [reflexivity | clear - FT1 FT2; numconst; lia | clear - FT1 FT2; numconst; lia | eapply val_mem_addr; [exact CB | reflexivity]].
* reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom8 E0 _ _ _ 34%nat SB); [reflexivity | clear - FS1 FS2; numconst; lia | rewrite Z.add_0_l; exact (sb_cell X W mem md _ _ aAR DQ)].
+ apply pairwise_disjoint_of_extents. unfold AFhc.REG0, AFhc.R_STK, fatom8, AFhc.YFRAME, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite (AFhc.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew (Ereg regs (AFhc.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))) 2 = getr regs 2), SPV.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. split; [|exact (conj I I)]. split; [|exact I]. clear - S1 S5. numconst. lia.
+ split; [|split; exact I]. cbn [AFhc.FFY f_atoms atoms_ok].
set (E0 := Ereg regs (AFhc.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))).
assert (E2' : ew E0 2 = w64 sp1) by (rewrite (AFhc.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew E0 2 = getr regs 2); exact R2).
rewrite region_off_24 in B6, B7'. unfold kFreeArrayOffset in B7'. unfold AFhc.S7v in Q1, Q2, Q3.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchSlots, kBatchBytes, kThreadObjSize, kSpaceSize, AFhc.YFRAME in *.
split. { apply (afact_intro E0 2%nat sp1); [exact E2'| exact U1 | ceil; clear - CR0 S1 S2 S5; lia | change (2 ^ 4) with 16; exact S7' | clear; lia]. }
split. { apply (afact_intro E0 32%nat T); [reflexivity | ceil; clear - CR0 FT1 FT2; lia | ceil; clear - CR0 FT1 FT2; lia | change (2 ^ 12) with 4096; exact FT3 | clear; lia]. }
split. { apply (afact_intro E0 34%nat SB); [reflexivity | ceil; clear - CR0 FS1 FS2; lia | ceil; clear - CR0 FS1 FS2; lia | change (2 ^ 16) with 65536; exact FS3 | clear; lia]. }
split. { apply (afact_intro E0 40%nat (SB + b_self b)); [reflexivity | exact B8 | ceil; clear - CR0 B1 B2; lia | change (2 ^ 13) with 8192; exact B3 | clear; lia]. }
split. { apply (afact_intro E0 43%nat (zlen (b_items b))); [reflexivity | ceil; clear - CR0 LENb; lia | ceil; clear - CR0 LENb; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | clear; lia]. }
split. { apply (afact_intro E0 44%nat (next_hdr its)); [reflexivity | exact NH3 | ceil; clear - CR0 NH1; lia | change (2 ^ 4) with 16; exact NH2 | clear; lia]. }
split. { apply (afact_intro E0 45%nat (SB + b_self b + 144 + 8 * Z.of_nat i)); [reflexivity | ceil; clear - CR0 Q1 Q2; lia | ceil; clear - CR0 Q1 Q2; lia | change (2 ^ 3) with 8; exact Q3 | clear; lia]. }
split; [|exact I]. { apply (afact_intro E0 52%nat (Z.of_nat i)); [reflexivity | ceil; clear - CR0 LENi LENb Hi1 Hzi; lia | ceil; clear - CR0 LENi LENb Hi1 Hzi; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | clear; lia]. }
Qed.

Definition postRIrh (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfibsegs) (c' : config) : Prop :=
match its with [] => CDSTrh X b t W' c' | _ :: _ => RCSTrh X b t its i W' c' end.
Lemma T_R_rh : forall X b t its i lz qb W regs mem md, rstrh X b t its i lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x3479c regs mem md) (postRIrh X b t its i).
Proof.
intros X b t its i lz qb W regs mem md ST. pose proof ST as [AC DQ BLt ITS Hi BL LEN CR LR BR S7r S9r FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK aSTP].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
pose proof (seed_R_rh X b t its i lz qb W regs mem md ST) as FH.
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (rewrite Hits, zlen_app; unfold AFhd.zlen; rewrite Hdone; lia).
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhk.segYR W ly regs mem md _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold AFhc.postR in HP. unfold postRIrh.
destruct its as [|k ks].
-
rewrite zlen_nil in LENi. replace (Z.of_nat i <? zlen (b_items b)) with false in HP by (symmetry; apply Z.ltb_ge; lia).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R12 & R13 & MQ).
assert (MM : mem' = mem) by (apply functional_extensionality; intros x; apply MQ; intros []). subst mem'.
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
constructor.
+ constructor; [exact (ARXr_wvb X W mem md mat aAR aOWN) | exact aWLE | eapply same_io_trans; [exact aIO | apply same_io_with_vm_backing]
| exact aOWN | exact aFR | exact aPRS | exact aINI | exact aRAW | exact aEK | exact aMK | exact aSTP].
+ exact DQ.
+ exact BLt.
+ exact LEN.
+ unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold AFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ exact R1.
+ exact R10.
+ exact R11.
+ exact R12.
+ exact R13.
+ exact FRc.
+ exact TM.
+ exact (batch_cells_tail B ly _ b t CE).
-
rewrite zlen_cons in LENi. replace (Z.of_nat i <? zlen (b_items b)) with true in HP by (symmetry; apply Z.ltb_lt; unfold AFhd.zlen in *; lia).
destruct HP as (-> & _ & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R23 & R25 & MQ).
assert (MM : mem' = mem) by (apply functional_extensionality; intros x; apply MQ; intros []). subst mem'.
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
constructor.
+ constructor; [exact (ARXr_wvb X W mem md mat aAR aOWN) | exact aWLE | eapply same_io_trans; [exact aIO | apply same_io_with_vm_backing]
| exact aOWN | exact aFR | exact aPRS | exact aINI | exact aRAW | exact aEK | exact aMK | exact aSTP].
+ exact DQ.
+ exact BLt.
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
+ exact FRc.
+ exact TM.
+ exact CE.
Qed.
End e.
End c.

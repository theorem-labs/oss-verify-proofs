(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1db.v (a working branch 84ee52cd012, file sha256 e68b650594b3) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_state image A (fs.asan): numconst unfolds kFreeArrayOffset, because fs's AFhl.slot_facts bounds the batch slot by SB + region_off kBatchClass + kFreeArrayOffset where cgif's YFhl states + 2 ^ 31 (AFhl.v header; fs EV_MAX 11776); seed_R's S7R (lia) needs the number. L edit, route-1 pieces R1-A-DG / R1-B-DG. *)
(* Modified by Theorem Labs, 2026-10: the seeds of cgif_file's released DoRecycle walk (AFhl.v: seed_O, seed_R, seed_Q),
   restated over the states of DGif1da.v (larger stack window DRSTACK_X, raw frame); the proofs are the released ones. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFew AFeu AFf2 AFh9 AFha AFhc AFhb.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFhf AFhd AFhl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif1da.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, kFreeArrayOffset, t_qc, t_cache, DRSTACK, DRSTACK_X, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : dr_pre B ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Local Notation hdra := (AFhd.hdra B ly).
Local Notation zlen := (@AFhd.zlen _).
Local Notation acc := (DGif1da.acc B ly X0 W0 regs0 mem0 md0).
Local Notation common_regs := (AFhd.common_regs regs0).
Local Notation loop_regs := (AFhd.loop_regs regs0).
Local Notation frame_cells := (AFhd.frame_cells ly regs0).
Local Notation tmp_cells := (AFhd.tmp_cells ly regs0).
Local Notation ost := (DGif1da.ost B ly X0 W0 regs0 mem0 md0).
Local Notation rcst := (DGif1da.rcst B ly X0 W0 regs0 mem0 md0).
Local Notation rst := (DGif1da.rst B ly X0 W0 regs0 mem0 md0).
Local Notation cdst := (DGif1da.cdst B ly X0 W0 regs0 mem0 md0).
Local Notation qst := (DGif1da.qst B ly X0 W0 regs0 mem0 md0).
Local Notation IMG := (AFhl.IMG B ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation entry_facts := (AFhl.entry_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (AFhl.sp_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp1_val := (AFhl.sp1_val B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation item_facts := (AFhl.item_facts B ly).
Local Notation slot_facts := (AFhl.slot_facts B ly).
Local Notation sb_cell := (AFhl.sb_cell B TB ly).

Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma seed_O : forall X b t lz qb W regs mem md k0 ks, ost X (b :: t) lz qb W regs mem md -> b_items b = k0 :: ks ->
AFha.free_hyps W ly regs mem (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz.
Proof.
intros X b t lz qb W regs mem md k0 ks ST Hk0. destruct ST as [AC RX NE LEN CR LR A0 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. destruct HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27).
pose proof (lo_top ly (am_layout _ _ _ _ M)) as (_ & _ & _ & T4 & _ & _ & T7).
assert (SZb : slot_ok X (b_self b)) by (apply (RIx_slots U 0 0 0 X [] (b :: t) [] _ RX); cbn; left; reflexivity).
pose proof (slot_facts X _ (b_self b) M SZb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BNS).
pose proof (RIx_open U 0 0 0 X b t RX) as [RXo BL].
assert (Hk0in : In k0 (st_chunks X)).
{ destruct RXo as (_ & IT & _). rewrite Hk0 in IT. cbn [app] in IT. inversion IT as [|x l [H1 _] _]; subst. exact H1. }
pose proof (item_facts X _ k0 M Hk0in) as (I0 & I1 & I2 & I3 & I4).
assert (NXf : 0 <= firstaddr ly t < ASAN_CEIL /\ firstaddr ly t mod 8192 = 0).
{ destruct t as [|b' t']; [cbn; ceil; unfold ASAN_CEIL; split; [lia | reflexivity]|]. cbn [firstaddr].
assert (SZ' : slot_ok X (b_self b')) by (apply (RIx_slots U 0 0 0 X [] (b :: b' :: t') [] _ RX); cbn; right; left; reflexivity).
pose proof (slot_facts X _ (b_self b') M SZ') as (B1' & B2' & B3' & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kHighMemBeg in *. lia. }
pose proof (batch_head_cells B ly (w_H W) mem b t CE) as (V0 & V8 & V16 & VI). cbv zeta in V0, V8, V16, VI.
pose proof (VI 0%nat k0 ltac:(rewrite Hk0; reflexivity)) as V24. rewrite Z.mul_0_r, Z.add_0_r in V24. fold (hdra k0) in V24.
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (LENb : 1 <= zlen (b_items b) <= kBatchSlots) by (clear - BL; unfold AFhd.zlen, kBatchSlots in *; lia).
assert (LENr : 1 <= zlen (b :: t) < 2 ^ 40) by (clear - LEN; rewrite zlen_cons in *; unfold AFhd.zlen in *; lia).
constructor.
- exact (am_layout _ _ _ _ M).
- exact IMG.
- rewrite C4. exact Etp.
- rewrite SPV. unfold AFha.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. split; [exact E1 | exact E2].
- rewrite SPV. exact S7.
- rewrite SPV. intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. unfold AFha.YFRAME in Ha. numconst. lia.
- rewrite SPV. unfold AFha.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. splits; assumption.
- splits; [exact B4 | exact B5 | exact B3 |]. intros a Ha.
assert (HH : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha B1 B2; numconst; lia).
destruct (Z_lt_le_dec a (SB + b_self b + 8)) as [L1|L1]; [apply (val_mem_apresent _ _ _ 8 _ a V0); [clear - Ha L1; cbn; lia | exact HH]|].
destruct (Z_lt_le_dec a (SB + b_self b + 16)) as [L2|L2]; [apply (val_mem_apresent _ _ _ 8 _ a V8); [clear - L1 L2; cbn; lia | exact HH]|].
destruct (Z_lt_le_dec a (SB + b_self b + 24)) as [L3|L3]; [apply (val_mem_apresent _ _ _ 8 _ a V16); [clear - L2 L3; cbn; lia | exact HH]|].
apply (val_mem_apresent _ _ _ 8 _ a V24); [clear - L3 Ha; cbn; lia | exact HH].
- exact NXf.
- exact LENb.
- split; [apply mod64_range | exact Rqb].
- exact LENr.
- exact Rlz.
- splits; [exact I1 | exact I2 | exact I3].
-
rewrite restrict_mkst_fx. unfold AFha.SS0, AFha.SR0, sr_set. cbn [bv_eqb]. unfold AFha.E0, w64. apply (entry_st_ok_full tfibsegs).
+ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg| intros XX; discriminate |]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|].
* cbn [sv_denot]. rewrite C4, Etp. reflexivity.
* cbn [sv_denot]. fold (AFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (AFha.E2 ly regs), R2, R8. unfold AFha.YFRAME, w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* cbn [sv_denot]. rewrite R9. reflexivity.
* cbn [sv_denot]. rewrite R18. reflexivity.
* cbn [sv_denot]. rewrite R19. reflexivity.
* cbn [sv_denot]. rewrite R21. reflexivity.
* cbn [sv_denot]. fold (AFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (AFha.EqSZ ly regs), A0. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. fold (AFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
set (E0 := AFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (subst E0; rewrite (AFha.E2 ly regs); exact SPV).
assert (BV40 : bv_unsigned (ew E0 40) = SB + b_self b) by (subst E0; rewrite (AFha.EqB ly regs); unfold w64; apply unsigned_lit_small; exact B8).
unfold AFha.REG0, AFha.R_STK, AFha.R_B, AFha.YFRAME. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* reg_intro. rewrite BV2. split; [lia|]. split; [numconst; lia|]. split.
{ intros o Ho. apply apresent_writable; [numconst; lia|]. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. numconst. lia. }
repeat apply Forall_cons; try apply Forall_nil.
-- apply (chunk_atom8 E0 _ _ _ 46%nat (zlen (b :: t))); [reflexivity | lia | eapply val_mem_addr; [exact T0 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 40%nat (SB + b_self b)); [reflexivity | exact B8 | eapply val_mem_addr; [exact T8 | cbn [firstaddr]; lia]].
-- apply (chunk_atom8 E0 _ _ _ 49%nat lz); [reflexivity | numconst; lia | eapply val_mem_addr; [exact T16 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 47%nat qb); [reflexivity | lia | eapply val_mem_addr; [exact T24 | lia]].
* reg_intro. rewrite BV40. split; [lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
-- apply (chunk_atom8 E0 _ _ _ 41%nat (firstaddr ly t)); [reflexivity | numconst; lia | eapply val_mem_addr; [exact V0 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 42%nat (b_bytes b mod 2 ^ 64)); [reflexivity | apply mod64_range | eapply val_mem_addr; [apply val_mem_mod64; exact V8 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 43%nat (zlen (b_items b))); [reflexivity | numconst; lia | eapply val_mem_addr; [exact V16 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 44%nat (hdra k0)); [reflexivity | exact I4 | eapply val_mem_addr; [exact V24 | lia]].
+ apply pairwise_disjoint_of_extents. unfold AFha.REG0, AFha.R_STK, AFha.R_B, AFha.YFRAME, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
fold (AFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (AFha.E2 ly regs), (AFha.EqB ly regs), SPV. unfold w64. rewrite unsigned_lit_small by exact B8.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (A0' : bslot ly (b_self b) (SB + b_self b)) by (unfold bslot, kBatchBytes; lia). pose proof (BNS _ A0') as NS0.
split; [|exact (conj I I)]. split; [|exact I]. clear - NS0 E1 E2 S5 B1 B2. numconst. lia.
+ split; [|split; exact I]. cbn [AFha.FFO f_atoms atoms_ok].
fold (AFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
set (E0 := AFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
assert (E2' : ew E0 2 = w64 sp1) by (subst E0; rewrite (AFha.E2 ly regs); exact R2).
pose proof (mod64_range (b_bytes b)) as MB. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchSlots, AFha.YFRAME.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchBytes, kBatchSlots in S1, S2, B1, B2, NXf, LENb, I1, I2, Rlz.
split. { apply (afact_intro E0 2%nat sp1); [exact E2'| exact U1 | lia | change (2 ^ 4) with 16; exact S7 | lia]. }
split. { apply (afact_intro E0 40%nat (SB + b_self b)); [reflexivity | exact B8 | lia | change (2 ^ 13) with 8192; exact B3 | lia]. }
split. { apply (afact_intro E0 41%nat (firstaddr ly t)); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact (proj2 NXf) | lia]. }
split. { apply (afact_intro E0 42%nat (b_bytes b mod 2 ^ 64)); [reflexivity | exact MB | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (afact_intro E0 43%nat (zlen (b_items b))); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (afact_intro E0 44%nat (hdra k0)); [reflexivity | exact I4 | lia | change (2 ^ 4) with 16; exact I3 | lia]. }
split. { apply (afact_intro E0 46%nat (zlen (b :: t))); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (afact_intro E0 47%nat qb); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split; [|exact I]. { apply (afact_intro E0 49%nat lz); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
Qed.
Lemma T_SB_facts : forall X rd, ARm B ly X rd ->
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ T mod 4096 = 0 /\ kHighMemBeg <= SB /\ SB + kSpaceSize + 4096 <= ASAN_CEIL /\ SB mod 65536 = 0.
Proof.
intros X rd M. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (lo_high ly LO) as HI. unfold in_high in HI. cbn [fst snd] in HI.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear; unfold kThreadObjSize; lia) (Forall_nth_f _ _ 2 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LO) eq_refl eq_refl)) as ZT.
pose proof (lo_T_al ly LO) as TAL. pose proof (lo_space_al ly LO) as SAL. pose proof (lo_space_in ly LO) as [S1 S2]. unfold page_aligned in *. cbn [fst snd] in *.
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|]. clear ZT. splits; lia.
Qed.
Definition next_hdr (its : list chunk) : Z := match its with k :: _ => hdra k | [] => 0 end.
Lemma seed_R : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs mem md ->
AFhc.free_hyps W ly regs mem (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i).
Proof.
intros X b t its i lz qb W regs mem md ST. destruct ST as [AC RX ITS Hi BL LEN CR LR BR S7 S9 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. destruct HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27). pose proof BR as (R20 & R22 & R24).
pose proof (T_SB_facts X _ M) as (FT1 & FT2 & FT3 & FS1 & FS2 & FS3).
assert (SZb : slot_ok X (b_self b)) by (apply (RIx_slots U 0 0 0 X its t [b_self b] _ RX); cbn; left; reflexivity).
pose proof (slot_facts X _ (b_self b) M SZb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BNS).
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (rewrite Hits, zlen_app; unfold AFhd.zlen; rewrite Hdone; lia).
assert (LENb : 1 <= zlen (b_items b) <= kBatchSlots) by (clear - BL; unfold AFhd.zlen, kBatchSlots in *; lia).
assert (Hi1 : 1 <= Z.of_nat i) by (clear - Hi; lia).
assert (Hzi : 0 <= zlen its) by (unfold AFhd.zlen; clear; lia).
pose proof (batch_head_cells B ly (w_H W) mem b t CE) as (V0 & V8 & V16 & VI). cbv zeta in V0, V8, V16, VI.
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (NH : 0 <= next_hdr its < ASAN_CEIL /\ next_hdr its mod 16 = 0 /\ 0 <= next_hdr its < 2 ^ 64 /\
(Z.of_nat i < zlen (b_items b) -> exists k ks, its = k :: ks /\ In k (st_chunks X) /\ nth_error (b_items b) i = Some k)).
{ destruct its as [|k ks].
- cbn [next_hdr]. rewrite zlen_nil in LENi. ceil; unfold ASAN_CEIL. splits; try lia; try reflexivity; (intros HH; exfalso; clear - HH LENi; lia).
- cbn [next_hdr]. destruct RX as (_ & IT & _). cbn [app] in IT. inversion IT as [|x l [Hk _] _]; subst x l.
pose proof (item_facts X _ k M Hk) as (I0 & I1 & I2 & I3 & I4). splits; try assumption; [clear - I4; lia | clear - I2; lia | clear - I4; lia | clear - I4; lia |].
intros _. exists k, ks. splits; [reflexivity | exact Hk |]. rewrite Hits. rewrite nth_error_app2 by lia. rewrite Hdone, Nat.sub_diag. reflexivity. }
destruct NH as (NH1 & NH2 & NH3 & NHk).
assert (S7R : kHighMemBeg <= AFhc.S7v (SB + b_self b) (Z.of_nat i) /\ AFhc.S7v (SB + b_self b) (Z.of_nat i) + 8 <= ASAN_CEIL /\
AFhc.S7v (SB + b_self b) (Z.of_nat i) mod 8 = 0).
{ unfold AFhc.S7v. rewrite region_off_24 in B6, B7. unfold kFreeArrayOffset in B7. clear - B1 B3 B6 B7 LENi LENb Hzi FS2 Hi1. numconst. splits; lia. }
destruct S7R as (Q1 & Q2 & Q3).
constructor.
- exact (am_layout _ _ _ _ M).
- exact IMG.
- rewrite C4. exact Etp.
- rewrite SPV. unfold AFhc.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. split; [exact E1 | exact E2].
- rewrite SPV. exact S7'.
- rewrite SPV. intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. unfold AFhc.YFRAME in Ha. clear - Ha S5; numconst. lia.
- rewrite SPV. unfold AFhc.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia.
splits; try assumption; first [rewrite S7; unfold AFhc.S7v; f_equal; lia | rewrite S9; f_equal; lia].
- rewrite SPV. eapply val_mem_addr; [exact CB | reflexivity].
- exact (sb_cell X W mem M).
- splits; [exact B6 | exact B7 | exact B3].
- clear - LENi LENb Hi1 Hzi. lia.
- intros HLT. destruct (NHk HLT) as (k & ks & -> & Hk & Hnth). cbn [next_hdr]. pose proof (item_facts X _ k M Hk) as (I0 & I1 & I2 & I3 & I4).
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
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom8 E0 _ _ _ 34%nat SB); [reflexivity | clear - FS1 FS2; numconst; lia | rewrite Z.add_0_l; exact (sb_cell X W mem M)].
+ apply pairwise_disjoint_of_extents. unfold AFhc.REG0, AFhc.R_STK, fatom8, AFhc.YFRAME, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite (AFhc.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew (Ereg regs (AFhc.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))) 2 = getr regs 2), SPV.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. split; [|exact (conj I I)]. split; [|exact I]. clear - S1 S5. numconst. lia.
+ split; [|split; exact I]. cbn [AFhc.FFY f_atoms atoms_ok].
set (E0 := Ereg regs (AFhc.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))).
assert (E2' : ew E0 2 = w64 sp1) by (rewrite (AFhc.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew E0 2 = getr regs 2); exact R2).
rewrite region_off_24 in B6, B7. unfold kFreeArrayOffset in B7. unfold AFhc.S7v in Q1, Q2, Q3.
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
Definition v1 : Z := bv_unsigned (getr regs0 1).
Definition v8 : Z := bv_unsigned (getr regs0 8).   Definition v9 : Z := bv_unsigned (getr regs0 9).
Definition v18 : Z := bv_unsigned (getr regs0 18). Definition v19 : Z := bv_unsigned (getr regs0 19). Definition v20 : Z := bv_unsigned (getr regs0 20).
Definition v21 : Z := bv_unsigned (getr regs0 21). Definition v22 : Z := bv_unsigned (getr regs0 22). Definition v23 : Z := bv_unsigned (getr regs0 23).
Definition v24 : Z := bv_unsigned (getr regs0 24). Definition v25 : Z := bv_unsigned (getr regs0 25).
Lemma seed_Q : forall X t lz qb W regs mem md, qst X t lz qb W regs mem md ->
AFhb.free_hyps W ly regs mem (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25.
Proof.
intros X t lz qb W regs mem md ST. destruct ST as [AC RX LEN CR LR FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. destruct HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27).
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (Hz : 0 <= zlen t < 2 ^ 40) by (clear - LEN; unfold AFhd.zlen in *; lia).
constructor.
- exact (am_layout _ _ _ _ M).
- exact IMG.
- rewrite C4. exact Etp.
- rewrite SPV. unfold AFhb.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. split; [exact E1 | exact E2].
- rewrite SPV. exact S7'.
- rewrite SPV. intros a Ha. apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold DGif1da.SY. unfold AFhb.YFRAME in Ha. clear - Ha S5; numconst. lia.
- rewrite SPV. unfold AFhb.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. splits; assumption.
- unfold v1, w64. rewrite Z_to_bv_bv_unsigned. exact Era.
- exact Hz.
- unfold v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25. splits; apply u64_range.
-
rewrite restrict_mkst_fx. unfold AFhb.SS0, AFhb.SR0, sr_set. cbn [bv_eqb]. unfold AFhb.E0, w64. apply (entry_st_ok_full tfibsegs).
+ set (E0 := Ereg regs (AFhb.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (HE2 : ew E0 2 = Z_to_bv 64 sp1) by (rewrite (AFhb.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); exact R2).
repeat (apply regs_ok_pin; [| intros XX; discriminate |]); [apply regs_ok_Ereg | ..]; cbn [sv_denot].
* rewrite C4, Etp. reflexivity.
* rewrite HE2, R8. unfold AFhb.YFRAME, w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* rewrite R9. reflexivity.
* rewrite R18. reflexivity.
* rewrite R19. reflexivity.
* rewrite R21. reflexivity.
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. set (E0 := Ereg regs (AFhb.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (rewrite (AFhb.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); exact SPV).
unfold AFhb.REG0, AFhb.R_STK, AFhb.YFRAME. apply Forall_cons; [|apply Forall_nil].
reg_intro. rewrite BV2. split; [lia|]. split; [clear - S2 S5; numconst; lia|]. split; [intros o Ho; lia|].
assert (SVk : forall (k : nat) r (a : Z) k0 (v : Z), nth_error AFh9.SAVED k = Some r -> v = bv_unsigned (getr regs0 r) -> a = 104 - 8 * Z.of_nat k ->
ew E0 k0 = w64 v -> YP09.chunk_ok tfibsegs E0 (mrestrict (w_H W) mem) sp1 (YP09.mkChunk a (CVal 8 (SOff k0 0)))).
{ intros k r a k0 v Hk -> -> Hk0. apply (chunk_atom8 E0 _ _ _ k0 (bv_unsigned (getr regs0 r))); [exact Hk0 | apply u64_range |].
eapply val_mem_addr; [exact (SV k r Hk) | rewrite S5; unfold AFhd.sp0; lia]. }
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_atom8 E0 _ _ _ 46%nat (zlen t)); [reflexivity | clear - Hz; lia | eapply val_mem_addr; [exact T0 | lia]].
* apply (SVk 0%nat 1%bv _ 50%nat v1); reflexivity.
* apply (SVk 1%nat 8%bv _ 51%nat v8); reflexivity.
* apply (SVk 2%nat 9%bv _ 52%nat v9); reflexivity.
* apply (SVk 3%nat 18%bv _ 53%nat v18); reflexivity.
* apply (SVk 4%nat 19%bv _ 54%nat v19); reflexivity.
* apply (SVk 5%nat 20%bv _ 55%nat v20); reflexivity.
* apply (SVk 6%nat 21%bv _ 56%nat v21); reflexivity.
* apply (SVk 7%nat 22%bv _ 57%nat v22); reflexivity.
* apply (SVk 8%nat 23%bv _ 58%nat v23); reflexivity.
* apply (SVk 9%nat 24%bv _ 59%nat v24); reflexivity.
* apply (SVk 10%nat 25%bv _ 60%nat v25); reflexivity.
+ apply pairwise_disjoint_of_extents. cbn. tauto.
+ split; [|split; exact I]. cbn [AFhb.FFQ f_atoms atoms_ok].
set (E0 := Ereg regs (AFhb.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (E2' : ew E0 2 = w64 sp1) by (rewrite (AFhb.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); exact R2).
assert (AV : forall k0 v, ew E0 k0 = w64 v -> 0 <= v < 2 ^ 64 -> afact_ok E0 k0 (mkAF 0 (2 ^ 64 - 1) 0)).
{ intros k0 v Hk0 Hv. apply (afact_intro E0 k0 v); [exact Hk0 | exact Hv | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, DRSTACK, AFhb.YFRAME in *.
split. { apply (afact_intro E0 2%nat sp1); [exact E2'| exact U1 | ceil; clear - CR0 S1 S2 S5; lia | change (2 ^ 4) with 16; exact S7' | clear; lia]. }
split. { apply (afact_intro E0 46%nat (zlen t)); [reflexivity | ceil; clear - CR0 Hz; lia | ceil; clear - CR0 Hz; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | clear; lia]. }
unfold v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25 in *.
splits; try exact I; (eapply AV; [reflexivity | apply u64_range]).
Qed.
End e.
End c.

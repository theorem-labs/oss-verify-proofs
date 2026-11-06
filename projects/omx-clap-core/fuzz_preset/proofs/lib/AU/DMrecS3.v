(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrecS3.v (commit ce1a656b52b7, file sha256 0d74ffbabfcd) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecS3.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 1eb86066e770) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1 / H2, a prior worker; interface DMwalkIF.v at dc3949af11c):
   the seeds of DoRecycle's batch-pop segment (YFha / YFhi.segYO, count >= 1) and its CacheDealloc-return segment
   (YFhb / YFhj) from DMrecL's states, the twins of DGif1db.seed_O / seed_Q (which read cgif's AR and RIx).
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (segment
   seeds; lane B1 reuse search the internal file LOOKUP-B1-drain.txt, B1LookupCheck CONFIRM). *)
(* Theorem Labs, 2026-10-30 (a prior worker): the image-B (asan-ubsan) twin of lib/A/DMrecS3.v at 14a6b2561a69, relocated by a Theorem Labs lane alreloc a5c53bb2bed4ad03 (every moved numeral a DoRecycle / LocalCache::Deallocate pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFf2 YFh9 YFha YFhc YFhb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhf YFhd YFhl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIF DMrecS DMrecL DMrecS2.
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
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : DMwalkIF.dr_pre_r B ARXr AOX DRq (as_inst B) ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation SB := (ly_space ly).
Local Notation hdra := (YFhd.hdra B ly).
Local Notation ostr := (DMrecL.ostr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation qstr := (DMrecL.qstr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Ltac open_PRE := pose proof PRE as (HAR0 & Hinst & HDQ & LY & IMG & HSTK & HBL & LENP & INIT & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & CELLS).
Local Notation entry_facts := (DMrecS2.entry_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (DMrecS2.sp_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp1_val := (DMrecS2.sp1_val_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma HLY : layout_ok ly /\ img_cover ly. Proof. open_PRE. exact (conj LY IMG). Qed.
Local Notation slot_facts := (DMrecS.slot_facts_r B ARXr DRq RMAXD HRM RV ly HLY).
Local Notation item_facts := (DMrecS.item_facts_r B ARXr DRq RMAXD RV ly).
Local Notation sb_cell := (DMrecS.sb_cell_r B ARXr DRq RMAXD TB RV ly).

Lemma seed_O_r : forall X b t lz qb W regs mem md k0 ks, ostr X (b :: t) lz qb W regs mem md -> b_items b = k0 :: ks ->
YFha.free_hyps W ly regs mem (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz.
Proof.
intros X b t lz qb W regs mem md k0 ks ST Hk0. destruct ST as [AC DQ BLr NE LEN CR LR A0 FR TM CE].
pose proof AC as [HAR _ _ _ _ HPRS _ _ _ _].
open_PRE.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27).
assert (Inb : In (b_self b) (map b_self (b :: t))) by (left; reflexivity).
pose proof (slot_facts X W mem md _ _ (b_self b) HAR DQ Inb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BNS).
assert (BL : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ apply DMrecL.blen_ok_cons in BLr as [BL1 _]. rewrite Hk0 in *. cbn [length] in *. lia. }
assert (Hk0in : In k0 (flat_map b_items (b :: t))) by (cbn [flat_map]; rewrite Hk0; left; reflexivity).
pose proof (item_facts X W mem md _ _ k0 HAR DQ Hk0in) as (I0 & I1 & I2 & I3 & I4).
assert (NXf : 0 <= firstaddr ly t < ASAN_CEIL /\ firstaddr ly t mod 8192 = 0).
{ destruct t as [|b' t']; [cbn; ceil; unfold ASAN_CEIL; split; [lia | reflexivity]|]. cbn [firstaddr].
assert (Inb' : In (b_self b') (map b_self (b :: b' :: t'))) by (right; left; reflexivity).
pose proof (slot_facts X W mem md _ _ (b_self b') HAR DQ Inb') as (B1' & B2' & B3' & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kHighMemBeg in *. lia. }
pose proof (batch_head_cells B ly (w_H W) mem b t CE) as (V0 & V8 & V16 & VI). cbv zeta in V0, V8, V16, VI.
pose proof (VI 0%nat k0 ltac:(rewrite Hk0; reflexivity)) as V24. rewrite Z.mul_0_r, Z.add_0_r in V24. fold (hdra k0) in V24.
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (LENb : 1 <= zlen (b_items b) <= kBatchSlots) by (clear - BL; unfold YFhd.zlen, kBatchSlots in *; lia).
assert (LENr : 1 <= zlen (b :: t) < 2 ^ 40) by (clear - LEN; rewrite YFhd.zlen_cons in *; unfold YFhd.zlen in *; lia).
constructor.
- exact LY.
- exact IMG.
- rewrite C4. exact Etp.
- rewrite SPV. unfold YFha.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. split; [exact E1 | exact E2].
- rewrite SPV. exact S7.
- rewrite SPV. intros a Ha. apply HPRS. unfold DMrecL.SYr. unfold YFha.YFRAME in Ha. numconst. lia.
- rewrite SPV. unfold YFha.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. splits; assumption.
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
rewrite restrict_mkst_fx. unfold YFha.SS0, YFha.SR0, sr_set. cbn [bv_eqb]. unfold YFha.E0, w64. apply (entry_st_ok_full tfibsegs).
+ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg| intros XX; discriminate |]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|].
* cbn [sv_denot]. rewrite C4, Etp. reflexivity.
* cbn [sv_denot]. fold (YFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (YFha.E2 ly regs), R2, R8. unfold YFha.YFRAME, w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* cbn [sv_denot]. rewrite R9. reflexivity.
* cbn [sv_denot]. rewrite R18. reflexivity.
* cbn [sv_denot]. rewrite R19. reflexivity.
* cbn [sv_denot]. rewrite R21. reflexivity.
* cbn [sv_denot]. fold (YFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (YFha.EqSZ ly regs), A0. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. fold (YFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
set (E0 := YFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (subst E0; rewrite (YFha.E2 ly regs); exact SPV).
assert (BV40 : bv_unsigned (ew E0 40) = SB + b_self b) by (subst E0; rewrite (YFha.EqB ly regs); unfold w64; apply unsigned_lit_small; exact B8).
unfold YFha.REG0, YFha.R_STK, YFha.R_B, YFha.YFRAME. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* reg_intro. rewrite BV2. split; [lia|]. split; [numconst; lia|]. split.
{ intros o Ho. apply apresent_writable; [numconst; lia|]. apply HPRS. unfold DMrecL.SYr. numconst. lia. }
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
+ apply pairwise_disjoint_of_extents. unfold YFha.REG0, YFha.R_STK, YFha.R_B, YFha.YFRAME, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
fold (YFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (YFha.E2 ly regs), (YFha.EqB ly regs), SPV. unfold w64. rewrite unsigned_lit_small by exact B8.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (A0' : bslot ly (b_self b) (SB + b_self b)) by (unfold bslot, kBatchBytes; lia). pose proof (BNS _ A0') as NS0.
split; [|exact (conj I I)]. split; [|exact I]. clear - NS0 E1 E2 S5 B1 B2. numconst. lia.
+ split; [|split; exact I]. cbn [YFha.FFO f_atoms atoms_ok].
fold (YFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
set (E0 := YFha.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
assert (E2' : ew E0 2 = w64 sp1) by (subst E0; rewrite (YFha.E2 ly regs); exact R2).
pose proof (mod64_range (b_bytes b)) as MB. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchSlots, YFha.YFRAME.
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
Definition v1 : Z := bv_unsigned (getr regs0 1).
Definition v8 : Z := bv_unsigned (getr regs0 8).   Definition v9 : Z := bv_unsigned (getr regs0 9).
Definition v18 : Z := bv_unsigned (getr regs0 18). Definition v19 : Z := bv_unsigned (getr regs0 19). Definition v20 : Z := bv_unsigned (getr regs0 20).
Definition v21 : Z := bv_unsigned (getr regs0 21). Definition v22 : Z := bv_unsigned (getr regs0 22). Definition v23 : Z := bv_unsigned (getr regs0 23).
Definition v24 : Z := bv_unsigned (getr regs0 24). Definition v25 : Z := bv_unsigned (getr regs0 25).
Lemma seed_Q_r : forall X t lz qb W regs mem md, qstr X t lz qb W regs mem md ->
YFhb.free_hyps W ly regs mem (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25.
Proof.
intros X t lz qb W regs mem md ST. destruct ST as [AC DQ BLr LEN CR LR FR TM CE].
pose proof AC as [HAR _ _ _ _ HPRS _ _ _ _]. open_PRE.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27).
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (Hz : 0 <= zlen t < 2 ^ 40) by (clear - LEN; unfold YFhd.zlen in *; lia).
constructor.
- exact LY.
- exact IMG.
- rewrite C4. exact Etp.
- rewrite SPV. unfold YFhb.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. split; [exact E1 | exact E2].
- rewrite SPV. exact S7'.
- rewrite SPV. intros a Ha. apply HPRS. unfold DMrecL.SYr. unfold YFhb.YFRAME in Ha. clear - Ha S5; numconst. lia.
- rewrite SPV. unfold YFhb.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. splits; assumption.
- unfold v1, w64. rewrite Z_to_bv_bv_unsigned. exact Era.
- exact Hz.
- unfold v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25. splits; apply u64_range.
-
rewrite restrict_mkst_fx. unfold YFhb.SS0, YFhb.SR0, sr_set. cbn [bv_eqb]. unfold YFhb.E0, w64. apply (entry_st_ok_full tfibsegs).
+ set (E0 := Ereg regs (YFhb.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (HE2 : ew E0 2 = Z_to_bv 64 sp1) by (rewrite (YFhb.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); exact R2).
repeat (apply regs_ok_pin; [| intros XX; discriminate |]); [apply regs_ok_Ereg | ..]; cbn [sv_denot].
* rewrite C4, Etp. reflexivity.
* rewrite HE2, R8. unfold YFhb.YFRAME, w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* rewrite R9. reflexivity.
* rewrite R18. reflexivity.
* rewrite R19. reflexivity.
* rewrite R21. reflexivity.
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. set (E0 := Ereg regs (YFhb.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (rewrite (YFhb.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); exact SPV).
unfold YFhb.REG0, YFhb.R_STK, YFhb.YFRAME. apply Forall_cons; [|apply Forall_nil].
reg_intro. rewrite BV2. split; [lia|]. split; [clear - S2 S5; numconst; lia|]. split; [intros o Ho; lia|].
assert (SVk : forall (k : nat) r (a : Z) k0 (v : Z), nth_error YFh9.SAVED k = Some r -> v = bv_unsigned (getr regs0 r) -> a = 104 - 8 * Z.of_nat k ->
ew E0 k0 = w64 v -> YP09.chunk_ok tfibsegs E0 (mrestrict (w_H W) mem) sp1 (YP09.mkChunk a (CVal 8 (SOff k0 0)))).
{ intros k r a k0 v Hk -> -> Hk0. apply (chunk_atom8 E0 _ _ _ k0 (bv_unsigned (getr regs0 r))); [exact Hk0 | apply u64_range |].
eapply val_mem_addr; [exact (SV k r Hk) | rewrite S5; unfold YFhd.sp0; lia]. }
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
+ split; [|split; exact I]. cbn [YFhb.FFQ f_atoms atoms_ok].
set (E0 := Ereg regs (YFhb.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (E2' : ew E0 2 = w64 sp1) by (rewrite (YFhb.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); exact R2).
assert (AV : forall k0 v, ew E0 k0 = w64 v -> 0 <= v < 2 ^ 64 -> afact_ok E0 k0 (mkAF 0 (2 ^ 64 - 1) 0)).
{ intros k0 v Hk0 Hv. apply (afact_intro E0 k0 v); [exact Hk0 | exact Hv | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, DRSTACK, YFhb.YFRAME in *.
split. { apply (afact_intro E0 2%nat sp1); [exact E2'| exact U1 | ceil; clear - CR0 S1 S2 S5; lia | change (2 ^ 4) with 16; exact S7' | clear; lia]. }
split. { apply (afact_intro E0 46%nat (zlen t)); [reflexivity | ceil; clear - CR0 Hz; lia | ceil; clear - CR0 Hz; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | clear; lia]. }
unfold v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25 in *.
splits; try exact I; (eapply AV; [reflexivity | apply u64_range]).
Qed.
End e.
End c.

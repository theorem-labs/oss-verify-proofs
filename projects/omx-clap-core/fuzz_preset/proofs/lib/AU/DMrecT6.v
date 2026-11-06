(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrecT6.v (commit ce1a656b52b7, file sha256 5fa5bb72d81a) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecT6.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 660980b9a907) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 1 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1 / H2, a prior worker; interface DMwalkIF.v at dc3949af11c):
   DoRecycle's COUNT-0 step over the opaque relations: the seed of DMrec.RZ's segment from the pop state of a batch
   with no items ([seed_Z_r]; the class-24 bound at RMAXD <= kFreeArrayOffset) and the step itself ([T_O0_r],
   DMrecZ.segZ): from the pop straight to CacheDealloc's call for the batch object, no Recycle call.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (count-0
   step; lane B1 reuse search the internal file LOOKUP-B1-drain.txt, B1LookupCheck CONFIRM). *)
(* Theorem Labs, 2026-10-30 (a prior worker): the image-B (asan-ubsan) twin of lib/A/DMrecT6.v at 14a6b2561a69, relocated by a Theorem Labs lane alreloc a5c53bb2bed4ad03 (every moved numeral a DoRecycle / LocalCache::Deallocate pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFf2 YFh9 YFha YFhc YFhb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhf YFhd YFhl YFhg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFhi YFhj YFhk MnRecycle. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMrec DMrecZ DMwalkIF DMrecS DMrecL DMrecS2 DMrecS3 DMrecT1 DMrecT4. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG ErrnoApart. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import ErrnoApartcgif.
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
Local Notation accr := (DMrecL.accr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation ostr := (DMrecL.ostr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation OSTr := (DMrecL.OSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
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
Local Notation RCSTr := (DMrecL.RCSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation seed_O := (DMrecS3.seed_O_r B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE).

Ltac numconst2 := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, DMwalkIF.DRSTACK_X, KSTACK, KSTACK_CF, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, YFh9.YFRAME, YFha.YFRAME, YFhc.YFRAME, YFhb.YFRAME in *.
Ltac nsp2 := unfold ascratch in *; unfold DMrecL.SYr in *; unfold spZ, raZ, YFhd.sp1, YFhd.sp0 in *; numconst2.
Ltac csv CS r z := rewrite (YFhg.csv_get _ _ CS r z ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
Local Notation rcstr := (DMrecL.rcstr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation rstr := (DMrecL.rstr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation cdstr := (DMrecL.cdstr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation qstr := (DMrecL.qstr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation RSTr := (DMrecL.RSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation QSTr := (DMrecL.QSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation snot := (DMrecS2.stack_not_owned_r B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation item_facts := (DMrecS.item_facts_r B ARXr DRq RMAXD RV ly).
Local Notation slot_puser := (DMrecS.slot_puser_r B ARXr DRq RMAXD RV ly).
Local Notation slot_vs_chunk := (DMrecS.slot_vs_chunk_r B ARXr DRq RMAXD RV ly).
Local Notation ARXr_wvb := (DMrecT4.ARXr_wvb B ARXr AOX DRq FR ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sb_cell := (DMrecS.sb_cell_r B ARXr DRq RMAXD TB RV ly).
Local Notation CDSTr := (DMrecL.CDSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation next_hdr := (YFhl.next_hdr B ly).

Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma seed_Z_r : forall X b t lz qb W regs mem md, ostr X (b :: t) lz qb W regs mem md -> b_items b = [] ->
DMrec.RZ.free_hyps W ly regs mem (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz.
Proof.
intros X b t lz qb W regs mem md ST Hk. destruct ST as [AC DQ BLr NE LEN CR LR A0 FRc TM CE].
pose proof AC as [HAR _ _ _ _ HPRS _ _ _ _].
open_PRE.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27).
pose proof (DMrecS.ly_facts ly LY IMG) as (L1 & L2 & L3 & L4 & _ & _ & _ & FS3 & FT1 & FT2 & FT3).
assert (FS1 : kHighMemBeg <= SB) by (clear - L1 L3; lia).
assert (FS2 : SB + kSpaceSize <= ASAN_CEIL) by (clear - L2 L4; unfold kSpaceSize, kPrimResvSize in *; lia).
assert (Inb : In (b_self b) (map b_self (b :: t))) by (left; reflexivity).
pose proof (slot_facts X W mem md _ _ (b_self b) HAR DQ Inb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BNS).
assert (B7' : SB + b_self b + kBatchBytes <= SB + region_off kBatchClass + kFreeArrayOffset) by (destruct HRM as [_ HR2]; clear - B7 HR2; lia).
assert (NXf : 0 <= firstaddr ly t < ASAN_CEIL /\ firstaddr ly t mod 8192 = 0).
{ destruct t as [|b' t']; [cbn; ceil; unfold ASAN_CEIL; split; [lia | reflexivity]|]. cbn [firstaddr].
assert (Inb' : In (b_self b') (map b_self (b :: b' :: t'))) by (right; left; reflexivity).
pose proof (slot_facts X W mem md _ _ (b_self b') HAR DQ Inb') as (B1' & B2' & B3' & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kHighMemBeg in *. lia. }
pose proof (batch_head_cells B ly (w_H W) mem b t CE) as (V0 & V8 & V16 & _). cbv zeta in V0, V8, V16.
rewrite Hk in V16. cbn [YFhd.zlen length Z.of_nat] in V16.
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FRc as [CB SV].
assert (LENr : 1 <= zlen (b :: t) < 2 ^ 40) by (clear - LEN; rewrite YFhd.zlen_cons in *; unfold YFhd.zlen in *; lia).
constructor.
- exact LY.
- exact IMG.
- rewrite C4. exact Etp.
- rewrite SPV. unfold DMrec.RZ.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. split; [exact E1 | exact E2].
- rewrite SPV. exact S7.
- rewrite SPV. intros a Ha. apply HPRS. unfold DMrecL.SYr. unfold DMrec.RZ.YFRAME in Ha. clear - Ha S5. nsp. lia.
- rewrite SPV. unfold DMrec.RZ.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by lia. splits; assumption.
- splits; [exact B6 | exact B7' | exact B3].
- exact NXf.
- split; [apply mod64_range | exact Rqb].
- exact LENr.
- exact Rlz.
-
rewrite restrict_mkst_fx. unfold DMrec.RZ.SS0, YFha.SR0, sr_set. cbn [bv_eqb]. unfold DMrec.RZ.E0, w64. apply (entry_st_ok_full tfibsegs).
+ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg| intros XX; discriminate |]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|].
* cbn [sv_denot]. rewrite C4, Etp. reflexivity.
* cbn [sv_denot]. fold (DMrec.RZ.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz).
rewrite (DMrec.RZ.E2 ly regs), R2, R8. unfold DMrec.RZ.YFRAME, YFha.YFRAME, w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* cbn [sv_denot]. rewrite R9. reflexivity.
* cbn [sv_denot]. rewrite R18. reflexivity.
* cbn [sv_denot]. rewrite R19. reflexivity.
* cbn [sv_denot]. rewrite R21. reflexivity.
* cbn [sv_denot]. fold (DMrec.RZ.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz).
rewrite (DMrec.RZ.EqSZ ly regs), A0. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. fold (DMrec.RZ.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz).
set (E0 := DMrec.RZ.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (subst E0; rewrite (DMrec.RZ.E2 ly regs); exact SPV).
assert (BV40 : bv_unsigned (ew E0 40) = SB + b_self b) by (subst E0; rewrite (DMrec.RZ.EqB ly regs); unfold w64; apply unsigned_lit_small; exact B8).
unfold DMrec.RZ.REG0, DMrec.RZ.R_STK, DMrec.RZ.R_B, fatom8, DMrec.RZ.YFRAME. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* reg_intro. rewrite BV2. split; [lia|]. split; [numconst; lia|]. split.
{ intros o Ho. apply apresent_writable; [numconst; lia|]. apply HPRS. unfold DMrecL.SYr. numconst. lia. }
repeat apply Forall_cons; try apply Forall_nil.
-- apply (chunk_atom8d E0 _ _ _ 32%nat t_cache (ly_T ly)); [reflexivity | clear - FT1 FT2; numconst; lia | clear - FT1 FT2; numconst; lia | eapply val_mem_addr; [exact CB | lia]].
-- apply (chunk_atom8 E0 _ _ _ 46%nat (zlen (b :: t))); [reflexivity | lia | eapply val_mem_addr; [exact T0 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 40%nat (SB + b_self b)); [reflexivity | exact B8 | eapply val_mem_addr; [exact T8 | cbn [firstaddr]; lia]].
-- apply (chunk_atom8 E0 _ _ _ 49%nat lz); [reflexivity | numconst; lia | eapply val_mem_addr; [exact T16 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 47%nat qb); [reflexivity | lia | eapply val_mem_addr; [exact T24 | lia]].
* reg_intro. rewrite BV40. split; [lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
-- apply (chunk_atom8 E0 _ _ _ 41%nat (firstaddr ly t)); [reflexivity | numconst; lia | eapply val_mem_addr; [exact V0 | lia]].
-- apply (chunk_atom8 E0 _ _ _ 42%nat (b_bytes b mod 2 ^ 64)); [reflexivity | apply mod64_range | eapply val_mem_addr; [apply val_mem_mod64; exact V8 | lia]].
-- eapply chunk_ok_val; [ | | | eapply val_mem_addr; [exact V16 | lia]]; [cbn [sv_denot]; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia].

* reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom8 E0 _ _ _ 34%nat SB); [reflexivity | clear - FS1 FS2; numconst; lia | rewrite Z.add_0_l; exact (sb_cell X W mem md _ _ HAR DQ)].
+ apply pairwise_disjoint_of_extents. unfold DMrec.RZ.REG0, DMrec.RZ.R_STK, DMrec.RZ.R_B, fatom8, DMrec.RZ.YFRAME, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
fold (DMrec.RZ.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz).
rewrite (DMrec.RZ.E2 ly regs), (DMrec.RZ.EqB ly regs), SPV. unfold w64. rewrite unsigned_lit_small by exact B8.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (A0' : bslot ly (b_self b) (SB + b_self b)) by (unfold bslot, kBatchBytes; lia). pose proof (BNS _ A0') as NS0.
assert (A23 : bslot ly (b_self b) (SB + b_self b + 23)) by (unfold bslot, kBatchBytes; lia). pose proof (BNS _ A23) as NS23.
repeat split; try exact I; clear - NS0 NS23 E1 E2 S1 S5 B1 B2 FS1; numconst; lia.
+ split; [|split; exact I]. cbn [DMrec.RZ.FFZ f_atoms atoms_ok].
fold (DMrec.RZ.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz).
set (E0 := DMrec.RZ.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b :: t)) qb lz).
assert (E2' : ew E0 2 = w64 sp1) by (subst E0; rewrite (DMrec.RZ.E2 ly regs); exact R2).
pose proof (mod64_range (b_bytes b)) as MB.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchBytes, kBatchSlots, kThreadObjSize, kSpaceSize, DMrec.RZ.YFRAME in *.
split. { apply (afact_intro E0 2%nat sp1); [exact E2'| exact U1 | lia | change (2 ^ 4) with 16; exact S7 | lia]. }
split. { apply (afact_intro E0 32%nat (ly_T ly)); [reflexivity | lia | lia | change (2 ^ 12) with 4096; exact FT3 | lia]. }
split. { apply (afact_intro E0 34%nat SB); [reflexivity | lia | lia | change (2 ^ 16) with 65536; exact FS3 | lia]. }
split. { apply (afact_intro E0 40%nat (SB + b_self b)); [reflexivity | exact B8 | lia | change (2 ^ 13) with 8192; exact B3 | lia]. }
split. { apply (afact_intro E0 41%nat (firstaddr ly t)); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact (proj2 NXf) | lia]. }
split. { apply (afact_intro E0 42%nat (b_bytes b mod 2 ^ 64)); [reflexivity | exact MB | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (afact_intro E0 46%nat (zlen (b :: t))); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (afact_intro E0 47%nat qb); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split; [|exact I]. { apply (afact_intro E0 49%nat lz); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
Qed.

Lemma T_O0_r : forall X b t lz qb W regs mem md, ostr X (b :: t) lz qb W regs mem md -> b_items b = [] ->
SRr tfibsegs W (cfg_at tfibsegs 0x3483c regs mem md) (CDSTr X b t).
Proof.
intros X b t lz qb W regs mem md ST Hk. pose proof ST as [AC DQ BLr NE LEN CR LR A0 FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV.
pose proof BLr as BLc. apply DMrecL.blen_ok_cons in BLc as [_ BLt].
pose proof (seed_Z_r X b t lz qb W regs mem md ST Hk) as FH.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (DMrecZ.segZ W ly regs mem md _ _ _ _ _ _ (m_vm_materialized md) FH)|].
intros W' c' _ HP. destruct HP as (-> & regs' & mem' & mat & -> & R2 & R1 & CS & R10 & R11 & R12 & R13 & MQ & PRS & CELLS). cbv zeta in CELLS.
destruct CELLS as (V0 & V8 & V16 & V24). rewrite SPV in *.
set (WINP := DMrec.RZ.WIN regs) in *.
assert (WE : forall a, WINP a <-> sp0 <= a < sp0 + 32) by (intros a; subst WINP; unfold DMrec.RZ.WIN; rewrite SPV; clear - S5; unfold DMrec.RZ.YFRAME; nsp; lia).
assert (WST : forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; apply WE in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, WINP a \/ ~ WINP a) by (intros a; subst WINP; unfold DMrec.RZ.WIN; apply ivl_dec).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ WINP a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. exact (aview_after_write (w_H W) mem mem' _ a MQ Ha Hn). }
assert (MQ' : forall x : word, ~ (sp0 <= bv_unsigned x < sp0 + 32) -> mem' x = mem x) by (intros x Hx; apply MQ; intros Hw; apply WE in Hw; exact (Hx Hw)).
pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof CR as (C3 & C4 & C26 & C27).
exists (DMrec.RZ.LZn (firstaddr ly t) lz), (zcanon (qb - b_bytes b mod 2 ^ 64)), regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
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
- cbn [flat_map] in DQ. rewrite Hk in DQ. exact DQ.
- exact BLt.
- rewrite zlen_cons in LEN. clear - LEN. lia.
- unfold YFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
- unfold YFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
- exact R1.
- exact R10.
- exact R11.
- exact R12.
- exact R13.
- apply (frame_cells_keep ly regs0 W W mem mem'); [|exact FRc]. intros a Ha. apply AG; [clear - Ha S5 U0 U1; nsp; lia|]. intros Hw. apply WE in Hw. clear - Ha Hw S5. nsp. lia.
- unfold YFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_addr; [exact V0 | rewrite zlen_cons; lia] || (replace (zlen t) with (zlen (b :: t) - 1) by (rewrite zlen_cons; lia); eapply val_mem_addr; [exact V0 | clear - S5; unfold DMrec.RZ.YFRAME; nsp; lia]).
+ eapply val_mem_addr; [exact V8 | clear - S5; unfold DMrec.RZ.YFRAME; nsp; lia].
+ eapply val_mem_addr; [exact V16 | clear - S5; unfold DMrec.RZ.YFRAME; nsp; lia].
+ eapply val_mem_addr; [exact V24 | clear - S5; unfold DMrec.RZ.YFRAME; nsp; lia].
+ unfold DMrec.RZ.LZn. destruct (firstaddr ly t =? 0); [ceil; unfold ASAN_CEIL; lia | exact Rlz].
+ unfold zcanon, M64. apply Z.mod_pos_bound. lia.
- apply (batch_cells_tail B ly _ b t).
apply (batch_cells_xfer_r (b :: t) (aview tfibsegs (w_H W) mem)); [exact BLr | | exact CE].
intros b' a Hb Hs. pose proof (slot_facts X W mem md _ _ (b_self b') aAR DQ (in_map b_self _ _ Hb)) as (B1 & B2 & _ & _ & _ & _ & _ & _ & BNS).
apply AG; [unfold bslot, kBatchBytes in Hs; clear - Hs B1 B2; numconst; lia|]. intros Hw.
exact (BNS a Hs (WST a Hw)).
Qed.
End e.
End c.

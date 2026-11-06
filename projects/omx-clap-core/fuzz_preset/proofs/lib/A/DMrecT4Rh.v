(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecT4Rh.v (commit 67deba317dfb, blob 2f3ec23c9ddc) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 9 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFhi AFhj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MnRecycle.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrecS DMrecL DMrecS2 DMrecS3 DMrecT1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrecT4 DMrecLRh DMrecS3Rh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRecStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFRhA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH.
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
Local Notation HloX := (DMrecT4.HloX B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation ARXr_wvb := (DMrecT4.ARXr_wvb B ARXr AOX DRq FR ly X0 P0 W0 regs0 mem0 md0 PRE).
Lemma RC_pre_rh : forall X b t k ks i lz qb W regs mem md, rcstrh X b t (k :: ks) i lz qb W regs mem md ->
rcc_pre_x B ARXr (as_inst B) ly X k (sp1 + 8) W regs mem md /\ DRq X (k :: ks ++ flat_map b_items t) (b_self b :: map b_self t).
Proof.
intros X b t k ks i lz qb W regs mem md ST. destruct ST as [AC DQ BLt ITS NE BL LEN CR LR BR RA A0 A1 S7r S9r FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK aSTP].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7). pose proof HloX as HX.
pose proof (sp1_val regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27).
pose proof (item_facts X W mem md _ _ k aAR DQ (or_introl eq_refl)) as (I0 & I1 & I2 & I3 & I4).
destruct FRc as [CB SV].
split; [|exact DQ].
unfold rcc_pre_x, spZ, raZ. rewrite SPV, RA. change (bv_unsigned (w64 0x3479c)) with 0x3479c.
splits.
- exact aAR.
- exact aINI.
- vm_compute. reflexivity.
- lia.
- exact S7.
- clear - HX S5. nsp2. lia.
- lia.
- clear - E2 S5. nsp2. lia.
- rewrite S5. replace (sp0 - 112 + 8) with (sp0 + (-13) * 8) by lia. rewrite Z_mod_plus_full. clear - S6. apply Z.mod_divide; [lia|]. apply Z.mod_divide in S6 as [q Hq]; [|lia]. exists (2 * q). lia.
- intros a Ha. apply aPRS. clear - Ha S5. nsp2. lia.
- intros a Ha. apply aPRS. clear - Ha S5. nsp2. lia.
- eapply val_mem_addr; [exact CB | reflexivity].
- rewrite C3. exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). reflexivity.
- exact A0.
- rewrite (A1 k ks eq_refl). f_equal. unfold kChunkHeaderSize in I0. unfold kChunkHeaderSize. lia.
Qed.

Lemma RC_post_rh : forall X b t k ks i lz qb W regs mem md (r : unit * astate) W' c',
rcstrh X b t (k :: ks) i lz qb W regs mem md -> YGcfRecStep.rec_step ly X (snd r) ->
(exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  YGcfRehidePost.acall_post_x_rh B ARXr AOX (as_inst B) KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX (as_inst B) KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) (ks ++ flat_map b_items t) (b_self b :: map b_self t) /\ st_cache_inited (snd r) = true /\
  (forall a, AOX ly (snd r) a -> AOX ly X a)) ->
RSTrh (snd r) b t ks (S i) W' c'.
Proof.
intros X b t k ks i lz qb W regs mem md [ru X1] W' c' ST STP HL. destruct ST as [AC DQ BLt ITS NE BL LEN CR LR BR RA A0 A1 S7r S9r FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK aSTP].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7). pose proof HloX as HX.
pose proof (sp1_val regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21). pose proof BR as (R20 & R22 & R24).
destruct HL as (regs' & mem' & md' & -> & (AR1 & LLE & WLE & CSV & SIO & FRM & PRS) & RAW & EK & MK & PU & PM & DRQ & INI & OWN1). cbn [fst snd] in *.
unfold acall_raw_x in RAW.
cbn [ImgBase.im_segs AImg_A] in FRM, PU, MK.
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. change (bv_unsigned (w64 0x3479c)) with 0x3479c. rewrite SPV in FRM, RAW, PRS.
assert (SH1 : forall a, AOX ly X1 a -> AOX ly X0 a) by (intros a O; exact (aOWN a (OWN1 a O))).
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK_CF <= a < sp1) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hs Hn. apply FRM; [exact Ha | exact (snot X a aOWN Hs) | exact (snot X1 a SH1 Hs) | | intros F; exact F
| exact (YGcfRehidePost.dead_shadow_new_high ly X X1 a ltac:(clear - Hs E7; lia))].
intros [C|C]; [exact (Hn C)|]. rewrite (ts_errno _ TB) in C. clear - C Hs E7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, kHighMemBeg in *. lia. }
assert (AGB : forall b' a, In b' (b :: t) -> bslot ly (b_self b') a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros b' a Hb Hs. assert (Hz : In (b_self b') (b_self b :: map b_self t)) by exact (in_map b_self _ _ Hb).
pose proof (slot_facts X W mem md _ _ (b_self b') aAR DQ Hz) as (B1 & B2 & _).
apply PU; [unfold bslot, kBatchBytes in Hs; clear - Hs B1 B2; numconst2; lia | exact (slot_puser X W mem md _ _ (b_self b') aAR DQ Hz a Hs) | exact (slot_vs_chunk X W mem md _ _ (b_self b') k aAR DQ Hz (or_introl eq_refl) a Hs)]. }
exists lz, qb, regs', mem', md'. split; [reflexivity|].
destruct ITS as (done & Hits & Hdone).
constructor.
- constructor.
+ exact AR1.
+ eapply YA0nH.wle_in_mono; [| exact (DMrecLRh.wle_in_join tfibsegs _ _ W0 W W' aWLE WLE)].
intros a [Ha|Ha]; [exact (DMrecLRh.rs_left ly X0 X X1 a STP Ha) | exact (DMrecLRh.rs_right ly X0 X X1 a aSTP Ha)].
+ exact (same_io_trans _ _ _ aIO SIO).
+ exact SH1.
+ intros a Ha N0 N1 NS NT ND. transitivity (aview tfibsegs (w_H W) mem a).
{ apply (FRM a Ha); [intros O; exact (N0 (aOWN a O)) | exact N1 | | intros F; exact F
  | intros Hd; exact (ND (DMrecLRh.rs_right ly X0 X X1 a aSTP Hd))].
  intros [C|C]; apply NS; [left; clear - C S5; nsp2; lia | right; exact C]. }
exact (aFR a Ha N0 ltac:(intros O; exact (N0 (aOWN a O))) NS NT (fun Hd => ND (DMrecLRh.rs_left ly X0 X X1 a STP Hd))).
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK_CF) sp1 a) as [C|C]; [exact (PRS a C)|].
apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [unfold DMrecL.SYr in Ha; clear - Ha S1 S2; nsp2; lia | | exact (aPRS a Ha)].
apply AGS; [unfold DMrecL.SYr in Ha; clear - Ha S1 S2; nsp2; lia | unfold DMrecL.SYr in Ha; clear - Ha E1 E2 HX; nsp2; lia | exact C].
+ exact INI.
+ intros x N0 N1 NS NT. rewrite (RAW x); [exact (aRAW x N0 ltac:(intros O; exact (N0 (aOWN _ O))) NS NT) | intros O; exact (N0 (aOWN _ O)) | exact N1 | | intros F; exact F].
intros [C|C]; apply NS; [left; clear - C S5; nsp2; lia | right; exact C].
+ exact (DMrecT1.ek_trans B mem0 mem mem' aEK EK).
+ exact (MemnormLocG.memnorm_keep_trans tfibsegs mem0 mem mem' aMK MK).
+ exact (DMrecLRh.rs_trans ly X0 X X1 aSTP STP).
- exact DRQ.
- exact BLt.
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
- apply (frame_cells_keep ly regs0 W W' mem mem'); [|exact FRc]. intros a Ha. apply AGS; [clear - Ha U0 U1 S5; nsp2; lia | clear - Ha E1 E2 S5 HX; nsp2; lia | clear - Ha; lia].
- apply (tmp_cells_keep ly regs0 W W' mem mem'); [|exact TM]. intros a Ha. apply AGS; [clear - Ha U0 S2; nsp2; lia | clear - Ha E1 E2; nsp2; lia | clear - Ha S5; nsp2; lia].
- apply (batch_cells_xfer_r (b :: t) (aview tfibsegs (w_H W) mem)); [| exact AGB | exact CE].
apply DMrecL.blen_ok_cons. split; [lia | exact BLt].
Qed.

Lemma CD_pre_rh : forall X b t lz qb W regs mem md, cdstrh X b t lz qb W regs mem md ->
cd_pre_x B ARXr (as_inst B) ly X (b_self b) W regs mem md /\ DRq X (flat_map b_items t) (b_self b :: map b_self t).
Proof.
intros X b t lz qb W regs mem md ST. destruct ST as [AC DQ BLt LEN CR LR RA A0 A1 A2 A3 FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK aSTP].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7). pose proof HloX as HX.
pose proof (sp1_val regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27).
split; [|exact DQ].
unfold cd_pre_x, spZ, raZ. rewrite SPV, RA. change (bv_unsigned (w64 0x347d4)) with 0x347d4.
splits.
- exact aAR.
- exact aINI.
- vm_compute. reflexivity.
- lia.
- exact S7.
- clear - HX S5. nsp2. lia.
- clear - E2 S5. nsp2. lia.
- intros a Ha. apply aPRS. clear - Ha S5. nsp2. lia.
- rewrite C3. exact Egp.
- rewrite C4, Etp, (ts_tp _ TB). reflexivity.
- exact A0.
- rewrite A1, (DMrecS.inst_alloc B TB). reflexivity.
- exact A2.
- exact A3.
Qed.

Lemma CD_post_rh : forall X b t lz qb W regs mem md (r : unit * astate) W' c',
cdstrh X b t lz qb W regs mem md -> YGcfRecStep.rec_step ly X (snd r) ->
(exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX (as_inst B) KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX (as_inst B) KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) (flat_map b_items t) (map b_self t) /\ st_cache_inited (snd r) = true /\
  (forall a, AOX ly (snd r) a -> AOX ly X a)) ->
QSTrh (snd r) t W' c'.
Proof.
intros X b t lz qb W regs mem md [ru X2] W' c' ST STP HL. destruct ST as [AC DQ BLt LEN CR LR RA A0 A1 A2 A3 FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK aSTP].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7). pose proof HloX as HX.
pose proof (sp1_val regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
destruct HL as (regs' & mem' & md' & -> & (AR2 & LLE & WLE & CSV & SIO & FRM & PRS) & RAW & EK & MK & PU & PM & DRQ & INI & OWN2). cbn [fst snd] in *.
unfold acall_raw_x in RAW.
cbn [ImgBase.im_segs AImg_A] in FRM, PU, MK.
unfold ascratch in *. unfold raZ, spZ in *. rewrite RA. change (bv_unsigned (w64 0x347d4)) with 0x347d4. rewrite SPV in FRM, RAW, PRS.
assert (SH2 : forall a, AOX ly X2 a -> AOX ly X0 a) by (intros a O; exact (aOWN a (OWN2 a O))).
assert (AGS : forall a, 0 <= a < 2 ^ 64 -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp1 - KSTACK_CF <= a < sp1) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hs Hn. apply FRM; [exact Ha | exact (snot X a aOWN Hs) | exact (snot X2 a SH2 Hs) | | intros F; exact F].
intros [C|C]; [exact (Hn C)|]. rewrite (ts_errno _ TB) in C. clear - C Hs E7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, kHighMemBeg in *. lia. }
assert (AGB : forall b' a, In b' t -> bslot ly (b_self b') a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros b' a Hb Hs. assert (Hz : In (b_self b') (b_self b :: map b_self t)) by (right; exact (in_map b_self _ _ Hb)).
pose proof (slot_facts X W mem md _ _ (b_self b') aAR DQ Hz) as (B1 & B2 & _).
apply PU; [unfold bslot, kBatchBytes in Hs; clear - Hs B1 B2; numconst2; lia | exact (slot_puser X W mem md _ _ (b_self b') aAR DQ Hz a Hs)]. }
exists lz, qb, regs', mem', md'. split; [reflexivity|].
constructor.
- constructor.
+ exact AR2.
+ intros a Ha. destruct (aWLE a (WLE a Ha)) as [H0|Hd]; [left; exact H0 | right; exact (DMrecLRh.rs_left ly X0 X X2 _ STP Hd)].
+ exact (same_io_trans _ _ _ aIO SIO).
+ exact SH2.
+ intros a Ha N0 N2 NS NT ND. transitivity (aview tfibsegs (w_H W) mem a).
{ apply (FRM a Ha); [intros O; exact (N0 (aOWN a O)) | exact N2 | | intros F; exact F].
  intros [C|C]; apply NS; [left; clear - C S5; nsp2; lia | right; exact C]. }
exact (aFR a Ha N0 ltac:(intros O; exact (N0 (aOWN a O))) NS NT (fun Hd => ND (DMrecLRh.rs_left ly X0 X X2 a STP Hd))).
+ intros a Ha. destruct (ivl_dec (sp1 - KSTACK_CF) sp1 a) as [C|C]; [exact (PRS a C)|].
apply (apresent_aview_xfer (w_H W) (w_H W') mem mem' a); [unfold DMrecL.SYr in Ha; clear - Ha S1 S2; nsp2; lia | | exact (aPRS a Ha)].
apply AGS; [unfold DMrecL.SYr in Ha; clear - Ha S1 S2; nsp2; lia | unfold DMrecL.SYr in Ha; clear - Ha E1 E2 HX; nsp2; lia | exact C].
+ exact INI.
+ intros x N0 N2 NS NT. rewrite (RAW x); [exact (aRAW x N0 ltac:(intros O; exact (N0 (aOWN _ O))) NS NT) | intros O; exact (N0 (aOWN _ O)) | exact N2 | | intros F; exact F].
intros [C|C]; apply NS; [left; clear - C S5; nsp2; lia | right; exact C].
+ exact (DMrecT1.ek_trans B mem0 mem mem' aEK EK).
+ exact (MemnormLocG.memnorm_keep_trans tfibsegs mem0 mem mem' aMK MK).
+ exact (DMrecLRh.rs_trans ly X0 X X2 aSTP STP).
- exact DRQ.
- exact BLt.
- exact LEN.
- unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; [csv CSV (3%bv : bv 5) 3 | csv CSV (4%bv : bv 5) 4 | csv CSV (26%bv : bv 5) 26 | csv CSV (27%bv : bv 5) 27]; reflexivity.
- unfold AFhd.loop_regs. rewrite <- Q2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21.
splits; [csv CSV (2%bv : bv 5) 2 | csv CSV (8%bv : bv 5) 8 | csv CSV (9%bv : bv 5) 9 | csv CSV (18%bv : bv 5) 18 | csv CSV (19%bv : bv 5) 19 | csv CSV (21%bv : bv 5) 21]; reflexivity.
- apply (frame_cells_keep ly regs0 W W' mem mem'); [|exact FRc]. intros a Ha. apply AGS; [clear - Ha U0 U1 S5; nsp2; lia | clear - Ha E1 E2 S5 HX; nsp2; lia | clear - Ha; lia].
- apply (tmp_cells_keep ly regs0 W W' mem mem'); [|exact TM]. intros a Ha. apply AGS; [clear - Ha U0 S2; nsp2; lia | clear - Ha E1 E2; nsp2; lia | clear - Ha S5; nsp2; lia].
- apply (batch_cells_xfer_r t (aview tfibsegs (w_H W) mem)); [exact BLt | exact AGB | exact CE].
Qed.

Definition postQOrh (X : astate) (t : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
match t with [] => DMwalkIFRhA.dr_leaf_rh B ARXr AOX DRq (as_inst B) ly X0 W0 regs0 mem0 md0 (tt, X) W' c' | _ :: _ => OSTrh X t W' c' end.
Local Notation v1 := (AFhl.v1 regs0).   Local Notation v8 := (AFhl.v8 regs0).   Local Notation v9 := (AFhl.v9 regs0).
Local Notation v18 := (AFhl.v18 regs0). Local Notation v19 := (AFhl.v19 regs0). Local Notation v20 := (AFhl.v20 regs0).
Local Notation v21 := (AFhl.v21 regs0). Local Notation v22 := (AFhl.v22 regs0). Local Notation v23 := (AFhl.v23 regs0).
Local Notation v24 := (AFhl.v24 regs0). Local Notation v25 := (AFhl.v25 regs0).
Lemma T_Q_rh : forall X t lz qb W regs mem md, qstrh X t lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x347d4 regs mem md) (fun W' c' => postQOrh X t W' c' /\ ms_mem (cfg_ms c') = mem).
Proof.
intros X t lz qb W regs mem md ST. pose proof ST as [AC DQ BLt LEN CR LR FRc TM CE].
pose proof AC as [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK aSTP].
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV. pose proof CR as (C3 & C4 & C26 & C27). pose proof LR as (Q2 & Q8 & Q9 & Q18 & Q19 & Q21).
first [pose proof (DMrecS3Rh.seed_Q_rh B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE X t lz qb W regs mem md ST) as FH
| pose proof (DMrecS3Rh.seed_Q_rh B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE X t lz qb W regs mem md ST) as FH].
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (AFhj.segYQ W ly regs mem md (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 (m_vm_materialized md) FH)|].
intros W' c' _ HP. unfold AFhb.postQ in HP. unfold postQOrh.
destruct t as [|b t'].
-
rewrite zlen_nil, Z.eqb_refl in HP.
destruct HP as (-> & _ & regs' & mat & -> & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & CS).
split; [|reflexivity].
exists regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, AFhl.v1. reflexivity. }
cbn [snd]. split.
+ split; [exact (ARXr_wvb X W mem md mat aAR aOWN)|]. split; [apply layout_le_refl|]. split; [exact aWLE|]. split.
{ unfold AFhl.v8, AFhl.v9, AFhl.v18, AFhl.v19, AFhl.v20, AFhl.v21, AFhl.v22,
AFhl.v23, AFhl.v24, AFhl.v25, w64 in *. rewrite !Z_to_bv_bv_unsigned in *.
apply aregs_intro; try assumption.
- rewrite R2, SPV, S5. unfold AFhb.YFRAME, AFhd.sp0. replace (bv_unsigned (getr regs0 2) - 112 + 112) with (bv_unsigned (getr regs0 2)) by lia. apply Z_to_bv_bv_unsigned.
- rewrite <- C3; apply CS; cbn; tauto.
- rewrite <- C4; apply CS; cbn; tauto.
- rewrite <- C26; apply CS; cbn; tauto.
- rewrite <- C27; apply CS; cbn; tauto. }
split; [eapply same_io_trans; [exact aIO | apply same_io_with_vm_backing]|]. split.
{ intros a Ha N0 N1 NS NT. exact (aFR a Ha N0 N1 NS NT). }
intros a Ha. apply aPRS. unfold DMrecL.SYr. unfold spZ in Ha. clear - Ha. nsp2. lia.
+ split. { intros x N0 N1 NS NT. exact (aRAW x N0 N1 NS NT). }
split. { exact aEK. }
split. { exact aMK. }
split. { exact DQ. }
split. { exact aINI. }
split. { exact aOWN. }
intros a Ha. apply aPRS. unfold DMrecL.SYr. unfold spZ in Ha. clear - Ha. nsp2. lia.
-
replace (zlen (b :: t') =? 0) with false in HP by (symmetry; apply Z.eqb_neq; rewrite zlen_cons; unfold AFhd.zlen; lia).
destruct HP as (-> & _ & regs' & mat & -> & R2 & CS & R10).
split; [|reflexivity].
exists lz, qb, regs', mem, (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
constructor.
+ constructor; [exact (ARXr_wvb X W mem md mat aAR aOWN) | exact aWLE | eapply same_io_trans; [exact aIO | apply same_io_with_vm_backing]
| exact aOWN | exact aFR | exact aPRS | exact aINI | exact aRAW | exact aEK | exact aMK | exact aSTP].
+ exact DQ.
+ exact BLt.
+ discriminate.
+ exact LEN.
+ unfold AFhd.common_regs. rewrite <- C3, <- C4, <- C26, <- C27. splits; apply CS; cbn; tauto.
+ unfold AFhd.loop_regs. rewrite R2, <- Q8, <- Q9, <- Q18, <- Q19, <- Q21. splits; [exact Q2 | apply CS; cbn; tauto ..].
+ exact R10.
+ exact FRc.
+ exact TM.
+ exact CE.
Qed.
End e.
End c.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 534 of its 587 lines of code are new or changed and 416 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the piece "the refusal
   fold" of the walk of LLVMFuzzerTestOneInput, lib/A/HPgSegM.v hq_piece_M3b_refuse_stmt, from both its entries.
   Proves no function (kind: segment lemma).

   THE CODE (fuzz_headamp.c:144-147, `if (x->refusal == REFUSE_NONE) x->refusal = r;`)
     RFA 0x83454  ld t2,0xe0(s1)        t2 := n_ent (R+0xe0, stored by the key piece at 0x83188)
         0x83458  ld t6,0xd8(s1)        t6 := &ent[0] (R+0xd8, stored at 0x8318c)
         0x8345c  addi t3,zero,5        t3 := OUT_OF_RANGE
     RF  0x83460  ld a0,0x108(s1)       a0 := x (R+0x108)
         0x83464  lw a0,0x84(a0)        a0 := x->refusal
         0x83468  bnez a0,0x83474       a refusal is already kept: to LATCH
         0x8346c  ld a0,0x108(s1)       a0 := x
         0x83470  sw t3,0x84(a0)        x->refusal := t3
     and falls through to LATCH 0x83474. The two x accesses carry no instrumented check (x is a frame object at a
   fixed offset of the frame for locals). No call: the piece changes no float register; it writes the four bytes
   x->refusal at F + 0x224, inside M03's write set (HPgImgA's third range list, (XF 0, 0x180, 0xa8)).

   HOW. Three block lemmas over the kit's engine (lib/Reusable: YCbn.v / YCbq.v), each for any float state:
   hr0_blk (RFA 0x83454 -> RF 0x83460, the two reloads and t3 := 5), hr1_blk (RF 0x83460 -> LATCH 0x83474 when
   x->refusal <> 0, else -> 0x8346c; x->refusal as a read-only region over an extra atom) and hr2_blk (0x8346c ->
   LATCH 0x83474: the store, through a writable region at x + 0x84 that the journal allows because x lies in the
   frame for locals the harness owns, YCbq.v awr_byte's in_frames case). hr2_blk's post says every byte outside
   [x + 0x84, x + 0x88) is as before and the four bytes hold t3. hb_rf_A reads the RF cut, runs hr1_blk and, on
   the store arm, hr2_blk, and rebuilds the LATCH cut at m + 2: x holds the fold's refusal (the first one,
   HPgM3bBase.hb_fold_refuse), every other fact of the cut is kept because its bytes lie outside x->refusal (the
   real-frame cells lie above the frame for locals, the pp / pod / out blocks are apart from it, its shadow row is
   in the shadow map, the read-only image is not a frame). hb_rfa_A runs hr0_blk and hands the RF cut over with
   the code OUT_OF_RANGE. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps HPgMem HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* the store's pc *)
Definition HR_ST : Z := 0x8346c.

(* ================================ the code tables and the entry states ================================ *)
Definition hr0_tbl : ctable := build_table rsegs HQ_RFA 3 TEmpty.
Lemma hr0_tbl_ok : table_ok rsegs hr0_tbl.
Proof. apply build_table_ok0. unfold HQ_RFA. lia. Qed.
Definition hr1_tbl : ctable := build_table rsegs HQ_RF 3 TEmpty.
Lemma hr1_tbl_ok : table_ok rsegs hr1_tbl.
Proof. apply build_table_ok0. unfold HQ_RF. lia. Qed.
Definition hr2_tbl : ctable := build_table rsegs HR_ST 2 TEmpty.
Lemma hr2_tbl_ok : table_ok rsegs hr2_tbl.
Proof. apply build_table_ok0. unfold HR_ST. lia. Qed.

(* the registers RFA does not write (all but t2, t3, t6), and the ones RF does not write (all but a0) *)
Definition hr0_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30].
Definition hr_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

(* RFA: the real-frame cells R+0xd8 and R+0xe0 over the atoms 33 and 34 *)
Definition hr0_R : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0xe8 0 0
  [YP09.mkChunk 0xd8 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 34 0))].
Definition hr0_ss0 : sstate := mkSS HQ_RFA sr_atoms [hr0_R] None (mkFacts [] [] []).
Definition hr0_extra (v6 v2 : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 v6; Z_to_bv 64 v2].
Definition hr0_RR (v6 v2 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 31) = w64 v6 /\ getr regs2 (Z_to_bv 5 7) = w64 v2 /\ getr regs2 (Z_to_bv 5 28) = w64 5.

(* RF: the cell R+0x108 = x (atom 33), and x->refusal (atom 34) as a read-only region based on x *)
Definition hr1_RA : YP09.region := YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [YP09.mkChunk 0x108 (CVal 8 (SOff 33 0))].
Definition hr1_RB : YP09.region := YP09.mkRegion (Some 33%nat) 0x84 0x88 0 0 [YP09.mkChunk 0x84 (CVal 4 (SOff 34 0))].
Definition hr1_ss0 : sstate := mkSS HQ_RF sr_atoms [hr1_RA; hr1_RB] None (mkFacts [(34%nat, mkAF 0 5 0)] [] []).
Definition hr1_extra (X rf : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 X; Z_to_bv 64 rf].

(* the store: the same cell, and x->refusal as a writable region based on x *)
Definition hr2_RB : YP09.region := YP09.mkRegion (Some 33%nat) 0x84 0x88 0x84 0x88 [].
Definition hr2_ss0 : sstate := mkSS HR_ST sr_atoms [hr1_RA; hr2_RB] None (mkFacts [] [] []).
Definition hr2_extra (X : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 X].

Ltac hr_atom :=
hb_sv; rewrite hb_denot0;
lazymatch goal with |- ew _ ?n = _ => lazymatch goal with En : ew _ n = Z_to_bv 64 _ |- _ => rewrite En; reflexivity end end.
Ltac hr_lit := hb_sv; cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity.

(* the `lw` of a small non-negative word *)
Lemma hr_sext_small : forall E (n : nat) t, ew E n = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = t.
Proof.
intros E n t H Ht. rewrite U_SExt, (U_atom E n t H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small t) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
unfold zcanon, M64. rewrite (Z.mod_small (t + 2 ^ 31)) by lia. replace (t + 2 ^ 31 - 2 ^ 31) with t by lia.
apply Z.mod_small. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* ================================ RFA 0x83454 -> RF 0x83460 ================================ *)
Lemma hr0_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R v6 v2 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0xe8 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 (v6 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (v2 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HQ_RFA regs memc mdc)
(hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_RF hr0_kept (hr0_RR v6 v2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R v6 v2 HJ H9 HR0 HR1 Vd8 Ve0.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hr0_extra v6 v2) as ex eqn:Hex.
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 v6) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 v2) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hr0_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQ_RFA) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hr0_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + exact (hb_slot_chunk _ _ _ R 0xd8 v6 33 E33 Vd8).
    + exact (hb_slot_chunk _ _ _ R 0xe0 v2 34 E34 Ve0).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 HQ_RFA) with (Z_to_bv 64 HQ_RFA).
aj_run_to_tok hr0_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQ_RF; [awr_ok_tac | ]. hb_mem.
apply SRr_ret. hb_post_intro B hr0_kept.
unfold hr0_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split; [hr_atom|]. split; [hr_atom|]. hr_lit.
Qed.

(* ================================ RF 0x83460: x->refusal's test ================================ *)
Lemma hr1_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R X rf : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0x110 <= 2 ^ 64 -> 0 <= X -> X + 0x88 <= R -> 0 <= rf <= 5 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (X mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (X + 0x84) 4 rf ->
SRr rsegs W (cfg_at rsegs HQ_RF regs memc mdc)
(fun W2 c2 =>
 (rf <> 0 /\ hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_LATCH hr_kept (fun _ => True) W2 c2) \/
 (rf = 0 /\ hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HR_ST hr_kept (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R X rf HJ H9 HR0 HR1 HX0 HXR Hrf V108 V84.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hr1_extra X rf) as ex eqn:Hex.
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 X) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 rf) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hr1_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQ_RF) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hr1_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. exact (hb_slot_chunk _ _ _ R 0x108 X 33 E33 V108).
    + apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 33 X); [rewrite E33; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ X 0x84 4 (SOff 34 0) rf); [rewrite hb_denot0; exact E34 | cbn; lia | cbn; lia | exact V84].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, hr1_RA, hr1_RB. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E33, !unsigned_lit_small by lia. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E34, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 HQ_RF) with (Z_to_bv 64 HQ_RF).
(* 0x83460 .. 0x83464, stop at the `bnez` *)
aj_run_tok hr1_tbl_ok HS HJ SHOK HPgSteps.RTBspan; [awr_ok_tac | ]. hb_mem.
srr_branch_tok hr1_tbl_ok HS SHOK HPgSteps.RTBspan;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
rewrite branch_ne_U in Hc;
rewrite ?(hr_sext_small E 34 rf E34), ?(U_atom E 34 rf E34), ?(U_lit E 0) in Hc by lia.
- (* taken: a refusal is kept already, to LATCH *)
  aj_run_to_tok hr1_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQ_LATCH; [awr_ok_tac | ]. hb_mem.
  apply SRr_ret; left. split; [apply negb_true_iff, Z.eqb_neq in Hc; exact Hc|].
  hb_post_intro B hr_kept. exact I.
- (* not taken: to the store *)
  aj_run_to_tok hr1_tbl_ok HS HJ SHOK HPgSteps.RTBspan HR_ST; [awr_ok_tac | ]. hb_mem.
  apply SRr_ret; right. split; [apply negb_false_iff, Z.eqb_eq in Hc; exact Hc|].
  hb_post_intro B hr_kept. exact I.
Qed.

(* ================================ 0x8346c: the store ================================ *)
(* the state at LATCH after the store: the journal, every byte outside x->refusal as before, x->refusal = t3 *)
Definition hr_post2 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (X bad : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HQ_LATCH) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r hr_kept -> getr regs2 r = getr regs r) /\
(forall a, ~ (X + 0x84 <= a mod 2 ^ 64 < X + 0x88) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
val_mem rsegs (mrestrict (w_H W) mem2) (X + 0x84) 4 bad.

Lemma hr2_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R X bad pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 28) = w64 bad ->
0 <= R -> R + 0x110 <= 2 ^ 64 -> 0 <= X -> X + 0x88 <= R -> 0 <= bad < 2 ^ 32 ->
In (4, pos) own -> X = frame_addr lyc 4 pos + 0x1a0 ->
(forall o, 0x84 <= o < 0x88 -> apresent (w_H W) memc (X + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (X mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HR_ST regs memc mdc)
(hr_post2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs X bad).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R X bad pos HJ H9 H28 HR0 HR1 HX0 HXR Hbad
  Hown HX Hpres V108.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity.
remember (hr2_extra X) as ex eqn:Hex.
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E28 : ew (Ereg regs ex) 28 = Z_to_bv 64 bad) by (rewrite (ew_Ereg_nat regs _ 28 (Z_to_bv 5 28) eq_refl); exact H28).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 X) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hr2_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HR_ST) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hr2_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. exact (hb_slot_chunk _ _ _ R 0x108 X 33 E33 V108).
    + apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 33 X); [rewrite E33; apply unsigned_lit_small; lia | lia | lia | | constructor].
      exact Hpres.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, hr1_RA, hr2_RB. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E33, !unsigned_lit_small by lia. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 HR_ST) with (Z_to_bv 64 HR_ST).
aj_run_to hr2_tbl_ok HS HJ HQ_LATCH;
[ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat X);
  [ reflexivity | rewrite E33; apply unsigned_lit_small; lia | | apply awr_ok_nil ];
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  right; right; right; exists 4, pos; split; [exact Hown|]; left; unfold in_zr; cbn [fst snd]; rewrite Hfb; lia
| ].
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [hb_io|].
split; [hb_kept hr_kept|].
split.
- intros a Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[<-|[]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi hr1_RA hr2_RB base_val] in Hr; [lia|].
  rewrite E33, (unsigned_lit_small X) in Hr by lia. rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap in Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact (Hn Hr).
- pose proof (HPgSteps.st_ok_region_at _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E33, unsigned_lit_small in Hch by lia.
  apply Forall_inv in Hch.
  apply (val_of_chunk_ok rsegs _ _ X 0x84 4 _ bad Hch); [rewrite hb_denot0; exact E28 | cbn; lia | cbn; lia].
Qed.
End d.
End b.

(* ================================ x's bytes ================================ *)
(* while the pair loop runs, x->refusal is x's last word (HPgSegM.hq_x_open; Spec/HeadBytes.v ha_res_bytes) *)
Definition hr_xP (cs : list cell) (keys : Z) : list byte :=
  repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs ++ repeat (Z_to_bv 8 0) (12 * (X_CELLS - length cs)) ++
  Mem.le4 (Z_to_bv 64 (Z.of_nat (length cs))) ++ Mem.le4 (Z_to_bv 64 keys).
Lemma hr_xP_len : forall cs keys, (length cs <= X_CELLS)%nat -> length (hr_xP cs keys) = 132%nat.
Proof.
intros cs keys H. unfold hr_xP, X_CELLS in *.
rewrite !length_app, !repeat_length, length_x_cells_bytes, !Mem.length_le4. lia.
Qed.
Lemma hr_x_split : forall cs keys rf, 0 <= rf < 2 ^ 64 ->
hq_x_open cs keys rf = hr_xP cs keys ++ Z_to_le_bytes 4 rf.
Proof.
intros cs keys rf Hrf. unfold hq_x_open, hr_xP, ha_res_bytes. rewrite <- !app_assoc.
replace (Mem.le4 (Z_to_bv 64 rf)) with (Z_to_le_bytes 4 rf)
  by (unfold Mem.le4; rewrite unsigned_lit_small by lia; reflexivity).
reflexivity.
Qed.
Lemma hr_slice_rf : forall cs keys v, (length cs <= X_CELLS)%nat ->
HPgMem.hm_slice (hr_xP cs keys ++ Z_to_le_bytes 4 v) 132 4 = Z_to_le_bytes 4 v.
Proof.
intros cs keys v H. unfold HPgMem.hm_slice.
rewrite skipn_app, (hr_xP_len cs keys H), Nat.sub_diag, skipn_O.
rewrite skipn_all2 by (rewrite (hr_xP_len cs keys H); lia). cbn [app].
apply firstn_all2. rewrite length_Z_to_le_bytes. lia.
Qed.
Lemma hr_overwrite_rf : forall cs keys v v', (length cs <= X_CELLS)%nat ->
overwrite (hr_xP cs keys ++ Z_to_le_bytes 4 v) 132 (Z_to_le_bytes 4 v') = hr_xP cs keys ++ Z_to_le_bytes 4 v'.
Proof.
intros cs keys v v' H. unfold overwrite.
rewrite firstn_app, (hr_xP_len cs keys H), Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all2 by (rewrite (hr_xP_len cs keys H); lia).
rewrite skipn_all2 by (rewrite length_app, (hr_xP_len cs keys H), !length_Z_to_le_bytes; lia).
rewrite app_nil_r. reflexivity.
Qed.

(* ================================ memory reading ================================ *)
(* the reader sees only the 64-bit address *)
Lemma hr_aview_mod : forall {fx : YK11.FPState} H mem a, aview rsegs H mem a = aview rsegs H mem (a mod 2 ^ 64).
Proof. intros fx H mem a. unfold aview, mbyte. rewrite (HPgSteps.Z_to_bv_mod64 a). reflexivity. Qed.
(* four readable bytes make a readable word *)
Lemma hr_rd32_some : forall (rd : reader) a,
(forall k, (k < 4)%nat -> exists b : byte, rd (a + Z.of_nat k) = Some (bv_unsigned b)) ->
exists v, rd32 rd a v.
Proof.
intros rd a H.
destruct (H 0%nat ltac:(lia)) as (b0 & H0). destruct (H 1%nat ltac:(lia)) as (b1 & H1).
destruct (H 2%nat ltac:(lia)) as (b2 & H2). destruct (H 3%nat ltac:(lia)) as (b3 & H3).
exists (bytes_le_to_Z [b0; b1; b2; b3]). intros k Hk.
change 4%nat with (length [b0; b1; b2; b3]).
rewrite (HPgMem.hm_lez_le_byte [b0; b1; b2; b3] k) by (cbn [length]; lia).
destruct k as [|[|[|[|k]]]]; [exact H0 | exact H1 | exact H2 | exact H3 | cbn [length] in Hk; lia].
Qed.
(* the cells of M03's lists all lie in the real frame [R, R + 0x120) *)
Definition hr_cellb (f : hd_loc * Z) : bool :=
match fst f with LReg _ => true | LCell XR o => (0 <=? o) && (o <=? 0x118) | LCell _ _ => false end.
Lemma hr_at_store : forall {fx : YK11.FPState} H mem mem' regs e L, hs_at rsegs H mem regs e L ->
forallb hr_cellb L = true ->
(forall i, e_R e <= i < e_R e + 0x120 -> aview rsegs H mem' i = aview rsegs H mem i) ->
hs_at rsegs H mem' regs e L.
Proof.
intros fx H mem mem' regs e L HL Hb K. unfold hs_at in *. rewrite Forall_forall in *.
intros [[r|b o] v] Hx. { exact (HL _ Hx). }
pose proof (HL _ Hx) as Hv. pose proof (proj1 (forallb_forall _ _) Hb _ Hx) as Hc. unfold hr_cellb in Hc.
cbn [fst] in Hc. destruct b; try discriminate Hc.
apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2.
cbn [hd_at fst snd hd_xv] in Hv |- *.
eapply HPgSiteA.hd_val_mem_kept; [|exact Hv]. intros i Hi. apply K. lia.
Qed.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the frame for locals at the segment's start: owned by the harness, in application memory, below the
   allocation ceiling and so below the real frame *)
Lemma hr_start_F : forall (cx : hs_scx rsegs) r ev, @hq_start_M03 fx rc SK rsegs B cx r ev ->
In (4, x_pos cx) (x_own cx) /\ e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx) /\
4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ in_app (e_F (x_e cx)) 1024 /\
alloc_ceiling + T_SEG_STK <= e_R (x_e cx).
Proof.
intros cx r ev HS. pose proof (hb_start_pre B cx r ev HS) as Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & HeS & _ & _ & HstkR & Hown & HF & _).
pose proof hq_pcs_himg as (_ & _ & _ & _ & _ & Hcid & _). rewrite Hcid in Hown, HF. unfold HQ_CID in Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK & Hc1 & Hc2 & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok rsegs B) _ _ _ _ _ 4 (x_pos cx) HAR Hfin) as (_ & Happ & _).
destruct (al_sep _ _ (AR_laws_ok rsegs B) _ _ _ _ _ HAR) as (_ & Hf).
pose proof (proj1 (Forall_forall _ _) Hf (4, x_pos cx) Hfin) as (Hf1 & Hf2). cbn [fst snd] in Hf1, Hf2.
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity. rewrite Hfb in Happ, Hf2.
rewrite <- HF in Happ, Hf1, Hf2.
split; [exact Hown|]. split; [exact HF|]. split; [lia|]. split; [lia|]. split; [exact Happ|].
unfold T_SEG_STK, ASTACK in *. lia.
Qed.

Lemma hr_w3 : hi_w3 headamp_himg_A = [(XF 0, 0x180, 0xa8); (XShF, 48, 21); (XR, 0, 0x120)].
Proof. reflexivity. Qed.

(* RF 0x83460 -> LATCH 0x83474 at m + 2 *)
Lemma hb_rf_A : forall (cx : hs_scx rsegs) POST r ev at0 m,
@hq_start_M03 fx rc SK rsegs B cx r ev -> hq_from_LATCH rsegs B MT cx r POST (S (S m)) ->
hq_from_RF rsegs B MT cx r POST at0 m.
Proof.
intros cx POST r ev at0 m HS HL.
unfold hq_from_RF. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v bad cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hlive & Ham & Hexp & Hbad & Hpinv & Hx).
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof Hx as (Hxg & Hcl & Hcc & Hck & Hkr & Hrf).
pose proof Hpinv as (_ & _ & Hsm & _).
pose proof (hb_start_wf B cx r ev HS) as Hwf.
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
pose proof (hb_start_R B cx r ev HS) as (HR0 & HR1 & _).
pose proof (hr_start_F cx r ev HS) as (Hown & HFe & HF4k & HFc & HFapp & HFR).
pose proof (@alloc_ceiling_val rc) as [[Hc0 Hc1] _].
unfold T_SEG_STK, ASTACK in HFR.
unfold hs_at_cx in Hat.
pose proof (hb_at_get _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hb_in)) as R9.
pose proof (hb_at_get _ _ _ _ _ 28 bad Hat ltac:(hb_in)) as R28.
pose proof (hb_at_get _ _ _ _ _ 21 (Z.of_nat m + 2) Hat ltac:(hb_in)) as R21.
pose proof (hb_at_get _ _ _ _ _ 31 (e_pp (x_e cx) + HQ_ENT0) Hat ltac:(hb_in)) as R31.
pose proof (hb_at_get _ _ _ _ _ 7 (hq_nent r) Hat ltac:(hb_in)) as R7.
pose proof (hb_at_cell _ _ _ _ _ XR 0x108 (e_F (x_e cx) + HQ_XO) Hat ltac:(hb_in)) as C108.
cbn [hd_xv] in C108.
assert (Hs' : hs_at rsegs (w_H W2) mem2 regs2 (x_e cx)
  (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r ++
   [(LReg 31, e_pp (x_e cx) + HQ_ENT0); (LReg 7, hq_nent r)])) by hb_sub Hat.
assert (Hbad' : bad = 4 \/ bad = 5) by (unfold REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE in Hbad; lia).
assert (Hrf' : rf = 0 \/ rf = 4 \/ rf = 5) by (unfold REFUSE_NONE, REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE in Hrf; lia).
(* x->refusal *)
assert (Vrf : val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + HQ_XO + 0x84) 4 rf).
{ pose proof Hxg as Hb. rewrite (hr_x_split cs (keys + 1) rf ltac:(lia)) in Hb.
  pose proof (HPgMem.hm_bytes_field rsegs _ _ _ _ 132 4 rf Hb (hr_slice_rf cs (keys + 1) rf Hcl)
    ltac:(rewrite length_app, (hr_xP_len cs (keys + 1) Hcl), length_Z_to_le_bytes; lia)) as V.
  exact V. }
eapply SRr_bind.
{ apply (hr1_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_F (x_e cx) + HQ_XO) rf HJ R9);
  unfold HQ_XO in *; try lia; [exact C108 | exact Vrf]. }
intros W3 c3 _ [(Hrf0 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _) | (Hrf0 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)].
- (* a refusal is kept already: LATCH with x as it is *)
  pose proof (hb_fold_refuse cx r m k v bad cs keys rf Hpinv Hexp) as Hfold'.
  replace (if rf =? REFUSE_NONE then bad else rf) with rf in Hfold'
    by (unfold REFUSE_NONE; destruct (Z.eqb_spec rf 0); [lia | reflexivity]).
  pose proof (hb_at_keep _ _ _ _ _ Hs' regs3 hr_kept Hk3 ltac:(vm_compute; reflexivity)) as Hs3.
  apply (HL fx2 ly2 S2 W2 regs3 mem2 md3 cs (keys + 1) rf).
  split.
  { apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hr_kept; hb_kin. }
  split.
  { unfold hs_at_cx. apply hb_at_app; split; [hb_sub Hs3|].
    apply hb_at_app; split; [hb_sub Hs3|].
    apply hb_at_app; split; [hb_sub Hs3|].
    unfold hs_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - rewrite Hk3 by (unfold hr_kept; hb_kin). exact R31.
    - rewrite Hk3 by (unfold hr_kept; hb_kin). exact R7.
    - rewrite Hk3 by (unfold hr_kept; hb_kin). rewrite R21. unfold w64. f_equal. lia. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|].
  split; [unfold hq_nent; lia|]. split; [lia|]. split; [exact Hx | exact Hfold'].
- (* the store *)
  subst rf.
  pose proof (hb_fold_refuse cx r m k v bad cs keys 0 Hpinv Hexp) as Hfold'.
  replace (if 0 =? REFUSE_NONE then bad else 0) with bad in Hfold' by reflexivity.
  pose proof (hb_at_keep _ _ _ _ _ Hs' regs3 hr_kept Hk3 ltac:(vm_compute; reflexivity)) as Hs3.
  set (F := e_F (x_e cx)) in *.
  (* the frame at the cut *)
  assert (HFly : frame_addr ly2 4 (x_pos cx) = F).
  { pose proof (hb_start_pre B cx r ev HS) as (HJ0 & _).
    rewrite HFe. eapply HPgSiteA.headamp_A_site_frame_at; [exact HJ0 | exact HJ]. }
  pose proof HJ as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
  assert (Hfin2 : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs2; apply in_or_app; left; exact Hown).
  destruct (al_frames _ _ (AR_laws_ok rsegs B) _ _ _ _ _ 4 (x_pos cx) HAR2 Hfin2) as (_ & _ & HFpres & _).
  assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity. rewrite Hfb, HFly in HFpres.
  eapply SRr_bind.
  { apply (hr2_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e cx)) (F + HQ_XO) bad (x_pos cx) HJ3);
    unfold HQ_XO in *.
    - rewrite Hk3 by (unfold hr_kept; hb_kin). exact R9.
    - rewrite Hk3 by (unfold hr_kept; hb_kin). exact R28.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hown.
    - rewrite HFly. reflexivity.
    - intros o Ho. apply (HFpres (F + 416 + o) ltac:(lia)).
    - exact C108. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Kmem & Vbad).
  unfold HQ_XO in Kmem, Vbad.
  (* the bytes the store left alone *)
  assert (K' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x224 <= a < F + 0x228) ->
    aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. apply Kmem. rewrite Z.mod_small by lia. lia. }
  assert (Hk42 : forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs4 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)).
  { intros q Hq. rewrite Hk4, Hk3; [reflexivity | |]; destruct Hq as [->|[->| ->]]; unfold hr_kept; hb_kin. }
  (* where the other objects lie *)
  pose proof HS as (_ & _ & _ & Hlen & _ & _ & Hfpod & _ & _ & _ & _ & Hfout & _).
  pose proof (hb_start_pre B cx r ev HS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
  pose proof (hb_start_pp B cx r ev HS) as (Hppin & _ & Hp4k & Hpc & Hceil).
  destruct Hfpod as (_ & Hpodin & _). destruct Hfout as (_ & Houtin & _).
  pose proof (Permutation_in _ (Permutation_sym Hperm) Hppin) as Hpp2.
  pose proof (Permutation_in _ (Permutation_sym Hperm) Hpodin) as Hpod2.
  pose proof (Permutation_in _ (Permutation_sym Hperm) Houtin) as Hout2.
  pose proof (sep_block_frame rsegs B (AR_laws_ok rsegs B) _ _ _ _ _ _ _ _ _ HAR2 Hpp2 Hfin2) as Dpp.
  pose proof (sep_block_frame rsegs B (AR_laws_ok rsegs B) _ _ _ _ _ _ _ _ _ HAR2 Hpod2 Hfin2) as Dpod.
  pose proof (sep_block_frame rsegs B (AR_laws_ok rsegs B) _ _ _ _ _ _ _ _ _ HAR2 Hout2 Hfin2) as Dout.
  unfold zdisjoint in Dpp, Dpod, Dout. cbn [fst snd] in Dpp, Dpod, Dout. rewrite Hfb, HFly in Dpp, Dpod, Dout.
  destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR2 Hpod2) as (_ & Hpod4k & Hpodc & _).
  destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR2 Hout2) as (_ & Hout4k & Houtc & _).
  assert (Hlen8 : 8 <= e_len (x_e cx)) by (pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & HL0); lia).
  assert (Hrq1 : req_size PP_SIZE = PP_SIZE) by reflexivity.
  assert (Hrq2 : req_size (e_len (x_e cx)) = e_len (x_e cx))
    by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e cx)) 0); lia).
  assert (Hrq3 : req_size (3 * (e_cap (x_e cx) + 1)) = 3 * (e_cap (x_e cx) + 1))
    by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap (x_e cx) + 1)) 0); lia).
  rewrite Hrq1 in Dpp. rewrite Hrq2 in Dpod, Hpodc. rewrite Hrq3 in Dout, Houtc.
  unfold PP_SIZE in *.
  pose proof (Headamp.parse_props_total (hd_props (e_null (x_e cx)) (buf r)) (e_cap (x_e cx)) ltac:(lia)) as Hok.
  apply answer_ok_parts in Hok as (Hcase & _).
  assert (Hlc : Z.of_nat (length (ans_cells (hq_ans rsegs cx r))) <= e_cap (x_e cx)).
  { unfold hq_ans. destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]. }
  assert (Hb : Z.of_nat (length (buf r)) <= POD_BUF_MAX)
    by (pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & HL0); unfold POD_BUF_MAX; lia).
  assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents r)).
  { eapply Forall_impl; [|exact (proj2 (ents_wf r Hwf))]. intros e (_ & He & Hz). lia. }
  pose proof (HPgMem.hm_pp_len_img (buf r) (is_props r) (has_params r) (params_struct r) (ents r) (corrupt r)
    Hb Hn32 Hs) as Lpp.
  set (Wr := fun a : Z => (a < 0 \/ 2 ^ 64 <= a) \/ (F + 0x224 <= a < F + 0x228)).
  assert (KW : forall a, ~ Wr a -> aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. unfold Wr in Ha. apply K'; lia. }
  apply (HL fx2 ly2 S2 W2 regs4 mem4 md4 cs (keys + 1) bad).
  split.
  { (* the cut base after the store *)
    destruct Hb3 as (Hcore' & Hfxk & Hfsh & Hrom & Hpp & Hpod & Hout & Hres & Herr).
    split.
    { unfold hs_core, hs_mid in Hcore' |- *. destruct Hcore' as (_ & H234 & Hfr & Hperm' & Hio & Hmo & Hmem).
      split; [exact HJ4|]. split; [intros q Hq; rewrite (Hk42 q Hq); exact (H234 q Hq)|].
      split; [exact Hfr|]. split; [exact Hperm'|].
      split; [exact (same_io_trans _ _ _ Hio (same_io_trans _ _ _ Hio3 Hio4))|]. split; [exact Hmo|].
      intros a Ha Hns HE. rewrite <- (Hmem a Ha Hns HE). apply K'; [exact Ha|]. intros Hin. apply HE.
      left. unfold hd_inw. rewrite hr_w3. apply Exists_cons_hd. cbn [hd_xv fst snd]. fold F. lia. }
    split; [exact Hfxk|].
    split.
    { unfold hs_fsh_at in Hfsh |- *. apply (HPgMem.hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem4 _ hq_shX Hfsh).
      intros i Hi. rewrite hq_shX_len in Hi.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold shadow_addr, SHADOW_OFF.
      change (e_F (x_e cx)) with F.
      assert (Hdv : 8 * (F / 8) <= F < 8 * (F / 8) + 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
      apply K'; [split | intros Hin]; lia. }
    split.
    { apply (HPgMem.hm_rom_kept_wr rsegs Wr W2 W2 mem2 mem4 Hrom KW).
      intros a Ha Hw. pose proof Ha as (sg & Hsg & _ & Hr).
      assert (Hi : in_img rsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
      pose proof (HPgSteps.img_segs_low a Hi) as Hlow. unfold Wr in Hw. unfold kLowMemEnd in Hlow.
      destruct Hw as [Hw|Hw]; [lia|].
      assert (Hfr' : exists cid pos, In (cid, pos) (frames S2) /\
        frame_addr ly2 cid pos <= a < frame_addr ly2 cid pos + fs_frame_bytes cid).
      { exists 4, (x_pos cx). split; [exact Hfin2|]. rewrite Hfb, HFly. lia. }
      destruct (al_client_img _ _ (AR_laws_ok rsegs B) _ _ _ _ _ a HAR2 (or_intror (or_introl Hfr'))) as (_ & Hni).
      exact (Hni Hi). }
    split.
    { unfold hs_pp_at in Hpp |- *.
      apply (HPgMem.hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hpp KW).
      intros a Ha. unfold pp_bytes in Ha. rewrite Lpp in Ha. unfold Wr, PP_SIZE in *. lia. }
    split.
    { apply (HPgMem.hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hpod KW).
      intros a Ha. unfold Wr. lia. }
    split.
    { apply (HPgMem.hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hout KW).
      intros a Ha. try unfold hd_zbytes in Ha. rewrite ?length_map, ?length_ha_cells_bytes in Ha. unfold Wr. lia. }
    split.
    { apply (HPgMem.hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hres KW).
      intros a Ha. unfold ans_res_bytes in Ha. rewrite length_ha_res_bytes in Ha.
      change (e_F (x_e cx)) with F in Ha. unfold Wr, HQ_RES in *. lia. }
    destruct Herr as (ev0 & Hev0).
    apply hr_rd32_some. intros kk Hkk.
    destruct (Z_lt_dec ((as_errno B + Z.of_nat kk) mod 2 ^ 64) (F + 0x224)) as [Hlo|Hlo];
    [|destruct (Z_lt_dec ((as_errno B + Z.of_nat kk) mod 2 ^ 64) (F + 0x228)) as [Hhi|Hhi]].
    - exists (Z_to_bv 8 (le_byte ev0 4 kk)). rewrite Kmem by lia. rewrite (Hev0 kk Hkk).
      f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      unfold le_byte. rewrite Z.mod_mod by lia. reflexivity.
    - set (j := Z.to_nat ((as_errno B + Z.of_nat kk) mod 2 ^ 64 - (F + 0x224))).
      assert (Hj : (j < 4)%nat) by (unfold j; lia).
      pose proof (Vbad j Hj) as Vj.
      exists (Z_to_bv 8 (le_byte bad 4 j)). rewrite hr_aview_mod. unfold aview.
      replace ((as_errno B + Z.of_nat kk) mod 2 ^ 64) with (F + 416 + 132 + Z.of_nat j) by (unfold j; lia).
      rewrite Vj. reflexivity.
    - exists (Z_to_bv 8 (le_byte ev0 4 kk)). rewrite Kmem by lia. rewrite (Hev0 kk Hkk).
      f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      unfold le_byte. rewrite Z.mod_mod by lia. reflexivity. }
  split.
  { unfold hs_at_cx.
    assert (Hs4 : hs_at rsegs (w_H W2) mem4 regs4 (x_e cx)
      (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r ++
       [(LReg 31, e_pp (x_e cx) + HQ_ENT0); (LReg 7, hq_nent r)])).
    { apply (hr_at_store _ mem2); [|vm_compute; reflexivity|].
      - exact (hb_at_keep _ _ _ _ _ Hs3 regs4 hr_kept Hk4 ltac:(vm_compute; reflexivity)).
      - intros i Hi. apply K'; lia. }
    apply hb_at_app; split; [hb_sub Hs4|].
    apply hb_at_app; split; [hb_sub Hs4|].
    apply hb_at_app; split; [hb_sub Hs4|].
    unfold hs_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - rewrite Hk4, Hk3 by (unfold hr_kept; hb_kin). exact R31.
    - rewrite Hk4, Hk3 by (unfold hr_kept; hb_kin). exact R7.
    - rewrite Hk4, Hk3 by (unfold hr_kept; hb_kin). rewrite R21. unfold w64. f_equal. lia. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|].
  split; [unfold hq_nent; lia|]. split; [lia|].
  split; [|exact Hfold'].
  (* x after the store *)
  split.
  { assert (Hxb : HPgMem.hm_bytes rsegs (w_H W2) mem2 (F + 416) (hr_xP cs (keys + 1) ++ Z_to_le_bytes 4 0)).
    { pose proof Hxg as Hb0. rewrite (hr_x_split cs (keys + 1) 0 ltac:(lia)) in Hb0. exact Hb0. }
    pose proof (HPgMem.hm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem4 (F + 416) _ 132 4 bad Hxb
      ltac:(replace (F + 416 + Z.of_nat 132) with (F + 416 + 132) by lia; exact Vbad)
      ltac:(rewrite length_app, (hr_xP_len cs (keys + 1) Hcl), length_Z_to_le_bytes; lia)) as Hxn.
    rewrite hr_overwrite_rf in Hxn by exact Hcl.
    rewrite (hr_x_split cs (keys + 1) bad ltac:(lia)).
    apply Hxn. intros y Hy Hn.
    rewrite length_app, (hr_xP_len cs (keys + 1) Hcl), length_Z_to_le_bytes in Hy.
    apply K'; lia. }
  split; [exact Hcl|]. split; [exact Hcc|]. split; [exact Hck|]. split; [exact Hkr|].
  unfold REFUSE_NONE, REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE. lia.
Qed.

(* RFA 0x83454 -> RF 0x83460 with the code OUT_OF_RANGE *)
Lemma hb_rfa_A : forall (cx : hs_scx rsegs) POST r ev at0 m,
@hq_start_M03 fx rc SK rsegs B cx r ev -> hq_from_RF rsegs B MT cx r POST at0 m ->
hq_from_RFA rsegs B MT cx r POST at0 m.
Proof.
intros cx POST r ev at0 m HS HRF.
unfold hq_from_RFA. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hlive & Ham & Hexp & Hpinv & Hx).
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _).
pose proof (hb_start_R B cx r ev HS) as (HR0 & HR1 & _).
unfold hs_at_cx in Hat.
pose proof (hb_at_get _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hb_in)) as R9.
pose proof (hb_at_cell _ _ _ _ _ XR 0xd8 (e_pp (x_e cx) + HQ_ENT0) Hat ltac:(hb_in)) as Cd8.
pose proof (hb_at_cell _ _ _ _ _ XR 0xe0 (hq_nent r) Hat ltac:(hb_in)) as Ce0.
cbn [hd_xv] in Cd8, Ce0.
eapply SRr_bind.
{ apply (hr0_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_pp (x_e cx) + HQ_ENT0)
    (hq_nent r) HJ R9); try lia; [exact Cd8 | exact Ce0]. }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & Q31 & Q7 & Q28).
pose proof (hb_at_keep _ _ _ _ _ Hat regs3 hr0_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
apply (HRF fx2 ly2 S2 W2 regs3 mem2 md3 k v REFUSE_OUT_OF_RANGE cs keys rf).
split.
{ apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
  intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hr0_kept; hb_kin. }
split.
{ unfold hs_at_cx. apply hb_at_app; split; [hb_sub Hat3|].
  apply hb_at_app; split; [hb_sub Hat3|].
  apply hb_at_app; split; [hb_sub Hat3|].
  unfold hs_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
  - exact Q31.
  - exact Q7.
  - pose proof (hb_at_get _ _ _ _ _ 21 (Z.of_nat m + 2) Hat3 ltac:(hb_in)) as R21. exact R21.
  - exact Q28. }
split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|]. split; [exact Ham|].
split; [exact Hexp|]. split; [right; reflexivity|]. split; [exact Hpinv | exact Hx].
Qed.

Theorem hb_refuse_A : hq_piece_M3b_refuse_stmt rsegs B MT.
Proof.
unfold hq_piece_M3b_refuse_stmt. intros cx POST r ev at0 m HS HL.
pose proof (hb_rf_A cx POST r ev at0 m HS HL) as HRF.
split; [exact HRF | exact (hb_rfa_A cx POST r ev at0 m HS HRF)].
Qed.
End c.

Print Assumptions hb_refuse_A.

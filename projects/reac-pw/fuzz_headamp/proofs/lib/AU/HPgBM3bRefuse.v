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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 482 of its 533 lines of code are new or changed and 418 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bRefuse.v at 5b91e0e59822 (image A's
   twin of this piece, same unit): the prefixes hr_ / hb_ -> hru_ / hbu_, image A's code 0x83454 .. 0x83470 replaced
   by image B's 0x836a0 .. 0x836b0 (one refusal entry: image A's RFA block hr0_blk and its cut lemma hb_rfa_A are
   dropped; x is read from R+0x138, not R+0x108; the code is in a5, not t3; x lies at F + 0x2c0, not F + 0x1a0),
   the cut rebuilt over lib/AU/HPgSegM.v's hqu_cut_RF / hqu_cut_LATCH and lib/AU/HPgBM3bBase.v, the cut base's
   rebuilding after the store factored into hru_base3_store, and the two generic facts image A took from
   lib/A/HPgSiteA.v (the frame's address along the journal, a value kept byte by byte) restated here. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the piece "the refusal
   fold" of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgSegM.v hqu_piece_M3b_refuse_stmt. Proves no function
   (kind: segment lemma).

   THE CODE (RF 0x836a0 .. 0x836b0, fuzz_headamp.c:144-147, `if (x->refusal == REFUSE_NONE) x->refusal = r;`)
     0x836a0  ld a0,0x138(s1)       a0 := x = F + 0x2c0 (the real-frame cell R+0x138, HPgSegM.hqu_L_loopc)
     0x836a4  lw a0,0x84(a0)        a0 := x->refusal
     0x836a8  bnez a0,0x836b4       a refusal is kept already: to LATCH
     0x836ac  ld a0,0x138(s1)       a0 := x
     0x836b0  sw a5,0x84(a0)        x->refusal := a5 (the code every refusing site sets before it jumps to RF)
   and falls through to LATCH 0x836b4. The two x accesses carry no instrumented check (x is a frame object at a
   fixed offset of the frame for locals). No call: the piece changes no float register; it writes the four bytes
   x->refusal at F + 0x344, inside M03's write set (HPgImgB's third range list, (XF 0, 0x2a0, 0xa8)).

   REGISTERS AND R-CELLS. It reads s1 = R, a5 = the code and the real-frame cell R+0x138; it writes a0 only.

   HOW. Two block lemmas over the kit's engine (lib/Reusable: YCbn.v / YCbq.v), each for any float state:
   hru1_blk (RF 0x836a0 -> LATCH 0x836b4 when x->refusal <> 0, else -> 0x836ac; x->refusal as a read-only region
   over an extra atom) and hru2_blk (0x836ac -> LATCH 0x836b4: the store, through a writable region at x + 0x84
   that the journal allows because x lies in the frame for locals the harness owns, YCbq.v awr_byte's in_frames
   case). hru2_blk's post says every byte outside [x + 0x84, x + 0x88) is as before and the four bytes hold a5.
   hbu_refuse_B reads the RF cut, runs hru1_blk and, on the store arm, hru2_blk, and rebuilds the LATCH cut at
   m + 2: x holds the fold's refusal (the first one, HPgBM3bBase.hbu_fold_refuse); the cut base is kept by
   hru_base3_store (any store whose bytes lie inside x: the real-frame cells lie above the frame for locals, the
   pp / pod / out blocks are apart from it, its shadow row is in the shadow map, the read-only image is not a
   frame, res lies below x, and the errno cell stays readable), the cut's list by hru_at_store (its cells all lie
   in [R, R + 0x160)). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgBM3bBase.
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
Definition HRU_ST : Z := 0x836ac.

(* ================================ the code tables and the entry states ================================ *)
Definition hru1_tbl : ctable := build_table rsegs HQU_RF 3 TEmpty.
Lemma hru1_tbl_ok : table_ok rsegs hru1_tbl.
Proof. apply build_table_ok0. unfold HQU_RF. lia. Qed.
Definition hru2_tbl : ctable := build_table rsegs HRU_ST 2 TEmpty.
Lemma hru2_tbl_ok : table_ok rsegs hru2_tbl.
Proof. apply build_table_ok0. unfold HRU_ST. lia. Qed.

(* the registers the piece does not write: all but a0 *)
Definition hru_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

(* RF: the cell R+0x138 = x (atom 33), and x->refusal (atom 34) as a read-only region based on x *)
Definition hru1_RA : YP09.region := YP09.mkRegion (Some 9%nat) 0x138 0x140 0 0 [YP09.mkChunk 0x138 (CVal 8 (SOff 33 0))].
Definition hru1_RB : YP09.region := YP09.mkRegion (Some 33%nat) 0x84 0x88 0 0 [YP09.mkChunk 0x84 (CVal 4 (SOff 34 0))].
Definition hru1_ss0 : sstate := mkSS HQU_RF sr_atoms [hru1_RA; hru1_RB] None (mkFacts [(34%nat, mkAF 0 5 0)] [] []).
Definition hru1_extra (X rf : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 X; Z_to_bv 64 rf].

(* the store: the same cell, and x->refusal as a writable region based on x *)
Definition hru2_RB : YP09.region := YP09.mkRegion (Some 33%nat) 0x84 0x88 0x84 0x88 [].
Definition hru2_ss0 : sstate := mkSS HRU_ST sr_atoms [hru1_RA; hru2_RB] None (mkFacts [] [] []).
Definition hru2_extra (X : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 X].

(* the `lw` of a small non-negative word *)
Lemma hru_sext_small : forall E (n : nat) t, ew E n = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 ->
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

(* ================================ RF 0x836a0: x->refusal's test ================================ *)
Lemma hru1_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R X rf : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0x140 <= 2 ^ 64 -> 0 <= X -> X + 0x88 <= R -> 0 <= rf <= 5 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (X mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (X + 0x84) 4 rf ->
SRr rsegs W (cfg_at rsegs HQU_RF regs memc mdc)
(fun W2 c2 =>
 (rf <> 0 /\ hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_LATCH hru_kept (fun _ => True) W2 c2) \/
 (rf = 0 /\ hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HRU_ST hru_kept (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R X rf HJ H9 HR0 HR1 HX0 HXR Hrf V138 V84.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hru1_extra X rf) as ex eqn:Hex.
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 X) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 rf) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hru1_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQU_RF) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hru1_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. exact (hbu_slot_chunk _ _ _ R 0x138 X 33 E33 V138).
    + apply (hm_ro_region rsegs _ (w_H W) memc 33 X); [rewrite E33; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ X 0x84 4 (SOff 34 0) rf); [rewrite hbu_denot0; exact E34 | cbn; lia | cbn; lia | exact V84].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, hru1_RA, hru1_RB. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E33, !unsigned_lit_small by lia. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E34, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 HQU_RF) with (Z_to_bv 64 HQU_RF).
(* 0x836a0 .. 0x836a4, stop at the `bnez` *)
aj_run_tok hru1_tbl_ok HS HJ SHOK HPgSteps.RTBspan; [awr_ok_tac | ]. hbu_mem.
srr_branch_tok hru1_tbl_ok HS SHOK HPgSteps.RTBspan;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
rewrite branch_ne_U in Hc;
rewrite ?(hru_sext_small E 34 rf E34), ?(U_atom E 34 rf E34), ?(U_lit E 0) in Hc by lia.
- (* taken: a refusal is kept already, to LATCH *)
  aj_run_to_tok hru1_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQU_LATCH; [awr_ok_tac | ]. hbu_mem.
  apply SRr_ret; left. split; [apply negb_true_iff, Z.eqb_neq in Hc; exact Hc|].
  hbu_post_intro B hru_kept. exact I.
- (* not taken: to the store *)
  aj_run_to_tok hru1_tbl_ok HS HJ SHOK HPgSteps.RTBspan HRU_ST; [awr_ok_tac | ]. hbu_mem.
  apply SRr_ret; right. split; [apply negb_false_iff, Z.eqb_eq in Hc; exact Hc|].
  hbu_post_intro B hru_kept. exact I.
Qed.

(* ================================ 0x836ac: the store ================================ *)
(* the state at LATCH after the store: the journal, every byte outside x->refusal as before, x->refusal = a5 *)
Definition hru_post2 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (X bad : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HQU_LATCH) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r hru_kept -> getr regs2 r = getr regs r) /\
(forall a, ~ (X + 0x84 <= a mod 2 ^ 64 < X + 0x88) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
val_mem rsegs (mrestrict (w_H W) mem2) (X + 0x84) 4 bad.

Lemma hru2_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R X bad pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 15) = w64 bad ->
0 <= R -> R + 0x140 <= 2 ^ 64 -> 0 <= X -> X + 0x88 <= R -> 0 <= bad < 2 ^ 32 ->
In (4, pos) own -> X = frame_addr lyc 4 pos + 0x2c0 ->
(forall o, 0x84 <= o < 0x88 -> apresent (w_H W) memc (X + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (X mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HRU_ST regs memc mdc)
(hru_post2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs X bad).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R X bad pos HJ H9 H15 HR0 HR1 HX0 HXR Hbad
  Hown HX Hpres V138.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity.
remember (hru2_extra X) as ex eqn:Hex.
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E15 : ew (Ereg regs ex) 15 = Z_to_bv 64 bad) by (rewrite (ew_Ereg_nat regs _ 15 (Z_to_bv 5 15) eq_refl); exact H15).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 X) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hru2_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HRU_ST) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hru2_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. exact (hbu_slot_chunk _ _ _ R 0x138 X 33 E33 V138).
    + apply (hm_rw_region rsegs _ (w_H W) memc 33 X); [rewrite E33; apply unsigned_lit_small; lia | lia | lia | | constructor].
      exact Hpres.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, hru1_RA, hru2_RB. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E33, !unsigned_lit_small by lia. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 HRU_ST) with (Z_to_bv 64 HRU_ST).
aj_run_to hru2_tbl_ok HS HJ HQU_LATCH;
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
split; [hbu_io|].
split; [hbu_kept hru_kept|].
split.
- intros a Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[<-|[]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi hru1_RA hru2_RB base_val] in Hr; [lia|].
  rewrite E33, (unsigned_lit_small X) in Hr by lia. rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap in Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact (Hn Hr).
- pose proof (HPgSteps.st_ok_region_at _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E33, unsigned_lit_small in Hch by lia.
  apply Forall_inv in Hch.
  apply (val_of_chunk_ok rsegs _ _ X 0x84 4 _ bad Hch); [rewrite hbu_denot0; exact E15 | cbn; lia | cbn; lia].
Qed.
End d.
End b.

(* ================================ x's bytes ================================ *)
(* while the pair loop runs, x->refusal is x's last word (HPgSegM.hqu_x_open; Spec/HeadBytes.v ha_res_bytes) *)
Definition hru_xP (cs : list cell) (keys : Z) : list byte :=
  repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs ++ repeat (Z_to_bv 8 0) (12 * (X_CELLS - length cs)) ++
  Mem.le4 (Z_to_bv 64 (Z.of_nat (length cs))) ++ Mem.le4 (Z_to_bv 64 keys).
Lemma hru_xP_len : forall cs keys, (length cs <= X_CELLS)%nat -> length (hru_xP cs keys) = 132%nat.
Proof.
intros cs keys H. unfold hru_xP, X_CELLS in *.
rewrite !length_app, !repeat_length, length_x_cells_bytes, !Mem.length_le4. lia.
Qed.
Lemma hru_x_split : forall cs keys rf, 0 <= rf < 2 ^ 64 ->
hqu_x_open cs keys rf = hru_xP cs keys ++ Z_to_le_bytes 4 rf.
Proof.
intros cs keys rf Hrf. unfold hqu_x_open, hru_xP, ha_res_bytes. rewrite <- !app_assoc.
replace (Mem.le4 (Z_to_bv 64 rf)) with (Z_to_le_bytes 4 rf)
  by (unfold Mem.le4; rewrite unsigned_lit_small by lia; reflexivity).
reflexivity.
Qed.
Lemma hru_slice_rf : forall cs keys v, (length cs <= X_CELLS)%nat ->
hm_slice (hru_xP cs keys ++ Z_to_le_bytes 4 v) 132 4 = Z_to_le_bytes 4 v.
Proof.
intros cs keys v H. unfold hm_slice.
rewrite skipn_app, (hru_xP_len cs keys H), Nat.sub_diag, skipn_O.
rewrite skipn_all2 by (rewrite (hru_xP_len cs keys H); lia). cbn [app].
apply firstn_all2. rewrite length_Z_to_le_bytes. lia.
Qed.
Lemma hru_overwrite_rf : forall cs keys v v', (length cs <= X_CELLS)%nat ->
overwrite (hru_xP cs keys ++ Z_to_le_bytes 4 v) 132 (Z_to_le_bytes 4 v') = hru_xP cs keys ++ Z_to_le_bytes 4 v'.
Proof.
intros cs keys v v' H. unfold overwrite.
rewrite firstn_app, (hru_xP_len cs keys H), Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all2 by (rewrite (hru_xP_len cs keys H); lia).
rewrite skipn_all2 by (rewrite length_app, (hru_xP_len cs keys H), !length_Z_to_le_bytes; lia).
rewrite app_nil_r. reflexivity.
Qed.

(* ================================ memory reading ================================ *)
(* the reader sees only the 64-bit address *)
Lemma hru_aview_mod : forall {fx : YK11.FPState} H mem a, aview rsegs H mem a = aview rsegs H mem (a mod 2 ^ 64).
Proof. intros fx H mem a. unfold aview, mbyte. rewrite (HPgSteps.Z_to_bv_mod64 a). reflexivity. Qed.
(* four readable bytes make a readable word *)
Lemma hru_rd32_some : forall (rd : reader) a,
(forall k, (k < 4)%nat -> exists b : byte, rd (a + Z.of_nat k) = Some (bv_unsigned b)) ->
exists v, rd32 rd a v.
Proof.
intros rd a H.
destruct (H 0%nat ltac:(lia)) as (b0 & H0). destruct (H 1%nat ltac:(lia)) as (b1 & H1).
destruct (H 2%nat ltac:(lia)) as (b2 & H2). destruct (H 3%nat ltac:(lia)) as (b3 & H3).
exists (bytes_le_to_Z [b0; b1; b2; b3]). intros k Hk.
change 4%nat with (length [b0; b1; b2; b3]).
rewrite (hm_lez_le_byte [b0; b1; b2; b3] k) by (cbn [length]; lia).
destruct k as [|[|[|[|k]]]]; [exact H0 | exact H1 | exact H2 | exact H3 | cbn [length] in Hk; lia].
Qed.
(* a value kept byte by byte under the reader *)
Lemma hru_val_mem_kept : forall {fx : YK11.FPState} H H' (m m' : word -> option byte) a n v,
(forall i, 0 <= i < Z.of_nat n -> aview rsegs H' m' (a + i) = aview rsegs H m (a + i)) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros fx H H' m m' a n v Hk Hv kk Hkk. specialize (Hv kk Hkk). specialize (Hk (Z.of_nat kk) ltac:(lia)).
cbv beta delta [aview] in Hk. rewrite Hv in Hk. cbn [option_map] in Hk.
destruct (mbyte rsegs (mrestrict H' m') (a + Z.of_nat kk)) as [b|] eqn:Eb; try rewrite Eb in Hk;
  cbn [option_map] in Hk; [|discriminate Hk].
injection Hk as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
(* the cells of M03's lists all lie in the real frame [R, R + 0x160) *)
Definition hru_cellb (f : hd_loc * Z) : bool :=
match fst f with LReg _ => true | LCell XR o => (0 <=? o) && (o <=? 0x158) | LCell _ _ => false end.
Lemma hru_at_store : forall {fx : YK11.FPState} H mem mem' regs e L, hsu_at rsegs H mem regs e L ->
forallb hru_cellb L = true ->
(forall i, e_R e <= i < e_R e + 0x160 -> aview rsegs H mem' i = aview rsegs H mem i) ->
hsu_at rsegs H mem' regs e L.
Proof.
intros fx H mem mem' regs e L HL Hb K. unfold hsu_at in *. rewrite Forall_forall in *.
intros [[r|b o] v] Hx. { exact (HL _ Hx). }
pose proof (HL _ Hx) as Hv. pose proof (proj1 (forallb_forall _ _) Hb _ Hx) as Hc. unfold hru_cellb in Hc.
cbn [fst] in Hc. destruct b; try discriminate Hc.
apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2.
cbn [hd_at fst snd hd_xv] in Hv |- *.
eapply hru_val_mem_kept; [|exact Hv]. intros i Hi. apply K. lia.
Qed.

(* ================================ the cut ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the frame for locals has the same address at every state of the harness's journal (YG0f.v layout_le keeps
   the layout's frame base) *)
Lemma hru_frame_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
STK' sp0' FP' W0' mem0' md0' own' ly' S' W' mem' md' k' cid pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal rsegs B STK' sp0' FP' ly S W0' mem0' md0' own' ly' S' W' mem' md' k' ->
frame_addr ly' cid pos = frame_addr lyc cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k STK' sp0' FP' W0' mem0' md0' own' ly' S' W' mem' md' k'
  cid pos HJ1 HJ2.
destruct HJ1 as (_ & L1 & _). destruct HJ2 as (_ & L2 & _).
destruct L1 as (_ & _ & _ & _ & _ & F1 & _). destruct L2 as (_ & _ & _ & _ & _ & F2 & _).
unfold frame_addr. rewrite F1, F2. reflexivity.
Qed.

(* the frame for locals at the segment's start: owned by the harness, in application memory, below the
   allocation ceiling and so below the real frame *)
Lemma hru_start_F : forall (cx : hsu_scx rsegs) r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
In (4, x_pos cx) (x_own cx) /\ e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx) /\
4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ in_app (e_F (x_e cx)) 1024 /\
alloc_ceiling + T_SEG_STK <= e_R (x_e cx).
Proof.
intros cx r ev HS. pose proof (hbu_start_pre B cx r ev HS) as Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _).
pose proof hqu_pcs_himg as (_ & _ & _ & _ & _ & _ & _ & _ & Hcid & _). rewrite Hcid in Hown, HF.
unfold HQU_CID in Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok rsegs B) _ _ _ _ _ 4 (x_pos cx) HAR Hfin) as (_ & Happ & _).
destruct (al_sep _ _ (AR_laws_ok rsegs B) _ _ _ _ _ HAR) as (_ & Hf).
pose proof (proj1 (Forall_forall _ _) Hf (4, x_pos cx) Hfin) as (Hf1 & Hf2). cbn [fst snd] in Hf1, Hf2.
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity. rewrite Hfb in Happ, Hf2.
rewrite <- HF in Happ, Hf1, Hf2.
pose proof (hbu_start_R B cx r ev HS) as (_ & _ & _ & HRc).
split; [exact Hown|]. split; [exact HF|]. split; [lia|]. split; [lia|]. split; [exact Happ | exact HRc].
Qed.

Lemma hru_w3 : hi_w3 headamp_himg_B = [(XF 0, 0x2a0, 0xa8); (XShF, 0x54, 0x15); (XR, 0, 0x160)].
Proof. reflexivity. Qed.

(* The cut base of the pair loop after a store whose n bytes at a lie inside x, [F + 0x2c0, F + 0x348): the
   journal, I/O state and registers sp, gp, tp as the store's post gives them, every byte outside [a, a + n) as
   before, and the n bytes readable. Every fact of the base is kept: the stored bytes lie in M03's write set and
   apart from the frame's shadow row, the read-only image, the pp / pod / out blocks and res; the errno cell is
   readable wherever it lies. The key and cell pieces' stores into x (x->keys at x + 0x80, the cells at x + 4)
   take the same lemma. *)
Lemma hru_base3_store : forall (cx : hsu_scx rsegs) r ev (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2
regs4 mem4 md4 (a : Z) (n : nat) (v : Z),
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem4 md4 (x_k cx) ->
same_io md2 md4 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs4 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
e_F (x_e cx) + HQU_XO <= a -> a + Z.of_nat n <= e_F (x_e cx) + HQU_XO + 0x88 ->
(forall y, ~ (a <= y mod 2 ^ 64 < a + Z.of_nat n) -> aview rsegs (w_H W2) mem4 y = aview rsegs (w_H W2) mem2 y) ->
val_mem rsegs (mrestrict (w_H W2) mem4) a n v ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs4 mem4 md4.
Proof.
intros cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 a n v HS Hb3 HJ4 Hio4 Hk42 Ha0 Ha1 Kmem Vv.
pose proof (hru_start_F cx r ev HS) as (Hown & HFe & HF4k & HFc & HFapp & HFR).
pose proof (@alloc_ceiling_val rc) as [[Hc0 Hc1] _].
unfold T_SEG_STK, ASTACK in HFR.
pose proof (hbu_start_wf B cx r ev HS) as Hwf.
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
unfold HQU_XO in Ha0, Ha1.
set (F := e_F (x_e cx)) in *.
assert (K' : forall y, 0 <= y < 2 ^ 64 -> ~ (a <= y < a + Z.of_nat n) ->
  aview rsegs (w_H W2) mem4 y = aview rsegs (w_H W2) mem2 y).
{ intros y Hy Hn. apply Kmem. rewrite Z.mod_small by lia. exact Hn. }
destruct Hb3 as (Hcore' & Hfxk & Hfsh & Hrom & Hpp & Hpod & Hout & Hres & Herr).
pose proof Hcore' as (HJ & _ & _ & Hperm & _).
assert (HFly : frame_addr ly2 4 (x_pos cx) = F).
{ pose proof (hbu_start_pre B cx r ev HS) as (HJ0 & _).
  rewrite HFe. eapply hru_frame_at; [exact HJ0 | exact HJ]. }
pose proof HJ as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
assert (Hfin2 : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs2; apply in_or_app; left; exact Hown).
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity.
(* where the other objects lie *)
pose proof HS as (_ & _ & _ & Hlen & _ & _ & Hfpod & _ & _ & _ & _ & Hfout & _).
pose proof (hbu_start_pre B cx r ev HS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
pose proof (hbu_start_pp B cx r ev HS) as (Hppin & _ & Hp4k & Hpc & Hceil).
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
assert (Hlc : Z.of_nat (length (ans_cells (hqu_ans rsegs cx r))) <= e_cap (x_e cx)).
{ unfold hqu_ans. destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]. }
assert (Hb : Z.of_nat (length (buf r)) <= POD_BUF_MAX)
  by (pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & HL0); unfold POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents r)).
{ eapply Forall_impl; [|exact (proj2 (ents_wf r Hwf))]. intros e (_ & He & Hz). lia. }
pose proof (hm_pp_len_img (buf r) (is_props r) (has_params r) (params_struct r) (ents r) (corrupt r)
  Hb Hn32 Hs) as Lpp.
set (Wr := fun y : Z => (y < 0 \/ 2 ^ 64 <= y) \/ (a <= y < a + Z.of_nat n)).
assert (KW : forall y, ~ Wr y -> aview rsegs (w_H W2) mem4 y = aview rsegs (w_H W2) mem2 y).
{ intros y Hy. unfold Wr in Hy. apply K'; lia. }
split.
{ unfold hsu_core, hsu_mid in Hcore' |- *. destruct Hcore' as (_ & H234 & Hfr & Hperm' & Hio & Hmo & Hmem).
  split; [exact HJ4|]. split; [intros q Hq; rewrite (Hk42 q Hq); exact (H234 q Hq)|].
  split; [exact Hfr|]. split; [exact Hperm'|].
  split; [exact (same_io_trans _ _ _ Hio Hio4)|]. split; [exact Hmo|].
  intros y Hy Hns HE. rewrite <- (Hmem y Hy Hns HE). apply K'; [exact Hy|]. intros Hin. apply HE.
  left. unfold hd_inw. rewrite hru_w3. apply Exists_cons_hd. cbn [hd_xv fst snd]. fold F. lia. }
split; [exact Hfxk|].
split.
{ unfold hsu_fsh_at in Hfsh |- *. apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem4 _ hqu_shX Hfsh).
  intros i Hi. rewrite hqu_shX_len in Hi.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold shadow_addr, SHADOW_OFF.
  change (e_F (x_e cx)) with F.
  assert (Hdv : 8 * (F / 8) <= F < 8 * (F / 8) + 8)
    by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
  apply K'; [split | intros Hin]; lia. }
split.
{ apply (hm_rom_kept_wr rsegs Wr W2 W2 mem2 mem4 Hrom KW).
  intros y Hy Hw. pose proof Hy as (sg & Hsg & _ & Hr).
  assert (Hi : in_img rsegs y) by (exists sg; split; [exact Hsg | exact Hr]).
  pose proof (HPgSteps.img_segs_low y Hi) as Hlow. unfold Wr in Hw. unfold kLowMemEnd in Hlow.
  destruct Hw as [Hw|Hw]; [lia|].
  assert (Hfr' : exists cid pos, In (cid, pos) (frames S2) /\
    frame_addr ly2 cid pos <= y < frame_addr ly2 cid pos + fs_frame_bytes cid).
  { exists 4, (x_pos cx). split; [exact Hfin2|]. rewrite Hfb, HFly. lia. }
  destruct (al_client_img _ _ (AR_laws_ok rsegs B) _ _ _ _ _ y HAR2 (or_intror (or_introl Hfr'))) as (_ & Hni).
  exact (Hni Hi). }
split.
{ unfold hsu_pp_at in Hpp |- *.
  apply (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hpp KW).
  intros y Hy. unfold pp_bytes in Hy. rewrite Lpp in Hy. unfold Wr, PP_SIZE in *. lia. }
split.
{ apply (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hpod KW).
  intros y Hy. unfold Wr. lia. }
split.
{ apply (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hout KW).
  intros y Hy. try unfold hd_zbytes in Hy. rewrite ?length_map, ?length_ha_cells_bytes in Hy. unfold Wr. lia. }
split.
{ apply (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem4 _ _ Hres KW).
  intros y Hy. unfold ans_res_bytes in Hy. rewrite length_ha_res_bytes in Hy.
  change (e_F (x_e cx)) with F in Hy. unfold Wr, HQU_RES in *. lia. }
destruct Herr as (ev0 & Hev0).
apply hru_rd32_some. intros kk Hkk.
destruct (Z_lt_dec ((as_errno B + Z.of_nat kk) mod 2 ^ 64) a) as [Hlo|Hlo];
[|destruct (Z_lt_dec ((as_errno B + Z.of_nat kk) mod 2 ^ 64) (a + Z.of_nat n)) as [Hhi|Hhi]].
- exists (Z_to_bv 8 (le_byte ev0 4 kk)). rewrite Kmem by lia. rewrite (Hev0 kk Hkk).
  f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold le_byte. rewrite Z.mod_mod by lia. reflexivity.
- set (j := Z.to_nat ((as_errno B + Z.of_nat kk) mod 2 ^ 64 - a)).
  assert (Hj : (j < n)%nat) by (unfold j; lia).
  pose proof (Vv j Hj) as Vj.
  exists (Z_to_bv 8 (le_byte v n j)). rewrite hru_aview_mod. unfold aview.
  replace ((as_errno B + Z.of_nat kk) mod 2 ^ 64) with (a + Z.of_nat j) by (unfold j; lia).
  rewrite Vj. reflexivity.
- exists (Z_to_bv 8 (le_byte ev0 4 kk)). rewrite Kmem by lia. rewrite (Hev0 kk Hkk).
  f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold le_byte. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* RF 0x836a0 -> LATCH 0x836b4 at m + 2 *)
Theorem hbu_refuse_B : hqu_piece_M3b_refuse_stmt rsegs B MT.
Proof.
unfold hqu_piece_M3b_refuse_stmt. intros cx POST r ev at0 m HS HL.
unfold hqu_from_RF. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v bad cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hf3 & Hlive & Ham & Hexp & Hbad & Hpinv & Hx).
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _).
pose proof Hx as (Hxg & Hcl & Hcc & Hck & Hkr & Hrf).
pose proof Hpinv as (_ & _ & Hsm & _).
pose proof (hbu_start_R B cx r ev HS) as (HR0 & HR1 & _ & _).
pose proof (hru_start_F cx r ev HS) as (Hown & HFe & HF4k & HFc & HFapp & HFR).
pose proof (@alloc_ceiling_val rc) as [[Hc0 Hc1] _].
unfold T_SEG_STK, ASTACK in HFR.
unfold hsu_at_cx in Hat.
pose proof (hbu_at_get _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hbu_in)) as R9.
pose proof (hbu_at_get _ _ _ _ _ 15 bad Hat ltac:(hbu_in)) as R15.
pose proof (hbu_at_cell _ _ _ _ _ XR 0x138 (e_F (x_e cx) + HQU_XO) Hat ltac:(hbu_in)) as C138.
cbn [hd_xv] in C138.
assert (Hbad' : bad = 4 \/ bad = 5) by (unfold REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE in Hbad; lia).
assert (Hrf' : rf = 0 \/ rf = 4 \/ rf = 5) by (unfold REFUSE_NONE, REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE in Hrf; lia).
(* x->refusal *)
assert (Vrf : val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + HQU_XO + 0x84) 4 rf).
{ pose proof Hxg as Hb. rewrite (hru_x_split cs (keys + 1) rf ltac:(lia)) in Hb.
  pose proof (hm_bytes_field rsegs _ _ _ _ 132 4 rf Hb (hru_slice_rf cs (keys + 1) rf Hcl)
    ltac:(rewrite length_app, (hru_xP_len cs (keys + 1) Hcl), length_Z_to_le_bytes; lia)) as V.
  exact V. }
eapply SRr_bind.
{ apply (hru1_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_F (x_e cx) + HQU_XO) rf HJ R9);
  unfold HQU_XO in *; try lia; [exact C138 | exact Vrf]. }
intros W3 c3 _ [(Hrf0 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _) | (Hrf0 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)].
- (* a refusal is kept already: LATCH with x as it is *)
  pose proof (hbu_fold_refuse _ cx r m k v bad cs keys rf Hpinv Hexp) as Hfold'.
  replace (if rf =? REFUSE_NONE then bad else rf) with rf in Hfold'
    by (unfold REFUSE_NONE; destruct (Z.eqb_spec rf 0); [lia | reflexivity]).
  pose proof (hbu_at_keep _ _ _ _ _ Hat regs3 hru_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HL fx2 ly2 S2 W2 regs3 mem2 md3 cs (keys + 1) rf).
  split.
  { apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hru_kept; hbu_kin. }
  split.
  { unfold hsu_at_cx. replace (Z.of_nat (S (S m))) with (Z.of_nat m + 2) by lia. hbu_sub Hat3. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
  split; [unfold hqu_nent; lia|]. split; [lia|]. split; [exact Hx | exact Hfold'].
- (* the store *)
  subst rf.
  pose proof (hbu_fold_refuse _ cx r m k v bad cs keys 0 Hpinv Hexp) as Hfold'.
  replace (if 0 =? REFUSE_NONE then bad else 0) with bad in Hfold' by reflexivity.
  pose proof (hbu_at_keep _ _ _ _ _ Hat regs3 hru_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  set (F := e_F (x_e cx)) in *.
  (* the frame at the cut *)
  assert (HFly : frame_addr ly2 4 (x_pos cx) = F).
  { pose proof (hbu_start_pre B cx r ev HS) as (HJ0 & _).
    rewrite HFe. eapply hru_frame_at; [exact HJ0 | exact HJ]. }
  pose proof HJ as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
  assert (Hfin2 : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs2; apply in_or_app; left; exact Hown).
  destruct (al_frames _ _ (AR_laws_ok rsegs B) _ _ _ _ _ 4 (x_pos cx) HAR2 Hfin2) as (_ & _ & HFpres & _).
  assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity. rewrite Hfb, HFly in HFpres.
  eapply SRr_bind.
  { apply (hru2_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e cx)) (F + HQU_XO) bad (x_pos cx) HJ3);
    unfold HQU_XO in *.
    - rewrite Hk3 by (unfold hru_kept; hbu_kin). exact R9.
    - rewrite Hk3 by (unfold hru_kept; hbu_kin). exact R15.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hown.
    - rewrite HFly. reflexivity.
    - intros o Ho. apply (HFpres (F + 704 + o) ltac:(lia)).
    - exact C138. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Kmem & Vbad).
  unfold HQU_XO in Kmem, Vbad.
  (* the bytes the store left alone *)
  assert (K' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x344 <= a < F + 0x348) ->
    aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. apply Kmem. rewrite Z.mod_small by lia. lia. }
  assert (Hk42 : forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs4 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)).
  { intros q Hq. rewrite Hk4, Hk3; [reflexivity | |]; destruct Hq as [->|[->| ->]]; unfold hru_kept; hbu_kin. }
  apply (HL fx2 ly2 S2 W2 regs4 mem4 md4 cs (keys + 1) bad).
  split.
  { apply (hru_base3_store cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 (F + 0x344) 4 bad HS Hb3 HJ4
      (same_io_trans _ _ _ Hio3 Hio4) Hk42); unfold HQU_XO; try (fold F; lia).
    - intros y Hn. apply Kmem. change (Z.of_nat 4) with 4 in Hn. lia.
    - replace (F + 0x344) with (F + 704 + 0x84) by lia. exact Vbad. }
  split.
  { unfold hsu_at_cx. replace (Z.of_nat (S (S m))) with (Z.of_nat m + 2) by lia.
    apply (hru_at_store _ mem2); [| vm_compute; reflexivity | intros i Hi; apply K'; lia].
    pose proof (hbu_at_keep _ _ _ _ _ Hat3 regs4 hru_kept Hk4 ltac:(vm_compute; reflexivity)) as Hat4.
    hbu_sub Hat4. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
  split; [unfold hqu_nent; lia|]. split; [lia|].
  split; [|exact Hfold'].
  (* x after the store *)
  split.
  { assert (Hxb : hm_bytes rsegs (w_H W2) mem2 (F + 704) (hru_xP cs (keys + 1) ++ Z_to_le_bytes 4 0)).
    { pose proof Hxg as Hb0. unfold HQU_XO in Hb0. rewrite (hru_x_split cs (keys + 1) 0 ltac:(lia)) in Hb0.
      exact Hb0. }
    pose proof (hm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem4 (F + 704) _ 132 4 bad Hxb
      ltac:(replace (F + 704 + Z.of_nat 132) with (F + 704 + 132) by lia; exact Vbad)
      ltac:(rewrite length_app, (hru_xP_len cs (keys + 1) Hcl), length_Z_to_le_bytes; lia)) as Hxn.
    rewrite hru_overwrite_rf in Hxn by exact Hcl.
    unfold HQU_XO. rewrite (hru_x_split cs (keys + 1) bad ltac:(lia)).
    apply Hxn. intros y Hy Hn.
    rewrite length_app, (hru_xP_len cs (keys + 1) Hcl), length_Z_to_le_bytes in Hy.
    apply K'; lia. }
  split; [exact Hcl|]. split; [exact Hcc|]. split; [exact Hck|]. split; [exact Hkr|].
  unfold REFUSE_NONE, REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE. lia.
Qed.
End c.

Print Assumptions hbu_refuse_B.

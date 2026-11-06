(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 BzCFactsSmA BzCFactsSmB CmpFsKit0 CmpHmKit CmpSmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_smBf2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_smBf2.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.
Module S0_cmp_smBf3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc3 : forall (m mf : word -> option byte) (x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 : word),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 22 1 + p 23 1)); C8 (Z_to_bv 64 (p 22 0 + p 23 0)); C8 (Z_to_bv 64 (p 16 0 + p 17 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2)); C8 (Z_to_bv 64 (p 11 1 + p 12 1)); C8 (Z_to_bv 64 (q 19)); C8 (Z_to_bv 64 (p 11 0 + p 12 0)); C8 (Z_to_bv 64 (p 7 0 + p 8 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2)); C8 (Z_to_bv 64 (p 7 1 + p 8 1)); C8 (Z_to_bv 64 (p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 2 1 + p 3 1)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 22 1 + p 23 1)); C8 (Z_to_bv 64 (p 22 0 + p 23 0)); C8 (Z_to_bv 64 (p 16 0 + p 17 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2)); C8 (Z_to_bv 64 (p 11 1 + p 12 1)); C8 (Z_to_bv 64 (q 19)); C8 (Z_to_bv 64 (p 11 0 + p 12 0)); C8 (Z_to_bv 64 (p 7 0 + p 8 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2)); C8 (Z_to_bv 64 (p 7 1 + p 8 1)); C8 (Z_to_bv 64 (p 4 0 + p 5 0 + p 6 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (p 46 0)) sp gp tp (Z_to_bv 64 (p 29 1)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 23 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + q 38 * 16 + 51640)) (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)) (Z_to_bv 64 (p 9 1)) (Z_to_bv 64 (p 9 2)) (Z_to_bv 64 (p 46 1 + p 47 1)) (Z_to_bv 64 (p 39 0)) (Z_to_bv 64 (p 46 0 + p 47 0)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 47 1)) (Z_to_bv 64 (E + q 10 * 16 + 51640)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (E + q 30 * 16 + 51640)) (Z_to_bv 64 (E + q 13 * 16 + 51640)) (Z_to_bv 64 (p 37 2)) (Z_to_bv 64 (p 6 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 4 1 + p 5 1)) (Z_to_bv 64 (E + q 18 * 16 + 51640)) (Z_to_bv 64 (p 4 0 + p 5 0)) (Z_to_bv 64 (E + q 9 * 16 + 51640)) (Z_to_bv 64 (E + q 6 * 16 + 51640)) (Z_to_bv 64 (E + q 39 * 16 + 51640)) (Z_to_bv 64 (p 38 1)))
           F (Z_to_bv 64 0x1660c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (E + q 13 * 16 + 51640)) sp gp tp (Z_to_bv 64 (p 29 1)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 23 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + q 38 * 16 + 51640)) (Z_to_bv 64 (E + q 31 * 16 + 51640)) (Z_to_bv 64 (E + q 37 * 16 + 51640)) (Z_to_bv 64 (p 30 2)) (Z_to_bv 64 (p 37 0)) (Z_to_bv 64 (p 38 0)) (Z_to_bv 64 (p 31 0)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 29 1 + p 30 1)) (Z_to_bv 64 (p 0 2 + p 1 2)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (E + q 30 * 16 + 51640)) (Z_to_bv 64 (E + q 13 * 16 + 51640)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 29 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 4 1 + p 5 1)) (Z_to_bv 64 (E + q 18 * 16 + 51640)) (Z_to_bv 64 (p 4 0 + p 5 0)) (Z_to_bv 64 (E + q 9 * 16 + 51640)) (Z_to_bv 64 (E + q 6 * 16 + 51640)) (Z_to_bv 64 (q 39)) (Z_to_bv 64 (E + q 7 * 16 + 51640)))
         F (Z_to_bv 64 0x164f4) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (QB 10 ltac:(lia)) as QB10.
    pose proof (QB 13 ltac:(lia)) as QB13.
    pose proof (QB 14 ltac:(lia)) as QB14.
    pose proof (QB 15 ltac:(lia)) as QB15.
    pose proof (QB 18 ltac:(lia)) as QB18.
    pose proof (QB 19 ltac:(lia)) as QB19.
    pose proof (QB 30 ltac:(lia)) as QB30.
    pose proof (QB 31 ltac:(lia)) as QB31.
    pose proof (QB 37 ltac:(lia)) as QB37.
    pose proof (QB 38 ltac:(lia)) as QB38.
    pose proof (QB 39 ltac:(lia)) as QB39.
    pose proof (QB 6 ltac:(lia)) as QB6.
    pose proof (QB 7 ltac:(lia)) as QB7.
    pose proof (QB 9 ltac:(lia)) as QB9.
    (* [comment removed for export] *) RDP LPK 31%Z 1%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 31%Z 2%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 38%Z 1%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 37%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 37%Z 2%Z.
    (* [comment removed for export] *) RDQ AR1 46%Z.
    (* [comment removed for export] *) RDQ AR1 47%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 38%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 39%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 39%Z 1%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 39%Z 2%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 46%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 46%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 46%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 47%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 47%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 47%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 6%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 9%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 9%Z 2%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf3.


Module S0_cmp_smBf4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc4 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 22 1 + p 23 1)); C8 (Z_to_bv 64 (p 22 0 + p 23 0)); C8 (Z_to_bv 64 (p 16 0 + p 17 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2)); C8 (Z_to_bv 64 (p 11 1 + p 12 1)); C8 (Z_to_bv 64 (q 19)); C8 (Z_to_bv 64 (p 11 0 + p 12 0)); C8 (Z_to_bv 64 (p 7 0 + p 8 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2)); C8 (Z_to_bv 64 (p 7 1 + p 8 1)); C8 (Z_to_bv 64 (p 4 0 + p 5 0 + p 6 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 22 1 + p 23 1)); C8 (Z_to_bv 64 (p 22 0 + p 23 0)); C8 (Z_to_bv 64 (p 16 0 + p 17 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 7 2 + p 8 2)); C8 (Z_to_bv 64 (p 7 1 + p 8 1)); C8 (Z_to_bv 64 (p 4 0 + p 5 0 + p 6 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (p 46 0)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 19 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 19 0)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2)) (Z_to_bv 64 (p 29 2 + p 30 2)) (Z_to_bv 64 (p 25 0)) (Z_to_bv 64 (q 26)) (Z_to_bv 64 (p 39 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 14 1)) (Z_to_bv 64 (E + q 10 * 16 + 51640)) (Z_to_bv 64 (p 10 0)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1)) (Z_to_bv 64 (p 6 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0)) (Z_to_bv 64 (p 19 2)) (Z_to_bv 64 (E + q 25 * 16 + 51640)) (Z_to_bv 64 (E + q 14 * 16 + 51640)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0)) (Z_to_bv 64 (p 14 0)) (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2)))
           F (Z_to_bv 64 0x16724) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (p 46 0)) sp gp tp (Z_to_bv 64 (p 29 1)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 23 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + q 38 * 16 + 51640)) (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)) (Z_to_bv 64 (p 9 1)) (Z_to_bv 64 (p 9 2)) (Z_to_bv 64 (p 46 1 + p 47 1)) (Z_to_bv 64 (p 39 0)) (Z_to_bv 64 (p 46 0 + p 47 0)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 47 1)) (Z_to_bv 64 (E + q 10 * 16 + 51640)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (E + q 30 * 16 + 51640)) (Z_to_bv 64 (E + q 13 * 16 + 51640)) (Z_to_bv 64 (p 37 2)) (Z_to_bv 64 (p 6 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 4 1 + p 5 1)) (Z_to_bv 64 (E + q 18 * 16 + 51640)) (Z_to_bv 64 (p 4 0 + p 5 0)) (Z_to_bv 64 (E + q 9 * 16 + 51640)) (Z_to_bv 64 (E + q 6 * 16 + 51640)) (Z_to_bv 64 (E + q 39 * 16 + 51640)) (Z_to_bv 64 (p 38 1)))
         F (Z_to_bv 64 0x1660c) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 10 ltac:(lia)) as QB10.
    pose proof (QB 13 ltac:(lia)) as QB13.
    pose proof (QB 14 ltac:(lia)) as QB14.
    pose proof (QB 15 ltac:(lia)) as QB15.
    pose proof (QB 18 ltac:(lia)) as QB18.
    pose proof (QB 19 ltac:(lia)) as QB19.
    pose proof (QB 30 ltac:(lia)) as QB30.
    pose proof (QB 38 ltac:(lia)) as QB38.
    pose proof (QB 39 ltac:(lia)) as QB39.
    pose proof (QB 6 ltac:(lia)) as QB6.
    pose proof (QB 9 ltac:(lia)) as QB9.
    (* [comment removed for export] *) RDP LPK 10%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 10%Z 1%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 13%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 13%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 14%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 14%Z 1%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 18%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 19%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 19%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 19%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDQ AR1 24%Z.
    (* [comment removed for export] *) RDQ AR1 25%Z.
    (* [comment removed for export] *) RDQ AR1 26%Z.
    (* [comment removed for export] *) RDQ AR1 27%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 24%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 24%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 24%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 25%Z 0%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf4.


Module S0_cmp_smBf5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc5 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 22 1 + p 23 1)); C8 (Z_to_bv 64 (p 22 0 + p 23 0)); C8 (Z_to_bv 64 (p 16 0 + p 17 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 7 2 + p 8 2)); C8 (Z_to_bv 64 (p 7 1 + p 8 1)); C8 (Z_to_bv 64 (p 4 0 + p 5 0 + p 6 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 49 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 19 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 19 0)) (Z_to_bv 64 (E + q 15 * 16 + 51640)) (Z_to_bv 64 (p 14 2)) (Z_to_bv 64 (p 25 0)) (Z_to_bv 64 (q 26)) (Z_to_bv 64 (E + q 49 * 16 + 51640)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 15 0)) (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)) (Z_to_bv 64 (p 10 0)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1 + p 10 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0)) (Z_to_bv 64 (p 19 2)) (Z_to_bv 64 (E + q 25 * 16 + 51640)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0)) (Z_to_bv 64 (p 15 1)) (Z_to_bv 64 (p 15 2)))
           F (Z_to_bv 64 0x16814) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (p 46 0)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 19 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 19 0)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2)) (Z_to_bv 64 (p 29 2 + p 30 2)) (Z_to_bv 64 (p 25 0)) (Z_to_bv 64 (q 26)) (Z_to_bv 64 (p 39 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 14 1)) (Z_to_bv 64 (E + q 10 * 16 + 51640)) (Z_to_bv 64 (p 10 0)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1)) (Z_to_bv 64 (p 6 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0)) (Z_to_bv 64 (p 19 2)) (Z_to_bv 64 (E + q 25 * 16 + 51640)) (Z_to_bv 64 (E + q 14 * 16 + 51640)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0)) (Z_to_bv 64 (p 14 0)) (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2)))
         F (Z_to_bv 64 0x16724) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 10 ltac:(lia)) as QB10.
    pose proof (QB 14 ltac:(lia)) as QB14.
    pose proof (QB 15 ltac:(lia)) as QB15.
    pose proof (QB 25 ltac:(lia)) as QB25.
    pose proof (QB 26 ltac:(lia)) as QB26.
    pose proof (QB 27 ltac:(lia)) as QB27.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 48%Z.
    (* [comment removed for export] *) RDQ AR1 49%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 48%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 48%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 48%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 49%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 10%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 14%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 15%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 15%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 15%Z 2%Z.
    (* [comment removed for export] *) lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf5.


Module S0_cmp_smBf6.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc6 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 49 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 49 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0)) sp gp tp (Z_to_bv 64 (p 32 0)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 32 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0)) (Z_to_bv 64 (q 43)) (Z_to_bv 64 (p 14 2)) (Z_to_bv 64 (E + q 26 * 16 + 51640)) (Z_to_bv 64 (E + q 32 * 16 + 51640)) (Z_to_bv 64 (E + q 49 * 16 + 51640)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 15 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1)) (Z_to_bv 64 (p 33 0)) (Z_to_bv 64 (p 26 0)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1 + p 10 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (E + q 33 * 16 + 51640)) (Z_to_bv 64 (q 41 * 16)) (Z_to_bv 64 (q 40 * 16)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2)) (Z_to_bv 64 (p 32 2)) (Z_to_bv 64 (p 15 1)) (Z_to_bv 64 (p 15 2)))
           F (Z_to_bv 64 0x168dc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 19 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 19 0)) (Z_to_bv 64 (E + q 15 * 16 + 51640)) (Z_to_bv 64 (p 14 2)) (Z_to_bv 64 (p 25 0)) (Z_to_bv 64 (q 26)) (Z_to_bv 64 (E + q 49 * 16 + 51640)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 15 0)) (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)) (Z_to_bv 64 (p 10 0)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1 + p 10 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0)) (Z_to_bv 64 (p 19 2)) (Z_to_bv 64 (E + q 25 * 16 + 51640)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0)) (Z_to_bv 64 (p 15 1)) (Z_to_bv 64 (p 15 2)))
         F (Z_to_bv 64 0x16814) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 48 0 ltac:(lia) ltac:(lia)) as PB48_0.
    pose proof (PB 48 1 ltac:(lia) ltac:(lia)) as PB48_1.
    pose proof (PB 48 2 ltac:(lia) ltac:(lia)) as PB48_2.
    pose proof (PB 49 0 ltac:(lia) ltac:(lia)) as PB49_0.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 15 ltac:(lia)) as QB15.
    pose proof (QB 25 ltac:(lia)) as QB25.
    pose proof (QB 26 ltac:(lia)) as QB26.
    pose proof (QB 27 ltac:(lia)) as QB27.
    pose proof (QB 49 ltac:(lia)) as QB49.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 25%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 25%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 26%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 26%Z 1%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDQ AR1 32%Z.
    (* [comment removed for export] *) RDQ AR1 33%Z.
    (* [comment removed for export] *) RDQ AR1 34%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 35%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 32%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 32%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 32%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 33%Z 0%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 40%Z.
    (* [comment removed for export] *) RDQ AR1 41%Z.
    (* [comment removed for export] *) RDQ AR1 42%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 43%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf6.


Module S0_cmp_smBf7.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc7 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 49 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (q 21)) sp gp tp (Z_to_bv 64 (p 32 0)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 32 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0)) (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)) (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)) (Z_to_bv 64 (E + q 26 * 16 + 51640)) (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0)) (Z_to_bv 64 (q 20)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1)) (Z_to_bv 64 (p 33 0)) (Z_to_bv 64 (p 26 0)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1 + p 10 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (E + q 33 * 16 + 51640)) (Z_to_bv 64 (E + q 41 * 16 + 51640)) (Z_to_bv 64 (p 40 2)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2)) (Z_to_bv 64 (p 32 2)) (Z_to_bv 64 (p 15 1)) (Z_to_bv 64 (p 15 2)))
           F (Z_to_bv 64 0x16984) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0)) sp gp tp (Z_to_bv 64 (p 32 0)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 32 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0)) (Z_to_bv 64 (q 43)) (Z_to_bv 64 (p 14 2)) (Z_to_bv 64 (E + q 26 * 16 + 51640)) (Z_to_bv 64 (E + q 32 * 16 + 51640)) (Z_to_bv 64 (E + q 49 * 16 + 51640)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 15 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1)) (Z_to_bv 64 (p 33 0)) (Z_to_bv 64 (p 26 0)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1 + p 10 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (E + q 33 * 16 + 51640)) (Z_to_bv 64 (q 41 * 16)) (Z_to_bv 64 (q 40 * 16)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2)) (Z_to_bv 64 (p 32 2)) (Z_to_bv 64 (p 15 1)) (Z_to_bv 64 (p 15 2)))
         F (Z_to_bv 64 0x168dc) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 25 1 ltac:(lia) ltac:(lia)) as PB25_1.
    pose proof (PB 25 2 ltac:(lia) ltac:(lia)) as PB25_2.
    pose proof (PB 26 0 ltac:(lia) ltac:(lia)) as PB26_0.
    pose proof (PB 26 1 ltac:(lia) ltac:(lia)) as PB26_1.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 32 0 ltac:(lia) ltac:(lia)) as PB32_0.
    pose proof (PB 32 1 ltac:(lia) ltac:(lia)) as PB32_1.
    pose proof (PB 32 2 ltac:(lia) ltac:(lia)) as PB32_2.
    pose proof (PB 33 0 ltac:(lia) ltac:(lia)) as PB33_0.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 48 0 ltac:(lia) ltac:(lia)) as PB48_0.
    pose proof (PB 48 1 ltac:(lia) ltac:(lia)) as PB48_1.
    pose proof (PB 48 2 ltac:(lia) ltac:(lia)) as PB48_2.
    pose proof (PB 49 0 ltac:(lia) ltac:(lia)) as PB49_0.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 15 ltac:(lia)) as QB15.
    pose proof (QB 26 ltac:(lia)) as QB26.
    pose proof (QB 27 ltac:(lia)) as QB27.
    pose proof (QB 32 ltac:(lia)) as QB32.
    pose proof (QB 33 ltac:(lia)) as QB33.
    pose proof (QB 34 ltac:(lia)) as QB34.
    pose proof (QB 35 ltac:(lia)) as QB35.
    pose proof (QB 40 ltac:(lia)) as QB40.
    pose proof (QB 41 ltac:(lia)) as QB41.
    pose proof (QB 42 ltac:(lia)) as QB42.
    pose proof (QB 43 ltac:(lia)) as QB43.
    pose proof (QB 49 ltac:(lia)) as QB49.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 40%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 40%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 40%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 41%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 49%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 49%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 20%Z.
    (* [comment removed for export] *) RDQ AR1 21%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf7.


Module S0_cmp_smBf8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc8 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (E + q 21 * 16 + 51640)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 27 0)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1)) (Z_to_bv 64 (p 34 1)) (Z_to_bv 64 (p 34 0)) (Z_to_bv 64 (p 20 2)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1)) (Z_to_bv 64 (E + q 34 * 16 + 51640)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0)) (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2)) (Z_to_bv 64 (E + q 41 * 16 + 51640)) (Z_to_bv 64 (q 42)) (Z_to_bv 64 (p 27 1)) (Z_to_bv 64 (p 27 2)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0)) (Z_to_bv 64 (p 20 0)))
           F (Z_to_bv 64 0x16a44) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (q 21)) sp gp tp (Z_to_bv 64 (p 32 0)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 32 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0)) (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)) (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)) (Z_to_bv 64 (E + q 26 * 16 + 51640)) (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0)) (Z_to_bv 64 (q 20)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1)) (Z_to_bv 64 (p 33 0)) (Z_to_bv 64 (p 26 0)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1 + p 10 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (E + q 33 * 16 + 51640)) (Z_to_bv 64 (E + q 41 * 16 + 51640)) (Z_to_bv 64 (p 40 2)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2)) (Z_to_bv 64 (p 32 2)) (Z_to_bv 64 (p 15 1)) (Z_to_bv 64 (p 15 2)))
         F (Z_to_bv 64 0x16984) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx e Q sp gp tp F fc sv w24 w56 lp cb gs iter nSel totc CX HA Hgs HgsM HM QB PB PD.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 25 1 ltac:(lia) ltac:(lia)) as PB25_1.
    pose proof (PB 25 2 ltac:(lia) ltac:(lia)) as PB25_2.
    pose proof (PB 26 0 ltac:(lia) ltac:(lia)) as PB26_0.
    pose proof (PB 26 1 ltac:(lia) ltac:(lia)) as PB26_1.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 32 0 ltac:(lia) ltac:(lia)) as PB32_0.
    pose proof (PB 32 1 ltac:(lia) ltac:(lia)) as PB32_1.
    pose proof (PB 32 2 ltac:(lia) ltac:(lia)) as PB32_2.
    pose proof (PB 33 0 ltac:(lia) ltac:(lia)) as PB33_0.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 40 0 ltac:(lia) ltac:(lia)) as PB40_0.
    pose proof (PB 40 1 ltac:(lia) ltac:(lia)) as PB40_1.
    pose proof (PB 40 2 ltac:(lia) ltac:(lia)) as PB40_2.
    pose proof (PB 41 0 ltac:(lia) ltac:(lia)) as PB41_0.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 48 0 ltac:(lia) ltac:(lia)) as PB48_0.
    pose proof (PB 48 1 ltac:(lia) ltac:(lia)) as PB48_1.
    pose proof (PB 48 2 ltac:(lia) ltac:(lia)) as PB48_2.
    pose proof (PB 49 0 ltac:(lia) ltac:(lia)) as PB49_0.
    pose proof (PB 49 1 ltac:(lia) ltac:(lia)) as PB49_1.
    pose proof (PB 49 2 ltac:(lia) ltac:(lia)) as PB49_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 20 ltac:(lia)) as QB20.
    pose proof (QB 21 ltac:(lia)) as QB21.
    pose proof (QB 26 ltac:(lia)) as QB26.
    pose proof (QB 27 ltac:(lia)) as QB27.
    pose proof (QB 33 ltac:(lia)) as QB33.
    pose proof (QB 34 ltac:(lia)) as QB34.
    pose proof (QB 35 ltac:(lia)) as QB35.
    pose proof (QB 41 ltac:(lia)) as QB41.
    pose proof (QB 42 ltac:(lia)) as QB42.
    pose proof (QB 43 ltac:(lia)) as QB43.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 20%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 20%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 20%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 21%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 26%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 27%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 27%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 27%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 33%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 33%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 34%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 34%Z 1%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf8.


Module S0_cmp_smBf9.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc9 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (q 27)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2 + p 27 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0 + p 27 0)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 35 0)) (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1 + p 21 1)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1 + p 34 1)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2 + p 34 2)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0 + p 34 0)) (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1 + p 41 1 + p 42 1)) (Z_to_bv 64 (p 42 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0 + p 42 0)) (Z_to_bv 64 (p 35 2)) (Z_to_bv 64 (p 35 1)) (Z_to_bv 64 (q 36)) (Z_to_bv 64 (E + q 43 * 16 + 51640)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2)) (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1 + p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2)) (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2 + p 41 2)) (Z_to_bv 64 (E + q 42 * 16 + 51640)) (Z_to_bv 64 (p 43 0)) (Z_to_bv 64 (q 28)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0)) (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0)))
           F (Z_to_bv 64 0x16b0c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (E + q 21 * 16 + 51640)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 27 0)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1)) (Z_to_bv 64 (p 34 1)) (Z_to_bv 64 (p 34 0)) (Z_to_bv 64 (p 20 2)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1)) (Z_to_bv 64 (E + q 34 * 16 + 51640)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0)) (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2)) (Z_to_bv 64 (E + q 41 * 16 + 51640)) (Z_to_bv 64 (q 42)) (Z_to_bv 64 (p 27 1)) (Z_to_bv 64 (p 27 2)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0)) (Z_to_bv 64 (p 20 0)))
         F (Z_to_bv 64 0x16a44) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 20 0 ltac:(lia) ltac:(lia)) as PB20_0.
    pose proof (PB 20 1 ltac:(lia) ltac:(lia)) as PB20_1.
    pose proof (PB 20 2 ltac:(lia) ltac:(lia)) as PB20_2.
    pose proof (PB 21 0 ltac:(lia) ltac:(lia)) as PB21_0.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 25 1 ltac:(lia) ltac:(lia)) as PB25_1.
    pose proof (PB 25 2 ltac:(lia) ltac:(lia)) as PB25_2.
    pose proof (PB 26 0 ltac:(lia) ltac:(lia)) as PB26_0.
    pose proof (PB 26 1 ltac:(lia) ltac:(lia)) as PB26_1.
    pose proof (PB 26 2 ltac:(lia) ltac:(lia)) as PB26_2.
    pose proof (PB 27 0 ltac:(lia) ltac:(lia)) as PB27_0.
    pose proof (PB 27 1 ltac:(lia) ltac:(lia)) as PB27_1.
    pose proof (PB 27 2 ltac:(lia) ltac:(lia)) as PB27_2.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 32 0 ltac:(lia) ltac:(lia)) as PB32_0.
    pose proof (PB 32 1 ltac:(lia) ltac:(lia)) as PB32_1.
    pose proof (PB 32 2 ltac:(lia) ltac:(lia)) as PB32_2.
    pose proof (PB 33 0 ltac:(lia) ltac:(lia)) as PB33_0.
    pose proof (PB 33 1 ltac:(lia) ltac:(lia)) as PB33_1.
    pose proof (PB 33 2 ltac:(lia) ltac:(lia)) as PB33_2.
    pose proof (PB 34 0 ltac:(lia) ltac:(lia)) as PB34_0.
    pose proof (PB 34 1 ltac:(lia) ltac:(lia)) as PB34_1.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 40 0 ltac:(lia) ltac:(lia)) as PB40_0.
    pose proof (PB 40 1 ltac:(lia) ltac:(lia)) as PB40_1.
    pose proof (PB 40 2 ltac:(lia) ltac:(lia)) as PB40_2.
    pose proof (PB 41 0 ltac:(lia) ltac:(lia)) as PB41_0.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 48 0 ltac:(lia) ltac:(lia)) as PB48_0.
    pose proof (PB 48 1 ltac:(lia) ltac:(lia)) as PB48_1.
    pose proof (PB 48 2 ltac:(lia) ltac:(lia)) as PB48_2.
    pose proof (PB 49 0 ltac:(lia) ltac:(lia)) as PB49_0.
    pose proof (PB 49 1 ltac:(lia) ltac:(lia)) as PB49_1.
    pose proof (PB 49 2 ltac:(lia) ltac:(lia)) as PB49_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 21 ltac:(lia)) as QB21.
    pose proof (QB 27 ltac:(lia)) as QB27.
    pose proof (QB 34 ltac:(lia)) as QB34.
    pose proof (QB 35 ltac:(lia)) as QB35.
    pose proof (QB 41 ltac:(lia)) as QB41.
    pose proof (QB 42 ltac:(lia)) as QB42.
    pose proof (QB 43 ltac:(lia)) as QB43.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 41%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 41%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 42%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 42%Z 1%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 21%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 21%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDQ AR1 28%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 34%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 35%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 35%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 35%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDQ AR1 36%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 42%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 43%Z 0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf9.


Module S0_cmp_smBf10.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc10 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1 + p 28 1)) sp gp tp (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2 + p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2 + p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2 + p 27 2 + p 28 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0 + p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0 + p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0 + p 27 0 + p 28 0)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1 + p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1 + p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1 + p 21 1 + p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1 + p 28 1)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1 + p 34 1 + p 35 1 + p 36 1)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2 + p 34 2 + p 35 2)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0 + p 34 0 + p 35 0 + p 36 0)) (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1 + p 41 1 + p 42 1 + p 43 1)) (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2 + p 41 2 + p 42 2 + p 43 2)) (Z_to_bv 64 (E + q 45 * 16 + 51640)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0 + p 42 0 + p 43 0)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (p 35 1)) (Z_to_bv 64 (p 36 2)) (Z_to_bv 64 (usp + 616)) (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2 + p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2)) (Z_to_bv 64 (p 45 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (A)) (Z_to_bv 64 (E + q 44 * 16 + 51640)) (Z_to_bv 64 (p 36 1)) (Z_to_bv 64 (p 43 0)) (Z_to_bv 64 (p 45 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0 + p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0)) (Z_to_bv 64 (p 36 0)))
           F (Z_to_bv 64 0x16bbc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1)) sp gp tp (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2 + p 27 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0 + p 27 0)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 35 0)) (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1 + p 21 1)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1 + p 34 1)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2 + p 34 2)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0 + p 34 0)) (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1 + p 41 1 + p 42 1)) (Z_to_bv 64 (p 42 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0 + p 42 0)) (Z_to_bv 64 (p 35 2)) (Z_to_bv 64 (p 35 1)) (Z_to_bv 64 (q 36)) (Z_to_bv 64 (E + q 43 * 16 + 51640)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2)) (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1 + p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2)) (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2 + p 41 2)) (Z_to_bv 64 (E + q 42 * 16 + 51640)) (Z_to_bv 64 (p 43 0)) (Z_to_bv 64 (q 28)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0)) (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0)))
         F (Z_to_bv 64 0x16b0c) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 20 0 ltac:(lia) ltac:(lia)) as PB20_0.
    pose proof (PB 20 1 ltac:(lia) ltac:(lia)) as PB20_1.
    pose proof (PB 20 2 ltac:(lia) ltac:(lia)) as PB20_2.
    pose proof (PB 21 0 ltac:(lia) ltac:(lia)) as PB21_0.
    pose proof (PB 21 1 ltac:(lia) ltac:(lia)) as PB21_1.
    pose proof (PB 21 2 ltac:(lia) ltac:(lia)) as PB21_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 25 1 ltac:(lia) ltac:(lia)) as PB25_1.
    pose proof (PB 25 2 ltac:(lia) ltac:(lia)) as PB25_2.
    pose proof (PB 26 0 ltac:(lia) ltac:(lia)) as PB26_0.
    pose proof (PB 26 1 ltac:(lia) ltac:(lia)) as PB26_1.
    pose proof (PB 26 2 ltac:(lia) ltac:(lia)) as PB26_2.
    pose proof (PB 27 0 ltac:(lia) ltac:(lia)) as PB27_0.
    pose proof (PB 27 1 ltac:(lia) ltac:(lia)) as PB27_1.
    pose proof (PB 27 2 ltac:(lia) ltac:(lia)) as PB27_2.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 32 0 ltac:(lia) ltac:(lia)) as PB32_0.
    pose proof (PB 32 1 ltac:(lia) ltac:(lia)) as PB32_1.
    pose proof (PB 32 2 ltac:(lia) ltac:(lia)) as PB32_2.
    pose proof (PB 33 0 ltac:(lia) ltac:(lia)) as PB33_0.
    pose proof (PB 33 1 ltac:(lia) ltac:(lia)) as PB33_1.
    pose proof (PB 33 2 ltac:(lia) ltac:(lia)) as PB33_2.
    pose proof (PB 34 0 ltac:(lia) ltac:(lia)) as PB34_0.
    pose proof (PB 34 1 ltac:(lia) ltac:(lia)) as PB34_1.
    pose proof (PB 34 2 ltac:(lia) ltac:(lia)) as PB34_2.
    pose proof (PB 35 0 ltac:(lia) ltac:(lia)) as PB35_0.
    pose proof (PB 35 1 ltac:(lia) ltac:(lia)) as PB35_1.
    pose proof (PB 35 2 ltac:(lia) ltac:(lia)) as PB35_2.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 40 0 ltac:(lia) ltac:(lia)) as PB40_0.
    pose proof (PB 40 1 ltac:(lia) ltac:(lia)) as PB40_1.
    pose proof (PB 40 2 ltac:(lia) ltac:(lia)) as PB40_2.
    pose proof (PB 41 0 ltac:(lia) ltac:(lia)) as PB41_0.
    pose proof (PB 41 1 ltac:(lia) ltac:(lia)) as PB41_1.
    pose proof (PB 41 2 ltac:(lia) ltac:(lia)) as PB41_2.
    pose proof (PB 42 0 ltac:(lia) ltac:(lia)) as PB42_0.
    pose proof (PB 42 1 ltac:(lia) ltac:(lia)) as PB42_1.
    pose proof (PB 42 2 ltac:(lia) ltac:(lia)) as PB42_2.
    pose proof (PB 43 0 ltac:(lia) ltac:(lia)) as PB43_0.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 48 0 ltac:(lia) ltac:(lia)) as PB48_0.
    pose proof (PB 48 1 ltac:(lia) ltac:(lia)) as PB48_1.
    pose proof (PB 48 2 ltac:(lia) ltac:(lia)) as PB48_2.
    pose proof (PB 49 0 ltac:(lia) ltac:(lia)) as PB49_0.
    pose proof (PB 49 1 ltac:(lia) ltac:(lia)) as PB49_1.
    pose proof (PB 49 2 ltac:(lia) ltac:(lia)) as PB49_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 28 ltac:(lia)) as QB28.
    pose proof (QB 34 ltac:(lia)) as QB34.
    pose proof (QB 35 ltac:(lia)) as QB35.
    pose proof (QB 36 ltac:(lia)) as QB36.
    pose proof (QB 42 ltac:(lia)) as QB42.
    pose proof (QB 43 ltac:(lia)) as QB43.
    (* [comment removed for export] *) RDP LPK 43%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 43%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDQ AR1 44%Z.
    (* [comment removed for export] *) RDQ AR1 45%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 28%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 28%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 28%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 36%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 36%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 36%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 45%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 45%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf10.


Module S0_cmp_smBf11.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac CST COST i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_storeN_ok s0segs mm (usp + 888) _ i 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
    lstep; store_addr (usp + 888 + i)%Z; zb8_store2 COST i; rewrite unsigned_lit in COST by lia end.
  Lemma S0_fc11 : forall (m mf : word -> option byte),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (S0 S1 S2 : Z) (ys6 ya6 yt5 yt6 yra : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)); C8 (Z_to_bv 64 (p 46 2 + p 47 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (p 29 2 + p 30 2)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2)); C8 (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1)); C8 (Z_to_bv 64 (q 42)); C8 (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2)); C8 (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (q 34)); C8 (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0 + p 25 0)); C8 (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2 + p 19 2)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2)); C8 (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0)); C8 (Z_to_bv 64 (q 43)); C8 (Z_to_bv 64 (q 35)); C8 (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2)); C8 (Z_to_bv 64 (p 46 2 + p 47 2 + p 48 2 + p 49 2)); C8 (Z_to_bv 64 (p 46 1 + p 47 1 + p 48 1 + p 49 1)); C8 (Z_to_bv 64 (p 46 0 + p 47 0 + p 48 0 + p 49 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR yra sp gp tp (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S0 / 65536)) (Z_to_bv 64 (S2)) (Z_to_bv 64 (S0)) (Z_to_bv 64 (S1 / 65536)) (Z_to_bv 64 (S2 / 65536)) ya6 (Z_to_bv 64 (totc)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (usp + 616)) ys6 (Z_to_bv 64 (usp + nG * 4 + 616)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (A)) (Z_to_bv 64 ((-1))) (Z_to_bv 64 (1032)) (Z_to_bv 64 (49)) (Z_to_bv 64 (1)) yt5 yt6)
           F (Z_to_bv 64 0x16cb0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1 + p 28 1)) sp gp tp (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2 + p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2 + p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2 + p 27 2 + p 28 2)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0 + p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0 + p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0 + p 27 0 + p 28 0)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1 + p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1 + p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1 + p 21 1 + p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1 + p 28 1)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1 + p 34 1 + p 35 1 + p 36 1)) (Z_to_bv 64 (p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2 + p 34 2 + p 35 2)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0 + p 34 0 + p 35 0 + p 36 0)) (Z_to_bv 64 (p 37 1 + p 38 1 + p 39 1 + p 40 1 + p 41 1 + p 42 1 + p 43 1)) (Z_to_bv 64 (p 37 2 + p 38 2 + p 39 2 + p 40 2 + p 41 2 + p 42 2 + p 43 2)) (Z_to_bv 64 (E + q 45 * 16 + 51640)) (Z_to_bv 64 (p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0 + p 42 0 + p 43 0)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (p 35 1)) (Z_to_bv 64 (p 36 2)) (Z_to_bv 64 (usp + 616)) (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2 + p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2)) (Z_to_bv 64 (p 45 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (A)) (Z_to_bv 64 (E + q 44 * 16 + 51640)) (Z_to_bv 64 (p 36 1)) (Z_to_bv 64 (p 43 0)) (Z_to_bv 64 (p 45 1)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0 + p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0)) (Z_to_bv 64 (p 36 0)))
         F (Z_to_bv 64 0x16bbc) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf  AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 20 0 ltac:(lia) ltac:(lia)) as PB20_0.
    pose proof (PB 20 1 ltac:(lia) ltac:(lia)) as PB20_1.
    pose proof (PB 20 2 ltac:(lia) ltac:(lia)) as PB20_2.
    pose proof (PB 21 0 ltac:(lia) ltac:(lia)) as PB21_0.
    pose proof (PB 21 1 ltac:(lia) ltac:(lia)) as PB21_1.
    pose proof (PB 21 2 ltac:(lia) ltac:(lia)) as PB21_2.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 25 1 ltac:(lia) ltac:(lia)) as PB25_1.
    pose proof (PB 25 2 ltac:(lia) ltac:(lia)) as PB25_2.
    pose proof (PB 26 0 ltac:(lia) ltac:(lia)) as PB26_0.
    pose proof (PB 26 1 ltac:(lia) ltac:(lia)) as PB26_1.
    pose proof (PB 26 2 ltac:(lia) ltac:(lia)) as PB26_2.
    pose proof (PB 27 0 ltac:(lia) ltac:(lia)) as PB27_0.
    pose proof (PB 27 1 ltac:(lia) ltac:(lia)) as PB27_1.
    pose proof (PB 27 2 ltac:(lia) ltac:(lia)) as PB27_2.
    pose proof (PB 28 0 ltac:(lia) ltac:(lia)) as PB28_0.
    pose proof (PB 28 1 ltac:(lia) ltac:(lia)) as PB28_1.
    pose proof (PB 28 2 ltac:(lia) ltac:(lia)) as PB28_2.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    pose proof (PB 32 0 ltac:(lia) ltac:(lia)) as PB32_0.
    pose proof (PB 32 1 ltac:(lia) ltac:(lia)) as PB32_1.
    pose proof (PB 32 2 ltac:(lia) ltac:(lia)) as PB32_2.
    pose proof (PB 33 0 ltac:(lia) ltac:(lia)) as PB33_0.
    pose proof (PB 33 1 ltac:(lia) ltac:(lia)) as PB33_1.
    pose proof (PB 33 2 ltac:(lia) ltac:(lia)) as PB33_2.
    pose proof (PB 34 0 ltac:(lia) ltac:(lia)) as PB34_0.
    pose proof (PB 34 1 ltac:(lia) ltac:(lia)) as PB34_1.
    pose proof (PB 34 2 ltac:(lia) ltac:(lia)) as PB34_2.
    pose proof (PB 35 0 ltac:(lia) ltac:(lia)) as PB35_0.
    pose proof (PB 35 1 ltac:(lia) ltac:(lia)) as PB35_1.
    pose proof (PB 35 2 ltac:(lia) ltac:(lia)) as PB35_2.
    pose proof (PB 36 0 ltac:(lia) ltac:(lia)) as PB36_0.
    pose proof (PB 36 1 ltac:(lia) ltac:(lia)) as PB36_1.
    pose proof (PB 36 2 ltac:(lia) ltac:(lia)) as PB36_2.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 40 0 ltac:(lia) ltac:(lia)) as PB40_0.
    pose proof (PB 40 1 ltac:(lia) ltac:(lia)) as PB40_1.
    pose proof (PB 40 2 ltac:(lia) ltac:(lia)) as PB40_2.
    pose proof (PB 41 0 ltac:(lia) ltac:(lia)) as PB41_0.
    pose proof (PB 41 1 ltac:(lia) ltac:(lia)) as PB41_1.
    pose proof (PB 41 2 ltac:(lia) ltac:(lia)) as PB41_2.
    pose proof (PB 42 0 ltac:(lia) ltac:(lia)) as PB42_0.
    pose proof (PB 42 1 ltac:(lia) ltac:(lia)) as PB42_1.
    pose proof (PB 42 2 ltac:(lia) ltac:(lia)) as PB42_2.
    pose proof (PB 43 0 ltac:(lia) ltac:(lia)) as PB43_0.
    pose proof (PB 43 1 ltac:(lia) ltac:(lia)) as PB43_1.
    pose proof (PB 43 2 ltac:(lia) ltac:(lia)) as PB43_2.
    pose proof (PB 45 1 ltac:(lia) ltac:(lia)) as PB45_1.
    pose proof (PB 45 2 ltac:(lia) ltac:(lia)) as PB45_2.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
    pose proof (PB 47 2 ltac:(lia) ltac:(lia)) as PB47_2.
    pose proof (PB 48 0 ltac:(lia) ltac:(lia)) as PB48_0.
    pose proof (PB 48 1 ltac:(lia) ltac:(lia)) as PB48_1.
    pose proof (PB 48 2 ltac:(lia) ltac:(lia)) as PB48_2.
    pose proof (PB 49 0 ltac:(lia) ltac:(lia)) as PB49_0.
    pose proof (PB 49 1 ltac:(lia) ltac:(lia)) as PB49_1.
    pose proof (PB 49 2 ltac:(lia) ltac:(lia)) as PB49_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (QB 34 ltac:(lia)) as QB34.
    pose proof (QB 35 ltac:(lia)) as QB35.
    pose proof (QB 42 ltac:(lia)) as QB42.
    pose proof (QB 43 ltac:(lia)) as QB43.
    pose proof (QB 44 ltac:(lia)) as QB44.
    pose proof (QB 45 ltac:(lia)) as QB45.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 44%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 44%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 44%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 45%Z 0%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) CST COST 0%Z.
    (* [comment removed for export] *) CST COST 2%Z.
    (* [comment removed for export] *) CST COST 4%Z.
    (* [comment removed for export] *) CST COST 6%Z.
    (* [comment removed for export] *) CST COST 8%Z.
    (* [comment removed for export] *) CST COST 10%Z.
    (* [comment removed for export] *) lstep.
    let va3 := reg_val 13%Z in let va0 := reg_val 10%Z in let va2 := reg_val 12%Z in
    lazymatch va3 with Z_to_bv 64 ?s0 => lazymatch va0 with Z_to_bv 64 ?s1 => lazymatch va2 with Z_to_bv 64 ?s2 =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm s0 s1 s2 _ _ _ _ _) end end end end;
      [ st_eq
      | rewrite psum50_eq; lia
      | rewrite psum50_eq; lia
      | rewrite psum50_eq; lia
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf11.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBf2.S0_cmp_smBf1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBf2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz.S0_cmp_smBf11.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB :=
      lazymatch goal with
      | |- u8arr _ _ A1 _ => exact AR1
      | |- u32arr _ _ _ _ => exact LPK
      | |- rw_cells _ _ (usp + 8)%Z _ => exact S8
      | |- rw_cells _ _ (usp + 184)%Z _ => exact SPL
      | |- rw_cells _ _ (usp + 576)%Z _ => exact C576
      | |- u8arr _ _ (usp + 888)%Z _ => exact COST
      | |- mem_inv _ _ => exact MI
      | |- munch _ _ _ => exact MU
      | |- wmono _ _ _ => exact WM
      | |- forall _, _ => first [eassumption| idtac]
      | |- _ => first [exact CE| exact SPB| assumption| eassumption]
      end.
  Lemma S0_fc : forall (m mf : word -> option byte) (Jsp : list byte) (xa0 xa2 xa3 xa4 xa5 xa6 xra xs6 xt5 xt6 x584 : word),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    u8arr s0segs m (usp + 184) Jsp -> length Jsp = 392%nat ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (S0 S1 S2 : Z) (Jsp' : list byte) (ys6 ya6 yt5 yt6 yra : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      u8arr s0segs m' (usp + 184) Jsp' -> length Jsp' = 392%nat ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR yra sp gp tp (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S0 / 65536)) (Z_to_bv 64 (S2)) (Z_to_bv 64 (S0)) (Z_to_bv 64 (S1 / 65536)) (Z_to_bv 64 (S2 / 65536)) ya6 (Z_to_bv 64 (totc)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (usp + 616)) ys6 (Z_to_bv 64 (usp + nG * 4 + 616)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (A)) (Z_to_bv 64 ((-1))) (Z_to_bv 64 (1032)) (Z_to_bv 64 (49)) (Z_to_bv 64 (1)) yt5 yt6)
           F (Z_to_bv 64 0x16cb0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra sp gp tp (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + 37708)) xa0 (Z_to_bv 64 (flag6 nG)) xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (totc)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (usp + 616)) xs6 (Z_to_bv 64 (usp + nG * 4 + 616)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (A)) (Z_to_bv 64 ((-1))) (Z_to_bv 64 (1032)) (Z_to_bv 64 (49)) (Z_to_bv 64 (1)) xt5 xt6)
         F (Z_to_bv 64 0x161e8) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf Jsp xa0 xa2 xa3 xa4 xa5 xa6 xra xs6 xt5 xt6 x584 AR1 LPK S8 SPLu LJ C576 COST MI MU WM CE SPB K.
    destruct (u8arr_C8s 49 s0segs _ _ _ SPLu ltac:(rewrite LJ; reflexivity)) as (x184 & x192 & x200 & x208 & x216 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & x344 & x352 & x360 & x368 & x376 & x384 & x392 & x400 & x408 & x416 & x424 & x432 & x440 & x448 & x456 & x464 & x472 & x480 & x488 & x496 & x504 & x512 & x520 & x528 & x536 & x544 & x552 & x560 & x568 & SPL). clear SPLu. cbn [map] in SPL.
    eapply S0_fc1. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m1 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc2. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m2 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc3. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m3 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc4. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m4 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc5. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m5 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc6. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m6 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc7. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m7 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc8. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m8 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc9. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m9 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc10. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m10 AR1 LPK S8 SPL C576 COST MI MU WM.
    eapply S0_fc11. all: fc_side AR1 LPK S8 SPL C576 COST MI MU WM CE SPB.
    clear AR1 LPK S8 SPL C576 COST MI MU WM. intros m11 S0 S1 S2 ys6 ya6 yt5 yt6 yra ES0 ES1 ES2 AR1 LPK S8 SPL C576 COST MI MU WM.
    destruct (u8arr_of_cells s0segs _ _ _ SPL) as [SPLu LJ']. cbn [cells_size csize Nat.add] in LJ'.
    eapply (K m11 S0 S1 S2 _ ys6 ya6 yt5 yt6 yra ES0 ES1 ES2 AR1 LPK S8 SPLu LJ' C576 COST MI MU WM).
  Qed.
End FC.

End ACeilS1.
